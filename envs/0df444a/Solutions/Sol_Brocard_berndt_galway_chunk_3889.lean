-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3889
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:58:45.335344+00:00
-- url     : https://prove2.me/submissions/2c80b91c-0dcd-4aac-a65d-4dbbf4550fa4

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 699280575 ≤ n < 699460431 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 699281825 1250 699280575 699280591
    0x3010e0622200406120525110c040e06010e0601050f030105010e030106150507032705060a02030408010501030c0503060f07020d18180921020309011b15060f060507020a030308 77
    0x94901c801124881c1c800030001307070015490303065280c1000c3c12510f0403148014018000c0c074008003101c17500030f00c22a070a80440d20181c90407109000400540b141012030214a49034000c1c90160352a4000030042100d6040380c0300001280c9441d50707030320019101c0748100c91030300d030079000c042006120a6004203541a1030340000703400099078940f80c0011f011854a10307414031020034408200c910405900a49218405001003103107030f501c90101d10040900300c0e59025040c4591804984103040c1da100f00180c5008140080083c045035a4034205003510401134000d0500a000e080d00044850103494000c03406400c1c0707a0300924145c0029002268081030316a03404080f003418200c0000c20040c03101400000c410101d0b00025182441d181c03c03440c0c6c240780441d0764040e40903000000315143d0088140d0315807200a08020343c01c043c401801c0143c000c20441c004150031000c0000c801c3d001c02642c807000c1035840c24090080c00d584c9402060b20311b405001002540400314003014400a4495032001e5008560 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 699283075 1250 699281825 699281861
    0x6130b041212110303011203022406040605150307200d0c1101231308030c0709060e0712020f0409050f0f0a15090e03090a0b0d1b080402040b01020f010c0503010e0622 73
    0x8002b5801401c208040050841a543c400e0010341d1409200701c034014002210a0304e110850500d11601c103000041c102014000764850744209210042c09070000b0b02414810ba60a010914101401c544903c900540307003120500c1d00405554010484c44040300030003440100003680e0400b02c03a0166100e050f800c80051800c1200041152041000d4078240343c0803000360021508000b0074008952045d4004a40c0749095024820150740254030b1a010343c420000140e0f035076114000c031111a01c907607803007100c0d154079050400c0100c04107400b5042c06514590154503054507070303046800171f03108074800004000c060b054080140025592021034010b840c48203030780c10f0400100004a81484036445600320020004001e0304881c5203104004140b0760a11400e145040300703d1004041480081009018a9403900d40080680c001c21580344168030280003400704485280c4024041c0d04284110140510003402041c143d280c080c0c94041d0071080041c04100b140d04410100d070180400781502d900c1c000c9 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 699284325 1250 699283075 699283093
    0x201020f03040e092b050304030318080a0915023a0503010f060504300516050909010b101211030c0703080f07020c06130b04121211030301120302 64
    0x1060000c0c00050110350b903241a07a00c0c00024642c00c0c0040b03c917103c48480c448200d580d900c41c1e00301d054080c03404c0b9107151094980e92180360590082a03021707e4a000c141d8150343c52810801800010303c42c0d0441980c2d0382d240d07580d80703203441c0c10039005103000341025030090300d66102d062041041c01c001484000629498440c810996114284000f280b000d000960000041c05542810707801c0c08010261031500f58035191170030144042040e84003088044010b5000302c0c200003980541c1541807480d8201080e2101490a0b103004c20202d505442001d01030304107480043d11001041c8103c00700402e02a202c0c0c0d080e4450480d0031100355140c002c41100c419030324142e0035101c420250140d0311500d404150343e030742ca030050309010b02002d5000700410306250000c002c110716a03602141034030145401361340c0e0301c1e00e03070f080c2507588003401030150046a09104082000540c1c402c00100b000451800f402403021814055002103071464800200b05406070300400041042c1d1440c40007034030340680030b40b05640c4501 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 699285575 1250 699284325 699284353
    0x1d2d01150c02150406080c070c12140f03031503030403112b05010504150507140d021b0a0303061a192007030209070c1505150607061e0501080a060504020102 69
    0x103030111010540c00c43d00810b05100540d003002d0410780020308104e507d400c10b400c654650350040c42301c0c0141000450901c16103000c00c4070119030450038020086c180d4070201880100303d42d41c1e07001120240ac40c810100c055810740c0c2000310444003030703a411640e11011200410203104d500b10700e406d009191002010300c40713204040940d01d406401d0344110004109410141040340d12400c86800c0507110a103400c0c140a400743e00300543c8089007000740340e09a1107280501d071038002401106444404400550f400e18000500441c1d000e414900c00d4404010b0203403240c0400d01400508c603660300c0280307420824011000c849820102903a40e452a14181103c003840d1041e450000c400c402112941c003050342482145024154268000054903041d0119840741c2c0312600480c0e0600e811010041c1e4920224101a140144e10b00404001a00d1036130703542c84525005000388030780c110304910200a210803a81c0c40c0158003800f4101e4003a440100502480f50300c0d400014507010700f04078154810f80d0014403003c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 699286825 1250 699285575 699285589
    0x30908040909140f06010303031406030606040507020c040c0207082418011107080c100c050a110c120f0105010503060412031e110c0606030a02281d2d01150c02 70
    0x145030b1100940107a5242d80342c09011303502a40d0824ac10b0010703220404c0241e4800003009640040c084030003140f19201c440050f070400c42c1c183e15098000e800e00c400204102e400240203401c480090007103a1060202c1500d032007140444040083c0ca82828101064854100c0504038140c0300d150000081c04040c1d000a91082d54041c01d0f085440f60b0011510041c0c009007440716988480b44001e0900111490a030010a46d106441d00343c0148402c0d40400044200100700180c40e101014040001ca18890800c241d81c1c0c04103000500880d600301000400c0310700303000c03582c94011071b4032003502a051045d00c00d05070040c0100d00c03804c90042121550445800c0340c280182d4090300540440c40b80d0702c602e142c4c020340c02c08000401d983d00030703070140c0f003410b0068999031100e20001d04c1140740d690842004055000203940d0544c4100a180170340c1c0b1400c0c9260721120f056600a2200d01152200f003100814840c4407061501c01c40007402100400401c41407000100e0403642c6001451302c050700001c280d00080c01 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 699288075 1250 699286825 699286843
    0x3050d0825081f0f0b0d020c0a0803060901080a120f030f0603150b010905302515090b0a1202040b04050a0f08030d09110612100603090804090914 64
    0x41c03164041c0054102c1d40c2c0c544040390f803070307802828403400d081040d401c5200840f4400c40b403005000084080807403c4071340c162003400b5040003d98560020508003c01035420a6800d203100b40344103400012a0710000440391901940102c0b080300c044624202a1240341250003250f05054940c01c0c00610910103228a201031803203200101c10b50f060803c0440d00b15450030001505000101d4018400d03582e88601450215440400c8450880030710050010703009814158540584188a039406003120703258021804162000d82e4007080a03a10402441180004076450010504141050260460150040032246014204100300d64443c0c159141280e0255203c9152454045801d021f98540708444000604410480703101d82ca0901c2407103138603440340080c0c6c40c1aa60740c511042041000f4400840b440c03080c02070113192123404da04030358103110000700d8001d01c10442000b070100b400d074020320500003a903800070102ca0070182000540c9005000001c41610300a06600c50109429420015504 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 699289325 1250 699288075 699288077
    0x70c12080405042309070609050f0102190b0f130b07181205010e0f0304081005061801080c100219020d0c0b070c06030e01140601030525050703081003050d0825 70
    0x180101c401081c4c48a500d1000d00364441d103410031701c81040303d82c0e400020181503c0003110303d0203100a00d000146d141040582403440680200c40c2070400f40100c000c800380c400e8440a4402c0920341d20303040c400f2441c0c294a04010300c0354001c0c0c00490300c0a440b0315807d48078000c4a50740e00f8016500d03030790310301100101a00201c039560b44800003c0e149003010300082c00100c111100550610381006009a20348a600d10301c594034a41c1d500c00580140d0b02c1c0c0b020b00c0002080007500503819611400810b40f1202038050490050508103900840e45100181d2180c0301c1051004003000c2c54215800c00a03103004510090321422803820020410045a03001480b10324400c0d03c4c0b00c0700039440c201c0d01402791380040c0d0000106901d010071215100640c0130355103911000928001405568450000d1440812807800240800c40b007800314091942040061007428080e44039403181f591a032a10884515141c0001061034100c84026102140100103081d00301c02c07828540e88072a01c0c0303400300440c00d6001c500c40390 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 699290575 1250 699289325 699289361
    0x50d081c1e0605101e030f0203070512072c150f03180304080304090b1f0306060207090e07030b0c0705030c0601050a0e070206190e0105040b0417070c1208040504 71
    0x40c40010b10030400240810b85444483d407109900c00707843c0301c03403090141c09100d801381c68198030701e482640202101103107940119260306042174000d109401948610034002c0e2150045400ca03800384440f10040800f0941407c07050510f007040840070410300c09460780214005c001c280e0048045d9014144d036956036030390070f6120b25081131740d480000c0d6001c2011035180c004200900c40b41901104450036900c00100114815a82001094941c00502c520f00d400c010f929600c20811945038120000301c5419170b0899100a4890740f101c011682c082d1407132412607101643c02c0001070701c0e41c000c1e16488070801c009c0c241070800ba41c9030741e411503010003a4030110341c1020005015914040451802908a0864244540c0f4004801a40d03c1d000500104400010200409a48003494011401e248044002071185044c18a490800ca10b029902254028000410b81d0003800b0031138140c0d02040d800040306900030749011190205101e094806440e81c41c0e0801000c1030a4659018092950020200c10 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 699291825 1250 699290575 699290621
    0x1021624060e310825060618020901020312040c0308070b07200a02010e1f11010c030e070905060a030212060a0b090105030c19030b010f03050d030204050d081c 70
    0x2803407001080e5980c58455040c00c1d1604010b000700f00c08500c80d4540c4988820355a41101174500079100411052a0715175046a50503820009140c00c41c00c1201d5075107105220040290001e0b00581c0511500c03140180d0007489050044081906003d400902030224200341a4583c0c0f07451032250b01500b001d8540107840b0f0240182143e0022010440c0038958240e0411019031403025030311190f9004003e4100311280d103101c41c070765035504c0301c8030700d22580c9040c468002c40012102500050890381d403010554030340340464030b01c40d000307000c4c80404070400c5014004581c00c2c070307042000401c4040e00c82c5810030b86c1c0c2c810102c01629100780e00fa1410042c80000c000500e01100c0641c10394000300221401440210010080c54400144140c82400201d40b00c01441039121244d18090280754006020b4000b480000603d002407900f100301a20f0003201038039043d11350604141c059100e03922a281d00194603a691102040c600f40140803008480720400002c0b0f84403a1035842034511b01c1d000c0c080b40751440101 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 699293075 1250 699291825 699291841
    0x406020d0206010302010509040506031f0903020c090f07080a150b03150f090a2a111203010f0504020715050f190b0303030c2a0a030305010801021624060e 68
    0x203004800d068500c0100361942c10b40c0d00007400360103401681da00460711600850001d5505009a200c5000e410080c800313000a09000c2c0009016110b405034050302030098108058201000c80c20700c503148030130007080c00b6110910304035000703031000f004909129902c49501da001c400307400c407600080c10115106a00c0307080080c0b2142d115584000128450303011260401c8840d200d41c03c00c2580b010315140001807024228040f00380914074204840d001142ca0300d260481960840202c0104e4103145044a03e03245801c0d241c560315120038019242e40300e420003400c00007490070b9002000c03154801c03080300e0303d0034001c220a08143d6806440b459080707444901009252510001e036030f1102150703044207010310342803440400d4880c40061b04d090401c000008200844820303000e051f11703d580c9049420145145407e45164031024a440101c0000341014000901d00605000b40c620818201e00c00c100c05a503950703070300184020508840e1f04d100a4645900301e00c010b99103d88070050200e0400400c5074540720720 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 699294325 1250 699293075 699293083
    0x4120c0b07020d0311151017030f0304061515030c02010c020102090d170405060d05010620060721021303110307180b1903050c01030c0201050613050c040e0408040602 73
    0x4405000403040c041c04000da610703001d08032003ca40500b0081040f014030859981080481d0b56501c80300c00009041c00f1103044899000c030100d0b0032002c081d2004d03920503038541c2d442c0e00c83d111003a4038040d020300100d40410801e40c00030042140c0b041c124190180e44000e604142c0009440200100703503600801c095440c1c0a01900c043d80070244001c502d0036203042e000468195401201034141001016000f41c400b500c54101c40240100600c0c880e100d2840076070701e00280c5424040c10001982d60034001c01030b440d2140711049414032501c050011036032403150032100d41c405c01c1c0f9000075000003050958800e03005440103055000e220700040218504609083c500313816074065032400396120070800c10074120b4070401403c2114444002040d0803400c7d4000844040310034980e02c03201d4514030b81c008100300000913001d42c1c0420a89090040803000c00e8160300300d490881d00150000146071607058541138941c0410b81c80072016078068101611344503419883c0303104030743c102c0741c404000800b40b0107035030100 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 699295575 1250 699294325 699294329
    0x311060403022e02072603070602161208010e0103030e0301140123091012050114100918020f06071b1409010828110d061d0a050c06030907080304120c 66
    0x1000a0003417924200c102070815454200c51900304085050b22884d681017071040301e41c0d09401c03110640d15000d9194283c4074400d900c10007250a0032501e400c00d0081c0340074115141c100da480070030b004031681c650344054851024424089030300d9540c8081080080f01c00d1581580606080400e000c01c941403070110300400c0c0c40951106114a01180c1000000116042d5907420b40700c0602011800c5003203841d1403400340041c0306202d26003050000400110194144118046403580d807000c2c040761020881e0807001480310300004e508009807849042081c18508014100d031840380e010410089155003a400c00060660040c510080c01c01d0702d40c0000d4901250140e0140ca003003030140202105452080111010440c4004075070003442c90a85c05200c203514003c2c10314407002d0612080e54a0b04d2400b000240f400d00c0721a288504841d1800303519440010b950b402541c0d0100007017002c01d940d041001055000100599034600c41c4250200b0b8210091000d0401010707034444541c0c00f94124588500300c1d40d09a = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 699296825 1250 699295575 699295577
    0x11012a090b2503050c0715030c050c2109120604030206100e06090601050705160501110111070602180a031101080a2319060609030b0708060a0311060403022e 69
    0x18080c6060b40046a11064181e1050448864501c0141d15054405019035820544217000766000022040c0d20401c1c1469421030381d80d400c1003201d11100d0b0507982030050080b44011588881a030302400b1400c0f11102049e0850200d1150904d50b0500006080d000b400d034228a10f0b8000030140000c054040146a421100311010b1540043c28110b16032280c5070020a201d2040c803110010519a074064802c840a040d0880c040d00c0c41e04410701901a4449182e1241c540000c80c807002284141c0c0c0c041c42064100601d1441c0f46107441103039221140a0b40100c2d0018010140c44050540180d0318840b14000851003030b0244000d81c01c11800240c00340d1001050011910704046265140301c980c11805081101b40002d10512915059503101d1122620310811300882e1078860042002504a01e10600b10703030bc81c40c00c0700110394a00c84103c81d002c0f0f080e2810f5400400c040000d00000e090407608080c9104041c0203582019a60b0f0005148039000f44224120312080d140c0f42c0040c030300d1503034a0540c0c503245 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 699298075 1250 699296825 699296827
    0x10209180c03070c06270309050103020c0c040b040209190303140a0f0507150e100525122705010e01110a0e010e030307140601090e0a0311012a090b 65
    0x40c0303103000380e40d102c0145072104010107100c0000400c009584a181a5214640040c0302e8917180c20146207450601142500407640f070100c00600d9620070b001f114030103e0108090060541c100e01440090320340485840d038455001d00a1000c26158031240301c080950000301142d103a441e6080c02b0f408200a08842591240c00300118088103401260094004042c1e103001907594403582088900344811b0740807011241d050900200002c0c0002854000924501c1020011501c0704980b001c50640a072058400c2d818845120b45155401180005408140d080c80070441904204140303003c0c100921074504c480c991909080f0500500f4170686441c0c213002c40c000c0003140e01d2140d02c11001d0298039041030070081d002011400a91144040040d4800060b044940320b5206291070100140138030f808404034401d40000003500003150190240392550440a000d42c5451074600721440c13080446084500d640300c04c0700203000d2412180c01c80c040c02c100900c03603000f1090307020000c0c90b404560b4481440340340 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 699299325 1250 699298075 699298081
    0x4060f1701050d061407020606040e01020c0c1009092d0902090402040f0905122101140409080408030a0210050705120105121515030d081e220501020918 67
    0xe40003299054800407100e000c0101154a08a030103803102a007044404c001d40300038803040b03a80000d00c0d280a980101c0b0140010501c54200a00300d0207444610740e000d90007000c2c3e03c00c0604007100c0c19010003800d49800c0b5912515180c000d03090b1140c200c1c8008400803000480401424040c01000c0150a550401e028501c00e6400085914101400103407260f03070383c1d00024400210310b80c4840559507010055480742003000b100c0c2c0d0415000021910f00d1101c841c84602115200040b080341642c1c0349004078031342280030b10180402080444030864040208020114000d103040010340000d20480c0c1c000d03e9007160040c003032403c0d220091b0802c0c007405001d0201c40b0301912034011f0241035a00650b201c2c0104400042c2c004d152401080400ba0044003610900040301001c0358140e5000e4410f03000c50b12120348000d4100c6505004545a0400c400300585d800c0070b580d40c08282641244020034800e25000503029011031010b144041200d42d0b1703500184c603100341e007400d140400390762503c0590000c8500d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 699300575 1250 699299325 699299357
    0x1050301150822111c1a0709030204140414010e0a060b030705060a08040605010f0608180a0b09011d06010302010507032307062a0f18050409050304060f 67
    0x1002012480080c40030010000e0703141d04a807516400208400b8409001030f401d2810000140f500d8104018011100403001032800c60030308010b400201e0380006002c0404568800403868050058035140c00c00c9040030b030000250392507002d298500400b0195006a90904c2d1500c80b09420030300081d040f0590400c5032000c945031020507414401c40c0c03c8800411006120130000b4200390711074010301d91001d004116010762982c0000f0f00c900c00c0d44250300c10030641e40c07a86a0003407003070003034401c2c440050b2074040081c0318400c242c0c50003040707400100d0850380080815502e401d003005c801c40f803192150703540d6803c0c042d0414001c0c0c121451800070030301404041d415900000c1540c0715041025081c0095801d410540e400c0200300c240301d07030861508503901c6625a103032000140030705807110043e0580c0b0155540380c48201012181d4500059110b040c00314a401d9425900001800f003020031900300703100c00040503251401051a014820805150341c0d500f4000d024020b03c0c9101400002c0220108103036940c5 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 699301825 1250 699300575 699300599
    0x10507020f07151106070504031502090f010c0510092f03030306010525110f0415050f040605030102030c0a020607140d0f06050613080606060c370507050f01050301 72
    0xf448036810300516079501d41030252000d5035000004d943e070b03108440400010355408409001034a10a40f100c500c0e610064900a00b68000e0030a040c9d880000c0c10308a9060b58050440880081c3c40307034054580242c00f000d0100200c403007458003541d00005010020301e9012107104030008100003221615410801d50340829a41c1c040201304905200001075003000b00c03040c040015101c410700c4811810001080c1c5031103203900c541390111358011503503600d40228619140c080e416641040e99030408045103054104149040c45401d0380744c0040d035407040032450381c800380003c62003090080c0e20140d69908a603402498450014040d0081098040580311401200421503800100c01540403401881d003501400042c011984100d03400500010300d551039110200f080b0b42181c6005003914069035810007800380c10701c58103580307160355042021107100c442c800c84504c0b2400d52040c4003000701c0080030959461501400034003910030f03078040001001a031070064050001c0003000e18003141035524001e4003643c1 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 699303075 1250 699301825 699301829
    0xf04060b0f0903070e0907061805030619111602100c0b0f1017010e0606100c020114070602070b090615012c030102190810050105030402240706050702010507020f07 72
    0x200042d6541c0039036410400d5402810141440c98954103000e21040e9403550107200b5007001c00c039036200d2500900d184040350f0040b50700182c0a0202da0380c2d503856210844a5507100008d1090b92420f00d0641d605400c00600501c0c01d004e105135031810345c5030041001b811582000b81d0b0030001c8407100000040d85a0503c1d5410081030301c4181807984070714016002020060304040d007013100144080420a8054004e520002e45903025200640c642c18240407054001c10201d6021803181c1425200551041044a03070106101d11458204083d0355240426a88020b006035800c0c0b8100c0c041c410b2800040c0a4590040c51420300511500040341c0044c1000303040c0f01d0113202c002e18000d4000d058542d070200310f110414008000f199555540504001c5880d00741c1c4240000401820004800144280814042e0340058480a083d5662039081226540e60706180400041940149100703016299010700005441200042918075000703000070308442c40202250115407100c10310820b110000b08a00701 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 699304325 1250 699303075 699303097
    0x402030a020603130203120a0e330412230a030e270709090b030c0d08090a0f060815011701090f0207020310050106021504080405010c020d021309020f04060b 69
    0xd26603413041d031031072682c0308120000703501400b03800a400008074484000b888042c0f104e8aa40b00703007c48800c03d01811500410f01c0c4504c0030079143d40031821002c0341c20580303000111041c90ba031030325442d00600381e42c080d03256008854440038003501045c48003041080c10030740c3d19128000c2080c24440d4074010002c007104100303140076011048109243c60450108041c65050700494403105041032040248024043e200300d60300315103404c1c420681031401103501e11070380381e0040424022404a490313040e1075a00509000d984902e14a00000341c0d0304901400754020310240d04c9810705490030416034100c014407040b01c2d03410000d01c48070010b030f0345100005080c1075607052440010345842c81c0302154000d2140800c082e41c184035400300468654103070303003009068501960984078000104d4484541e41d5409480c01020b1007030512051105500c1440349680d0b8a000500c84506076101c2d8011a0155102800700c1911544501014041d030034100d072404a114000d4130104441850425510300f64040d0429070341e = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 699305575 1250 699304325 699304327
    0xf0312250c030903330921030b0312180103020405100f030216050618010506060d09110a0b0d0b01110705040f1b021b010c0308010611010e06070302040f0902030402030a0206 76
    0x1c0a2501c541c12810155070f01c407003441303018950320810f0082c0b204004c3c01d6000302d001e05602001080c14901a510000f940402c4c2c0d049008450020103d11110900b03441081641d40c54604d811998100270503100d1030800040c2d03a507070315611500758206a43c281502c1d4140f6004210811450f1200d84102c11140700c40d24000c1d0544070740729400c40180c45561400e0100016a2101c1e0341407010220300d550181e075540c100e0303020891620040c11b003070395421280d0300d60140d418809880c85070601c0c0c0100307204a1050082c1004000c440c8001144680d180d00441080100031071100c512100c030f4811202001d40034208513411361040100ba40c0d541d0501c0c041c5034022078903200801e401c00d14581190384442c4204030728040d8941c048100a5032404011409420f00d0300712140000c0d59400b4105c2e202c080ca0b00360307131242c2c035a80c20000706440d03c0d040500c18007095942c8250600380e030356003440814080c15403940c02595407803030014810300000954000f080c00520420a010040c2e4000686240e015816140070f = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 699306825 1250 699305575 699305597
    0xc03120c070e0708161103040b0c07050d0f0b0c0702030a08030603011401050907032721140a080c0c06011e05040618150f031b0e0708040308060a0302030f031225 71
    0x72240c0f52a500ba06c06035520020401003840705501c4050100e0031880300854040541e6481001f410b044120001b5124110301100c903070108850030107143e44090388401c1d45e807802c8080d0380802e10b0125004816100d460b07011081c002e00d8034003806462400024184030304404d5050000081c8090310103040c2c0400d06944001040600c2440060500303120100588210109018204032074040540b20705010220b40e20303e10301e10018042d80c030b8004514501500d0904008aa280c2030300c0201000d46980f849072400d02140c807924400700242c40c040c0041d01100d0f0700c90ad141264810804e0180d400a13031042d81000402d110606c50416600d80705001c1060104886a00410700034a030303a269080460407501106c1c011080c040c08800001541c1c5c80c0350605e9469030b45d1030f040c14060490940d0800001144000070401191003820760a800c00402004180001e66a030700081c90140d0b401d094030150740000c5444070400b1740f004115644038904420024402458006c00500045200205800d2100e09414 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 699308075 1250 699306825 699306827
    0xc0f03040e010f082d1207061b02070b07020f0607061a04050c0c03180a05061b0c0f03030d0b0f0310060e09280510110306030706091a07050c03120c070e070816 70
    0x91034180d0b1404031b00396038902a0782060800341a10b020000ca032050200c80038941c039032000034210b003150300171004942031400960030402109242c519490740f101c014450980468420720500c005481c502100c0c41c4018924404d11065460051081d00c3d0f040060004d118620004022030710064802d06c8116a44024800080c050714810f400594103ca800304111040e0b001020780741c9042c9a46804559000700d0300020401d0342c014007051290107420074042c503614410350307401406900c5001080e220405450101207480c092001104400711038a4a0040080c02c90b405120350700448203a01402a0040a040c084684206080081e21410030080442d00b0700c802072281c04454500400144014400c1502d442c001c4d03001a201c0034468042d6060000b5082d0090710480e0407202c50403a410001d502d20782d04c0303140581100c0810394070f034000c4141e02403103607400380b10340314405202c081c02e581c90b08d00b0034031458a0540c4581012400100f04c2003031020068000341a581e0005002001c0b000301d400e0303124 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 699309325 1250 699308075 699308083
    0x1406040b0f0d140a1503020604030b09100221010f0509040f2a150f021e03070b0405062202010203030402041a09010806061305060f01050c0f03040e010f082d 69
    0x1c071902251030300d03c1c00e4072248103480d0818040c034952070050080041a144442c200d01035880000d40c0080308000c2000040ca0003881d40781d2121601c826039120f01442403008042e0390001d000340e1701d0341c0754101c00c212920241b24446409000281c4406244038209400b18140c0c0c0c002800140c100a00c1c94503035130400480071610390350b80c403024808218140d0344c40080340c2081854010203002182692020f01024807640850064031205da004181c94814052403072100360b10040d039008580020007030f01c00031501d8881c4641c0114800d000819070352504030305420b0500e0000c1842400002c10141a00141c1c3c1e002042e00c0c2c106404a80014100a512100351042180f9801183d00000000000511040c011803041d10070041070b1041501244d11050360402c85404850389640000806503490141d4420000780401c2c03000301c0d003107035031406601941c1b13491500301c1e9010654a20b000b500500001d80a0110a4010100315001f001e0bd42c01c071100841d0311210b1080d1801030b061184a541c106844100 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 699310575 1250 699309325 699309337
    0x2010062102041e14071101090201090302010e1c080d11040b03010b031510110c0d0f110a0f09050a0b0f010c151b02011d060103081b1203150a1406040b0f 67
    0x14108105003000b1402c582e60f452011600c2e00d010920110686c10004410f0107a075034450b07030507550100d1850565006568030340f092038070507801032409a560020150b601c00340c0c00c1c08500500340d0503218190702c0d12031801e60b00000d40102c0c00e82001d0204000161100c004d4a040d242103174100b6880341e5640700e00355a441094020903511a9580c0e12081840740c00005800350802407a0946440030000f034140400b18031000c41c0181102840c02d04c1d0300c003003401d1140c00e0150341d400a02d0040400c0c0d680076512003010352174004c1010690ba03001440b81c4044a44a0021b21050540e0755504981d1203070b0020b80550b4010501408144c014026070007040120791048902072964010680030301003100c0000e008041d5422110819070078010814103081002a64a049960040030145001c2001e043c840d401190380246202c14070074900402501490000503610492038112400d682d01c072000d0130483c0300404c0307510000c8091500134002c00e20342c070707030030203c0f426912101201c9503589013105c510107407403082c0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 699311825 1250 699310575 699310631
    0x60504121515060503041502130317070b09071811030105060705100204150e0619120b0a03030f030c03050603030414010e03030a090e0709060c030f201006210204 71
    0x3081d000c03d6480d009805180254041c1d041d42c41d051030200c014004a100d8400b04100718020200c00704001082490540380805200815609282c0c05948041c82c008042d80c01d0359564116880034084940340d0b03e0400b0f14400b0482043c000c908421000044600c8180034480c0501c0d40000c0180500604000308003050b1407032807003150341b01e41d03a84012142d000002544800201c04175600425440c042064450390031446555000700343c4201000d6920002815500b0042500d500150309199621142170008602944445214a120030b100608403548440d8400600d071500d0309000b0151030000503174050b1010000307084007120b481001a100d560119003c5945448005007444000b540325074803008540b401da000001c1ea8031005400c2d0340b85503050050900207060701e02c810000c2480b8540800340c030b030141d090064100e000740c400113150f03410300504003486501c2520840708410840c03090800405a00341056480300e4900300062a80074a03081c040d200301d890f0b00b290009080b041c0590b890007081 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 699313075 1250 699311825 699311861
    0x90610060e061e04050a120c06051606050415050a140402282c0403050d050a18030804052103010506340203071a03130305041a070b010605041215 64
    0x340307506258103a80305004142c01100305190000d1f4aa040b51071648115074055a180030030360806000b20f80a0700b00d452180204002003040c4800302e403580c82102c0c0203501800c0801114040040c2d802d0503102e02134a0f000c0f400c0d260401a2000e20406100260800d80c101c400d00061400390000000355248901d80c006034280040e40010340c8251217107422900c1a940c2d0b180032000100c5044201c44000032900038000c0b80d420004969031000c141d00035640401d003031300300040c6194580340f86030718030700b41c243c003100881c0642c1d0502061010400c20606d140009078100f84402c0910f00d0103800d0f41c04184101c50080c030010414901c0c00d2800f284400f18041561304070803001b21541410f03103203131030030140230380c0240034141e004900700c520007110320754003000b0b10031080c40e6072500c21703110f8080d8950754000c3d02000424403000c5000c10618260011035a00b04180545a444500b086502d000040e404501800401c1000308002c901850300f0408440c1c04c403070806160052009000040c01708843d644e049600 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 699314325 1250 699313075 699313117
    0x18050d0b060f130506090c0301061b020d060e0133060c0503210106032901270621051308030a06030c09022203030504090f020403060f020909090610060e06 68
    0x4102e904c4107108000c00c60300030341540c59460069404c2e00c42802030500051142205a40100c0150441721015202501044060002d07448030011594110000c100e6a5101c1d400921030854038070403002c3c42803800b0300485031101e0100c4481d480803010b1056406018540b41c1c0f51091000500c1525491105001101610150300e440200e0100c401d008010203e403070018100c40301129555495524000708190440d4140030600640d000c006d07c2d4002d000d040542002400e5100f602d041c1e000041c50940c90742072108800142c0030010130201c001c03400d02d4074540000c100482c070000a94441d40703504280e031250b40c1e45403085010040c1c20310740c201400301c0d14260400624140160700420344182e203513801c030ba00c1c984494244141410644405000100144410700c4040c60036440f07045d0b5054182001442c1907540d58815040d50701d10b500107540194040b940e00c051342002801264440d845201601191074807801403201003540c0d0184000b0048008040300d010303110213040b1141054100d40a0031020 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 699315575 1250 699314325 699314359
    0x14040504090620040509010b090d050f010f0b030a05070303080405120304080a090e0f06060a020c040e01060f0b0301061202070c120f20090c030907050d110118050d0b060f 75
    0x4210035602c008001107200d58400303070f022640305507419118010440d00440c0d20300f42c102e803100e4200c0e000240c0d10007a5031004400048082000309050070300e501c004601700c410760403e002202c0b20406021301a41103d030f240d02c0026004a0802e0549501d07042035a8140c8441c1002454085114008101d18800005001c00d110f03610000d40300e00e62041d03964144258860b49260b07642c01050322a15100d8440794045803079460034401904603107200b4812104c20601c42c90001d41982c90240c44125265500c84062103001e030810700e074402404603848840e1031949800001021741d225440480080b0386d0105507403007007185240390403000344520058a03400404030300340404003464a0400b10740841d582c51001c401070303840c1da0300740d480280010070420305503440034240110342c1e0004048260314003a801c0c010400303a81d880c400c0740c0e0040c002c0810201200000c0300240c1f48049800780c002011703c15030350801c02a81c4000f01da004030760b407010600c509501c5200201e815050390040a5512214204c00c0740811 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 699316825 1250 699315575 699315581
    0x30b040609020a15020606010c11180a0507030506102607170a1a060702040b090f04120813020f01030f0e0d2316030203071208151f140405040906 64
    0x20b030084a0061096542d1840d1021110441e5035400144c2c01c10000208151700442c3d80c403c0e22802503206104154501d40054000c900400f0181d08201c019014010402541d03c80d03d5841121030070100000c1c02d16400041494161555403010050200038481100c0c03054005070030010180d88030104c0c40d0070300000150400310b8141d0320f05034120201c400604007040c940250401c415130032780351540d1100d240040c07010f10703801948185d801c40d8403100d1420b035685035810100e1066112182c40300f25800c01d841c043e0203808010b4032403004c220307001d414040c0c030701c40c40780300308901d030340d04803129030f200c00c40b00005a002d4040c0b07010304030085161181d028054030005c1014550b003202c0380d49050a0841403a541d150682e400020410279103c280802c1041031000d802c4915000d00900481e401c0854070b13558801401c03c40c25000b40050f041d40140104000490054103402d20111501522140c040114110b10148100d12400b007000075031050015845081c2207a0250401403c1444000b02e107040003005 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 699318075 1250 699316825 699316841
    0x1403040306020d02090f09150d020301020c07060203070506010e070f1d030f0d03060b0f03060d081b030a031b17070504091a0f1e040b1810080c01050403030203041e030b0406 76
    0x7442586120410b646014040d030340c4a4000d130b5008c4021043d4010602002070502e800c200e03051b6508000c3b07218404000c1003c400201002e83c0115035900807850610300707080040c0e00484005a04c3c006000c20140c0ac42d100038454070039854a0140320001c080b0700038030390071503500854150040e44c2d103000383c409010600102010050b2401d105140c0d0741d01c40e250461040840f51404403c050012075401d103042644000500c0c0036004540c20003403017211400c00111841c000320030303e50000800c01c0030b003074241c0104482c5204200c403070348004800c1200036005001c903600c0010311040100001d80c21500850980e0040c0c00e48100420004410300d60543c0401c280c00410303417055002503030301c0d500c0b480c03e031546601049030001813541c03518410082c00702030a1406d0700b803a44541c0c8901001c01105401880354400c1e14a40802c40c0352030303d0300031301d28185441d003150241040b00411041c00801c1d0000210380498418802540c610300b80e40358050998070468000901c4145004140030501c5025084591 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 699319325 1250 699318075 699318079
    0xf040e041a10051320030f10060302090d12140a09080106051207170102070b04050d120b061b1903020d1d091f030503210901020a08041403040306020d0209 68
    0x35590311524140303001040b5500c141caa109420300307803402224519410001c00d124a840d202c0303600c651603d0900782d107900125503400440005004000740301030140080340061019050841c5416412408580c411002401c041c000684050400002501c01e5440c1040d944044140c0c64403078080e0200201200c00a01c500d0701690308010022616107000450603030001c00d0700c00200061407400114816040d880910001a55802d000c03003030100d54082e251500c6107105a019020640e4804005070005540d0090308442a18110350300005840e080111440c40504c00300d940307200500155851b1a00b08090101d04618240542c1c5404154000032480c031038144035102c64a0350010310403401190f00003550b01603827000c01c2c0070200305190004050500b8100c417801d03095440c03070307240e0b203c0b1482d5601484202560748154511503002120b00c2c0261a0050720410080d0314110701404000c04400d800b0300083c2007102560f004074059007040080304d0045902c40c0c010b5448489041c410b000a40208404034 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 699320575 1250 699319325 699319373
    0x13020703090f0803030403080c040e0403050405091509060d02040617010207020306010e0f04080c0a140c1507080403030f02100e010b09091f0c090503061014090c040504020f040e04 79
    0x300d190090242c0180c140d03400800203504540e510b1f1404ca81820018002d851880d2042001044607440b1000d480c0c410ba0090322020381d560b18003000c1c001801001021801da201c1849000d0180c1d503910701c0c43c0c5030090822185402c001080d800040c1c014402640124103000e10581c4541044006401600585000301d0541d0a50b07a614101c840c0248802c660100082011400041c0010a100013500c4100401e2040718018401035403880844c00640314100700650040e48040c1c0e80b0315040c00600122084061800d00b0400260f07030321050380c007940c0001810f2107441c0150800e101e208110074001c105c0c080d0030030700008540c241944d000b850109645402031070f03900d0000c0c0e00c4900004d48001ea1321502d2410300e000c0040c244030100100a10440e44003001211540000c40da502008124014868503800d1861b091800302c480d03042000010045010381807000070001140409401d4408841e42501c01607a9601c0440120300203109642101b4801d0b80000280804d01007000c0c581546c0034004010700d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 699321825 1250 699320575 699320579
    0x8061302090115021b0f030318090708150402073f0201020a12020a0215040b0a05011203170421030515180f0a06170616031506050c15090307030f03060308040905151302070309 77
    0x21240c071807044940480f0dc42c40340382504080c0c1803a500030f203511405941c0c075500c500100462a11141003210b045002248001c4400c40e05406061000444400d9400218039216003488054007040f070810004d06825400b10fa2007010900a01004640710002c4070300448500c1c007494003020814080c0c42e00310f190740c90040080b41d03401a001000f0340c0345401d900e8461020f4840e1424500103140100b040700ca41c400c00a50710320b005000c01c0c44c450140d0454034003041c00e1400034140722a8154030550b492180d41101c0080c801c0054028403682c002e9110070a000641d5074202050700a04036030360000000b1106100f014480d4400421014010225401c12424045411004806460303954089107603640c81e8013403c2142d207000c0d4004000b200d0240d07084d19814180b83d0002485850308440380a07007900300240a00030140c0c00f0000200794011420100040c0d4150b854070101d80c0101e00842c49101d41d5030000c507884c3c0b41311400c0003802c0b200052104103000d00344aa160080e4000010840104c0c06000300 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 699323075 1250 699321825 699321827
    0x90d02160e061210050c040302180c12090102070c0e04110d0c090c0e0a08010606080108010920180a0204090f0605030d030b010908061302090115021b0f0303180907 72
    0x44200c451503a1200007039254501000f680d51207104148a0030b200389100003c40b1100c90040c41d1060044181c1c40b80c403503155005102d80c030b40100d140008160072640421600c459404160380c94200c0c00040c00000c0c2ea14a0042402031140f014040c00c2c002e04400001204021202068032403440342c050007070304050403010710000c0308425800401c0c00c03025001c01c0c000c1140b00d0740400500750381c40c0703000d001003908000818041240c60f04000060794442c00c2c24010183c010850038014009040204011002d030b40721400303039010448003403d9003021096140740903a02c1300302c0d502100030300310007100d0581003050700540258480c0c442d85181c1414184c6002c1ca5503414030550045400240c00303030104c40000b200440c0100b0aa41003541800110003020075403840801c955407042030400d9a98000c0b42d000d00400220301c2051344962455040182c0084980354081030401081d028018011304550709a8005111803030b103000410742500c000b0441c0100644051603070b5102c4202039a12607210388440b84 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 699324325 1250 699323075 699323113
    0x1060e0d0f060e07210c060f0f0807271410170a0207050f030d110c1b040f020d0f1104030203030307120f020406030e07050f0a03060203150306090d02 66
    0x14024012030410211880402c0030303a003020300c00c0340310202562000c5807030700c80d4079428a802081c01c0e00410b0a08260208111048110b0720203041d1320305025100c5200e030f51000b8444501112900200b00144001c10801801000219600c0741084850010304290f090021920100c80c421580408200c0d4141085820b11100440c481481360b030b0750750700500b101c10361280c80d01c501810011950f58204200380c0800c03400d2111808824040300a140c0c0d61409031614030030741300c0c1040003000c420001c00c1820014200001d4106812104905804803001e1b000c3c0010001c242d0341c44203404c641d000040049a0f001113621815040c044c04200300b0440700c207240d40304500e00580c00700941680c410004611094090304150010701c1c0c50100214402805441c0d44040c4d802652000c07000ca034442d842651061424400c131000351a0659001c00d5a01034070000400c0d049a81c440549a1540003000c284100b1405580c1030744440b0203012602c003810120f810b0f81d5529818043d03e00103000d2200071722041c4d90302d14 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 699325575 1250 699324325 699324349
    0x114040602150c04050d0c081b090a0b03150a0c0801080d05090112020d0f020a080f150402220f050a0f0608190b030d2307080708030711120301060e 65
    0x1038010050116082d20188141c400a0b11400c1d010320305000001e0280c2c1c41c0f00503404030078421006800c4062401d0421481c1140d01c05130422080f110151264450301c030341f83c2e00340d4407040200c4080f40a103809004641002903104220b0440d0f10114100b000340c401c203403c1940648456901c20301103070b9840c0c0040da00d5504001c00b880c001907040100c100198444c4080c40744a4030210401481d02d0307010800e001c1140c1e000c030840450b054000c01e08035000703500a15003581c03040381d440d141042c81c60210002c001030344407010384910a0382d01040030381c1d00d80010080c0e07010405c0000005858981c44a80140110f18184034840c41038041038030200300e841169640900300c501d03c3e00d81e034041d03071a003000801e11030344061034594010303958080311303600c81e60300b040b84c00150604e548074103038000104544045641c1c100b101d50700003000704000400015240b8000c42c0c0c41603070040b04030342d12506c403680102c60011264156040350b00c11200200c0280001c000250704079495074480c001d01000035000d01404403800 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 699326825 1250 699325575 699325577
    0x907050117010312120c08010510031a091803040b0306030105061206040f0f1a0411010e090a02070f0c180b1c061e09080d0f27020a0b07030e01140406 66
    0x8500410000340c0d84030180a041c1c00e10b0900e4501d1400601c5c2080848a80886400000e0100f5004000c3c0b800c2c4064080f950700424503040c00256081443c2c0440d01030300f804180c0c02050300000280d80d40800b00f40d0803c0c1c000d0342c2420350350388542d80c90104d1103c2d08180c555031300c654a00004181245080410001e04440c00d6010703005030307034544d2101d0002d075038080300568114080e00c00c0c41002445001c1070141164640f81d0b403040c00d007020304054030001d64038070080d81400800d4500380b20b1942d55890117548080c0d90030003d40c1e280154034010096003480e54000b030104003500400300726000c12028080103409100c004020074007003c81003000d40c4005007940f401c003460260603070303000c42c0454000b00c00b010340c402c0010ba000402407100b4030071a4903003102502c02e500085082442c5142900588402102d01d250500c1100c01100441840300c4500101c2c0d212116400020000c644070b640402000f04180200c1c01d03203840040c00c020301121080c070000ca0014400d80340699010010205a03010307a605 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 699328075 1250 699326825 699326867
    0x503010c020705040b120607141c0e060c030907050607082101170c130e070f1d100501050319091b08010b010c050d030f0e070303051902061e04020409150509070501 72
    0x141c114191101062002c9c07482103000204980320180b1112400c130120315101180001d4280d00340040642002d101400300c02c03c622003002800000301b00000d103401540c40c111002035a8465601d00181544074280140d074000e86100008060b20f05010750300d504890102020074800300d1291403094403005024200ea61051110088541e40d4400343d03c820180c40a040480c1c400c55154101c0b806801d001c0e0b4803e9000c580030300d14201c54481c3d046c0e4159004941804420407603410703c0000391140c0001001801505080c042c004d6080e20360342c00a107485500401c0784182c9100e003100c040147c1d80540103004280d0301703108000030207500c80c07a807a40e025a0414060030f441c000051048004d81400c005540180380c940d829a4000f80061218000a510030b0301c880d82c0d94000340301070074014210f0080f403000350340056081001c0e20098002c000307848041c012804040d41d5481c40002d0003030021030b5003e4280c1110303041944003031a00b40d02840c004e0000604039200d03242e03541c004680419a81415001c0005 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 699329325 1250 699328075 699328081
    0x1e030a0b0f07032912121809060a1e0e090a0c0b03040309090e0109080d0912020607020709050c0c0d0f08010803130510030b0d0b07180e1f0503010c020705040b1206 72
    0x20500000c2c8404c00b5004142c180841205a0518540800900c800c0303000200042d180602c0c0c8010701c0f05030700c103190a480808092420000180002c3c840e4450451504841000600f441d91060400c0300a0040128556954141000900da40e40301d5418100e801c60440400400c1b45c0c1071280c04d0300d01c11a803564030504c5480c1003001d044007410740e0f0340c0c01d04190764030341d851800080c0c03800e000380c031301e07038103404400112505103041400e8400a01e40d40002590440d0782803081ea258041010000c0d43c4002c0c4001c1241c0c0ca4038407181c0d105214560a016050080c0c8451041d021b500c8602c0c01540c00c22130b5a115010390b20380c01502d032284201c0802001141560030200000d040012440c070b00400c440c02c1c00a01d41d5888004107680c4018054100d030001400010045c00d1600012030044114541801b8070350700b41812214906210082d0101414820741131405800141c001c80b20805000050028441342d00240b00283d0345096030701035907200d1030034000d40c0c85e51800c00b4074803030222060140042000f51 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 699330575 1250 699329325 699329381
    0x7140f160608010905040831031119050114160204050c0c07150f180f0303090e0a050f0403030209030f07180f0903090605070c1d0708241e030a0b0f0703 67
    0x700b001700da04001140d0784441d858108231007000401503010314201c4950070030020401086654443c0f40100c4a88610428403540c2d034443c4001d902d01c4100132200c0e40c1d641102208081c8460301c010029400b9050404020000c0e28070000383c008900d000c000c43d1020358036140030300550a0804101c40002c0d5030340b000d04c054035109460b0503140303e000c80700780404c1c95200d454003403041c046608160003180b4141c0d01002114035131080c1d0b65000341c0341e00b000c00860030f040c54103d00c40e81c000b81014007056000f081710b080580c0d06220072200b008000044540c0560b407100c04070f041482c0b910104c200710b0304e40003400c00d00303c0c5240912100258903681d2005218249002640e2a0304481c50a6610950108012a041804580030500e214901540e000c1500e04000300905401000f0a54040340901d0340780f00e05040b00300610503540f401c045442d51807009140b41003181d02000301241c6c83e41071150130400e0b004d1101400741c0c0c90107015040e000214940c0e81603000d400f81ca800e87c00300c80144d0034050342201c1034 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 699331825 1250 699330575 699330607
    0x60509060306012306040f06081e04030212091c060c110f0606121e070e0106020a020a0b0f0c10060f0501020609150604060803180901060306030807140f1606080109050408 75
    0x6810002c0411b03040c0354566041301c0421815800c00c602080d2400203008582c0303020300c40c4404d900002c1043c81d00624165400a4a99203000744501c401000030a820605654410399030850780e031800401600e1622500f05200030306642940000030804d080c4200000d52808a8840c1100781c0b050000e003501c0d15444280402d218040f00030400318060403202c0716445d241c80b076200056400301070003070050a042654003194210107031302c18804d5603c10600d0b8001601c030109102c003201d1041560584801030504205207a11401805103124020150120b208000c198011000e40300580078540d09180c03590016079a850080d103000e03045a2103001031b41c00f0791030319003000c0342d100b60302800c045081991180183e1860f0000d0749816005405c40440080314104500c41c6401065240b400344040340c61615403080c103100341c1d03074080c1c0104e62440100015041c10000542c80c5040c0204450190340c43c1c0d44480042c0c81035014200000341c02030000501020f6602559003e80c1e004002c852605d08140100c10382 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 699333075 1250 699331825 699331889
    0x2090603010207021203030726130203030910051b030406080a0b15120f0601050a0903140316080d14150f0310020c01020903160303020a0b0c0f07030306050906030601 73
    0x3040d03408000318001030f11114644c410500c05c0c03030300550b220700700b00d00c0203006860380388040031040740c1d01c100000342e19501d003c00301c1d0008002c0c01c20411000350380c00400d0552164041032074100500c0f90b1200d44041e032100c020107441c01400400c074003500078020301503203d01c10781c030542000648182c0403030100e4005034051202d5001c01009070789070408aa01c4410307580c11042422034810b81303000410894041c2026000e0340700341d09107061490804200c0300a01000c0140c0400340c41e0307020305017244080041c2002260920041250813001c0c0c01064a81000c40784d010111550341c040c20614600500589000d400d4061600d400c4000311024125051101d40082c40010a906101e8030700010f42c915454802411050403800015136a40c0001d014107142145800755142c3c544e442503800c05c04268042101d5020550124000c01b89803101c0300c0007034803800b4420888106200000e040c1c1c04158060340300100f1103409503400c1c1980d0f59190201926440240704801c00c40e882c2d00d040131416107403041c4441d4 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 699334325 1250 699333075 699333079
    0x607081f030305030601110c150c10061509151d04021c0501060225090510080106060816031407080606070b040c0e010b0c07060c06021207021605040c0507020906 71
    0x22045440800c4562025a648181c0215600009002c41c0d0350f4010254000041c5000061107090600d01c00318081c0140e40d07400400c00c92001c210451801d1040c41004030700300d8410303010700c2540c0d101c00c060020040d88198410100709000d100003558502c400d060f068450f41074403039411078200f282000c003c80300c0c180045540940c0c200040c90010382c01001c2000e034a4114000050190f0420b00d0181c588030b951803108440741500098081c681c0ca116004e102a00e040c6840440e080d1150019070b58000c229030401c5600394241000840c040d50311802040c8a0940342010301c0221000c1c0d83c094003100c41030350600140841c0c4100148038070740503400e5607420400c054015072a10b501611560002c001c299004c075a101e280c000200450040f850f003450241c09011101c2703140c1168000d001359900a02c0c4100307014002c80c811294240001c41d415111030034010300e10031626140c401c0c0025103812a001441c0a240c402000218150400c1d10411141520540750300c0e01d4406507400300850210000c0641d6 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 699335575 1250 699334325 699334351
    0x12030e040b0316091104030209040f060608070303120c090305030a0e030c04060906090b040509190f060e010f050c04050a140d080703093002060706200405030c0f0102060708 76
    0x485951000c0080c580307501c0c5820442550681001380c50029a800300d04071448400f0184024805640c48155050300203034003103150f80c080c542a1034510042d02d0998061b14541c0250b42000040c1608980c0300c2c1641c20f81c4000411102d04000000d450b40d000b5170102800c1c0d40e10070f10205483e80d0103a1004030001000400b02e544a0141200181c01d80380a604051581c944401040000280381d001d030404050742200c00340054900389a15607a80ca000d00d03641075102600c03195480a20000600c5d103001150070070400c0c001c820303c1000050180c1070350100224860300d0800001c200b51030880540303050300d40050080660340d00c3c080940005154070000c1580c0441c01e802001d001030340500041c03103c94480e8030740280303141c03403d0790403002c04540c050140728440f0403812071174054000b485c00d034400311703411a10203448503511300740f080042051b4107110b01c035090705000d2030b940360306614084c104881044040314100701e001d00621605001e00d5040301c1c00340e404940410005809140e07055840b2144101c00 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 699336825 1250 699335575 699335591
    0x30e04060e040320030c0f010506030c09220506070503370c020313080f12030618271c1403131a0c030109050a05040507060e04020c060903031006020712030e04 70
    0x441d0546d0700181c010001e40d8000c00080d901d004080c010301c1d520082c210b020b003960152590201c0c804d01e0000f02280d1445100e200d80c44001081f40c9046500b4581040481d6158a0401c0019155034800d82d8051014810751902d00c5e288294407101c400c000b01300e901c0300a50f50b43c031900d841001c0c0c030b602034410042d80010700040e01a980d100c0d01100051142070700a00c000200c0361107180c24040300061b080c203448810010440070351204203150381394805411401c00365944a4a48040031251045038404080116410b2400584c00041c0f030690412900c01303807050741000c40415202c00300c0040410321100c8040c0002411080d0980000c420503016109850811030400d007401241142155040c84540380400144440720003441031641c00916420100400c4c1401d0701e403607a403520148542c0c010444020b0805580e51101d0301a28000c1a04030101d510a062014009489410031a02040d421681c19000900144000340d0401202c03e0008549015481c540b0210307260600386407519001501c4880f0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 699338075 1250 699336825 699336887
    0x402011d01140f031e22020a17150a090528080f0a02190b0f0408130e011701141803070c080604060c050405221d0307030e04060e0403 59
    0x10f003410b0f5035002c3c60980da841c0090000e00b007880c049400082618030031003002001504140fa10090504202240b040000c142c8002540c610b2107401c100c0078080d01600622080c0c41c0007811540a180b035518241203640c0d0b1002940c1103494640c2d01038000e92016082000c4c5801d030040d00c4a03000d00305411443c45078a562104905980012044001c2944c0051410701d001e41c180b00000012a080340072801018003501e403140f8180b00030309244000c22001000c00c0403c031382c41049074003400451642107801c540d00c1d0030020b00d2403000d01c12010f0408400d14969074500e010b1140b054201c00c2c0350305516850b00c5400000c90700141d20070740c124051200700802008200d016030075200500c6040014107444c41e20f80303010000c0e10514100801440b0050006000f80d0340c40e41800c1c6070f600c400d04002180b500700b0a0410b80541160000342240e048a526110440311000c002003080c0b501948441d04d0402c2d100041c08121000d40c420705a01c60070302d4022400085c401c9061148965814000003c01112061 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 699339325 1250 699338075 699338077
    0x70f0c091401080105010803040609090f0f060b070213060b03220204140103121404060507080403120c33090f120e011d090402060c03040f0f18050402011d0114 70
    0x1c64007999400c01001004100402d0180901601081d0042e6003458608030300600000701a004a00200d038980400492041c001d80c4040311180c6440c4040c0409035440981070140c2c2d2018401fa400b480b1070b440506e102802a015180456440220152550b41e44210888940165020036294034499480240241e900c41c02581c0d0f48040b5200d80203c00c0d451407a1402800c8455100034081c030060078402201343c2c03c903d0942e8121886428013503559a0203151903071081c450740c0c00040620121640300c4075a0383d403002000c07080b64841c08501044001c194583c640d0035101e284aa800014006100f822005998024100651140000e21207002c00da940cbc0380000101d080c0e1070b070006000450644580c0d070b408800b000711004e40c0c20214440300590350110380c084c0b400170000703070140100140c031440440080084400500c3c540111201c226207400c84003032910460320030409201c80020300061464441d10030b5074080c0c0d5050f1170744814a200d905c4500321190140c0c0040713042c02464049044441c0c4144 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 699340575 1250 699339325 699339341
    0x110d0807120510090e0c030d030c20060a06050604030816060902040f0f0b010e031c3b0109230619020f060a0e0307031202040909030c0302120f070f0c09 67
    0x20010032059030a04d542c2004480001035058015800381440d901261004542401107501d2440c002c90b604c020317a04252100038401001c0d041080356003090070003001000c150031303000c1e8201d00c1c1c0500c14290b5030800c0183d00d000718040034041c0752080007040c0a80c43c0d4800c200078118800c00001c140742410740c001030101d6069168002c01c042d20f40e0000d101011442c0b1400855031002d0170a10042d0007a60040ba54844e80c01034040c014116108940d41c4280c00340c074199030004803490400780e484c16170404540104048a250700c201061000741c5819035070050308001c081d1010803282c0c41c10f41c0003c441c0c0400d5103d032086090f40190080008505440840d803004521000c40d400600003400c502400f40c0c507101c002000070090900e000d1044030320140100440d03c040340c152403c801030182080c02d04009110f1944131009072458035001500b01900020480244c0d40641c098810954000c40b400c607241c13080510201c120320007048801300080c401004c3c000800d00451040c84000d465500f0a005c03103030743d0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 699341825 1250 699340575 699340591
    0x30501090c0608100e15190810110d0513020a2607030302060c030a0b2101051018020d0f02040b07121106130f120f02010606110d08071205 61
    0x480ca280c0600c04108404001003015103000400d501c0c00d4010401c42000034055108482012408100b418104049900c000c10005094005e443d25985103030403803240f01c1c803440d140d5005001408080300403a1084905609102c45a5807402144440905c02014000c00c41c800c100c03010f820040c0561141c02c0c080c805000d1300c00764401400840c5440508090342c0500e01005030344118004d10020b0303804186613801040070105140c5903202c40d04003001802e00f0282e003075000f031601c51501c1141905003890640030700c2d0250003082030ba180d40200ea1058401400b405507440d0801c01e43c00400d00840c0d000b404045402c244c0002c210103e10448401d90340203900046401001107120b03000d0001040c00480d10740d00340d0400d0031510700c40c642c440d500c1d814000d000386038900030040503c0034070002c421a02a1141d002da001000494050400741501c01004814001507190400120b0614000c0c1c00c031034003448940e40200030203000e8504c00c84230100000d052101700325000c40d06c840c0c071440c6401107034010a46 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 699343075 1250 699341825 699341831
    0x1050c04050a050f0d080304020a0b0d02270a062304080d0207050603011d0a110a08070201050109060305102406170a090201080f0622090212070806010b1e04030501 72
    0x1c1d2038108003242c08140c0120307205000c100d07032018055840c540745080803944181000e4583d51075000041d090205030b440310104483c000b03080044010035a0040c40815205804420000000340e0482000700d1450700382a00401d2107a014880745001e01c0310082c00c00140700c410002c5240f00260814503421651081c50564401c0101c0d00c00241c040c854500070300000d40c0c11504562408203d15500300d4000c542d0400d03100c602e404520b5801c80f0781c00c0701c44d84014654000760f0703a00607010010301c0400d0840741500103504c1c10002240c80c3c4101d000d09012260403600600c030424041c0e9090006119071100041d0b4400c001c005084241e0030069117100912030307903d814014559148019245440041040004c0c86c50890880010f07a00111483c5e0490000c003c1000d45590b5640880d04034901c0c0000c80103101c041c0c00403a02c44000903005022031a1003541c9008000b5001201240e9031701980c054801c00390402d60040c040b825917040508082004014440d8140f1050715142030540d005ea08152142c0e51 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 699344325 1250 699343075 699343079
    0x402030c09091902040209120309130e030915040509070c1208220611030c07020307050901080d180e1602010c0806031024080d08070e01020a06180501050c04 69
    0x5400e000280400109480501c40d0349040d200d02c54455001c0101d0181003044070754000c1c03c1d911198165000c1c020040d1071480c9000d0f181003d01e43e20341151010360311410b010013041103190184c2c0500b0200c01071950085081040c00010080782e50000c090601101405200005003591035040030b41c040c0740e040c0c4681d076030f650140c24034828014101301007500b400300080600410a580401e034000954100c90700c15900c00301403500344040d0404050011350780070048244a40603d00e00e0051840714402c85c01c451200390b8a1050000c003a109114134600d50f00224040030915000e010301c0440120200b804010064031449070301c84001c8151354607a40307061071140303280090f03409200e4140f0f040030505000500740760400000b5038070500c03005074141b02901c1d012203900000303c9243c0740100c0c84055003000590354840c540d20750b0300c0e8000040c05000840c3c5030301117040c03d0b0080c4000c403450300e010781c0a0500c48039251208009007404c07104840c000514002c615011903000c0c0301d4140900303012902d01c1d0b9524 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 699345575 1250 699344325 699344329
    0x103060203180c090708090a0614060102070611030d0e030408010507020c10170c0a020c030109140d14090f15030a090302010b06090d1104150303090312110d03051b120402 75
    0x84000442c80c14150f000c0c00c0c8448480ea5001c903100d6114015103081c039600d0f0780d45000b0038100424a50000d01240c00c1400c0e0019081a4003001407188000703a0884526503500d55049520300d00d1001601141c1d00300b042441c142030b00580190702540101c6040780d140030b6170741e045a405c40b4400c45002d80142c0007000c0d01d0426180c41d040d00c0014181600d4203c2d8000c01144800c010341102a04031900c0e403400141c0c980ca400e00a00102c5000c9030003d000b0445009182052952500c40001021182c01090001503446009002040300090980c42e0746080801c20814000e11519141c0c0c1158441494102504030a580307000441c8640c03452100802d500600e803070007a094450990540c0d1140780c2c1840060b10984070303c0d140300c80607078200501d00641c007442c001250003484020715000250842c0c0e01c003c424550001d11044c22203200d4421501e400450480032a103108211600c5a000d800c400c0c60702003203600c00d0300045c1d0040030740602d8071407054880c1c032102034540c48142c140c40d0030705820b000c00c0300798 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 699346825 1250 699345575 699345601
    0x303100302180906180f161a031b1305040c11010e0303060d0602160b040b071202040b120403092301020f0303090703020d0302160611060901142802030103060203 71
    0x1250500b00001c02030b060120f03950303858080c01450140c001141c1d8214240000342040301c500076000030f60546a08548a01c2d40500000240c041e40007880d40c1d0089915070301c01100101c1e849219180e21440e9400d5140789131090a0f0321a4040802c0c2d500c00402c0030420b039580c2c3c42041442c0c0c3d010b85489156011001d0f0f20382c00e4510200d2600c91942061040001a440e9044400301140d8440d2005940d001c41e070092031a1054850005800a07044000704010000006600d41c02038100303403603140d040b9001446810036481a40110035141d0420b01c2440020212008095041842803c000901546514222011121207011a03140e4985040c5101d8256014401022020b0a4030040c1d461460100c60306a502c802c0da100083c051800c8101078000c0c54801c1c0404600204c100c185074014036a9a00010304021590300d07844681e0042034081048840c0c144255220b00d880724540c00900c1d41e501c107108160850b6405100404d030041900105101120310083d40a10310902005843e42440038840c40c5c4 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 699348075 1250 699346825 699346849
    0x10f0603061b050d1104090e0c0112090f082a010209120102031b0a021002030a1b0806010f030b030106030f0c090b1c020d020d06020c0a030e06130b09030f0303100302 73
    0x400320400310b01a0403290300000b01c5008074261540850002840a60004a88a1a400300402e285001e540d0900000b01145105810609907145040340e412050300f00225010500f00611308200c03c0c0a0354001000f20014001c07043c0c9108401007038100e90707540c89008103c2720340c01c90301d682d5000444140742c0c54039240356120040e40da0000c506500d094100f29048981c40d4810703000d00c2c200440d241080341d1080010105d1400c80000644d10307400c000072036502410b105101c25003039030444003240810390300c10a10f0510882059640014201940400b60010600c0345001500355403504070110225440b0780c1441d4400e0310031401084901c3c0350011b080e044030f0b010700d485849440c41d10f140030340c140d0105440e40302d85501201d00c408000d12502c006203160002003c000c24a40c00850700c1c00d001400030801d8100d9901035119006401c441d002045483d10030120204100800c401040c01902d110344060060070300c000c0c0c1242c034100501c0b0310952643d04211450039800d21030620500441c104440d089503 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 699349325 1250 699348075 699348101
    0x118231905010e19030c031a1308030604050703200c0c0307060903030503061318060501050103020a170c0f0301081f0c0507150b091302090c04031121010f060306 71
    0x10150515000920030f58010206900c41c01c50650502403014000d010368000319400b00c604402640e50740b4100000401c21a9103a000e81d8004002822064405c81e0078158030740e000c1031052455641c2c10404c001407802402c2d0f14201a0b894803031201c55141c00d07004500b840c59400045858010965541e071034180c070100107a00a17046102d00304102d6400403d5030701035070340c181010b1341c03a69a440003040d05070741d4901380303241458200715148104110600b140004140955801e1017181c0c0c80794015420b900c208044a0005801075614890b2845003000858001d0741c045402c40ca031500d65046440c940d0404e0304a0903003600041080c1c220506044090b0240040c0410140f00d110145e020140ca9400341c403c001c3c0c5411440984d8104880441c0c2c0515a40035000f040c0f00440e0408401e140804010f42c44e041780268402000f10309421a001d055604980e400700c0681407140d0294180a11100e00075913664100c07003280c03d40c448002c428043c2d4105000c2001c2c000980e01d01e1410141d02b0349100c1040c1c85 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 699350575 1250 699349325 699349369
    0x801051311190b03370b010201091e06020c01020d140114030a0b25030225020f040e0f0102030103050a02090105181f17010b01080c030903030105011823 67
    0xc241084100b078840480e490100450346a90750342608421860b0780120b0f41060484a8107695004240719111200000550104010401b41d0708016402c941d0b404001a120412440405290081c5608842c40161180d480942005a044009400d81c0c07c44484041310903129070881350004900350f1410300401410404000361b0402c3c0c000701392901d050700409003036401c2e8040012004041004070701c850300b01000001c2940300d03c0700c40c020002d4200c40b00400004103544006c0e14003c0200d1000206e10750010100c13620014401e08003c01000000040700c118040e0341801c0690700310a01c083c500842c0944050103926250b841088007244050f0030180c800c6446004a940780030200302d50540c0051071703030343c00d00000c1c00c418400c2081600950055404890440403c0390f000d00c1904141e03c550300c21780711a01940c8402461048134002121001038030380c41880100220761061200c4442e4030080139550004984802e00a02da000781c00010120f143c90031284207045041001e00c40ea00c18020741d00e01d17 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 699351825 1250 699350575 699350599
    0x140f1005030c1e0d05040c0f03170d06030f0b0609070807020a0f0318082104030803040f020105070b0109020a02120405030a0201081e13030e06030c03010506130801051311 75
    0x2418a0102400346028080041203034110700200c0601e141c003070075000500c0c1d512050001c01e120080c010850307045824501f030300d5000413801251070144003a40d910001c0c0d0003158a00501d18051a040298080d04d056180c000c0040854039194007968424002c00c850243d84c80c00c0003d0220741c08d4003402030070820001004110b00d0681c0418440413142d406003000d48600300fa400c041328a04103002d0001d0308140401e40005d600000012031580c20007a1030303840a0208801d51020030319009920000c0e0446c0d90800000e00011300f00c2000c1c0898900c14145a410322005407141b0303c507001d00360480f4803600d41c0040c000c59040d4040108108010140039414940b0b4203000110b9228515800000e0600c06480c0108510300e140d007440f020b01090311144440702e1b2507c00740c0101d05406001e42030300440d10f2184039407910305081d805c8911070829115428510307481c06091045660051204c00000307071100c040403c1c00c600a001d814000c001050089115500c3c500b400b407405885034818501c241e01e100d2038 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 699353075 1250 699351825 699351827
    0x605061c09050a020913020f060702011425030c0201120e1b01030f180b1008150a14090c1306030f030e010207031a0a0f200c070f140f10 60
    0x3285500c40c6002294005891400c90b1070011407a0303000f9031104440702045040c2c2c00340010b41e0300b0742d4001c89019058040040a011662281c81d201a00141c08522038245002040c4014940311109944400480a1040541413102c1d00200210002081030354243c00399070340b04d07a1490742102d14040c00c10084a208007180d9440c0f01e80c89406c0a010324074042086242c1c0680c1c01820407180c1c074081448400901c3c01c0100d03100c80c04101c04c44500390480c0c08115984261a842400c1c4c41d01e44004105090078589200d849050007802c0d03450b215112049400ea41d0f82850811303000720b03011402401d00c0c030303182c80401c505596211206001c040c504441000424140c50501c0f6055400d0300382440000f0303080c1c004070f09000c201d0f00050450f0823107040000700c0c004849100340c403d41f01c5c00340c108161030f5113001d20000d030b400c0d410700081942d88110510b441414054001d041d2501c442003164882940c44024180c2c0b1500c50788080500c4240392118242824000c00361790000d0f0080780c00c0402c441d13038208 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 699354325 1250 699353075 699353107
    0x3070b0a08150f1f02010b0d0c06030c021203040611040503030c1011160f0303020f070b1b0a0e0f2803170a020d0c170301031b0f06120e011d0f01060506 67
    0x8071300c03090000d03800c0720407075180c0c001e500030402484040d010741c030341c5c20680c02c0007400a00c02d44268030020380703000a080c542c240702085200c513182400e0041f41ca9a103d50b15658040c040321b40000410314420000020a076904000510030b02d0541800b07440d0141d044107145088402400d03526105040401c020340080c0d92503a07240d51303d103500c100f00514540103810120000d0160f0058451340c16000217100081c006205100340c851215400318a490380b4072541c000c441c6000f802c20680100b1081f4100a015142c138030f1a8100302c0c580038150324011205858003403818110700e009840031103880c50b814070a0120902d0a401c845203030032241e62400c0340b04d210007991180c1c2e26001104114540300403c08000030300e40c2003190006820a81600c82d6101d040c511b43e454464554040400892000001c6103102100410100c40640d02c1d004907003d0414040405004900b007045003555071030840343c40c201c0001c0386010346100400000c00c8800a2144820700b140d80c50740050307228690600c50783c030741c0d081110 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 699355575 1250 699354325 699354349
    0x901080f0d18030503121b16060f0e0303070f0207050901240306050d0b0106120608100e0f0a0b0609010b031302010521250e0904020d0203070b0a08150f 67
    0x3190454140500b186040c4030400700e900010940d000001d00c0c020303901000c2103014003d28045188604c851221000c4452500c5190490380c0819011002040801d115901a6031864092000465101e40c04e40b00c0301d065520807640725010501084240d54000e0341003000f8000b8040503a00c4c4e01040d418500c1088a44413a44429501e404030023400214a500c03a4001c00e0042202406180401c03283d8606032654080074000c010004112841d00020100c90380200011500c141c0081c00038505503410b0100506080c1d640c5046070f10a22150310301c03111041004147e40d6000e119080c415080c15410040e060b10182d0240010741c2e42031042c80541c645182070900a99824203005944404a84250800c0d219000201100c0c48129081040b041d0113858a0700c0c3c0d9080300604560004030000381a81c101d444102400d40103018400010014100780400c42492800101140c0d0b0050340c030148000b080c0d0006202000150024040c44042c45c04c1131041e83d60030038125034075003808200d000461401c0700342c8 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 699356825 1250 699355575 699355577
    0x1419030209101505040e2202010f180b07020907020f0c011815110d0329060408030c0c0901090608100f0204090204121703100b0f09060304050c0901080f0d 68
    0x180441c2242c4200c0030060020f080e4603200e401c48900140e8003504a41161007054482c4041c04005859944018400c0155101c085a0344401e483e55400440718070780c45540070014801094240101228140280d100074650103411640c1d038423144c414000d0a2901820034000e642c4a80840b014a003008910300f10701300030a2811110b1001c001d641862600f034654401c00603c5040051160115840503640c00b6610402d4107d034114198500b00300c0840c0c124542003102c8440100c10520401da0103000020011001000c00e03003420386421441e0708507440321940c03005590208100420608010701418014260208204005864224500c1e16811714100c0e580071950b40d0310101c1c0c11420b45a05507005088540e00442d2287c0d200c40c1002000410404c041e0303103882ca9844010b00b000c40201c200da201e44141e030341c008002c52800c0320015070b9800603841115403e80a00400c802900c07004003942c4994000c4004021000da244107100c4541c1c010b82005c0b240da00a00c80c2000b080c100041c4504600e82a = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 699358075 1250 699356825 699356839
    0xb010509091b1204050105041703010b0405060d0f0c121119050d0615020a0c090e07030f030c0501020d020316030c2106080f0303070f050910030b03031e0414190302 72
    0x2040034240e031103109070820f0242041c003410520090000540c407581c8551701c184400c01c0411800402c8030000d000900c6098105041000180401d051010190803143c01d00100807400510000d183c81c00c1c0c0c3c2d509848800081c2c1c91a403900c41c06032150240c44884000d206406242445400c0c1d900903a02004030b40905200300060f40d12103048680c0d120b500102014142041c800aa25400035100c0424402c16030380ca00b0b1104000c91b2880e503610400c500b111440000700006460741c0e55a04901c041100d0940070b0042e441c14540c086038007070005103a00d1130000300c0140c1e42d2911543c5906525006c1c171680d010146003440c100f009a070842031800110301c04550b074080c2c624031010250003400d0386400c650141c1c01081044c610090002001d980602c465446925018010b454101d50303500984074820303403201c103000f61000300500952004e40170f900058107480ca4641031441203148140d0000a003070130050005002c105200524035008010181141c015581280302075100380e0b80c42c220f0101a00c9038074 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 699359325 1250 699358075 699358111
    0x50406170c0c060f160801080a0f1b06120e01050603060c090a03061a03010c0f0207060c030504260f12030406050601020c030a060b010801051002100e2e0b01050909 72
    0x301d104151a4500d0198080303c1043c0342810041c4c100c51400e4492034440210350145640040c081e1200704d040e614408002c04200c003080d00d030801020302680007500c8603850b0191001400c0502e9131004003400140c0c54011004040c030f41110b048401d4000e00202076403400303080c018181d4022580ca60880c21010455440b40f0031180001c0050019500c01071040e890300d150b40035007002071010010354120072002000344d0384d0303901e4042d117180241f00440001a0803000d07080c0b28a6008488040d0b0030f0b4024034100b400c15803100c000a401c0d000142e609203400e5413400b0040308900082064841d2040c128025081c0c1c08180c00d0388056501019100418654580000601d0f5910070410041e020704002c3c102e48240395141006001400c400060500060b41c8600100f0281094181c01c0303114074540c1d0003030800200001d625030040c16807290030101c0f4002c40d03841d09003030300505e102a00103c5c20359980394000c038418080a422140c0e520883d43c140403060100b00c10b5955000b08282d400b4886904050700e2203 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 699360575 1250 699359325 699359341
    0x12c010c03031d150603070b04030b0a06050d050a053903031e0315030c01211d010c0305010510090501050a0332060d1110050c030409051605040617 65
    0xc1d08002151001c030381280f006404120001c0c0590700800c084c003400e01180c43d400240750b00c03140b940c055984000010401080028840e06050354400ea6161002840300d4566000a2620425550586082d4001d0380f5090500c002800400c645a104100c48068a1400c5480c241605265010780030b500009010580c40b030349003403044031b40b40403082045801901058003d510a03400c10741b41120100150311042100d41070000b240802202e0503103032003100e04910900186d0203000a03000741406a01c8641040c0c140d0680c0f40340d040c1200c6150000b00e408034a0850007011600705a001c184a40a44660307009616006201c4c901a00c5087c41c000b951440100400e030058007803403004003012840700308401c20645040c20300e18010808842012450b40b00e9a08004100422a801902c90522204062032500c0c04070ad48030500300040c20b043d400c0c510001161800c50700a40c2c420a00c1645403800c1000d00810981142050b140c0c0d41841030805043c401c009000407804000c0c0800c600088010a40d06 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 699361825 1250 699360575 699360581
    0x7050f06070201021c0207150b0d0506070f030e0a020a051002070812280801180e06090609010e120316050403050102070309050f01090515180a03060605012c010c0303 73
    0x24441490031584a0306000c076009000b0343c0960107464080f0060314215180240c1c900071035050319000f1a0079034000c141440c1035401442d0349000140d0010903d08001c000807020300002d07104e02030684480c58068400a00602a2150a5014509500081e10000c0144c4e1413400301801d03100701361420a00152aa00306174039040a03600b040c4114480c403001141c42c80034003030040c00704162881ca0740c0e107200a1a242c0c100b448030300300c8998001ca1440030042c00304020040350009400315105010941d500c0402d107850510000351340300781c02600b1040801028031424010340c0541c40795031f001010500030001e10750130307036001c003600003821003144001040c2c03030620610685000d180c2003c000c40d9a02468503015240050030b200f214003414072500d4121056014500f590101d0314054840065215200b4000d2030541c054042c80c8142c0c101e01515009544034aa140030240d4401c01300019814103120015010100109007503011a404a44015881317a90907408041d01c402800d000c0140d4080e45000e9003d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 699363075 1250 699361825 699361843
    0x3070c0209010f0f0f120f150906020405090f0c1206150a051c05060f04020f07060905030d06050d11041a0603070e040b1002061b07050a0c06120c140705 67
    0x7100194070000702d060403601d0703443c2048500005020030a155502d00074150013145109401055000040c1e01c00414041921418a14410726500c0001d50440242c8001c54000180580300c148d40850180414280360079450782004040038540c1052400c0e030078520303403482041c240b000b080c1c0d03804d4040742e0b8544500720300110120508408684030344040200400680100f20000d50145e106941442c02500d03602c00c950140201803c484203603254103090101a501c22031030006051000c100c03c00100702e0a100e034804182c4214003130355650380d91101600694100360801403040c00403181480024591070f620010200083e50041a29101e810b0446481076040320f0311a0400c41c000300b00881150f005e8410703403001d4000c407005c1044406040034481314030103e801440140c0d020f100807034813203901d107101c40380d980c0e0b042d4a0584c03808401d683c409043c0501103034100e440c086500000d000030740d00300c401683c821080c03003802c00810000480c02400550070510f0340c4061100040e0203000d1000030700c50321035 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 699364325 1250 699363075 699363079
    0x5030303090c1509100309020f091504020c030f040807052b111f020d0306080307050618190c1508060307060809031b0c0913080301060806040e06070206070917060c03070c02 76
    0x402100c0c0d9405c05000b5000aa07012407046d0210a100b40003403401ca05c0090041142c0900c881d042c2002c141800025482034050200a110500c0450360f8074604c0303801040901001c40142030300d10301d0311041c0b03c0000c1c00d0404209004449401640740e400220809519954104a08070108900307000480c842844004802d002d4403902a418441250001444441e421160307908100041e5141c07d043d450f40501c801c01842c1c0d41210780852802510795251000c107071030803425507050104882c0800c543d00e00c411b1044814140d0341008101c1c08051800c80411000c0b2410684020710348000029107600c254010700d000d0080c94404501410020020346044500c000d900148040207981000e5503003440c045000d104610800000d00c0c030070120345544041c0c0340e01941441c11039082c40d2023980d000a0090103a50415a40c11000144140c02c000d8a07001e1101d40c1c02802c1e4500300303807074000d000c103101d900901c1c2c2c007111542810403000000900580e02c420341010450b140d84912804035900031420101139 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 699365575 1250 699364325 699364339
    0xf120c1a1e0418050f01060201110f070201031d0703030318080a0f0210110c0d0509060304060b0612010902090f010e15090607052d0d0c030e010c08040f0f05030303090c1509 76
    0x4000072006600c040e00422007402499061b0780d070f486c6d0880c2655803007000440700240078010307d41d0444e40301c1e0191580701d1050401255079415602d03404604a0f4444200e0425407103d030041040c140c140c800d1660390304110700303c0007a0f0320440d210300180e881420540c03802c01c41004034140001e03100b0700c42d070f40344941d090405112034903a50101070810f0308030f4855010180a800041d01d90386008070111800c114000c1e241504513600d9440c1e03d0001d08082c680a604020100840d907048111021000c0c06401c0d42c620041c5c80e440343e40248100502e0000c500e505000b4400c541d042c1c942e0781c2107400c400b0000081d41c410359451587c808220a800740d800005c2c0284181c81d20404544c02c1280010040100c1e140203110202904201568030422010000040755140c0b00c2080464410b4500b285003110605064410000075915010141e00980c024440980e41e0072060222004499070500100411801141141404032600c1d440300b00e50303404248114101400450351044d40000e544180f14000d00c82 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 699366825 1250 699365575 699365609
    0x50c12030a0905100902010e15120c0414101d1203042405040f0b070302150a2705030301121e060207061d0d050d060f120c1a1e04 57
    0x44025212050084446008400800000d8076041c03041d0f00c05c0c0d5405035a507a940e89a4a13045c0440101d100c1e45030507100504200e80c4100030013110029008107200e200b00c0d56158605140d20880c000464030341c0f4441e0010001c4500785603403183e0f810310191021043c408070203230072200003107072846050080d0069000101d00090010301aa510b401c0118030300080d0341901e0a1500100d40e40d10660183c0a00708080341c5081c080200100040c01d20b00d0320a004030703104420400781d200c016220441d004141c0316100c2601102c083c1100703218012004407412042000980303581c030641c588c00140079440c42a40c584078035030300348500418039280159403106001d40000e05800c1c203502039440903a00781d0b1100d0800c101598214112518608000d050f0780203418148070041c2c2c00c440d55404482e40150058491b0400314503050f06800c03003c024191030307080c0503107403d1901d810100c06425501c81c421130140c44021185240c4207200300e540051804201c94142850f440031900e2034082e94220454520502402c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 699368075 1250 699366825 699366841
    0xf070909030201051305030f03101e060912030804120203070803090c15041202100311040807090b060a090e100f06020318060406020a0204321501020d0c03050c1203 72
    0x14000c441e0003a40244180e5075010105401e10f103810000a040ea0300070001c40980d142c010020310303040010107003034005c890b03500c1d0803d0006000107800e0003903501c0d00c024204a07844d0001c5900c00146800702c41c645800100b03840c0601509001072015040c1001d442e5100c696038800d204444106a00404183e2282080c805035a514184100d029004034100101d00c02c86401d030a00740e6080321080e0700c01d80102c001e16800c1c045020700e03694820040c10b846181280b803942c0040e000e0005003031680c0042c0000d900d000100404d40d030130750740420b00982e020408840d00a5004094600350366081404036096226662011060101903012448032022100e02040c000d5011006150303030000d40c1d002d0b03505d10058404101c584d10581c0319440260780155280350050030940c00c80006610902c58070100d500400d809004414880c2030aa042d24104408204a00b803400c0d0700848414804c0c030060081d42c1c052040600220780300700b80074090200200d030240f11200100032501131410300516040e1a800c04002c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 699369325 1250 699368075 699368081
    0x806091606050f0d0b030a06062d03020604050d030c052a04062702040306020a0f140c030406030b0f030a1104140c0703140f16020f120a0803090f0709 66
    0x862403254a1810000140c40748a0410358149004001d8140c1c80d043d50a8804801818445c42942d01030081354001070104038148588002400c0ca049190011184285c642c00c1411582c4148106001c54180078805a1a054151410340d0820355503040c1007091801d090305d20001161008295104411509110a400940d2029012007100d042d01c0c00c10b11290400003a60081d00491781e2030406540d1541718070541400b5000d0b502d240200040c41c0c1500c0e44c9510040c1e03880b03511804042225100b09895283e8440407403401701100041c21030070135a0003076215071248914440d200070981c4603400d0780d03a5039030f8003415205076210040c11902c8204c1c00745407060007060380c4a50140b1841c94902c50120710340c284004079100b40c034080240c0d85440e11590b401d40744100d420018155003041403281829610381c602c010300c40b005a1009500c042c00003841000020039210141c14040c0200d09000090318a0005d6122000360b4020106c9840f651012420340c81c0890007400c00d140da21a2000020700011154 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 699370575 1250 699369325 699369343
    0x203040503190f080f06150c0705210c06091201021b0d09121205041508060a45020703030e07060e1f05040902180a060f0509120106080609 61
    0x102100005804141550f8424107a00031401143c02000021041c4d441c040c00c03640d0000f0b0041c40d85042c086401c4aa891300d030060518030000754064001804a80341c400840c840f24103501d108044401036202c44c0d151034404000d03131540a4503000c65840c140d50784032241c4d084080911030086440716108940790040e8800c1b450903419074080d4a5000158501c01d04003003040d10303c0304a4980c0302c0495a91aaa240c100704002581000400c0c00302113000641c000c181150b000d4903980e201482d0030003a08202c01c2d4a030396405514800c00070300300011620f4408208880801c2e1040f00344004007044c181001c00c99403141e1174218124800145a020103804d030344545085454042200d04440d1100d906452a210f10078045510a800c3d00d2440c04c2c0d09022120207101c4016032070b04509055a840c0c11a040e60001c0c082c0e120180c0039082c00c0078860800307281c00303000ad0109240403000341c05040c80c0a4014859034038498000c042d2100600e168403c250000f0000300b90007021030381035140000c403841c0c6448a203 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 699371825 1250 699370575 699370597
    0xc011d060601030c18170307060c090e09030712030b130608070e06180f040302010212070906020f070b0904020c0703020d03030608070609061218020d081c02031905090304090203040503 81
    0x250341d02040c038403807a008621075400242081038181402410001b0070002403020300144000c0103807200140c0349004950040d407042e103606c140282040c00500c0e80a000800c079504540c024003101c00400c4028518001480030b605002a404102c0008500310100e0006074000c07507401d10200140307100c80010060103c6001480220541e100d030010058800655070110104c80360b41804241e0740d0b030f400703404c643e003062203800018034058880300003010b80901140e407000403400366002040480d030140b102d01c080040d0000078101450030051400e0007400340b500440e014641c04a0070321440fa600700501d0003c0d5030000d1a10344030002914008000c0c00c954066584135000b49840041c01c1c07401166000283c91054595144600c0a07240c2000244107540e031907071542025244500140e00c03010b0300313000100d02070b1421541d81d02810b010220381080081107007203168810400c10403400103640c007000070040c4400c0040f9080d1980b0328614514082d58000042e020b00c00010b200c10007400000404c07401540d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 699373075 1250 699371825 699371831
    0x20109210605040b091002070b0606220602030301030317070f1101090b0928110f0f132a020303160201020405121005010f0e06090405010e030c010f050f01050102120c011d06060103 79
    0x450b848001c07d038050100014101035074480480c0340c1d1300e046800f8114102c2c81180264024403401c1e180c1021300b0307082c5d200c1c0c80580c00010040c82410391014008030b00d500c210860175100d042c2140c00400000b120f0700d40d0410001d01e14075078031741c101d029000316030002d400ca5031100e0b19052851007692140d4100a50550b61002069404c4003101000b81400d00e03103030401e441000380703008142400006000c05081550104880c501c01c2016501c41307080c00a4030264503c001800751103040c074440d4000703005015601c0ca1000d800e0140e500755002081b20340c003040100403140caa03001207a059029018a0b04407590029003d40314008000000419008400c1c807540240110f0340e903030b40301ca20380d591030f0300074003514030380c008009080b90a1403040385405c41e100d9400028080c215004c01801c1d80c008614003000c0d0794481496141202083c014607402290a2800701034551511001035500c0d1404849500a00d01c082030b50b491002081d400b6103d40714000035150021800400001e8851201300c0d0b0b802d000c40d207 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 699374325 1250 699373075 699373093
    0x31b0f0409030f0302070503090406031a0c0408032a070b1c0506011242050909060f150303070c0617040c06052203060c08010909020109210605040b09 66
    0x5050701511212903010707101c200010342079079000c030b000c1d50101300103071141d00c800c004100d069104c034450600154042c1d40c105650701c18031f8046c4141081c01610b01440b9440510050051303c0d800b00840351020654040090141d07a01520301800b1500d074052031070140a444c01c00244d02070000020640403100506284140008880000c110b460076100740d8002071030700080040c0144503500c800c64135a01e15504a4802c850503030010b00012030b051840d604504503900c010020000c0e400d00d000680b40c1100c4081c91403600d002203940d034010041c020b0217031134040004100030656401040c1e03040386024058a0f506c0100d0f0402049140c0d10f84900400100a45880001d0b03852041c1e00c0c60040b41c1c07281044041901d03010301200c0a82081c000c005220030b42c0c044002030b0444620701000114440c400100d11040440801303080b6101c1680000c0b0014103112039500140c0c1d02620b04400c0d41d0718a1500c0c00750394240c03d105500c4041030300c801096140b4100511061001c200503039803040c040c070342c1141d000e04 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 699375575 1250 699374325 699374329
    0x90806010909050610121502130611010b060f07060b0a0b03010e10050906010905190e090c010f081b030a0b0d0c03170702150a05210402010f0311120601020c031b0f 72
    0xd88a1086c207000d020203200d5600080c00d22001c44800c031040b403c025051020003189040292181d80c850808611407000c03e200d010340070301909544200c01c880441c1440300c89007085203180f1a8400c0184103642e22600d04030643e444d45104005031660250264803580c541c0c141071108002a80d92912140342c4c1c4000259a251402d0844d10444e010f035144607141c0d10300418400851080142001003e16920003c6584503590076903500c5054078800030803825200c400050007820000695030708020031401002080022125803446040c0f01c2d10503e03a0300c2e0b441d500700400030724a16041a6121420f04100c41c14016041612015279006600da44005100010000501e00c103280000303400003d544a081021220a405001007101500308640340401c80400200d4021a186242c128464101e0610080d541d1000390b40346205000c0c01c0404c45080d2210211442d80220407601228420200009900b42d03c2404910000c080180481c3d2885003403a8003c2d2140111070700550003544e04062800986c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 699376825 1250 699375575 699375601
    0xb060108010e0108100b0604080109030513060201151701200304020f0301020406141b15041e110d11091003050118120c11130e3a0908060109090506 65
    0x390304c00360080500c2d00c00028030001611b4109032441d4880ea0600000402480a0084d000078a00c65038403903540e140343c8001001a040c007038000c041103a140221100700c1c1140c825081d03099550813520f4a18400404020350302500070f0001c0c40d03207940c444000d01660f2072607150145018900c02c48915283c03061410615080b4011841940001071040341540411594200101034008079841848040008100403a181002d030f0301c1c580c01001382d02010002440300e03820031032031308550280c2c0d00c44207040940c03500c0148850b203d4455100d540c050313411b8002c10840b01040c1d4407a01700585000002d1030001c0300010714a02d940300c151225401c3c010601891207041110b52043d40e0b000509404443e11003004503584121303d10202d403524112901d42102c0d5880b400702d5040ea4140c0400841c506030300c854031900303090446940100b604040d03144d071005000b0b00803092034045c0b2103d00e803228000b600032049500c400250301c05406401100004120500981c201510b05c50203079003260405c1e219021000c0030 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 699378075 1250 699376825 699376829
    0xd08011d07050307052503050c0f0c0109230a0612060501023d05161106070815010c060905070509010b1c020703030b040516270b090406080a0b060108010e01 69
    0x2c0c4081001030740c0140181c0150500442042c0032903464031181a40d0b14603520a48004e50100f000410f00b03481140c0c080110901c081c070040c0140440640500c00a0705c80103a5020b032800b0300740d000c800c00c101c40070400c080c124242c41c01041d00307070030903035421303024062159008142031200d0a1440110340c65000151024140402e0344c40d03d040c82c401c000b002072250001c41c1da88000d120b00d0360070800c0404411300866000790441246480110031621005d4101c07179030082a103495410034410000000e030000d48460380079060300b001818031401d0000488a22881d0740c4010310052521241d20180100010b004042e07640a55251a07141d0300c0b0340c11444280641102c101c0d1583c014400901c084a00380c014011140c800e08011403241001c100050980b002251800d0100402e9134510382c8041c2c0c443c01c015904050110301c4040071708415006007102103603024a80c50440300003854105611542d001d08000c2810383c007a00c0c06049a4900302038803d5090721138a00181e80c0303900100300740b062040c0c2a41 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 699379325 1250 699378075 699378077
    0xa0e1c11120405120a0b0a060806060108010b030f041403040e09010b09090a060e070e0406020a0f0302130302090402150403080a080c04052d120c01080c07020a0b030a09050d08011d07 80
    0x10500c2c0c03610082208500c00d13801200c0460080d00d52810000c1d00c545101c2c1d01507050b400001c00e00c5800d005034585041002044d02e0704220708400108106001c110840341c07c00500c2d121003003180e4482c100740f607005440c0c0c03800303e40f1407000040000301c0d000c484000e0760058400c4002800049040410011050750907105003440d500310007840d0f400140298810820810b16000307032107065a0741e0b80709054504080f00c007038803a00e40008004c404194440350340c400c488041c0c1030450130000c0c1d6090740540c61201d400003d0045100001003020355442d030b100c0340c0030303a5000700b821556961a481c04850310b4001480741c1002c5003181b000f0032007104642c000d403400c1d2500034021881e619602c22141a4280c0201000f1034a4040d10a01c9403681c6c032581c041200441ca80b1005140d02d02c2c0e920001408100000c02c1d400c5851803d00512005960b1405141b04941d1030420f1680c8070b4403010480d00003800c40c010000c0c80ca04c100b026161281e50001d1505040707a4140c905144c80c0ca40304002240911004c44401c4 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 699380575 1250 699379325 699379327
    0xf03050a05040206120702012007060f0917160807030201060807240807050904150617130f05030f04140109090509070b2a070905100f0e0a0e1c1112 65
    0x5e1140501c0d842e00692028aa01c00440c202c3d03200d2250410034584482001403440c40011351030107002060040100c0030703410400411030a8413a4407146c0184182800d40d618003400002c89103c2400d01106240c411a08403c05503910185407501038002d00e880d224440709401212000542c0014012920107040412921a02d0314602408100c4401900800d850240007090080c8030013070b102c51013810074000b83d4009040c644ae04046014003207101203032680b405115440100250045a284400d01095201110250441007458140c1c11400b42c400f08207040d0002040000340c9192030694115078010a0300c0d220801d640311142842901e074101c400c48810f0b480840104030120b500e000a0250340c40b0071541c403c1d03681886803418000051424440301c00e503c0f000e014400c03081c007846102e80241844119044440c900a42820084100d00c540103c01107401d000232030024150300221000440001511500c402103400c050080c203840c861940041d284e01d4900d802ca220004001e1000040c03544c0b0a = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 699381825 1250 699380575 699380587
    0x705060313030c06111b071e120c1205070302010f080c07030c0521041a13090f0906050106030504050d0f1704081b03030115050708041e03050d0f03050a05040206 71
    0x50f606201d11a01c1141d1a40e6036a070100f2622210301e014000143e04800c10380400388445108901d0480213420004e82d10703141a9500c00e150320009610030454007544048840c0e24150704002000703074080d0b40b003a415111100007a000f0000042039800640f407007601d40c8000014441001c40740800c0403500300056100400c600000f190007105112281841242128051100141c00d40d8044036000d0107600c1c60180130500740100384c16203010740c240f0300114856905202101030550030311103080c07140010b02a83d408400251040507048400002e400c914140610759441900030000d003001c0b101900c1c81d01a4118441802e0f1242c2c02046c1c40c103c06544802021081c1400d140d00c4c0386002e0070031118100300708040b00e040303041030642c6508040e5940c042c2d61650724040b40b0750004400740200d081041000c108800c001010a800e40b410b4401e00b2901d00c0c10751800d000201000d1302d040d00086c02c01d1240c044010425a803005d4410640183d5a8040c0a01d0301ca21180300c041e14000c1e50020740c484018019 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 699383075 1250 699381825 699381827
    0x130b01120206180a0801020c0307110315190603060c0f0e0f03120f21060307090509061303050c07030c17010b0f060f12010618080c030706050a140417070506031303 72
    0x1444507030243c010705201c001507550050608a0b80300101c81141c075000890032406000460070180c0701c100094001c0d181d40c22004900c0441c00c60000c00816180e0382ea0301c000910802c1aa20543c080d690001080043c03481101c0081c0c2404000171407000002d40c2d040da40c5a05003090049034501d40400340c028460f042e00c02c04007803141e4200c080d82241001e42400340804941e8401080400111541e950400c00e0400c0e800b07160400100d50030000059040c04144610684001102540301c0c680038000060b9483c140b0f0111101d204030a4410864490401c0100600200d40c0c0306c0b00c2200e030b94000c3c024080a600042d43e09079040d500c031883d84860780384005841c2d4101600144511995031468502d0310600c81340c0f00072030f05400e070407410005460741a0082c295594200e26000741c0568401000600c00c4000025030307032020b03402001d081000c04190415014001c9100800d5502640e06858403240c6941007900580344c2c104d5641164070401d00c0019680c20003e089a000c4c11801c00c1548a207501524 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 699384325 1250 699383075 699383107
    0x6240306111c0209010219080919050301020309060a050115080c03072f160819051e0c031c0c080903120d09060c0f020d03090804080105130b01120206 66
    0x1d80d14404500400ca00800700700760300881200c0d1103500000513162a5444002482d001c000094100c0c2c025120208102060b0010103131140220b04903101c030505014030642400c480010f038803c982560001c00ce0014040012628038456040202c0800180c3c0c0d0703034044146491300c0c071605a00411181e1300031641c240500c50040d030344800c80341092240c1131030000090490081c0c00700c1c100051740c1c010307603030300210320003480602c0c002c02c03414407035244e4182000c09068443c0b4047d0410104900a0904201042070031b103c404011035844001182c03034889240c7c083e454200803803045120707008030100100c42054003140c095856034035940341d030b01d241125650341d0742030351080f1030143d81840307200075861082c0800c6004000c601001c400200c1d03200000c0c0380c03001c15554940c02400600c003500c4200781c412580000c00c031400030702d2894040350064050030301d81c0c0e043c0305680010485508110070041266806c519006880d44940c00c070351385680c2d94401d805c101802560b0000d41c01001000131603501400c805c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 699385575 1250 699384325 699384341
    0x307032d03051510170c03010b04061209060612020909030708090613050307060c2010030902040207140d0f0302130b361003180326070201050406240306 67
    0x103000303041841098002429901404c2c2d440300019030701600c00304108420245141d04100011a40750655061004a000c4c501480c0130700310800c07040c1e210b03400c0129102e4104101c00380d0410b8040001e02c2e2990341d41c0510a00c2c80300c059002e1301203075012a08000000086070a01d0703402120250030209000200601355001c181104085a002c0e41e0210b00b0b90303814484076001344010b4903070070303829940d901e003d800102c6040601030884a6903c0188400d45890400d00d543c03540d0341c82c00013844640c41c40002c00234003a028019096660000c0d00305040c1d0b400082801c02c658a9131600f400d040c85207007049060344a02c1e2540410301220341800c20010521401802c00d141c4c41512403104500145120350042c2c0003500b00700f040da0541200c094a40c200f03030340c0f5120610040d00d0144040314040c10307071800c28400803c00604001070700c0546155160618100c000400b901e0311051100c1c04c040d08000c0c041c0405031015158146001078a00d400700b1500b9110175450299140340081c82c0c80c58803071000800c10b0b4 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 699386825 1250 699385575 699385591
    0xb09101224050106080a0b0d02190812090108060307030f02090c0c10060f0b040503070b0304061e09060b120d140904020406030e010f0b011b05150403020307032d0305 73
    0x603000350782a5041c4411040040e51400400200d82d032400b00700034a010030240500f0a09803401e503030501c003034076018060814250141c4481554062042594500d5186070384160f4143c0035440b403090601d2005d500903c406c0c0780c246d0394450180c1390a010107845d004140700c014201e660746441140141419090300d540101a0180e40c2d051070340c0c0d02c4219080030032005030b0160b0107039a180107125001c1c1102108000c0c11215589504050a1402090740d890190040708103c440110001c0c0801c101900b2071548260809801c050b015003000240002d4080080c003141c80d1400e011910301c1908003108004a0603440200404c0441e403e92400e40b0b81c0a140070142a698404006000550302c2e2800200000c00181c1d0300041d2101d0320a0003903003100d02c1415118002c608008452030580e030702c20320091041e150401c18201c02510342c81c049150250207440c110303a50014504110502da000300140080c540262a040c003404664001211440118582109200c0c20000072044451280d40f10540c00355103 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 699388075 1250 699386825 699386843
    0x40b0c0a020a06140d0e10050a09050706110d032004080610080115180605040c2706050f0f0408070e0a14040b0a02071a090703030212090d12020109060f020307030b091012 75
    0x101f40f07401e0055580446072100183e8a400c410410846c007048400010603c5103083c820a0110521098885021903c07c1040544400110b4448800004c5900300b080c600136000703a950741d842c480d0503110b1901b2035140c2c1c1e0440d40100006508001809551040b0010f81c6140109600317103080544031014103845840d129580e504041410740740c0c0c0c8100d0608000503102d6143c0c005a0b403911440b5410065410554108001420489260003c0c00d076203840c410356603440d8403050405100d00b518003d5504c0f4102903c10f14500158800c511b01044e40200440001800554150b4203410034860701a0780c010444921240003030300075800c03940680aa54441c0411650407003410040b00da045805441002d50354001000800400d5010855a51a01560300034035051880c560001101d8a1110a000d0084c51513a48488041c510039440401d040c0d611050410882c40c50104400007500201e0310000424642001020310389004e078181e40c400c800d0748114044e403604100e0300190b150102d00c011034603008 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 699389325 1250 699388075 699388093
    0x20915040501080715050702090705090d0c0612060905072001020903120c24010504091a0a0608010b03010b09131a0702010b150a05120c040b0c0a020a06140d0e 70
    0x158a004442c0204018401081454100740003840c0a94250a125040c000100002e400603180c441c11540d2000b010f007882c640320790140f0003040c0205544c140090400300ca95901003109a00b00c10030401121005a04200d000c0e26581d0384422a44140c4003080815508a0407903200d9610541c00c81e41095014005401c258002000c02e140240441c00075800c0300c2c012440c40305102040240c0d2081e1400c1030b407c4c0014150b1518030080010040c010b6078000d5444008081c24040503941500c1d1000d500c01c08000c05161054841c002448140034a80d1954206150440c3c1442c0502500305c0307000c80103191a07881c1c1c5800c009100074012000c001c40d880664203004541041c0b119107124070500c110380000c034458952104114005480f610512902c80080c0840f203603456000060711040800007100c41c1c2c1d10b1319803d840d1044d5019582c031501c0c180da80000c010040c01008a50807210394829294034401a4403420265000c905403003e240144a05100008548a25070007002e40190480c0985142d41c0c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 699390575 1250 699389325 699389329
    0x804080102070510050903030105090c1612080f010e150d0c091d070806010e0406020304021f0908011b020d0c17031003050c0904020a12170a09080d03020a020307020915 74
    0x81c000d0141070321940c10007449604007228038012143c6c00070800018520315814034000541402e001b800228207608080b404003001000b924000c110b007604040e00c100d000c840b0390002080b0701c4c01240d11180c4800300070000180c00101c640d80d41d000b40700c50241142c05a074001c2c24021072410b0300401b99102034070014001003021091255400b00b40c100d0b0701508403a480c4409030b0b8500002070b400710f01c45620400c0100290b29648201c1d0380c000c0d0b031010700581e40e42c90b01d000054000c0e030303155000f207101d17222294034202a80c1c10551901c1242c078680c0007440025a180d0104040300c80030742c254405600060035007811588145c88011840b80b0404040194448030b071850340043e0402c54a8005560b8065414810b000080181403d198000c03100d05049103480e50225428010522681001c06000e001c010100203600440703520450310720000c983c43d0b00d0748600c001c0c24042d2034031482040303002d00091002034503c24000c440d800041500203514100ca59800d011103990b0081031001e510038081003080d025 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 699391825 1250 699390575 699390577
    0xc1501080307020a1a070227010608150a050604091d061e090d1403070306030203010906090614130b07090510030c180f15110a0c06120e15040804080102 67
    0x3a01401009685502c807501c1800070645450b0055090490b45525070404904000c04a6203495416176140030010610001c1d000444140052144182c55003000811b05591119111b032240c0d40b6042600801c04402c824400069000d0080e03e401000030841441581840c0d04010900302d80c40c0019104500f0178984503003010400c3d5202c1900700d00c000400c081501002a0b140e41003102d075405003101c106500713000b80011300c02021410b04801c0110000c0d11850082d03000f03400440c0c0240003404807010307501d00305005010301c0324110b49151030700c60f103581d0082008400603c0340c9074007000200003c8070313601c036061041c90040650b010040d98010201d03440e00d40403080b003042116601c0c08500d2104540c405844200c500003900051300103550100103c1b4520380e1a40c04030b0b590307035042101c0851f504400b11440d04400721002c89610446001c00c04010014070100100e502d103685180c1100c2406180c00252070300e012410340c0d46e5200d4a4a41a941c0022a0258009104403061840d280d5101005070036 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 699393075 1250 699391825 699391829
    0xb1f050c0712050d031802010c060612030903020a0f030b070305090109020604081b0f0d0f0501020904060803120a051905130209011d0618240418020f0a0312050c1501 73
    0x5100c20b080c000d02000001c00038001040840e04051100c20f4203004a90340500d503c18001c2e0400004145403820b0003a181c0c00b05000e40207414040c160381d04c080c200a00201c017070b88000c9026000c10800000c400c060407517100309496020181c5140703030300d640c5c0c0100e01030f010240103510103550f20b402860040c0e450750010001410f00b1009400c0f1140085070080c015582a80d11500503220701c2d24401407a903502041c0c1e0f882a41c404400c1c0d072455914102240280903046030160480d28100000c5640300000010303210941240b00e03480403a80e40e018400013519400c0d03501c0c040c6200e60743c03503000e402e89580c1c0125501410f0b1803c1c54084554a0f00040d841c80402c0c0d2103020003181181d00c4040880340c20440a40c001000e8031582d000d1041c100c0390300a25980184656060a40c8501e0030388050782480311000e94150080040c400300b071051208003218a16841c080f441881c3e880b4905a0504001c0040000c0b40d400030b0265100404a202c01d440700d9020040d400054021195406600c80c601c0020b0382c0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 699394325 1250 699393075 699393089
    0x100213050630060315190c0e040203040f1511030103080703051c02032205060411060c03131418011a1c06030203060c0408030f090a0b18130b1f050c07 66
    0x2103050000515040000c05d039150b04403500f910701049400b2140184460001c00c4039600000c0090520300d084902490b01e407003240d171050001082c00f052140d0a0841c080c1103010748051100c085420080c101190807003014420f108900703000420110742c2002c082d001245c001e051440c50700d102c040004001500301880c4a150ba58080144504414040140b210782c0d8050140460320707082a445458ad90600200014466003c031140700c10036869040c16141411641c40403280c440114204000034403c1c00d001d03d404803210740180d24140d151950441c140c0e081c00404403407580c1d00f0104e0b0380990300c0c14070700c034040b0341c1004004840c038102051200ca0503402084000260050443c03040504044018040120040b8180401e0100c108003000301d400740400c0301c0700955260500404103103d624160700010801d000840d05440c0c4c3c40c0407042d40c41080c00e04841e070503910110800003108561880c00b1194220142c036201e00103045070144210766030b400300e0510f2410b00c01581c018900d00001500015 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 699395575 1250 699394325 699394417
    0x7022b05060c2106031e0a03080601080c090d0219030501020705011b050301090917030a0b0a1502030405011808030c1c03330803030106111002130506 66
    0x6080c05014040c10703030404026207403a494407807540d01900f4610340354040c0c6008611002c001c904180c2d400c114818120035100c950600d0080d40d507030398944901c201c80b41503001c90000303000100150700c9135100c039110b01142211942815150024400d01e0718140386c08a802c034089542c03001502148442c40c0000754860400942da84400d46003d030f00791402000e03030b05070007110400311032001c60f080410789040d94480a00010741d000c260070001000112100030340c11003407000051200070551504044800a000d40301c0d0f1030019039402010008201c001c04610060700180410b1121b58070800c160850644405102024561140e04c0c0d039085902c071321502031041e403102c504101e50f1606209070f160060f003107013000c00c080340039560030700d010042141209003401c003a12003404810103c0070490000c1e18109040741c1d2a503864460140030b66100340c002e03000d2417151400c1d4a0040803c0e008031031000100d42a240d41d210300d4001031015a82040c810400004a900b00039200500c1010140507000c2d600b000398 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 699396825 1250 699395575 699395659
    0x905031c2303182503080c031c1410030302031812150403090e01030c0302210a0516051f030903020339012003060d02091003020108070f0e060702 64
    0x103180044000c9035845134080c00030704403002c0026141c00001c490700254016503c41c82a0b58442c118410000ca0600d1805000d45407aa0181180e01141100702103002411980e02c8600891020000c82d210090041e44200051951080b40c02c1c100c19419401500605030141400c240c141006250032521040b82d60b080f0400c024940d00800d660001c0c900354a44400d20b5046441e054034851540c007020b8010041108120300c0d04c1a402481d00c0c0800318130054404508551511030f0302c40000f0700d40000d400040c800c0206082c07405049180c038454030304803412400001c1000a034090120a5015025400706215010b00c80d80f010021300500c43c03035402d08d004a40340c070344040b116411820080f484540e00d41104280e40001094107039040603503c82005489603907060008150f0b41030064003d4004021300c09100074140034180c0721050b00d10036204e2848940e504c84040395000000004440040c00f490900240b90900100402d001d5002505829101c4140c0d0001a181400701d190b841e6081c40e51024 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 699398075 1250 699396825 699396871
    0x310090c0605130b070f060203160e0f0102062d04080a08010b16110a170106031e02010f080c042102030d030b100e0a031707030905031c2303 62
    0x4444003514403802d02a040c0301e031490080c40c03000c19a0041032100e980001d80442804004c0711402001d40e1310440c155030f42d00d403418408000d4121111a41d0220f4600e20b121586803400c071141032910340041e0700620103555905255408c1c1c0d026840544264001c000310a804814544066885a0300400034540d403580d413040c00421540050b0703c00b40601009121f038100415001442d84c3e42103800242c0d5005855400d000149150b000d5401901005210307a4134840068064028004403800340c02d490450301c005400782ca01ca2103e940d0b000b40003501d42c1c051881041d02800301c070b580080b0120101401c10751101940b0006040e0420f041c0d4011a031105180210f25042102c140800304a1505020741c0d08660080740c9801e4091403101d042c03000380c4600c031066880e10100e000046800190440800180303420b807100580c00550b00394000740381001d020580b07040005184601c9a4003041c61150440e5800c002c94041050010302480d8039001a0f40c4245201404051801240300400e098008018010 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 699399325 1250 699398075 699398093
    0x1061d13121e0203040f0b090307050a060c110f0619020102070c0f15090605031611060f040b0f0c070809130507110d180b0a110a080d0b0906090a1802031009 69
    0x6210b800c65204101c24812240842100d404440c00591003a86503904080001c0c1061000e802c12a008804070100103400c980c04010850558050b5011107034041701201800403482500d41c0c5540c00407000c006800e410201d102a01d84540c0041c8001401c10245558140000105900082c05010080d8060110000c40c2d03001924011107404e0540005280540160044c04000e1510304401d0f21003c080554a014040420035095100c0988201d8138240324821506042030360207440f411950380c002256098001c034028010759401c1e20b4070381885010740e6103100b00d0344444500380d0058250f0b00e544056421354002e540c0140919100c104100d0540a122840e2540080d0040d0070070001410b20154280c441035004166045500890390f9014182c1c01a9110100070140700d2041c07088212200a00c014103016003094412850103200d80980e107810419002002e44041d98040200400b08146415a52002100c400d080d82d45060240381500000c3c2841e20a512030704d88541c0320800a0100f2501c90307 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 699400575 1250 699399325 699399377
    0x30103060b01090b0c0a110303070804030c0f0803120a02030403050405210f0a02150a020f0706030c0e011d2b1401050f070507030c050c0406090b0301060801061d1312 73
    0x680d040d01780725031416403e030f450000d1070018280b10f51032003080045440900490309401c1e00b0498069407542d8038604108000c80320720890001c2e035041d14003c901d40001004030380c030803440341d5450001394913031100d000c00030761001d80103c06011040000140b1500e40c2d040007030040c1d4a2503e02003610450750715442c10000724444082564010703902050040e07880e2039441107055a0010702e03070345940144005070700d4086480f00d95215032103422000140b59615800489641e040c69540c1701c0d0b00343d5187d0054400c0d13021012111020050f000070b010031814000c11a020191101c0340e40d041645040c451288580c00c17003401910260104510391195050074041c170b43d0411281c140400142c600390000030b10601030301000408005000e000f44080c0501040b0424140c02d000f401004400c2e41e42c0c0c4c9690040c00000c4405029500701900003806403410300c5488103d031084402041064404406d1841d946c00041c1801c281c40c0390309038050301040851049100e501010f0300c54440c42200402d428100c0b070000 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 699401825 1250 699400575 699400589
    0xe0a0b0c0705150f1e1611010804080306042a0e090f070f18081b0112060e07140706140f0a020301051c020d0f060c090602010203060f0105030912030103060b0109 71
    0x440403540c86540480202e913903080c41d5070f0503561141940d4140030010103401003024281a000b240c0c01450f80130300e0f10003170701d001d01c2040004400d1000c50015114a070088402a104400c00d00004d20316082941101c2e01d440d8000010302c02c500c000716001203107481c03c10342a50000d1401e00108200c0e0030980d102603000181a00c14420515141c40c00401c00d540d044c0d140030400402000892030001c0340c40c0420b000d00000c6040e110701030200322076629130308140d9007001d00103620450003019100f0071703110b80020345007010300c0c041080e40c0d48041600d002071a080000d00c480410004680840d055200e81d842902000c405000c03281000c5003650030301e00010b00340c030703080f40c2c41003004002c0c642d215110400c6117640b4440c0540519030320300000e09400a03015016000d40441581c002c2000b0b50f039072002608007580c1e01d807180c2140c1c444008030f080380400c55140b80c21220700d21080d0404c1d0b004201075a4000b41081c207c4508120314000c075000c5402c01e83c0126112602d030002c0007020340c1c2110850380075181c0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 699403075 1250 699401825 699401839
    0x17011a040504021c23071206180b0903092706010e031e01020702040c09120201200f0c030d0906090302040f0b060403290708040f02011101140a0c0504080a11010e0a0b0c0705 76
    0xe21f1400300480c0310a000051810340ea030303044200d401d04804c0b04080b00d10f4000d11040e115144c180340e4281c50780c3c0032102c050703c22038512030100d0709c3c000d80c00390000c00401c000300d611840c2c0d9901001554000c40300000d2651600c11313a080c45800ca14440c03928140f10003044000b507106c031024070501003598002c524002c14031240307c5017484602c40c032550004080c2d40920b00400107200c081701200313618035102481d00c0381b40140203051201d0000010003c0401c14154120785c07080e00b00c0a81240d55507030f107025403000590b00741020800b520b07182e0050500c4d4240004006a1024001c0000700c01c0c0d400f6520440b0a41c44083c002d0784030000c0044031700c0c20b015030b44916001526003220b0003400301000520042130842c0c00d04420055910031043c82c02881c2c1c650008021800758002d0030113000100310382049010381001c5144480911035001d41d02207904110003000d40c15081c1da40d4203002907800c07001e507041180344200e2030407a9451340c03070010003800e110350030075503400c0003190030390806070282c1103a0b001d094 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 699404325 1250 699403075 699403079
    0x20901050414070c03030204150e090a0203011a28111506010e1207050901170118050d080a1410090b0306090c040f0207020d050717011a040504021c2307 67
    0x440603840e8884800c1ca01310000001c80e1800b900240a19002100503400f03800c4c400f4002034000841c5a9007020454000c0402c0c0d6500c1050410f81c4000d001307485090708045102000d50301c2c8600502440c0a01c62003c69980c844030004005007030b10402c000300081d4544074400c8a159080c0002175420144d00b603208202d01c2c00100103400c10820740d20050056004880305101d840c41400508040d01d0f0060828526503500c456140b00c0301c03c00c9038020700c05e51070003c120104544032030310b2642c403643c42800b41c14641d400400503950210020f110041c11071705d4200c00b2039a0380b0900a403070712070700e01c1882140f0141e040c512403204942c4802d40d1203000358000424851400e01c0040c03031440c400d60495003c210004440d848001900800400135040b110304104a000c006002c900305040d070300c21101028001400f46d0020342070315031500e00c8c1041040c1c0010600c1850800380c200b25030040c0060480c4143c0380341b0411001c2c440c003507418156419407400c429160100e545a01d00502c040102000340b00d428 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 699405575 1250 699404325 699404351
    0x90c050327070b070311010c03020c0f07080601050d02060c060103080304061d1c050904090807060509240402040e19030f0e030318040e0d020d140c0607120f180209010504 75
    0x46203401209810400803031340508161103407030000e100654400007413002d0792094002038045d4021200709035143c06800d80807582c40200142c22000c0390b85100007058240d1a0106212500618180c00d90300440c08229004601a0030041c0c0343c002c62042da88c9580e01d2602d41041d10840e0802c8090114038960980ca444041c1030020b2000784420114142c2050003a8035001030380c0c14810350207119041750030022149d0070310059001905026006101c140115564552800d440e040406007960349a885076004142a4204254460380700e0f1001c1c10000740c0c402412040c6142c55401440074120f001c1200002041591021003010500c2c200d0800c1c61401d60f002d00065100c0c0204d03c190004140c1c110014401c0e80c0eaa0b03006100d803285a802078a01010440b03100a4680b055a9004000301d17030450031000c001415442101d4200103620058003040d181c0d25000c49988914080c140411902d400064030b00146610480c3c1d00d0600c2e0b19000c4000000d10b105102803010305a011511907450001d11640302 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 699406825 1250 699405575 699405583
    0x9020d02030d0e1e0105030a05060f0d03020a020a0e0702071403071a09120c0607080705010605060406080a1b0c0213060e01090e0f010b01390b150f011d0109090c050327 74
    0x141540409c0d95907401c0081900314003403c0d082c1e0341c40881180d6030828940c0101d03411507194003d80300000f03820b8403204039160180701a16101c0041e0b1001c0d6081054802c03e4500500c106801020345003403554070302c03c2040710164031650364110031000902d0481440c010704c2d1010700d40c0c900740203401c4182c1010009a554020504050a14000014200c08012003941b0000c05060014003803919141c8134030004103204401c96641c80d02c1881d1038007202010101c02e107103142c4c40003180e8407001c4103036065092007a00c1d170713a510b060b0b0b4040391103010202d00b0a0702507807164080c0407a000d0000300005c400f4a020710f05042a4a401d01c240d00d80305c00094140d034840d85080c0311101c030b6280c0d6440268001d2803451055030554411050b40e5105100000f0082d00d01102801040e0442e80c9009800700e440401074094405400c15000c81d2005243e0f0000d040c4001c5d410201ca201410310360341c5181c2d80c0c01d418040e14000815039002403000020000c90802c0c8824030b401c0340202101e05800e1500300310501d55a = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 699408075 1250 699406825 699406831
    0x230411040512211215060d090303021204050f010b0a0b1209030415021006050907020a0b060d05011509050c0f0d020d0b0303130608010b130909020d02030d0e1e010503 73
    0x50001c220320342c00425000c01c03510002e01d0b074070900c0024010080c030b40d40381d542e000700364940c1c1020404400300f40e0800c1d803150b5aa46100000745420716007003c6c80701c504c00400b066001201419020b202d8821590800e03003070340e8800c81c0210040d040c07540929030340f58219002080880c1c861400c6500c02d1202c2015102a196900042d00d0280303c903403a0300444919500643c0d0140d8404240c5081441205901080400503202212018001d03030b40c6903020415032410807114000168402d0701d1200100324400745094020381d01400c41040611540c0391242518420128840e244010b00010800c01c0d440740b05140e4080c11140c0c816050500c0021002c01c18800d10703244292041d004501d1041901c010b40c003031400000020102c03681c070401d0b090181c00c400c1a91003601d0101304094000511280700004840004c000519004c01c041e0600c1402402403090301000e81e0000c3d150076541d8010b03201040010f41c885069126143c000d040c950400c07807035048400340042410150121012039136006019a50 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 699409325 1250 699408075 699408079
    0x80103060c030b330a08150118030f050d020105010f0306020304150f0506130e1e07120c090b010f05090906181311060702030606100908072304110405 66
    0x345109192000c030050310031503108030b51011208070004100e0402e9421400507843d1051000394410b10b213000300080340140c0310b9034004030703842c0c100160164040c01103941c588803050514502031840c0b0fa00d00da0203c56207801c100c9801b020742c04801c3c01d0100800c4865a4103c0920083c0101d41c10704083c0c0d202e5801500c801002c07030f0b4010000c00d0402c04840c00b50b181300e6885082c00c0019102101492000d004196561401103040b039070441c41c0d1072006d0052005207003114008111701c44c51451180d0b0405880310340d10126010302000407903145030740100314081c68000c2d61545207050400051b4400c031855400020705024413901101d54032131b0400309490510404039504070f4213039a4000840d50744c140c070301d0003e5007164400c001c100911101411001a0500440c001a003001594050103100d11400c00040e60662001002500910b8496a1050030b00d41e40e00c0c080301da403503450154502e080955041944000c401d80311007112358031a4004280d444c1c0e021075050002c0c07070400140004510850103a0780c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 699410575 1250 699409325 699409331
    0x10f0503041401020a05250c0b07080714010e0f030c0a03050c16060906030b0a050306132406140303130501260a020403030809121206010905040c0206011802040608010306 75
    0x1d401c2c040d80301d02c0e040c01ea42140d0002c1d503913880040070040466109003a410040e1040906601440d41e110170034140255002c0d140004403170404d0180c41da5030b00b081d00c0880700e07640304000c20341c00940114941e002044e100c200102e0203520200140b1b060844c3c581511800d54014000c0305c0a040700003c0c02c5001d00d4040c03d03c4e954138410440702c1030030280e441140100607103241c0310018041d680002c04a003240c03115901040781850031000c1001d4511244240c90b03043c1d01210100740400e0143e0021074003248190039095480c4e0761802c4151074000b03802c9442801356502c01c1c0c200807004140030380068008044000d149420302440ca110804501800b40c00e040000c18490300c0000e003810b0405d10703d0780314602180101403901c02c100401950141c00f0880c0058080310110302c210800242c800c85a80c0071135459418242da500030684405c50080006041000001001a003602ca51240e00d0f0f0505066001d44115130411f013002d0941a042d20790842011310400007040346981c0230401d281900c1d4016008 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 699411825 1250 699410575 699410581
    0x1c0b240a0e090709060306060507050304052b0605010e0612100e03041e0510090f141804120806030606010c020108090111040609030309210803042409030305060906010f0503 76
    0x4507581104119559040a02c482c2880070709a0841d443d4400c541d16980c0c2400440d0321400122518050190010525803041c0310034072403890501d0080039903500000c89400704604a004e2030488000425050702c02650341c05c010300c0000c04000c6010b9004105945a590a200d03112555036615454200c070860255206403c5105c46805e2046500130240c2c4604584804e1a14400000c0960340d0f100d074a00c035119586c40351080ba4010815082116044505192071505c3d140110b41c141d040d41101c07540c0005c1c000c1070504a4030117000030078003840c007803104d0441c404a50103000c0c0202c0740140c0010310a0348000d04100450383d00140043c9026030a1a00340401d455100005014081410110010b850081804588250f0001c006011a80030366180003403540da5a141c450014086c5621500341d1564401240215030110300954119100740085402c1c0054140c4107001843c45c2902100d0310303030301c0317803045414140c0c58050182c105500320b44020013414160006031200e2040400c00c02841004400 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 699413075 1250 699411825 699411827
    0xf070320040c20100c02010e1b0a1e050402040e090d080903030612010b043303051c0509030616030b040509071a0712080406060b0903060601231c0b240a 67
    0x500d5103000094109000004100c5c2c80a1302800400d604581c05210f05a031110400072845800c513628003000c1e05030316145050010500c100c0d2804000021803c0c0044000256510b8900c000c100901042c0d000c80d005050400346582031080e00780c0e00c5020499148280401c1242c08000c0700d400035022200d90300c48200e048003ca016022700742d10150b02c18900b02e101c0800442112901012802c080e1100d05045000c0708000c40030061400040c4c0150310080300c0f00d07407814840e88900c201801c00d040040c102080500002e25202003100c034a80350b8001000d91140b026054040c20500707083c00c440901940c9051035034140c1d60040740c8036000c46000d404078034203840f41e025000c80b0a01038008035152800616001c2c05049060155800c850561401500188009503d800da03040b000c0020044c001c1502e400e40111440c50b580c0603680701841c0310040c3d6400307840c914001040981c00c200f00c20503041c030280d6101400c9642050405d40500101142182e01058455a12580540140300c86480c1c41180350 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 699414325 1250 699413075 699413083
    0x120c132706080303010f051e150c0105100f090209061918080f060c0c0604170c150a0c02010504030203070f080409050c03040606090c0f030e0f070320040c20 69
    0x9032080030614000c030205211074040300a606940003000b100c6551035072402400301d4080540c00402d488841c010190040345031103014950401c41c0f2092082c240104403c1403400c4900c10703201c9185107228654100035244140c80707420003c200b410411410031007104e010402c0b03880ad010110604e443c0d14452504030350f0280d544000c2d100449101e00c3d0b80240c986d900300303545070384c01c17a0403c3c0c0900c01d150014810182c0b090465400c1005400a060a9291951603000b41c10940c3c0041c00088018003c000c02d03d281040700e9005140344046460482c02c0003903104084030360403209081103906140400000c60780010444542952001505400741c03800d0034510024080c980050b201d00d0b080c2000d000040e004c8001450249000350000c12a0716a15010744045442c030354400f40200c1c0c18000e40166a81c083d42c0041503841c01c090a83d40507032072003030390b00e07040c1203543c0c00854840c00c4c128058521180c400500701031b008819102004096041840a8001001d414541c943d240360021540c0d9912800d00c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 699415575 1250 699414325 699414389
    0x100801020f0304150614010e15210604150e18062706040c0b071a041b06020303060105070807030e0d06050a0b0105030421170c120c13 59
    0x85440707091503010303203803158010f0f182a503c00c0b02c04d042500d40c4081510825040b40c030b94002e40e1203940d64850064951207031542d41241d014804074024040c00507e10024103c0300d04100050846004000c1d0410744104040e11880c0101d2811340805041520380e02004140d8140c00394070012641e03191100c0780080382600d0301c40c025020341410b004d03d60f803c240681c1d00e80711908200c080d51145034111a076890200301d81c05004440415801c2001c030700401d00034020503002c0c400c0001410080d801d0840850001d4604880c880c83d005080814520f0707031424800905150720103107146090100000b016401416005400904002004802c040c0101d0501011210180c01d002d2500b5460400c50014401294948805403d00902d40780039881541180c2c82154805410740040b081d0810402000300540d0208080c04610016014841c480b0404030780b25000701100d4070f60320b50041646a902d050054010b10800d00c0900110b01c0500403004040f0907502e24441e8072140740d0540b15084000b28043c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 699416825 1250 699415575 699415589
    0x6011b020f0415090c1806030b0306071b0506040f0204270201210509010f06090e0a080c010617030711150919050a080102040f06090b030a15090507020a030306170a030810 75
    0x5c540b80c00c109030072003440207019070030751031103542156103c1c41a42503628025410382c0c15005070001403c2c49010310510034411115060426025000d65292864840b0a88040c0d60422010000c1c3c0c04601d01030051b010380b1314a0f400082554900c902d80e201c541421a4002070600c41101a21004225010303003408801c060880e0621680c04c003c9002802003401459113185a030400c0f07800700f4440320710b015404940d288500100003080594075403030195000040151859501d0320b40025010030032084200c44d421144024503a550b1507031600706030740c0082290540c01000310b044183c030307800400015075000d40d5090301d9801d14070030a00c6030707510f101000d030b0005503025945210101c0c8140055010344203881005034541e940e06c0d2584020782d03614190707104020340d0200410010750035180640000c540990060f001c40401c907116010320069400c22900072006911114a00c001d150b0306000d40c0d0010070000411500c86200c01c0c111035103035140000090709226260f070200305454030b201c1850f401041c0c0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 699418075 1250 699416825 699416831
    0x301021204060e060708010b040e040507121209050907080c070201030e120c12190c0606090609050423030d0c0c0b1806070f0509041a0d0b06011b020f041509 69
    0x1898201e0043c10201c1403c489032245100003000d41e802110114140e03005240b0701030500f40b8107000100c4141000340200ca0901a940d000203020880090b9100d5a51250072952250004244001c001160b2030340101e11031001c0744144880719411110b85034011403051840e0341c2c1d07000c0600050340034010380d9146114622482c04088c505a40030b0700a0102c0e51080390a0703411518000c1d800001d0780c025140700191810345000740c84245406141c450010500c0390501054441e5242d44503411900d11354000a14980c03620104010402110003039071468100d1000c0c4043c00651040b103990b0b074000d10703000706480c0303990f14149004c55000722100d0503101e40c4200401041d00e0581d6a130010f128000a100704c40c0c1c42508082603185000718038250304042c041e600d0508017035103101003002a1842808520106180e91100c5e00b698540b0b00f965102076000300c0643c4502c0c1044e0340014a07002040b02c021000400c4400d20000595448250311032020080f140802c00200920311241c0c4070485900c0241e607185 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 699419325 1250 699418075 699418081
    0x3051509070905010e0a05150319021612020a03080403030f020702062a0f0606010c030905101d1c121e020a0c0b03010506030a0e010612061b1809020903010212 70
    0x10b80310202a055034402c3e80c032500d0085000b824800301907458000d01d0340c8004a0311009901a069802440e4044540500a0010040d98030340d10201d900c28040b418541e5813400a101c01d01829200034500c140c2340384001d2100070fa0b9505c00526064010b000141010f490f80050421080030fa0151000350390001c01c030594851282c3c0c1d000780070000070f02c078040801c418120b0400c05400c02003109402c0c50030013405043d169407044011113041c5c502030002c90902040010210740740e1240300c1b0f40400411540c0700c0305007040743c40d03030707a86500070380b040d0214400d100c00411400752820f00e203442400198405181500079821200c20394000040d032a10100703a03c0120740200071581d001a00040c15400f6003402000305803a080c00c401580b000340034032a0010820004221050340c43ea00c1924000d02420000074182c1d180c03405204c061146000075a1150b40301c4c0340c501c01e034064603400c2513913240070f0b0704224090840c810950403503101180304007201603501252100b89910290125050f0f8048450b100307202d8a = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 699420575 1250 699419325 699419327
    0x307090f020d0615020d080c0d1a1201060807090f090222060e060d08071703010602031c0b0102120309190f152f0418022205060a0305150907 62
    0xb41100c1d080b142d01a050010010321042c1041c0d0030312507001241c1c00b0340076821026500340c03083d10307002c5c04840c0b2005080100d4010204d0621440c15803800352038640000e212030504004000707064449820299141c074004004403400050780208450584c070010030003030b1140b4103203002030216040194000c000710300115060701310760b54100d0078100301485c00c00c101500c511641142840403106a0b402c5440c540034800415940c01c040d00c040340c0308507242d00c1c80d00b105005540c501d4000317901c0180546d002040c0d032001083c00c03501640f85080c45120400214515400003540ea500c22412544c04640000c08900c10901c103024003504c040d060451016409803d140036405401410815a94858280e0306904a410036004d40205400b501c40c11100912210650200d40ca4aa0b0f10201c2005410000040c0444502c0032070481c1d8010500c0050719010703c00502d1240c201050301420700e40e890104103200340d5032118166840e081482c035001401c2c1e51000c3d4124041a4030089036540100036404100400d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 699421825 1250 699420575 699420577
    0x606040c27150806012d0e040e100b0109080f0319090803040b040f06081009050a020c150f16080106050901110a0f0210030908090411160308070f05030106020c0d020307090f02 77
    0x98074080c0d803820000c1a1a41842805c07400c01030800724402c034001b081c032500610800028100003401480002c88c44a40800c0c41e1400286e800c80d021341684821142c4102e40c0c21041d09e40061a00e0340140286028084607140c0b240f20300b580039101841c03684000142d03244030310a00f4020b031866100b1030340d403607880da05c8071070484e00141314807103841100d4040030030114030130140d183c00342c403041c2c101070600c6090020000182c8002452190350541c240000b99441804111540e01c6821943c1800158241010180070803140206200070946100701c54082250388011104d044604074508251103181407001240ea410b45640e0301ea40e94800d21428a0510444240300d0a856100719505042845510b40941c1981d1050601900a0100f4091003029040c142c001034440780500925601e04406081380e502da8a420403c290002000f24040280c1e09400480030f46d8080c4581c14000d05540c9491002985c4481d455002800349138299000e60454604100d002c0283c403500300140709440314401c000d002 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 699423075 1250 699421825 699421831
    0x201050a0b0a1413022b0c11030d0e0f0a11040f0b06030a0902010e060c011b111e0106090204080703170723070308190e1e0d080c01021603020606040c271508 69
    0x6c028500340886050034014042c0b2040681740740d0245080008030b000407802041804240e0049006003801c5030a0340c3d0b02400310040c1c1c9445414040d061034103084c2480211340d949820085020b02d0003503420450350700c035400d0f00da10400c00c000100310344460b40300484482465401d0303550001c13000300304048050b0341904504444001d82180c0040552203400448241c01c07040019091900100c000092005110140c80c083c000c14030001305405130782d0711040081341d000d0b0384140096001410148200400304445502c20301c1091800c42c181500c81d294070340383c0201a403101c441d260503103803909020441402030100850704540302c540c4525001c50702503948692010741000280610446046d1440c0100d5000421010030380060200394040d01070017920074019800303441e910b0007800625001e00f003d0008000c940b480292401800e0b16910700607140200292625201d00d00304001b4a0000b030b400802450094801c42c00c050041e1130030a4900c00d06541c903044100000000d03011407c03c0e43c0c10281442c0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 699424325 1250 699423075 699423157
    0x901030b0f0601020c0907033902190809060a110115050a06170c1e04122d0206180d0b161e0e04060909030201050a0b0a141302 56
    0x1201d9a1180300480e1100b05c0f2000080d4460b5600c40400c0c3c1c3c2620a5205058118902000442d00c501d02c05140120540e900380040180845860107000a9410311640d0a03540c6030b141090b084800b40d40c0c1d4030186005100f00300e03000314004503403540c40034829100c25518111880081004042c2e440c00210100f403640191405404401e1000550b14465540780400084240b0020801d85802c58441d400381d0140796a04510500c640740c0011204440005000514018a600d006182a071511201040c05404a1150884040d8020881468100c924408980e0440d0955a107882d590303e803071000c00000a1481c0c001c0c0050303044e10100400180020b0003000469503403c0c20202e0000200c6060003400c890225102c2d803142402c1640340654a004106500104089440303903c3e04005000ca810b40b90068005070b44400602482500c0c07403045000b60103090320b01c803000909103210910b41c1009607428601800081d1101401c1c000a90305545072440f100303098206581c0c03440c4c5014445c0e05010b075004 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 699425575 1250 699424325 699424351
    0x3091e05030c030f1203070c0506010f0e0a020a12110d110c0c0d0c0e0402180403030b04050601090f050108061c0b071214130f120c03020f06040f0209090c0901030b 72
    0x1c501d43c43c002030f0981d01445900000d181e000c403e10841800c07a080039003c001400384402c2e108001840c00c0c000540600a02d956180810385000d034880c003e82e001a0502c451144100705411038164007640c00000284540c0c0086040c903940303980000944105030445081134a003410030105090007030001d1411000280454000070202020131010050801000740700c0b2400500810032a00484071040d8058002400000743c1082e6404400500d0f0341181d0440000f5681d4048241501d041e01c075098101100386441c0c0111030400002c1c0140b10a00c2c002c5070305204103070b000140256540c0c251101c448810708a2000340310b1540c80e000c2c01018059800d5008920780e00749098095801c3c0c8283c945441c01d40310351006d1615502048d03544005500f5044e030351084150006000302fa024014000362107059680c002001209007030090900070400800d42da560020014040490008160520382c80d4040f10580348070744449035082e1401c0e4510131210b07007040e030b03100000060151030341a0601c0b40070300d400a4 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 699426825 1250 699425575 699425593
    0xa0201060503033c120105010f0c0201021e01020c01020c0303100b03040f171b06100602031801030b06190504140f030d1b020301050405030301090e03030907090903091e0503 76
    0x56142e0141020150014010380358800c40011000c1304004400303400800003d41990503803010342c01d07030f103c00b181c080c4c0480108010441d07540d0280108a1b0b5100034508a41011b0160380000e448502400c07201c078424104001b010001c0b01c007075044400d40000360000315543c0d140301c49410384030b402c200c0303070100c4200c003d0f03030f002038484042000c0b02c0c4147d40c00700110310300355595558203200040707910980103800400d101038183c100d440e0300e482d0542c5085900400d030713600d020201410842c800b42c0150085400500c040d003805840c00c8011405040d0909001c210141818041200c9010341100454520142600803c0c032139080750041041d102c40310260201e1038902404e104181c0c0301c4822960301a80110041841c1502c5002020150800d03200c00d0700a021090300020309480013035078103a41c1d43c3c1000004201100311440b61440003072401018504602d0800c0446494600324403a20488039110f071450003c040c410f10f000806032041e25010640703402d0441d89204030501c58062103000348511544 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 699428075 1250 699426825 699426829
    0x908101d060112080307051213150c05160206070c0e090c15180a0801020c010219020105010302150a03020d05090616110705011103090943081b0408030a02010605 71
    0x1218182c40700311001d14003500e840e0792407410543c401800e881c20400280f00762388807090840c041030701402086220002c1450281000e1110034600d61904001c1d510b069220001c1c02e400c03400f0748685e0300740100d80c03c1c601d81040c004144181304e2102c0003000414403540c0842d200b240000701301e015050040c1100c215051003000c5c00030821b61020401d454100510507604001c1112504441c07160001d402e21006940d00c0015509980060102c02d441d40d401141440c0d00e10010ba4200b403491031107200030302c92540f5640205000601100c40001200c8001410440c80b40c003e80460b500e1200c0c4082c02c020700d140210b04262a100d00341d800d0000314540080610a191080000c1e04030008000d01901c0c003a481d0400640728400c1b20000546c0d42c0c002840030703841640c3c40c412130500c00c8041030381010301e90030444500300203d1800a059180c6440c0141e84c810403005003102c003020140c45040c145940d45a01c0180078402c800b002890304030550024003c00c0944010010b0040f08400783c0080c4480364607041 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 699429325 1250 699428075 699428083
    0x50a0315030f12091a04030b10050603072601031a09010c0516030e100c031101050705070809060c010c110f07080a0609020607050303010605030609060603061008070908101d 76
    0x80003400341c4940500e0503010a070f21100003203a0044030304021001c0e541e40c1a40c440540581d900c10f022800c03011500304184482a842154040b020001c521002401e000010b01503000150050302000f046150a040315110803420500c3d0650840c1402c00c29a940d1500c141d070900b854107030502da10407403400b00e07202c06014010344c0941c0159882d41402c000b030740350510b16503501507041501007003025004054161502c140c404040035040e0b8944100010a040242c50343c4540c10f40403420340c0c908420440c2e01b5500c00c00ba10070395644603c9880e55181100e00040340d0340900c44481015500c0c142c040c00030310b60060502c102d048400320680f88220086d08029407121810300c1209940c0d000004180006180c0351b0020302001c0c03009140a04041c915103a0500c0c54100360042c40c04268000140315080c500444d0141c1d01440841c0c68500c0d5240c041c000c070b224a001d1000d000300340f1480b2004030b15a2401030342c056000d00030610031101109440610340c0302500c040b5070404480c074012202d80001c0d00002c1 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 699430575 1250 699429325 699429329
    0x6040f05060d020f030a241503170a05040302030d020618010c090b0c0f121c0e032b02270418030f0509040513030e2b02060f0307050a0315 61
    0xb024a120518181c003030160b100c406200269060164101150004e0000381440e5143d0703036000801004c07240d104110380e04690b003e0001071001c80c80450100009440c0028401c0e00d0041c1112050301c410a10400707680900464100171750500403011003205c00c42d0300044541c854000d80c2081c18a003040c804109080b07800c001920b0000441c02e100c2400311105002c010800548048111000313122000d41c5107042500d0103210918030310001902800b490705078144c8001e2640e44c03070320030022420381900c241e60300e02c030341d40e004003244415041c40f040403010034410307484c03404030400155034034601403495140c0303460070010024500e0114520209a0704240c46403102e0f1000310502034100320303090384042e40c14802800b50041040307020882c01000c1c0d00c8900a90740550000300c3c502c0e0288060746000b91010001d050054000c5103088003a4481ca012000001185460b8262000c0313907400b2800402c0c400d104026084c0141e80b0000180050264031600070507ea200c255130412800807a00c81c0e110286c00e541c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 699431825 1250 699430575 699430579
    0x2100b040b0d020405131407140402040b03070c030e09013201140c010204091503030201200f0a1403101e050105030f07020a02150c150c040918150506040f0506 70
    0x10b00050300142404d52240780c1000c0112100c4000080540d0380c00c1e010b42841403d0802500b080404000910741e5890802445008a90560030203080500114240c000100352000f00010f8401c070800b41400307401c0d07090250345d02402040407580c55a14003a0300050301c1c03010350861422810300b91201030401c2ca203890209816964030070051108a41c020701500001d810013400d541c01c12000442801a100b141010366070f090810401601c1c41c20040c0c00c40341e84502450848903055601000706009404582c081d40580294a03211542c0c480203c401961401c00d07804500c00000c00c2c1708400401c0c0150004440042c0e040d1084032403029a0740e5104101e9224030b9020a6061011500141c5c901c1c5495611900910446500c1140754001901c2e0162803442c40c0700b6110300141540304010300b48054800850100011007281c00c2c80305c1254200c0c4500d100b50122141e544500c5522200a40006020301e5005441c0c1c12807a4110765845c8020300d0113a035020702c51860400c105110b0106030144a1040c900 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 699433075 1250 699431825 699431839
    0x6020f030c0712020621070f0201051005060a1701080705150f04060c020402070f030e120a261306050a090e0103031b060b03030c010e010e06010e010b09061902100b040b 74
    0x501160150485403c210490380114103000d60040c2d048105011380450780041c0e0070380c90505006030042c00407088865008110390410003040b00350280900400101d62058649903654100c0040444e02c90a00c0803024494100d49000003d00c030f500040e82006070b41c1d007200c8611514240c1c014401c4144070300340c00148100c400344410080103011b0b000e07a41d20140003500151902d00303555503003503c6004181046000c42c1c03001d44422035604108441c5500000d04c0c0000b0854400c0c02d80718800b4100c84558070144040080c0e6007034040b04804816980c16000c1e0b51280030226454a40240c495040b0401c060000b0310101400903a81144100d8141241d4240e22030001d44468038050461100b1964800d0b1340207500e8190640883e14100010503081c54004000244510028811401d40e01c14100401c81e40d070040005004003e07103030800c0360455800a41c002d681c0c400c41000718680d402551032122404401c0701c03140c0c40603074021640d6a187c0b00001001c000302074010040104071039000712010b4100c0c034 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 699434325 1250 699433075 699433079
    0x80709021e0d060906060201051906061d030118030503240108041128050406080105040506062403010e01080c040903141602190515030c09010e012706020f030c07 71
    0x104010a105880000086030707003600c2d000c0d1281529002d90090005031740d10713030400001d202b003c2004a05441481010311039586031582c01401090000b0041480c507003295058460b81d42d09502180402080c1c44d04c80d6035402560801900c40d803c126441e1050541101984000e5110090350489101050b11514000c1d22181c8031b9101c01c1c0c0720030f820b043c0c0040790305005019840400c00e442540703d0341c0c0d840501000d42031a05010036150f540d0b004610580c100024080003500108120340d0041d03058640c0c540e076000509411400500d4104600c070400000000440e104540071840d41c16a031031003080781c04800c40d20091000b2161041c00160015004074560030403018204d0080241103c110080130711044980c0010f5011501d141d501c1d801f0900b441c104000c28100506030800b034112250b4483c2c03c600d414066000c2c0ca00c00c0c01c01c16410401c0e04c868003081d580c098031808103030a00000000c3d142071880c94401e610072282d80640c00140c8a01c1c9803180240d04008100c45005120f10701030800a8 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 699435575 1250 699434325 699434377
    0x30308090607090e04020d0605010b0405040f05060604092007030f030b010c0b0615120c1801080c0306040f0908130801061e03111507080403020f011b0b0919030908070902 75
    0x1303018008980c800303681c2c074002000c24a980155400303043e5000180d541d603440d24040200b21034042c400850340c10700300030404c079040d0740e20000d0b07800f1a2101c0401060104540e034001d142c401640d40c00050084011881c40c05040d0b000c05900791602ca0340e00c08200c080e1111005441d40c00d082c21005011541000000d8141e04000e11124440f02d1608626030600b90f400382864401c01c0200d8880350800300200300c03501c4541212503031100507103081c00c0c0a161801c101420f18824400240082c0c007980d1140c00d90207401c482c5902000b85641c1220a6035191600720f84202c84564107480354840039801c110b0089010b90f41c02c0340281c501d013100145c3c00038107851035480a0203030000c81103465000956200142174044a90010003180340700d910740c9a541c81c154810040c0e036425007071110741000039981c09000c0b14610403c0039032525800207010503003642e8088490703141c00028141000442e925111520406030082140801da0300c100058441560b1203000300b004034060114034042d02011369940d15050 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 699436825 1250 699435575 699435599
    0xb0a1406041419020c0d0507050601062a02030a0b1302031e150402040b030d02100606022805070302060d060e09010506030303040f030507061e05180d050a051c050103030809060709 79
    0x185400d0349016045c4450500383c40e0508080ca021a00802c07400a054010007806000359800340425007400342c10641d00c106031551401a242c200000e1b070844800c8001595010005d501c11598030118648aa141094446844203440744040340644620b80c1c5d410321208440050800a00c072950041044184220704003036140300181090360001c0d59440380c1c2c0c4550300c060082f9604001590000c107010440c0502800440704164803450031034010115182d400c0850b401d9000300300c015480310800d036810b5403c0060802076140d000941c04200003a04900d505030b160412800c0710b288030214400c654510f06030768240c03502243c1c034543c19041000001c00060400509410b06070003442c0107418417504e030761140700300d51500810740a400c19866180f084d03500344e40646035004004880014001c0503550400d0380e00e16020740304206008001c603c9548440c404c0c400d036807484119030b04158007080311a0522004010a00046d400621702c280007071f1540c0c0c3c00051aa02070780d1952303140d03035019241c030f0411060 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 699438075 1250 699436825 699436861
    0x3020c010e040b0d06141305060f1504092406050d290a0516020a020a0b030c250303110316030203040809040e0c01110d051c090b0a14060414 62
    0x200943e58400f0f8803107521601a8181c415105550002d418a10400e6034124050000e040d0368181a4100040740090804240290410126100c000305a103603d43d1140300c0349101440d198000b450700410405110104084401d01007d541d0b0b10744440c40e1195126060743e00502032241c119a4100c02e50000130103440c0c543c40f020b1130242846403445040d800600d00345c4410f8540c0c000c0c0c1c686450900070004815951300244007503e000174106001c4503404a400380c00c1c18130801004005c080006034850b106101103d0451301104074a03940302c0500710010301c03210740c9840300390300280c80c149201400e0703620503003124007815900340445805884058210040d43c0700400440d0340502c14810402c0c0c0ea29240541503d0240c114042c15803050b2a01c00180300c6040c0c8c420540090340040081e004698001048400f1040300c20a03002070b5245117600c0d04040c1020003001400a0b00d48010071450320300c564404070644000150300c200c1d94542108100585021761004200d682034180420890b140c15559590 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 699439325 1250 699438075 699438079
    0x406050712050f03040c051801061d120307081b0c0109090c0c0f061d0d2a23061e0a051f0f090e160510020319031a0d03020c010e 57
    0x80782c076581040e143c403181c0068408503400c0783c415406000074036021404104d400c292968013056076251400040803000344084040075640c00b181b48480707070b03161170040a898030380e050120782d61080c581c60100e0f0180d20100078006d51210712600741101030000f18100310303198070503510b20a80302c0c01c2c00c05100082655071032201c18000b2820500c03000481c04d080813840d117405a030340081e03045c01140038954105203848100c8080d8100510130004160824507540160414a1a02104603440c031008015105905006003400301c101c40035039080314a50ba0041860203442082e92515252084c05640b91404014000388030491000007401c800013991000d5480080403040304801000e02e034060180300002d400145103640e02c100c09001c611114043d02882a1241000f0100280071005181d0121010701034030b03116990742c0d000921241c0c420415500100b070412851071498a03c03040150003450700842c41e40000c000602c0e915100c0c9818505141900c2c1c054020700901c2c54840011110300b000558126 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 699440575 1250 699439325 699439327
    0xa0203092e21090809040b0108060a1211031207140307020109060f031b020c100908030909040f12020c090109050f160201060e04290705120705121905010902040605071205 75
    0x81c84800c0c0c000c1c101030b20300413540295a00c4040c000d1109507001d00f1001414802d441c82449100e0b282c0111560407030740b401c620702c0540007041c6805000080e0094a03e40c5c14030804001d0b20007903c0d03401c01030080c0ca2082d2601140ca40c01c0154458413070062800190110306011010808240220001c00b00803003140b074002146c4481f46c071250710054942d02e0580c0144d200d411441140d09106a80c00b54190f024104401d10030b20f0150401e50741d10035019a540546050703c00700f0100f20301c101840d51495072101c07903580303540c0408200030b655030304c4c00b00d402e8400c610582c00042d0070310721071249600880c40d09402c1759540d5680000c032011210020042c01c21907594207000030f2118914020307640a5480f07180310090a46207219200318188800b29210420740382a0305100c00c41d604041266114132440f0031880d015560000192602d00071400e1034603036204a1400c000c0c1c0c2c20072a0f1102406038041d20b07010042c503604e41a2a0707040b801540185408603070100304480215982c0009614161180d141003 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 699441825 1250 699440575 699440627
    0x130f050133050a0f170906191a04020904060b03040b0f01050405090303041112070b040e1f18060b040905040512090f09180f1b01031407050c010b03030a0203092e 71
    0x48442c480c006c86403041160000d00502041d40c458401158004911030410b00c9a8903540d40030070f01c1d440e900c040d0b1521a543c0003032000e0041e1140d800050061003900075068891606007071111042104a030078540d1810024000305403803605106aa00070b1001c4d00007141580d440e540e074030b01e12040404100307520a6050744000400c2c10208188030182101c40c1c1019259071500048014440b4050204810f458841c80d0074a40342e09500d059504941000010502d1122244442e000400721900b1000c60140c00241c049061452508410b0080d0b05c60300444180042c1c00c0b0b80909140100000746070b0000c12b084c1c40000e1840d001001c00d0b0407081240c000e0001c0003268106624050b41c01300410f03400d410a200010101c0e81c54517950040403000e007011300820f031420f4041c0c02c0c42c0000502840602c00c000c00c402158403170950004011103405005c03641d507003400ca03034040d40d00d070005e07884148079400801500b101c80360a11210010851440c02401100e14890000d80303003000500c0500c1d078001621005 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 699443075 1250 699441825 699441857
    0x30c05040b090f0622410618030c120d050a030b03010507030c020601090213060525200a0803160f0f03091502150402130f050133050a0f 60
    0x4091010b9185810141c2e2040381c1c172a004010003aa0142c290505680c0e2100300055203800d2400044c0c848440c0c1044103201403010510241c4440c005a0b045500412040c403541c40d442c400e503150310011006c86101505540030010345240038042242190400c103014201d80b402003004d005145c8071030401051001c4503c0100b800c640c0b003280c110b0002511111804100d40d01403114502502da0404d05500d003030700e5a071b00313203074184580d100d5201008000500403d40621841ca000000c01e050390040008400600b42a4010b10800040603903028242240e9241031815010400455822502640c145079403444840420807100b0300945d026000e640c2d0200005405900008001c0d01c0b0340c4400b001d2030b00f010010707940c8684d08903442d0150b5004074542c04c1181d1106641e698899412642c6c0300322000095510070140424000c00c0d26200c0c18040007040014031148201000c844800020000071070400032040c0c02c414003000c082c0410810401c061302584076449502c818603050034140301240311220 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 699444325 1250 699443075 699443077
    0x2102913180804140108090604020108070c20090105030307050619022a011424040618020d0f0212070809010b06270108100e310b07030c05040b090f06 66
    0x40101c42c90300000030244659902488140c585210a01e00240b0610301003040641c1c4220181c8007074140f010340320000740000d210300b8072509811f41c03243c0103103513800c002c4241e002449480750030b092049000000105a5003400400e48800d503401c80014889500c441c1d04070f10030841103450200d01c5a4003048120515081c56003140c901c806c01207003450180301085a85400c442004940ca280c00e150170003401582da4003246a101c0d82ca034074031401d07218485018009030040c50b260748066800c5044500e903460304e04007a80076040360340140b90140814407001d16100203d116081c880340d04940e803080030540d264440e03541190b010607480000140c000700d010025500b40c00c42072801100004032241d201600351510181c042443c003e01f0510805e003000b0b000044040100d000e04180b030402400001c03180c4080d01400441c141e9143d100ba2000010003a0010070444c9140090310000c040e50085030710720381310340f241c80d5030809203607200c5050608251640116500c0721607103036403080c001d060450789903071044 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 699445575 1250 699444325 699444371
    0x20c031e040303030c05130612241d0403021507020309031204091503050303010504090c050915030d0f09030816061d0c0307030b041e0b010602102913 66
    0x800e15180c40c95842c008041d11002c40c054403c001d0305114a01c09000c1c4182010b05944c203e0030000d04100d01d01041c0c0c40103080380310380281c10403483c06d08240440c2d04620380c01c040c0c44a10050300c440c1e0070740041d102400c68050310000c0048c0d112514a41040410b0103c680c1c2046051050317a1030101c20f100024508888102d203540000c03000113040100d0012403080c0382191894009081c0038a01d103803140e9449001c1445014000c5882d281d80808001d6042100c60103428001e180031094280030313850300032822001c98050300a120310880607040707501036450302203420840d503503e4103501c1c01c2d075456240c19048452a00c20b40e01c00080c0c0080010580d009020244072142c45000c04c2c40b20604040c0d180c50700400f10320f03010303800015042c0042060707078844680c400e400141c0b40c000a0644200001c5100c19400041c010300700a80001c10140d40c003240c1005000c3c10140c043c44010319000800d0404d0141210400492607a400f10904505003900600b04041112800048100303074160448038500d408 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 699446825 1250 699445575 699445627
    0x14030a120c050a1b090e0a02010f0c0f0f1a04110f12010212070e22051803040605090102060f0105220f0c050409061e0909050c10030b030f1f020c03 65
    0xa0054a81030100c5113075244000c001144080c880304180208107a110750180304041d04101c044410503490500954a6100590740310044501d940200d09107401c4403140800700301c41e0101000c004140c600c0d001029a405140c0182d500d841c07c142010400c80c1c4101185000c2c1c0c0c0142e020340080400107001e20140480400c0c403032081a09181c000801030290303c12481c030600c148034030125866242d5143c0304c1c45920380744601c0700144a444040074045240300300e40f1041101d201c00600031030740303a40c04806004915000c0e000ca0f00682c44000355000100c0003401820782000c0046052001024078840843c1c4254038114009035282809200c0e0060303a9501d04c1345004140c001504020b07010f440c1c80f68800030b00c117005100c9100095180911110300c02c900c10480665210380702c407400c0c040c00784a2156812402031600740700d0000c0d6840a0003408450100a110340640c0d101c1004c081e43c0072034101140580515070007900703040d07580c02c000250001894000036100c14802c24101d915405400c500c5c119807 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 699448075 1250 699446825 699446843
    0x1b08370f11060c07180e0d12050f060127050a12020a211b1e0e240118150816030e0d0c02010c0615080714030a120c050a 53
    0x403400e00d035100078014102140100410028403600d10008030784032060311070503840129007604961002002d4144440d01d162075000e00328043c0c0c1c00c2d5400c1015184100144a002e00c001e980780c50120520101c00c0382c030140800c02c404144010781501103100001c9103c9801801900390325200031a401c10900d4218040303200688141105620b031544800004120030b154029811004103004808a000450001d18071900302d800e241014218403c404060002d00918103003002a030105c034481c10109100b071a00072458480401c1401000b807500d0034041c1344040c1022a51641007004485d0000302c08051405600000c0c00400c0d8038030304078100c18a0302c15503036400c91181001010902088659441c88091525002c10301101000209241804260600f8080d00340c40d29030005030741c09000d006009103203c5c9400448500c0342160754428080d6013101007143c0c1c400b034a07000c0c0c000c0407900100c1c01d260700d0f620104415002800e40c1303000c5048030243d860b10030501105540c5481c0b418400c035030210b0f450b40c8 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 699449325 1250 699448075 699448103
    0x7020706182115050907060f0201020909010b0c10050a090219030308010302100905100215010b0a050904050a110706020405150405010c110f1c1b0837 66
    0x6445407001c1e141c612100721071141d85103032000c0e8441c0201e007807414020540100d0842c005011003031881c683c842592542c00c0c4094903046204a8076031a03c0d0140d031021400e40c7d00030b49078080c414400d8034181140a082c20394540d080410a011a40210404220364860083c0071049100c00d4050540541d06940021031031804510402c1040c60111080200c000861902040803d5000f028541107030b406840101c008000500102e42180203a00207030340041901e44082a1240e001805c5440c08030f03110303c4602c050b601d034202c1d0b0846110f40164000066801d000801240c6016408260802000d00d40020000d0001c115800039421041d801d81c2d1195000c81c003040542851005100d040703040340e40c9540351904050000e080303040f0000c40030b09140180440d403e010303210400904240d000c020b1404940750300d03040b001e1140800c6448110f60000404500855410b85280d441080d251a50702038588030070340400d803489490f42092161b40000700410600c1d03000701d58201401c00c1c54015189108604 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 699450575 1250 699449325 699449327
    0x20406081f0506120706081e0112060c02030a090308090607050717010506010309030f03090212061807051f0f051e030108150c091203040810021b0a08030408031e07020706 75
    0xa0b00080036240203200074035106400c0340020480c481078032017608050300d880c0ca8140c17520400d840c10154580c01c408510002081c0540d6091038070900a01c103600034043c00044480480e20b9000700e0f082c03040401d503003101c180300013840d441c041e108400d009003c00c0e060903c1e54441d1480c02134a5070100481e404a1a00e0907900c22003070190a0340140207081c01d01c07074180140c0c1e00800394411107191004065440089408540da801c1c41c0c0324460482400702d800c1402c00b41002060900141c0040c40b0a21544100140c0c0e0704140c4110400e200f025001c540c44000c003a0420740d4605180183e440401800b040440c60740f17404200e0744410462030000c44c036160340c18440c000d071034040640d03840c492403d905000c204210b02d280301104e80000301960b0316403002c2c1d05080e0107842c5001d10b40011515001d044503040e070007909607000e00307603903015100d84070701001c00481d0054884000f8100030744102070800c0000d02043c02840199084101c0e1340030107075142107000012061a41c165008c0300140c022240030801d031 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 699451825 1250 699450575 699450581
    0x1090b070807230f0711130b030717032a03040803090f060315060c190b0403030c0f0f051b1606142517071b0e0c090904020406081f 58
    0xc20501008604a8500b4240d914600510144c00780c12480003d00300d0801022000903200010003030500009840b084487c6409003603d041594003a1240907c0013a054545506459100c5e0020b03010b1881c100c030b03102013910115500c3c50100c1c02c1c103080c1c0015410031030b81040140000d0000d4405540c503103800b001040617200c410510140700300c03000d0081c0040c000d4040962074181808a83c029914501403c016080425041012541e02031511103071060125124680388124429030301003040031003010050351000c401c400200002442c64100402c0e00340658020000d04032450240c0c442402400754841c984a0043c2030b182e960007010100f0454140c1018510b441d6040c519169402d0510465580c5020f400013036050604c7d9008500e41c00c10f01c1282140802c51b14410790300103a650315141020b0740102c024940c0d542010400100008000780b0013007519000322400b400e2a89001150810002d40007406803090781d02607506c0b60000740b411000c00c21402d00c500c00c5129400c50000c0452a6421 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 699453075 1250 699451825 699451847
    0x902010203070c0b0d110c0c01030c1101060e1e010303080a0f0917130b1c050a060902031003150506010e0f210c0a050406030201051606021606060503160e160201090b070807 76
    0x150184c184501f159511003c5048801c4000a180c00109031405040c01c0700c0f0f0842c0300c1803084803546800d40100f0403019601d20940700f552039600303404020180d541e542004007801d210240c0000d5040e00803882d00382e03440c4c000c3d40c0d0213610f00340c000c03d0000c1540c031105841c41900d113003224560000900b80c56020306c08144c5030300618102c02e04500b8071089401c106c00d0380002a0008251655030b000040310003042d544045c000e8024480110f4491414441000c06210680001e48903610408040b21142da441c3c00391501c83d85041c0e598904400500007032003041c0c009840181e03800b1a0001000400083c8085a0320100b203202d00105a1070744081c052100200b850b40165008a04003041400981d81000843d88014540c0382a009134200c9070030007000034002c08e41c01900c002e90320341842c801c0c440b65400c41c07130a9920403815142011022500041108403c1c45a9000c550754070000a030481040380b00e12046030042d000109216540344d5400e1414403088030200d010841d0b441c240012a80d000285600e = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 699454325 1250 699453075 699453101
    0x7030b1e0703090b010b0a140f040f080610030f0f020316090c05090a0303390b0f1003030323010905011406120c16060903021005160801090902010203070c0b0d 70
    0x88040f9164951400c90b100500030751902120000705004001c0c0f0840c01c041010018044440d2650104021001a94098800d805030321200c1e10001c902840c01092a0b40103111441241c0d0140c0c3c5503a98403155071040c82c20540d20b01c0c10700004580561030030712141074860440114001560b040c518800b0444d405400280d08011090100005540322294032909480c0c06041c1400c0e101c001100c02e0298140c0b100102d181041003040c070780101c40780084450640b41c4100c4203582182d03620f0010800c080b10440c0d8054801069070001c10220f4029482200140c564500303c0190592509242206c0b03c42a404444510ba540d001000030301030f0000400b80d003003400c40e1322902e000d8141001c8203c0e0360024118011440c030005000804c1c0340d50912a00700c45500c4038003409401031a080207034031102209855540142001c0000d03414140c42401d900401d80c480d242d04540da402d0003401001009000800c9055200800c12040031406c00c10961b4001c0440348075180d0380e260425242010341e03202d0780320f03c0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 699455575 1250 699454325 699454331
    0x902091009150b070b090c030a031d06270406090e062e0608071211030a0e0d02100207060b03010207080d0f06051c03140c01020408070e0f1807030b1e0703 68
    0x4040c2c4000f140855a00c181c10140704041c545400c444e05040c48015003500e64144251400b240406412039039248a00310041c940308104c1c0000414400140304115007101c5c4485901005e032070301d0b910305582a0072203402900009003151501c06640c2100c03150102c0b40601c1d07005c0020403003940c40818103004e41d82c100e00300c600710b001001b003400300d020180b81c000c0c0ca007404034000c00034420781d100b114840c0d608034901c081844030303591440341d0703206591050307515403046070078242c001d8082000003523181000361301a8024124184ca1022080007504500c070101c40782c544440c4140c00550b8240042d04000340107001580c0c0d43c0d90a02d03158403c403a06004c124086605200007006a80d558128003200031314031500d40f1400c0045890704846039140c0760100014920046800300500c0015070150043e40c10710700c112100d03507895a4000102d0300c4201c0760401c80904010006004040100c0c070000c0104284084826541c1c0300e5032504032006045071829501410b0004011044580e24801a0040c2003400c1c20 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 699456825 1250 699455575 699455579
    0xb040f060b030402060c0c040f0c081e2712250507032a140109050303130618030b01060305040308130b0714040302040e3306040f090209100915 63
    0x103074458000288080d11403580418000321040c0240515410648010b004214139200c1800c80001007009208040c0000d04840c001680c21002800c00302390108030b045014400c1c2c0c2c906c224400760741c0c481c40e0100c1015101003c0300303804100c2006034018049079502f5540d11484039412030b4001c0d845c1500c0750f00307a0340329a55261000c5280071800d5429283c00c9510500240403c1c1c81d4600718440f40e83c1e071125240b00b8610009a40341c4c103038003c40c0d140b2009903509145551354a082640da0b005003803242e03030000070103503040000d640585408005080c2d050150b00f2225900d80b94680c22410907446440481e0f11141000201540709231010f5200340300e00c201c3c104480d400c1c0c40d0300300e0030013004009005100c0307180c402c107a00d070a20300d0544d402945d0080c818007202968a0000c1d84590140048415507555000c14101c500103400b41c0f901080d5608812030702c656590002c1101400c02c6145a41381c41d9901d4150801584400f40001d2044440003403403040d0901d00f0281404451038803000700300d6250303803801c2 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 699458075 1250 699456825 699456839
    0x1f050a050c071214070b0f010303090b070b0a05060d02030303010807060201060f15030c3f022104261e0301051302030912071506050d02010813240b040f06 68
    0x1d400d500b000c00b8076100f124540c03130b10514105441401d0020301002407040400c41000401c507022810b803407280d82e82c10761036a500d4480c4049802031245c002c001c29403280001d41002c4030765124030391040000381251049422030300842d0542e4800c0e080b24080d42c104000501c07415409004603070040010941e004581894200c42e2a09a4002e110300310402d91668148903066203d048001a01600c1c581450388014085c501c8600c031380f40d60002448080070108041600002c284280d590318030760541842412001c0d0100c03460a81c0c001801111403404100015078076140d0300c55a0300303801e510043c000d9a21900c885500040041100c6034052a4100704010b02c001c0c0c8034002d8400d9500c8001d9000b503126220003e2860404140c480c1580a800380401d03d00e09205c4002c04600d11154540390400c01203454109100c10b00480c840040e000c0b8000402141202204410103d0040d003c4d0050015040e00d1f608140b203105219085242040e440324050301840c90301d4407a032441440d950100704002c2d8070f0220 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 699459325 1250 699458075 699458093
    0x7050c04150807240f11010e0d03050a0e072105010c17090a030e04020901090503010c0206040c090506030d0503041401090b0106020d09050306160c0501060b0d0b040c02120c1f050a050c07 82
    0x185001040700903103001140398012506c1c02400c00000d0000c1c0300c4264001507455407140031000d0030001074282004078407118050f00c20b07090446004030183c07030203500f03103010742191542482c0c1c11003040082704018800300700c0038810070302c80818580c1c0d401c1c8d00d00362403a12b1041d455401342050f5000d4102d21440c2000a07000000c2040404c07082d1405619030302b0b42001600d00700901c3c1d0181d90154240807000c444e0701e601280c6148541c0c880d04003206001e4070344810034100c49040301c4483d010340c4030308120800c6a0081000e140d002d031249c0781030003600d90840c94039400e452030f000040310b5969054005000381c60b018025070341903465a10f40050705529000000e0740c1c885c400f4104a441c401079509802d13495100d03101039401e09800c03400a0002035a10b003f040020340c0050300400c00b01e0320700070301d0b19030780d142c5070081c00f046144607802418443c810f101030500710b62001010000c54414800d04111024050900c0942500515800a100d02d4000442802e40c0c10007803174400041d03000c000c03031800525001 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 699460431 1106 699459325 699459389
    0x30709051513020a26010e13060f1a0103020a081b04030c0b07051018020103050a020d0608030c010f0c05070b0901060b04121109070504050607050c04150807 69
    0x103c3c070301203054413174503200000200c0500401030300c03e070003a036035412401c9408010400d2440e6520310003110031500811808a46511702d012101c1a4040360904100083c201580303004c020a0000f0f084c0b1400800600150310201c0d121041c22030810142d034040d561203001c00d10950713103448109229030000c0400b11018411800b41c9518032905004000399085001c0001c580614140e0055010b080001c0c4000500d50307003404100d41c002801d01824004044503009103588603160200b407800d40d0008810600d4542c10440d140c0311040d48036003101c8245810075088205a110907003020302400c0190301103901030707601080114112105101c502d860318803070740800040417122024000f100c00101d60a1000c41d40c10702c010020707810002e0081212510074001c1c3d804014200d400602251001c01c1c03028560280442c1c02d0212140400000024010504014510141407120000680001 = true := by decide +kernel

theorem cover : BRFrame.Cov 699280575 699460431 := by
  have h0 := BRFrame.cov_init 699280575
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699280575 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699280575 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699280575 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699280575 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699280575 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699280575 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699280575 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699280575 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699280575 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699280575 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699280575 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699280575 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699280575 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699280575 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699280575 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699280575 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699280575 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699280575 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699280575 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699280575 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699280575 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699280575 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699280575 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699280575 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699280575 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699280575 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699280575 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699280575 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699280575 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699280575 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699280575 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699280575 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699280575 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699280575 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699280575 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699280575 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699280575 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699280575 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699280575 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699280575 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699280575 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699280575 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699280575 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699280575 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699280575 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699280575 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699280575 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699280575 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699280575 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699280575 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699280575 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699280575 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699280575 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699280575 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699280575 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699280575 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699280575 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699280575 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699280575 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699280575 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699280575 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699280575 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699280575 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699280575 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699280575 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699280575 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699280575 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699280575 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699280575 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699280575 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699280575 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699280575 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699280575 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699280575 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699280575 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699280575 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699280575 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699280575 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699280575 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699280575 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699280575 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699280575 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699280575 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699280575 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699280575 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699280575 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699280575 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699280575 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699280575 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699280575 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699280575 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699280575 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699280575 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699280575 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699280575 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699280575 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699280575 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699280575 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699280575 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699280575 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699280575 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699280575 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699280575 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699280575 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699280575 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699280575 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699280575 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699280575 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699280575 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699280575 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699280575 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699280575 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699280575 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699280575 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699280575 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699280575 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699280575 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699280575 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699280575 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699280575 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699280575 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699280575 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699280575 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699280575 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699280575 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699280575 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699280575 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699280575 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699280575 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699280575 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699280575 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699280575 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699280575 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699280575 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699280575 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699280575 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699280575 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699280575 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699280575 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699280575 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699280575 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699280575 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699280575 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699280575 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 699280575 ≤ n) (h2 : n < 699460431) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
