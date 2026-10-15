-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4478
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:44:34.7697+00:00
-- url     : https://prove2.me/submissions/724f01de-c95b-4c21-95ee-49c1bd3f31e4

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 805215827 ≤ n < 805395683 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 805217077 1250 805215827 805215833
    0x20c03040f09290112050709080312010608011208031f23150403050307080a110d08011d070206161e1809050601080c0a02100e100e0f07050d0204020c0d0c 68
    0x1600003c901c08081c6508840802500000c04200c03140d209081140e4449011a01442c014510b840180030300000703998440316440c081d40003030303c0244200c00008004100000d0048080c003003034846940c02a81c124034603034440b407a085000e50f4000f41c04c4007003290054000f600c86c00040702c0c0140e032903424811191300b6511000700034072852a503642e04803940081104000040000088952103613014101c191643d01584c001d1300e8403460004c080b51240280c90300700c076171698041d8403e4180c40354900ca81d14070700e40c107486003000c1d01022aa5900981c0c000c41c013103400c10404018803864184540781c19600b030040000d401210001440b10800403030741680c10b00c81d2010011b40b050003d00040d050400c00c40c0303412000200300c14000b40a004000d02d000428440c070b5803090103551740c1056480d81c18414a80f210f0501643c0d131050040c102c42c12844c0c41c452031001400410b251000030a500c0041c4a018189000c00180d40020320b8100e80c07055003040a03000200d800e0003001542c090584842582c19040c2c2 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 805218327 1250 805217077 805217111
    0xa0e24070b1807170c090103050a0302010f0b060414130e010c0306080f06041e020a062706091e090c0c15110406050d02210717040203060a020c03040f09 67
    0xd41900000420ba414400c054180003580f401260043c40c0c20f84064881c80e0b031460708142e003a4070f07a01c3e0425950000030050120004101624078403a9000b0803420b4122590001110114106583e00c070004200400c8000c2c40284c035501160401443c82d4610450703000b131582103c40c50442d10b03050340d440f030382c100f2551034140c800d40b00100342400180c208a40c0c504556a15403100500c01042007400021100400c40b82c000c0f10000241e01415011000f41c40f03c0300903290703a42d4045407282c00501c0e4124200812440b01500046822584810b0038a60400c008000c0d081c80d20050f004808500400000c4c05d82d480b8000d003151042c00d0384411010030f085051091200801c5240011a2070408040e40c1c2640110000c90b021145079150060321200c800307003041d010703100d03690140c810704001c0b1510b01201c0546201c82c43c0141c0040c0c560709200105051541d08002086401a5268101c02c0c00144c100f045034000740705000107881580e14290326115064030f00c1a00b6046000030726540c05403440c99201e07030 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 805219577 1250 805218327 805218331
    0x20f011b0f140717040803041e060e0d11060f0d090308010602070f0608070c02030307060b120f031b0c091906060e030a0f060216080304060501060507080a0e24070b 72
    0x1e80390003409000b0001001c4070358410404010039141403110110782e4015031105880140402d402541c0d550390740ca401e081180d0706038194013400d04038210000a40d8502890300400000400f0f011144058060703101c4644144e01041e1740383e0491810464000106076030360051101e24410305000840701e4490900a04c0c000b01600040700b5135102107020b100c40440710540304201d811a103418281503a44040c115000e09010398025054800820003200700402c0d5003000003035a00c01c1c2d5498110400c1c0c284840d60790303404401c50341d240340c0080000b500e41c0c060201c0190303c0e0954032000c0b40c1640d4240800b04800356001c50300301c803c4800000803803140800030300488009111920b8480c101c0b42c80000041e40702c49600700014491151550101e04210064040c2d51050189191624a142d10781c20400143e500448040340c2051601340082045806402038454594008116509089812506031003030782c1e03403210081c0d00242c00e68941c00000e0041c50700400c0358407012001d0b500c0340414601042041c1f40 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 805220827 1250 805219577 805219607
    0x1005070201020d2c0a0203030301170705060a0305060310020a0e0d080405030a0506070f0e150304030c0b090a02130e06042006071110090b161509050c01020f030f0904020a020f011b 79
    0x31405d5103001580c1d0010035a41500c200c00b12203400c095003200c445181c0000c551001d6041400451404481a00750f4003c0b441004203030195049000e52030700b01c6040380708404050000c03c002090100c000d040044002d0242482021b03010300e0561101b00103032038445040342c01c035026404401008040760b13114000012859887c1810017120b0134040c00210040710800c0d5884124401100240506224071100d80c42240c001030b108501741091034400c4d484a0f600c01c410f902580e965440080d40469520903039818200180140c8100d48846d5100016800d41d47c070641401c030b541e503403400c20b2544c8100c0204103441c401d003002044c0345a4501070151131244044600180310500008020310762082d81282c040c0503042d11007050951691400101d03400901c0c1031400ba607444d101402040210000f28008407120903022110200447d1584030350305c0c072840340d290311280800d004892003414650081c00c1d090510380140d0340ca01c144090090308407030861741080c00f14075078030400700410713608040d0807551110 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 805222077 1250 805220827 805220833
    0x11802100804020d06020a050d05010303021b01050c070909031701060201020d06050f010e010806040f0e0f1e07140112090f0605090106061b02150406030c0201060f081005070201020d2c 81
    0x540340d000101d4030030030400c1c045c1140c2e40004000450520a104413811003800e000304000ca540c5904001b95030309600c420f0840c1c040001c022000983d0b000d1030940f02c21203220b500074100142020380c480080c0c07030008021410700145a90f00e039040c0c0a02503416028007015800181c65023001c1c0305d210183c460300d90105006030760f110844040c44c2d91200050340e42420030300b4600d074161192000701d802048a410501201458003051000e124404516001e60302c845504480d48a050b9440080f1704810b00d508814031507000000401400241d0000441000c1050615811443c2860121402c2e03d002c039800301c0c2e010080894030320400c4068400e99410020b142c00801904d420702101510041007403041034400501407041d4000c6540340325662000140c2d02e0000394850b5662180507003e4550341c640351025500300340d400314a00c0c100319042000c403001c440c014050015441d00c0500208001f4000000b155002c224070056140c00d8000d02e40780b1412401c0e00c0e103091905003014405500d00c150100c0451b0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 805223327 1250 805222077 805222081
    0xd0e030c04021903052d060909150118110f031801060f06031e02160b071b03030905251a130315020705150f15060f0c0f0118021008 58
    0x2503a510b41101c505515080000d85034403003075400e980048046d080a001d010001100d44c019074010201c0c5405440156103200b40d5458114080b512070305c1281d00301c03003609202d8004100b030b40c0c1d0405003109002d40301400003590180340d81004001c1d0b84000040c50340da120000c2880f00741c088810340c0080050a40000700240c07400d1110040d545040351098104040e11107084925620424070107444400411a0031581c4041030880d00c0000b0004800c10740d40260303001d0003c1d44980c01076a480700e030381e4004503e00c95a90b80b55a4140c0c02801500015030300c2c0c9c80749045d90303c022089200c520800a41100843180c4c400d2500040300710072810760b030b08621690424880c440c40045070b0f12004060f40d070301c00854100e5051110300340000b4050312002a00340e11980c0101c0004280365501c00b4001c80302040b41101c181d5404d0403c01003851280507031900460108030203112105100c1c0036010740c1c94003c3c1501c54041d052443c141c00c0d5280444072400c1d1011401c2450114900040002101c1800c1c0c02c2003c1c041c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 805224577 1250 805223327 805223347
    0x1110d080c0f0409050115081e2418011802120703020a050c1b0a08010c0818070317130608072c040e0a0302120f030604150302030d0e030c0402 63
    0x62500034108140c1500c0109104070148100401c1c2e50241061308810046503940340006a94a4800603481d4080b07810700d40820f000c0803e003525041d41f216021445030558640301079040500710740425030444220210080030096031504800c1500c0943c0401e50003580d410040d02e00c8040002c604e007021400c0c410007007801241180c085003640301059050040c5c07a41036108007640c4600c41d003031b8580c80074010344050070340020301000b01c031100d118280e03824180e0640301c0c4030880c00c903482e600031080800c404034001694807050b440d0740d412002e00300342a505c00b241d682d5602070811001c40703502890514041488506a5020020040203009514200b011414140c0b00980880720603c0029003404240038200c55101390150300703912031440544100500c00400031000d0f1110000310048006001c0c001c031941c0d0f2042440c05030f45c00910807815003461030321414100b00080c10740c0e080a0103a16400000000503aa0901c520b9018444580303480582c1e0350f0354400c060408450194052080c0c2c8107111045907 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 805225827 1250 805224577 805224587
    0x503071505060f1807050c030a050c1204050d260d0506270a090303020f030702030c100b180a09061104080607050304030f0315090c0c020f090606301501110d 69
    0x64104544240c6684400717400312280d11404140c00220310001950518039036004004080684400f8195030382901c9140e0040e01900c51845110b60010500c00c1d10008100241a84c2c0040180210000807580c4e810800d041c0c0c80d0040d0004228855450007084014106095546401040701140c0d00010f8903049181c800700170082c0c83c085541e84d4500c090b90815000f50b0448040c58911611141c0700c0ca0101802540e030f0784580030800786406a42c0d048007040c9840d014200b81048000c1c80540ca20541c0004400c110b0001401403051940301d6880c240400d90364450182200043e00040e0703a5981403288041c9020350140c20482002410070401c00444c2e48603185800381c4641e450702080c1d840400c400843d15207199005800c0203403401c25440901e030b41100d1400301c250301c03d45800d120540b00408100003203004031405900802c08102c00c0b44100b2a0300c40042c7d030b20110840380c5a01c071419501d0b0190000c0100c41c440f400c50f08a0149198641e013000f05a842c40304100c00905003c1c054180c0101 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 805227077 1250 805225827 805225849
    0x204031403070b0c13050a0b0423221e05010312020c0f0402070f120f0f0201020c0d0f170406050a1121072106060e03071d070c0503071505060f 63
    0x242100012490400c176038007820381071004090040003d402143c80d49100003c5900604c40c0328072000c524050150710303080d4210700015041e0010060241c1f4525400345441034a4010700140200307a48554031041c106106a603411111300c042c8000613690306501c1c0104610100d4040301055603c042e0b1466210b907200d0665440c010810f40e40961152414074105100f4100084010007900039981d0350060b55074019030400004000307907500910140541410307070803407003400c030001c3c0740c0d41164a0742c001503405951115820302075854501c00c0380141500035100c20750103480480d400c9859000340003c40c030311360040405035001d1a202900d0581c01c80d5074402844501001c9000002007280018440c0303004240d07401001960f1400c2c90040031023520301c031000301a140a05008107004450301341d50b5081c00940f45054450030094104d01301e4540c0340c840312a00005150400304000003c03a40001401070020f44003d62141c110380b0b254490840c260400c0e2100200070901900c6c0c00044010265101c4000e1b038 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 805228327 1250 805227077 805227091
    0x30201020c09160e0a0b1b06011403060105120304080303240103140a050a0b220612020a0e09030f07122705010e041401080d270e07110708010204031403070b 69
    0x820080c440740821500d4040d80e0040d20811030121f04182c0005918000c0b10616124409407802a0b88900000c0201c5c48440795294069001c10014820b0342007130441140d001b03110f5803c40303040a41d2a00e00b60302e181d00c1150b0b6400003804020b00d00c44103044850b06851510800d08052100c0700c918801490340340401001c211507030392560041000c030111903000d5518040c01901d5444210f1285103400301c400d9070014200c9000d0b103402c000150034070400c154160101c1c0c0c010922101d0b203180003001001084003519104031400200081d01d6880c80308802054030500c107800340ba40079480988003500b80f6905d000c1500440200a4603601c82a51516000013921002d00f80300c0140030322480840c00400e010130030084403c100340c0c000b0981400000c0d0800d44c40e0300f00c2c0d840031841d46010b0040d0120601d4000c08086d0000c051800384401d03071107541c000d03910100602d400e035400ca802071181c40c82c11600760b101140d580d44c0014184240501101c0c911110202c07200210f252105681c2c0d0076400c03120090442c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 805229577 1250 805228327 805228337
    0x40306051602070b09100e0406080d03060807051002030703122415020c06160302010b12011b05180d02030f160f0f0506030c090604090c09170105040320070801060f030201020c0916 79
    0x1e4400d42da80d40c0c0c4041c022b0860001107401017004058003070001c28203030041144038401d80e540003406281c104080550340f407080d40039604000c15640d00352603100a50059411054031072510603441001d561491a0000c00c2e08000040640f030328103106c800000050080046412100410190761211811520218180081327420a000d10382822801018201c4802ea0b011580428031841c1c0d19054100051444030040034401201030650240c0b07143c8079214076a0031800c2c0f05003c0489a15001003002f188038005400d80d92071440b0401005d081034002902d20b02840340410080c0034401d000d000783c1000d05000c044001400d41090002569804002e042074803e0b400050003459075200c07102540d0040000103424409200000c00181c03101102d0700a101080c118404401e0059805000346400746800d900d90114a03c100844151013943c0c0b01c10f0305502c1c4c4200c140c00070b174420003445124010441c400300e8280c0f20341544002170500300d0085025106242413424800c240d9402c240c00d140304107141c102 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 805230827 1250 805229577 805229597
    0xd09050d0b16170c1327051902070b07020d020a0b0f060f0a03050a0618150b030f0d021f0c09090f090f1b0e01150309050102040306051602070b0910 65
    0x2c00c0300d0f031050103950300c407500400c4018840705452800250252a49003940c95203000e4076070100884942a90110051074002c09124001c1c00300142e10a40d00224003081954820306198011026a4450320b01199612102e07010000900d40c18007081d01e140d00e461000d0000d1802c1034460711990000900000d02010004021410342d950b04c3c10440500280541041d8980d40d07a0301f4004e444d1a000c40d81660048d05014205001c124021101e149032a4041f41021080c000600d003000100f001010321501885807010200900c0001c0100100c1c4440c035600a20301d00d000b9008503654021034213183c2e801241019850766080341c208210ba0b00b1b4400a42d00041da5a0380584103101526030290082e1101d400080d0303040a01400c9002c0e602038280020070240ea055440c2e00c40781c1e0445c024400c2190780c1003101050b0b91b14611a0b009506401c0c0918005800c1076180d07210401104c00a440f1030368510b0086842542458041c0300780e10080501d0f4a600b8141218040031500d1205007100d100100454494 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 805232077 1250 805230827 805230871
    0x50109021606270f0302010506010306061202131a0c07090212010512030f0301060314100e13080c01060b042c01060806191404110f040e0907080f0d09050d0b 69
    0x30600301040c441a40c61800c0c3c040c40c1050716103030031103080c02d400650130310300000c000303501900580c401c41c0c1c0c1640d901c02c400c0200d44d24020007900058032a000c84650080001400251052091324003200110342d5513403004110f08241c58421107074048007026006002c00e40700401074888440c1114402c2d85e65641400e0032031030a506500c1411240035a4000100011503600e43c50713400030301c107603070a8041001551960844482c1318012442000040d000000000300c030354960101403406c03684190b0003d41130028040000782074400580010301c20440202e000c206800d00c03a610042441404032038514039a00ca00429000368005001d00380500069502040407922a07209048161256110f0401c0086d11681c034127504c4030302c010b201403103581443e544442484001040f240c2150380d5203645403809103443c400070254440208003401501417648001400d000c24020b101c0c0c26064040980f0110a0340400584200100d0f04000c0c043c104091815000030261900c00b81c0001105407980c20141c803600f = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 805233327 1250 805232077 805232111
    0x201050403050d0e18061e01031104150318120305180109060b0112061d09240103031d01020c01320d0e0c15070602040f1701050109021606 61
    0xd0710007031992040c250b59808160b8003003014030041d80115002e416011007500c12084c6818240c0d040c950001c00104011000f002079448248204070605001c106150901078500c0c00e034202e5803001e02c1100c001d0724104001c591510541007281521034804000700c0d000d40300c4600c1c5c13400007004c1000707059031580401d203030b4a1403908486c80260701c04020b10444005d480e140003c3d041144c00710740441d2481c414500402054000c00c0240d07451444409810041c200340c10354808806005c051680c0100b00010800e003440c080c034201d0030b11201e0ad8590495146180007810018600c0720628504c00406c03c050241c0e9002c1a42803c091007485d201500c03000d030325080c0440c4d00184050042003100382c07194040031250b0078050407030b442c8046030400c08480c943e105952152451503c85502c00542419040302a442d10042c120311401210014105600c5100a80420f220390308200b01005602d081c42c60004002d014450151618050a40c01c08000d41160412800044c2009143e903071036014120040c2459 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 805234577 1250 805233327 805233329
    0xe0a09231b1608161104020c1510030203030432062208031605010b0405070c02010804060e060a0911010915210c0c050d0206010506031612050718050f180402010504 72
    0x20f150382d07503450610111000c0344104030484a40700c0102e41400706140074420340c1c0701084040090720300038400058010003128000c1040400740141100817015880410180002d005502180d403514504c941c907014858040c4550050080c1d4501d0340d400703e68440d0015100280d5641c41c045204091140540920803d00e4100000d5407001150b004146000c0718000e180d500d000714000c001d503690034004d01094980807030380340340440c8480390002e005500c14042d40d64018001c4000252015081e410141450800d8580d041d0060f02c4030481001d10912811030302d42c0d11800d00b0051107480c50f00001e1000141000c0b840300c1844510800205003951049151200701440c1608102c26180100c000e01440401041592507100d017102400489000144e02da0590314020103a034110b6944411012014040700103260810105510000d06d020440c003640703010b4002522403d04981d441c4403c0c0081c0801e40c0d00152003200b4010003206903850380310201941d001e0802c52504a50ba403400107850034404c03 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 805235827 1250 805234577 805234583
    0x1c1d01020c0d0503180a0e06010f020f0604030e12031e1804021c060b070317070c0b042109060c060e030f03011805071e0c02010e0a09231b16 62
    0x159014410002c01000404403807040818101190390103000713020074464140144201c590b8640b01284866002b00417042d0340345013030f01c100d52600c40400c01c0f00b410010192400ca020802000c085c1109142c80b4104084942030034008605190b000f0a80f410006008101c100d020170300066607614401010142e003001e1103010740b09541d101c400a14400c4500b015680c150138840c60407801140c02d0020900300d600c82da0305903589500308101156086d207008805024401840309201c852000038003a903541a00c05c82c06084800100701c070180c403500b050000b2000030810814648014410b59422151011886070441e800056100b0380c014250720b944540351900c0c000e100040000035101c018845d26550300c1e030b42010180301c16210a03406450102c2c911001c05440e21561f08103140480c071803010050380c140145801503042280c0000b00303d4a5590f134000b4800561282045c0c4501c0201e07015500c810051006081c071170303241c4440300e0354002141c2080d001401000280c50240e03507002000201c100d83d0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 805237077 1250 805235827 805235839
    0x909030f0c0c0a05040608060c030601050702090403051e1e0c03070c0f09060504110d020913050106030b01020f1603030f0e04020d0c020f0c0a1502100e07030201021c1d01020c 77
    0x7608400d1582d9181c1c6146014459800c40c280890f042c14980128002c48203040d00030a03181e05c07100f500c0c0b00e480c0c10081c4658101b10341030100783d003d84c0e9840a41400340d4044e1b01c1d07240d170324501c000000890290381403034134030305607400c01c0012040300904028000004169100c42d840e40101e00060341036114150000e01452440b45010039000c004c031184c0d00440c0c05041c0104203441c0ea40c0244415101c002040d486469001d02c0011540851600140143c0800a1005820340c1030020400102c0e402038001200080c1d0721651364582d960100a00070741419104010425500005602c4c2e82c3c260b92400000d04206101184080300e42c001c01105000703490080066440b900b442032004002e01208088100510a88100d01398107600400c4060a0460140c9209110344c2002a0304107100c491610b41e100b188214554455420078900c00c3d10840c241c0fa0010303003101451800028a449580481980f94480700c080d160041074010b2126201c2d41d540a8101d000341c0024001030b401d104038403041e10741000b = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 805238327 1250 805237077 805237087
    0x406031e0321140a05010305070501080603010e060f0601110a17090a0e09030307030c0f020d050c1222170303160306081603060609060605070f0c271a010e0909030f 72
    0x1410035000f9030001c100512651095a6407a1290800e0301e00030b10003c2d0403604415001c0c00954030960320701c0c6e4855405000810003041000c04285042c0080390000c403105040b00510100b5a406501461149102c0006040303d0b411505c40c03201e065000311041480702800111600b0b9520ba010244006040842c6850440c0c50104000c40c0c60380d10840310440001e1900044101300380c0210042d0141104035801044014034460040e07846070312543d40d03105144203050300d4001c80e04032007000307000c0c00c1b003c807286590548405517040012885608a1141c0d039504c1c0800e050000000401e4a50010800050740c01d5414030440540040c4542d80002e0302034010408140c00e41c5041c240004116842110b041000d1030740e50301900c0450310207014100001d0004c0180b80041340c1c0f61551500104d004002111f0100d80e550002e40c5180c045a101e44c140000d54603448840580364030603c83c500c030503549845031444510340000c0049074200c81441c4903c8030b0748081703111004104192480c040d01c040c051641c2d8 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 805239577 1250 805238327 805238387
    0x9191506030b0306062b020a151d030a1a270102121501020c1905060313030905040b0a030b27250e0403081506070b04050c0406031e03 59
    0x505042419a80079103d000d000c01c0650a04d5070301d0b0030b204400154007026034030112100b01018201b16409036808a40c81101280204592500301e802100b0750701c4015820304101072031124800800c0c511032094000400d102c0100d60408101681d101c1c020580d941036541d0070080000c1118019400f0054040350b46030780e41821015402000c081304a841a4404c1d650703641c540c07400104449800da80160010b281454803814126090305502e03d0101503802c4407904d40001c00c0c83c5400c212420214440c400d580c11301499000f5034000c01408040e50144040d00314000410f00e60045880000c0400105100082050300342441d400030010140840c41c540040c00410035903115101034130010300076058070300d403000b441c5c00903c3c010845001c0305005825030b580f070700c5c291283c1c20700a140d8010400702e191710401326030310340004080051140b010100207003010f0070309a1400c02d100d000280154588101031000c14114844040400d8401191036103c0034540303400c231550b4095a0080d415040c44040300021 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 805240827 1250 805239577 805239581
    0x30a050301141002070603090519030504230303070f030e030601090204050414060d0b060a0f120b0106021614010c081602090702120d09031b03030f060b04050919150603 74
    0x1260204a042d070180c1c0340d00700421004103030072140302c0c015a02010b000c01c102c0e0f0003a00203000b454003410598a080301640c2640d000a18010011000258001018071455200d00004d8020030305034002034800b0460013001c00c3d900e1144403c05000042c0d032444100801d44034119002c03010801405030b401a5942e01e03a400080e40003400380c940300e0fa0030300e81500071000080c1083c5118a00040c000d00007130115484040300b480f405090b140c0c018464103004a141d000102804d0000c080600114000b0012800c19030340852041e04504119041030181040c01c03480704500c40241e07280f000d144c2c2c442e400f00384010f075910541180c000f0030000c40414000400922074440704c0c0c00034003e0710380d1500c42d503130240220303124401c40549040407082030140c0745041003d075100320480ea1090030503070700f10b06507070202c0f4604050000040700000d4030f51001b03100c29029800789000a10940315210b040900b041d0008081d100c0045c2008004804800c10400e00d400581000f410070034511003410b5803a1b260040200 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 805242077 1250 805240827 805240829
    0x1903020a02194a0a020906040305030a171302010c0b0720030c0f210313020402070807060c0e2b0c0303080708010506030c0d0b04090602180909010c230c030a050301 72
    0x1036010711100906000c01e803c501180e5011121103803840030340d038001010b4000d4005003038030341d0494000e10000c03000034400c1000709002d005984840c10040d071410f04a10302c1010041c40200703020407000c42000180d800c25002901d0580c42401d500103075a440c0004ca907059403141942900407032a00e0ba80da08404080020701604540409a44003203030030010036503499a10f5103155151900c094554034914008002554008100d10320848103d000c5400040c1a44c011481c203586600b00040e2134030400140c1e100302c00120001d810105003030341c0e51100040001e5039110340301d01c0301c000d4803a0761080c041400c0e90382141240d0114401100b20f1712401c2c0284242c600715141800b06010000108541c030b1312005603840f980500450500e04641411050050b0941c8040701d5000354603024500009141400605805c0803060101e684201e416400c0050143d8080e2140907140d26001c0011142c59110081c8c511580200021503c81d1440150907150b92240a100d070311503000203c1c441c0006544100114 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 805243327 1250 805242077 805242149
    0xe180705040303021204051c0f02030115090509010c0e04020a030e03040905040b1f061115090c131406190f0303021b041404120309051207051903020a0219 68
    0x154551744094081c0510300c124002d140d44442c0c800d20b008018148402c60200d181d10036000d98a08202d1580442c0c00d44001c5400c0b0030701400059400e2003004854402e00c0d5000e40201c009200c0b8011910019042604c0e20b404640115000a000059680260884100d1403210003c4035a2140d0f130345c0741000102400e40c1d045419649100100c0c1c1c18181f010b035141f8642c01c918508007140352400d0350648070100030004101d07680c0160b200700c0c9030701300b68404801c0c480e00482014048540032401000004020400d54900315407800c0c03042c032150b45024100355444481a28001c1840001c0052480c02c940a03030310004104400c4c410100405a002c42d0500c40000007000719003c000d07200f01044145c90510b056601002350000c0010b000c150030804070045801c041c00c001809001c0c07520750500345200852640e0701040001502810080308102e113158050041700060003100496500a48030a80130001a1181c000d50900c550b4a0a0180c0e20b1350051135042c81c24101e80d00c071186001e01c01c2d000d80c4920 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 805244577 1250 805243327 805243333
    0x40b0603070308040b070c1701062c01090b0103110307050a020615030d1d061611010509100e01180311100807050d09150c09030c08011a010e18070504030302 69
    0x4510182000189001580d500044003804c01d814598045101d4024410580d00e4030614200017401c80c0400c442130007184030707030400401c801d814051014183c20700c0450001c0b20080803004240c6586195440380c2c150b6200300313804200e40c851500104d000e8040c00703c8117005090008203000c2255000401040c141c00e0756001e581242c2d9940d00070198500201c080705803d900031044000c0700301d100e042800c1d0305072550f4003002100203403600814415000200360100405003000c1040030301007a0404a90340034000d20342a882c0c000c044012079050410035940c3c206014242d4041c204a80c010004600140c16021030010400c2e0303282445903180b403071301100d18000d46450500c500c91520801c9007074860012612400d24108030402e00a004003101e0405640c40080d58900c026500c3d454091040c44044c9950f5808001d8107508042c805130f100740d40190000da14184508903a110b11512271032001100b4201050141c1e84400032a155400710042d10307031100c000c0010441c00e01e030800090801da038066400c13 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 805245827 1250 805244577 805244581
    0x90609062d09080d0c11010c03020a0b09011e06060e01050a03180c051c05072d0e0601020d05090a0302060d09150606020c03010902090c0708070813031106031b1e12040b 74
    0x109a030704000c11500507080c401c8401b02071500d54048e009520700a84284121240d01e203c80d200d10506400c1500d202080341d449035080b0326034141c3c0b142c0f680c601038a401c004220a1746001400341040c0c0b4500c10040c184100131034031000071400b9901014602c0724500c0e1204542c1503901c3e008445030568011148a03c0e20945018100302c0e91070504284c0741d500400814042c2d0429824843e5104d01c1c18821160401f02140c100701310312003002c49002894001c07004440d505180c000642841a00c004800c02c0000c148008445941d81084450403250140c813501e82d19a02d130351300203010341120003001c0c0545a29a9529000580f21f40c046004c5540d65804d842d000d04070342080500780c0340034070000b9511440368030100754074281c10001000f2503481198840d1900d001f6540390f4036140c10040e03400000c0078100c0002c0041c45603540c15144207d104844613451450807004000c04095501c1c42800b0981020070180e02552110300c1050443c07100e512002d8840654626030640110b08841c00c860201c80400 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 805247077 1250 805245827 805245853
    0xf0105150108130c051e03100c030b121506060d1401030332181207030b060a060f0f020712061e05040c06030f0b120a03030c090609062d0908 62
    0x20b1034070080c81c0d100306403600a51805c0d0401c00880400d2a00d02c04082e05169248a680d03000c100150203001544000300754414151320140c2124030418119008500c04004c01091003804104070303240c1282d800d40d100d119124800422214085c0311200c1541a26282850710402d41222a1390704880c4a81d40342000c5102c290300b8255904101c450094030300200d451044a0880300001800c060151715a00030403944600d00000c840c200340340050f400d16040f6800c00d1040c48121010944c0c8007074103460240045180180c0204000c20b100284010804c19100c100159482489403500410400d03003480f0b803110044c18810300809903003a0800c1428180160311500440c54000d040c81181c10281040072546408802e030090015081c10000c442e0381e5191003891551050381030607041c0b80500081052030760718600501240c011040079024003802c0c1000300501c0790300080101c1580e00910300010403602a11a40c1c0c03120000455411540b08000642c2c0306d850303406000034007210070040443c0c4030360340866 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 805248327 1250 805247077 805247101
    0x3040c050f10080402061318061202060706150801110408071203051e09030109120e0f1e030102041505071209120618020306160f021605040e0f0105150108 68
    0xc240242c2003011030020410903405260926445400139219034030b0281c054181084d664401c2e0002103424030104034000f032910700c6100300005441d00c040c0c00036a10b0800c2d000a602c50080c91001008180c0f6074850108200c03035001c401c0024044040203000c200090928078102d90001c1c081c03126207124904000a00c001d426200b412a0358054480c540741c000c5062417520b1803142c281d07030710f0034441081140300c8568409101d085ea4450055907150001501c3d6000205a1420360300031034800e0040480490041d510890004071178119140d9280e140c03842200401d003e406030781e020a90842c1c1d90900b07203462903001001009810303c0b604002d0610806c50200741d4980000d03000b5085550351040321040055016803110b5041c152203c0e10f4101248a540000d1a105085039455450200b032240c407240c1603081000c1030410212030000d0510114202603100c8010031314440e603403246446880401d0700c10428451044030000c200002e020b1031800b94400400308250300c07480c034002404540040c00b251041 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 805249577 1250 805248327 805248349
    0x29091b0a0b12091e07140d112407050604050c090f16030b0d1203050108032502120d081608071b1b03060506041812030e160b03040c05 59
    0xc1c5003424550042d488201c4224020002001e41c40395900c03824148540000c03030101c413010707003004050700740c01e060388803125010122070300703014003034000b5800002800c002c4203500c01398080e208075003542c02040403400c90038511060080f020304001030715003e200000c6140352095000c0da0440300900703492414082c501c24119600465100040702141c4002900b0481c107164680c90b240104441c5e00c2c450000320702c01600c0714221041103150140c2e5000d21f401d4041c0398010319440c00a14100440c1c80c0840c101c80d050b4070b50305a03881e044000c0c50411540d074440d00540c3c030802d030821182070301103c1d0005020b509054a8180e04c1000340038850400340c4c4035200d414032404030f0741c1d00c50400058020b0712980740a0341603c11146061100a8410064203606400c170046018003400300d940d04000d02440111740660050050b01288130304800c001c18041c981c03601d00310351035203400078016400011950070280148101c08450852100001d80308066a001c0d5008900500054a480e035607401008000011 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 805250827 1250 805249577 805249589
    0x12050a05070b0c1c090312050d060501090810020d060b0c030c0f0304060f111c0c020a0b0f0a081906030b160305011a0f0c070f1a1629091b0a 62
    0x40320400d013103a207840300d04410751140703401c1407020262a55100078180c1c4001300c2c9500000c002188400502441c0d000d0203006103021700f0700554181c1005c24081c6c403030001c000200d40d880d400058030041000541d00c45801030446441c05901e40d01d041580310b407294031204004085100e1318034080d080c104040210b40460382e140e00e42c110325820740541035807080300c0107d00d40f80034040c42070300b00302241c5202d41c1201d041d9141d41e41c280d20303030304107204002d1001c20f25042402d401505000c3c6140350518481242c136041c1c510308010040740d49007400d4860300c019680740c1105940c10801e0000c00c01c0b5442c0d00c114052000d4212800907103442d0b00c800c900311002442540c0c1401107414031203080e40c019400400e8107070081d409003440c0c07030b458200c010b141100310307881615061403402042202c84924500c0a05c14088000007a26110494510007030004c0100f2000d080c1032981105c022103070744011400040402d043c0411549880c00f071410a07141d6100017040c880380d1440001c01041468007455180c10340e20 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 805252077 1250 805250827 805250833
    0x115090b2b110a030507111c020f151b0705011406040e0102131e050a0830030703110c01091b06020f0a0f030e061909050a051f020712050a05070b0c 65
    0x59803007022406010080c0c8410280034031031001c041d21010a0000490340350034045000c0e503c23041814024504421609103043e00d400084840101101341d041840c3c0003140c00f26400d00d40d00703103d02140503030f100301c0600270180d41c0780c5541c0006201c105800039125007000c4608000b04403042128909030b108403d031400c160a10003c06124100c0703480702401c5c50450001130410050b4580c004101954442d8018840342d501c10051000d0300e600c02501d584040d11140b610ba1030b5110184020850382c00050020390a16488002500c8c1d41e06180f030a58548807140f0000388180c02850421140007c40103088100e521410b01003c1045400010344031001d0414400418141126450304d401810322000c04404001d04414002c810381da550740907117420199060300d41c014403103104019241d0381655000500942d11640704110a40d03c1c80400c810b84e052951903100d032040c1c00d1004034206002070b0405c01c040010341d48a142401000200d01c4c60980c4500100c42c1e0003030f180d0480030013500030034148c0c0003907038 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 805253327 1250 805252077 805252087
    0x2181503061b07240e071701090201020a080f0d020a18080706020703030e0a050604061e081e0411030102040902041a030606090d050c0402030403031a0108040b0115090b2b11 76
    0x54031030b03494120403401d2265001c0c1c081044101c800181c3c1d039442a607120303a9000001c02d0040180d507000e02007c80086a00820001d03183d540040d4a901e40d640014203021408296807800c4d003042800c07504604480c0100715a1604007801c003402480c000a1982082c5441c50808900030740001400700035201e06030004d00606d8516542102d000d4004a045508000520b00000b251740f141c1f00a8005032900352990141c07152825203d89035104c45c031941d0810406054144030115501c460700541d003500c680078484042c0e9981c02e01c51000450211050781540c070010700040c01080f00d501070b2059070200c842404c04031040032140d002d640019a841a800602040314100d40d01e01100c80c0400203210b0ba0a60318044801e40004049800c1220180d011948460100d0500b45400c06040d5041c2002d0800340c01906050700c40b208040814011003c404d850460743d03c0845015515860082c0b032505d6407190342c2c0c41d504411240003d1100080801c1c0f007a00000f40340b917840e441c00f40102d0100103c20160a00d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 805254577 1250 805253327 805253333
    0x30f0305071d04060f03030e1513051c0f0b0a1409031918030c14090906070806011403010f03030e030307120c020103090812060a0501050c1902181503061b07 69
    0x550690b0680c030342c0c0160348000018140d000b01c6282c200031402601d400c20401da00409001080c079480c20350342454a003c1000444400909001906544050f1090403001c1041071104529010b0254040c1142d0245126401000350101e410f1744101200c000600112060828440925906940902e00c0d5007041c0000b01da62a030700085030140c55503510301601c6140351403802d1140343e000394009642e01924104d0034080000d250744104480c10050721605003a103070040a05454050250441d010021034102042c16a031003849000303400140c05d80117541ea940e4520854150204512003200440c0c80101004460b02d40441500d40c21078014102014042120078100e8100d0b0700303400c04070306055550031000e020449800207002c01903100403006105090a904110013004203900240c10081b04011145c5054030229036180450000010620f41d15081e10001e231405c0c4011124580d6a00c0f080700b04083d54002941c3c003254050143d041e21800e85524004050b06401e05440f44a6240c01b00501000 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 805255827 1250 805254577 805254617
    0x3050a140c031b090a09120c11090f0a09060e0f0c121f0207050325060b0f0a05150f0f130e0705042610060e01050603060f0907030902030d0c030f030507 67
    0x300514891000900b0303000c41d9941087c0f070650b40c0b01c020000324800074210030801c1c001c0104070584000c84000c0b10a140480825001410050409416a8035103180204001e144d8000021100d0301c42c0590302c51484030b140d1180c4c0c0d00040703401d00748a0030180c40c04d083c1e205004510207030300c1101102200c400c4d45154146502a500c0b07030000301c5181c17004020303240041c420202d001c0030140d401c001d040c103800700c0390a00100707440b5030b00c4000e8800e4032003049003002e0742c0d1484040000c403802901c615002c1081036078484140c0c00381c09464840a40c0001d030f646103410f80c01006010388800f40100c60106505c90b0380c44c01c00140101c50110124104210034400f9888540916001c05441d410003041543d900d030049060040c9000075074040c1d510f5002c1400b20600c100891405040d040d181142075203440c0d03000030740c0d2407014414039000e42403400108000a110384c0011110580241c2122800c40b1203840040485a5800b004c1d070000380d03030f40c1072001c00314842e014040c018100799850000d002c45102185407 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 805257077 1250 805255827 805255831
    0xe09130209040804032004050a0c091802071203020903061003080304081605121c09020604060302090112180c1d0604050709090f021306090e071803050a140c031b09 72
    0x140f00e0505210003c0004d07007005c600ca2500340a40c0c00a00d04282000501081e43c00282c65075003a035040031110f6200a41c00a00042100c0799150100d0040c00e01da011100280b1810b0030182040110003155079019805400508104006030200c40c255a6440c02814201c03583d4000107110110420210b400304825030054940c140c0c501016580c0400b42d81d880383e15044209004808042000c100e0340d1a82c502c0c0e4003400d02c1414905014400a4050740c005180c900c00c6000d03040c10701d90b001c1040d410507445000c902e20416151032042050307a10b4424010300c3c0d20304c002d200300e480100d00c603400b15140154404600130001c42005443e002e80b03614040201030800201240704104e9115800900040345c2c0c0104610014041ca005039640f0078400741240d41401038001a0900c54110400c2102d0481140b0890b40511207142c1007078242e41881d160702421005030f10140581c4501c03840307030081c030821681d41e40011041504451030643d080d01815105d44040b1170304025450400301e1305400b818030300045a = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 805258327 1250 805257077 805257083
    0xb060108190c020c031c0203040902180303130302090610050d0902130c05130501081b0d020f1c14190504110d05060702101b0c0c0305030c0309010e0913020904 70
    0x1800001e000501002141c844450b2800140d0061303001c07000a04050000006a0509241c91b4070040c100c000040d590340314900c00d030622594002244c460740300020144044030040103044e2603440c03955459442e921881808160b114203160008620185400d0105401803646525038509205500702c143d001007004c1d2a050340c002405440e201d80403502841000160100e64079050b480711910a11140402d0075030b04800e041c40201ca0520880c46120340704881205401c4408603550b40c1e00d203a02c0406400f5080050508440128255540b00c03c0311054024808025a007040314500b88244460b001c103040d940e561540790301c1250440c2d181059041503a10500803007608840a00c0c1c0300208400d01d03900c1c0310958494029505000d030203503040c0300040301c2b6001c00c0014000c40e42400895403000010300c0306813060011042d4414208010491214000d64000003500c2d01c9801c0342c0c1c1d4141e1242d000310a158005103d036095109245440f0445501500c2503024459015540e035003840b84031640075100f6 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 805259577 1250 805258327 805258351
    0x80c0904150608060a09140d0e13090209040606030614010f0603091b08060f07020609340305060105010921080a1403010902070b16320d05061008040b060108 69
    0xf140b5250200500f80c0540d01601c00015802d040d410075551038604c400c0c0f0b04900342c00202030401469032000401140090444099641260102035a401072050550003900a1410710030403084c07010fa94042400c59000342c42c14844803540720090030000f07800340540000540803103402e000d1144654803d400c010b10444100b100130f880b1141d050f0b406081d5034040103c2e64441c03c2004000b0b49021000d07074100e0202d00061000382092060151100c054508240d42c01e002c007070080e80b10f00e582c05075030700c003500300c2944071010b10b912424200d890b680300340203c0c0e000c122038020000c0c218101d81c02d00005170540c0c0c4401980d400459440400d036504c201411010031038208819103920b036010b0015402803104d2500141c0e034010314600000e480c071000748442c2100280c0c5070031102071a040400d00c6ca0b20169140311003408001c425510710000340d22405d82d0070014010580080c900e0003a4090340c0504001c80300c0e044d202ea0080030446078140200c0b0020500e403d0301001c19001d5000b5403c103500602c2c56910 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 805260827 1250 805259577 805259579
    0x5011a0405061003152301141201092c0105010504180c09020f130e090d0507080304060c12061d0906011d07121107150b01020d1b060c050d0501080c09041506 69
    0x1940d240351401c2c001c8500d191401007031ba003081d83c00c8103600b440d5400d01c83c20507041c00c913103401c00c42d1400c0c0b0510800c9802c940302d04110403200300810f503c00070500300c20414216041280c20b42070013008240100ca0195190801145034410505441c0c0e950b08d50007060b00c08000d00b48280d21019404c02c0102482d038034024049840a81400c2d0303148400381c0800c5540d181c0754030b000001c491400f40c411841c1002e01c9410098040440c502404a80d400b0303402200101c2d245c0c00d0107600300c50014510390000c2c107051401030081030714001241307908175031240b810b04021651a0401040c0e1103c400b032007040381c0c0402a0444421500446032507681c00b2049007042681c00d8400080481540c1d00ba1510060f000305c002806010004801c54600030468510310401c4851034200003c0d5482c0c4441841c0b800741b107040305c914010b43c24608200308032941d1002c8180a0103040e183d01401d00c3c1c01445d22282c11134100350011421680005442c2c02442c4000d0541041e5100c644622815980c56030407040240c2d02e4001c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 805262077 1250 805260827 805260839
    0x150603060533030f04030e15090f0d06050a060e01150f2007060801080d02010c050406031a060f07020108071d060309011d0c01030b06040305060a0b1c05011a040506100315 75
    0x10145100e040c002c104e89409192901e0000d202082e02801d4500c524100f80041c0007899190060f2010b215064901050420302c403c00202401130003d0001c0c074a03400c0004101c850580c60304a18102c80c9007120089003640c13600301070200000a030350311900080d02c480403030a180344241c0d8044003e101c0035030030003581c01501c843c1a04129080e040b920104a042c4010482003908005408000e03009100070030021149100050007449030384101ca04041d19096444201000c003201c1c22008000145150f603141200340ba000040c3c2c014420907404290101c0025504034040c6a101d411616200034012003414441c3c104035980d040a482c01a0790340d45d919564100c4041078400d0303044039015400a1034901d01d1200014185c54454032064040c00c824881040021400165150404203000010440011500c04944288040702c0031200078142218010203121041d1702035042c502c0d9052410300c05240482c240f10907510240c3e0450b402600d80340b400b9041c030b40302c2d030700c007103c444c011070f00c4900d80c1c6980b40 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 805263327 1250 805262077 805262179
    0x31806091509050106050a12230c030f01150501080103080f0a0c0b040b0411040207051207050f190b0f090c010809030d0e1f0c050a1103040f091506030605 68
    0x40100c416039900c480134056860101e10050060004542071841c2080355600c149488200002182c6110740c0304032500300c070f0f18007408820400c1cae07009812110b843c0c09840343c2501030149055070741c06074100080042501d504c180b2520341a00d0708140c1c820315107a19121011071982c880030441d0104186640c0400c00102510b00580c0194012401c003811070a06040c581041480c1c0498644a988104200c00010701c021502c511240c500000340390300c8021600b00300741000040d04100060340640041d014444034400c0208030454000c01c040059a82c401106541c185026121401c040c0d1018540f82e04075841410007907070000c0010140d82c2041040e00b442d40c10345220350002c403002d40000e458528001c5810303101588100002d9018414100803c601510300c1c45480b40c221304004400c001680840b0082045900414a281c04100300f40e59895211000b4000c20756500c10140044800103142c5129000f20015244014501c212018a440000c0b059802804035164440345080c03445400422032 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 805264577 1250 805263327 805263341
    0x8250b0a171b0d09020a09020307091202060903070f080f03070c030206090d120c05013204060207150912020a030801050f0406091803170c0301061103130f05100318060915 75
    0x82c00c0130842c1e80c0d07588101708800f000c5400100206106108000106500c800402d08883c0204581c7c0c840368414008110b0070b110341482d460b010701c10164000b819400c00e09603030049883c180b0a84000c00b64070301846480c0d101c4c07068081c01c480b0040c1c13000e10161410a000340000d242c0100b003800842950f80d40e00d009403006120440111384010a908c0a105080c000c00410b403d80c0008040c41110b42c004114807000c46041441440300d007400041d08125250303040307a410a4111140541200300c07505040003424000b07004880600c0348110080341580000b9091280607850f8941d07558980c24102031200c0401c512064a901585586002a8402d9144909048102010740500c1652100d0130045d1107250805541103505000c60304020840c0a031500752815645140360014050b908496060702d580a5044183c0002030a00d100103041411200408100c80b0252412000d0084410040c4d048074440c040c0c007010602c03110701480c005100356001181091040c40c0400300801480c1419048601c8 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 805265827 1250 805264577 805264597
    0x210031d0706121104260a050102070609110619111219140301060203030109050a2901090801020c030d0b060705160e0a021903050402040608250b0a171b 67
    0xa030301c1c40300c0f00040d10f4081d482504414810341e9180c84c2c036148061038a1981007440c20880c050800b41400c3e150014030070808840d8000b002035440c6c0ca8a070408100038100d1240843e0b4846194140f003000d400c2c43c000b0343e8000440f141381800c0c405c9120800351000c902c454405600390140c0b01006410340c031403202900318101560700c082c1d46101c90110290a020b102d10314001051403e0004205071540041200d040d1141c41002040d103880381d620810180c4070340c4401d100690b82c000707081034082444024403074503601c00b6aa90701d00a0307541c0b00c07602c0c00c03032081040c0403035160030421101d00390401c01c6d0420000340d03001a204c42d02d00001503e48070705100e400300c0e91002c2528440030400200c09250399454005030b004404525001d003141207142418428080a4145a242e0700000c0c00c0d980c50794000401050080300303880003030401c2c2c2550040400481e0031a09000e45041c4045003491080c0191040156107885040381c12019070408486504000e000d51041d98080843c00c0c50a504071001c3c2003d110 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 805267077 1250 805265827 805265837
    0xc021c06140a0e03030109180803090d03050708062b0503040e090c0102010501061d0d020901060c0c090606020607080a0e030403080c010e01090213022115011103070210031d0706 78
    0x400000501c84040301910b551002400e041e95807191900100c21071341141da12003400035100c002c1240f0244012442a4040c00c088404010402100000b0400003075006055408001c180d03181d2006542d40b11003a00c2641e049007146140c403c0e1080000551404810345803011202c1e00f900e60703103c1e481d6511541101354560224418042019410000d400300309a00740000d11480d03041079001810120f04c01c644041c844503070503004040d500c03a030710b0645c1c1d0160017400e0120b080da12280301a2245504480840d50003941101c0000c51860700d00c60b10b402e0f901194003a220036110510200e4110001600c15001c03035a582890002c0700c002000148011485000b00230380740d098042c00142120210760300740c05607905200c500d00044c0d5070310604403075a336000e41006071135001a080d10601c0455042d0203038804064081480040d203d40c0031031070014082680c5880e280d600c164041a2a1301420380000c3d0000140e00589443d9802500421500280b0b0001100070784aa29591894414540c0c05000424 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 805268327 1250 805267077 805267091
    0x14010e09041a0c03160c1a0403030b130203010e0606090316291206120a05102f0a05070f0228060f020309060306060708070c0609140f010c021c06 64
    0x2020060b41e90710120f803458003411880d000f1850000d8020f9609034030104000f1300b00010070401c8842244c1140002102c49180d249450325003c1c3c010b00060140340d03c03983d603015040c00e4000c00c50003120305071115052450016111030017485055002000041e030b0600030741c03404030203045801021030010403e40c00c010404400341030140c1100c503550b0b0416202c41c0001c100d01003e81c003100d0311858001101b602c00da80c81c1d40920081606001e11401c004186015044509034032405980000c21880340072006034510002d11944400c00107000000d80d81c000c1070a00244190a0140c4c2c0a80012405012400a840d9803507002802c1818513019004805000d0810f0a050580102c0300d88082d00260500070002ea01e0460301035030300d0258940b402d00c5107800000180e019243d284c1541d04169000102c1a00c0f2042d0386424160102c0600402c1c0000e0784071080041d0b55604010850b0704800081c0c5130700210b0301e6030001100c80b040d4200040e030304a01c28140012410740300c1c100c0860400d0150328009001 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 805269577 1250 805268327 805268363
    0x30305070b06150c0c0f18060f01021002161106030702150903040e1303020d0306080703140304090e15150904390806090c01081f0503030415020c120714010e0904 71
    0x4070640740280e01500e01f010021881c1a150102241c00090480e07821502862400040789410583c0001c0802d150020600490f03c80b00242c0640c40340b8454000b0300c0c440745107030f02408840e0004071213080040c0c2c0102d00ca15064040441443d4001c6990020b0341c0c5419116154000c1e090b100740d0350814080000c0360f1490a25a040c046640300c40e03550f2606102c0e051a1120041d500d0b012800040d0248030b80034000408030300f00b04203c80080184410034011480c0c890140c6880f640011007040420748590002482105070540301e03001c0010003004011580c0f2a40c4a20244030f1401c0c0c40e950710a0101c041c205828020440441c14000500000140c810700b00300b41c86013080350140c2030044a600122040071513a0b0030000701030f40a0100305e658070b0074052240e20340c4864400341c0d2105405010000c1d01040d034030641510340061083c1a02110400038502d828840c83c00300f2004030b14159000030109200c031214200104001c038405140218000c101c1e0000105120025981254007030560044c0c4105 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 805270827 1250 805269577 805269589
    0x7091d0108030a0e010302070c12051e03030703020706140c03010816080c090405160801140106050703020a080a09051206010303391a0403021005060a030305070b06150c0c 75
    0x84440111410a05549840c10080c2d0341d008a01501c4203000000300302c9503481e4483c0d819140926044044c1c442003d40c0c624155040c171840d050107803174030b024695426400109820b68035003000c80e100025480c0d0b943e40c080441c0250800c9a08884c0603407190705c1451900c030703007150182c080c4411401c03450f525494040c02603e45150200e078103d0240c0880810400c140000c101e102e0541400d80320580e45517100d20704141000b0b00042e514030f44040015010845190560029052020152440d0216601d80900750341c64000c8280080060348202c07040c80c00a400d4002401c0b0f0041c482c1007504c11151104009000c0e00c40c0c0d591007038000c0d481040104145076000e90031030001c100050b010380b2080c240804450100b0030711141d030034026081403504810049203000310301002d82e094101064508080c5002503c652160344011078050030440850038500d446a403070012298140c13201440d000490341c4154505100502c82c81c1e00503502c09a80081d402503c0003029549a500050702131100c4510410074 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 805272077 1250 805270827 805270859
    0x4030516060212012405090409140604060b09150f120c030f011a040618021e07080901080903041203081008010c050a0206070e06040302010c050115260a08120a090b0709 74
    0x600011703080e15a03003003608031045654003e030a03940850400280e0034804202c09106000e544540300b000c08000034090340350312691100d041203404021548a610064070120b003490a0503074422596200e086881c03034288001e0701c00c0ca070b0007010b880041c540400084e080404211800303040ea512800c0811011824a00500b40003104503800c000842c24031038034485a480000314078107529400103084000341c8451013038000e007800b1107031607655841661601040c590040d124850104000700c3c081482c220020050f10151140c44841e4000c41d201c0c1d40b002c5231103400c01350004842c10940c0c103000c1003111082c080d2890040e9203494190369039084110091a1900041c14041040a001c03d64038482d600c010032901102d409191104003001c2e5400c009005000c0740009211800500034000b410f80401d40c070721704411140c0e003004c28480e00d6807000552609204e400c01404854100f0644803400211044a81c00003444040064000015924440b4000050b9444404144c2000d000c001102001d80242 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 805273327 1250 805272077 805272119
    0xc0309020306100608010b04141203040906140f0108010503100f090507090c110303040f033e07090902031011071b0f1e141203030f180d02060403051606021201 70
    0x103103400d1a00c0c04404580c418a22212b224583c816032205002000300309440c081c001c41102005265a11040d50040480c00110980602c190010700300e110340c0681d410078101c40d00a009004007001d45280000101580803d184c0315a503580800800708100f005504040c208130100007802130309a80000e45080d121160380c0700d1503030080081100046010f0000c0c0400d680c18148030034448240318020440b001c2e02100f2040000a600481d00160245041c06a4281c006020b44680a40f9951390700d081d6041d60401a40640c0700c640b6815200b505a404104018900d120050070103900e80e41d84001521000c8240003440b088801c01d000c076501c1089000c0080c401c3c068402c1003508601010440d00035103204400328444250800c240940320310401520208410080d0390b520325080071482a500010345100100d5a01c2850784041460000b40e2014139410640042146581e0756a0072111580840410403282520b40045400601d441c0082d00b086248104485201e44c10161000c40d0b041000c1114 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 805274577 1250 805273327 805273349
    0x91b03060510050d1515020c010e0103060303081501020f03071a161d1207090f0c03053d06080403110313051908060103080301030c08010c050306040c030902030610060801 75
    0x22400c1d0b0004102c07804c0240c11800410403001e600307510701c8460001e501c140344c01880c001020004550115806d4140d8000b40c880c001c007040c915004404845940c04001c000c44e403a203000c5400803000380e05071961280148112081c5c1e40c00b81080d1819900600c00840f00740b02c1550b03084584800044107075600151340b10b4034664803403090b44024000c80c025240d900000c40c101c80c0e00c11a503150001d4000c1501e04a208903050181d603540300748003c00304000d01c40e20f000d141c13200e00c0d5019442400740714000d500385500b01c0d5a003d44d400d201c00703000300c4900c101a188400045558001114656100000e1040751100c520518150901800b001b00208020403030760010045556201313000141001641c0d415503401000713140301b4012062106507030700311000c0c40c07040100000800604070010742c1603a01c544006100176a480d1913460030707a901d2081450110f034042c0300068075410241d01100c00200140780c0403828800340d4020a0500301d065031b1101320608000810302c006134004a259004243c0c0e9492 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 805275827 1250 805274577 805274599
    0xc090209060a0302070302010b1017090c0a03120e2d030c0901090e10020c0f0708011b0c110d050106091104150c081902030a0f0806030607080c04091b030605 69
    0x2069446042c0300d8000b8194041a0401814400d51080c10542d6003d429050500f034510b00240c41000704403048003001030440001006101c011031040c1d861800500f00ba0b5441e4150b0340c0d0000d081c4071030b111400800020a203c2502e5680d981c0341180704410112010311085200322260b004203200060710750082e407100d0b080510780d44138507030720318110b45011400141902c1401e10407030400c0c8044104a50590001c00c080e0201040411010340499848003240e545942c0d4110160a8501c04071182c81e4803011410f91214282c0600903080d42503109118081e58405908002030804200140543d0282e41d01d1400b8402c000d1541710f4102d10103c820b0a02d4217144c5003003409100785800340714203020810125038802c1000300c414265100d00005094846002c010b150009540f5000440000000703107152640191290040340001d009203405005060303580d4800b802541d090074040c2c00200016010000000d141c8050b00c5210455510030503080652051000018150b0700c90b0341007079200340c000c000 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 805277077 1250 805275827 805275829
    0x21130b070c2705070903050a05030a0318151a1c0b06040216120203090307230901030305160305090310020706140c0d0507090302090403020c1201110d020d020f13030c090209 76
    0x1680ca01c45182040042055619020300305d0307580c990795100405920545504c8400c2003000710240c07208207035603541000f001445603c0031801909005000e048004c07a0941204903035030940007a45000510300300c0300312100c0840e0202c0c482c1c484802c100c03011006100a414204029078000d10341125007200d0660170101c840011802049402c4030040201c813840c400c1c810014001e00688035071042c0101902d6926640d05045c14003880300c501030490380b0070b03082500e00c1c042c548110001e060342d4140c1d0f145070501d13200804940b814480400c040d001d01c07409011842050f9010040c103081c2c0c51000d04050b0b00c41c106440c005060b15003480c0c00e01441401441004000704d0b110007a075801d5401000081a1600e640c0c1083d54070200340d0300041d40002c110020030060540025240385004000c0e15007980008445107000d01325510f81400d103c030250200404010303c1d0861300908a0a60907100061902141d00090001b80e4801e82c078058140950794020824800341d885000e00070309201000750724042c00710b0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 805278327 1250 805277077 805277129
    0x70305070807080c0a08091005040503070b0105030d050910090305030318061617040c050411180a0e01061211030f0930071110051801090821130b070c 66
    0x4488417003007008240008011000800035219807252100c070410240c200390400c04d4884c1c0c04501c0640e5109010303c0001018280003610713000d50009951800c1c100070048003005501018051148200a0311000100208405100550207010500071089250a030700c148141826002010464441d40e05841a9242d64218843e003040c034000020116855459140143c52a00300c1d410894216103446011206c2070711040041001c03003c982147c0c400654680c0803c99000c0880c0540e80601e180e010042003500d001300d8000850944419011544492285200c03460b07410464a0f0504000039506100012005021001c50912a41d40c03003000300c1c0380b00e0040c1451440b1007454010440c00080c1740800e00c19030254402c14024000c164003480f42c1e120000521580003500221a60b60310702d14240002d42c051600c0008a17400000034080400c0c0d42c0301000e492000400f40400124000c01c10104101c4054094030b000d8031800341c0c40da84500b41c5040000c51810150460b00e806a04c0e65a0320300d4501c50f507 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 805279577 1250 805278327 805278337
    0x280f0e0607140a05190c05040203060a060e030c030109060b10022a010e0310060501080c070510020c0f0a0f060621060b010201110a0c0515070f0c0507030b070305070807080c 76
    0x8078081410789081c51020b10314084103464098824020b1042c0c82409021a420207601c49000e440c1d0711134003946400c00c100485c4402c0e00c0250380005802e00c2001418000d0702c410071507001c000c00f0380b40f208076908040fa0954900c6a01295059954040791030b41d4600360040000031036031417004001c0f030201d0401903d000010401d84020081d00c0d5280c0f01d0281c0c0c8646030b1514003010142c10788081b1800c01c500003003c0e01950044a000c85c0c05440029411110041030f2040150000020240802030b100e07444000e600020a040c42402452100150000c08200d4010842d10412000015103603509160b0b0459255801038200c41c402151140800303c2c03003140703c4030025044400001c0000c9604010303030041440c40000a101400407a009070303140c0d000340e410320013503001d0002c1d075072034036403854402c0c05421003203c040c40890039506c09108410b2040b40c01d0f0403058403c8003101c00450316030b00c540503503007021688000043c1c0c032a01040f0316661300044154000103e81819a018246012108020b002e0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 805280827 1250 805279577 805279583
    0x1706060414101208091003150501020c030312100e1006081e06061b070b040501030b030109020d080f040b0f0d0e0c092811040320060d09020105280f0e0607 68
    0x44040fa40e414030801c801100c2004400811848943c4240031002d4003400d11440800485003403800300140c00c1d400428091030740540140034524081c950782d84001c2e6800c02500740111584181000310308241340d101481c2c098810b003d2040045458030382300500048008240344d44c035050744002071464070034410906410220403a84140c40b003d021400c01140910104481c085110b104000142c1c40c1094000b00141d4038207a0b0f051060080301e00a050a940070040000e42041c4201c0071100450400c00c0035112250001703955915081d50b80100c0e4a40e5008000d5119400c07000113100302044080d4455084001d40310005804072a40400002d02e003150000d01c2c02482c01840380499a61000961416400100a9008002d0070510b445c01e44140d421600084807e044806841407491a81e4510825180c4009103e146070688003600316002d8854140c00303e042c4107040c0401400302131082120406100050507040c08682c003000020075000140020314107100400305a60915100c11040b5000c0f950 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 805282077 1250 805280827 805280849
    0x4060308031b0c072601140714120106031107080304061a030a12030203070c050604050a12230703090905190501060518060901140c0d17091e07170606041410 69
    0x248540380449001d60320007109019500c4c0c030302180300c000e600800081c0585400e59030089c20906001c00c0065620402070003920358a00180100100c51094114000300c1c0703000180c10b410440242c1d54081c058000351811100035440c2c030340301c1e24180e00255990076040ca0490042895101c20b45030346c501040301e400301d01c04154000000840c803601134007050036010f5100c411158107250600b0030640b40ca84184049030f41240d194116000c039481054a200302c0c042c5140700c030540340064440301440340e10510303046080c885080000101d00350a4070a030780c4200e01034465120a100d2410404046801c16007083c010710001784602d10505480180441d036a10080c1c4070300ba0303103060400c0141ca60310300c40c440c4111f2103000080e80c0610000e001c612010500d2440c2c80700526180c4008140083c1c01040b100d2a0407540041501c1c0c082d03040f10b01d030341901106860705452004e038441045038051280c0171603820a90f80075106100890a00b48181c40a603400d101d10b2600d50700b44498615082e4140341301d40e42020b4 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 805283327 1250 805282077 805282109
    0x160501020a021908030712110a020307110a050a061b08030906040317072703020a030f05010b0915040504030905031204080c0306011202060703170a09020f03210f070204060308031b0c07 81
    0x194940d0f0090034108c0000124070b03140e82c0808002980ca80c4102c3d0220f500d04203025148219081c88030184064a000500402c075250414404032604000c0c242890504d40302c801c00d034400b0522820055000700c0c1844040c001c5450030341409403001380b07540305030302d131421340c442c100b00e0102d6104010340d40e40c0e03611003081120504484d4080518050301e4202a50129506100004001c1c61522050f08144a0030003803214101d0311040007030310681242d000c56040308042c65480b1a14095002e6640280710381015040d20b900c0700c000c60b26100c20301407d03d1140b1400101440a030000300203070140c5a800b03c004165940c1409928200c9102d0040028000e10380851083d04041c016000070b4008440b1245c6012036141041402010300201c0c50141d00882911500010608011864441e00c0301580c0c0b032285003c00204406d40503030302140320884050300030700114005070340b0350240b80e00a41c000d50244c2c0c0c07641002c07019041000310801c03000741d000c00700300000740d03620901213011030072148501c070040509 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 805284577 1250 805283327 805283357
    0x60c020d05030c0a0320100c120509070501020106091a011803050604260306010e010e0102070305100c141801031a0913030809030f04051203160501020a0219080307 72
    0x102030300003000740300d4007000c1800c160001c00051150209170190340c0b000a0304228188441c6a8842640818065084003080c80540600c5400c840d41c00d08052030880510038102400208590342940c44100c550821541045103690902941c070103088490390030400112940c020b015584150b0120905200705500030740440ca40f1003940600540c1c1240507540c0625103890000c00101c006a1068440044010303144440c05c614000e583c032a16042c2c480c1244040c44000542d0003465041c0c00714114464404080b00085050041d501e15503907150000c1407079803c070345001d05030b04a04c805811840304244488600c0062480038481d40a00a080015076010b010014242c650040305440e034000b8148024054102106a0410a454001e41c3c403c405601c540c042c032501d80c852440a0704546009000500c11482c020201100490880c4110381c0f51400258142c1d8051190780c80c1034801707960100780c0c480e04c650184010408003600302e040320001416551003400300c1c00054202c40802400c88003442203 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 805285827 1250 805284577 805284589
    0xc180522060314060702011508032215210e192d060609060b0f0d061a120609040213021c0204080106051504030f020d0609081201050913080301060c02 66
    0x2440e00201c0f482a06070000340342d19030b40c4600359030600056191005018003040c00c00740710015a8a00700241d880c1407034000380c002020016801d02044060500c0d0002807070b00c0d05e0380340b0703850100840e107075460206c6019907041205003010850b00421404e1038042080085e0120708aa01404403841c21004c04080303080440c80000189500105040000e03c09442085010090306030f080c0b00c4d1509008082d103650030380040d11041c1c8904081d0b2001440006241e2081030060702004040000c0080c00540d1500c1c1101c06040c20100e00700382c0c00000649990419108040e00c0c2d002070169803922150909a0210300e444880c0c80440f40015400f0540c6a4641c1c011204604084004041591501d031500d54080c000e140610440d4401c80301840c4071202c1c000000c095804503604030041c003001e4502a0244840c1601110301241c0003035a03014520005892100500081e0483c3d03820040d9a604000901108007405015481030700c180e0004400010031440440781507074003d2500d518001700b00d1000c1a5 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 805287077 1250 805285827 805285829
    0x10515070203120706050717071202070c09150602010e0a0602030601020f060a0e0c010e1c021801030f060f29010908070b09191a0913020d0c18052206 66
    0x54507000d041d0f0f000781d00c1d1001ca40502225801407100b0001c0d601c07500c509480c04000200b160117a010300d07000058003103000300044000c84220000151a0507c40c0d0f6075810444410f03048458000d80c0c030042c11840c3d4a03003d22080c0504800e0008019020465a116649081120340140722680010008220f42d1003030140540c01c1c904071081315100d0426445031400740c80e28081e0758805100b410305408a640c841d50203c1c06403c0d0151407005d41000c071a055034000c907c4400103a802241441c251081003a00c0e000c864002c50040340c0f0600c9580322454010251502d0410a0074814182244001e400140900360144503440300d80f80f042c230000c1e410041c3c0c0c14404540c084201401000b00c00510402c400300281030200c03084946011b980c2e24140c10280502c07507405900151516500300100600705038000306176000300103100d44020f402d501006000d0b44d220a42c45001036480e003101182407600900c0d5010060f10060656500e40d0820020510300c2444a205078024040c8621480c050403c41e40000 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 805288327 1250 805287077 805287079
    0x80112020a1701051603090c0e07092103080a09021f111f0c090b0a0f0306091109190b0702010c080f041d061e010c0c15020d090515030105150702 64
    0xb4880441200c1e0a900a0400700c1301054410300540c2d04115a521070700c40c1d941c1d8540c3c0104004800c40c1041941100c1740c00051800060000806001c5100a10b076110080c201007002000d41111070079180c010029140581224065070809e580c14005079566401c120103207184100700307031703c41100072400c0b1003120100101c150540105400304a200070341c4450003040048200d81448500090354003151030351024812034800c16001c0c003480c0c2002d031258100004203c11413401061941e1110700003402c8400d4a8608160a4030006030385c849810451058051400c0303002034a20054541030031524184a4400020304000280032500f040010035010340c0d00852407880f03013913112521030517448544412130a1038024a2010030004005182141d00040003207400c10555400210714401500c526000c44000c031030803224100040f440003142c0000d0782a9000c180d00800300c440d1126406818114a134010600404241d040d0001d482d401e48112030440c5d1081d29803407850036030440d011809018550002b = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 805289577 1250 805288327 805288349
    0x1060e01030b1003092006030c0c0a02061303060f1104050d0f0b090609151317070212010209040f020c0a020603060d0503130303270303140c010e0708150403080112020a 74
    0x1541d0389913810342c80b80d0401c42c464024134031000d541c1c0c1a410f06441108030300035071103c02040011211461080505111219042143d0030100e003540040d50300d40103007600791014a0030020800c180312007401011081d4092440c100705061505040091900c0f850055501a841d200e8425040107009080200426044050811035040608050b40c69a60568040d030103846114003061100a2035014240140310500d01c00307040c030300a60307215581940070311103080d0382c0380040c0078050143c0c4032484030021202d1392100040c1e80342409410403045420102b20380404a1060104840d482000164501002c1c0c044941684030307610705c00024941c4a040c1c0005142d8000402e02d4907846580e01003a90039603101e074035420318a00004c211190301603490004103000c01c503644410400700e4010142d0880d00b03a040c0d5400b5140201707074002d1b5820b454a401000049502030242000b081c0e805000e001003024031280141c005082a8500902e040c0041c0503502c03451944444040455854101c084020071b290004 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 805290827 1250 805289577 805289599
    0x904080c0c0306180d050f0322060e010609060626130c030305070b06012c1c0b10050102030307021b0301060e0a0506120c1e0303090307240206070801060e01030b 71
    0x44000b4134030700d402031030016109902c55000f205d0300440039554a4102d140c842400c60b612032040c098815200d50910204403000d01d0507002090f60b030f000703154036000550f00110f10765282c0703c00318045a032103034004ca04000c0500814180d12079150207400c41034085a0609031242c660000121046180c081c0050a04a481d0800410942c00001030a41c15010380440349096a035040196900c040720407a0ba0b03a00040d090100c050143c01401d4020706890261004411204a10024540603c001b0742980c0b151118010000380c204c0403400b9402500003880a5400d504110001969810011980c3d07022003400c48a4640340f51425030041000300054424505c480c10040262802803a09803030303150185084040140909400141c01c450410002d40092061403c1000c0312220545003c9400c1d854001040a0603080d5010016403000d007a07001042c2915a80307401084c030b8000da50350b0309142950001010400c42c0c0380c0151003141124200d0030a1200f440d80000120700520002c05400d5019020f040 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 805292077 1250 805290827 805290841
    0xc0c02300604060f0c0c020105070501111305130b060307111c03020901080a06060509041113031202100b010f05030c120114180408090409020324040606050f0904080c0c0306 76
    0x40c5540298011003003009412074210307100059032508600d0b00c01240d042034078031b40103501c100300400313000c1d0007580001200540140d1007501588540002e000c07071500305070244418500700301e8100c8000f80801c820841030342c0080204844e400010300312400c0c085204c0c02c4991040c0180005810060044e14030740c07821308128000fa000750802000f281c0061030310000903080c443e6030300c12082522001d40303816042c440e080781084040d011140b50340489000072320912142c8140c00703007554042c40c0710351403070358100daa50307000285080c851b16000c11459042c82c07400b015590f000107522089510b03a1600c5607407a9248800d0704020f00c1202c0c00d982400c1c01c0100005000030780e2840749030340680200c070411140d40c0503000101d11081c0036a00644181c400704548000b0b4a0683e2003001070b40c0c800b6040d5070030000302948011400014400c12a05166207100b01300c100704031b42c8920000b401c1e0407070785031600e60014800b05108020041c00208032110018a50000c49820491032550550080481d0b4003031034081 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 805293327 1250 805292077 805292083
    0x4050703031b0b01030602031909050c09220204020f09120f06060d03020601170c0907050409050a020f0d092f0307080712110a09111201090c0c0230 65
    0x210094000450440c2110707208503000c24100c0c049604030450310f07003a90035910b48100a500c050302c0c03d00300c2d214414000000c1611780c01002110380c0101c000d041945007083c1440795101340200041041141e40e40241600802c161442e5005601540c0041e1a00d66400b080850351084a141c1580b0042c600305041c40c41030300180e004003401030002507031582e8171203c0034860b003c2c0c01d4200007070240e0002c9005002000b042107099010324980d404950705180700b6008a110100f09a0723045001502c009024070250000e80181a0000100c040451418510030300c00d050340c0c056200301005070b685443c251800d00800014640c403010000c1e0591110b40e2498010f07481141e1081d51950084c0207003080002c1e00240400c4200480d1081000b808404440390354060386c082d0351016282e44034030280808220110a1f2203010841c0c41e403100112396881501e5200c0e42c400301d05034441e12140c0d042512043d62954041d110351496581600c2450040340f06a24600a180e501c00c2200e800c248803040e000130180c0c0c00 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 805294577 1250 805293327 805293329
    0x60902090a15052d0a271503080a0807030605030d03020d0f09170c030705060150122b080402010905130e06070e0301111e030915040507 60
    0xb00390342000c001d075a00280b1807510104225400011503c0c1000b018050200000c424000c1005010307646171521545200d203004071442d003490400540d440c054a80d10303420b1140c8214002c0c9504050071861a654603c040e92242d50412010442040c0214038880d029811602c0070704030080503902d0040003203100a0003908a140720050aa040810b00b0440000e5842155a00c035000784000307011a514004580180d48204100d00051000b0460340c8040341c400e0141c24080c0840118915110940241007544003100702013218049001c20070203041150416409408200508061800c0c02c3d69400080d40484c1d030402310042d00e0140f0410016560420900c0100100c1d50346d000e03041d040001c620449002c501100e000340405c0920100788100d10300311031000c0c1c02c48080c42c2d0200c0c0307240b241c143c81401c050080d900c0801150680410300c40ca0300d402e00400003654840000d060422180c413002c3c01c0ba86620824010002e0780c00000b04400e10418030440c00c04d640c903020341030520b08003403801c2644d900300303 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 805295827 1250 805294577 805294601
    0x92706010f0c1101080c0c0a030201140109050f0109050702010b04062907050a03200d110105090c0607150b030a0308060a0b04060f120b0a0b0c060c0c0d0c060902090a 73
    0x202003862482c0c0a0544000c116801500c0200ba5021036401035801d100082c0c0a40d2130844240007005c5078400c100080d840d054420350012800c002c0c2c0310440300e20b024060b000070820609000c1007040c006c00c0d40c80c2c2e807411641c1072031002c14682c82c4c2c100c099004041001c0e0494100c1e04240020030240084000605114140500d440c844001c4011420060140707100c01000d40c0c03c034840b0301020a10a600101941c40c081c202c20364007500011045142000c1e4400a802150249c4c3c50000059020300c1801e61280a49024002c0c0e1810100041c156100c0d01c580140b16110200c0c1744191210142e02940000f0300c0036088079488031441c10060666402121880e1203147c0011003ca0003044003c02d45080700c003d81c56244028506400036102119003510038200c40d991680484080c0da00d1009110040540c2c0c1a400e541c0c0c105a40100d0622000400201c1c5000c410800c12a004000203140c9104041528160740c0100803031070000d01510380140040c0d0700024450a1000c1d841c1d042d40944680e6131 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 805297077 1250 805295827 805295837
    0x108070501030c090909021c0506070305060105090a2108040609090e0a0804140f040f0e06160807050c030c07090e0c0409200d0b0c071403120c09270601 67
    0x195410044064501d00341c0310800040500b002000300030102d4121a01c443d100038441808e82110020b00452a00c510303009440da54071441c180300c9810f0705403013410340003482883c01c2494121103001056504400e44180f030700c411500d46040e0028031103248801ca00d00d42c4802e003140d4450b2f803034800070468083da00498405038580035a411035050700059000625602070001410f1034500603c411900d00c0300f500141c1c1040803500500703d10740e210710541c0110501d40c8800106040e05464207440c02d20002c0607400165010030300b0340d01c034640122080fa40240640743c003d6550f072580c0245815405040310702c1340e2503c61170f08041200082500611400c24101c0100c40e00480c40004100540d0600c90001d005041c4007448108002d101e0401da1402e284043c101c00c0000c04c05030749941c1401030440ba03000d03000b540440c40c201044a00260940c45d610180011801c0c2003d101418142e080c000e480c8034002200011824240d4541a694070f84d0b0714580702896050b0b0031040001c60444804948150002d2 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 805298327 1250 805297077 805297079
    0x1112011d0706080c04061b080c010603050303150402040503210417060f241201090b040c150c05060a02031302031c270e06030109150606120c0e0f1c0b010807 69
    0x84a140f003036174100c1c0c00030f40d51400b800d1070f115180911512040301c140c4000d00308121904d408070090150000651241d00155075920f07207481200661016846001d1080340100010049990000382524034112a003400301050010050781d082c151050382d000c0d500c103000e91300071904a0303080410a1880381c021600207005564516120203120315048103100d050410000c4d84900750b08108818040310f081c1140001041881620340c01414401110110340301c8290303107014440c040d851450f490307640e031442c00c00d030440c2c51040d5622902c4210050000d001c00e41c0c080001a10780041c442120059030b0003805803450400c03c0741c08411031001e080034030700108012000708404c1090404625010140302d10007540703040d08004203514050009000140e1564850b04040e002c10880e00d041018a1070218000a00600e06880900500c0000d01841c5030a4a0003d1500600750042c15207841c0c00ca04541e25041036401d0400594138115110641c08450719400c010700c1000171108496040c0c40603601140c902c2 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 805299577 1250 805298327 805298341
    0xc04050709060c030f120e061008010905070909080714010902030705090c0d050c09062109211b1903030e0307170a090302030d091d01031112011d070608 67
    0xc50700c81c02000035540f50700784010a100b40050420000d451414a00300b036641e1800c6002e039890000b10380e0302c42d0042c0e014407070220741e0500510300401d490300081c400c0b218981ca40c1901c45800d441120181c0e502c4000c110100f00346c02040310100c0d9401480c80e44d00d50a503c1080c4e008024698049010780300b0044085502d14080c001c89204403a40401240352002d05030b071800107003d0207040555080c1080c4115805603031100c01400300d0803111500d8020181c054000b000031088040c00312107298002d1150350000603241c001c0d05000c0b00f842602280d40300440f02d0302105801954281030803c0c050440110407080c0b4106003030032000e001360340074450140e503c0a01030300d921036107070020324090b10040d02007100443d94000d058400d03030350b052650300c0039500d801003800d1403105a01072000510b01c0c503040c04011810400d11000f00d41c00719480880d076055a42c2c1010041d040c2c01c90510074103a081071001201c400750050b4001c040ca40d28008082d200c3c101d0203c1d07440103940100404184100006005 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 805300827 1250 805299577 805299587
    0x210c15030606120e0607030c0318081201210305180306040b01050406052d1801060302031905040f110a09151502030c1902060403020306041202120403020306010b0310030b0403020c040507 82
    0x1c42e00710134040c0510b9219202c05030000c01c000c1180d6028152a028100c40d442c0701c11039402c504500400466959162610702c1c03840785601604421240c40742a055508015070440002480c00d515080c00c643d544110800b4a40c0c5003101c42c04076501d481340d0420001005803a8040c0d038100c41c0199400d104040d142d03404c010f00381003049550f14054080000c40700301c405801d160300c06004000303440160035040041103500e01c0c8109800001c0420b400106004980031500842c2e454113000c04401c10003800c140da11805a9040a20081e05544034880c500d000c50751001c4141e00189080c1804001c201440c0e8901e0039100218070880b080c41902490a0b01101d0000c41150080c090304c5000d0021103082c070f030361000fa40c00c00c2c160503600458240004001601c0401145014501401d40c1403448014000002d14001c594034001454038014402000141c4002030101c5c156080c07282d0b07940e120b0761443c0c0d00406100b19540098003000d4000700b031000341900400c6e180c1048009460602c0150b8540c40155a = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 805302077 1250 805300827 805300841
    0x80a02060904020f0c0303040b090d0305040317150409150e030f04090c05091302031803090a030b060d02060f03041703010f0b0703020f0f1b0406210c1503060612 71
    0x5003015040003035020030300d0158018074100210b0050542400000c3c0c9000340340d5003040b203080711001401401d00805480400280740f01c01c060349814007443c80c0c2950300801c0302450340005c240000c0710002007104060340c3c20034403031408000f40003080100070b039040040918070804a0150001d1501c0e1807040c0600b80031084480d05030801e40c01070b1406140c5100d0b88001c05202c19404d08010060110613102c0c0d440020826030042c0c0c0b110301603181d0418262011400c03d82d19241d003081da0040050f01c2c007684410b07030218116500050540400e5440708041040d4480c408030080d4440000600d00c2840c0c16040c0155025501407a00d034003890b01d4900009516100038010344031400354aa0041042ca00301c0030050910030b00c43e10640e4220094101a1403400745d26100d0341c4840c1c1c01c80440074801c00e80354010845040c0080b242030114625180380e030000c9074012010305218010340c03410a401e00001d10001c000601080c68500b50441004030014014030722401000001030040e00e61109500c11801007070 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 805303327 1250 805302077 805302079
    0x90c0c060e0a0b0a0e07060507060f02161b23011b0b0f0a06050d06020307201f140a0c1707090f14090f1902070f0b06011b0f030c060e010603020307080a02 68
    0x445904044007508c164014410445440792146002c01e2401003030b00140c03a00d09c0c0a0410404811128605140c0030926080d0b4001c140d10b010b0380030490340c2211078141881c1d104041c079040d84000300d0001241d00e150020030352400e003d0300c0d146110400000d40e0495100303065444002c480c07920740820b00700c00d035144c0303124080d40400e140500e84041a801d0f03008682003041800d01d0072207032540c03034131503503d0a111420000c043c0d0000c800440030105044844907070341c42c1c3c0440422055030b026142e8240d040000d80803d6a4a98420388111102e006940f040c00f00480360710460040d01d030003140103090385118082c0c440c2a407142c030800200000604001806080001c0422007240e56200641003d2400101040c1c0061103c5682098220031480104125401101e09018444d01c504101803d610081c02c26410000300b06980c20034042614000500285d0001c94184400594181111070f03280b654000b078011440e10050802c13070321055003d00c080301e20940c19581d00d00d5440c8055500ca2070000d01c06 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 805304577 1250 805303327 805303333
    0xe070b04180e064003030f3909081902011e050d0b04150806040b010609030507060e03150109051005062b1515030e0d09090c0c060e0a0b0a0e 62
    0xc10b244a41e002800c410580301a0ba0584038a1500c8001801c0030644c0c000070b5010940d112202c1c6031403020390003075044501010a010785402100152800800c0700b01d206040c000031018006035105104c0c0201400400050007110030018002c00c1840c41c64070701c08803c0340480c11310070301400b1440130702118480011107600c41ea0704201199110b000a00303c242103007540560303104001e0070f948041c600104050030601000708041d1416140c00320341c0307560680100d4180008038008000159001130032005a903c80c1c50140d008003845c0d030200e460081c80d01d80245007900306000110300201c065001d54401c051001e1007001455460040c450b151045503400360554003040d0000e280395400d08a00c40c00805040030020721521800b003200c114100e02d8004041c0364004411001c0042d5050094424906040c0050440c1411400d0090501c130700a04c07034102002e0300c0d01c191000842c002c43c0d03286261604581c0a010001c26485800c0c1c07602c070642011140c40705000c000c0b82c545007440c403c59504003090310007 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 805305827 1250 805304577 805304611
    0x10b03040605040606052206050307031212180807060c0815041806050406021210140d020105070c240c0b010314070b0d0f0b04090c090e070b04180e06 66
    0x18034014000040050b1441501d41c3c800103a6601e0702040c41c4160b008441c2101d001c01c901401f402d00761905540064401c2c0e1120b4024804206a5003001a9140603400c01007101c08103001d40788054000411100a502c50035000c01c01448011001850820702c9004200240c9440304010707900e40c0426a0b1051105091452140742030a280e48110f00304044020141c200071010350307400064420440b0100c0f0043d40100303a21000e9074000c000c0c917030400740301c0056060007030030110300d40c404400d40200345100d040303a42c0d041c00c19640504215814103410221500840d41c4800f0305840300816000c80c03d2a40c001104003041842c13080c60710322810f96114802c0b19081c0d2a580300e90820056201007102d03540241c0f04c002030312654400050814240508001c84c2c201c4c0c420404808a40c0c0315140e10780034500f40900340c2c000070350304018031081c2d5000c6840024a03254100f200c61808825801c40740503c0b00000e40070486440400b503001c8188072501052201016a804094a400c000c0c1e45802443c1c3c80400 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 805307077 1250 805305827 805305833
    0x1020102270d0203010e010218010519080a0b0607030c030806121209041b0306140d1101320405040b040e030307050c162c0702030720030109031d0306010b0304 70
    0x40c1c40c4100003421090804a1500020300716240414020516035001803104416a00d4018070b6070100700c242051070038680d40c040c4081040d000c00c2415410050840002040d0700c101d54090803100902400e803e80f10919803038050171001355071105030301260103500011480d16125101040902d070b02400b403c5080a03c000c1e200c041d03005001644d0b4020303100d0b400f401c04924030010180790310500e07a41c00f01d01c0a18108402819500c40500d241c050310030401c2c0100400c0b40303c2c080031715041e002e01c0c003951a0040b04285400345039052001e103a0061118402c00719404400001c2c10503a14204ca0802141c0c4c0e013902000202c5001c40d00c0e42800b03400600018000c1c50241015024030481001a47d0908914007903034240101c0c82d4020a88080e02c0510b00e8034100ca0550180c000744c00050844446400c14100103941c80c00f0b1428000c040701c03016219644600c84010f104900100040d00a00500c1c01500d030103031441d28600320360342c68095410400c82c080d1031300080300e9040300c41d00800e0a20b10b8035192 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 805308327 1250 805307077 805307137
    0x3130e090a0f020414040f0b0924060a03050708210705060f0406020d0f0501030b0a1a06070302010e010e0d110303060a03081812060603150105101107090218090601020102 75
    0x810180da103e45d0f1500c1008103125200c1046118501c0b81c072068000036902d107049500300002905000c101e62109050f648811051413030f0688940103558080c0c0b5596030300c400100d04c3c04107508000d00b140100d400c00280b4407000901450300f0000c01e500c0483c0030803044020b400034042d0400140555015001094507c030814002c1a00300307002d00005803a0400644049050710040d15084040e10740d038600420074008100251508042e00c120305100407042c40d020240360810a40005104090000720242094002d601040569584900034418109442e4400d51103202419560f0049a860003501540369000320841e0f21a600082480c40a80d080d52101071154009460704440046144040c0c42666202c80d807000c5040d00d170304001c03c401d1810109050a000c03100d071240d84030542c0403005211a075620a0016820006441d0005d604080400c02c1c0c2e1810b2090f62044164501c00600d8096519010702003060030b50003038518807c5034035101c0c0124204d11a41c00114001a02180c45000d100600 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 805309577 1250 805308327 805308353
    0x304120e0d0501090f1118160309231912050a030207140703030311070803041101020c191a04181a03030423030f06151c0503130e090a 59
    0x1804403103107081070b41c0d202c42c21500200c105803404081485180c00f0001c2889285c1e001d44400d980c0701c417001c2060709480c000590050082c01ca00e02d03103808880b00041c82030303002080403508075010925101c259040d0078012004181413444502540c0e80d079146040005003100700044d800192031400010001b0129902e421501000c0708060302000417001048041aa00644078107480c09001254076510780a012142e051200c2d01d043d0900b0300119010440d40b40079650b04c05d4020380c2c41c1ca50309080200403800d1111035200c50341e00c45010b00301c0310118079024182030140c41404200c407242149440d0721252a0140b8031801d1018281d602d4410300d882025040300c81c0d5451400070241c3c0500725400081c2c195041504140d071700301004001c0c0c0a01c88070003094001410b81c15005424100342c850044c0b03844903c0103051040300e895400f0724114a40703031f62001e070b070b0040c02031344034680702503603601d001da80b40d81c0000c4014032000400e800105820030443d06060086142000401c0200002d6448008081403 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 805310827 1250 805309577 805309579
    0x8040f0515030a05280b1003061d10170307050c01080121051005010909050c150703140708030c03040b06030616030c02070509010303091a040b03060f120a0605010602070b0304120e 79
    0x500710a000d41141160303d26080c90305d07203100403c1c481007a4050181320603001d4884401c25043ca24200070300c0802c2280d0741c0f21580e8070081e690940d5940c0d00200d010180d00e03031103e2088503400200c192843e0000c0054510f1178400c8041d03a00709088880110f035082c01c00c1c021441001c0c041d07505030b0441120700c051030038914481c0096900340c0c0c07443d0703625000f240c0e0244c2c0130780d02d000c3e2030301d1600c2c00b00a41441201c4060904a400d842040e0092072413034500c3c001c0110060500107800400c9038404040740076501010340c010807003903491400c0c00041c072142d00309403002c881c10100c18012070060f10340491050320407170401b641c42c607020501100490207012a120400d0075402030b6840801c01e5181e0040090185010361a2940b007540f030b140759405080114065600002c0d410301040c40b002c10380c8070440e508107004030761403d0315000000c00905003a421140450040c41491600070407c1490b402c428121503003502034132511540c880d40d5118034441150002c10075240c428007100c0c0c60b40601382c28605210 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 805312077 1250 805310827 805310851
    0x1504020f0d0b06151207032c0703020a0801290409140d081b0405040c0306080105070c0b010503010b010509060310080f030c2802100203130308040f0515030a05 70
    0x100c0080031407940d03080084103407210280c072020000706090400b110401d082e1801421454440b4124034040c00038405017240e000c064a403a41e40c1e903545400c105a4112400031500900c201c4080c0108070b6a0b02400d10003280101550a07001070400018484d01c95000078400d10070680c5205124001e844114207030704694426a00e4400d1004912600c81a64090000c5001000342e2801d151020f002158028201c061860381d0680404904500780d00362011a8000d40d400305e02c0c0c0f02c450714145c01410540e0000040c075032820701003000d441d52282d404842240210b1003143d460341c03a402894261007080c0d48140c00f04004100d0074119090050086501505444e080030322143c9582d00c1e10b040403120804100031303520102d21000500010301151b58004298913075182021003803d200d8804000ea0700d4003a100354101405424040d000307200b115804804070500801301c54580ca46050300b81c009008d035100e80c10040b5000300c4c01781803801c42c92005042803651607003155140c1c20080d001e00320007003810031202 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 805313327 1250 805312077 805312099
    0x3190c09020d0209040f0e150601140f090103060b16080711060a180e1005010809210d060e011a030c0705031314030a0305030a0c020c102f150402 64
    0x14000e10240026032607800b40941c2e00c039803890030403007690f04259a070354215141c008074210083e0001910041021421405141a50781d02c4c01a1200d403d0651a103200c0b40d4002401005001d00e031008200e0154240c80400500d034650100c2d03013081c000c42006613854010a0032440100300b440000c0d04d42a171207981b0b005004c80072800841c0c43c0760030124416010030303034481004c1c8445417206040c1000c0c040c609054446480c181c1035441c48034035a4401c46041c40011004296583d105020241009040e01c0c0c00314819050341c4400300c41c0394082c0c100d034040546450400301d50b1307108142c44107040340d40305600d221a804880c849190280c0c0041e2013041d04003010042080003a40c14400b4010407944040400c03001d92800401e02140c4e403555071824480d800c2040a940029041001e480e0404d001c0d010000e80300c00c441009134030b000306c000342c029400341514042e15400c5900880404020410318600491035024100184500042e00403035a0a40c00146031007000300f00340246280c0c0700340002d082003581 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 805314577 1250 805313327 805313339
    0xc0111120a03060320090412050d0c02030a02160e04080c1005010311211b180a051602071401141b0604050c0d0b010306180203160f05010e03190c 64
    0x81c0d4000180d0a010a03100d0008000b800106240304011a0707805100d0816950810000303660164003e00040c09070720311907008030691b031040040e120300101582c0100540c2d2074211010b9601e401c403059a034010b20075140128501c10043c6194800c44005414000d15600d855644001035003124008160300d00c02d051100c0c0740c081e0381e0700805000314040c14111a0603060001400b0403510300314549041d0b14005600b07408085400074860807900c0c0040700d00155002c0da0320000c0c00c4518040f00d42c00441c4070040030312810100c60740c0b0443c0110070203c0103d41242c0382b0380b020b85e00c1e24800d110b020708401443c10359042c15405204030190b0360f0f20b44568180f030002c5103190258080c504240503003242e440081040f04100701082144003443c0d04890741d0790010859541d03102c0082d0f05010041c074164480b4600c0d612840300884100c03441d03600405540c000b0842c0342d19180352010324072a484100d0944031001425502880ca019000f84015001e040b003484020b0440320f050405c0c07002107a11641a003000544 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 805315827 1250 805314577 805314613
    0x1506060c0f060a0f0b04090b130c1814010603200703120204031410152603030405100c0804021e12030a030f06050901151101180624080c0111 62
    0x810400d00c040011385003982002e00044840e00e58416010b1807802e04003c002ca000356810650217040c0204031800014245441c1d6240c021035444030307130466250045c2140039111908210502d0b10b1510602040d6a43da44d0201c055a4100054662820f000102c20129802c9031005008103800307810408201e2003248140d5089074016802508c804000c0c04044c810a44207005511420034051410b0000c2a10071041259410302840f6210301c021040208450701e5406407441c1c0f0f0403a001000303980d205c3c81c00741041512a4001c81140900600d4624100203260048907410b002e25009000468281e010700b100844451644c802310713034840303e0541ca10106030341c10070080c0a04c020554022030080307070038024402510b5190700520312550b80500103210910700c04281c00c0003000070341341c220b684880b03c06849005005c204520320341e401942d4868070502105800c002d07249070950702001030100498000c228004014050703244541c1080c550b80d042513201e10b4213842d03001c0321b400035034044170a210f420b010 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 805317077 1250 805315827 805315831
    0x6030b010b0306030105180c19120b0108070605041d041e03050d0c091a1e030112030e121c0908011a01020c010f020c06071103060405010f0e1506060c0f06 68
    0x1c0311000c00010400181001e0248540049440d41c054402d0381c800e1114a23104c90130061064003c1804032034a542502405041200610214804180104550a1144103c0c209002d50ba102d80701d05c0d10300082241c400d001702c030200d502c2c84401040c0380d20280d00e2200500400f410664a884a805180c0000d100300303052260050704c00d407a41940d0300d81c900d2510094850101980042c17043c010380402c208100426104001d8600c17a0741d8030356494241064134130344041e804107040ea1407008400442c200e00000043c04845000e0389a4996256076482001360f0200a020040915000b142c8243c050700000c490780207010f10303141440c40b480c0c0c1d1680b052a007164000c041e01c0500182c906811403195805120942280c0e00038078000d8410800f680c0c001e551001e0140348a8011880000c00400707110a601103a00c1a282c0141074072120b05041c10921b01030141020000c141c1c500d403504044169400140d010320024000a200140756180002c100440e000b030114242d0900580b0a201c1c020340060002034 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 805318327 1250 805317077 805317089
    0xb041d010c081006020a020d1a0a06031709060d05070201020910200d080106210606020336120a060501080f1204061707090b0d0b010e0406060f1206030b01 68
    0x2401d030034600300207144510150a10041000d4120203202803a8041103a840c000e4040d2007280c1007000c90710b414101980b20503100016040540140054030340c050304045e00710390003980300c02d030784045480a4820034450a18101d500080400698006500d039420895114000380001404c1016805c04600c10160300380b17500b00012000302c00b070308881c00c03101d805107149003010300100310400c0d201102401d240c0d41030003003805124880c070405d00340c40700c1880380c1113240300b1a25043c00083e5032007201950760707000400001c54045c03004824902c0400c608540d4200542d01c50b0020302e0800016090125010074030621441078080d105499010400070b00030b00f4003c2c000380c4010050204460480340c1401504041c80c90180c07030411040008560001c02001d071440c00c0540c04d4402d8071269016a500300d06640018445200424061004840ca41c003201e09841e0a072294404031460b4010030084a80e240a00c10218080204a03003003944a02d000c2a044109a1400616640c40740c0b1044442e0409074421 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 805319577 1250 805318327 805318331
    0x102010605151e092209020a060309050c0301052202060403060e0309100201020c0604021c170a0e040e07030f0804030b04060914030310030308070c06060b09040b030a150b041d01 78
    0x1c26800710038081180d41000745201d12030401e4008000245410790a10b04804000c1d40803208401c10080769021006c0c0c95030050030710079803650b01e04025000d888003e005456501440304454024101070040c00c0c8562041ca030000c140302110320716861028090202642c00000510000c800a0009c1c0300c5e07168502115802951100400e604100200d01c442209608690040c440d21081120000d070b150f40040d41183d0340740303030216058114491107600c600068001702c07a07403107007140c018003400080c03810308007540e22105810450400c2c4819075819414115095101e2601040420f500c490502c00d290300c15002c4615040d43d81c1c440c010480b1064406484540da035032800b000b0440d191042c000d894181c04d010718154a04044c200000c41001d10010f014412940009840d942c40341259059441d8024000c001e999110100558907030800c01c05580201d2900c50b41d40c0061500040350301c249640240590480c10703d2034402c002403c0c18803e000c1e08140c644241469401e0309820402050f506a400 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 805320827 1250 805319577 805319587
    0x2070504020a050f0c0f070f06080f19091a070f0c1101050412080c0709050105060a0c05120d0e0601080a0b01121a0c07150507021207050717061b0405060d0b010201060515 75
    0x406c0d0400c050783d4022400108503040400010381c001081d1035100a1440c00750015960742100d00080c4180040148a550300e4100c52a0401081600048118560554940495450f4141603620468005811020440d2030f061a0009600941000d082d0141894014100340d07580c2a94005406400d0080700d000c04003160500c0c1310388080048034008c2c0090001804503516203c082070061240d00c4402c82082221056402800001c0006409005003006065944d21449040707800501c0d01000401050040c3d80c0001a205030001d4460102900000900380c60392031700103000c080c1d504040088030100800e40761400010080300c0ca451040703611210b503990f10f004918004190051030861030301c245141000b405840f13980090380d00f800105034021142c0e1070000b824000d1414403194000303180c105540341856096040070902c14040c600e5450b4100e03880781614440314160040c4d0003400d4000740144400082c03220350b50000145010180000a00c242d00d850100c2c51710100c4c0982d01001e2600094 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 805322077 1250 805320827 805320853
    0x302060a08190c0c06020306031501082a0a050d1104050a050702010e1204180b04060303090302010f08070c0f0f1227140603060303040e0103030c0311010c02070504020a050f0c 77
    0x30b481001d500903072000c2203401e026203400b904002d00d400c07018060705d5001c00060b2060f10208681140c89d000c50900403003d60b510540166200a0000c640c41c40840010110314043c1a10481d400201c40040410805030706000c14800c401050311001d80c0c460748102c58a0003140c50f1441640c0c01101502400b05080c034041381d020b4250340d03210103820220750010501d8500103610320190340a441000880314520022688940054182c0c3c00d00f80e81c0c4245800e0f0000f04143c4c11108042c1164800c1e29100041c801d01c09096030b54a10031200b4201182068604030001801c111182d0181c51159490480ca0b0382103444e206500c090919211020911000f0724006c05000318294181c012041035590548034100302151080c2e19900c00c0f2240035441c04008145969014030599000c1d0800c01ca00e06055a9281002031680180042c25130100740b105088027406003060150200701c0f00d980d0000c0c5002e030b1a210503c0025030103000c8440c20090148040400641f9500003001d155030710f0401071408651240c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 805323327 1250 805322077 805322101
    0xc0b0a0810080a0f081602030f032104050d0c0828090504020f04120309080a0305030a2711032a03060702010605100f1403130b061c02060c070302060a08 67
    0x3421400c2c242e40300c0c001802c0069210380d07180350240c1e8001d00c8140c0703640c0003051401c075800c2c00d1200203505010781d00741421074840c00009810a098400424008a145210192418041590060300f80d4011480c51b541041c01240500313a49441919203501c0e144524a074800c190a56a11341c800500b12a5201d07010503901c07451040191a0482d021803820701c1d0f07109501001e128900c542240110303800103280038107006030000c2c80202040030643c1c00c2130340c03075280060140e03100311400e40b540b514005034000a00bc0c4005860802c201a528022661801e62500c0224490044040e540341c49070a40305c0407203c110084481500c650341c4c4c0c040b07480031030903401c060804600400113021685040350401c2030750ba80e180610b5000400c1d06120341403e0b5001e4040b52008880d0686440c00e80300002801250360500c0001510720303008050305640d035210b91041000c682c41100d1400d1100760f0421441d005840d014000b805503500000494200d00c1e502d502103445900205490400300300e0850402410310100 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 805324577 1250 805323327 805323329
    0x4020a091404300e0d0b0405060708130b0103030e0f1e2707050a090b1801031a0108011e090f050f1305100906180602090f01020619090c0b0a0810 64
    0x30000101c40d005102c43c502800c1c000c0d0311a0700304840300c000501c5940341e08180840d000c2c0c01c0076580b0318034500385c141103a8a010035951900040d68440000d40d404c09044da50141495128003403000b56465074404035603440c85d940310f0f141c1c000c4110000c0c40450b542c2c0403111010340a4034640c100407680c41d8040080038040a410815040c2c14103100c6c00d068040d041d0107540c003040e103003401c548904240e102250184200e1700107100d903400001d000028005e10303066401e20f408091f42c05018280309a83c3c4e03400c0d030a000130100f0f40403c054800601515040015140710041c0c0d006408140f160794066003400c0c1d5410740303248226070350349009008038030b010f03a00d559074810205440c1c082035804d0341d511030b07580707400a96000c403841c0d9441030303c0410444c16400c48450310807407610140641ca09410450001e6000740b901c80e01c1b81500301c11258655002082c210312503000744400c0c5110040040860010b03120b207803002c8a0072030300000081032801543d4082c040c01c04031587c0d0440549003e401541443e425 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 805325827 1250 805324577 805324613
    0x90a0801051608250c060c08040b07180510030f02070f14070f030b13050f0d03050a110702041107080f07050105071103180a05030a05011407030903021504020a091404 73
    0x11003080002030310b001e8600031540f0307032107086805184040f4541185d42e400c980100805040c00d0034050051280d02c55660b600442c080c2201610035101c0038415220a034584007002c0c0c4600c0ca446042110741b40009024030b50041c00c2c10042003143c0b075148403004990080d80c04540d0820003443c4401402103250601040400703000041442c01c1c24202c4850744619103110080084c21400002049060b4054505003950b40c448120b450141c54060b00903103070a90003003d1030000e450100007507130049003401070520540060700c0d01407070264a40c0070701000d007444080f0510842003c00c040030004000340010104802880c1d5025120406803030202d00750b800c00342034107003080011840c40329110004000c0b24050310405040b004161f081c030780031078141c44243d88a5070340b40c0100b502405c24440e040d0401010044007070540403013652440403e40c00c55a000c4405401039010050b42021003264410f420381007030000b0549164541d54008000640d0001404540d100a420043c001001011000840d202c12 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 805327077 1250 805325827 805325837
    0xe030c1908030a0c0c0206071a0601030506010f0c0c0806010b030403030c1404060c06060b0a020a05060f010b030403112119092306120a0e06070807120c05090a08010516 74
    0x42911281e90a01000c2c2c10040c1e4079035140258005140101d401030105940900040c5d2540210b09155030903a00c1441030300c1612501600150056100340700305c52140700305848100980380141411140144401c6080b144c41c80011800315500c20104500380c0244030020483d50b132440c0038a001000d6a8101c000182407142c2940c840c8010314440069405540700c2e4682030322000b0303a40c1000400b03800300d85e01080c10b0080010340ca0f01803503408903c03100a140144c0c220754480d19069522000c0762000d12070400055010b10111300001e1145007600c140346580c0e012a44035a0080b150281318413000e1100d580c0e43d843c00169035020504940305070400242d01d04100d4446403524442400000c88030948101c2003800c41d5400b1140e940b1001541c8030b4484801551100d4035107000031a00801240c200000184945000524414864940e06206911594805010154094140014041b0181410309100092040d616251200701c2c001d001084244004a0a8100505008101d801030001902005 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 805328327 1250 805327077 805327123
    0x20d0b040b180d0801230a0902092106060132041d160e040908040e0402030c060a050a120912020114161e0207050607080309070b0313021908010e030c 66
    0xf503001034072a41121b030090502460f008152040303000b01d5084e0700700181c0c4040803035400302d851900c5602400700c84005072a03141c001c601e21810349442c0035440200409651012000800d6544602140c030650440d892a401c1c110f034209112600d262020290315120f2030003c2000c0001290030442007168462204461400341000d4511114010f030345d00c8840306111604690b101e254441e640941c40468000360181d403201d46402c3e81d0728041c10306480c141c1c424841d5583d01299490803504840717010070161103192401c1c1e02c12000303485113a4104001c0e01ca0f1503440400501103100311090091001e405d0f4000280d00f44240452410b880003e800049501c4400602d0001030f500410401da40c5a921411448901084481240703040b0041e0002c41d008480854540304100610b40a18082c8401409560545840d103124070080e000440e44803803a081d03800d468a015003031440c4500100036180110211050f00c41801a00303403640e0f01c980f0100c9600014440402d804140034051034813031007026241d040 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 805329577 1250 805328327 805328353
    0x50d032d0813080c030a08090106080c0d06090c1802090406060f05040317040f030f0c051804260a02030a03110a140d0902130203090d0816030207020d0b040b18 70
    0x20400041c1504503082d080d49941c814031091401340c0b40e4548254040b40da490881c98002043c014095030302449960a103003000c0b81190700800c2400100d1070140c110101220180c490001401d84a8010345800000000102c0d80c0710000c424010136001400b00582d0300c0d0030500038041200c0c05c540c070200c10041070140d04a801d550250454040342d80000c982408203e80001c3c0c1c80f55449542d0144034503100800c000020402d4084410626500400c10341101c1c1d6910f00c01e02002d0806039401c2c100d00b0549200103400910030500c11004010a00a01242021001b8038100d07154800c642542c00350f840801c10b40740d0340d54940181354505401110143c1041000c18014120b0203050402e224201400304600c4d40b540c8243d408030703040c0340c0c0040910342c82a0801d0910320003136000750781702103681c01801c04201442d402400c16500400c04101854070024125200f20300940200c9800c0703078801c0740346400c1004245c0c20b02500d4092405030300111a1070070100c031004c008080c9510148503e8000c02040011 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 805330827 1250 805329577 805329587
    0x902091509060406060210020730021b0303030c071103120306120a0f060216150219020f07051005040f08100b0306090705150721121119030204050d032d 67
    0x2c47c55050070250b111040d502d48a00c3c40c0c102503030003200144c401500341c2c20344190306901c00b612090903001d481c00c07040b491445c1d03c5a0440720003c03036010392040020400c1560428000d02c40507001e01c081c01c00c00d41c070010009040200030704508241d201c0220500101d40b81540c62101034942000050004811903505c0e4501c5542501010b00642e50208043c08171085c20010411203640c41481c0001400344500c040f4001d4000140d0a9802d00c15500d0740d5000500000300b600300c000c0604d00030303d440c2d46000204018031511038005001c0060a00001a00f19011760002d03006c3d0094074081c01481c00d03070110322402c40d8124141e0030700c00c2d0b0103142800490000460100309584040d99002c5000305a44a243c600d4825403100509103920510b04801480904540c3d18540a0541c0d40000001d108400801035851210544425000c100007480169812740300724120400035003009424a981c030400906100b0407244143e000c680d01c40f0304c04e403c45d0361405e0040c145031150b92001f00c0f988405000204 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 805332077 1250 805330827 805330843
    0x602160905040f12020d021515040509190f02040e0d23120c12010524030a0e030427021204080d0905010203100e010b0a0f1209020915090604060602 65
    0xa5110341e90000714081c03010152002150507004540c0044d98540800001d58404401b41b066005001786401e500620724040c070801d0181500401030305072410040100001400003030200c083c035204200142101d40d1400b20b17800f2859003c1c3d9101100c140c881c3c0148810344101c2c18803402d0700c0d000420300c0c06426401007410354520b040c04c01d5210f0045030094101c4c0c0e2500c600400002040414010005d01400910052070700c400d91b48900c40310340c2d80c1d62090240c1c03032083c50014242c0545082c01c400c440c0d1075100c050b40c1d010340200c10205540508092060950340310f60803804042168000803034011917036941425141000c02c0d401c514011403400820240310004d03000400d0362000040500c6441c0c20ba80150b80e9254008000b1540e03410302035104000c10915101d0450455031590000070040f020798180c0720700c1d1307000381c4484c0002000e951040740c460120030080304a10b5947d109420250301c504020502c038102030b0b1850100c00703a0301000c000c92404000c0450340304a0070a20140a06540410854 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 805333327 1250 805332077 805332089
    0x405150a170703081803030d1b1e05160f0b01030c0608042609040f06091107020f010c140346140f03040605010e0f010f1e0b0c16060216 60
    0x9502ea10141411712103800049070301750b80c540b10214441c1d900d54802e0348962031884130f2007001e141c0c0c410301850550b5942103081c0e1041000d085d5823106001f86002e000104042c00c1a4459250740e81740c01d42d2140c10320301e45444142c81004854005200f0041001c801002400007070400c40282d203005d56a0404100d684901040c04126050010484460040c00d44201810080050058583d051a400c0050240740300381d25019060600088a48402ca41105c0c40d413900900a1040500000f00645800302604422981d1208011b20140780e140144050101c100c01110344c02580b2109041c00f200100240f060000c0203017164040040c0103491030380c982c11184aa080940080b1000080b542c10343c003902d00e4a07481140d000042100308541548410f060711304268000c8016120207034203040c0810240943c107411007106900740400244484c1e4195403440180010f90126142d505042903031300300240b29280d55100403070149928041c2d0704090080c10992000b41000044002c00304904541c6100d40 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 805334577 1250 805333327 805333343
    0x10081e181c030c021605130b03010507020f01062108030408070f030c0c0f0605340b0105032e050606070c1d062b05010b1009060315030c05010e0f0405150a170703 71
    0x2007c0109401c4d0010f808240e0014000c2009161114010f5242e00a080c84280d02e5443c24001144a00020710359082514420040d10f8a014444d6114841c65001920640701c0e8401881414006040c0003520368100e41303ea038541d0009041841c040900b20b03200c1d0418002056980424003074170b82c1c000256542c09210440f4022030040c680d040d500c00302d4158001c400340b103110040d900d041c04101c01019040790026400c4865030380e52440448030700342d4903580742c1000b464401d80c040407148068200ca40c0010000704050b2504010784da40c462030a043c0c1d806140e01d15500540b4080c06a4140b407a103600000546081c200c500480e0303034080b1a9079126503290188500d0703085140501c4070941c4220021039020381102240001d06002501c140f00500c40e410019042c00f02d441b50942425190100f1203500c48050880c2c1428403006492400d00e0082054120300c0d03000c10701500d942c0d04c0c020719000d0305064083c1c0c802a4802e030203015403014190409504d0910117000ea00f000c9100090603012260844c0384 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 805335827 1250 805334577 805334599
    0xf091504030b1e1f0b0f0703110d17070e0a092a090524070602030603061f030305030606070b0c190e0a030b090a05010501090b10081e181c030c021605 66
    0x1005903404c2a0f40000c1d43d1010003058100f41c140422000307015086c029110a080742d04916802e5a4400000c10481c0020341820740034003a401542c030382590881d801c3d081c80c55803c202000451504150790348044101c40d00d900000207005a10101400e030364501c008101a42a1080c0d80070740302c000540b0589018914000f40042c0001c1000450386410b07000038081e07542e880351414200082e4100781e52091007409208003040f00d4000140381003501c3d04040c03200484071817a5403810b80c0c0302d40000b00040d4002c4020402400010591000240304000c05626aa11005c044038400c0128151003980c2007030041d2011a904290380e020483c078103ca900c81443c051942d1410300f02c07418482c06610041480d8280303000401e21030001e800c4515040000d90b4041501c000d2140111203090b0f085e80c08180c079003000d6074503504402c0038280c0c56a0003102c4503d404000d116055596241030458001078200c003030015003024503540c0c18007403104d2244082c802080c041444010b201201c81c2103206403480351000242d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 805337077 1250 805335827 805335871
    0x5071b1104060815150d150c050702060d1a06040513090201020111040906140108040b0a200711040e01060f15090e040506040201020d020f070501050f091504030b1e 72
    0x10034409000040103071400302200320920b030003c107000e480d00d03c40c40000c2d170040e6005061104803101e00d0b039000712040350304940420700300d802403ca00c1580c0d03041020070020300000d619107100810f0400c240e90000280102c078810034440700d0348450380076849110100020822503031102130000c404049c000c1c0000b04d101c240e20041c1c9c0102620300c0c01c4e46c40c0007004200090110507581c0420200d510030303c034440014140100450300820304950041c00341c803d440105500800390b80c0030419401c2c51100d4110501d0001100712220b8120f003030304541c103138040030100d1250304150141140c05c003182d20081c0017941c02d100b020040c50515009400b80e501d1406003003504a07100346411001071000003103c0c2400d003082c0c1000303922100e0440d0180c0c094440c8640c03d409551000481c500d1100200026051081c03d1200440f8154441500040300040500c500c1100d0780e545103201840b0810b1800041ea81c918514058007040801030125020060308030b4125642c1040e06541c07a48010030360008403643e40020 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 805338327 1250 805337077 805337081
    0x70b09011401170d0201020f04140f0310020915070302071e0e1503010c0215010b0d0e010e06010f0b0301030f03030b0d060501091a091323160905071b1104 68
    0x8111040c0000041d00002414a20343c8480800003400409840c008000c6800c20390907481109007616811340200400c00c419034044407107a0280742c0080c103540c0711540d000d000a2609400c1450000c801d6800070303006404d854401a9045d43d075920b110902d0420a00d40c4000c1d44070400780c801e21442007031001c8406011114103c4020207801c0d201154002d909040d00205905110340401c0d80c081d41c03800c03003203280d0140006202501c1c0c2c800041241003607070a0580801041c0c0100e40540007554407041c0340803a40d0401c0c005d010101c0d14110007030407190701d4a0324403020a03010340c1c04010342d41c20400060011804030300c600e040d02501800d0114101a50802103400d10401c1000a002c42c3e2030f2200104d0103a2468114540f87c2c49051050034080114004102e009841641d0321803034855910384070000130f041040e00d10301281121040524045400c1c555904028208146000c48181203805003e02c448078480d468011380180b500c0d0014003030501c0d80030741d50140200090034030030030341030540c641ea0b50300c1d = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 805339577 1250 805338327 805338341
    0x170c0c0a050a03020a020f041404150e0f012f040911070f0c090b040b030c0d1a040b04030f1106043504050f0102060c030a021303080309030d05010f0605070b0901 71
    0xc8021070380ba5001a05009456980c00c0c0401c0f803003920b00c0408000c01c0e160074011245d902d80300c04014031032a1190340e91480401c001e2000025050348620848030b10003400e1128280829000f00042060071a104000e01007649683d80301d0642c0f410f01c01c49688507100a02520f0a494144500081429009280c454035001d00c02004184000f1101481c04005c800c00400301141c43c030640070b2065421500c10030040d54800c400186d015401001039503081e18220944501c1c40d405495880c0b02022414203031158500d049a054886000c0e510510042645c40002c0e0002100c003450018115041d441180b61140e60140c00074144070000e0403a0300d102041c0c4110189031009601846424540080005030550424446c10742302d48180c0aa4085950010465900c2200126504e900e15a0386509820094010b50300300c80ca9460f1103480800000c2c5100015409003c0e424010364985000258945c19070b0416089407081144190b030070007000d174200040d596120f520407041000ca503a2109014010880 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 805340827 1250 805339577 805339583
    0x190c06020a03140709080a0201030f02220608090601051005130b2a01020a08040f0507080703032c090c1b030a0504030201080112020a032004091b06170c0c0a 69
    0x100003000020260554801c070403606082c41c0b4a0740c00c1c1e4400c9030a5491174402c3c4580101500441c1242c00107601c20380c04040c0e0100800001030809011104140540070340000920b0f1514000c0c206000594028501e039a00881c2c61004081541c14500454140000720303007044140400070030041c1442c0210750070840034060980d40304c1e445108038a003015006032001400d0080002000700700303141034018000c4540208968882d0003558503580d8030000103984166066174940035000b03000c501c00b0760a2040e5801940039a4403a44411141c401c1d030b051140c000030b0020110b00500103c1d004549480342055072103055114084c0d140c0c0004401020181c24005040415000c0003900003205500304002d002130700d000380e850300c010380e0322510200c52202600102070351041d010b03002000080d40a08030316111601d5103101c40c0071006000045025505103078000c46800e84442112105220b015400400601c0c5078501403810100b40c481c0c0c201800c0c0058202001c0d540f00081c9102402010000c10041c2c0e44c0c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 805342077 1250 805340827 805340831
    0x51e030702010e0102011d1c030203010807270207030e01110c03070b16020a15030509031c0f0204030803040c05040b030c01200f1906060608091e01061e030c0503010e03190c06 77
    0x1f660740c01540f10790f13141180100c150010221070092501c281b0a40f41030b81d036000000d000c2c4034200501ca4450f881c10071080c12001d101501140c401c8107842c00544000c5110380c5891000c5003107003001401c801da407000c0f104000c1c1d000b212011a150340001e500030465682c50180d542c1c594010042c084030f9009610040d42200d0000c1001844602c60b0306c0b1100b003090507a504000079280c40705400d482e445411110030800c0c5c42099031a0110480d40e1000240200d030820062900340d40365640380d01504211015243c200b0340800810060911b0b0041c110009401c90181c00d0041c20704002908803042c20520140c48a072078125452064004c02c6900e030300b13100c2d2104a13442400c24145080300c1c043d01c4607007101c400e41801e03000183e040c09002120b00412446000d040c04c51145152038202669114040040e9902c8602c0043c10440520810018000207080c3c3d840c0c260540c05d0901c19084564032550280c2e01d090302d0061105408015200c103052641e1000240d0010447c0448080b844807a02a1200b4 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 805343327 1250 805342077 805342121
    0xa020c031602030c01050910120912020c0a0504150603090807020a0312090909030c060933050606120f0c09191e0e0a0f0213030f051e030702010e010201 67
    0xe0450500300c201c00307100b201111a40501c40004403071601580480316002a1541c086140c4d0030b008220840410f6180c0400044295845d114102c80b40d001038210b1000d038003e411446402d04040d400d034405008192024015400c1c4020142c010035018400c000c10190f5520550040100110803995190b80040c010410300d51241003200ca442c0d12282c440d40030449903c0b00146403038040c0503040c281500764540a1101300140c41f0074024181010080f81c5600c8240c00c103500788020402804001d45408007214040040d04450384100e400140503544a4181489800031490081c840035910200d00d0303049801c03c2e103664892413840e020345c0700d50b15804a4007280d404128259140d102d0103c40b008442000000301c40c1d2450040030301c03a401808840f8041200150050000340c00800c4c189420810061424030700503c0f10b10302180e140c01c1100d01c44100c1d0341d0ba41c184907040094041c11000e05186910130701e164142c2d1030385c900c00d03040300905008091601d42d0b103da00030343c055510300c1c403620f00340c0d01c8a0f = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 805344577 1250 805343327 805343347
    0x60903100f05010f0e040506070e12060c040f0f14040903140706050a110702030a02010e0f220c020706020d030c0c02190323060f0c130605030603010507260a020c03 72
    0x30b804240a144110792038580300040e0704610701807142c01203400c01c001e8402034a034040211580c50301e10b01460340115800803410f10710641040011300c19001050b03d0303500c81d803c2c5041c1100003492507211500b1000ca80c007003403080160034010b00c40ea800c0100da0000705a56546029900d81c2c0c2c452000001c000b4021400700e09025094010ba4030400180360200005003500d41740010074050b250019415610034006240154081c10794007100c844000c100013000811032000840030180d1900c6c3c82e520515009108041d03800c04d00030464246007a0000d4546141403040007552291840c030300c0c0040503143c40a411015000d5002400440d17006040c0350600c00b45110000c04601480c4401c650326403441141e4900b00c20301c04000140d01e444000580080c2c1c869115814006001810030250404108182c241d100040040c9100a00440d1034041c0c480c51700a00f01402c4450041c1000d00f44102c2402038907040306d0618500041051104002a140d02c40900c6103000b4011a950764140f031000240d05100c2d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 805345827 1250 805344577 805344581
    0x702060915160e0a09181214030f070e330a1706181801050c0a050f031801020c101118090c090301020a09150f0e060903100f 55
    0x4520445030031101c040d03030300e04008061410100d600c40801118039403900c10039071103820300c0940c5035401080421041d0b11001c030102251503441c4030781451080624140208400e620803500889003500b0000c0207064042540c0d80180f0006040307038280703031120380041e110601860201407548030240230003c4003418400494100c0d9000002c001b019070400ba07001d0400c040140c21900c0e22015035841c940d01c0e150070784450512000281203564881900000c2007010300005032070a2003240c100441ca0900004019805e08482c07018204280c010350810045c10125000400c650012208040041d83e90340c488503848122180c02c101e80c0d140354000a150800700c200080c1c2c0f1811800c1003001000107903250014403d0501c100708040c483c9500b240440c4800e46008080d082c0d1201c14455910701d402202d1000900b2a130000c00c241010070b0402a042c03050030300200e000b40f0025400d00700380014002d043d101400c1d941854414900c9920000307a404001d440502c00a0900e110071001070003141c581c100b002d80 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 805347077 1250 805345827 805345831
    0x60d020409180b0a0b0109050d02030c060706050609070c0f02101e050417010b1339080901090506061203040504090c080f12040e1e04030806040c0e1509010c0803070206 74
    0x26200c011000801d07030841c105e110b0302d04114016100c00d400e5529020621180700180f0704141c1c0c0c54043c0c540c0c5000741d0b850f000e00401a035846000001490725004042002300c1c10f010740144108000c00540200140d001070042c042c80d901128034001c01c40326600c0032160042026901c0c0c204810400791082c1080d00031001d0002d07644441440c05045140c50480c0e8200d40d0030b0001c0540c01601d6401000031f003002c80e44642d03120705840c5202c40d4800a0000d5440680400b0300c5640c5000c00840403d0180310f50018040383c012100700000e024505441c3c48095840b0350140c00d161040e80b400700c0000120208108403001010b01070000e100320f540d03d0402c8440107045108600160184403108034815201007a01e41245803402d4400e4201340c18106240e402074001010300540009125a00b210500c40c0c01d2118070681c807955881d00750f4500f50007880240e034404a071a8092041c1c442a2050583c0e83c81900040300c0f086485150701c0d250b4220040f1504c00364000c0260010500005126010303034003051a82c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 805348327 1250 805347077 805347083
    0x61d030a110a120206030c0a031d030a03051b03160e040c03021e040b0a2307110a06090b09040504050a120216060504150318050d090614030f0402060d02040918 70
    0x344246646111080c0c2c12070a42500a605c0b81e010400580408040c8000d045980740c1c902c0c00040b201d288000c83c81c0c0d0ba41c0400300700381180c1d00114140341d21503032501509a0001c0350300a2445e40381d0300c00010090758003000d055003140e81512400d14044078811241041c541600130310500c200044070101900940c0480d4104400b413001e6800380e01800303072800440e411a1b2065401600c0c0c0740d821581203540c1e0300f801043c0c40006201c003440000000d009000750000500841d00602c581400400b0011084001d9101c10203006a1560411240e50b01d20155140da42303041e81c000c1135641d52450010704007a2a0030006082c0c0507030400444045030300044405240e0218010351230b12a8648030107540e140142d10450655001000e003011503548030f074000700d40d52a50b444420034246415505c69040445503a000400280c04000800805920000c00b40d001c4d41c01c1442240345061424940100c2c0300018000f038002d460020312448078981c554121401003104040c00c200c140003039451084250140e417415 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 805349577 1250 805348327 805348339
    0x1a10030c2301050307021c200705100c020d021201020408060c0304120e01051315020709090206190c050703060b1203031014040e1906150b04061d030a11 67
    0x4100100d0034031454040180510503000140907040044605038001451107045016158401c03030340b40d100d5100c2c00c805609907160400f242e003085850b41e1028016040c510000d03480748008020b1910b0340c0448080c58041c0d0301c0c1450f18800f890000c82e107403181041009401c0415144020400c43c01035000c2c0c41502c480400383c410381e854804200c40940010788028280050310285400c0b504d010b28000155410181402400c100308111150a00c0e03000d41e0002401031454400381c4100d40e818065280034000c1c200041082c0d41c1c407034001c98540e0046c5048480c08414912181c14918000c0c0d022609840e8820700720f480280e282c0c0382003c00340501a04050050000700c000d083d5003103022003900c0c81034080071682d64205180000c0914460f01d40c150250300259100e00c1c1540b804010b220b034541e03042505500d1510b0000d1480c0000450f4202240d03102000f01200d024071456500740110f604455461900c460710030503110a2801849151602940c0351280180ea0303420400c45048072449800210380d4 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 805350827 1250 805349577 805349579
    0x5070f0f05120a141f2102030a061508030426030c0f010c02010513020d0204091104020a08011703040e070c031e020105060405060915011b0f0f062d091a10030c 70
    0x301c1035010501d60031075017840d00c41650500041c080d40340c2250070164403200b81c4202c000d1680100707051020011041d262191100703408400b5160b40c1c0031042c014131450004616107440c0829120358074006004462601c2c40c0b040c108029180208280e4107100307003001c00d44080000003207400c1c0c002c00b040040b001c00740d428180061510181d0301c0030318000c84d4000e130050382c1c215401e80c20000100590442180e00440c2824031640b15180c1e880a403400003a07980310382d400c0d9410101a1ba8808106481e128000c1d4001c10052100d040714403105a04402d080c241101882000e2409139406044010040a11070388450710700381050303054118900810090b60100f01984500044c00b00140d421134840759807507250181039100d0b500c2215107224101d204400081c100c2c0f440d136107030030303511080020681d40e4503402c01e11581404401d00c03400040921140c5041d03000c03840065803c140c840c6080c140ea0040740c1e50310b400010700c60202c07010710301e400c034010301820301c0d00e4482024103001d003581c00f041d01c006100d164 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 805352077 1250 805350827 805350841
    0x30a020708010b01030915180c0807030506090a051e03040e150f0406050102120d061d040b0c03070801170f010f020301080c030303131716080a1205070f0f05120a14 72
    0x111b002c2c00503801c51032441c1020880c4411360060b001074007400700a00c1d142150b00c408a201760340060082c1c0144800780c07250030300c1c1d410400d251580c094450545604104c104000040d0000b88039580c0424820b0700d03c031044030000030a82107000350740c8401c4d20b954000d0200f110300d011500350001031941c211110404d41c10710409110445d10300b8050580903900031000740401c0180e24014001000711844081211600c61445480196449a01039070710314450741803000f004281d041140c2d00004074a2058110300d1b29600082043e10103200b01c045035022000341d5042a0010311004040c4c0e02944020b0000050f8822004020340c000d21403010a8051542c0d0300d200d514021084a00501c40a105004500029200d4001c50024103540704052030041151a8440030a1a1828001c41c010400e458660b1100c0201034070003807840b440800c5403403501c0304014140d50003121014100d070f964900340445090750b2505480612444114004552038002004500701071500103401c005100c40c000c05180d15854 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 805353327 1250 805352077 805352081
    0x30c0d1d0316050d020349090e06150706050403084605070801051c1a100522061517060a0f0b0405041a0d0311210d110a020316060e030a020708010b0103 67
    0x112078040048c41030369041106d45520054580c0001c00100900020300c01444128000e6100400840701161690b08100c113040e088413500361310000394150014500c3d050510458544098082c050900e8200b015a003641580c1d420700b80c0b002034a441c400c0045052580340604502400d01c640e6200d00942e58219001c0e0001d03104101a1130350041940d503241031226201c0c00c03800001009180d10040781c600005a541e104815100c07000c404c2c0703800c2e06102003540c01000942d0441c1e00555161081c00c400200641c5d07010010020b520b0507006140c017a41c48060026001c4000c69006a1141d0300142c0d000c41c0603581b4800510031207108540030080c0e010560500c0503c0a401152a640701860b46090b001190240601c040c100300050250b420014100410325100446c0010300780c0d10031001b1070140640942c51050030455603a00e01860b04110890400070b40c0e030711654465041161440307018808209043d0021490810b1540c1a00d41320645000025aa040c1a00c240c040315800c145071114154003034 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 805354577 1250 805353327 805353463
    0x18021507020a1a04062025060c08030403260a0f050f011d0c1306200705030c01120e03040303030b031006060503010608040302030c0d1d0316050d0203 66
    0x11020f00e820207140c0541503070003c0b02800004e0040045a000443e20f46040c04a80c041800014410021840112003e4800820303a0090320601c51090320130004070b00a4429240c3c041c3d41407400303000c45610b28000f040d040c00a00c2c00608403001001c00d0202214064000c1061f580b9000001c22084d0ba52414200f01c2e00380a2150701c200154010300d2070307040203142194982c0844200704440c984200c02503c400c0b1f034543d039800140040c40741c0d01c5951310301d20b0035142034019051240080c03440c1814000000d803510411101d0905120341c0303540c0c1905000050708501c40c20f801074820b0720b40310755481c240a07000d00568074502d4401d006215144d06000d10754402e12040d5100b03035a42c0c600396800d020058480b40300242c010303015444240144408008104000040c0c11600d50304c602c101c07002c004090580a009045181c032a410030340316580e0034450000310360100c41d022541c1d811449900d002083c180b8449800b4280c40c540e81c194606a1400901510b01c0c0d603c0d110144a204c40f00c1c2605003503018156 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 805355827 1250 805354577 805354619
    0x5070b0d150308040b0a170a091101030e07090c020a02030106032006041a070204020c0105040c060f090b07060b0612010b1806070210030902120d08100f030f0618021507020a 76
    0x20500c0180a2170805101404003a1800d0a00c0003095030702c100301c840461411103818411a40f2040c083c000c1000d0f090500c000304000b0700301070080030001f40c80d080d15483c450052a60f119500d401d801c1240c0c1c0300b005074550050b00680200500b5449081103101c185510012082c52420780180c2071141c140350046500300da0f0210003900306900281c041d980c0c5944084002e81c1c1c040e809000c44bc51a038070a204241c0181e10654400003c1c91a020000d801a417002e440710040c0000304c8000c0006200920440d0303000c50780940006004910000051014004c5000b0740c4078419101c800070402410544c000d01010752501484403141c0c03404001c10030580f0560100070342180740100e007903c49a01a801c49080710340b00030450703194410040c40e818904040c084998001614010078000b0a51600306210043c001d1030098440c42800d41d154452400b0340302e03d004020340e41da82c4040036080b42c5289150321441c0d004088003140d0b01e140d0440c000f9500500002e82c490440c1410000b4504a01c3c0e6100480d101 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 805357077 1250 805355827 805355843
    0xb06041503090f060c0e03120301140d052b121a040f060b0d0b0f030c0607030518190e0609010e06130605030a05060106021b01021f0905070b0d1503 65
    0x105a400c2200940103414048540d21070141c00c220004281d40201c510340d000a0b0b03900703995000c84400f0545803680041003240b0542003000140041e51369030185a00003602035642d000d096907a40340c41380c0390125070412840c83d2246182203800300a05001a80036480e802d550741174031040c80f0003281d0308440443d0a10b00e0600440341c0141c038581481e4100c2c5141074250000020041d6903007003002d41c00d50117441103503422560b07807070141e4462519040c24408400203500400b410380c130309000700b086403040c40c001030240b000104800c044140c00c0d0b0354100d1203010107800d0b0025546144072520284442c1d000b42081242c842d40003480c1800d1000749181201c030015203520702d83d2541000c0c030110f544402102d010040e00c8100118482d1002c22483d0581c1c0c3c8503400910941d0314203a0024100b1070101e6580c01d8000c402c0410741e10a03030717001481d01c1d402d43e0354040c80c010300f0040410b20402444d90410040c0640a10030000424081e0342009d0403400e081400c0030b00c8641203040b81250100c0301d03404001e00300c0d5 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 805358327 1250 805357077 805357109
    0x10e0108070e0a090317010b1e1608090a1d01030606060f020d030c0e0406030b0603120304050c0609040e0a030909180302070e0601021504050c151c051909060209040b0604 75
    0xf525038003c0b00e0100d0180c1450503202c5022243c042c01a40b09802950f00c000000401020101031540c0300c40e64000060f041c0b50a008017240c441d0b2002c1003005005d02098008522000e065540c1d032504402002e100c1d01c448290442c6519035070340c40b4402d01c01680c2c1c10b80341403400601a405148540f1000c4000d40c0600140100f0000c00d40040c180b810780c441c10013481d19243c80050300c03240325050181d4001c0e40c07000c489140c19000c00d17207050210380429005038014000c1c0000120001180d004400041b0b8a8139252002040418010322f00d02604804e1817041042c42410300d6001410300c0d0548070105c83c144043c0c80e40031021490658800402801a030009404001300542e81407116044001441902d145070300c103014078440d04405a800707460a0304035011100e8149091841d503c501c852026510341003811404548404d040301503902c08030140c80350001002c00030504140040c070341c0303070260400c650a203604040c4000e402149805001318642000f42c4810b20f4050107a400701c4101c0c0000318000 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 805359577 1250 805358327 805358341
    0x60703060509063c0f0d02060304111804080a090e09070603022107050d0b090402010c11010e0402030a0c09080712081b0d120f0506030712020303071a010e0108070e 72
    0x4008840480750103024201d061300500ca406040708802c4440c2149a66050f8035880b0810490340303143c00420f803288a0140c10701c00141c403007009a0f40e100e90811940541e420f47d41d0085100c000902c8095040c00c040b070070410080020701030140584401076070f00d01840584503641c41e43d051505440c00d0300103038012503007041482d01c01e4009100b810030030248500c02c2000f02840c0f20501d1002d455050210f680403a5800000f0031520403501a00d1003210520000d003070580028000780c45481e0040d003039a01803060a24240d0048204050b401c1019004560700d18150400000078041c40c0c2508001034400383c80021b01660001d50042580d1802d101c0101d600110351701c1641c69030100852070680c00301003091108202c02032001001c450401d4549d050001d03154030605040795155414840d80c0c0780740c001072240e6510009194029220726030607501c003418440c00002e24500070307104d0050500700402850148100c2d401c1001d8102c2d411031114850350390321201c0107900d900380c0380114002c0d400941700003454 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 805360827 1250 805359577 805359589
    0x90c0906040b0105040302031506030f16060e0d2f010306261e031206031603060c050409050a090c150509040507050f0c01050907090b01140703090b031806070306050906 74
    0xb5400504020349802d0703696000c42e0801d58a800382070141c00b805020010a410244403044480d0100f070042c5ca010740c82c250705002040100d001c2c0608102d4a074034400e0403a1903401c0f01450040c1c0061100ca505c810309903401101d5102058014441ea0120310810040c3d40680980d80548040f034069500c180c1d941c969184004a4600d03600e14a031180c00d42c0c02003240111124019844078020181d40c0d80c4580d810500711010000d048140030350b00200d60144080c42a00c0e41c403055940c00034012034001c4078940102e038a0b020b19044204034502c2e1400381314045406600c02505a2f200e24094421560b0300c91790780ca0080000c600d28404030350700f000110a14036143d8800c03a800101400c03c42d00700000b40140c00310540180c0e00d0712107280e55800c1400200700c0208070140040c02c0285050100d8603450700003e215240200b074044aa0f4030100e01e0074205401400700740c000c2c0003025000c90b00d0386421000f4402c00940c0055201d000e004801c041003482c2c4c401e00444043d1507000d00159202d80703c032418440 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 805362077 1250 805360827 805360841
    0x14120618010207080706090b060108010b07031202040b13080d0807050d020a1704031736010b040908030403090b09150315060d0e0c0a0806010e1305030f0a08090c090604 74
    0x41955400c0002e940002d004c28080d2682c80d0042c1d40005010750715103041d07190300c00040c207003030f0601c44414010840c54840c50b08550340c8690500d00f014104400d101200084d0060b5000802003880115600c1600b00f6109084000c850341c040c12140901c185100960710b400d015280c20001500400000034410400d4000303091003416403500c615071a11601195942c0b001c251801c40000701c0c2d9242c000c13105c0000c20405508280c08243c0b80e2001000c0ca080c08000300c02c1d0081d03440c07145090742103410700b0010030760289403802c501901c148000f44071850301c51950760007100c0c110f011400445000c03030522081c40c20344951034805010410441e215288454040d0002000e0380d5182e1900740c003d03149c0d80c0b40c040c09405605886040801c21720006a003042c1000c14102646000e241001010803042c00001740e02811543d000812503c16201d4061881e4000118030f4003030400e1000003a5400c2c000600030040ca440b0f03078030303940d0712516446890240c1d03240c5401b915032540c0150717400e011035060320313103640001c4c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 805363327 1250 805362077 805362121
    0xa02030105061603111006080d1d0d11030d110601080a151a0d0507060f050c07170304080303010815060409050d0503101a09100207060c0f06060e10141206 68
    0x2140e001d0341700207503841e06144502d048001c6444000800c0700d58000c20600f000ca440c41d00344821a20680c205114070300200c81142c603c500002c0817180180144444d5420340d45401900b59006107010b0705000d0b05071004003440550318822a0000182c802e001b0810b4103050740e00c1254224101e201c1c01d80300f00a480a0003440b49801c0c0001d4a820f2581e0701c54140050f1540700300080c200701464410050401362003183c6039414080200030040c00303403401107801c4003940e122003102603021111500c0c6034075600071034100c12800c1c4800000460f0248000070f240840454052001615035100d00a00050700c23544c1700000c10355808140d1a01e4820b019802942c3d100920000c50711250780d039078141d1106584034110b00958064005491074560501c140c0b40384030512940024110949400d00003040f81c4641a8040c04800222400108111443c0c200d0030003060802c0044c02d25003000d440e080900300403807140c0b94445004500882d11030605801048408655001401c0e0303a558200030318610161942082c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 805364577 1250 805363327 805363337
    0x6020a06020304060b03010c110c0607082203020d03120605060c0d110309030d030905010f02120403051c050405060702070f06050909100f0b130f0f0618080d0c0b0a02030105061603 79
    0x4d074000746c4091080c104110090795503c0c0c0642c1d10340840c1d83c02c01e100c3e1000c0300e005c1c0504000000114503503004945501090000c0407014407134155015004003100c1e00029409000d03400d201e81070590104210042034004282000341c5035071002001054892907610b080240c2140c80c1c140051400345015400c144c0c88c04050b00e03d043d1321600003905104e14000700c400442c0c1d07076585142c1488024401e1034585544820210325116008024410120b4001d1004081140c0080c4e00318941100d90f41c260020301c52002c061000c0d00303107490314580ba84000c956070801485000c400044a40f0409041011200305449451a02a25006000798440010030020700f42c0380300d502c0082d01b0154500a1401840e0f11024551a107507003002e088494161544120303100c0c00741444c14400d16904501c0e06049802a003404025046c14000b90a0010b001c0d81c400480381c098003400000c110303040001082d1403445085017014590f80c2280b402d04034002800741d81e82244091000c0c220360400820b0b400b40b014004d0800e = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 805365827 1250 805364577 805364591
    0x30a060603020901480308060405150d0c0b1b0123011a0c03030c300c09010309050d030608010b0607120c0812010f0f1203020a06050c0c0f0c09010f06020a0602030406 73
    0xf0f00b01030740f0640d2404445c60483c401c1c04000d15911078201d6406c200d0443e8103204605001c01d030035456000d040e8940d03105400f0362202404100c9030400711002042e81c050803c1c0c80f80310303000c004040c0e90b8440308511215401e040c0c03c043c3d000c54410030260102841815120907908004690080780c41280001100000421180710b00c41c000308080c5200782e0401480d40e56038800343c201c40d800d0243c8101c1d1020744c1309a01021450640814001c1a4810840a2500c1c4c5031107401004070054281c416001d0310a00600c409245031039031680100c010f44491800a019000790413042c000d15100c0c000000c0c0c200500311410401c0d40d0710601503220003501038640c0ca800c0642c0302d9a40203400600780c5c00300c001508034100402c0a039400a900c6001044026900120301c119030302c020303482c2e0254010003401980c0d25800102c852070160f0966045c0ca003800e040f281c4041882014542d03a11101004c071340704241d00000001c0d0b08031000da001e8103940e41980079164600c2d195960001a400c00b0700100d6143d43c881070707 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 805367077 1250 805365827 805365917
    0xd0b060301060302060f0d061d040303112110060e1815120105041e110d03051309050123061b0c040e0a021f05090f060f0f030a060603020901 62
    0x3000c0c240c50004146d24640d0b6101071040f131002c84019a1100300f422a0415005a4500745480d403985d115405040c0800c01c5075440c190743d102d910071001ba80c0c1300d4400b07460300b400b1600900013070140302c0c21b0110030082c01152034000560712484841c500e20351000858804218120490034600c0e0031030600b8401901b030318003000000da00742e1115044024aa0741d00c4040005014001c07103000301c071f002d4079408440010340a4881c180d03451110380f004c5014900035100720013054070840c00c5846004002007049810750703e41090002414003803050800c0f070642d8485207018250359113481d20400070020801c1f8906251000c1000386034000e103018910a0213129401100d644842c0100e4001e5034201018080160f00ea01c1000f17500012200c2080c2c2070310380c0c032001d48660741d04442140e611031011900940f250440d040010100e20540c50140d50008010805081d20384910016502403100d005080c40303401d880e448110106d015000c1d84600180f0742c0380352000d125842010300510710198920011030030004103 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 805368327 1250 805367077 805367089
    0x30712060b032803020601140904200909150105060a0c0312020f0d0c080a0603050c0d020d17070302120903030d020715050403021c1b0209071b05030901110a020d0b060301060302 78
    0x3010f54041c03a03840e2071604166051041c640900a5045524244004c5c2400300310150300003880100003050010403200b009900600c0560341040062030004e030391508a030000d444240c0c442040f040211a5000840e0030f01d885416074440c2c002541d41e0461150344c9450485020002c580c126009035400c020102c4203102201c0103201c600c0701c00602248444003844010b0910fa0001d224117103040c904030092001440104801c502c40c43c0840b855000e440b143d00018444c2c8020100040c90f14980a00480c0c00300d2000d0007400d0b0250294085c1c1d080b0f40305003014040d0510980f818540c0c10741041111441f801c007141c0c0600a01030080000441c13420114100c1d204403142950154051303803248005001a0362100c4031301d00c0d01e82e686e03e0455079001000070020805541e05074020701c00c1d14840c0000380e00b0307407040e00558840d061041d02c00310111401d0401940b00d900c004003441c00500903200300d01141c00001000c0d02d120740e02420f400d4031050707252a09a43c000025041d00d905540320400000076036694 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 805369577 1250 805368327 805368373
    0x308070602040e25030c02120c070f1d0a09030e090403081902070c03021302070b010b0406180e15010315230904021806010e0a0603050a0605030712060b03 68
    0x52400140e542d030400c211500d402c0c00042030000c0002185641074403100702004d0f5034824400324140400c9115400209034200f10341d0401540c2407100101b090007007107800059410403102c100c0c01c1604050340b02c0500b01026031020048000028100e00441c1070038400d507011556840c0246018480d02d480180010000d003400d46050f0700042e400c800b0b01278400014001c00c501880c602800318648001c90b9a040f03a203040c24400640718000341e040c0d100c4e4810301901101c140c07079880501c4038001d40c0c46190410117034010f4020840014180100f103204ca20308080d600050f40e402c04544040e0391b40748003a1a400101c2c141400c0c0c1010784480415243c9080200340c40702030701c4010001d40c1c0800055030f07481601c0e1756540196100340118024400541c1b01c46c40080d90f050482c808000303c0e0740d00d28005a0780d4074007910006401100c0e5907400564035915921003070061481c0481804281d54400400d03555044a019490350070079020001d0002a50550001e8160340c0081c1c190341d0030405007000b08a243c540c0c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 805370827 1250 805369577 805369583
    0x102151312020c0a08010c020703080d0b030304030b011503091a0a0609050702010606030e0607050304020d0606030f0303020d0b09070207120309080f240408041a1621080105031c0504030807 83
    0x20043c00c49245240520702c50003d458400c001300502416004006d42d503143d1440b001e020181c001440207600c0b145500700c02100799001c1c040300c0c0e440eaa2450400c6211030240716220705181d00500c816246403081c040e0002c62604290540009000910b40da011490050318201846030340345400038006c80c482c042d0b14851501c54000140c01d17407903d4006400d94007030120040e07594101c10100243c2ca038100056036007107501551008540790700c6141c03a20040125420140200d01d0f0101010201a4543c009141e424404002401415984414402d4610098400002507049040c00f402444900a04c0c205014002d1403d02e011300da81c3c00c40c050600043d8004444560001b03500070b4070552041004129000c0d000c1072244a502e0640c5619030342d03020354051840d40c0c062207120102c405d00500141c4617100701c000c848040680f10f43c9004000504c00003002042d007a6020902c400b031500901445040b00d40203005805201070741101003a102c40c0e05150103060210501022020070715040c0a0010588 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 805372077 1250 805370827 805370833
    0x901060315050103020c031204021c05010903090b0a09060302030c070204061503061a160312180203070503031e03060d0507080a211710230a14010215131202 69
    0xc1a90280c0e5014401c0d6002141410300400051074140e100004603030b03d80360341c401c2e00250ba0f01d840c800101040c60003245546210a541d0410341808010350120707140501c00c3d16200c000d207a407002d40308417070f00030b20504a020840440e42003100318042e8000b15031100303103445490b14140303e0382e0009080702e015030080c01042c180034030310b51034080c0c15104010241103560010072251036804604ca034144500c00842d06840c990206580170540510695804000000000d100c1c6010360812500403004210007030307100707204a803000a228140072040329115204850000d0b140030740b20781901004d500240665401148510304a00407032001c1c01444068110b4034041c0c1100b030514140400308150b14803101c1d11844200ca51205141c2d003000e400166034083d009094920394420741e05002c8070031f090b070021550300700d500d05407810104428034002903c0000c0b41c0c000080d036110203558501410003040c8070b025030700c4005540d84c5022020f20a40d40901c2811130341c04008002e0761005410090f075210200564 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 805373327 1250 805372077 805372091
    0xc05060a050c040f080a05120c0a030f0c1502031e1003021c080a08240d0f031e020f07080601030f17040b07030c050c010e06040603020a09050d2d08070303020f0909010603 75
    0x10101340113806008d0030346a8141c3c200007000c100745458a072a80790080901196815004450740180802d901080d00310300700000c80c0018218200c084c1d4401ca50703408071802c2d11200c0c0541e114481c5042c43c01042980711003500b00b0b0031942808086105111613131046501521070500044444004040c1c2210030340e00c410903070400031058512007100e40d540c0d0180c410b2294040150303464042d04081116041001003191160504099800e812044508481a103907031030040201034000071140c0c40200280700702e5035144c3d48d580885495070700a000c0100710601d90344203d00401c0504c1c40c100715140542e00401c0c90305075618030f0184c2581c40810700b1800301d020701d0000300500500b8801200140c80c2800d004140e44610400174607903100d40c2c041d250500d6800b05803c10014400c0ea0310030b020340b0001e42480300b060b049080614002003000702100140170880324064801000d095040c413840e62005071142402c1c0143d905501a4000c03500b070b107180300c130280030700400c554404070810b00030070054070002020 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 805374577 1250 805373327 805373333
    0xf030c03021203040b030412030f05091606021b12030f030106030902090708042d0b1e0c0a0903020108060d06051501081806041e02030601080f0d0c05060a050c040f080a 74
    0x840c24050b00c0b8043d001808100080c85444040740d507c10307800070780503203080c00700c51041c1c00800e030000081082c18600010440d45c2d08001034004d00d81c5031410860514107503501400c0360380700803402c1402002c07805135410441c2030034002003041a400d51902502c0c2420122940300b00310740c0090307100d00002621143c0400075801c0041000c0d400201c14a46110305243c0f40c2c07182554800070007280b0031290b50301000040007001c050f600e0b8065a40c040540034890501403c0c0c00c40c0a0f08040c0e481c410142c840002c04c556082c15002c4954000c22502c8400900e03255400544c1c5040d402400181c00c10f002d442c014000502d01e200d891310a658103801003101c01d00340b40005010150040400d0b0901070540d9400d60707000300008031140c0c882d50080c0907445038a405100b51200800d1040700941502c580000890f620b40c0c04a00901e20b0a90042128a40080c0030000c5a03410010403020b801500081d020609c500c160b0b40206610a0080d40007600c0c09a440440d03201e512101ea2000405421a600341410 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 805375827 1250 805374577 805374589
    0x3c030f010f0e0601051c0e1212130510090c09050106051b1609050a0b36040803011403010e030f040801050f040809120c030105041a100602030912070f030c0302 70
    0x80c1110102c1c40b0703000e103840000a401841865080b01c0081c00c0b5001d1140322561517000305c1060140e030b100340e0307000700c00c0c2451109017500044ca070710b030272100d2110005460603c0c1800400d86550424000d000110704c0540300c0e001491401020389400004010116800481e806400c0c002d00d01a070300e41c1d6450b8000d8202952811040040400c1500f0050768038007001c908d201c206040c0d800800c8005100d4540141e50ba0003011420a0b003034211403d0040039000200298169105260b0303141c14820400549003281d9000034111001001c12400b03000520100c1c1d00c0e95004c084080c0d01400006900149a8000703141d60001100d402c2d0b0000300040a0000e4002070244a80100788a0100009402c050752001c0c441d0082240a0780035800312401e0035a44842002621040070000c0e0003001903007442d052074000b5000380807201c035003214040b0210300c030300c49118040d00480c0c1140d8007960410b0544420840703822101c600a054a1044020101d9400c0c0391145d40c0c0c004501c41c0001c481880d00c2c1d0b20611003 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 805377077 1250 805375827 805375829
    0x1050f1603050601050a1142040302031209211e0309190f060216030305011205061609091505031207050604030c0c0e07020c0f063c030f010f 62
    0x401c06041005003c800c4c0d03000800d41d00c010780c840c20f00d640c006640440680c94071524504c40c06440c05103051840e4036582e8003800e01c05e00882c1810191504d01080300c01c8400800556000700142e204105800749200c13007002c0c00342c10142c020700340c0700c200c040000070303103400c0500703445102c4072880c0003500d54072a02c4108200503851342162581c9003103103400c031401703074036440c625401084400144840d1010052082a10000942c2c041c5c800c540340c1c103441c241c140076901c04c0801140440c4c83c21001013070b48111100503803082a0302000918040c1e481803080710f01c288072072003039009110940b4004507604011b40140c00651106118038041940340404161400d10701078002d0074002c104106441c0401d0000c65640e520580500740007540d848140340000d030f0b00c003450340540e20b0f00801400b404012940803c0c21000740000b1181c0680e514982d00c2004000c0c0300f60303202048a8145c00605d0b04d12200800c1d43d00300c060100d903500e10400f4001400310803042e401140c0120458038520010f006003130b01844810 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 805378327 1250 805377077 805377121
    0x304150c110c0109060804060906290103060b2701030219020a0203060f0106090b0f04030f0b0a0b0603060f130221010608010812030f09100608011d030c070b07110301050f 75
    0x104c1552401101820844024101501c0c40da1580c0a040c24481180c00c18281881440c1c140c100b984030704000694000148654640001d00b00f03400054520f01d054103480c0010740c1205201e03288500503011400100000c8210f506050b000d1020010740008510f40d54402c5640f0f401400c00c0b4402841010300704200100103030dc40764110f40040c445150b01c4031241d42620070b48001603540d0881198403860038040d030351004202d01d1541120404001d50350030501c1c0180c00142050081c0042101000720a01003151541d030800b400c1c81048010b03142620500c4c50081c620bc000518100b80d50b02c0e00c4c2c50315500c0c1074444a80032058801040145c0d40101c000380142105009000704250911401c0030354030000e03010a05c1d440341100030900f4110180b0580384030a003c5001044213a81d1840110b01030928400441c004030480d104c0300c1d000100100844d8200d0810901a103a1103040410002050700b05580980703030140001d040c0200368170b092140b903028000e6032800402515103019000407486d6246010 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 805379577 1250 805378327 805378337
    0x6011205060606281815020c041e0f150e011503051302150904050703150605070b07080414010614130c0f051e0d060501181a0304150c110c01 62
    0xc0701c00c6900b070294080c080f0f401840c400c444c2984191044560880860b0032080f80f820102001800030a40307900343c82d15200036001d841c1d00150210800c8112140e4111071a44001480884000f0416540c08a01d000722912000580315a00009190141103103800c000c858141140052010403411040c07200e4150582c82e040c0a0b80c504808803030110900340e840203001c1d01d160880b402003142100296266008094410025803030044001005444180c200780c44000d1f0844011035041d05c603208450803140c01139180c550607190030000b11083d160040c0152041620102c440151020a016550080c90207581d03082441c149102001644c0c1c054070103050002d443c201c042c00041b50071900c41d01001c0c0b12810b00c41d844001c1498200e1016180300100b82c25a41e0005d00c81c03251a5141d0303c880162030302070f0b0320014030001d02c030720f51511a60203001c1c00d04800e00d01c24007040d101d41b6800040d0351040c03040001000305444500881c0645d80c81c00005400f0610901680117044002c01885c58141424640 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 805380827 1250 805379577 805379587
    0x50d1808070b011509141201020a021b0612010e0702010e070b04050102061003202107170622020118090c1d131109030609030a0801090204141c020306011205060606 72
    0x5480444640710304680c00100d6960241d490f0303100304901620300c87e000020741d03440c015000c0094485d0000000424400c40070342c20302407141459404d486d2104800000b9500036400c1c40c00e1078001c010300070100c4003190348404104404c2d400c140007020041183d0860281c0b598181400603041c00310040c454404d010004c0c10410106000040101c1400f0000344000050540302c00030a400c80100400790b10aa04c442072030110007180020f00a044403121100c00e0460100122403a44880094421300890306646d04000e94603010107d404ca0224030504001300002500e0140c0c80a0b40b915500c000d105c9651400101402c6070012241600c0021301020040040c480a00292008000101d4a0782c02540c5080141690f01103008551458178014115011071400888580e6250701c500c140900144e04400000340c050064000e03602541c101c5101c600b18501d04d04180403802c88031442d1f8900c4e502d101e4080d5009030f00c01b40f2000303004e130404c2542815422881d0409915084014051500401301000 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 805382077 1250 805380827 805380869
    0x150702190b03251e020a0219090b0d03200319090602010507030603020102031c06170a031d220f05150f0f0d023d090608090607050d1808070b01 63
    0x1130402410b80109000c00404d1418035012803410001380d00080d00100350162069a003480c40035560300301c03404180140700303042040060002c00c0103610001130105040c07a403510812111004d000d0f5002007907800312818a0b40044025280c03094030082c0e03401081e940441030111a42c280140390340000c4c40d06003400200d1459000079070300c0c40381c2c824010030100201d41c8030021a110343c1100b0028001d85000707040940c00490150344820800200b24049004c1c3c8481411014610400f1291850007c1881021b41c400340d4000700c2201d00c0b40344a110095841c584032040350f841d44149400f0380007121202e141d150003081030080d4000c06010705403140c0344510120400e0354601c0b80c0d00c0f2000f641a44c0c03142c010030701e02d5070181000800072030382071180f00003c0ca030010b150061408110245415a15071583d1503590100340ca200c001611101443d4001c0780000c2e034018010401408020215203000503291501c0d04c0d1000c410034842000c0b6910038000070448140701c00818024054068000f2500c00051006 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 805383327 1250 805382077 805382087
    0x51912050c1c0c030204030501020408070f0501090b03010905060607051603120c0507050d02040207080a0c0b0f010b0d1d0a081207210c0c02090a0504020901090605150702190b0325 79
    0x1c00c050b5003d440e00003800502d0b101750165001564040002c0d502c581e21200403d07280c000e6405080101039411000007041c2d07124422640071941210102071560b402c100c6204080c04004003000d400c0704041152a00041081211507403081c403283c068105141107103803018009011011100401864900b0035000c22000b080c000308440c402c58545c25040043d10114000e4025840d01a0041d000442c41e90315480d004158446940e12885440b20503985074020f005039000280500c412035082444240404001da601c0511800c0c561101140301000c519455454224080f800b1184d00703d000c41ca0b89142c04a01001c540c00800351f0038008030406013406640310242d0300e9401090b80d9512203512202c0700b13008080c01c0051035005010b80004d8a000c4c400940a8403017920700724000ca003060300000720000640305000c240c0d0343c0180404401825401c012030700d90400141603070f02c0722284140ca000d5800c400040001498421441a100c0c035012184005000010501e42d891201c48944030345074551007 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 805384577 1250 805383327 805383367
    0xb1b07090b030d0c0f0602040b0307030b0105280903050718110c06070c1407061e02010b010f03090c091b1d0f040207060e060a02040f0f0b0405040c051912050c 70
    0x3494002082c0384c0904000c1351404441d540070308a14030020703010400d000d1341c9008500c1800a618203000900305030004407804e2003841018000c0110101101252000ea20225002081c80e49881e989080c1c4a889407030925449500910700d000240c0c40c00d10713005290f402080f04c1c8034031740c1c4042420598103e081903100c04c0300038940d80421580070300c00e404100c0042142d91030b050030380049603016911141e010f80b039520b800792820a00040e041140000302c3c0305019801da1000c1c103944460802c0712001342035000c0d011100301101c084d41e46902c0400c80803601c6c400e415070044091007c813440d44d24048081c00818201440082641101e65014183e031180d00a4200f80501034400595034055420000c0040050200406590040005100f5012080d070041c0c401d40d4405111100f00503030300d05844081040ca881150070a900c1030004011600d020703070041d8006c1d41107043c020301e002c0300410b804d941c007800315032080042241d005002440e4078161040d5544911b111507141c1c44c222108e003140459101c0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 805385827 1250 805384577 805384603
    0x9050c09101e0906172509050d0b04030e03150103080708041707381308060703090c12020d0b040302010e071d0609062103040b1b07090b03 61
    0x66044118001c0c2c820b4009250300380780e802070001c41102811009000701098440c1d030000a41c210152250100051403e40c01000341506540401c854081c40443d01c3d0084d0121074280300741d00c600014a5114640ea12544030b10401e5a14240d1030b042c680605061103021540b0b0299000108214604239a010003a05598000105945070391030351920081c1482141c000e020722003804603924101c0c0704001507070015100d5440409819201c0700c2c0303c07214810354110b0107008540f0154011900000e590700244610212500032039151a2100111464210306981031320021b6901e00c1d13a0741c10f1101d0001c0303030b0f03028004a07030004003403040c00d400058040000410161000c1081c0f0b007c0f40402d130003580811102c007100e50503100d400d9a1403140c4604031500ca03000080c0d50310050b000030040d180110341a031040c54000d2880c0b20158180e21030301e00401601400e000305100400001c00d100c4840300242c4001a030040321038070a008005a02d03070410070a580150400d60510b0352004c115070b404581285030b049 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 805387077 1250 805385827 805385839
    0x90504060204120320010b1c0525180615030203090a0506160e031203040b100902040909021003052401020705130b01260106050a02031308010e0709050c09 68
    0x495050400092203180d2042d000880120103aa0402da00001c443c104200c5640044440d600d10300315141c20780c1da1501d81a41d00107203c0e800040d40e040c80c01920b0300e00c94040c0c0704032070444404a08002d075220a108545c0100c040981c001c00110000b074110324901641c0800c2403101601e401e10030b50740b5910460950080c96000700020302c11140c1000125200344c0c10108503046420706500540c5a904141c80560000308240d220701c2c15800d00280004480441108040c036694554071400c0110a02030140700c407480c4084c0c0c000419440c0381c0094000750411003c00210621188100910002e4410180c1c050504040800a86040003074001c1142c0310816841c2c4000b030b220000403400c00030700e50041503010744861301e5144245250b81c0b09014120003071700c94030b001d40c900301500c040181c20954154110800200140406403280d4054109031180c1d00440341048100c000b4404c5420740c9801615082e9558202d50300c0c102d01c00c0180100a001903201042a802c02492442c41403203804541c602510f = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 805388327 1250 805387077 805387081
    0x3150c02100902120607050409061a090f0310050106050a030524130605030114011502210d09020306130510091505090c0a080a0b0c03220201090506131e05010203040905 74
    0x9125005813015808203101502d0280c60071510140941d00305005100509140c03280c04a28188001c9450b030051026100250510101c4d40070003c91040c00fa200030f4250040d80000b840744242c0c0d0040314003030011313500c0d1140c4800d10351800904842c80141440e04140029602008481e50421030207022881503407070051480f00d00031034202410031644615010340c80c1510310001c20300040d2905050710141103c0600000b14034104036a40c20b94080f403c5080b40c596840e00d1b840115000040041d220b1513403020482c1141c40d000281040310480f2281c0392408000c0b101010080b080c0321504081e4002d802c01c200790006c3d40c03180848510b01100c4250705071781d501c0c00f25149039410001c0c180c00d040001e141218031030302d070503840c1c0c0c485540030000c0710b01441990103d0083c4a071881034a218041c2d40154401e0200c420155020070b21400b501a41407007100c20b000308103a19140010300e84010307002441b0015a00d0301c10b9680851000096815004501240901003603901000f107900300c2e108071a02140503 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 805389577 1250 805388327 805388329
    0x31101020c070801050414060105130e0c041a012a0305033c070504140415031e0c080a0203030f030718030b061c05070603020a020109080d0603150c02100902 69
    0xa00c2400000900c070b00c503000001400900540013148500e20480c44160015900e600c107030750342d210030700682d94044070000c1444840340d569440041e509400404a411031001440860300b100d1100ea03964880c0e20801641e003102c1c1d40c004003650640c000d10402d0100051070366525031380607110204002e041040010105594209010654480c28118455114043c11858004150070075a07001c40280600d004001809640203000342c90444280c1d110f202005001c0408200061000001d80e581004e43c02101002060600342c40303d922041c074640c240240d01c3d80d0300346004145041d0b1301c1102903078400c0300003400580703000c801e5400e41a40170240076103d4030356100640b0f00707142c0d5203564219108402d4000050207811008680600c40a071654090510100c078211000c0e000108003401c2c60b4002d460402009109600a11a82c0f2040c0300000308030703030306580d5680303140d03c0a100e84184070745660f0180203106d8000144a19001715400c1000000108c00b006500c40303004100d40c0011650300e9540c4019 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 805390827 1250 805389577 805389581
    0x1c061b05091012060b121506070f0f170310080a0525031707060b01021908030c160501060e0106081509180109140607050403020d1101050c0609060103061413031101 72
    0x40041e0105041c0320702503e0b40f80d905c81c5a080105003c0e02d0080d450040f4401c96104012101c1905005d41150714004481c2c407403980d000c2001604407105c04024403075001180140c41c0d0310500046040034541d580c14a26034000d40070030541c01c1038429070003d9045000040c40029200340c83c035407a1701c041c080d42c0b5001103d0848004154000340581e40b082d6241d84102c06c03c3e41c020500f00d40300e084200011801400120307540c200c01415038800b8098025084086511030004e5940900c2100d20246400030941600c11049800c1c1030413a0140e448003014400d21b18004401805040b40385014413013480e200f450302089814a03502c2c113005041c03041c007140507002a50380550910032501d00912201d8400d180c1701d00103843e10500500c848c0211300126a00c2f0f072043c001c6408a940041c01031000d030110303894011452402c40c04181c18031a081004d1034403900306000742d070b200e200404040d20f03540d0700d5414840144e0b00000f401600e01a0840100301c480742806103070031a07a9804cc40e0411030301c0e03040c94070240 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 805392077 1250 805390827 805390847
    0x509150a031a1516022b060f110307030914010e030405100c0305030f060a0308070f0201080c090307180204030203011d07091401230405100303110615010804050304051c061b050910 79
    0x80f400c0424089410b10000d11080300b14480d000c01c00400708d8505005040320100100884040c008001280c105440794011800750b900400a400800b55480089030848d440360240020682000c80c003001203151680c00c405070038489040080c000441a540246288401030000011200c80004508182c66903000c8001543e13000d44001e54035941824450011540c102c0300700d0000d4807520000f08042e015009071440c2550240c0245003c40c100344038028050b4144150724840c1d5401d01000025a90034011460300200c8001708040c0d00307200c03001c0305080290541041903010304011410f00780a400c91600e90465480100d00d070082007598090350100c0c3c1c0444130003980305040c041400150300803040c142044912942312800b071881c8510301161100d1044805042038040b040107150a5400f9081043d44141b044040c0c2e494a5143c1c03000586006850001d241c0340520519048204051441603001c101c42640c0550741e10090141c0007482840765110a07400703006090fa945043e180900600381d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 805393327 1250 805392077 805392109
    0x90e0f0c04150525051b13021b0307080a021203061c2a05010215091009050717010c0815030606040b04090605130528030509150a031a151602 62
    0x3815688070840801c543c290051750540101d0070ba020960f00b40240c90a04101d01400b0702c0c02c0321011820b40402034001c5085141c8580301d6580700541800144010103500c1e02c10840c0300e440f151a484001d2a1503231a652207210184104280072107682e440840d841d246c1416400000401ca1614100c0d00c0b1009030400c00040b02440e0304d20b00e026401c5030440310180c400030781c21540d00115400c3c60070302d04441694000e10982001801440c08d50315500114580741c002c03012078011540d00d0f040c51607892080b0700303010010f0f503403aa8040589a8041c201e070360400341f61141d0340c40d00140800000e4881e1009400707e845650368890f0803000c0d80729074010409003604104204082d1529103141680051b124078215140c4c00b5038402d40c110011442101450b0395100187d000031244559002d81e010b600c490546940154542842d18419034030000820701e800d09a070f00401c48100111048145800d000c214a2003080d0025903c83d0001d14075040d9045c11640c1828040041c081e400031481b440001b070060 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 805394577 1250 805393327 805393357
    0x1903030b090a06060311040e01030204020703140f07050c0d0344040506070309080406050a0507141b0a060f0e041121160f08040c080706090e0f0c041505 67
    0x10035402d000390310180840315251001d000d800c8034085d031041944941e004d0a0340d01c1c0761810040c40581402d070b006d05411031007400c10840c241c6002d0700e21555500080e00200148000241c05020001c06103d2601080402d8074030b440300070b0305c95501419442c6010f01c010703980141030f40c0314220310502d0041d0301807988640310481c08420301282d042141d4041110195194407880c00854045032082c8140860140c00c106400c0c02c05040003000c0310182e004091003010071009020290124190b54102c0d14158200300042000700c0c0401560540498080341007031080c41903031001c0018a42000f41042c00fa00203150840342e2440010000d001090205001c0d50502d4011501400d074401041c80c13030516804502260889071b4591a80070030032000341c8102000140e581c500303980702d0703406182078940180c443d41c01340c03059980302c4a08624000c601d0b1f100f03000051002c0d804114405101034115008010051800c0c801d1520040b10700383ca214030b00c5101001d034092182c19003018407950558034041c004941e4 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 805395683 1106 805394577 805394581
    0xf0603031b031c0506210304050411040e04110102072103080406140a0c120216080f0c0601060e13020a0206060405090f06240108091903030b09 63
    0x700300040c0700511003030b900c0e090100102d01d007010300e0b0480050940360200810822071300d0000301082c601d0ba21035910a0290300401282d00307440080c1d50204214520748142812449a5030108040c005003005000400610b4841520050403d90031100303015154040803160300f00c1c0b810004080080d08841d140024020320a483d4858015000001d404c0444d002c00e07041b5540440d15200442c0d47c400c0b40d0550590001801009210b0543c0c0450628118014018056440101c05003910a001c44c5d484e07100300c4802c2c00c50b506480c000b015035a4659407400d003e070814201490051107603000e08108620720000748252890110035074000d0869440d030a061100501000d42005164011664641d0210f18104040c1c4e0140740c0e003120324105c0100025031003014078100070700181085100d80602200010001c0c40e80240041070082c000c445580d4034060b002410041559a081108441 = true := by decide +kernel

theorem cover : BRFrame.Cov 805215827 805395683 := by
  have h0 := BRFrame.cov_init 805215827
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805215827 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805215827 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805215827 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805215827 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805215827 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805215827 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805215827 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805215827 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805215827 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805215827 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805215827 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805215827 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805215827 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805215827 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805215827 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805215827 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805215827 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805215827 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805215827 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805215827 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805215827 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805215827 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805215827 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805215827 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805215827 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805215827 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805215827 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805215827 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805215827 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805215827 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805215827 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805215827 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805215827 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805215827 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805215827 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805215827 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805215827 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805215827 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805215827 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805215827 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805215827 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805215827 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805215827 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805215827 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805215827 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805215827 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805215827 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805215827 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805215827 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805215827 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805215827 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805215827 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805215827 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805215827 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805215827 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805215827 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805215827 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805215827 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805215827 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805215827 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805215827 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805215827 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805215827 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805215827 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805215827 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805215827 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805215827 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805215827 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805215827 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805215827 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805215827 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805215827 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805215827 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805215827 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805215827 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805215827 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805215827 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805215827 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805215827 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805215827 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805215827 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805215827 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805215827 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805215827 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805215827 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805215827 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805215827 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805215827 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805215827 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805215827 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805215827 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805215827 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805215827 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805215827 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805215827 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805215827 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805215827 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805215827 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805215827 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805215827 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805215827 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805215827 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805215827 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805215827 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805215827 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805215827 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805215827 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805215827 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805215827 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805215827 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805215827 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805215827 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805215827 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805215827 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805215827 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805215827 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805215827 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805215827 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805215827 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805215827 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805215827 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805215827 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805215827 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805215827 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805215827 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805215827 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805215827 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805215827 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805215827 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805215827 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805215827 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805215827 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805215827 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805215827 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805215827 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805215827 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805215827 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805215827 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805215827 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805215827 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805215827 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805215827 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805215827 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805215827 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 805215827 ≤ n) (h2 : n < 805395683) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
