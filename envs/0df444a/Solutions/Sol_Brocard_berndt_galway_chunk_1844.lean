-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1844
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:52:44.303987+00:00
-- url     : https://prove2.me/submissions/b3c8fcca-d04d-4ece-b8b8-1299ab1aeb4c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 331474820 ≤ n < 331654676 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 331476070 1250 331474820 331474837
    0x10e030f07080705160f030308090d020c0d06061205060f0f070f2a23011802010c080c01060905040212030c1b0105130803070311060106050d05100b0a0206070f020a0f0602 75
    0x8903000b00601d002442035064005006420850031003c1e1548c280107026080140008107550014103108070f040c0d40c0410581c252505c2902c0c2050000c540e45010001403071240d105002c2080004400000c1210101b5010701500b003604444034543c0381d50452005112041e5206004200d1050755a00d4090140000400b80c0000d9200e50101d0f1540c02103200704582814412110540390310390054070082c48448005031010303034000810001e41070b80b4003201142840180a418401c00c407001d00208034804080350b00d0b0303604510081c031240c0d0b038441215000e0081030341c040341300f688807221644040a0000a84034001500e40042c011130031000341c03503801c00c1090759865041080c1001180c0c45040f540c00d948008154a00080da61400319042c001c05800816401144980042004000156002068440d8885408000a810344500c68081903c50a0f6446558034050221f090700c0308680100c0c0140c80b691158607192140d042d00c000898031000c900310002e0510500c90300c1040422400e5001d8641c01 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 331477320 1250 331476070 331476073
    0x15121005030f0706020f0a080f090a0302030f03040f050103020c030304060c030b03010c0c15060f060e0402271513030f020415080706030f02041a0d0b090106030b03010e030f07080705 80
    0x140d40392000300e4100110b01010b840b0b075501115003041020382c1000b0700c03aa11900c820241c00405580d551300c20192260ba104101222404254480d595850310540304c000c40d8020122401040c034220327219102d82061140c0500c40054000011381c0d0350203402107900c01c140d90005540f450313455584400050291602000c00c01da07a4092510080c0c40c24072400d100d5142030f45800f13483c5821850a8465000034402c120446420103004100c51460300a2010540740c080c1010802c00e58002c021400900800c8140c19001c800d032038030717494000c044045000d01c001c015100d11110303101c40481080188103250301005410100034007000414201c1e03401c00910b6100400220b40d04a606844101000c1507401841c9103800106040000542621401400e402ca0030403d60500d490004140c196525180c20742c01e203100d00090881c1c00d8a000d41c0712070095400102003079159611100010001c02c0ea40c6101d5000790b203401003440583d80c1c00002d0700e4135400100d40032443e10700b050b51802c50640103084116440d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 331478570 1250 331477320 331477351
    0x1170415020c030d051e01030b090f24060a03150c050408010501080606030d0906140702061e1e0f0f070c0b0f070b0a09030909022208010b010e1512 65
    0xc00300030340010180700035440d00442d12003620b401d00b042100d00c0609203403000c10484400c08291225001c00c07a04603a0442108060f07503803015191410109250010003143c0a40d400c690095440c003100c03908400d2104500560b030755628418040c1c078400030301004e07000f940750514203603190502d030f0405140082c4d5858490f090503138841106095900a030804074660308040c04000b201d0030204004081094140782030120f451030700d2400380c002040701c680364941110003e490000d5480b40d0007100c1503a080106150812401d8003480360035600007855100a501920b00104120303501c60040c3d134600d0000e03d140925120080044007101d40c000310301102c940e1000e1000040301203000c0c0c0035010100003041010740e10b500340e10340080c8400d4010100411145030203200340c04a980480301c1815240f4590005a6441d14409500103000000e03181c121411070103d804550480c040d0071400003a5802e0701c650020303884640c100304040b80310340504a291701040c8520144a6107c622040d08880c400302007030711 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 331479820 1250 331478570 331478603
    0x30a11061314030606090c0f07080c060403031b09180f0b1f0e0a031a060418080705120f03190207020d06020c070f1409181e010b030705011704 63
    0x74181c40c00e0380100c0044118105211841c142840601d610070022074030707000c5071b00d0943c00c07146542c0100d04002d1010200880e402040000441c1143c00c40c403810307000c807035852405140050140100802001c018107003030a58102e00360055403048280e400a600d811070180c0a8040c400080240e080081ca6560320b41110805503182c418402c4c1d114195004004100d048000024203030200042c1c10600829000d07504002140c003004540d0206061007404001e140c894a0004001d08034840c81c084480c1070050540c010400c14000415070b243c410b9080e20442ca00031200075046000e50507064100c0700d0100005003502000c001d00100154400320010304182e010380229192110854040700d600358001510600300004002881c024040b0300c4440d41c285003805035042d4201c90744400c0d14058110b4a0104035030501140d2028401c94507203040310b40c40d25040300c1941481c11030910620a03946040310114150401150140580e401a1100301d48103400a20000d001c5030002d0042c0c0340c14450742c05004 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 331481070 1250 331479820 331479847
    0x30606020f0709051e011e050609060d020a1101181b030f03050c0a080f1c05071b0f06110a080f040b0103030809032214010503010f0311060d38030a1106 67
    0x34041d182c2c003540c600c03589440e8664421f00d164203402480c403418050015042943d2010102e41a1000b52000940c440040100c01d071800c00002c0038030000d550074107003c544a03c01d29411b92281078007609070903050004518000c00548014000a0032142691300d83c80082401580101403c400361011908194900d440382180b9800111013600829000140f410b00501a0a03a028440030350100400890402000c003609900c203620418413003d0408600070207001e107032072051030300380d402840500142507031400388091035029403260b40c00706003a180403c0c560641d0148691003158083c0f005841642151810307200303414000c0c600c80580c0700400c903800c9800401005400050b001040d80c0100318100074101030300c640400c0b01c10f0f04200b020310040001d04540d420000489820100314003a00309940c010800398030400100501c0c181c10403802c103440c02400300c030680a2030501038460018034011502c6410b40c2d1f4464044d06e515a00035145200802c005517060640288010a1140782103416001c05 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 331482320 1250 331481070 331481131
    0x180f120215070305060f011d09060402070204020f03062e0e06070609050601030c0816210c0e0603010609050402030c010f0201150608090607020303060607080c0c04060b0703030606020f070905 84
    0xb800240c9840c14800c6a0510840c450020345003400c051508100a5185204200c18054403520650340000402c4043e101e650485a40d43d8025000f0340d81c81040300e208801c1c9600c03d488281c01350210584500300000d841014a1207098036050f0b105003400303d594201c40d4029100140350344240704000c10710018400707105880303004cc03040c0b01419580d0b246050204101c1c425510194642c0c21103191510f020740b45606410940d43c0741025104003805001044009141d12240241071094003a4089480c02c418102c1d98406e001c210002d0160320b4490041c041660002d80c2c0003501648690a0354a046d801103480e803241c09224030000904000b854000e01d21129907a01c0040460362640c180180c551040c004c066100000f03000442c59420b003a400728020384138070013001d8031041c000b1603400801072050182ca80d0b042c074010014001192030f201000c07800d0f403100401300c1c003180c13a020340052018000f180840316169042e003e850b40328a80074045c00030f0280100075050158180c2d0030051041490840c5 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 331483570 1250 331482320 331482331
    0x303060b1602011403060a030b0901060b03010f090f020708030609041103190203010b0f010e0d080409050403030c0f0c0213020702060906030907030506011202060403140f010f0c03180f120215 84
    0x7000e002104900000d005080541c100035940c00701042001705940720f020070305048039400410560280d840c000401d0040234181c01200d209807000000059049610400c08240d640801c400c000e200741c001450002c07445000c0740101004001e1000071468603182c03180ca540580a07840c00003410b03003444002402c05800d407070303002d9090307000f03818450075404c0074426994a00019101c1070b0b07212001da80041c208140150340548103001c08400071041000300d0003a10001c00300e41c10280141e0a080c41c014015200c0302d0340c1500060700f4441c5002c2540d1241c100e45042d160041c2c0785525058414000c40065401444181d0300030800b0400088e00740c03541c0d00114820006480038041643c00d41c070345141052010303032103c8041071000c001e400140e52134408a078100c035801001d41c4401c220442083d400c100d224401e59000d5407070210005452580340d002400344000f25602040340301d000302e4010302041501e03000981245110b11150380000d0ba00b241c1e0b038080300400e00499200c500c0485030700b46d4240c41220b1 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 331484820 1250 331483570 331483597
    0x81522050a0f090506060d08040f03050a1202030a0e10020a0804030b090d02030421020114070b0106090b0a05070602090f0a08030c0606041802040902011125091103040303090303060b 80
    0x1008040700540c8125000085602001d10503d1a5134444a9079940090400c0d4030035038241200f0000c20110000700c90040c59807600c2401419640d040940c1c441e5441c900c2610075225090101c40c4561010088035203101b003944440102c1c490074000d0042e070040541c0000254456015000c010880365070140c0000c51040600c45800c2c40d00d55070440c10011807031900c3c029580305100030b000c141d10f01c0d1034400c0c4800c00210000d4411506e80012101400030204001c26840000760300d40600041150060590704ea988603503420b13a03540c00d45a040351150032101030014806008504c0043c00f6500100072940004280c485066840400a0750302c4541c0e0b40029101d80c000a200b101d0100107110b0700354070480c121390402c8a00304544140386070580e0000028030669075150aa400c6a010f401070030303050034040c01100e42840150095410f6502d2803158035840d0040f00000003004944c40c000c502107044003e4130542551202c3e501500502400c0d003044082c1a101c00021441c51035081c05040c02d10003000 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 331486070 1250 331484820 331484831
    0xe0f19060b04030501150806131a011503050906011401141b0a0606060c03140a0c06020d090b1303210902041503110a03021f020a06051f0803030106081522 68
    0x5440c5084031110b1b5502c9841c9089002d04000320366012450a5104000c050b0802c1001c400c0c1c80c1040100d11380410940000c0410400130400c0c1d000c0c0c4205040340c503d941c6003000307981c403014101582c51000b445034084540940c4404000765200b200402421a00c40c60010309000507040c01c0c14862240011031407841e400020498140011401010002e00c014104403495003c1514002c18003010520381c0d16a42800051818181c1e01c9548449140d98001c8000c42d128001c20030180044d00c400e0b10103803135103545403010401501c1d04003081010075030b141e2502c4c6148140814800750b50000d0f41e183c40451952180d442026071614040c50f44821120120308028034252b16044551000c1c2d0450f190046030301240074001612400c804925046a100110140c88a0010304900c4c02c10404002005a400c200603c802001c5c41160219a50b214000c803420341074a80759030583e280000d108010024414038003080040e62080307a0802100b00c050048010034180f00e5a8040340e40c4441045881c2540e00e0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 331487320 1250 331486070 331486073
    0x10207020d12020d0315090207020d020405010306020c1b1003230a05041205030702071806210c050d1109071209050714060c0c040515030d020106031703010e0f19060b0403 75
    0x44c04001000030b90703400c04000045c800d8840035501080d5005c0c44099590001c0c8520640d44d807401c3ea40d1407564010b01c207009941e12843c0040185d00031018203410b0344140079104e82542c0210a62400008002e0401c02c140803202c0700071006000c000801e410801040c2c680a08460544100540310303200c44040800c5604040c94a6003940d41c0000444017001001d00502450a07800303c5c504007150f2218504160758460100900020002ca80c44204031081070790510032100b0344c00036504107041c001c161203401556500240a0400f00c3c41c140103108228a1000448518000f00c042e50426440c2c64442c3c0c0200c00318086030300721100f044040e141c83e4010001000104181d0100a07640c0c20107131490f5080c1182180801c1c1d071080c1d40718401d4032494170360700003600311f64250102c400c400300c0040c02c640c2589080b0202074000c081078081600c50b0806840c0030360802c2c52801c2220304071080c100c103503d107a94541070503440c2c1c03080182c103243c8101502400d00040400c00e01988025000d6009020f940d00c1c81d5 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 331488570 1250 331487320 331487323
    0x402040e0f030c16050105092103070318081f02031504050a20040602031e2a2e090303113007021f06090204090c08150906040e010207020d1202 63
    0x150410f508151342c10900902840e607220741513a40c440420f44440c4040c0c40020004194001d03460b600c101c240c40041408010305a0125000041320f500400c11029152640d20050f142e100203440406540d4070f1007904010303011321398021a4416020a104004010501c00040660f00103840b00e9545985074130b80d25020b804c1402c0c0301502d01c460901c01038a424a03012001e5142d02443e603900d0700042c03500c00300005001d400c1d000c4070440050801d107102c1c0d0407025911f04000f400008209a41d0f403292140100004042c184c0c40f5078115860511710800f150416810310140407c900704a041545400c00740503031508034405040003030601e954207090709080f016504161000c101c000840c0038a4a42804919034003c50040746503160807008541101305601448040d051507070140d62400e00c00a400079a8074010f600c034180d500203d03610b103002604e98179942c0c08568154035016522400c50b01c0031606070724056202d80d0001040c50005401e0080640000d0040003008001751400b0505d80e00c0e0050f100d90 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 331489820 1250 331488570 331488583
    0x10050414060f04030e06090d0f05010212010608040c170a061401090b010201050c04121b1508070c050c04021e0304050304052106010b0d0603200f04020711090402040e0f030c 76
    0x614010b410940c030301a14020000c0d020424494012140058401d045441d91280c0d0760b407968021860811080705803500a00035440009801c0e0000c84003800498520b104000710340c007541c0c0081c5a2243d1608002c241d40404c19980108030203032040c3ca01e20070004202c0e014040386044102c900c455a989000c0344901500c05c001551411039140c0010407003400703141401e40c1d00350b86030541c0400301032115252084840e103011180c80b0503040c5400c03000031043d0944040040350307803880d039441e00143c91b8264243d0300c018244034010800d0b0803a0141c4101ca0070f143d8080d009041003007902620458848000c0c090f140c1c015502500e0a03000041c086c0041d0401c10140c000c108a02e4158003c0c2c0c1010600c280d841c0d0a042c09052501a40050004203034040740e00020b02543d0410840054a881c3c403501c1c3c200d65550618883c001c1101c000000d400703181c04e00c2580c114540142c480c401c0c5908400c10000040d1009000b240c1c05940c0744c0100d21008800c01203540842401ea0095541e01e58581c115880d268 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 331491070 1250 331489820 331489831
    0x1305040c1d0604120f030c0b040b04051e211309020904142716060e010e03010c050f0d0905070e040b0a18080a110d05070219060e121005041406 63
    0x102d00300000c100c90010040b000c046284c004840300c0d9075010500d07003250380b01480c60002c1c1980344003105110900c41c610000d070313015510850444031200d12809403e0480382c0f8480c9568a181c1055a601814841403540c014112100156162404a1000180140c0400c0760070964505a001c1031140050416100c1d100e070024550344c2d40d1209140c0019403140d000c10044407080d440d1403081c03030410b00540400c0204080069080c80503d45038603600024200d504403843c4500092100d20310075400d040600c01c900c011b46080ea11185480aa50200d1200d58480e102c0311102540d2810300b400811414030460000c2c1c0000550207a2900b1705007030202041c02c01070101d243c018603203c40040b81000007002110a1079000722005d0b00e0301c518000c2601e01807615038211481c0d001301e0980340540b960040040103c40e2003254810140d400e45203807400c112206000300301c081203041d400a507151504540b40780c80803030100c041b01e03c210311405c46007090300c0007640c0880e2500760700309114203481e10031701410b036025 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 331492320 1250 331491070 331491079
    0x1a040e10051014040504090602120a050c16050c0d030e0316060203030a1122051809060f1003060608061603020313110d0c0b0901030b01020f030409021305040c1d 71
    0x5608200008006000786110a81401030f4060b21070351240046040d10000d0400030010014103c0394182800a0750050301c007130700c2501d09500010050201403085900450300d4401060074040e40324a40081d450011072b0a403036510407440100c0140d0b44070304844451038030aa8402d800d0300080024103150521135918286c600c07548600074410b02d07078000103881d48111141c1002c11005196804660544a460702c1203000000c0fa103559401207800135407460449400341c400c00500f00d06a6000d980c800416180380000e03800c6040130502c98441050125007201140304842e42041c4c4d00d42d0350900f20361580c2c0c400074041e089581080101050786140d140b462000703041c15032851034040500c0500c0d5130912401002c4c0703140d840320990340c0c3d00d81148641e00301d544010056229602c584026203e501312090301030000381040d401141a52004c107a0003100107031503008504190500c14080040c2d0080e1502e1601c0001c1c02500044d03c0e9100d01840704100310544610312180c90400f5181c1e00c2d00001e1100c0ca004 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 331493570 1250 331492320 331492351
    0x50301060b0c101d0a050a1b0302060301030809030c1002010504050c090f16090906030f02040f02040e01060507050a060c080f1f060e042004080f0601030b04060203101a040e 76
    0x1041e102040d4100191604200090211084148040300825448021500e07100e141185c0003080400520b83c03464038040c484808204650349420f000b44031103804000d4001c10140b0040000440341805490720707c0008094408100659010a801c04440d0807a000140c0d190401d1105002d802d001c60000d101d02a50300100720300c2c289800e2592044003420306080c4c1c00103a40580180c0303100d6002c0300003414513281c3c1407210079503030f081504080384000d00a81c401d910348001c1d01c2108519100f01d404030384030301030400312aa08c0c10500b62400d40280c0c5081c0d601c1d0084072504030005045101e2500b02400c9500c40d40203a01b404c60b84030046900081004070b10800100242d10560568020501102c405144c0400f81c1c00034a004240a0301c4a1403041982c41c0458410564149040c4082c1c0103644108003100c41041d030300f64070103030f80710028407002d00701d41d0145022402240310f680003140d0281d003034460740417840c0d0768854030a1120798958032107901c002d000c1000c0c0805031190101c3c07600010040080300d503 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 331494820 1250 331493570 331493587
    0x50f09041104020f3114030a06060602070e090102070308190b1305070f09030203120c1507020c120c060a030506060903070602010b100212030a050709120f0209071b0b0606040e10050301060b 83
    0x40d91014040c14003d40c441b440070300c00780e0b0b0301000700e40071441c0e1080003800300581d10035010756680740c3c50003030500d8415070400003024110140309032a50346400d41c5e81c2001303d483d00b40107100503070f50713003c01400140e844050703880a0740c507940d035a404c580c900e803c40011180f501010050020703002e40c5c60102000404602040540c1e0001010440580c00016840e52400580c3d05203240c00e0388506956501040b00f82040005a004919a14860401d80300d142e13032012920b6485444154100341c113903102c0c10601c004101d0034400c0c0c0c09560f102c3c8014040e00e02d000e4040d00028030b0480039074850b00050303440e00024032072170426065a001e0f200c03603800101004040d00751403400c039000090454004030361b03a50005a01030702c501030440081c00d52200c9508c407032a02e800c00c40c0e9100514a401e0f80035041c07400216400521900100401e43c1002500b81000039169440f40080c1034068400d9030320400521020070a110400b040e81c4c041d8940062003001c03103261005150a48040740c0c00102442e000788240309 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 331496070 1250 331494820 331494907
    0xa0e011107030b0c070c090603020a05090708130303060512010609060b0703080c180904030f0201290d02060d110d0f0905331906050406050f09041104020f 68
    0x640c0c2c3d0000010302a0355801c000c00000d8000c07120040e192210401e400124a43c107540420f003a6802500d102c290103886106100b1101415284140000e0a030300010b81341d0045a02c03010240352080c500441c64954410020703c00c81c3c036141d080c800d140d541c1c07041000100002e116103402451441001820300c00c5548000c2c1010000070f046000905000560001026000c8400c0c51240c80040c44851141001d00340109802c3d1081d00800c0558078044849480100701303410b41201502c1400b5038000d4215038401c0c09061924840c04a030403800502c0030749456405405841f21942d00100350940340c000480070300050364a03610301c2058582c40c10415802280000c030b0040800301c9225680600c200b0b00c02c14502101e20381c4083c0070365079404401480038640740011040d083e5410103c1c10300c005603d4208000858416104142d44031000102003181401e2031341c10154850700860003250024450f00204090368031404012004400000d052400a060349184c0c0d40343d40c1d101042040324440f52981c91 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 331497320 1250 331496070 331496083
    0x306051003091b03080307081e060f030a0602030106030e0c06090a0b07140a120e0405010b1e19050901020d0201020f0403020609040f0e061b0c0607050f1603050a0e0111 74
    0x30405403944081d5090010303045042c00d80c40c3d02020142015a0359041085c415007003034880700e0000301d600e070100c0c09003410030101054503514415200540e8030340408200c05000b601035440d8240c0105240c11001c03503144d20181d4001c00c0d1907140440e5150744000702c60b080000c10a00725101d108107010071001c5403a0071240c43c050b40d07141c02504c0d44c1e9102e941071000601d162403140000070700ca0b0603900010410f50101040500c0364a48488010302204010801901e00c2402114002c58045c05090b03529060300c13400c030b44800000d400c180d05d4a42404030f60703c54101d8014803480030171000280900c42d960304102517a8002c82c584021804c1000756640d17003015110b1032001904c01d26006c1104403082c0c2d43d603800b4806d410100b000802c10f074907203a07440c1900c50b403044540021049940c0c00c0c5402801d40d10003101d4034011041c000d00015610b00c141a113043c1c001c00e80d42c03010b03110306101a0300800b100000c0720f50030601a842d02030f1580c0181d640101011481e1042c507040104082c0300c0d00d120200020749 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 331498570 1250 331497320 331497349
    0x10f09140d030210050108150109140c0a0504170a032703033b0f0f06090607030e09090313241218060605040b040c02150c0405040507080a0c030605 65
    0x1a070340c0c0100c41d080480c038201040b01078881c41c61030440002441c500008407401c54150035640090390340c8c3d8801c5d0410445040b0a0464860030700c010014400d506044000c0080603090305260b0f0605440d40206d9445070803180d81480194040801c40c000e05400071402401000844062240d07800400781090311622030344401000c1c0174002c0c408884046601c03c203481450244404c1d03151880f000c842e20100c000492107810b02403205603049050b0340c18400d0103040c04002c0548424600703044082400895405464240c08000085a40310901c0d551403044500030812080110703281c0c0604802d0b202c01e402c0706d5109071035115106484000541700319114068030030701410507408081110030400050903400b0f0030128103500101000040020355406081079071000c2d01e040064074a4982844200c9035004021009640b01940200b0340001d200e028651240c5070307207031480c02c050382c801c003180654606503104408a207800c6c4c1002450351440c8503820000d041c2c2d01e02407001c10700d00000710303800f030400303400 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 331499820 1250 331498570 331498579
    0xf09020102122802010c0e09090a0803040c050a0308120106090608010e04110a080d0311121f21120801030804090209040b061201030201090b07050c130e0601080705010f0914 76
    0x1032415500c2642c51a02c000d40e503d00e640e01d6140440d800000b40201700085003032001c144c0807440d41c0d40e54101410154072428030840100401140340d01c0d5045581c10042c02250720304580740b17001c03c0366103071181c030a401181324a80c1c0a4503402d44208070804400d0581140c3c0400c60300356070030054203501c03600c0f0904407119141031075121b49907820700100b140c0c4820822a0400303541e01c00001c04e07103800a50305000080d15941001480080340903045c25200d0481280d000c104210701103070781c000c04014014030500f02138914a4580c0c3d60fa0680c6c401e4045e01e1280d01d038004011108903824045a004e06040440d05032801030010360640c0d49104071802180507074800190b001c00d0707d03000e64031903502c020030b081c000030b0060303842d41c8030032131186072650007400101c6c0001c00d03482001590014400030340c0d0b0700c1540480980122200c0750b040c0b101550b1098103040104d611080b402a10407414004030b03010301402800b4264082c01d101c00075011140c4900601d041080020040003d03804114102082160480c0c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 331501070 1250 331499820 331499827
    0xd1d090a052203050901021501050607110a1a030f060603070816021608070602160b07060504030306120c091113090b060408070b04061206030816081b030403060f0902010212 76
    0x8030166001104802c28802c04980803003414150494090000d10300b09900302ea9500c410022411012071003889000d40002d800e00040b0b000482d42c40a540480001910707100c00c1d6544c0319900140c1220f112202c41e0705d0080002030000100c1a4400709a0001d000d0715000e05c1c0d0308003094000c0c50080020180b98a07502c020050003900c2e8802e0104810f000c0314076505103420b0352176842158540f15944075480140c8079001d0044100d131601020181141c89190243d070605510f40c40b00d101030040104210101030ba05c0e00e011980ba410711031000c2d4140c3c01750b029804681d0500417030300304440505c00c80c00c2042e1410300c00540e10212071500001510031603a4007203003281c01c10f00800e8041c011500b0520583c010108003083e00b424400142003292425a9201d034000101600e02c000c07900e8900008d41040030030802c0d146000c0c0c4103001003a12034450043e903454800082c20038015111080401c0c0090b41000074100180300b120300442d01d00034407660f010003000780c00794000b03552181003111884d61140c020 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 331502320 1250 331501070 331501081
    0x6150f0403150b012007080307200d05100e030f0f07060e010b06160609080f030a05160c0308060a03120905030c040506030c0919020406090302010206161409041b020d1d090a05 77
    0x900c0880300a00e0218216030700e81909e0b00d800b04551070361788010200340c0000618000c880c9081c090944a1503004809800301181416120010307060100d2060404d210400ca007807054000200180a680c0d40c80807850b489a080d4507100c82941c03a501340a2840360f051941c4c000003641e42100320f0f40c00d440010340c03041c01d804c0d030b80c0340c44405441210310142424030003085140c28401f601e40110300c03605038903408024554892030103400c1d203003043c99080300061070108600b0000340160320203500104014107507054030790390b6902c101c0c4038030103401d24100042001001304820b0800304901410014115030038082072610401103035549080c010094800d2540c070001c030744050304981280307070300881000043d56520348070600a841d0442c5880101d00600c6940001030784060551800c07919858282c1d514500d000c80c16005a03081d422000d880d55000d0b40d980e10b112441d80741e85480c01184629500070b4030811281040140085005412182c1c080f00c00008c09409a640e0820141c0d104182c01d0000950b42c584 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 331503570 1250 331502320 331502323
    0x30601050d060b040306061e080a0803130f080408070503120f13031e0b010909020d0201030b060c0105041a1006020c010810080307030c1205070507050906150f0403150b0120 76
    0x654003d0000b00c0d000180441449919048035069a440d284880340f03500810903d14240046480341000303641006010030002840140190b070811010f5480751341802e0562506901261040d40072a03a0704400031b004c101c014420302003200101811006403a0700c590000c5032000381d00c51104500c000210001395007808152000a007000b6540040240d8418202142c0308848519110b10942e220031041c07000003030800e624080c115006502405800c4040001d90041d409810794100c001c0e0702090a0000000c0c2c88424860140305a00070710035544c03001d8087c1101d40302078201a14421039040c0c1c1d02007d2042c0368000482880c1c6240030700c0c250f10709030340390b41d052200c3c03620a0b00809200d00001032010145540f2034048501140200880340005c00018003d403610b102d01b2000411a4001e40d00c100301c0c500d01048c2d540d500040142c2154900725014500680e41e601c0040d4a11403104081414401c1c03020050010202104000342040800b010074000b800180c070304198480341c4400380b410000712410 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 331504820 1250 331503570 331503581
    0x30301090c1110060e0606070201051c021e070b0907030305040308091c08090103061e030b0411042c01060b0d0207140d0207090b041103070c050c0915090f060105030601050d 76
    0x21014142c2d40c603000941c0800b80580300d2449281890f0413191701140003498540211041d01d036050b102c032031610f002c002d004020035688e00382051500d130b4240003044282d080840b200c0c20f00d218480d85641e682181e0301c4c260514140180116280350b0003c041440004d80000484003500d411150442e140c0f5605e1000400c01c054901400d124041e000000b5010801490060019504d0988082c80724645515200c90000801d41c0c2001c803c0415a10030000b00300c0351290030760058000c001501400c450b0502050584502034500890301c01d807030040241d0010513031241c507020000400244031a600c1c0204841050107010b02c03c401c4a640000c0c1002004030b5950300310208081281903038144240c040002e500c400c0300b031240100483c1019400e54031481d141c401ca580e0400b00000c0242181ca6810703040758043e050700c00860b050b11800380c80d00901d40c2c3e884076480c880e00c2070582c900002c0081b032090041c3c030040a0003048030b45002e4414864180e0f0000143c0707a1040c821700e0030589484100b00d0241c040e00 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 331506070 1250 331504820 331504847
    0x31014010b1608161e050d030b01050a0f030f050c070c06020105040302030a080612070906090e0c30011401060e030d0905090a02120a022a1209130f0f06060e03030301090c 75
    0x2174640038040109084250301846181c040c0003030f515000341c407440983c140c03501c4403201800100200901400103029501c3e000d03c00c2030610700018401c2400e101c0c0320459005860305070348035002090078020042846000406425244003c3c005800e2590b0084c0d42d038003c507030a01081c4540c1c0070018145840d00801682030300021401c44407455a50410304005220754003d20040c9820700032290444500051116640c12003d44981c0300160b00c00b14116406a40742c400c2e4200000440150080e844240105041400c1c4805001c505515224000d001c000c41d0b04125802504001c1130504080e03007003100442254800d0b21215650703620003100b00000e108081a2100040c991814043e0504d05a07020301380913006e0048084600c0c0c7c1140c00c1c0300d102d0807143c10f242d015503c440d891039522441000130b048103590148c075003030851602030038074400d5030581094096043c2c0d03035001e1140322000501651000740303100e007012448020380101007902c80c401409a01c8000307841c3c44100c46258400c401282070701 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 331507320 1250 331506070 331506083
    0x70213050f0402010e01020c28030212150601031a010806060f07031d090103081e070f11041406180408090405190e010c1e030b031014010b160816 64
    0x145494086100300700740a881c1640001d0911030281c482c0d50002031900200e4400501c800703560328410303640840912004134042865100b0410000040c1c6030b086001c01401c4000c000340c0041d00b040d90713075800040300080c000ca04050406034008a1640382c3c1c5e115003180d49003071921130040e50b91000402d20078440c83c4101c0d034085800168110034940d01c007090080340394440c1e0fa0b50400064500402c081440c080c00040c01d100410401440e1010703040c51198516000c450000741818071603100c4402169501c0c0e400d4a00c0f1000740c50070126884d1602c84c0000b030411040560b1a981032590114149442016002c040d1205007000702d818480207401f9142c00b0700c0d004105000c1c2c1c0c84c1c562118000f50244454040201d0b00705000001229018081c114801007195108001c0c1d0307140d01c06d2215059842d800410515544101c01c40082d1818844005180c4880700046a9800c8450114502d64016800b00900a40c06d200c4030750707030418074640414102d0b00040096291000d480e00038100b030b603c90170000e025 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 331508570 1250 331507320 331507331
    0x30c071e0b150f060903070e0702070803040905010801050a0e0c040b0409050307030e100804050a0b2a031b031006030915020c0a02010305130309090c030b030a0f050f030f03060402070213 82
    0x8a00e282c0e880d64442010740c0c3c0486a007030203c06102003030049109140e4140c011800c00d0069044219505074800d0103403040310301c81d680d180d034260b055910075000030040e562600700501051000b401946e8129050708010885031010301e02c2c1a0b122000d07040000d2107143c40780e4891019546e5904034852058000d02602e903251190314010f00055906100c0c0790048105121039611a40a40c210034440c58002000d800904441d598203c99400d0040c0400310b08140b460351003007030b820903907500598441500380c602d51740d007401910310900c400a0ba2284c002e0300f40c03c008011103440704044c01c0b0100c4000741400f10701d0520500d007207002000700d000845ca03480e10200740921002070004007140628000e880c10085038071020380352000d07003050a10203000700307221242c10410000e0b154410380318440c107883e002580a0005d8002414405999415075a000d4880c102c00305020302440b216000801c0440214544402a103c80710309000042c07110b44191342c045002002d5480d0b48800740048500c5c04070803c607 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 331509820 1250 331508570 331508581
    0x10c2a09050a15030503091302160309051302041a0309030f1204111f0804060605120307120905100c020105090a0902030a0606020706021b030712030507050d0302030c071e0b 76
    0x1e00040700e252100c14101207a00c0702a8108a481c10f050302d401c079014620340300d20541480140d20304880f003090000c3d03080180c141001c460107030024200741710340d6032509084d10b448200f0042d08070180b400c0742c1240c8100310800000032403900b82494031000006540d22660340945150840c05000c82d540c420700800103036211041000c242c024400ca1041c21345007501c0320f100041c01814000d4507159500040d000b0100b90285020703048182e0701ca44600e4000c241c849c5c591780894031089455206030800d51000c6003004c00c0002ca55440b0310203440d41d180112010745484000b40c0d035041c0c80c0109406204007000b8141c191b91080c2e0450344048400350110052999070340b407110089d03000312079070040b0714a844c2000c0b42d050300c0881c4400450308641d0051000020000c0042075a001420407198035200302d940000341e1500004c4400d10701c82c002c1e00c0301501d81c6441c2c2411401c1548000348202090700c1003041028038031008066540f03c6401c207900e5030740f03005080c180b5814808000c4014214a006004001 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 331511070 1250 331509820 331509839
    0x10051f0207080a0b01120f050d0207030302060a051302090a06030c0605040303110d05032805040f03091a03070309110904060204050f040b09150120070f1202010c2a 72
    0x110010a80c0e401c0381c0c401542e036031070a6216241000010005810300d001001542d03441c031014418a07000c0e454150311421690f44041c90701079540b21031070148e00144c004009254052103025400704404800348017900c1c100d40b4202d440c0305c508000034491004900801c9001e502580300d00f011315408807014110984504000d403481d040b611044000030000c0810400002c0c3c040b560410740c60b0b442d20f03a01d085d07866071441c00c01101030004880a0800034041141a00e020754007a16004a00840d200d1700d2204007410001d20508141d04096100d03503903030b90560a2120180201c0ea4001ca01d46000543d050a03441c2c803801c4100d00d000030580c8115484140001d220b804c0d03005000b243c104680849a604800040c070054a04081145074802d814400040c00402d100e0490f1145a030145001001000020900c40503000c25603008601c035440700205103c0000000042c4010300313424101e07100781c0c04440c0d00080c205100500001c0500b9921f4081801c0e0110b4400005460444081d0200c9110345480310720 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 331512320 1250 331511070 331511119
    0x807050c0a061d0402030c09090c0a090b030f01091112040c050406080f03191b0f05010501090b0609010e0a15080a05070503060a150507080d021e0a05121005 69
    0x52050721004400100140910181001c0f40c100007501d440e9220080c007004020b400c02090501460001c121061680d0b441200080c411015014100d0300ea9120a400501940c041d8001d0501c0310010030600440038a85c01c00d8504440803441c01107440010403440784902e0040e14801201034100c00244010444031307010940c19503a00b62070802c2815500c0f0184c690301c81d1400552003881c4c20030000c0b0766203c54000389214120903d41040e40c0c58111601a2013200821076105660b0410144028400c0160a00a26005186010b0240300141070303100000d505c1e10070350301031505108503e14001c10f551240c0318031038010b01841c00741a003000318540c00907011001c2102c05050180c03a2800082095004006a81c064480a0401124181005641201951801915010708c0024002100005c046070010009485040303800341c0c071100c429400125811100b820a007c0c1e11080c00049a841d60040a41c2d10120a5980c038103840d0302c404076100700100580d00300e07540054032500345040e0000c616148 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 331513570 1250 331512320 331512343
    0x909051503010c032016080406021b010206010f180e0303011e0e100e070210020304080c010e070b0f130305030705060105150405030d0e130606020708191518080705 72
    0xd001d011201001141101c9a0b00211025050742e00c1840c8108040340026055042a8504454201045454a0507c0c1c1c1199128100580c0140034482c001661005d100a1686080c00113203900c0d4144004030181008601504848052880584102d95203e8000d2248044002d00380c17030345c030358480b1039030040c45080709148541b002e00110002030140d05038481782c0c800c400f805400114941448100c1c0c80d0040041c00490851090b44d4440303d01e040c90f8401140907511031180b060396003c15001d40d40c01c3d0b41440b50300e1400c035040b00c0d40800c10007a8203021a0103588403100f0741070780c500c1024070b022094400c40c0c0014200b0310003c83c078402000000242241a80c03401c580c0c0a0000c0d0546070f28109520a038010f0540542040c0e5080359081e0150300d2820382030320000c0221405100258140c4215503032540f01c440160310440d01004031a6051045c9243d12390403090058591000752584125183c400d210b000500e5030f107940c104880000060249095644000410790300c80480c2000e656a03074007a00e0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 331514820 1250 331513570 331513573
    0x1404091b060e0a08070e0a02070f050d020304030c060318060c020a1502070b09030a0212280804110307030809090a091e120c02010804020f03120a0215010609030317070909051503 78
    0x484c400500084030303070031180c0000001040b84c2d2075003103500280d009a001140c20f01500c60f000d2001940074800c81d21038500c01da008644461079410000c409041030b5008905062504604c16004075150100c2000c1c142c1100d03000c200000c1c0040c04a26040205001a00114a003011840f45501503001002c41c0d50160303800c0c1115071150102d06460348105401c0034090b9101c0f14040910b000c401c0003405120808032403802c11032005091150f40000d1703046a800002d03002e401048108064505a00030b000410b40080080c241103a41e80503440c0300c0c194400c0e2286150200150142c1d03c65080b02c034400c0e90011070104d51070128a01410b40c8420380078111074901604901003541445940300042403030b0140d48141030342c0c075203400380201c1c15020518079416000d14503c0ca8140201000207042c20221a4010402c03030507004040c80c491807068102e8010040520010804a984510000c4510a113000541c034241c982030010303200c0407105c0e803041d550142460f0401c04101c4010f10b00408040042d030 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 331516070 1250 331514820 331514839
    0x905030604301206050307050d06091505090c011205010f03030c110a06110606040b0603010b0d091b06081303020a030f030603062d0b030706050c030c060411030f0303011404091b060e 80
    0x40580f00e503900d001d02502700704c0c0314455201107602e641046910502800c83d8404802e0040b003040e00b69001212807140030390068440c2145035034090183e0080181144040007194180900c220150009204c040d003003145803076101c01884115112108140d100502c0c0300b40c40c2e80d403600c02a0000c1c0e400010400180034250009000d810700e8002c0101d4030000602c1180756030300700003030620305030440c03860026010380d51207503140000c040044203180e1000082c8080391440c0340013002005160001d1003e0303001c60070102000002900044c0119100368141000c407003094040340c044005155560003e4407060605411600005080301b600b240114481a0b480700100003040c1e08054407031110743c06806501200b403c10009100b0005010808412000e507817901c041c440425250000a440941e1304d0411500610007510b8100405004184050b024504541c5490001c03008103160005660060752264603190404c801445444107101c010601c2c881865107421000f42020a01701005000d10100f0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 331517320 1250 331516070 331516079
    0xd060f051815130209030d050d1104030b04020d021504030818010206060a0b1614061e0c0307030c05070b1e01050609130207020103090f06021206010905030604301206 73
    0x700c03069104121910b000d1103440d03406800c0c0f201c481c00005890040540c240615120360b5024080d102013803620f9070707803a030b100c4001c50280000c8600e403112450f00300c141084204001180642403a51040d0110354000d1006130b1400418108080c5030400c0c03406010004001c0304001d61240601001c14103408010345406404006984d120001c1e50466481000340a04028440c0848001c00031201c0e0b1a86080c42d00b5280d544502046400910680840c0c20210401521380308940b0007100005046500e40101d0411056039600c601c0040e01c140d04042d00c40310251122405641180d030031a502c143c2d04142c030b01e0490756210303a5106000340208015010700c000542403800c001520030084006103c0703491854210101402984090300c201d06060711120b4041c00303d2120a00714080034011031000d071b60342c090481e10580c042c0c001000300d03040c45018030051019841c00151194402c2e4884400d950500e2004030769182c58003c20720100da68004010f043c000c00358800301100701500d0644040c0801ca0702d0303 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 331518570 1250 331517320 331517359
    0x9030a051c09030510050903190c1103060c1204030c20030d1e0503180f06070e240904090804060f0806040c2a05120306120c060406050903030d060f05 66
    0x70f031002a02903031288180781d41240581d801a500301c0110341c101c9161621206402d200d002c00701c5101e1000c9030606072303103074180682c40500c3c0c0c5040030b00318050881ca15100501e000d0300e00900390502451300980c0c002404160058440000c0182c100e44644908000004500750030064911054000c2c0940d10800c1c07001405103654603000b01d0140d100280140c0c0c26a001c5800e038200130301c5a41090040211800c0462040c005003403801410005031402d81f80454000d4000540130030725900918038020840e100d5500ca07258014424461104641e42e40160300000e000350032642000390001d1000a40020305580000c1000c12941954030703044900e0b650141008201c4080e8080318011800c1c002030301d0355914880c496001c80041d240024030200e581e80c0c03589031900d60010710860040100105000b82e602e0010080c580102c142001000289004000304d09540902c1c491482071100200b01000d00c1c0c0d6042c01650b00c280007841e000c20045580741002d4407000c80c40d100e95801600030040480a010f207 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 331519820 1250 331518570 331518587
    0x62c131d0708030f0904230906010e0601020703030c030507140c01030c0201051603050702031e0d0501270b0604030227070c0b0106081003050d080403020c0d11040203090309030a051c 80
    0x141002d582400001c03100072045500c40035480754000c2e5071303079003c0d2800c80002c0b04140007c41c40e030a0301c913440d1429040d110320301030040e0817540c00616428100f240c1caa03400120310341034a0303162419500c00b00307061500f544c041c00f170f404004142c0000080b42c120344010014801280c044240d0b0140300312445214240c1c2244e409480b081210014007010f40c803214002d8020907040f9403507104a03450b1071031024030541c1c1124a4074008116240000e0003400303014960080c0340c05065280212051404802c4851a282c8240110259026280e030108a500d503600820340d4000e5801404a202c003151070080006180f1a00c0620a0907040c01c0002c00d480394802d280d092070407039000c100c1850503424841c0a640c0804018904000003003000b034003000040c41403180784c80c13411040e100c10b001410549000703820004140c0340c0301c2c01a00c0c02c3c00c00102003034101c0e2034512615000d8400503503035229215002d0652054411f11501071103000c6092007041030015040140311003203420080c0301d5600450807102c03440d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 331521070 1250 331519820 331519829
    0x40303050a3c09030308060f0111100902040b09090a060e100207080306130b1005030603012c0d1119020d0210080106110703031413050a0609090e0601062c131d07 71
    0x1d22100000d00c1f141000700e40251b40b0141410075540450100f418585072620703041307419103242c2d1103403595801c608060241c40301800341100e400407207113080742c9031540c6d03840003a0001d8400350b161004071024000900800d40801c0f4410030965070396100c0d061280c0e1a130b00559456004002a80a07060340030064440e04209000c02803285582c5000d0b00400c035400e03080a01055415507a946007040c07119403980e03000e2031028040c0d0449202510026916080000c541102418002605142194808007050208103451300640e00340c500010b5002150312100d000900a4009884551004500d600014003d048800d02e944000020304102031054984402d880005c0c041551807868900c6c41025102600e07035451083c0c0030703904040d541c100007294040d080d44940081405200107100100d40c41c05064000c08070038000340341c507514003080141755200e00100144101c1c0701084c4000c440e070741c0c407a01000c00b0340f000300b500e20080d002c1a0358400400410504c2c3c00318000d41070708003042e0320011036150103e6 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 331522320 1250 331521070 331521077
    0x40b1201080a03090501050d2706181e11090a0501051f0c020d1506240c050c0108090307060c02010b040c0206060d110307090e0f0105060114040303050a3c090303 71
    0x4c03450b01006660b0358001c600046a22500d95036046120680c403400104484002008585260080e08103c1c0480301c6103c40c0d0220010001c00f02c6002c1206c807060301d41090030880c1d40c0307044003c0c1400c203400d104600140090b4000300c907500380b00c9605074582086068038400c5500f018401d040c200c5620560032950846004241d941c104100503281c100301c0e140c55140a40e01d52050f0b0781918045030b0445083d50410364461030005104c44038000400404c0c42850f030641400245406135844140c1d9411303500f44007904000340000003a218100510a490380d4035880501070200004031030029020380f01d940c0340035004034a410450401c2902c0003d107203000c0d150103844515008602d40b0385600641464a881d5010f200c0c41200064610301e0b40701d805003951680b009404200e820500b10760075035201505c1c0038100b08000c5000014410554101c0b000ca03613044c2070082c2e5036810764900b603c143e1003424111130640140c84003401020340d1a01980e2010080e2844c0900044041e070055490080500000d03000 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 331523570 1250 331522320 331522337
    0x6270306070f0813050a0c0e011a09150f120714040e070c02041b02031b03040315181205130605030702120906071b0f080c0904110411040b1201080a03 66
    0x4943c05800e02680000496000c1828002c031a12110b1502012403400c4501800c1c0070300801484162600181c003402d4000440b04a281d42a901986140501049944603000100c050828105820201c420341400f035404643c0703030600702246500c0d040d01211440e000c03030a000d207c420541c1075642110261081c0081100843e12850000c65600500e02d000700d80166486401018a11601c45408010392a0b07a004503a81c6e881010701c01c4c603980c4002400019030340180030038400568100c2e096600108071440000d03844c041d03502600d403141c44034030000d04001940b0301c84240c050f0b4010001c0841294107042c200c0141c2d03980804603841e06c07080314030400680088a0740120011600c0040c082100c004017214140703002900c801e00d20442d90030500e0010b050070841084180041440030009010b54000784c0388c0e250b50140450210b91707000700000c2503075043d1405000103654561042d6041103000c2c0e11281ca80e9202c640c10500b41e804480012100c009413800024502d8001803400c10455055461496 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 331524820 1250 331523570 331523597
    0xe010f210303150e0a0c09090b06091003141311010c020a12020d0611130b13060c050f10050a0b1c260a05210609160306050627030607 59
    0x41c030b2000d0540755080014200000d03404c0e88108130714050700507600c00044101b41c50f00c0140505441e90b11101e0b02e02d003022545001952001c041d18050842a079223040d008440c0c0000320001c02122964a01030490ad8013444480e18000d060700c001e41303200e1542c00d02d00145540045d00c0046240c01c0003135000c407001c4424070019032840800400c0c1072001e03041d144880c120f0754842090381c05444254200c2000802c0c01c109803946082d16900422170b000e60709140201c0700300080d0300382d0b029000d01e42c02d2040c118800b10810000300f000e00e0244c03d044c800d641403010b07403071511800b45c00141e13607281449041400380d10a6250007203562031826158901d6114201056850b000e45004000031038192048202c82000050003480090424000d5941c900346d40d042c1124014040c800100f40f8444944401310802c5000c0e200c2d035032481e40210141c0084e29403d201001d0441c00b600480d000b003030300031102040403a0070784000510b808250340f601007105a01480442415a10315003110300000151b05000300d81c2 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 331526070 1250 331524820 331524827
    0x60103140309090a0903020c12150c19020105010f0803161712010605040f2102010e060c0102070308010801181a042d0b070206010f0302060f0904060e010f2103 70
    0x6020080090a8905152810001800c403d0b411140b04409940f10410041003550600c02904100802c80751400c400d82440c0440d50741c0e80d000c0b0b480328400080800801c46100d01c0704d00340c0e4241c804481740204041c0900320003d010707101c01c1c030030041c5181440201150042c07010046d80c050300020004140200741503102e0281c00e010a059200001c90b080101d0150103041c1c0007150f0191040785c907019034651406112050394034560b0700402d040c0c182c3c0302da03103100c81070302c1c098071039140341c091810000c1c0c1c0d04524005546031280440001413513100040351810107030001c50950403102640000c004411140c29820ba541d10f208200074980f035a4924100ea0604401d500b223a0010301805120070311038808040700790720044115102130810008020302c002c116401c4521688084a0b101800143d4034003816180c842005010003481000003040c1c0012584a800030b580551000500c1842296a54038032050f0400081c0502c1702c09070212280850a0722080c2d1018440d001a064004442e99054a044 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 331527320 1250 331526070 331526093
    0x70e37150302250c140a1409060307080601090b1504030b01051c08030705070b1005010905130212040c05030d03020702060912011d1c110a0605090f0307062c060103 72
    0x903000d030100100f89040b6808a01599500d80e01c101c034044000e9042182d108103486000140500c22000c624043c4030f003034800305101075200425685c081182e140c00000071706020058001c1070907072244a000017090300160b08008140c11080e107141d0103443e44c0700040780c0c19108900000e407102c49403a004104505182d84680706a60315016840803622080d40c1e00c10403030b4825640c1c000045c10115021040c004201182504a044c04058a6481d4075080001e017080071984100b03407155540303086140c1750240303a0301116015130805414103020324051070f100d19403004900416000b4400d410003041481d01070310032500f03400d0f0020602c4e400c00360000d04210081800d01d0001c0761035502c4103245105030102500000038a400280500188510b1244030a5084200c050031020044494102c41c99030201040300da04140e0040f101144c244e4844544c03c3c0f42148521034807030b85d4800040d00d6010721100d9403202591544244064080e401c06a40d451140c0d0142003010300150410300040000a4074201c14 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 331528570 1250 331527320 331527337
    0x191d091509070b0f0405120a02030615030102071b1d13020f060c03031306110406050711010903120215010e01051012060902070f1505041a070e37150302 67
    0x2c0300d004944484072000c01d5080b10b60220141400810203102c280b41c450748050320f881b032001c02401500110340019130f80321400b0b030000d444403010f4003400607a40c400b03404131804107801138403003401503021f0120b00402042610820300411900001d80504e81c0201640070701505000783e50170f81c02c0c4210b400700200c01004840180c0d0103c410005e5072103000c42400074510942c20055603818668403401c012042d940c025100303000d130f0401044203118103134200c425a101c560701711803003000721160080140d54000040e0805400002e0891003018010b0340050200b00c889142c50403510603903650142504002d1081c0601644500d400b14802c0015108030740e950328240d401080807031a641d030b9140b0141240d010304416540d50548403402c606006001f0aa0b498030305a03500c00b003019192a4440510313082c101c90b01c00040001032004900001d100e1001d0580c0a6030044c81030108110300041d1700c0c10b02443c80391112a25150f0414000b0300c2c2e003400160390859807a040040d450941c0f07401c1c21402940031240 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 331529820 1250 331528570 331528573
    0xd0f0806041b0e150f071104090218040c060801120308250207080c190314030903240f070503070311040f06020a301d191d091509 57
    0xd408040c0828004008126640c0d00c40c0c0c05465200030a006102090000802d0340841c20403d001c9045c1081c403c60b0065500544040010105a4000750140402d0540650b0127015603038420380850007100f003140964490f00c05039018070303075424055482e01c13001d11440041a014001c000046030090303000607031100c0222070384030402c0240700f2446a4149807000d20740040e03000c1501800b007000208006e1041040494802c0315030341d0746003100e0f807403c201d601000388091000030340010710301c108005031145144018299000c0c4000d80000f20140c5200c140d1400c9071b802c0c0c0c1c2010581d40d4403541102c5018500596581e861036607580c20540140038504401007000d0410403000589400c0c1003028409440345171b01500c40a511424104a409041c08004050640031042001141849508008c02d0301c12810428800ca050030200481224500020754014070740c2529043c1c007206911102c3c05540703a544503142499203080d480501c402040310001220b601080c40d00504c20f043e42d2045502031100030 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 331531070 1250 331529820 331529831
    0x90f0807051c0215091002150a020c030706061d0109021204060b0f030307061506140403060c050714010c031a030a0611090607030f0e0607050d0f200c040e0d0f080604 73
    0x1400318810740281d645504802102017010348046c0b03003050101c0c1c0c081055100911f4551403030500c480c48204047c20b0400203945c005a0b65614078001d00c1600e003055004038081054556501204144484d042d07002c1008a072400000f20b0740c84814400d4610045000f04410102d96456980030028810901102c0d40039180c0d0701e00c800c46a90800050170030381d2050710080748041644a050707500c400c03660010802d2200d2418050345521400c030030f40301200d0300a0400708000c0d90b91182601c541c8038120740500550f8151004141040054001041500d82d5503020803c0009600206000d400498000c80d80754200c2e02c809030104030b1a400c10420f03500841c0704649006d88171000079a480d0302100d003c402040e200d078185030000d6000030391110014010780d01a80b030031105039151522041c07407424510a1004992441401e248680c3c0180c544035000103c02c5543c80c1c0d0b5100b210342e95849001c00303034481c504040c0d04101c21000480e04400340c240584a4450b0711b200a88242c0e01090001c0100b03030020b070790380c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 331532320 1250 331531070 331531073
    0x50a060e071203031a01020d021203041a070e090603030901050d0b0604120b010e1509190f020a02010204210f02090a0906060e0106020d08090303010501050c1608030307090f0807051c 80
    0x4011403600c83e1090f01c00080a031280d8110b00f03001e1003941681815504486c0c514016943c000c240102166180b214042cad5a980b1464040c00c3c4003904c4a4038101c0b400210308111803035410040340383d09a01d003290782080796941d01080680e00d01c80d030800b1500040046c0100b003480c46142d0003089400000802c1c1504068803912448907000031407500340c4007034005100400a41c65045144d03908400303402c01c1d2010b400c0c031040200b2481c660161004c2c00301c540400918600f04120f50003580f1040e0310050555460020b140c00a01039045400b0b035441910514503a07014041600c160342a210f580120070010242c05a002c00000d008002c000c900031307075103415082cbc0c00a030b40707480303540090001021302031141c0d414520700034174110b0303100e13001020720a861061201500d4000107880c1102d01c00d20300903680d0000300c0f0080b810703d200840d015800603200c20340851800c00c00302c00b5600c10308291752a0004540e0740c20700c8204c3d02d9007600c105040760b001400d041c400e904007403c42c02044c4041c01d94400620a0f42d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 331533570 1250 331532320 331532339
    0x20705040906290d1e02120d171302090402030a06020409050a05010b0a0c021908070305030c120a0e0103051b1201090b06090a15200606010207050d050a060e07 70
    0x450000b180e90070390380c003840843e00041d02c1070401d05600c007180e200e48140e84400482d00141140c0d0300501406020780d40c00c0c800140f1029409004e80e4050304002d0070181c0c40a003035a441d50498410000f0079100340340c400b0b20214902241d4811b90503500b8140307100f003003502404840b12001e402a6090f000d4078180d1400308000b070000b00010908100f0000301e41c40e21001010407100c06030481c000d501c0e400c11450201c076600a00110a00781c048a05011908a000710403400e101395030320a44103400307035060010030b10030080301601000c000d58013919081300d180400744e809485242418000701300243c1d070040f80d039442031307001ca0343c01005403d1640320048200091082500304610440641c2c5d0700e0030060204000758080c200b1103003016290305042c5024040000c0d1140c3c958000ca0000111540410036850300c20144c0303a61b03800ca40c1210500c0c07480d040030440d440343c0085a1190240c4160480018182070544200c1080c68020001e0080e81055541d03020180803000e03c2d040c1c00d8400c00c140070629288 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 331534820 1250 331533570 331533581
    0x100c030905210609030702180606030f180a0c141206012702071b0911090103090f0209090a0b0106021501061d04050a0c08060d231504030c020102010509070f05010f02070504 76
    0x25504c00075130b1611120320410824841c06540d200841b03010b0820b00415842c1e841c02e4070f4000c071340c8603031013249659849a000c0c0c0181410380448901e119000103582800180200741e000d844010609245411050080c44503000c611900c91405500110040002c909040c05911100784925040580e420600c0300d114145d030800c66041e5000005000394480c0800610100002840384a905000040406a0141741401010082c6c0c1c10705031038098000030480da03c44c100300203507801004a02a8108041d10940d195601141111600c0d0510300100700680001888a040320001c480e810481c1e090034011289124500c0001031808101c120049041d40c990241600c07075822181c0004800e042a80300401c6008050601c03805180190030385004107000e03400407500c2000d51b0010091100006907030a2401c1a0120400b8040034131350306101c1055405552000310310b000741e009100d943c54103018140c0b508101d00c03c0d942c144504440821440d4050400c1c06800e000754016600544c1d50f03100800c0c01e0300c4 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 331536070 1250 331534820 331534831
    0x17070306050d12020606031f0e160801020703110f060105042703050921060708100f08061e071709030f0d0b04060f03081c0204031202010506100c0309052106 69
    0x12004220000950b810010103a01400803401000d1840341001d2145404140d810721580d42a104c2203027107040402000440c10041180c0d158124440d6a50940c600075000800c044002030f55929620b082442c0005002c842e1072041005802c0c00e920f410200720040a00b0305961040440000040745542c05414001180900030384455a0742c510390707020811183c002c644422613040c14410654811440010400c3d4800c18504000c1c5151300c0b5198060704282040c0e000c01207001d5800000708981c40082982c03401080c43c2560403104000c80d03c4100054a400c80e04c0b000041d0080d858820441c1c0d03c4840c80b50440c5003881641d240028800d0017155641c0700b0720f0640b40c0710740c586900f006030b81024800e0300c00410402008075001c904666030111548110002c041e08100541038900002c04994100d6000f164040011030740e02c50380c514040d010313000465210340308040880c883c419a9010b10318a0000c0d592656452444d14180800c001d20384404030301c081c200c81454a5000040760301084128001d0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 331537320 1250 331536070 331536083
    0x11040b040b03060f0f100b0414010c02030304030f06050708010e0f07051b061008060705040e04031b0b0618010b070807080c01060f3204020a1e051b01020a17070306050d 74
    0x10301c5c09000f004010400540f00c0c001c15801408108000d4010f4400d8400f641d08034020b000c103600c0480300480e80d16440c448040d5060000040020401041c0050343c04400d2113124244101d0380ca1140664447c0405d22504101d613196400041c80001e0042d40c0d43d5000b08a410103509101e00d942d00102d9107249900c207545036074092420721151444410f544d10003403486000501c40780c981600001d003140518411903186d08410004142014000c8102c40034409034070900360300214030b904040c1000402902e0796070040c0c450b000103211007440a244181a81d4844070014601a055aa803402544c481d031420340d850344d07050100c618800c1c4280940b40090484e183e40605a9040076150322281441c0d00d00c50005245c0c0070190100080e00510080e9002c8007181c00680750700c5281415101c1210f42c1da100c402c600040382d260103600d50490040d0000407480d5500711510600c0080b841c3c00c078071820030100040f4004480341d048130388104407080e80c8040e80307250101d41d00782e85901095002c510b800040348e83c2e = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 331538570 1250 331537320 331537351
    0x13061b140c0901080a0203070e0702120d020d0f0c020606130212010305071502030306100c14060f16020a02090a09081308060a0513030c03142a010b01050711040b040b0306 75
    0x60b181108901e030142840e41c010700481140740d40004d03a1380304184140c9150501d060700042185000380510007100090660581c0e40c0c650702c00408000354810600e5119040c50808054513605a43c4100c400c11446038008081640b504020015804c98204032103039030540030440d800302034541140041c0210700c90801050010300741150f610b2250841104081154818004c00103039a4901351701641000c0181001c500c03c401908004078019a01a5080c01500c180014401100c0850843d14803c41405503500740301d94400d88104d03118901840080e44c889070103000303d610b1032002e50050310b00c58841c442c5c0d58900b0754590144100420664003492081d00000c04101c041901ca020f0903600c000ac0c2161480b1104243d5000741c201c00040801808102c071310403101e500d8550314012142d411402d104040c08000940201c1842010750011171012942000112950355015405135441d0640c040ca105040e211b001c002d05c4014200030414640c001d48480074030764203807000c1c001c86001d008101400f002 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 331539820 1250 331538570 331538593
    0x816150b01091a04031115160201020d02030703050d05070504080d0801030b130302031611210d02160b0a03090c120c0602071503020711060310080606040213061b14 72
    0x1c2c02c05a01c0542c1e40d00200129060161440c0d080340e0640703901442c014101c41c0c0410100e041a500c0114482c4c1080300014000407940100e801d00036400d00c01d034201e480c0e411200c40c00701c0c1c8a00825100501081c024010b101c00d201807500904d038004020301d40642410369550005103000d0300b201c600c2c0301103070303514005009010171841910f5101902e100040b080e19801d40c1d000b5924868005070004c403001ca100070340308005055903c25200200208104a4607200101e26180c0d180342c121194664401d180780d0307003091400464450446901041c01e80c5000d480c08500c05480d0340545140410559035600200c0010b80119914000d080e0740110040d11060601e44501080c81c90742100b019540401020095000c0008074180404c680c0d02c1d0242e26003c95103005840003604503210341d4044004030400c141c404411600380100c850315070880d981a2203060a000480c80340c0100c1e422556030324401804402d005102c0020201c00022400c96541141d4840c1c46c500d0031000c1e80220241c203d01e10094 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 331541070 1250 331539820 331539827
    0xc050f1c0206070c020f0d03170702010204090b041b0c1505071215081b030f1b010f0c0f02060307021f0608010606020c0d11150a03050402041103130816150b01 70
    0x6030700803ea0304081d00b100489400140c0d180e003030b5007913052203020946403005c101407107289107014030b01c12800503035a41c2c1040c51019010b5006406140b4a0a00e0244646258a0580100c038600000310055905c0d240710780c0f0045800340f8480106440b004074006540d5040940341c801e01d4070510403070351a000e0101c8108820301c1525031341c3d56034004080b07504005004d10400400c00c07540a0a0b01c00e0507d551000c0000817030b0608188164480c02800b40710746003a038007604525600c105407001d13a118103d4141c00c000942d8420384503d000350480c00f07000040001401d200d80150340101c4580126425411340d021340c1c9041480271000346e1030709521038004000320b000900452020708101e0028146000c5032001040032101d00000141881703e168101803400d448202030742140b5841c070120b06035108840340c0702030007424060780c00300c0c0940c0c542070784c011050348400f09982c0500705003541c0b60440305003601e9924840d0882d52001010104441c0318400240a43d828806854034801c00411416036110014 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 331542320 1250 331541070 331541083
    0x1110607021c08070f050a0306050d1a01080609030316030f180c06090b1804060f031b05011706450a02190302030a020904060810050c16030c050f1c02 66
    0x406201000042c002d080d17401002042003441207140c140d4645c00482c80480107002c070b40d4003498004032050354032814016a81100100420809050b40860740d07110f40190756040102c4030507900390400e20104040441d103001c000460102c6240205108450084c0c40d411640d00d100001444010300c3c84e81002c0080d01003464000748401e040c04500c482c940700b00d1325102d00c5103868a15041c61000f4800d60746542c0d07640f008004c2c7c000c7c0321500884540302e00e4501000c0d602c0070300100201101010004056202d5001d070840d981030720040c03850a0300c3d024213022200102300b90f04250590402703a0f9142c010070f4049c582d01c41304010483c1c042420f025002c0b00300b40810107092001c1460041040c41003407040030800c0f806540c507a28006981ea40d5030740c6d00300b0080c01a150f0b52a48507041c03242c001a04200000d140300079002300d240800179500e410182408521403c6052600510342d09007107400310740a410014074a501590990b64a801050714141c00d1410a00d40d52200380084010004e0066041000 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 331543570 1250 331542320 331542373
    0x60c0308160903020d020d0605070906091e3807060b030a03140705030c06130b0a0c1b051005100305060c13181d1c140a0804020111060702 61
    0x41003003001c604000b002010b0301e01000c0e003d0b0f840490740c502151a10f80c4c0c2c5120380b6800501c10030480c1051100100205694030400b030009003484c2c1c01003442c0e400040d51411181c10303d500c040b4401d1400f40011988035542d04449001da0403584186507000024000450800d00c20350840e941e158603203000d404607944150090300a0f4001310003503000a410003090b0000358071a030340054466409291440c0745208007a000d035040d01030700d41441001d0b00c03030701c5195032003504c00c03005100760b6610764030180c080303d0380140003400188100d82d03050f001c681c004413021107081c021030640d80c50b00c005c04442e800341c80c41a58071342c102c2d101c058010020300c0310901229410070700e0301130802c2c503004400c0c0d0704c140711921500803010200300c51086d0b4a00300c40d030340e402003040340103803002c84400a2407841125100d07410300e04400032801511801840b2239100302d0000c20000e401c04141414a5801003007107130200001441281407000e0a14585001a0f003006124461406a401884161503812000d0f04003002c0700c00 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 331544820 1250 331543570 331543591
    0xc180117010b060405190305010e060a050a1a010e12120301030c050108040b061e12070906090204050112050403030207080315031203370204090204050307080c1c060b0a060c0308 78
    0x1100b103095551408441c1101d4046880a030301c0d00300f107403440d002a00c007984020708540ca0040300300e415400120f821485224440350402195980e80b0046040d6401c0c8880c42600c8007021a840b540396014400c0f40c40208402b80407407804480c405c03245460045015050016014081700400411020b4260007020740703020310382150f0328102503a912821101c01703050300b4816030f0f8440e030b00c9110003500f04074488c0071a4000c1003014810f81c4407a00a445a88174000c500e141030400201050095442c000c550032210184c0d40c107940300e40e404203580c00401c0090001c5003059002c004043c003148a0001640c094a000090303a141005440d08151610451050f800e1038150207200300518040003008031100b141403541c07500c00c12001c0e410301a030010011f41100001c00d03c00300c0c0c0441c1e9040390b94094425120190100d4982035102c1c18103d0340c40312940e0456a201540c481408100c240c40813141180341c2c4500400300d034210800c000035401540c0780c0c1004000031240c01445003816403104440b40c02006014 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 331546070 1250 331544820 331544831
    0x705040b0603041e120309110906030a020103050a0f021b010609061202060a0909110d05010e01030203121e04060804060b0904210c050d0c0c06020d0e0f030c18011701 73
    0x4040748060000030400780100c02c54120008589004400641c1d4296000e9202541040321a401030000c24810700140d80740781c00c4503c11117060900503036141c050344009004100b289250b500450103881c00810000394540c54041d811400c01144c00135000340c80e40361800243c3c071400c461919003120503e07405171800c0d03410a80e0401450003c0c06036060403d8054824a688a19414081e280c5c05d840e584031030308542c0750030f140c0c5103a903c600b400f0342018418400c0c14001d43e41d170340f0700c0f000700c42400303010207035141c1c10818030100318542d803100429049280313090090903e40c468600b10082d4120303511040c04203400303c0c104401c0003128480d0301403020046a449030207040944030110500c03011480c0400b4200101400a81f00e40110105086036078017104903042c3d10500100103250318030080b011a144562000c0c0810700714008a00c1e00d00040d4980e0380e04141d4000441003180c61190320401c02d81600902a00d08110f8440c42402020b440c04e0030f0728540315500d0300141c010703501c0d0610003030502a403411 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 331547320 1250 331546070 331546091
    0xb103002010c03110a0c050f0a050306161707200303100b030601030b2d030f030304031b02090421020a0b0406050417040609140a030b0601081b0a020f070504 69
    0x808000515940a1900c0080c0c200d0030703d025500420b8208030110580b0500c03846404202c4890b0462058420030340703504845040d41c0c1c06002c400889130151a5054200200055080c00052054001c25401e481c0001c00613011003140c00042e60240c5a800004201c080101c02920200c04a19401104030b0000e501e507182c44010204604018025907842d1074002010620a030310030b030012403040d0401030250341d111000c004040c160350094518042440369030041c0300001d02e0045410b05400c000140a5407866856a07422070305000d00200000700d001c45080444007689807c1480da20a41c42016940360b41c400e0380e01e01c8403180d0444160f0904540c004048240065030389010140c0240d4413020100340c984031031030074442480560300000944d0502080000d15144c0c0441003c00f145c0c0a01001c40c0c00802c000284608407956020241a2000e0040419007075485412142d602110820141064002c069a50700300ca501c40444440103a1200e220f100714160284401c10042004450402c04080710 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 331548570 1250 331547320 331547399
    0x2010f0903030503070305090f0708031201090501031509050319020114100518060406120c0e010605030c0304030c03020c06040f030b01050603160f02070503030d090b06090c03010506070305070b10 86
    0xf00300345e00f0140c9400100718410000c100d58524001d0300d400780d070036503501c4407200380d62a086a1b0b1940705801801e400004d4941207440b43d9030680703410034610714030494140d2980d0f001e8081c20f01c00300e030103220400c44e01a1512041003408007400b10399002240081803a6258805410040d28085410079040810450b0381d070b415140051101e00d5521032103c907901d940c000741c020b004036442400da25110840103400c2103429180d54090380e0351000f208980d81d03202d1034100c5103400119840b040d101801c0011402090144045500c1c0c18030a104039204c0211110200c0c400d6000366101000300c01002c4c2081c0108280c0e0b40805014180550f0528110316002210b00c42c400700c0c1c0702d5500103025091842c1d0a03c00c0c400c0c040300001d48805002c880c3d80d0b02262000b4002080c0081e01035418007811030100c1e00b1450226229406164500e48150030344c0d09220420000768054502102402401c10107280022031041c60319129003074003d07004201c40e103003840310300000e400e01e4440070190382d070302c401d101c1e88464 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 331549820 1250 331548570 331548577
    0xc020c10031103180721080304050a020a030503210903070b0603030d050412031a010f080601031d030307020d020613122601141008061c081602010f09030305 69
    0x48800101011004000760014460003092240c5140000108a01042c00d03144180e03e02c0d000c20120780f8644d0782c1d00c20000e1a080c00c0000410340a19451121011901d210061904a8080e00940d48040078950000325000100d0703000f141c1c50341010490560640c0d900d0006104846c549444890b00d213454400e05480c1e2207505402041406884040755041c0c0b010801c1e20310002500c002040582020b00703040345800e1500015100103818440328610120745002c000903214010f03191103e0800300d080e026592032800410300c83c100341d980d017100300b500341c00e01c0c0302c0103102c1c8400c60281d540c07824008002810885001601d8003954880014021310b41c950740104140306821002d68047d5500410707040f6182035600e450254000340408d80c0c4c460741c80d4000300340f82c12102400480707a1400c0c40b81c418868001d07010003000000ca14400001345440c01d101740c4a00d4842900300c608244080e05030754070140e64001c1c1a03c800d1015680151204658102018007140f07030340e50414412040c07465400402c2840f = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 331551070 1250 331549820 331549843
    0x3030c1d060f07050a060b0301110703120c0e04060e060910121e0f031d1905010809010207050d020d0e03010603410d03051510051309020a120e010c02 66
    0xd000282e050304050503501500c003000d5001c800d071490643d43d4141070000e400b400c60b44510079441c2c1090124a55240401c4810705a0301da282c0c0b110801d00704100300002e1550345020814030840802c1003030250350320301c940c4002e01a5255075224509200702400044540100300b100750424031034040c40a0000070050b52442e551041003502400340c00318001508000040d001810241650104802c05801107040c041c01c07400340701701403403100d80312041003810b485055440d10000c4a241d0300744082d510984441d54080f15090015107000001d0361018540400940c4200068002c82a40201260300c0f04050080d40c40c100e00a00001d42107132602c04250544c5030140381d1403a920100170700c404080c2034445c80d1442c01c2d2090326440d0b252912506450b400d4240c603820010b0318040c0090600180300511014410000d022101340420b078540695440e0f2010030100c45ca042502d03000503101403140001c180300403841c0e4444d545007140a5000080d20b0400180500c40d034100800194141e41c0080d00448a9 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 331552320 1250 331551070 331551079
    0x6090d030203040504090c050907020616030c0509031002030709060327020f090106030203090c040e210d110a030e0a0b061905090a022d0d1104080f0a03030c1d 70
    0x859652400341d1462040c0da00440d04542045000014805030310340880c201c41c010748002c052607943d00d00c02c0b40c43d11000c0311120001c12040d4058860503100394440d003d03c12a600b8024030344028140028549100a10500d0405d50000204149994400740510040003030b81000d21040004268103164910106504008051400c003020150740d02c0413840480a2000340289c100765840d5007008010f0b6204482c1c2c0981c1e4804c1c880c2c0f210a03414144500700400610030007a010010b1a050100302c060100c002802040c00d0a00615031290703554440c543d0814a201921a912001018058159280c025002d8a5038000155041c0410a4401d4069108a089542012407102c0e017255820150640d000320b5040400c03902040340700d00301980203003405410b2030412a4015500c030030100d22540c414540094610041c00f40e100c403591580c21980700075003958100b6003020746542c042894440b061001c1c0119520000450b401d140c0c15209403403941c0e072185001580c90006d210300502c07044a410040307015 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 331553570 1250 331552320 331552339
    0x504240e120a2010231812010905070602011b0306081b0a09090f1a0601092102040504030503070f020115140f0603040f06060e130204020a1107060c030e0607020609 72
    0x80d07140110400410b00010111404800e000308010044c50a120142c52004030170700c00c1c20b200e00300c0d0809481d15011030402491880c102c5c0414403024850340780e5000402c2d900c0308682400282c0a010a201602e2543d00014107100e0b2190110340980c0140400c40506140440a0003040400710380303a010103007107032072554100d00c115001c22034031080c0354020808a4581901c10041100d041c109203003076401030100135841514603152120300c0105444950126580000030850101c41a01c03018a200c00c40c815841c0342c4015801040c1a18400c5034102d001460010810285541214001d640c40c442440204030000d108c04885880c0c03c002d00076030f5030045195a51454940d681a000e50540201510058585c203191800c460210302000040f142d02d8203201c00415441c0d160700d8611310503080c50882a244500907001c1c000254070500414042113080f04006052540401c41000104410391b80c0214012b02d41c240180011aa101c00c24414081001154056a40c5c00141d03004807104442480c403 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 331554820 1250 331553570 331553603
    0x60804022806120c08040201140412030e01020f010b03071419080129030601030204050411033702090105060307050c12071a0f160504240e120a 63
    0x3110100300d00514040558404421060004001e00704a426540b548001030864030344550566801c40d10328400110032400080156124021845c110000e01841524058a0741c070000d81c011548a0143c000c60a42c091008855904000181c10750705400000c02103030300c00c200082c0d103545140c40b503e8411700031260002c000b541c0d1021140c041d110380b1516a140e440e03881c0796040c080d00703010201140c9104154000500c0c1902c001e00b014540700c0003009130000b07a0840e0300300b0004210107401603926a082d80011541c41d1030030094604d111080da0141220640442c00c42c88009041115440c1c4103246191070b100141c817a4070505040d40c0048039240d48a039949001202c59020700c02401c10f15100380c201c1052600c0051000701401402071280608010107155154082081a00c100314401d5202000407218a106240b40480c008149062440d044c1c1d03401804609a41c00714810002e1003985d001000100d400c800500c2d040c0e50260780f5541000c415040d415140d4540580242810148052448 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 331556070 1250 331554820 331554829
    0x6040204020a170112050f063304151e030f080c0c0d0b1006050c060402010e0111030f0d0f0506010507030309050a0b0405030c06010609080d11010b210d03021306080402 74
    0x2010f40305455181d410540e540d06400c0401988800251410b01846580d40c000880220300c1038402d4003103401040c2c0104035440010300074001240700c0d0b01d0041d088000c419187d500d600800c12001d890b00491003030391f41001c551850510000401d00020030818408100107282140d995004507000300c006074807160b001030030900389415880800e81c01541c1c074075034404110483d03900d94018805e441e10300d200d042d00c5d800103440328411074a100702244e0042e400540158410202640310704ca040c501702d910705818540349461600310340b0300c1880ca88008240700d003179001035103e0440c00b100169401d03c03007030800d200041c017180310310280034080603180c000e05000d11604010344050b5030b5109101d10100d10700307400c0070b40d100c1d080902c400c80c080c0158000018403d12858001061fa000b0f42c002d0300152403c507000380c41010241d480c003180c079501e036412510316681d004400d2503003030b2140440b0b15004c0040880c03d1b0800b20340c490b9000c181841807000e05103120b0741d1081901030340c43d142400d80382c5459600008 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 331557320 1250 331556070 331556087
    0x13051c020411120f01030302010b0103020310030b0a0f021c0e0d0e13060b0412120e10260903070b07030606050301051512040309050307060903052d0a0602030613050906040204020a 79
    0x7507020301149024420700d00e4003070144c00c0c100c030300940c02041090491401181a0320041c1c81400a50740c0201d01403000c00c00399030b4210340110312124005075080c103140b082c5003682c00c8020380d014101d07400000f0400c10006030140301080d210083c045d200c44030f003680c000b500041c84001068000c6c4000c0006004602c480e40c800c0d4050b05060b06040c0c0c55960780e85140700310107041182260007804425480c0b40160003580042c51244000307001000c2e07010815811140780e9150040044900c0c0e00311150803174010083e8540e03024900c4c42000c1c41c4d880b14a81818009028040c10f10403c1524118040081e0343c0e0050a030790540c0c02c00c60301ca54649081d54020060b9008107481e00050185c0e03542804209908000d18400f02d50007901500e00300340e602c54040c0c81401c95480094072540101190326880c818840702101e00e92101c5021844407100060b0700d614003502d400080301c90070384c0081484864036126040c5a659071b24080280300c1c915100c0e100980f51500580020700460f000702e5014041030081065 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 331558570 1250 331557320 331557337
    0x117030d0509070f08193c141504080a092606070207240201110c010507022a0d060f020706060306050a1b0807020307080d0213051c020411 61
    0x144903a041c101e6000f6241c0035a8811034603080b015103400154260086050000740d841404004c0306409540c0301e0718402118106c5007007031a5000c1d004607007100c81c1c190300299480f0080685950545403480c11000c0d0400d0000400d8196220318641c9907818174038100f20368016072156985480301190081518141541c6d0440445500c0a60b00c000741149548080802406040121402034945040590b140c1c0d001d4050a02a0400c14440c010600844003008009072001d2000050001a41c1406201d5400a0303c0080700b81c2d46502c103000346c25a04000003126a00340d05102542810001440030303000c40201c0300c180c0145029000d8905020803036010110301c44c0106410748d82d541d043e240103402040d06002c115011842c1001007002c002903407042c0700110a2000c80701200c00581c90081c1d0b03040344018a08000c5100400002000488a02c05042c045260640141c0c4805d12281d04008511031a00014040c0103c280c2c255904044c0c42c12080c1ea042d015034000800050301064140c642c40b074001c0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 331559820 1250 331558570 331558597
    0xd0c06020109030306050f0f0f060c0f030a03060806220c0806070509131a1903061503030e0f03060a0b03030c01060602060906070504050f10110109031d0414011703 72
    0x144180d01074000e0904244259000c000503500d40c401c0100c240d002c040043d40160710f151b821003280c142940030701060103005140c5420a5480c84407075181046013282d20055400102d9140c1c142c0c1e0b01030254401030071090b009048503160100c140c80c032581c1004100704d25400145154401c0c00300c400e240c000a4000303e41514a02c0c9000e240181107a482030740070500605c0c21440010844405100f481c40d24070035270703107441040149402002084d203540900c0c0c245402004400100103501403264130109201c00f0300d84401c003403541c04d02510f04000307050028083c0248040d201d41030f0f640810a15800082d0b1607001450b0b43c0018003080c03841c040c0b0f02c0198003a41c600f001c040364203600020f00707034402d640c0030080f611103940f091b00440e4503008910443c0c0d0800c2c0c001e200320750f02c0e01c3d0402d100401c4032200d19040140020030707c4100c0c00e442c0c6440059003c02d8140b000042c00486c041103496643c1d00503902031165a1055900f0052518141301d03400e07960300410020000060180212211400000d4 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 331561070 1250 331559820 331559843
    0x60702030708160e01120303090507120c05040f0e060429090a0506100f031509061d060108010c050304060b0d1403030f010f080a020103050c0d09061b020102070f110d 73
    0x82d4016a10446092110803040480324001044903041c0c1050b410b03601c00002110040301903075400e8003e80396022044840e4003403914041448030441008005181c05003821803211803514062008071114607100100260030046e4104180304000703500d54000c2c4d880002c001103902201612640d01808403d8100010b81c0042070040303030b81000a84c0c0c0f000601441c1031710f2203500d0721042c02314030000302d00c100300304103600c00000c0012a05001558002403403d8402041c9040b02e59940000c03158020510200d100d0020105c4401c00d20400c06c0c10b0150408034000c01c00c0001c0030101030038074080148000c00458450858136225100d4103080c07a0f6095000201131101d80550000c3ca80f00d8100b2aa044010500704000142048003e1000d00840c0e5010010b040c22007019001180a800020f00181c00700b1300800804410360700b58402c0c40ba805001e03e0b40001c007071400c40580303098604098649030440e030041c000302010a41406020340d81d6648004002040341820b000b186240340f40541c003a008001c4035 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 331562320 1250 331561070 331561079
    0xc01080c0f0d090b0609040203060109111e1b01180809030f030a02070303020c0f1012110f04080c040501030c06081e0f010330050919060e1921020607020307 69
    0x30381040e480303d48503c62031350326a6500c2c4144a40305008850207581503000000420030010a5484a00c1e684030442c5502c0ca406084142c100c100c0000342c17010040110000307203c00071030b0310340416a011280301800900042c02d882503040e0f1040d01084000c3d100d03050000308603c007941c0400074240c000748100c058a48904e808400692150700511041e00940103038140e10042d4a4078420030300c22800000c00084001510450840f16610100c5403150b2850351224440f101001c0705000c0d100171214040780613030310350130144650706040c0b0f1681c02900a90501005000044582e880305003903400c3c6150050095880d030714440b402c015548015009500d00704180301d54801142c50740b6058900841b116122114601800300c01c000354241e40d070028181c464218186544100c000f0a00c2c0030004100c0340d04c0c200748240000c5440301c20391010340403598a10780d040840c14183d40103a00c0d0000d401c01e020040346840c01081000c0e50301d00c0c2d8000300d001401e050004540e61201070354441074000e01140c0409488 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 331563570 1250 331562320 331562347
    0x6031505030d05120c0c0a11010c140d0314190b060409090506010302010f1805010318021e0306060114030c0d060b031018060503120c01060b0c07090b060c0c01080c0f 73
    0x34120490807140b50400140190386100c11901b03900b01000007408041e4480c0c40d02060803941e240c40ca03040194401002000ca4140d103540a81c0d4003055001e0110443c5459003c0c080700c100f05003400e20510350f01c003005506026000703c281ca0005011012504803c10380c002401403050360807000b03280389804098402d0000c00501107041c0e91003a2603401900824520644101d2814044030801c03100e50041440903510a401a4503174420507081660f003012a0760015612000d070390b421911f81078400c48040c0403440c0800800f90025028200550030401314040b0601d2440001c00a4522880004020340309201c554010402800780d51081922420702000d4a20ba000280c42248481c0d40701020102c5448030f0f1788514022184001c2c001c0518900703000700a00a80c0008002ca0702556980c0c0e000515204100000c00d083c0c080d910203442c41038100f605003030445000001c0140105010311003a5810a80000c0200b01c800003401c0201a60fa280c00801180e03108a40750300ca00c9140c0030803120280e800 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 331564820 1250 331563570 331563577
    0x2120d0902031204231c0605100605070b15060d0e06040515060a2d0e1b130b09031011090a08160b0703050409110702032506031505030d05 61
    0x100710140c80880003d49032150850065005040340034003440d689480c0c0020518046282280c00f4003030005041c1c0c3c5006445807011040403c3e00c03559290307000c00210250f090040d00203024a42401030401c0142d46070003441800040c040c0071441404503c602c10740c0d43c2c00301507a603440c00403102840b00d0681c0e0242c40361119001e49044449114076804083c101e4120b0301401d100341000351804000034507000001c800510a818070380c3c0550305403402126200101c543c5c02c2c3c09011540c0c5c0c0038280b418200c00d50f90b030850320141a00410b00c4203000300106440030301c254808550070203540c00e46403400c42d40028106030301045041034091500702c0707140510794500c000d401542401c07105511b030655590140b07a1141000704071442d444203007c0b000e00c004188980130b01f40207402440d0043c10b20ba1a8001c2e84126840020f070004490808100001146820007401e03202d40ba2501c000d10b042c072203001d404246094075002e502e05050b00c50380c0c05c100c03000901c01c2c070a009010040032a0510b1a201001070f02c541d2 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 331566070 1250 331564820 331564823
    0x601051e0f0d200d0b010909050c03010312030b0f040504080d06060f020106050102070806271f0b03030a090302010f1107090b120a0804060320071202060108191202120d09 75
    0x40c24090840c480e120700f001c000610403400400c451401d403078001d02500400c0e988062605200385e014012402160178070501d84103646103241c0b50703629415810050380c090200e00740d41c4200760a00754009001d40780d0303900c54500180d050304c011074541c071a440e209285005180120000c0ca283c0400042d0181d401800ea040c1a0b0f00351b00200b1000351290012601c0e41c8941c001c1c0e19569000c01c0100d40390080e81c1d4281548203561914404041001d01e55150030300282020b8200e40d840d1b02424002c2041040c440c201d01594220000c40c900b1801034000340141e2580e200c064140001241340c14800e6014686401e4102c072603c0980b6100ea480b1a41d00000b0003903058a0b0740100284401c100d80321314001100c46e41503410040c0ea60407d07150036400c5019207200c01110305449001c09034000855450400b404c40c444c80390000300c0100c61030040003860640141c2c043c3e01a507011105a8680300742c0c40c02c18003105030b0480030490014a5604080e85402c1e0000494000740304000b4411154100a900c1400c0c0d05 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 331567320 1250 331566070 331566097
    0x3060a06030204061e031104020c03040e071409090f06040f0e0a052e020a030605040908032a0901080c0c0d0c052a0103090f02090109060504050f0403080601051e0f 72
    0x10b41d00d5002c621017800e449500c007203511440c20800d1020443d12528a5101d180041c009440c001d040460317141036820503070089030501007560502024681040008200c103c8031007401e400c01c4814000181445000f0340030030705a54000e00401c503242c8031034200c2441e4014044041c00700c4140580e426513540c031190030030b0300c240c0240072604446d42d4000600c020301c4060b0990403400d105801003024001d60000090400b030655400c0001040d403241e011344541c4500608000da01d03498801800c3c07010207036000f030b00c501d003545c00d46480031000403203400c0d03c031383c814203180004441d40ca83c0349540b014032500754000c0b410b1003030108028441f58010080c0b0212031142c0161060403540c00241c070b8642101003d400050710a108411605510a03448080f406000d04d240b4135400d00244c01060b42c0030401e800480c42c0588401085c00541040e01440d80c001f40314058440c450714050b18001d20000c0c01400483c10440000b60f0072103462116014070390707924810000c80707603144034464400003158010790012010 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 331568570 1250 331567320 331567331
    0x804141f05072d2001090e090a050a03080601030f09150b041d0606180f060621072601030506010902070203031b15060d020d12120609020909010e130206031503060a06030204 76
    0x703044d480d80b0103021988040c0c44643d002414448003c180c21802041c001c483e108182043d000310346e0800c000e06c0803078041c0e156a610303418400001001c2d6889a0400c032010381c10042c074100000e1000305080c051000c6240c00048908001e000030700078003001454030720300107007050b51000104004540240144011200700b4041c4610901d0b81c11a90402c44501002c14907000008146050200042c030a4500403003000c6180c14007000075444021040da0240001a25105140484407110007010412281030004030140e614607540c0c80c3c1d903880140680720300c458011481d14210b450810a50f00c88c51145000004e0107044801003030b5076881c240710514512030031680800c005051900342008403a4000e02038001080c90342c0c4a625400041d000210204400004d8849241304644660005801c4d004805692500e6040401014000603000a03442c040c00d0f0041c4444015249140341c81030798147c40c81354480c0c1d100b640f00170402d812940600d405000350410840480b4080e405081a68400c4404015 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 331569820 1250 331568570 331568603
    0xc080606091003330f05150307140f01020f0607052106060d0506120a230d0c030f021501030f0c08120d0203060301090206070804141f05072d 62
    0x18011040c80f000d0401510030505121316151000c800810707200c0500c100754000c1d981c4104c44101c40840f107520416903902d4042c09185002c0a0118801600450060000c14201010080c605040d100340500c40d10383c2150030315003079000b8050401c16141800a85000c0d24000001400641c0046501c0314820400c04402440c080807003112030041d800600701d0703401c5c1580d11320004014000904120760003102c058851000307210030000c2580080c495000c11034001c5119020315100030308030800d070540da0091401c107007038564440c007000c3c0c000f034040c900700054841070740040c0e09140c5c41c82070f036042102c0c1520002c000d208002c0000e22150303114070045003e42e5580c8900c640c4412140d0459600d03500300b000404217890b00346d00a580c22500040c0000785544069002400552204000300d0b071004002c02e04000000182c0824060b40c00b080e210007000c8021a01d01c0c1c440c018010340e000041c4800400c00100740841045584906014100302000880209587c003d910800610869800401500522 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 331571070 1250 331569820 331569841
    0x60206060a0f06080403030f0507030207061401050108060d031101020310080d0c050606010c0516090c090f0e0604050403030b51071707030507290c0c0a0c08060609 72
    0x10110350102c010600b446040c032608031494580074100b6420543c85400b5080036800b14410b031401041c1a440c0140e55080d5441c02c0c1301511803443c1c4a820038a007000c010825030340c01000556104900711450501c2040740d18098580c100e1040700c07840c0c1c9601c0441003003800780c3c0ba0091380b4183c61442c011100c4904005804513003250909900400a82051010034142c0d4003404541c031115105206440d250002d50160700796603601a44032604494030382c4031380040340b6041108500a4450088150522307820703c030b11140c880d80d0280003207000310707035820001341854401d030301440020f40020105001c00780741d83c0b01c0000e204000e0f0002c503000e40c408522a0052440e68640c02d0101600380b9010411b01d419480640442d00041310641e218248058081d660500702d800802116200e91a800d0f01e903405800d00d6040d16003c3e02003080b0481010f035080604030a441000c0d584400c0e400091603580c40b400c5001d50921604080082600f8000340022a0080c2c020070071030b10810301903034a1012a44c460f02d042 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 331572320 1250 331571070 331571089
    0x80c0d021b03040e222f040906140c07030801030f1415040203240c070503071b18090b0a0e07050a1d0601030902010f141b030d11090a0e09070b040e0106020606 70
    0x3000014035615a10064800042d400c401d15a10000c0561111806c0c0100381952403c0c1e10456179035a5600d000042560070008003504203010201041c18940c0d20b56001e425404103010107440560b40000b40c07810410010500364240c0d10550607115101300780001c00c0d42c4d80c041941d0813032203801142d021143d98408111004641040c40064024076200c04a0b0112160311514007512140400c006520100e94020380721130050544900c03a071383c1540f030b00d28010750007041354440068650406003180082800b900300980c000510b01030010381c200c00c0b140118a085440d0740660340103502c08800041d074a13046002c401d5031300c0001e4210078907661101c0c0118200c4541510090102c3c6192a020310340600c6001c10f08564104110f0141c5802401042c580b00c902484800e080d25034000541901134909034020b000c0480c1c4480080390800544900141c03e4403064018800784102c0d080c0000c45080313003081104010b080e01c0d0b81c041d075600d0b16808000440c15090048101510035400030030054100310812 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 331573570 1250 331572320 331572323
    0x904140411100e010c060e0601081b010206150f2b03120902180406020906030a3e07020114030a061706060a06033b0d080c0d021b03040e22 61
    0xc50385084140320055412003d408019203105031f0740d600c10300d48420200300c1d050107405110000d0005290780f40d5a405410075a01c4198110340001d0244040c001c6800e408001c180c00440381705205040e80d9010072060303840031517003010b440b00b5001006031207c02d83d540803038410700a540d03a41c0724100004050007501c495110083d048181141040700c0d282c164944c5039003051184802500c4c20000d10001a59500155601c03c240d03580e407071841050700802c03449001c03035039000c84000c11050042c0d10343c407580346000e03018580c82c01c00002d00d200444e1f10030b50120341101c012168540d1603040a400540081007507008010001001c01c1c1d590000d11030000b0800c0c81000d0080010800500300f501c100d0140003102400048400c80303414280c18140c204100950460000ea039a0400100c1501400e02d800143c0300502c080c0f001c0007041c0411000c11404440c5030040103000036a548070f01238440c2c04400500c80c043c5085000c081404607000c5528400d144c090440348904440a8a10032942034800c81040750 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 331574820 1250 331573570 331573577
    0x30b0303070b04141c020610090b01090501110c0301020f0702040b1e0409060e03030a0f15210c0302060c03030402030c01111915020406050c07080d0807050d02090414041110 76
    0x1400041d40340640c0c1e08194202d006132541d0602e20020503040b031030805e01c030001680181e800c00441f450014a0b540c000c02040d1405d100c1c0b1648100043d064000394000d450410039041881e42800a00300007141d802000500215501c501078885e1360160b4002800482c89142070071480e001c549000b008074500e40781c001240b00300700000c0c441000010000301804036051911516441c1410b88188007851161803401c038041750f40003201d251507040300e03007294031110548403d1406210800d40c0300c4c1c20b49001c00790005410401d24860824800080e82d950000b0361001c00014114100c26000c005103000354030960032118024400d03c0192a607000607046100664040515420a00074001c83e01c16400d0240500f1070070103003506185000c0c0e134040d40090b400315800190300c2d03850386000c2020707200404016000e03000390403810000805440d03001d08040c08201002c29426183c540543c1280c01c80c0100420400242207941405034461204a0b4141c48950307162466588a0038481c00118590a040c0d8 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 331576070 1250 331574820 331574843
    0x40c0c0308010e060319060c02010e0105070903140c0919271101120c0f02070509280e0a0b06280506070f020a0e010e0a0606140c010b090115030b030307 67
    0x4910a030050f002050268144103541c490516414802048840580204030124501440d04006400e40b2090b144666141e8506002c00074880d500268007000c3c1d81d0f000c03402400700d44911009034a000b0482c07100c554048070740b0781400f00ca000f43d00c14451a4900405003400254080b804c504c03035002c0760789038002116600a0760180001d2840700d0741880408141400031040285400c0c00f02140c0c0380c90a08000f01c1c1d100032058034007940401c0304000a1208032690b81c200e181c1007580082d0741c50021446d00c4140c2ca02c050000e01b105540c0c03c43c1010404050499604840900b071000c1900c40035940140100b1505200c2120382420400f4800407840c100380515a185c90141408660340c4403030426680f580c5641c182d900180d4602d04402d0007844400e000102550400e0b0b0700128008020b04441c0002c2d00e049810000345070400d1503c6c5102404c4481c03140ca4440610005025010304003086500160344000812101c0d00c0700101d45514040380ea04100d0000080e0506542c0c0c81400340c0581004042d2 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 331577320 1250 331576070 331576079
    0xb0304021519051b060f091204050d0308040c08030d06030c050f012106050406090c0e01050a020c010e0a0315050f010b0403080d090305070507120213290301110c010b040c0c030801 79
    0x10f100400f41d48070207030310000b004180304d42004d0400b0000d5a4034885440d654007407009034035040280c5108418040205480c013441c08000a10000c000e04008007840800c00c000b07018001c0242030580101088030503256141621041c820090480f4007045849035000440402c0504024984005c1d4010684a104003484000102f040c00300c08032081031105038507441e0104542d181d50080700b004011320200450521609080545a09a50382e0352a04010090101c04056a8005104103101b9028200303c28140e51410119124030b04642000d0282e8543c20754420030740c201070f8002c1307214101c014043e55a6903201c10228030700c0d118612019100007800c1c8029006108a03a0040308614800e04115182c030b03585a442031b0600d05158088124000f07814100d000317600b00b0000c00405284c01d44820402090b079a152510060600b414143e000e1150200f00f081c80c1d02e003540002540c071420100d83d502e421103409054060025840418001c034101a641c24025000b0002c16030300d20f80c0740d181c000340c9a0a0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 331578570 1250 331577320 331577327
    0x302060708150102030318010b06041403060c070206030f09190515010608010b073203030a0b0405040b0406050601021f0b01021501140105030702011401030308040308100e0610030b0a0b0304021519 86
    0x300051400e03550307900c1e000c890a40d0b4ad0001000249048062441201e881d1000c041c1003103802842c410000c1e0b010000100141c0d01e41d0100c1e54000500740a03042c0503250018043c0c5496107014401807410711081c841e1043c07100004d16100181130429407689142e0322a41c003180e03454001c4c410a05948002d0000c2e2001a10070700e4018981110902801caa1240d1280c1000e00032611210120f0280c10001c1801425881c034041c0001c011000e0300d081c840c6040c03540d0303103968100b00100701800d510340d5900420b156a2091225001e5404801171000701c1c480d5402010300246418035441c2d001d880760300340c43c6071207891444c0f040341205e6008030715000900c0d4103001503542d42d200402c000304655962058900c5e000300708036060301071806035035600340130300e864680604140c0c00503068000b4800b0844c4d04200c12181c0026281d84170100f988d42c40c03481d154541c0c1c04d40140c4581e0700d4059103c41040c43c04180021140007440c030541c021600710317880101c04800c216480c030895031000e00c2090340761520f1000b00d01 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 331579820 1250 331578570 331578601
    0x6040605130c0c0804270e0307020424030c050109050102190320070303171312051c06090b0910031109180d030c030f020a09050d08070f03020607081501020303 70
    0x70b007810940301c07804041e510341609030701c250443d880901c28801c80300d04050400c0b100300c01500580004010a2082d82d0080e95a805400c0000744142d03100c88a241600c84600c15440741c01c0070100c00b0300744c0c00780c880c601008009598004c260004554000002d0250303c0014480400c0300204d05004c000c032580e4408640d000103c10000265956401c0c0c0328400b01c00803c0280001c5010b60742d03a6880b03c4104085410400000d801c90208444407641e00010400041c239070203000b8528100b0b60b0ba28054100300c0749120200e00019040c003403400740000b6000d1640c1d0807110f0f0040c0c0840741d032900b613a60004034600722800b600003d00034001e507403400181c5007000c0b12042e4010142c4041801c00710f600303510880c0b42080304003502002980380c0c2010701c020754040c0207408000290500c1503041803401c004c028074010700761145078403441e03940100c030301444100401c48034030700d42204070000301550606001e592801c0c10baa4482c0001c1001d00012510203072085000d00c0418142e014601d961112222405c0405 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 331581070 1250 331579820 331579841
    0x3020d0201090b0316140f1c0609020726030f07210905011517030901030b0d0605011d01052706040b1216090213060f02030d0c11060604060513 63
    0x2d070040041500e0b4225405180300340811a450360703440740b80c41e40c000c1206010000408810f002070050002c001084d10544940711001030404028145da514428090f08180c1d2045e00028070005160090140d0304c1c51131441b540e074000071030300e00c0401919909079a1008070340c640b054040b005c0204050500c10032114400b03880c034030380b00c01c5040541e1420034100c6880c4541210144e64418159114511200041d001002648442c80603040341d81c1e25a6120300c80c648407641019a034089003901a526040c040c001c41c3d402c0141080301e582c5580040c2c094005444214900014610000581b8a05a08080c0c40c84492807492010310741d000c2012502284051b1441d035000e42c40d031051008588407404003810980c031510090035407403d003d040140742c400d107400030107040e4010440c1320285403140001900702d88052604c84801171300b001c0d01f241140294418200c4882c2490340c602e02c069172055a408000f10941c0690b40f49031121410032044a00c41e10865800920403001d10740c1850b0720b64407411041 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 331582320 1250 331581070 331581077
    0x30f07030f111507060b030d0530091e0f0a110622210f020d0206040b0414151215041404080d0e0d02070302060d06080307050109020906010f0903020d0201 68
    0x81c1c28200140101d04082c038590f580c0b901c08102c24081c485140101011403400390003521800f000c000008105200c0c0311050242c107600c2080c4546040f40c03000e152902010107040101060800351840d58841114001820810b0081c0a0313000b0298408500e20354101d4200c002000130300c4031580c0b6a8003a95801088a6100d501800380707104c1d694813043d6442010140100401ca02400c12a00032418a0b016110340d00e48240d8070128000107000086144401d901244d1350640034400748001200780c49a500a005542000710b00081c00c40303401a007007a00d0300c80c111101102080518032a0809001c1d610305002003810040120360400112141c80e01c5902015201040da0100401c03000612881540e088402a6000440501c0820036100b0310552104440261608103040340c0000c0d50f503903990001a00c60600014050072680c2d56a000e500140240c809684d11903165041842c0204415070b001d902411445000801c10361003010702c000c044201da00d442b00d150742590280001850600341c201d060 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 331583570 1250 331582320 331582343
    0x10806010e04030f1e0e0301200f0f0c0d0305010e070c080306010e01121109040f0902180916061709030307140c0102070204151a0403080901270803070c05030f07030f 73
    0x100900081424046445c40c1c0b281c0031102001001c5c9400c40700100040b0480c2d010100601e0080d17200201203c0522580c030031029155010395441501e035203d0000d03625803d01c1036070483c140007501508828101c80d0100c1c0303240305641d903c034000c0d200c0700e42224004280c0d241c100001039031980201c0d502c17102c1007410302d800300d800c4015032080f8046981d100582041044c01080c0c90059203040d020700c000b4900442c0052158002a501144108095003d00000b4151030000200e01180400c24a601803d58031b1012500e99907990340030b0140d03400c0307245c016107244680000484c40c1d08000304882c001e04c1aa506c2a40c1c1c030503006502405a044451036031415502000130383c01503030340d9004a0403441640030303c03080324510303050fa04051002003a00c6a2078a5005100810201b48480c003a1640b084c42824890b10048070180c3d00303414a42210940216044104ca002c640d028000000d440c889114522030012151144105991921801408001079000388000c4c8005800d0011101c0b0180c41007210300076 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 331584820 1250 331583570 331583597
    0x15130f120c02060a111002090d081804020d0506010f080603070b0a230415030507020a0b0a090203100518010b1309031206061e0503060a1401020304030f1505010806010e04030f 77
    0x21680c8040040800545c84a9031420040c5040c01400d100c4803a01004500d02020324000c11031024506001901c4d6420100d91b01101e10310440003aa1100300c014011903544412242c0c50004110640b0801e00041711030429454547c024001c290085900900621b501482c140e0400030a500410b884c40800000c40e20101c000c0600b11500481051949840360b140c504141000d13417602d0011080008040c20b08081c0702c0781ca42c000c5104030185400103024440742d507618000390060010180000d40601c120107030845c81e078940d0b5005134000d803802d049003c52040358140c2c26007601c180d0700071140d2140025a5200c0c0d039100c01d0780a003401034801d04084402c0c40304070500308111181e030b41c00b8902113030481c100603843c6581c0c046140c40075149070038040d040d410443d0202d4041281c5000300d038140d0480d014403a88907030003082075400466000000402e400c40514119440c0002c9140755140b450801001060710b4074089605410388030b81420015007a43c5035203046450780c000e18110818080f60039031204 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 331586070 1250 331584820 331584829
    0xa0e01090c03051c02070f091d0f100f091104020309070e09070608010b0a051806040f1d0703050106270f030506040b10050d03110c06040815130f120c02 67
    0x74000e50055001d07040161301040c0741542041060011002c54200c2c9600340081c40e07000f21440b040c0d85140d1000500f1580b814222410003502403c1022107100c1c1c0c8041c0310400e0780006002140c040310ba4010301c20070000034520810b072600181c0041003260b42189081c0a4240756000e0341d80018190200c071507007681c40b11000707100f0b181501c1c0000907401c80b2009000d081d4110211134014401c0030051850440c110000518601841b654034891015080082e240c550b6800c1c182c03005045146048a211a81c0c3d2022034100060070021540704040200000c0c030381c038001c1c41224100c035000c0c1c4603650706010b0807604042c02c050500900c44c00c031500340b0300400d4042c11150083d005e14030802c024580c0c0d0030541402c100c2940c00034003070226011600401e10a684a54244119840d0705052814072603629410705820020410a1950064070104001604003800140c141442080d40007054460f101c3c401d8501040200800c00303442003058000072000920000441840715240d031428891188186e070015 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 331587320 1250 331586070 331586093
    0x30204020f0a0327080307020106030b09070501090b0405030d05030c0c1c120519090c05090a090b0702030a0504051201020d0906020d06080304180c050d06030c030c0b030f0a0e0109 79
    0xd21103100118141c007196402d40308801e00300719044d03090401d02c01c40300c281e030801c1040320000800185010010a1a16000350020b201560340400c070b09040745004410146e54451302e2183d98000340c03184000159a26406049400b41c50014010301010368071100207a07032a80c03010300312842c0c202c0308000d00c00d003074007050050140e10240000040310f90908140000e001010203006656903900c1e2200348103189401400040808042d5140459074980c00c0c10000c42c024070990080e42c02c00c0e024800c01681800320b500c1101e44a116102c00419620345490807a5680100e000d03c1e0f002c1070041205120301d2400c02c034511080c641401c0050328007200a60032a040c2c0b04c00b80004c0700d20540105903440f64200343c3c011080035082c1c40e0700460034145408070324991010400c41d007105a50b0798040d81822503100d90b00300c880300c04c401681130088940d240703024101603d1610003500d5050390074001040503400d50701105c0c040d44510364100d0b05c9881c0c0d801c0c3c010007091a1760400c1a0b030340d81c54104800085801085 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 331588570 1250 331587320 331587337
    0x120a0302091e0f220513050f0d0801050f130222090b030606042a080703060b07030c110307120507030b0109020a050301171011180103020c0307060902040603020402 72
    0xd40ca400c0348100307000100e0640094103802000010501c0760799100d400d80b4003c0340800b12a04610004491011010070900c0700c001c3e200c060030300c0c040000c035001031071012074468031404c01c646504160404e100d44681010f803180000038401c00040140c1c0c50b01c04110848400003c2103c0001042c02c3c046c1e43c1281d100c41c1c0300240020358252035107031060450b6103090003004011814041c48a100000907160800200082e00c100e40e991f1000018000c101044d000e415024078000030180340c2d100300900110301c215600000241000d0001c0b80c004d1840c41a41c100035032584410224040d5695040c2078203603c0c81d04c83e901880341e17070000280041c80314404070308a8041c50140089a0460802d01c0e0307401c40503000500e0481c010440b005503154080224dd04403003113800007155010041030301c142007094181c030320140c46090104c030710a81050b03a1b004142401280e0104007100050400540a90140d008006102d4005010703000120302103030010301c2028801040000d5068881d400907040360420103c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 331589820 1250 331588570 331588577
    0x30a0b0c120115030f0b0f0405040606260f0a030c08071407091d0705010c3003050702010e0d080a020c190f03090609030803010510020c040507230c150405120a 70
    0xc4152a81621a0300a400b24400081c4001190b19000c41e1181e400400d41c1f03401107661340006014001c503607007c04050032054224a9403c040811504200b0751080f1407090140124040d0324044080000da00d0006641a2a80d0071011001c0d200c2f48581c2c1c20424098074058010040c1125192050140c40f000d420400e400180b0300410444461003007019841e440e0003580141d106000c680c1c0c010030b02040c40340c0d0002020340c40d9403400341d41900751011803c0007221883c9048a100700e40d038040e08242d200ba40141c2c0200508030035030707440c1907030380640007d5080400c1e904404560503940c9500282459000d05048032040c0300c642d03140520081c0851029070b030000f0114644400c141e8442450b400902c80c52406041e03082c110385030b0000c41e110602c1014490040c0034a01d062690090159880c0c582d070080c4100a00e28100c900542a989030100034001c1011001001b050980b04409540c0030108840081184c24242d02884005000107441a150f0b88039410360030840b4880e1a004000b407051569 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 331591070 1250 331589820 331589849
    0xa2606010f1a0421030c051b041a0d02040f090c03060e0c030313061b0b0910050601031103060f060903030310180216061a10110f0a02030a0b0c1201 65
    0xe0701c42001500c801c059030701030340204003c1140b18811140707241268034038420750081c0141c030305d4156068514204004c000c0e0040300c041c0c2c02005291106079112007010703a8140809544400d0161007180741980d0300358010030021110025080c40d0307004581c0c103180140d0001d85028561a290303400000d980c41102c000f03480d07075140f0f506010140004404030308150011400d00e002901e603d50150b00341c0c01400700304840e01c02c16141c3c01022211001419401041c02442c2c3d04054541c5030700e4103018800f81da0154101000f056a40d446885407282110700e00300705a045480300410424069000303081181e01040074098800c0310b5409000543c002c529440c0b44808191a204204d2035001c292901d055445105001021480002614650410390702480c001400b951605021704280d09050003140c1203000c907450040401d4104502e000c0da4000c2d50200c03803411200301d04040da85c015005000303403da0404081200000c040802558100f401c540149040c5031b000c44071721180c0d8000340c0c0000c0c030080c10350 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 331592320 1250 331591070 331591079
    0xc11040e19110907050d020c100207080a08010e070c1b0b12071d01050f030619140a0e0603190303020903010213050f041a0f010509130605011d0a2606010f 68
    0x10125600400c100340d0745143e80785040f034400fa20324011524860000ba400043c20045803000b8081031446000300b840c115214990782c24220590b4008042d4100440c0c0c1c444004113035140c194a0380c0d403003254180d44448400d60300303a403090006022144400d0340c0e080031540c040740c500600c401038010318011180c0004240350190004045888a5090400080d00307882c06264599000044820880110f40080c1d80c80c0c841001040c11000c9400000f00a442c0e000c102088040c003c180300d50084004840c1d4565041d159140203280000503595258140d20914140e226024401034954206009080060400424001190980c0e0049546150b008400c601c1800640340a01416100b440180c0b810050340518141825614504029540c805c44060442c0d80031031384101d0031100581c074080e02c0d40944800080704400a86450b008050106401000c507a90503c0d94481320341e80e80d1001040c207d605440c00c02100c2c101e0f0004800307549101480304240320300020401c1694000c241c80392410310742c9442d1 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 331593570 1250 331592320 331592333
    0xb030403050c0d080103050a030f0c020907030e0c150901081f030609021005070b07030506031906020301090b0312041404020d0c020a050f010b0901050f21010606020705040501060c11040e19 83
    0x40d08410003c2c0007504e001403002c1140064002c503c00c0d40740c14002e080e00c10061041d650001e0b0310000951041c4080200420281d243d000502880100c0c021500c98101c12404c000c407003c260085805144003e00c00d60310250b02c105143c9801c0307403480b82080c02c610030314824650b05001c15002a02e007292100c44d80c1003107040c00c414030135800c0c505140442c1084c0090380c6040380040090b040c6000c0503145c00100b4555a410f1101909141036003290428900e21403030a035000c2d400074810480c1191411801c2d040c107081c04a031908e0b21108400d405450181011010107814140e00300703480e0002e500340715080900b5200e01c19005480340b1a0001c01a00d03500340b900301c0c507240e04116181c001ea41009822602a100e501d54281914001c903410160000c1c40b0b404251581864483e0003000e0407070050000781c3c008198410020f803109642a210003540b2041400141e800030302c20300c80094000340d0828049101d0104007107090380010300118076080b170012994a0540c0c0c3c110f0a0800c111030700c0001041241 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 331594820 1250 331593570 331593583
    0x1609061d0910170c01090906050d151e0905060106141213080c150c0f18030a02030303070c1203060e0109200415120e0c09130606060c060c0305060f0f0102070b030403050c 75
    0x1003038800307108e030504103008644100b10340b5800070040b075a1002e003c4601401e80e0070840004842c08000034620580351310399000340c1410b48050b22140154000429003030312a03484504142e2107007042918040307440e000d800e81180d00034180118040c0d0665181d0000b40c0d110000c140e0520031030003c0001031440d000c00e540b460030250120088010800440c0c500803030070411748a0140801c00550041446407000ca8105500c802d0300a40c140800000c00030b00c607412828660160703008172089040c00c7d1b14000c09070700716000c600030310b003410300c2e45001001486041e03041030240c0c1041411200c100200c11100d000d094000c3e410a0148800021070350038030a505c0103a801c841d4842c1d140600010309a1210141c070741140500e040d024003034040002e120003015500400429a0207101048103660350003005180c1d0785078a00454000d801c00c0300f4410280d20900606000720740091121140350100d10410040030340079516241540502800000c0030400c200c090740c4554002e031902c0c2da8601d05890360505110 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 331596070 1250 331594820 331594829
    0x915061c080a1d0111120c01060302090a06031a040201080f041a0115030f0212010b1b03031510081509070306031709030d02030f120a02070204051609061d0910170c0109 74
    0x145c04901e0203110100052800141c485001e04150f80c0c4400c1c600e690f02404054002942000008080c805568502d51050044a0140043d0003071040384911484485105840c06400118060045070040340c41d00c103001e400910808255402c210070360b6100c042450240d020803440040903070f240042580500440060f0301c8100000c41c0703408000b1001c510174190600420301000d1003c0749114143c90841c02d40c445100420040700c1d00c0b8a418000000364881c00c0b6620750003140308011070003000740200e0145008810308250700c0f401a4a00701071040c0364900810782070800d40c40e1200000460300e40310107048006014900140d8500f5020240740c03900d010300c11900d0440d03204100d6660f81401000550b1883c1c001c01c2d014100030b41398464410084c1c007070460080c2d845464902445100442c00701d003e44a141607840342000715a0710802a106001340d0800380018042c1118040001d162419805900010440c510b044041e00c1300e07003261052a04400b07580c020b9110b042918001d603040641b100081 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 331597320 1250 331596070 331596077
    0x607050a09150908190302160806041403090a1205070506070818040b04020d090c050a0b040501032a050309211818070e04050915061c080a1d01 63
    0x40d4402100910600746445254005903000c00c0b01d44555108503030b010024902e180466694002d422a6140303261480c03c41200076105000d56411241401c031130003c100c0d003620024210039500c0342c403280e800300300d2080019001d020401030a002135031207480d01c9014100b044c152204080c900d140031890824241c1020744104000d01c88200007070790010486003c205030200c01402d0501040226000d0000e000090b0703403060010034458003140659114041e510b00504104000540d00c00a00461040901a4019113901040705100c60f50098100000d4080c0180500003d40400d03201d80a44600b941855000601d000003405404241000402c5021401c00e00903c40101c840c045a4114400c80104443c100075445c003400040d81e031020f4007008000c600c040f0307004034540120000d02ea582c403292018865850701020850008001441060520baa96441d2655403a09802c00132003a8459241100c13150703955420900144451014060800031529006c414080712241001c0c4400400c0049042 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 331598570 1250 331597320 331597327
    0x180311030702210c0306190516021b010c1217070e0901150309050f03030105100306030206070f080721030c02010e0d0f050412050f060106050a0903020f01050403150b03060705 77
    0x2507030f643c4103600301d40c2043c0340560303000c0c9a40b4402c01d41050344048555501d400394204010840d6001d2001004a00302003004118956418030002030350812500c107040140e002c550004504001c40e050503ea01e40f050500d0f20941c28159250003850b0b9101021000181d107040a549184040100341a04507005060102101d03045501141020350144617413008001a0a00c103070403140a540528002a08038040c1e80c40c66401c4c00c111035680c2d0081c40342500601c9c40c1200c45d00f03010b02c0ba104407000d41e68001c2c060751a20603039454000195444000c2590342c0c080412010380080e030084064400002028411260514060400b0f42190b54030100d040540e4107000b61800c3c030000114201d4075021085c10f09840840040404032001c1c010342e00010340c813460011381c08042c00000a074404865043c0002c0302c1d0142c0e00e620003180e141c0103c1c01f50002154203036a0900061900005e0070040340018540641015502c0d00d40e150b543d210501074804c51a0b44641e00340580c1070038411150320540d68100b1915 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 331599820 1250 331598570 331598573
    0xb04050c1606020306011b0c05030f1b0d02030115030308010e1501020d0c030e0a180606180311040902060304060506030601060302040602030f071406090d02010c08040c060f030b041803110307 84
    0x8101a01c404010180d60780000040c0a680c042d50002035070b90355812001102c00c045103800c04615170703c4e01545103e0310841442c070800c4d0341c0c001225003108605c04d68083c4000c664200744504e466200e14100da055480d00717454102c1800029a040c0210302a41d6141800e51400400f003070300c042c0c09440c18604450045064005d40d8000071070a50404080c540f500340000d5034101201c4190b88080a41c0e881501044000303119283d030000106a5210b520007040316995502e001d490451002080454000c1c2880082012500701c0f000d00074112006040481d01941c160300083c03440d84200c078100c840329914814080f0700c1c02c04025031400b6213040d0400b14541400c1c00d0000e0354a000b041d0740e07400340410014031032080000d0002441c001d00444002c50340c2a0070600c0600f6103500d440d013103c000540ca0710303943c1d4412911034140d0354000c6801180f850002c40c00c0181c1103481001c0c1e00c08481c02d1548440d594240c507151449800520180d1884110010485240042900d80b140302c4010890740203000c00c40 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 331601070 1250 331599820 331599847
    0x1501030908040b070f080d020403110607120c050f1203041b05010212070519030c0b10060c0b0c19090602070509012103020a060f0516050a080c09030a06020d0b04050c 73
    0x40507211910310070790702c5038098170b04001031381c100e580001d140c180007089064104000e031300580145ca1245003494840300c01002400300300c0c017521601500301038a032812441d0070b50042c0340300b60075103000d481513a041c0c48282020600c1e011a955400c0d02d0040d0002c104014002019010f41c907142d40d20901018031450440001e643d15070320b006d00201740800054100810808002d0a03d11521029880c45948052305001c0c0002041c44030986840252400107001c000c075000100042c0c441c9526414000138450300d41c200e807100024030b50040740100300144901020000c5230380b000c4c0d0800f6a1800d020314203000009044c400c0942c04240501030400051041c0061119215814440d1201c2d0503015642c81c01c0c22031911007207007006000d075460100c05a0703404d0360755001301c0c0c82104515554801042c0602c001c0700e007032142c0c0c0062800204072001040002ca0003400a01c0110002070448107001125202c000899001052147c030742075a80a00b050701d41094080c1c039030701800d0111103d0038420444500c5 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 331602320 1250 331601070 331601077
    0x3070c090c0509030601121a01030803070309030c05061003060f0e060114061c051e06010f080a390201020301080d050a03110f1305040c02030433081501030908 70
    0x21042551034500c41c0c6961440340050300c24581c0000e085400b15690b4100540e440000d8103420b61301070350b6a003400d041604160016a04803944018041d00d1a80d551804600038060b07618224108030310101c0070b41c04540104015030203055241e041e02802491480c01c80122040d000c14610018103084051850110218403103045031111103c590500542c9000540b1030f2169091364140d44034030301a054500c1990341d0101d44a8105148000002c0350b17012890088a20110340450014090303a0300b50074101d110301c607081d4010707042500c082414450304645820300c0c540307584a10040c1c80174142c41c01c410312940401569440c0301d40001c510310350505403881d0b124130030100c11300d05200d000503103500142d202b03074005070005070046062919040248144092980965802e045401d00b50002082130725252140310713048007581c1c004503e05880d200e882d2848090707a000f1940d4088090020403815590602e055004000759a912000d9152402c100d10040110485880c1050f2401c01c0100c0028183c000701c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 331603570 1250 331602320 331602329
    0x50f061905010e060d05100312230d060e0702010e190506040206031012061a10050405040902030c0405040303020901021213270e010209150c0a061d071202010e0303070c 74
    0x1d945104490380403404c00d100720740855060b2458141002200c0300e910310180203880c41054401042c0d100e010301103507200400140007aa4840c110380d02d0094985002c020b108580b4500408204150380e1184010001d408071101000360b515800c048254440070b200f10810401c09007032017620318100da1070702c3e235031850000e000a003c1c0c207000000c10641c0903107081c1c42d00240201541c006003009035140560152030742100c0c0690826801084d02007502c2d100840c403c1040300da82e10344c1c0c01e061610081201402c109413080c0d03003600425039030358410b1301c840c080d0350700c41c0380aa10b001da51144034000081c90000b9040400c4140d08042c0030b0864010720700200503003161400310160082400ca0b0100036003030901c0e40481d4000710b2804070078030300c3d6002c10b40103800e146004a810007213204421400390701720310a902188a4a80014100c58001580380c0e010010212052490a0380002074603151854048983c010001c01d10514a0103c11507903c2820300c07034496000d0b00654200701c4156a01c2200141c02e018 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 331604820 1250 331603570 331603577
    0x503042d090207030203040305071509170c01031503023604050307020d021206040c090501060c0c0306020d090215180609100f1103040b030f1f0e0712050703050f06190501 75
    0x10783c1402d161003041680c001d10380000c05e8820003543c4400300700075039055034080404511041c0c80028280c0540342c9221009038410013804102624000445c000c00c2011075000070022035400210245c0c90340701420b5400d600400c418000b01c040d01011040d4055080c0845810390194010000060004000d60300e5081e8103032000b081e980040d10024070701071a00b1009408521032641007000f880700001c41501110b000050070401c41e40c940340201c0e00c42000c8074001d80404041403040002801690003003206002890000462103c1d690001e41c101c00640e6002070700402c04921001c00c0041801042117645048451500e041003401c0801e010400f0b86404070248040060740c4d40d6214080d10104c940340344490203580d51162202a6180640c000f82c40301c0d1610404400012102002d12130003c004016800441203101c3c90031900b8061805d00402c40010803044079001d2400070507034020310f80198241e407400310b00c1785440042c08507968030080c0800d104011031030390100f1051180c42c0f403034142c4d2800c2c40c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 331606070 1250 331604820 331604827
    0x4020307141e0c0a02040b0406150c060b0613090c030b18040201021002160b1b0f0a050705030a030504060506330f03040b06030f030708030105040203070c050105040503042d0902 78
    0x100c44a440e241c10300c251400b81d0002940415040300402c01e122050b1089804002d8500340b0004e1104840c641c1c0900055810100d4003419403d01410800c10f03024803910001c01c01180c0d40d00422807642240c0d0301c1da4040544800d042c00b03811214026040d0740c0b905c514042244103051000141c400c4100c1040712000400240800e040d64428071140d8407954003080d0941d5518100d01c005000c00d075084106803140081c3e44042413402e5015041e60441a594441c0350342048410885c003140e6501028000341800b20402038280060014009401c0110303050700c00240c031386050b007494819540d00806403442007407d061001700c540286d9580d40c5c0a0b04a103840100f1402d0b504205040510988500441e040e1000c0104000c02281c0c0300441d02c5501c0503000d03900b0700d0b0800c6000b2039480c0140b4400505441c402d0006210604150f80910760103c1c0d546000c40300b6403c19104c80c0e0031518152816902508001014400a09410800624412045403601c1c05c600d00307040c100e90812803030040401d000d4000 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 331607320 1250 331606070 331606087
    0x1110f03032815080f030306030c09061c060c0807260903120103080307090509040816021507050609060c0a140d02070203060a02090102100506030a030c050f010f020d0b0402030714 79
    0x41c69181e003a0b01c2c100003001160104507180c4520000d901c42c1c08100e21803000c0b4900c4480f8040192406180d02400400c1e1603101c00d0308108500c00000c4c151900a504aa02d03c0b48204031003801a1400e4041c0c60009154000040003c0444200610300380512005000308280f0114400c100c1e400c43c1d0038081c4c0d0b02d0f0a1345402078042d086100d0000d04c2c0c200d40070a003001009200d9000001d5000e00502d440701c0302103036664424002d1044c41140c0140180c481800043e605401400c51106254130080c84e0b803201585904d00ea66160704940410b6907230303501c030344204403c030242040a5178000a5070800c50341002400c58000b02800210691205000c0c004640390b00b00c0403980e01070394000c950040988400e8038002900c10001e42082400310300500c070f15244500e10303d07100c0c0710300343c0181c501501501a00d155031b101950400e036424400c40b01840740714003411560f4001e224a20458140241c0560381e1040307440341200b900c191180c0c0d00e110368410002d11809070b410400045003289511080c070b40760070f900c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 331608570 1250 331607320 331607371
    0x1c02010810090e0705030105010504060e0a0507021e0a02040e06090a081b1e01240504021b030d0e150f070c0503090406030c06110c010e040e010b1e01110f0303 70
    0x142d00054805051688841e81c450001c145a0213590068000308896aa190200000d8030400c0c030071103c2100d002c1e404541c1c486026000258000c0310742c0121802030754500c0f02d03502440010856062543c01203ca800218500381c05100031540a0500800705070400c02961030300e640c0c051000030f0a10b10000f4001d05170034025010311035020b0810007520012002c450304801f28010402c5040015441d0000c0c5403282d8030401845240307058245e50301402a4204001e10000394088c0c9050ba0040750b0030b0640c0300900500304000c1001075141c030008242512401d0a80340f40c21100c1e403102028550031001c0000020a11030f0080e032001507454100328500c401d007440e500310b200c2c0d0f925246c2c0141c10301001009200340100142c0c116021a40c922501c0000040c2042c0c88200d018030041c006a400c48205425281c55040f9102420b44200009204004540010309100848543c60500c0e4140001e82da081d6130450000b000301c090b07440160840340702118600f92244002001c510082c40100701c00c14a1680 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 331609820 1250 331608570 331608601
    0xe030106080f06100f031509060207020d060b0a0815070c080409060602070e0a0b030d03050a0608100b010e09070e060a090305010c0305090c030d0206130602091309111c020108 77
    0x308010703034140907090381c80640c070f90f80e044440348060842c645000442c804001c030f141c0d0480350860120b030124070714100c002000d8200800b0541c1e02c41d80038008031001daa555800c2405651184200054941d48a02030003100f49450380140345540003188100f10f0102d80ba007209074040500d2429001024840c034100440340a81d1300003414592400e6404102c5079000204002664001d0200680c1559904004001d031303140503005035010b8001d80d150807140c034000c2e00403941040180360046001030700c0e56005441e00c00c90369050405280c075104541080e58000908a00c030410035103820b1003a280c028805400340c8180f2880c18091040011505c103600e200d100c042029590040c0284000c10703425000070040e000545400c500e40c002d201c1c1204007460001342d0311907030100c070360003034952590b03040303440755210448250580b14142c003005612210b0b035550f011600d00400216001079451403505000301e480100e5a5124080c14000d031030400c0b9010518a1100d100c0d42c240380492080c1d6454003000c00845 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 331611070 1250 331609820 331609829
    0x108060603040618080702010318030f18090e01050f060d0c060c0602120114010806190506030a060807061808060631050c070b0a060e0403050a0203040b0a0302030a0f110306010e030106 81
    0x713455001d107010405910024450f581c001d983c180100c0c6000c2e1a2001c8588030007400401050f002008500b00c81e00030848401911045003003400203907541e05849050300c03500d86926007170ba5510030400c02d403150484e4081c1e41014041e03c041e45016101d0380d0740e1646002c1806000107000c005440e2a0402c43c89030101d404101844a0000031560b40c0c401000c1900981101c050110300003c00091207400c0040c00c10002182000d1004000340c50081804580c1c0e001400e8400c07520388581000c078888608104903002080299180107900640000c28024082c4942040d03469402140a100041d50b941024440d0038840381180d400b4a80c5a01c6039520b108000c1100040440c2000200224084404050f00d20f013401103501b490955100b488013000c42d407480c0100241f1b240d2020114010910401c0500350450320b40c0103ca00d000d4440b0358042468005040c0340e80000c1d0000100038103a40c0d0b50080c05600d070003840007884454404554000d2a010007011181003184401d80b01c00c09550940104c80180f = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 331612320 1250 331611070 331611101
    0x241e020304020d031809021603030e2a0d200901080309132a030e0f0313140112050109060f1203200c0d0803040303140405070501050f09060c0a020a1401080606030406 73
    0x12940a4000200d04540010507000300785002610102600081380707541090100000203080107101c400da40828046400785181c00801c2c001d04800040c8006a58010b82503c84424ed600c0d41c1c10749007005403020f0160040c200c04c2d001400a00d1f0b0a456074806540d01d0302480002061510721200d80c04082480c401450600710224481655510b805500c06c46400c80e0480c241c0d0040c14500341031581d00d104002181d0090001c0314400c020100c0c0c00101c3d550303080814501036034142c00192980050390b000381c10807912696100300800c13410700e200c41e22074000c1840a055110003103c42d01e000e0042c1c845000b1141c000551b540c084002164207024000d4180030091010280ca07030070b405c01c680290012607086010a140200c0004807048110b1780c14480d40c4c1c010000c061160030100111410341007080241ca8a00e010300400809541d648003601da020101c80041c040a1400d00404c4080142030388170001c20701c0c41840c1c404042e40d002c4e0880d03074401c5056034500c2d50b130b403503600d401c100601040b1100c2003031 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 331613570 1250 331612320 331612327
    0x503030403120b060a030c02120c031c096002040f081b04050c1b030909040305070501061a0a051b012901050414010c241e020304020d03180902 63
    0x10a0b010360120009003940c1c1d00311b03914000c0300b054049c2240b00700e010150b55035105024541501504546540c03003286000408a1985841c0e035400071412900301c1c0c119078036401503803102040c03003c02d40d030441d8924038a40c1c0c164400414614590a1210501c3d20040c4c94058100391014480141c044a001742212004003002564a00d11140c80e50034810100344030b030000b400d0140c114509030007070038043c1080d074041c2481d10402040d5244803120340300711841c0c1408240301518031903a40e00b900030300c0349000303454041e0b0780e192900d03005c0c0c00c40d040c6030090243da9a5460075401c078281c0f400107641c0c076820b00d03041c85552007070282410415400c007182501030079070801954021016154400c3d198820042c6614090381212000669180c051801031900c4505640e001049542c41059924103440c0162500f0103020420301d002003036002c1d040400c00000744c44428000050b51006042d5201182c200e204601750b09150b8001405031411000c043d08005841418a1030310240902d100000c01c0003650440d035 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 331614820 1250 331613570 331613587
    0xb0702010507020d0e09180d1101061514180406090608060a0507020601051210050a06050112110a0e0609180709050109080d2a050a0308090c150a09051305090105130503030403120b06 80
    0x9d00010719200c03034019400d1500020b0b200c05216440403c032001a21a000b50240038100350703000350400c2504000e414181c11182d54070380c48610880d4094100083c021809504241082c1d143c014080e284000c4189804100038a0b99404100281034034401c840013089035401807550392808602c40300d41c05020385820240300e0440c0c4944d000404840f801e80755110f100c20341418040494a0345604040c03540002c1181412107403140400c1c00c0060f0000384450300b80342a9a0109028400007250800481d180000340300c102c1c0d80060811004100c246800d8800c28144107815490303958200e410414402d00552a00711300c0d6514660503282e20003076030042203048943c14030320764420f1b980e401940800c0c0c50070007040c928030300413030300c40303407040c0094480f8034000c0c1040602c190942c81821325a003009000b40740030400d03035a10300c00e04030a9402c1c854082500e040200c1143e00715680540810000c601e8900454002940481031382e40c41500b5080140c10002d50707081c848050725618182c7c82c3d024000240898 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 331616070 1250 331614820 331614827
    0x7020307230d1101080c0c0a030e0f06040b040b070203030423011722020604050a06030603020909061306020a031806020307032729040b0702010507020d0e09180d 71
    0x34920000c1c485180d00001207806000c14207400c5600980310043d002500758095010b040c000d070f000b00c41501c0e821b180c450041c618508000c1c5204044000910454001c9814030b03000c10100003042045840901d890b02d4506412064030951150742501d0102140c5c101c10b40d501842960000e04c8045c0003c0701100c0922422400540d0622685001ca0040c00100c81c4c0c60131070440081c440e0b03c900708580ba03440b07507449004070b071995050740407039000004200c04500c0b91150b140700b0700200a45e40f00802d05034214030401c006072000600441c8a40d015608004081c0301e641c506c0507a040d081840103940b05031040084000d00400c2c440c01106c1320402180c481081460390003144141140d980c1041010301c48010811003503054801c0c0b01039440d0f1800d822003c500e40f08101d2201c14003100328000c24a00d401c0c0181c9800c08100c505541c20b00303071041008001c0c0d0302030180d20f41c0310720584003510b040318108801902c03810b081c1d05903d0203030714140002151058207848010b000510318044070b12815003010001c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 331617320 1250 331616070 331616099
    0x1030b0108060a02031b130b0c1f0905060123150c15071e030f1a240f070f020415091a06030c090303040902070b01140d02030a020f010507020307 64
    0x10741a00c80d54001510900091003603a008010b441c1505081e144030701842c0b41d09400400b10b1103001c03d807a480020f0300c0e640b00e030002c0000b1680390700034060f00884043d50358482070607066505c80c00d9040500c0c44000850104425040d186603501c20502e00c800d219000704d49651012101b6000000b03030300c04620581824016101c020350103001c4030082007a01c3d149031070500c1c040d00c000c008a60300000549880c1030b46003074018000264540001c1076040c2c44001015a101820100500d01102000c0181420002c00d042d03240e9a00050041341d140340002c0c00011841940262811060046021810094042c0300d200f50190020814010421860b20040301801b2501c914000d40307207001000d0448080121400d1210701c0010700d01401c607521040301800940c401d80c403c0341c2c180400c1101103130840307491020340300160145854070000d42c18490341913440702d82a009184039214010342d4a0042e900040d0034000142e041e00c00303540d0092020016500c501514200950601030345001190302c60120050 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 331618570 1250 331617320 331617329
    0x40309120501050f01080a051203090a0204051503070b0a09090f020705030a0e0a0807060c0b04031b050102030a0b010c020d030309080f1602030706260702031608031602010e030a121401030b01 84
    0x81c1850346c1c0e440300c0c1a92006120002805604800c1d1111410b42000020310b40c80441d4400b91101c4a5151b030004040b034904413405004404007078001d480c1c50804100b0203029001c0408140e20b0b0070000e080140105210307129a030754262300ca09043c83c00110030f40588180c2c5503c6021a511800f08039005480e180800706482d0042601d00000280c6010018009007290040c0d29050341c1c208042c0c4900342c103408028021750500c007412440303002211800d0000001c16010303100050312800d01d03445d0003003641c1c03401d08007070304001030074030380b0005a40c50500303030700c680780e8142800500d0f014945000c1c1c44c940150b203911a64514041000600030808134006e2049502c00c505958000f9282c10068403052000d030380203000d064810240c2c40312003010219035500080503004403410f0004c040d55400a4034441d620440300210003200b480f101d88840e28012030014000c0c0002c2c0003191002806599a009127a000820046030300303c0d500e5110309903404802d6940c00068904000d613164140255000428440d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 331619820 1250 331618570 331618591
    0x1005011401142a0705060c03070c0e01030c050103200a0315080313050d06020f07030905010809150c0a050f0d06180209060306010507060b030105070e10210504030912050105 76
    0x140c42e0a0445030011580c20480c00741411100d241141942e10004820050f40751003840b03007000100f180d50b100c40103440030345265801941d59002601c0c00c000d410b1041d50040780002082001800002e081155190545130f081c0380014182d0a1030642c1c1005201c0114030040481e400568a40210ba054100ca5900400c140c940000300340d8400e0724070383e2481040305501d041c8400382028002403030504034260110740905409400c0a44198403410203a116a07070031800315084950810082d44c00980b0198081c0070007002e00800c0305013504600c0c03030890091141c0700c54140003072400070ba9401607042e64100060424281d448503100034113403005242901074030b02c0f5850016500400b40f90507000b202c107031a4000c5c1495003551142001503030140c000751005c03113040b42c494000c5c402584092060707074443c06244d03681149000d01201800581c00303d11152101f0803003039061401c0f10240030810b15a20f00f81c0c08400264559881c01d0850382e4200c2c541140807180403400e00c2d2001d1060542155010307604044 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 331621070 1250 331619820 331619837
    0x100603031e020f03040303030903140a080f012403180c0902040f080d0905091905131104020a0c0215040e040302030d0c030b03060610110106170c060c1506031005011401 74
    0x600c00e0f40da500400007810300d1940304201c03d00010344aa00304016203481703401d00c2d0751040a6010b42600c80c1d0002058000040d03c00020400800403140d0383d58010064182c026800c08800c08a044214000000f11018036848481130f0400c0303215448101c40b5560005410542c0b035482e0981200030350300c2449101b05100c41085e000c9172103400442c009000d02066201d08503440d01e040203014410000400c2c2c00391028159030b81518159407409000d1040851070041c00350078030359140c40050728580c2103845002c0c501c140010031495401c004040d140303580407200c02a620168514412092007650890340058036214148000c00d500003007c3d0100c8403112106008901144c0400c400b224014103900c0c2c0e141d0300100101c1d0f600e00f48010a0010040c2924203029200d510180103401d6a0b8654004c000030021034441085405003401007180210045886514004015500e50313950310032445615040310070b0034089681070317500f00302400c20188060800e000e21f40e5a80c2030802000c11a918007808204e009 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 331622320 1250 331621070 331621127
    0x40b0f0a06050c1e030d0c0e06030108150c18090a270309050d0210110106091109010315030b07080705120f0702150708070e0307030813240e0603070210060303 70
    0x1080345889a005200085040c45080903101000e03115201f1070105010030300c2800b040c15100c040c0154046c001e02e00060150920440c40442c41d084010264414590300340306280d070400c03c04034200310303130002120001c5982c3c1b50100c00038000c080c1100700b580e51000c80c550044245803200b0300c00b0078075402a101c03207251650b95420b1201c8103003d00b500079403081e00200c0717080380207005205003280103881c440001007c1c0d4032031b04140112180700f69814902800491080e00715a414040c4c15034406041e034a40e0562480c42e40e501c04032220250810092155510004141e0f80c46282625009100098059024104841500e50440064429400602540480c000100c1028200341e0040e030866603106a1340d50b4242c01207070809569000282d0600a490000000c54980307000303801c0825107610060342084c544410252003461240b5411100e000c0f24006500003a0400c031900c110035000d8402d699a44d84034102203080007481d020320b0800c5840d001e40401450b9020005107c00160030b00d02e410180950b = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 331623570 1250 331622320 331622353
    0x1005010812071e0c181a0424030c1802090a05041e110703111903030e0a0204050c0a03150e0109020f0702030d110d180b07060e030d0c02150c09040b0f0a06050c 70
    0x444001c00004400b0700c0345101f4106a4000c409207440740300c103440d100f049004080144041c40d4400d803070f0424948403d1180510b8142450303d400071500c811885e25003d400815440c045600c42d60b88615070716076115043d101c50a4100c1d801c05514002041242c2e094054403049400c020401d400103541c0482000515000007801c00120100da0441203405005a400318003501107090104c00d11301500c2c1c42480141ca442c010503001e1030803102c40c0d94541d90800e0b03000302260411466807410000100080180360006041181968101440541d45521a507143d0074548903641001b9098410107040b503040300c0d40000420381108900060710041018003000f21109108604410100b001c6030070100040409c0000800c1424480c0001186594040540d58116045562500c0c0199116003103010501c0d03040c0310720a800b40e0032610801c0c50f4108454000c5650240540d1240a41d550700c00c62000d665850302910700100c0000c01c840d02444e22510300a06981001140103a10300c201c80c440b2121699 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 331624820 1250 331623570 331623581
    0x1614010b010c03050909090709020703020c2b06020901140708090f0402040b0906070f0605040b070807050a09050910030c081b0301051e0a090b0f091005010812071e0c18 74
    0x20944e40b0b85052240c0b4108020701c0c06005080c00701580314510b400079844110340043d120890207500900590386101d024000100180d2a11100814290072255960407202c8058039000d42c002c1001a1154000d200507588054403000c8070a030000046200f81c20401200010000b0542c150340f070181010102c414030050340514040e10b5801c480034041c030407040c02c140e0098618180210060409105543c40b00821504240c0f401d440303804102e010071801641000115400088502e000d618181d49620000c203d45154050544a064110045590308001048032409140c126104032000d0303a8502c00d05980e02d6002c10f180c0b240c03501c0e80c24070060914044c4541c07449040300b1040b0451000044400b069802c00007080310042c2079446c543e090100b414042070390711881503510b0140403820648185841c01c4440807003091120704100060000c81004508100c5000340641110f4482c8400d20f001d80d20703415155218400301403050207c00501100c03220080495032410b90140907440030380c41e0b0900f03459 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 331626070 1250 331624820 331624823
    0xe0411040c0f0c030201020f13060206240906010e040f06050f0a080c010f170103030c060506030a0317060a03141e0604050a1e15050f0a06030201120e01021614010b010c 74
    0xb02e02034400d80800c0c0c012481e00c22030f9403091000518040a40f50300507003d400507030101e001c459515000f40f00b2580c04000094018440400240f03103070816260349150507001020b100c2c011800e51011441a0340140240d00b50a140123100344062103a0205103002814207119240c1b00f208102c2c030b00070035800e100c14800103035210311001d0f24071203041c01c0045d15462100b03c101020841ba05592051280b0700c02119800785101e40c0d100715110740360b81446419034a01a000314070940040d50726000003a000321b000c2c0b040080b1b0864260840c1d40e00f0b030019198140c15072010346aa208007006130a008004540751101020074190107414060450b08280d0342d5500b106d0040455000080b0075020400c40301e00e07070708803c0c8d8010320700c1081c1000ba40c82c07401d4030511801c401ea520ba20350003485400e0142d081c0d069846800755208028840c659000200100050011010441e666458007020410203404440e6980c5a800014442080c649020404404291060641c0754a000c0c070317000d41da6104505142095 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 331627320 1250 331626070 331626077
    0x5030f100b0d0b01090c140f04030c0611190302101a1009080706030f060302220b0f300111040e0109050c040b1b010606050d0f0608150a1103010e0411040c 68
    0x81c0c1c244000340300100b403540941b00038003880101c3e070580507440030001d101d54040310324102c1c1c88600d1490880d400a019030484002e0003004c0307100c0700219600203101d045800c0544194020000c05040a03030404500b007401c1000d0074100030784440846c041c40c140b00140c49094603100c20a40c03450000315603594607030013030b5010f40e00700f1402000300c148650030a102000f9080c1000401c2ea40d01d0b8000342c00d001c0c2c05094204480f81c00b2400340d10086981c441c03000e01c0074060740d03003071540d105407000540070754a403442c0c0c449214240c0d1241840d20045030700301c035940402c460003000380f16904603610440350040d103e0b15450381d03142e00000c2000c8019004003800303620f40b8090f20742068213107107011005400c41e0043d800d2202126070001500306003402200018440c0391602c9a0322501a180c402c1a15013032403001c400c840c1481004c0104103c0001d0404004080d13004200c5c0e1625218000d10142c0480d03040250b0400c8003200210b0349205210001c0e0042d4411030f9484911007a003003c0c0030503134035070b0022400807 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 331628570 1250 331627320 331627343
    0x120f03041407091e0b0a0503120f0c0f060f100302011d0303130b0306030c090609010501050304020a08010207062703020d08090c0306010306020c01050108160306090c05030f100b0d 79
    0x2070340200030320441c0240c12041d600203035116540c6a04441484d41d90414041d9001101d07000302c001d07031051140901040c2c03500c0c40420304240c04280d6411301d02030948d90b480000502800e01940c2c100682d400003080c0c2c025500948040110b0641e40c0b070301503030903021a01c401c80c08a180b554400b18014100c6c2d0341a141ca4003016060007202c101842307160407180d0503000070000d810780d1030641503241000d4181300d40380c0c07512403c0200a251a0032140f071070950192034108184501560740391142411100c0920740385503640d9880c80412687d03001a0312009440d030002c107400d400c11500b60000501502183c1e40c500035006950401d054080c05440c0150241c0c00046a40034120f1203080d6481e40580b40604840414200102091820b1b10903403080e80c04690104818035a80e000b0f004640c0140360420041c403588400b8003039500e000b1294403005100950340c0e04040c0c1042441c0070300400802009059449910607403041035141e010245d0400041444c10110340c016140484090ba503154000711810b61 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 331629820 1250 331628570 331628573
    0x81e01060509010c0b0a050411010f02031c2304030311190e1906050309060c1c0c030b18060f061e0304020f1507060b010903080712090306050108030a02120f0304 71
    0x800d903101102c80c2d81080300102058000c100c0440946000398011807001440e4030300b5007011041151810411030400003500c3c0b00003103540d800420b84400c121185880801d210719201a18010899140c0450f1019000404205182612104584214083d4030300348280b42c0381c1903007001d0ba4400d200c0c95403008500c8036404c95506210380b4650041c00c001520b4002003102003250803c240c40716a0151000410000030828016000c1c080103801110003911035040090b80b402801e20241c1c50844141c001c3da8400c940d40410f1b20940104009110141007501d4010b040791544450080803503000340510881c0b10007201504042d41141c103210b000c01a4230183c19510004c824003580054004daa1106010242280607540e5499940344900e0004d08503580d19118070706107003544c91802186051000340c0e40100089820380003114525603002d1801c0e02c1281e41c0c10420380c1c60b4002608040c0c601483c000c00402d500c41d000006000e0b00005800301c0c1d02d048002c2c40c504080340300301c40e032951004505202040 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 331631070 1250 331629820 331629827
    0x1120203040f0b0901020901140a140705072103020d02120d0e030c012a0e030304090905030c07080102040914010b09151209010c030507020610150c0c090606081e0106 73
    0x607082071189002e82001581901ca408001a069607404d1a0f6580000e40804039a0402c05e42c21800303480d10100740c10200002d1000d0032160f00351040890043c1c0004c2c125080000510903000501181e801e02032410440d422206910300011908030058828014036500f9903000040c040180041032420525101d2a40d4030000500490036080000f484180002410340e1420700420503d80403e15038004100d01c0c50307150b082d008805800b20401c0c03000c0440c3c0d01c085624084100d0b004c0d1005035001144500051070014518419070751055002d000d50380300414140410b4000740b04641ca40641400101a00708080050303c000b8492205860310401c0012000e0402080b040007105401e0b025a08102d11704130041354812084425000995443c6a842c0032a41c251041c290000c0561005081c1440d104d44040e0b01c8000311f01940c02c132141e1032075480c0c402c01d2140c01c44002c0954444006110b895a0704021b00181605014040105003114000b400102c0e94050482400324203503c0f001d016460b10f1f0054 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 331632320 1250 331631070 331631077
    0xf050c07140a090504111f02060c03060d0f050f0d0315180207080f280c0b04111c05010609090f1101030b180f07020f07030201081003020a081c020c011202 68
    0x95000b25544a00098065041c490980320b0342c000c250000b80a0010402c000100d5182d03400f418140a031103504024940e0f000803016481018501400d550351941d00000c0c4008081d94002003107900c0d289030b044204040070510680a0480108443c60300c4030707180301641901c0001c400d01d0081621540e040140b5281c01070300382a401c425a400528144032a10303003041ca60311068500000135400280390f900820b0302500b40140401b01c03162000007240f0048003d05207500382d08042c1c0b01c00060404182803003050781210000030340c024010b6524018103003403401c0c0740c031940600341c071390707500e066000511140580500c5400540c0314002041e49410b503912951054080e0001604155882c100225039407180341c1d00c1c0c2e4401e01c1d005117080c1c2510341701480c000c0c0302c40010f04041c1190001190300003801800a200000d0346d6090130710003050b584112418100c82c055900103540301440d0040000c040d68007190a07501c44410035010318144071b500c58241d0369403a0620195001480241505042d00d07400e5024 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 331633570 1250 331632320 331632359
    0x10501050312090a240905030607210e0607020a021f0207030308150d0606140a060e040209060c19030206010e130b071107060302180f0d1101110d030605010f050c07 72
    0x4c40c03902c03641301d0b22403442c10740f0b030005900350b005016554140c2541d0440d000c2001003c0440003007005150090380201510300d44e40c1081c0800c4454407074003103602001c0e0452000d10051a00f141c1d000e242c02d1a00a65a1030f0900b410390080c006080d03031983e0044030400c004070f02105900207001e4a450740e50100d494000042c00780030008444080584039a403111404500203001c0c880105102e400c00c9040e80b4095071000e1030502c0784801100400103581c1200c40c601ca4000b04450040e00c8128482c003044041c841c641010200340100c0000c0f20f51520040c0784410664025030803640141e0701c0300046008007005a6407620400004000300303002032030820039140e0201c0c0c03526008502442004400745000700079000540840d4000c10301c01001d104007406a1030220b0210380f5003500fa08000b011904e00c0e4502e810107007081e5036507071135400c4c40c3c0d019004000059454000f00c8800480900004000344041c4c01460700190742404103180355445002a02c05c1e21503418058070141c1d141129a405106040c0c54 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 331634820 1250 331633570 331633579
    0xd110403020913140a03120e060f0105040b010c050105010f0f120503030f041406070c030e040207020f040f090803010803040f0501030209010e121e161d0f1b0c150901050105031209 79
    0x160090101d82440861712092003503e0f42c2e81144003401400d41581c0d02c095800f0010350002c0100031100000e40c0703066044134408d0303030000b8100c104080101d07810080311030003034010360810000141d8510f1710400d0500301e80c1c0505104421640320b01031003070300018000c0080c200383c2c000e03c00b241603140f04100c4160458400d48400100042590005d030900c00d049814401080604100d10145604030719402d0300884102c0c3c0c2107203041c060782d0004140c02000800b5500640d5200c00c02a8103940c0c5074410b500c1103400034406c0e0b850b5a035440d40181c2d258094060b07540a241040c000050359401703402034a102c00c005031a00c1c0003201200040c40041c8254000715271503440703400082e0f00015110510420f100040001030440296030104081e4003c00e1a8007610660000794100580c800407070b2581608416420301000c05c60700d4180714810180020101400003250010340c1c809043c600144418a80350400c0304c0c1c803070700d58664420074200c0b0001d103e20303509604019442d00304034400304014a40d0440041 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 331636070 1250 331634820 331634843
    0x30804030803100306060306021902060709090e151014040603080f030910051603051503030a1103190f120902030712060212070e032505040207050102070501050c0d110403020913 78
    0x100e0356420750384564400e81d8250f80c0002c1d07924407242e01020440344ad122500040c40e0314140200c0082100407603205072420a5500c1145c56095101480032032074110190000c40110305001076041070721485403003030103200c204030142e100890400e8012501100c0d04450344900b002c0c4841e44103000c641c40140780d00d40500844d091303c0164802da00c0307840c1c0610058100203a500d40000c030094200c640c003030070307400b081c0041d4540049565800022110404414030f1f1042c100b1303d608801c2491070090704101081c4103500d66050f139180d0351000e40c034880032415980765078044000d4400032080b07401090300070b900358100040500125a440d150441d62611901e801407402c1150340102c0d0040c41c00762208000100c00e2040940d407071508121107510228061980522100c0840b02002142e015128080c0100d030007140c4103050003000e50640e110307550401300074401440c1c0300c0303000421680151915681540741185240260108109171000c0d40c1d4003500c0303c40e10361100c03100000655511002101c1198515 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 331637320 1250 331636070 331636073
    0x2030705250b04030f080c070f09290102100c0203071a0f0912030601140c1606110c0312030402150c0303160f08070c02060c1b15040308040308031003 66
    0x10003611064880030a81658100361601d2141010000d0364003041a451041c4000d00c041480e80701d0002c83c950340316140c0340d80ca00070250f1042c2009160790189c2401514000c000682002a0304101d00d105c001c40f500c28801107540c0e008442c0003281c5480240181c0c021180e40c3d22078000c65004a034003009600482c1c1c140140c90342c03055200b4140c0c90750f04100380c030032a060028044801e10000d0308104400b015080303850308060005100d0100030b0046041200700f41d5625408403241044821034400300d800d4036010103c140250700039801c1880346c040051012035202082000c04900064001c00c018083e103090400f10385805820742010344141d03840004095003006203002c800003460240700c0c080203503460b0715044070000d0f12380e04240c900500b84100140d94201d0300f036000007816882001410714070561046400071401038084e0441c549410b114600ca0845a40e40c500042880d031681103604032040b881c0c6104001d01805584401030054030b0500c410f200041c9a0405140e1181100b0184a12103035603 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 331638570 1250 331637320 331637323
    0x1e030504080c070b0c07080d08041e020d111e0a090b0402130312030f0b0f0405090c10090317181c02030714130c14070201051b06160315051002030705 66
    0x1c03680580e500f42c500017412205940e040c0201002088040041c2c03410b0040d01c980a00341d000c000708010300c0c55040404000d510780210b143c031103501c6d802030041c941100f054a84540c4410b80b020076140f003000007101454036014142000c2104480c09446000d03410303c1c18100e6409042105812940a0b1f002d00c14150360b4640f240b0110300540c080d26003040301400106000d0103d13208840744140310b074108445050141c80c0c3c0c561136240281e0603580003440f5604d0130485e50401c0b15150205500c1600283d0000c81250300901c1c5030705032030040d200110400100b06a0b186148680a07004c0d2016a1100150f81c4504e0440002c2548858180c0700d05008030b071540c000f908146481c1c0014030b5001012140034200d05040008071a40c46000104000f04160200007070301c4c460100301070162140700000c0c028116481070050b1400c0980d03404503280c1102c0300e00c039002c6d280c01007241c240d142413502e1080c500c80f00d403180c01070742000d0132020004152103081509018191a14180290a5101c20032507030000880 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 331639820 1250 331638570 331638583
    0x20c1003110d020a1103030606160302100f05010602010b0402120105210d0815060703020c06030c04030f06050103142e0207080309010e07081b0402160f0302100c1e030504080c 77
    0x28002c0d0042e503900c5002e0010300300e4202c40642c0c0d44d07070340c2c400d004000640c0c0f030b40402c490b540040318540b0402c500c0750b0326049140614440c11190010b0404110b0340c0341800b20b800117030590303049400074401481842c042c4001c030b02950340c52461a801e05401000b40d03081c000086401c00b420104410b1000032104402072600900000340c60000e94400108408040d02c0241000004422981a4640300080e207009580710249240940704690020104507440780e4a000c40c0c001715031200d0a00100030180c1004401080e00340b00030ba403103241c41006000c1000c0c011a03050000200c81200c0d549003596141a01c0703501480001d0b110300c0950800c0308201080003000994410608440080307220f00224030740508155040d4062121640000400780e0b13190400560540003c0c0c0c1584c0c01070722000380ca189800101c50004005d090300f03035001c4441082c59404030b40c19031035040513142408030028036001190706089030a0038022240e070700302c0950082842900300c00d4000d405000224241242c444002d403c028 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 331641070 1250 331639820 331639837
    0x1215030203030a0f0f08010302220605100305090106051f050f0d0e16050109081f06030b04030210060509060a03060903020a06061502060a0203060a050d03090902040f24020c100311 79
    0x100f101030014011944404902185611451b120183d54595408100d5917030000070b9510088148a2520100001c00d40c4410005d0400600d110341c4015038580140041c4801d40d81e8520319402c0000c0070502d420121080103118108140a20000700704c80c004890540100c40440c4000704200200b00c0c059540c3c1c000c041d45215000090828901d106659404460b2190b01003414400e00f0041004159000f260360701030980c6010740c1e07140600403907d02c0700041440760001403000110340148000d00da0b000659000b407004030802086015120300c10014000001c440c81c580c4006240300c1400010f4958000740e254074824012166011240d0313554a00740c414a410000180500039801ea1260342e0401c2280e80000007106c0851450030201d01040c0010018024180201039144902c0c00701445120f04000500421204645458076200050f804174682d02c610b551f030340704950301c1c090840c0e40540307034a825095a8000700a030707207400000d01015000000040c0309156590f010040180140801800001d = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 331642320 1250 331641070 331641077
    0x8040f0204091505250c050a02130209100c0c0605160203060a0f0b0d0f0221010507020a030e01080f06010318021c0204060e16050f090607051b01050702011215030203030a 75
    0x504003c0502141d50080c0030f141da1102d2250598550901c00340c0400c0800418030b8401108400381c2092031410741207890094211100c3c00c96100000c01c81e03800b41102a00407106100740160525013155040d0f4007403806002c81c03011007403c100880c0103100503e000103107200b45040c01c0b20180c0005c4d05042c4100c0300319209580340c4081004010032481100b8458004541d014041001c94594510320481103a00070b014110102c0c0b94585283c651a00c880003643d01f0009000b5490034640c0292142e507409421000301e503a041001c103c0f503001d102181c0c400d2450100041043e900c01004401400041c043c140304092031003201c0001da240d80407680c1c10044541c1ca40c500c03504052052004548059010081e24524542480105003140103d2034451a0b246840c0362200400c20b803000451180e106225402500080d00314204140401c0107281c00300d992a842110018510055405100b944070081c00241035091480b480b031010307400745442c004e0b504018022643c07070703a0100b0710790f621842900011 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 331643570 1250 331642320 331642343
    0x90903080402041116060c02120307030b0f090411040f0b031b090a021606090203070e011805071d15070b01230a1a0a02010e03040f0e1503070608040f020409 69
    0x82d82024020b003080208002c0704030745082d5080180c10840d0381004c0c80104200d442e00600e1784d0061007040124590130380b87c5c121690340e08042801500038016000c2e858028181c5070014945450a08101e034841e03030300103d0600341c204101080100411000300080a015515621080144c41c100032840501e080d00b0340b4502e007140004100942c29500601210030329004000b04031680d045440c81800f45a8003141c0881c00fa000f0b440006d05040c15a04182c40c104038040c00014034218030042c0b00b0035070444810400064070b854008941d59441207031076a11504a0001c03a1702a820301c00030345007000e5081c14a9508201c02c80d07458000703000b400c0c5c2c080b140001403007403a04641c0c0d01c129016801580304441d00e1155514108110005103d42450140054004120200b50f1030003904111010050801981c0c1d079152104c5d0030280701e0400d4000c0d11403208003400040c01d0720f504581c104041d0b100c004d00030100c40d40792441c12105034100900482d1440f86d40c8820000585a40c05402c0c0490b105501102c00f = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 331644820 1250 331643570 331643573
    0xc02011415010c210306081204030f060204030b0a050114030609281e03021618050604021603050c0d0e060f0a020f0a030905040f090224040803120708090604080a0503100909030804 79
    0x141c0b41d20f47c00081e501c0d0032032001301c80004c08000842d0100c035813003962403101c03840c24100440240220b52015000c0301400d800c000da00d40c5240e00031411b0700c4a9198150f45034076264103240d0307130310303811600b0081c42d0b48a2100d001440c24850007100c00380d5114000040d00352242c1d0f0703480d030040d800481000d454a103481401c034101501071164540010700110002e0040f4606551b041d14442412490703507036555a1408602c031520f4a4040313540c8041c4650910500c000c60740b8000340340d58010154000720303010311969481024480d4010361615480288a14200075040c4500b04542d440709030703007000f5442843c44445001109210001820f400f0380c03103d1400f1841c20007480241c900412144000034a01030203900142c0e24a006940400c0014400e440a003198440000300c3d032040d9002034000c1e10020442081400001d40c080348160040c0da600341e11034a036130300c050b50740f510103a600400c00d80040c0305911403036108030080c6610007101c000014001c0d5584440d030088609281e001e40001e850a0100300 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 331646070 1250 331644820 331644827
    0x105010303081303080606070602040503031210050a05060f0906041d06040f0c08181f150501021513020f09010b03100503060c0a030203090109061401090c02011415010c21 75
    0x140c0c480403030740040f220f9400c03641e00107180d1003000780070500c100e401040090070310800b0750556010f410080d0469a45a03602d501504030f82c1d100300d030075607007101d807000c004501400c1045079842210806418107090140a00951a8941140f050f00d0b4120b40c040c4000214070b040080d03004140200c0c05030141035030808a0512080c0c44404409040c1e5a00382144c04210b140e0000109074040b40e80c0564044101e920310503941000e03003c0841e0007200c80001850003032120300740d12554200424041c6042e0142e680c4006a84940c10602d02c03070031100540001640e400041c0089146c2c4600c01000c000f40d00280038001004103000307030016400701e8004000c124400d80d5054009010313100031030050800c1d00e002582c16641d4420300180e40200758020010805546003500120382260780240300f44081c56501c2c0b40043d280200344603242c0c1d914201240481c01c20300601c680302c880c04601e40100c00564504800105000744d0b20303500d50400840040c0c2d800030441222044454203070074480c2800803001d044005 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 331647320 1250 331646070 331646087
    0x9100917010b010c02090604060801150503150f0106050c0c0a03060c02011a370306021903050f0a0e0f0d03051602150a1517010204030c0915051516050105010303 71
    0x8030940c1c03400030603009503030b000200014940d50449603a6110768411010a01510103036003e01c0041d0700f407004000070740c941c040100c4c0035030304150103d41e60a4400c0c81e18400141054505d40c50244046005002c624401d8004000c50755500d000c461014140c0c6c0c02056007050280d20a4410b140e6403d184500194280202c031900d10969101d600705001d0240050314009082c0c1500c2403d404600822440304491904c40c0b00410542c480c1000703140e901e0a100c0d019500003008000418120b401300900d0902900c1598014008002c525600750340306c1030241c00900048080390600d200390341c21000b80704070800141c09807004550740480e0b9410b00f40c1031030012a80126540d02503411010007070940800b188011940242c11600100c0d941c1f0340c0c0d155042403502a40c00006107240340d05518008d0354015001002100d11030b040e40701005544416070000c5907907123220100809404a4100424604a40f80e0310040071940130141c0fa044ca172283c4503031740600040c41190242d4607600108240b54120040 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 331648570 1250 331647320 331647359
    0x1501030e06070e0f010201090501090c091b0f14040b03131401090201051204030c02120114010b03091f0b210f0d090e0c1603032a020a0206070206091009 67
    0x9206900340340340080d00314489a8001402400b11980c4d4001c2c4e6807003504141c240c00c1e0440b0003000005510f0405001001d46400340700b8180341000708140d00c2d40040c11407400c00009039600e24940c84001542140e080300b0304119032003404410301010030355141d40c2001314080c8a20704031b8010585418501440552000c2291030880d034502000100541d030400d00322200e0541403021a050f0341c0c0c403840d054031251000400039400c404040115282e4510544c0107208001a00e801004d00340c0c0e0b01e1810412a02c400c5a00c170300144c000c1000400014080c8201d0302941d1803210020413003c6c90f0302c003ca58400409034100d81c1c0e6405c000b4050814800902041c0101ca4145020380420a200803000c1c2500103288690788007001c1000000d01d80440341000e44800090000d40604440e4050600501a0005401000a0328070b403003208100119503030700340c0c40404d480c0c0d0050700044203550208034554118440c141e800030010802c01301c0301d075601100384c504034400d030319100640390400b091400030041e607082 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 331649820 1250 331648570 331648573
    0x3091509010506192d0306020301080f1006141e120a06050105091302100302040905361e070909030f0f0c020303040b03151801080d020a110402030c040305061501030e 73
    0xb889041c00b1610411768080300c0500303085100c1240440c0010720b603040c0c1d002402d103a101000214403c1d40200c3d40b071410440d0f8900304c0b4580048a100b4500300c403030901c500d159901c40000b42041c6410202c1e120300c9505402d0703030741c42d50b072240c100c010520030201c000f640300301c07904605112800c00000307215441c00b5040c10303038400f4240d1514070a070b41b42c2c001448102a20175076074402c60001440c800d404031806001100824401c5050543c40e85440805411501200c1c80e1400c0d98802c074480d00741c4c1c110015a9103c8014030003201a2003200003855010240b00c4014092882e001c1003501040c020710015510070b40d1025590500c0303070b400508203002d500d4090100803002c0140000742e5000800d640546015060090b079a0302c0e07030411030f4100004c070000355030041c00c110403110f40c203030a40704001e04035820307141641c42c4103807440300407620b0301039200005000c03031115010000c01c2d0425038003071540300500002c2c042c94a81c0707a40b20245440800c0b00c203100f120150f107207042c5803941c0c10f000d0328420b20326510 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 331651070 1250 331649820 331649869
    0x703060b16080715020f0715091104020a0207120f0b010b031005090a020d180c1401091202030c030f0c040f1a0103091e2307150503091509010506 64
    0xc5000000000e4041c01600748500481c0880c18000b01d4640c07004d0b40d145800c4119034400c2e003050940307000c0d04548026283e8924010407450030030f5080c092100350341da2190701c06c0200983c01040000031342100d507212045114a07400803d901c841c413990740e00d0303546c050345100ea000c403c0c2e803501c2100b042050f084000104018401d000c42001001d01031410394408a40e805125610080c00348002d004514840f001c4905260070011000840001c2481d401d0195100e0300544d5100c1c00000d007503092031209280000c5140304204104640d20b24613414091004065a90103408000020320308450b50601c4034040e00074002072072146c942446080d20500c0100320a11003c0e146440e000d020102c460013040c141500c0c3c00100042001c3d00c2c85c06400c072401c0b4442d00d0310340b00c0142080c28000020791312410060000100c000c40400c00020300c28121418440000500a0304240c1290940c10103841e000c0070744100007242e0001c8c01c103070144070f1103209584000500791801e47c0400c007070b00c80c8042002d00c030032000c0f0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 331652320 1250 331651070 331651087
    0x1403180a14060a050d0f060b09030609010204050d020d06020903030f18031603030e151c0510030f0f0f05031b06060a030b060d020a05040c09030213110a0318020306010e0703060b 78
    0x84040d00c000f440b0508100e0b4071440f00f40300303903c00307044000d1407040c40d189400c101207401c00c5a600a4090b41109504460665031544a80c5080340302e2800b80d203600400c80c110403401458a89000b00082d0b108090260802c1c28800101f072640d00004000d002502000c904901c400c29009500c05c003100c422802003e150618014200811030301d4000a420001b0309504c80700c0544500d000f0200c5845c1c492100e6580712490018088401401c03c040080c4504200101d8282c54a000441c410749400010b003004000031030b600c110f0b241c03c0544048a004d440d01000c0008100140302824901211050f40000000509000fa003001300c0100031520800e140b100c1030010a4488846c3c580c0404181c80482d180b98481c00000e683d44040d40c00690300c45e01f0804080c1d06143e00944001c2224805d4442c202e20340c2e01c000c11401911411000000700060520021304ea4074441e4010741400207202c5400b142680c0307144c000c070707040c07180c03d81000700d4180c4c58034144134016071f052194900402c0111540b904105c200c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 331653570 1250 331652320 331652329
    0x60304020105090d0f030203030106020115151115010b13090504031e1103030a0608010c140702060a0504050d030207261506040e0708010507090f0b0d05041403180a14 73
    0x600080e0400401003003140454071240ca019040a4115217168911031240c50001d65070380c424000c000040d400c1c1100c2d21255490303404001c0a503002034000c00f640c03881020301180d600580d002501c2c1c0502c01c504600f6541c0b0388644056000e000440c1b00159a8210101d4460703030f409242e070080014610b0001004086507201c41c0510180103030f08040c07d40d4034985101180c2042c880d588001c1c00d4000001449407880c03142d44024110340002000f8002d8010310a000c0d82c040011041001c032003d403c0100030014a42040200020081420081d04280d221408201ca00415410490160f4050ba01c02e00c0032541c141c0d410107079400503001580c010403030904130350b0301e580490141100100d0840045031003541c4982203100d01001c800b0480341a5903943c09264040d01040c2c0361600801d44107000410000c0e0507030700348410784100c0100c4508d4078120030920310040ca0010030650300d00c011200e00010340803051008000b0701419028207078501a1079000c1001e07601e01f07a4003094840e900060006030340e865 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 331654676 1106 331653570 331653577
    0x31c0e0708190b07050f040902180402030105030d0c060209060c0a0b010617070807020f070807030309080a030801180b0a0b0a020f0f0316020a030c060806091506 71
    0x9803208116111695040790340a2109000c02e030070041102034a0040e040021890400c1c80c020803081c0b00700031508560000388181da00019101d0340c80100580f001d207030110880302113246524010000e551601c801051000313001640981d4030500c4180e9040d940849405022166184003102c21f29481d40000740c000c40c1d03c1105c18002140841c400e098200000c0010002c442c0315840f010b00c00e40e004000203002c40e00310b02c5a0524110b184806100402c0241346c5800204001420342c0380140103070000750803100305944001420300110703a00051460442e45e03850401b17114a10038060382d002401014640e207401154200c07000840c069502e00410103403580c0c2d401e4641095030030b41100e032103c90180010415a1040c0441c55008186022070740300c242c8010880d011003541d03541c410b500b80076964000d002003090b102c10400141061210f0550020365031205d1031104107482c000501600 = true := by decide +kernel

theorem cover : BRFrame.Cov 331474820 331654676 := by
  have h0 := BRFrame.cov_init 331474820
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331474820 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331474820 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331474820 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331474820 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331474820 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331474820 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331474820 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331474820 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331474820 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331474820 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331474820 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331474820 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331474820 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331474820 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331474820 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331474820 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331474820 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331474820 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331474820 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331474820 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331474820 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331474820 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331474820 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331474820 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331474820 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331474820 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331474820 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331474820 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331474820 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331474820 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331474820 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331474820 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331474820 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331474820 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331474820 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331474820 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331474820 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331474820 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331474820 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331474820 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331474820 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331474820 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331474820 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331474820 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331474820 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331474820 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331474820 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331474820 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331474820 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331474820 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331474820 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331474820 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331474820 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331474820 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331474820 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331474820 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331474820 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331474820 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331474820 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331474820 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331474820 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331474820 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331474820 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331474820 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331474820 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331474820 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331474820 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331474820 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331474820 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331474820 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331474820 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331474820 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331474820 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331474820 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331474820 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331474820 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331474820 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331474820 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331474820 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331474820 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331474820 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331474820 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331474820 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331474820 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331474820 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331474820 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331474820 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331474820 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331474820 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331474820 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331474820 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331474820 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331474820 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331474820 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331474820 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331474820 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331474820 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331474820 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331474820 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331474820 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331474820 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331474820 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331474820 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331474820 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331474820 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331474820 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331474820 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331474820 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331474820 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331474820 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331474820 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331474820 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331474820 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331474820 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331474820 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331474820 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331474820 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331474820 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331474820 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331474820 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331474820 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331474820 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331474820 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331474820 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331474820 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331474820 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331474820 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331474820 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331474820 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331474820 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331474820 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331474820 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331474820 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331474820 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331474820 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331474820 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331474820 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331474820 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331474820 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331474820 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331474820 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331474820 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331474820 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331474820 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 331474820 ≤ n) (h2 : n < 331654676) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
