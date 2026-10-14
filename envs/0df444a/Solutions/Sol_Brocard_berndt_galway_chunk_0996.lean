-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0996
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T00:43:23.546329+00:00
-- url     : https://prove2.me/submissions/dba9e1e4-c8d3-4e73-9d7d-247c7d90dbd1

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 178956834 ≤ n < 179136690 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 178958084 1250 178956834 178956847
    0x3309080f040e06131401300303020405133b0609060402120a030f05090f0d05010f150e04030302030c0c010c0c0201180b040e0406110a0207031703071b0602 68
    0x5000028000401d5071114240ba1031601c2c00a22200d00000f551103c4c0f0b1a1505069a00d01c0780103120707460540b6400404803504c160004011101c84041c2c920362030002c000386840804042d8035400400540c1e0b002d6490188030519816424141ca0000745e09507160824219010300f1026801c0b141e000544104080c1c1041c0300b4103d0542e414000142c03099510303a003101041106609146080503c1844100d0041030404401d44006040c4900040c40c41c04200d40000c1042c0030381e94207107504c5050040103200c1c0648142a2410b20b00030903a1941d50840107041203e1341103010003080d0120202c2d18030100c1c000455540c1d5800b180250b000411540600c0300510007070444a00034850814250b10544a20440c21078034000588104507010000741305160100090100380c41d201d09403800c9030600768007118551110b1410802511000842881215021509928039640007440030f084074007483c000c3e003030940d0801c2c0e00126484100c1d0318401185045103150300c441e80041c0701c00009030049000504110 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 178959334 1250 178958084 178958107
    0x90d020604060c050d08070e01121b020304140f0607060c021207080d0506060c15060607020d0c1505160213092108090a3504090504330908 61
    0x10495004000001d8441c0450f0701007100420400c0480291750030708112902d04008010800100619081d0411040b02601c840061054218481100389030965102050710160029940c0d0418803414565824922a02d201410301100051000802a000a103010f050352900c802600051808c10114850030040d9202980300201610b5400c1c0b1900c030a0355900c81034030582c002d0303034005814a485140e04001c1c4000c40a0000340c90a81e030700013200030201c2d5544035000156180030b80c040c06500034005128007010008006400d00c01e030b6000703009107602005007480844450003120381103010203180c8611100940740911042211000001e8042210140c3c0c2e9500020903d071000790b003030401d0015180396030490300489583e600605100081400701c200351100c042c07803001075107842015080c42c001b41010344043c00646a16920780544690380e6661581b00c08001c200450703059446500882d01c1c13580858800c1c02d03100d0001e8081c0d002e551502d0302c050300d803c010050b40030220b540d60310070005c0e2030414 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 178960584 1250 178959334 178959337
    0x1b080a050304030e0d0f02190f050d0c0b030a0506030d11060c090d06090809030d050309070b07030507120903020f030d0f080a0b04060e0a0e0601031a060d0b091c0f0c08090d0206 78
    0x11032146c45100342034030491048c0410b082c01e040d0020406070200000f071258a2403100145e045480c02c4a101c101002281400c041c64022038101c80c1c5003031400010411000d4070358010f1800350304207404483c0f0b21311101e01c0884ea480c500c0200d903c0141c000e20042400c2c480c194024040225000305851082d6030a0782d101d10440e0f1200310b0448050002007903400641c5814041506002900e0511038a1440c0411b01d4a07261640c500645641a501258220500d4401c1e0b080e9002c10354050786071350800c2c00f10200507001c815544000c070701c00c00c0700b210001700c1802c1c0441e00310b1007500326450b200b145044ca40d10a46d10344400a00c003440a60740e400018060340d88a00500d0000c207103040541c4000d0800344005000d840ba0a0b0751602e06038040c50042002448881040302400c4c0c8510f1940041c1d103500001440160018801421500300d0300144030b4440340c0802d018a0000354009009142c00510b01c0985d03100d001c0389000d0313022070803c410b160041b0700100f0040c480110700030110f03440803620381e0025985 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 178961834 1250 178960584 178960609
    0x30c10140304020f060d0c0306060203090f060307020109080304060605040b04020a0806040e1014060a0506070f0803150d03082e030b04050106090c0c06060906050906040f0f0507030c1b080a050304030e 88
    0x12140c961046147c05501882210301030070030752010354074040c503201c04210741c5d101c40a400790107804004000361036180f00b940041045580b19000781d903a4140b5060400c0944098000d030380c40345180030644446480e00d4800c4400110568031001a9561041c0030400140f4103001680d9a038010418042344281c524400c499008140a03041401c1c0e081c141c06014108031140c20441c0901c9041040f0001300c0c07002d013542d240180d404001c0c3c683e80c1e41e0b0105a02a01c400142d1180e400c458009100002c06030001490380c803c0201c4004181000f8401995000c08581c118030060100751150041c00403d0b44240b9060344140910004036800e540c414940c82102c1c406681c00001440e9210a03e040080300d0056200900d042c42c8103100c00d40c280f00c00204e8070103015203403501c5540d40f410300500c209400d40000149000b5100c0400591034004030140c064801d50f0009000660205a225508114801c030480c1c0380c0d80203001c45081c013a000e5000d031515840900240d00344031034184105030365034945200343c90 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 178963084 1250 178961834 178961857
    0x209030109060f021201051507080c0708011806140c0d0b0103020c0d110d08090d03090302011407030221090307060c05040806040309031a060d02010e01120203010b09030c10140304020f06 82
    0x1d030b13036480c240e5082d45c00e001a007109110ba4404401c840c0030900010540b0801500310101a5403040070241c6503103840e046506c170340070070350800c4560342c0640e00c50f2110682c41405000b02707000c0e0541ea2144043d000380e0440f00c40080c4a81070100d074100101660003408a00c00c10f04005240c01c44cc10740040ca400c1b4104401800078210301c0c0e0f0410412018002104d2054084c18180f40b00d092840d065901c40100e40103400030107503503c40700d40238940b0075005091404451114000e090420400050195014040c40340002025a04116881940c00181403003180c1c20070203182440302030b685400c00382418841e2401040030620000c1842d003424000f15008900c20b4032040c46051440c5003800002c84e41301d011031098078410b410040541c48a09158003629424603051003407030798140050b201607074003004403c4064404400400c580101c2001020340c0c00c000c41c11121450214010402101e030240c0003100001c034040581141c0107070369806550030503c01007001c040d0840e80350208070240c002441412 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 178964334 1250 178963084 178963087
    0x120e06070b090705011e05091507060212010e10030506150f060a0509030d03020301061d0a0b0c0a0516030c0306020d02040b0307180509060f0607050708030a050714010b130209030109060f02 83
    0x10396070086d01ca42c0a0002e100198410002d10300c00241281c0100d0300c00718003034402d001c1d0102100705000708440ca043d501c00001c6444282240d0310001c024001d000b841002c1051001088000800100a0301229030110042c061503a0b046030103510404819480d41d000308a0308007184c1e25580d68009002e00c41140d655203900c03040781e83c01b01454007001c1410360782850320408c0107110741580b00c00e15040440c01a0306d42c820741281000407540d0007585038081d03241500d01141c4c20802040210320004401d01a10032107481e40718882005c000b60f0031a20000302041c0c130006081002494680180001c02c2d06083c0042c106a0389242680d001c0d4811158400000c05415280c00c2d01d0360408051000341606403030003a52443d2400218001d8004003c2241c80340d200403c0c88d03030070040d0400c80f800280034030303000756500c907500400c01801503042485e0407a00662411045400d501c01485000c05440000f800380800c031306200302c6000290b020f0540307039406540f581a0417001c80d4840c0214581101c00c0800107 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 178965584 1250 178964334 178964339
    0x50a030b04031d0f0409210201240e19110409020a08151c050307120203040303090b0a1b08090306190b090c2215020604060b0d120e06070b0907 63
    0xb80340d4908154040419a894900c8094584420400c40120798090345c0000c0c25455905041c0600c0c0084542000c952480b02c81070020240d0642003041182c1c424085030640007200c08140c115a903286c002c544005c00040e00064503003030702070b0b02c001041c0203504001452610719007072440c1c0c60b4416008055426000100c90001e00d512480207544140410010306c0e18485120020b45031004960000d420b241c44180280148201071044490b070940c048440c5100c2c5014480c003a480760040c0c407007035010541900d0001009002c039012201d03000c980c0e5403820515885488000300b4181c2a03601038400c050240a0100192400c0107424042d200c40b044056011185030001004c2d16000710a0754000c804441c01e00214088181c280d035107a03001c801155410145050a002c0d0903d4180d0203815000c940030302094400e82c001c14424001d500604d02440f0180071401401031019111400a01c5000311700030b0b0104e02d9104200075403420b48028500ea1a01144d500c50b0101070000340d0f020015a040b84204 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 178966834 1250 178965584 178965587
    0x3052a0a0806121f020903030705010b09060904030f05070c090c120b010e01120b0d120806040f0b06030403030e010f0c0201140603010b010c080d14041101020d021f0e07050a030b0403 80
    0x1031507001ea0704460401d648840300035010344039139060a001d941d50071200c40940a04a15405031818240c3c06030480762a10b1150502d14003030141311143d40d002d01200c0c0c0c04951755040005000d4441e981545800700b600c035520004a4580d0b20900302030700c4140e40391501081e216014040c030b60010b941603444592140d0103a1f03131002211100081103041c0120030034400082c1c0d07009020203041d10340c800800514090f1036404100d0031003010300c0040000d00083c603419520b581001c1e80c940a0041500c0400418a04280510894004120700c0e6800f070001c2c800200001d1094000031002c4005c000041419804141d1800c1541c0c2c9003005000581d45642e00d0034080075040740820340c0024118002e0110090140000c0c010710f001190107010f462001682450070001a003061401c1c40e40303506801024542030500084030301d2407416040c014014142c00b203012510018034105080e48028007201d280921482e0030005100051403c80f00d4041c6110024040c0d0741c0381d96100055001e01c036200406d1502c1e1a0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 178968084 1250 178966834 178966847
    0x2010e0601090c02071712041d130c090c1710030203100204050603011503090206120115090b090d2103051b0f30090c130e0d03052a0a 59
    0x102c1d5a00c9450811002441c03a400a40a011100718032903004c00c130602d4058441c100755869a001640000005000680c0c01204590b8160741480c0d1010003502d4803074107182250701407016400781201001000c00d0206552943c0122071650407402c25044408044c0100080c1502c12104440300c01c07442c610404c150b007000d0003642e60020889200314501800c10001a1007804107001d00c1204940700c500d5072903845d002e07038000000150014444d94544022542402502c4400d0252074801003000040c10305481c022840c0006a030003818246041013264401d011444090b104203980c00d103c1c106c00c1c1404503c104d0704409050102d550040b4880c03422070010082c0702c1d1040d02c92901d200040000018100d1800d00340c0e02018901000c0c80d0042c1001c4803850300c0301c4d0041c2003c00010340c82106000d8050b100165020380190705842064040c0c052500d0401240c1245100c100b1682000940c050681e10aa0160790310800412100c4800b846264a512089074080c17103141d09031200249003010303582c0005 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 178969334 1250 178968084 178968089
    0x7022e080f04080a09091a011d010c02221e1b02101d0f0106030201110706080a0507020f0a0501091109160305070e10020106050f0a0806040b0a09060c02010e0601 71
    0x30300e804103041c950401410071600030409403508002050b000e003114495242d50700140004138041c00880d20044c5010698140300f6005408504c1c5444031691804000e9040001a8816118400110340e00e80030711440300311001c808900e00304058a040e0303504030180315030800c82c11101071440b400c02d001c403101c6007100d284d4201c0c1d0700d0402104a02040b01903000a812450340341c022000304c1c85030003004804661030310700c1098801c940a5081e5200f00010154004821030f03001f6a00c20380050840c40710756483c0c400380c0c00340a001520140010b40350308400d40119401c2100c41c1b0445156442c5071200504100f154202107540340d44480f03540040c4151100c620400d000121020103280c00c140c1940d0704a5900074500b01c042c551034000080071140103030401c400142d005000460b00300c01c0f01e20b00900034801c90040074231a07800000c105101c2d0901c80c109505aa103144020007460b100c0d52a60182c500009269400b090340b9440c5a41c000381c0a8044d940c00d0030000d4001044184011f1506824224143c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 178970584 1250 178969334 178969337
    0xc010501170703050607050c0a0b1807060e0102100b0303090319060b03030405060703111509030c0601080a08041806090908040801200405100905040203013819030207022e 75
    0x1d10061000c81c00105d00d9540200c00c504105941d802150b10b1a8103203021a4006004d6244c0c00e030812402c0742c0e000c081181002071550035a40160703114401500d1b0105882c0341c00740141e018585a845044080d130100080079001070441c0e041460030000a490700d8004185c18010403040e40040b005c220250040900c1c86804802440c10582040041500c90082074400f800b002800360a00b84c0302d100030f0014480405105050b43e259103449002e6035921380c8a00c4048a080c0700304c000003d00d080c0301280301c0c40d00c03540c401e0304c2d203160615003c0c2001c1030300b41e0183d10b001340980d0b884e000039007114513101d07481d580e5100300c0032991100e01c0c000c500d50840b071881d0000c03080e070b207010200307a00b0800c102c90459069940495600c0075900d0f84d00c408a411301d0443e0004c07900644004008150100c4076800c494400c8001001103410407480e050b17400c003000075086d026100600c1800f000352200513100c0740c04000c140600d40182400556000a0800c8404910a40800122010300038456540f15010150b91246 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 178971834 1250 178970584 178970593
    0xc09030d03050405150604020910201902041d01050403030903090e100504110903010f0b0406150f230d0606031107020a03291608010608010e1611030c01050117 70
    0x160f113400d515041401c1c01d59606135a2074000603503558031507054407458a0003820100e1070300c00d114005440403980308040300360315a90f180041900c0790009001e0702c0031140d01400301001100c81d400e0101810250940301d16400c1a0442d0881c205000d2040ba80f14602a035004143e000040c00c019102108941142c48111941c03070803c41c95030a0fa5a16004440c5c058400080d0b500c4ca070700d180300329401013600c0c0561650030315082070b011010a070000b44480c402198200b00e03040d40d03850200b000305045461500807980c501d0150321078078011500c2650207801402201030503400e042a10149a10100316040e00c2959818180000d43c1c0c580324a1040d482c4220b82d0301d25103072036500002e4004400384001000200f400600c05410402c842200c110001810342c454030301c2c1448154600365260004032400044c042a0002500034480d941040c1207480d0317000e580100e41c4904110b10070600ba404100e40601005030001c1241c604200018808800c066000242da941008116014807042143c18400d84c1d01 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 178973084 1250 178971834 178971841
    0x1a0403020a0b15091503030c100b0418120e030a0b190b060f040504240e010305010e0a020a030b0402120627010b060a08130606090219030c02071412060c09030d0305 72
    0x4130400403d0700413200140c80b060703403991000000c0c51842010a82c07400383c01a84845412060303140c00c04c045861085034144150030401000300007410603060041e0402c40c2c00710a0048403402800c50280303105000e019100c6500c4d0076101c0400b20b03041a1400d1b10320618140528104c0000c41c4103504c92050110f61142c9040581c03030b4914024040c0b402032503c07540c5d6594041d8810082c001c104a400391480c080d0740e662954a01300e0002e100c001744000d032303900e50912103400c4004601240c2e4404480c0e009003603001d031508684511030128070080c41203800c0441007841741c85810041150700c0c419841c2051604904e2900358182039841032141e002180c40e810700c0b1820382d596803190140c0784019490f2411681550f00c000f60026000c03440c1c20054542c034603021001c035484826400424550340d00454501c00c141003100e085040b03c1420491100603041640e0501001d0407850b004040304200038843c412001a0a070901c1c00e20500ba42e06811150b4001006003580c2424800d000c00c040b400e060070441e529 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 178974334 1250 178973084 178973089
    0x110a0b1e060301050c04150512040f0c0b03070909020a1b08030105010f0806090a15170d170f0411030c041b0f020d0203040509040606030b0703090201031a0d0206071a0403020a0b15 79
    0x103140a600e03855080003042c418400e06c123500f504d561044c2045441107034240303400d140c0e03006800144155080c0c280c501011a00c00111011a8061360040d503900c0036051070300740e0003070094015034840300c108042c58000e9003600400340c98941d1643c0c065401140d880d49402c00141c00650010284c1040c800a6410401540c0c2c40c9441a07a1040d1003d0010402c034140803250581c00f92a07800817042d200b44412807541d070000000d0702c40e044143c07a40b03800c02c1c00c070342c014035092014104940c400e4084024a00040010b407008a0005403003e02030b046450b00710010001605440c00c030414004c489490708245004182d04c0710f08503d07160500c0c000760184032803620000b0f4403840340c0e015985c0038400c484045400c01c003899001000958206031170154509003200010041d100031001039000030f041000d81240a0755649452001c8417000381011405421b5500b404096000b105003541c01c00da807640d402d511410380c0c0024a200c0c52107a8050090120f031450a40304100d00509807a1100940c400c118181c1d8 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 178975584 1250 178974334 178974337
    0x20405042d1a0d03020c03070909050c0a0b0d1509060801020910051c0e0a080a030b031c0207030b040c15080a1103010302010c020f03011506090602100b0d03110a0b1e060301050c 78
    0x102c0007982d92407846503880c10306915141c3d41210840d054456400002509155a070103000403a1007581502d103030303440c0390080200b2801a400b840300b290740100150798501e0ba0551040801141c1c6075040544c040c0e8602e108000c480d103541c04000b03281d400081980392407a085902c0e81e8034060701c0c1421414500464070600b40c1050b00740c501e00d201c0c0c0d40d40d5182450001c04001800b02d40d40d10081d4950b0303400351400c0050107001e0f54003802e4024460202d070004040d00c00044000745107440c2c2d000303011851554403507049052024200343c2c1d004900100108414459025a4901450a0b10707292010306208580300c04a840b8416403000202d414401400182c2e400750f4815103450301104d90120410028000a0040080360f07180f80c0310390b2a01c1400541c682d044101403044400540903501c201c01d01c0c0d2003000035035200034034259000b82012241000240200703374042d0040b101c0c10407141c694100355110340d0302c0c1b00284c0b0300b0b2002d0030080021b0040b03240c0c001c3d5600da0100c0143c000b4070290030300c2c481c0c40006 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 178976834 1250 178975584 178975631
    0x93c0503101a090c0903061311010906080c16020604060c030906110d05070501020d0507090f0e010305030a0309050313030c0311030a21020a06090c0801050c0406050405060904020405042d 82
    0x5800c84001250500f0740601c01d41710040d000505560481c18013500303040544002c040120343c26100d4034095882ca41c061181c40044803103d450321405d90f034501d9010716640e800240060002130070f130820080035844090191001c2c0009031100b130102242424083e1550841c0d6000400b000030f9010030889480c004551703451a5015420100c1e218542031030914007a000344551403a02c145400308012805d17501582010032610400044d0703140700c0d1140311010404509000240141d0300421900524178400e600840099000d042540c0c02c20010001034011403096a000740d6800403000390620500c04000d0040005081c110010405038105070782e154403059080403a07800d0070b11420340b000c0341c090080c8001c00c500d680c020f1040040034403901c1c2c40501d65480d800365144545c60400041e0007100032604480036502e07540c84183c02c00d40f800b000c00420781e0040390328680041d000e008c006400e44036400b44543c44506070301406080c50420281c2030a00028440c1034030301c541403e602c441540d16a1103120038 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 178978084 1250 178976834 178976839
    0x60c1716200307020f21012c03090d020a12150f0204030b06151b0a050d02010e15040302030715020324010507080d091e0c0510093c0503101a 62
    0x80b8080130384001180c0385030364100441c0801854100c44200704042d070002c2d015941b0886200c2e580c9464023000c4860001c1100610003a602c10851900145044409824100e05c0200021503150302c540c50805112074043c0708035180b080d00400c14540a02502502e400741200001c01c60525180d42c43d900c0c0217481c060b00d014004c0d90320520034900701a50008464140801d161503800340103400512940d2040c4221043d0b407507020749065040d2491060040c85030303007028240109207445614072185d080c1c5e00094011025448100602000112030041c500e4501421280051b12460480401504e80300f18980e50301ca11706003642c4072003440e81c01400340e80d4a5074000340756648407100c5800c2a0002c021848019201c1104803007101d14038412804954582481404900e08541d990300038048403106281c02c4a0104609240038884805400c24001032880644070324401c02d00c951014002d042e4031407201c40d0b280700010b0000d0207541070810400c10351921590301008940541c5803042d034605100c01d000392 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 178979334 1250 178978084 178978099
    0x507030902030f0309030705120d0f120f14070903030f030908040e040f200603010e13061b02070602060105030a021512010b130e0f04060c171620030702 67
    0x54559109500910300154040d08456510450340742441e580d40007491058401e100b110000701c0c0e00e0602c00040000d44038044010f24a5140c0d00390190741c50042c8074031080400584040f8900c000b0154011076103194208400007030b240f14141556880500010910000c3c054540030420010360300c44003800036004c40d40b0307000038195024608003070b4030b10840c1e00140e0030809801c2444140301904290a00062242134810003100d01d41070031600040307410003020f9100b10144010092008603145140d40b00c0f0009001400c021030079500e1004990b202070b02c40340c1c00100003009001c1c59804111a1014081e40d000414482d0300d4840003942c0e642e80404028000e0701c2018020090003048020f98008020a8660704902c0d0385407040800306d0b8100d1705030581c064a21080004010801d40c00b168090f080c2e03403041d40307410394482e15440c0151000064010420a0204d140101c42071030904081c011641c1030190304401903e114010002042c00c3d092901e0030040c1134081a803010300004440303c00303505440c0003 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 178980584 1250 178979334 178979341
    0xf1106042306040b0106020607091a090d0203010e071806080a0807051c030e0705060f030f09070801090605060a0603051e09030f04060309031404051c020607061d01110708030a05 78
    0x400840038a519855100e50414403041000c031600d13180c16038040d642242d01a40e02e9540484040d0b140e0312030162056441e1360000905c080f49001455011006010606202d48580c0402c1c21034242d07500b81d04050f00201d009002071215170880d6100c00f000100705008290815141da51290742c18640286040390010f200c0003004001e008900780050032850414a02080200c054041e1004020642e16801501d0020905152003020b50b0041800c010072142075075903e894400040304081c200000c1c910410100140108090085c00c908d00e108840111700b0342024400d2041030015a088642414146002c000c1400e1009101c5440600700b9840d03803185440e08010a41141b10310007003001c40038800100440e000741c242d004010018801e40d40c0c00b1450064002008003805103004c0c0550000d02c00a200b001d82051644051003540002d00700380c035010f001e0303807001e003101c042c90590144921086041102a8400c0c07140322054a0318502c44c2d80341c5601c6903070342061880018040715000b42e030390300070 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 178981834 1250 178980584 178980623
    0x603091401090b1f0e070507020120031305040b01020c1e1e01170118090809030601030b10062a05160906170a02030715170c07030f110604 61
    0x5041150340e00002001030354440d050a100c1c402d02100c45a800031440d900c0c401c1900041c0401c10201e03140d18941c0b05298403074040c2228140c2c46810264100403810403601c4584500e010030810003102c07100250b90b2560142c1000c5d2103402198030031841245005401440360340c0200300141c1c242b40849411010000810000d0071000003000c0f4150004a4460383d043d84002c00c0304c9103401507400740c0341c045864001d41c5101650b44007d000390303100104c5c07221001d442003009030040c440d002e1042051900708100e0202091804009910940b0703a00d0381d40042c0085400c4030400b5002030401880c051121020180f1280764503820241400c05592818030408203000f030a21482a06140c1d5140001e511580c0320f000502403d120b004d1602d48943c0701e4600d44c0c0002c4001000d000169001c1c014007402c40c0b0b001e210300003110100300040b003132221610f41000d6012034000c0891044408190075911030049090060a040c201016441408441d0b0000c0c240e082000a005910a501c07001410088565000c0d = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 178983084 1250 178981834 178981853
    0x31903030903270501030f09020a15030608030c0615030708060f060f040911040506030c0906090c090a0b1305060418110c010908180d0b04080904020f160c0902090307060309 76
    0x3602e089501e001425840f242141c906a0440b50243da0911600d400f06010004462451400951200d00c28008004d801c4806c070200b9544016410001010f9a0301c1d5445810340d40008500c6080340c0003030013004603480100402e95080d14040c0e000303111180c104800a80d0300ca034040d10081c2c1308480305e00002c5413666824940c0c020454064000c2c041ba210514142102c04c810180c40c5105038180000a84103003400234042c1040e900090048059481c1e40b8244100640040e00045131440100941c82c0c4d140c407400d041000078503141d540103a84103041c1c4030b0304140340c0c05034101a21502d002c01041040011220081141880940380001c0c58281c0300110341080c400c0e200d03002000d50a01d10b1160a000e424000703414009008c09040c405140580e0400820f840d161400915103c410400308022500b0342019045940300a03000503d060020184651103421210009625425036581e550400c410361400d6001031000d02c0007036003020003c2d0b0010f901d80400740500b20405613200011801c1c08031201c1c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 178984334 1250 178983084 178983107
    0x21002010522151407120b130504111008010e1e060f04091b0f14220b06030406062d060507020d08030a050103050d0503040c06140c060901020c010b031903030903 71
    0x140422001101141d6503400781e030102c401c5401b0030500b03140950401d09600980d1214a402001c021000901503140d070010007002d08182c3d0f2440c049a469000e9443d498101691048203071558200c0350325044242540c464024000e1005a0b814080d40302407400220041341c1000c1704450300d684415119011400820300294054500380324040a0007290702c110320300c0c200355003021030543c0645481384158400e0101c81d03031085800034082035402c4540d800522a0700c0500c442100c000c00c249000e00005120b0350004e80701035900b40d949190401544803946407042401d1a03504a0301700d420b5040d03c0c0380780482400c3c400d031030501c00c0010303c240c210743e5010020003800750700c09441e544030b0400c6050301e8010f003824082110644030f00355000344058040da0640c0d22407940170268102c41030a20004075082c1c0b50058090121300307414410600d903d40103000c03ca10031110040010307141c0703609044079800d451148440da4000c1e00075507049204100c07124004020f56405040120b111070f558030f8110780211100 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 178985584 1250 178984334 178984373
    0x5090a060806040305070602120c030114011706041d01050103080d05011d07120609060b0a02070602030708040b0708090603090f01061e0e1f14010f1403040b091905010603021002010522 81
    0x4278100000c20460b40f014605035801e44060044014a0b200192003103600c501c0d0780707521081c14400085244c035041d0401e0707079401a02c45181c207040c0080c00701942596000c1e0000c80e200c41011030642d0024401e803007078078014108a184d900d0131400000700380080400c054400700c200212100394090103076044e04008010600980100005a80c400300003d4a8105181200060141c00c3c000503000e0f1000085d00c40c410340100d0070501d410316290319040b05510a50040310b00302c82c10710120f000d941d200790280d803003520b85e680a04215494654506c1c2103c1316a040510407089400c03000281c07003200202c4500b500d9040b50255a1034850704c0300d6450b2581c42c12904824803440b040041782076460485120b0061100713807107145072030301400e50030b4415122040c1c50b204120300600c00100410410003166030000105000e1742c10030b10314000300411400b4070810544080c0e440d00c00800441c01c0c0380da0310750440f901910080007942009001c82d0343e201d500b0781c0b051468080d615288414009446001007092403003 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 178986834 1250 178985584 178985617
    0x110a420203070209010b09030634080f010806130809040e0706050408070506040303140a09090509010e0f0c03070302190e040309080f010e0709020f040e0a0605090a060806040305070602 81
    0x6800000c0d507991101d80b040f40101062000040d04880c120140da07034081004000e003c8036a2400d00041040701700c080c0c0a0200c021121072140b40381031480c440000c05506544030b40b40c528140192451812040e4803ca1103039100804014480300e001d00d04604017940f200b2420741d03070201c00c8001405031020b10045c4240b405a038800149040d0050024270464020406507122255540204a41d034020340c4000350200d0036001805040201100003482680e1003030401c00718035519030307805030101d500c1181d4030740490795110242000344c403040080c008040c094500a1210041c03d40110392559a10301c002400740400d00b4018a101406400303203805802000074a400c03510f8030342001000250303103104a410600404160580c0c0d00307818002e000b00881013400500308030340b0340b00c550002584a080f0280e0310620600c40814a8400d0241103400380c4010080032800034106030400520032401f400b0044003a2401804104c20240400c0065200307405040140c7c842d8170343d0a007280a881100d41c5001080b14 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 178988084 1250 178986834 178986959
    0x30c06030a020a170702071701020d0f020c070807031a0c0409021801030c0e030601171213030b0c0c100506040902100c1101051813060e070c110a 64
    0x8940d0107049000f156681c1d101c81508080b0689844200030b80300d06005811110b424032801c4000720400c2c3c65200c11000040c0f41a40904200d0308450803540c03843c0c91580c0003d88001000b50400c00c0a003d04412005002c940e450f50380c800c42d100e800d5003800c80a01e400d580025403500020400d0300d004240c5aa8250343c1e42419481402002844107012404245048402c5c09114800ca05460101c48068010426030b4200030760740d848034a6030815551648103924810007160031720006000c0030b0b51456020b0754000d0031450302848008008040f084a01428010404102000501581179400d801c8002400d5150344011401908401c41d011350850741d501c100bc1340312035020209080c100c1c002c90030410b220402c580112440d105505001c001c15003917407201d408601e084541a46424a1000d002901c0d5640d40c1d03417002c43c4101141e40700045020200510288000301919503040c01049620502c42d030700b0715800c034680e0035801414105015203100781c5240c0e01c42c0da043c1c01e4291080c090406d2070408 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 178989334 1250 178988084 178988101
    0x16050c07030f0c09060e06130605102a03020a06020309010f06170f01020f091e0901060f08010504060509041e0507090f0b03010509060f040305070b010e0105030d0206070806010e030c0603 82
    0x40b00100308079a50301e000c0d5800107404419110b00d0090311420304034540c6c40d86480c0100703c01400740c81054840f450781e4440004007603a0312038680c403030f02c48a038450700401074840d40080c0f00303054001902c88449110040c00740010350f0201e0380c40e00c2c00c2d500c40c00050f02d0b0349030341d586580100b662481c0e128100d46020b0020a0f12440700b0418200700c1d240d4003c961003c81c3c2d00d1801800d17400351808441c3c280e03105100b220a00d1415691202018007866030709190b4190440c001802c008080e1b205001281c0e10042c590300c1998444c0a0781d000d03002c20340707050141c145014003141e003030320000b00041d00d82c200c0d45820941a0b03070074429400c1c1840d0001d044030304150700e07400b2201c020031240d00c3c0200c0342031a04100e018a41018092a8450365090f800b50000d1f0b9502c075140a11103c00620840402c03208000f00704c001107075014424060800d00d1500b441030743c188400c1c1031920f00d8100c4503805560240c0104807845a002106550108085c84c08408003041ea10110349850101e0038020390114010081221030f5 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 178990584 1250 178989334 178989353
    0x7060e01020a09140a0f17010216261303080c0f0109080306040f06030f0201030209060c030705010b09090114010b09060d1a01080c04080303010b13030f050d1202090916050c0703 78
    0x4a900c440d00f00e4011464004020b48142c41d4851102001d880300f40401280902031f41c0f000c52840c0c00d00000d4a040f01002c0c0d89624602c0342903044401f141d4016103504001030014840e403407040d0510b1802c0c9418203c10340802803408510008100c3c510000d5003644981c4203102540107054150001d00c054262403038409401e400440d889801388e403600d00700c01c4464007030340612004c407900919891101c04494004501940c0008490350304898204105041560100014038000e0b01800c0001120071885082224151000e0100b020076810000c040c640b95442491841c1101c1e1618401c0350f9415100001c90903601a0100d42d03201c84d480d0820b02d15055460000006a40340c2c2642d40b80001c1d03071202d020003ca4042d5010740d00042d0f0080c00103000c1142800b00804e400100c03410000e080582da540ca9103000f040707240084510382c1140303030440da440d60009056046211104010340c24010000c010a4100200a00d4a0410080c50310406c007504e0040e0110303801e030300d0381b0415207001d03c0d02c81c103245014 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 178991834 1250 178990584 178990589
    0x60e0907080c0f010e1003020424030506040504020f0d052104090b10080103061505040509010e0d110c061c0c0c12050a08010603051f181a031207060e01020a09 70
    0x202d0003828044006482e0051550f0507005058691a8003c43c43e18103102c1014000c2c4940818907500304400b04000c244c04810b09111001d00000300006d01c407a050040980c0e1001c0c0109006034141030912005980381c00021241000c2500d10364807448481c20034500c3c1c80d0301d07100031090101c03100f0640d0f681000100e0041c0151030240301d06000c0c800c00402840f1a4510303000c4254005410440188006131041c2c2214a03c1c0b508002d040b81c1c4962100c00003002c954080d203600c2c031240e6591452a080c643e0500444c2a41c400504155051200d00b00009846016049280344540c10000b007682e041401d22091400283c0105000c016200c5030004c042c00b4600c0981064602107000c05440000c18420310441d070f03031807515540d0050107920300720003a000b802d40906124070b010314030070320340c0100c00c01e4482c2d080082c007590080081245041381e03074900b02d50142c2400e0a0040e02041003441a480000b2800060a083c000f0280d461895040c004020000c450300f00000394000074045100c15840300703400d0103 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 178993084 1250 178991834 178991849
    0x10b12010c1103040303082205071401020606011103030114040f062702070c060c060e1f0609090206070f0c03060e06061305090606060f0f030a02070c0e01030302120d060e0907 77
    0x42503900b802206680b806103100c000d0000708018006200c0800400c4120514490340320390340c00311340315952024140f14031a08110006018004d18440940c1d040180d40d070040001c0c207280720842d104644403a220710050080603c00182444100450303102c41e0303c02038081c0c0c5903040c02c114441d00d030006124010303600a0500030000c000d01c548102140148200d03109190701558103c8118542102030b54400c4500b801550941d43c1c40340d608200350014004c0388094100c20096038800c1100c580785004031801034000640c020b1400e01464010388900f0100c4d00b07051703044641c039007103a8401e280c01a00c150b0300c0d41000340420f082060000f00c00b940010781a004cbc06003181d041e401d04100ca1544400c0724002c4849410780d50ac40c501281d40c40c10028010142400006042d51a2960a0400c0407841d8010794156010540c0000d4a6080c40034254131080074101140c0f6021655241d0f40b8000d640380300c60048403420050008641000d680140e0244006040302ca1080303c141c0381035070340651104400e100703940c4c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 178994334 1250 178993084 178993097
    0x160c0302011103030f0a090305220e010807060c08071b08070614210601030f020a2001020328060314030a0806031c1107080f030705010b0301050c030a020705010b12010c 74
    0x400c02d030003009130703071144100f05256461075480aa0309005084480c2e0180e050010400040e03007800c10007001e10b081492086d8880003500d240071400744540300140c2c404101600004002d202941d4082107401a080d040b80c01d0340d03151011814444200034ac448141007001c1280d0600080a001c00324040040b120301d501c61040607030240c02d078a90281300d21403103403004128080409400040329000680c20900600d40080d0410076212048100e80c400b4840c00301080e901c0c048800e0f14170710f008034490b80e0b4284500035815402c0190140a0018040c0e040401c3e000c40c03170071019900c044a034412002950007005c80d41c0c2e4248908089034595101282a00c0020308490004925050010361a4100c0f1215404000f1508180c0d00c03c8800148041d074000b036500036000e0004090300100a4810300590b0320340990340d030b103091b450201e003104ca5000303c103030103030741040c04001d0040071070710603070742d0015000d80c0240e501c64842ca01180107041c840d544661100c440120807141c480c0550200c1240040ca0316101d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 178995584 1250 178994334 178994357
    0xc0d111f18031d010519050a031b11161d040f0203150613140a0207050106080d020f1015060e041404140c0d0f0f030207181b08090d0e0105160c030201 66
    0x1100c2d60700ca00d01e8034406c001c40c8070f0080c0041d50300c10401440424414900016101d1800e54960700104001e00c80360000b0704445240311680400f8010561034821101003107804a18006030600381c0c0c1603c181ca50300c542012400107050050700d500000c9000c0d8020140c58940030303200d144404a62040d90b4460040b110540301d205211101d216851030b0040c9405440030950b11601d011019511540c0d0485141d500c520000600442c1008403081050541d00503151491200802d03d00d8149104082904a4205510400c0c43c0c1003c495136026a880c0345000107007070503110042006003400b00c60001304c0785500000c2109000404d02410744548814042d6940c211104003007000c0300c16001c3c0090306000d0010011b2000650040f80500078611a0040d43d0126980d01404c0b1085030262001840c100e032107101450240080441d020009003150800306410b0402e042060340d1039a05400f0300080c41001050962561f024200340c3d210481264003640714004645080c0f0000c082510040b80419040c5118 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 178996834 1250 178995584 178995587
    0x1906030c030f020702090f0c0f0409020403061b080402090711030c01050105030c010e0a05060903070b04080105040b13030e0405100519090e0102070305032413020c0d111f18031d01 79
    0xc40e40c5143e0020503e0003a40c8682e403d07002c0c07e143c041c200d9007859400304464285a08900007510007043d24940050300c540c0345080403820380303241d03804000c0c06a036241c0700c002c00340d500005402d400a405888001080e5102002540c8401d40300c501c0c07038041d100200384102c9590f415000181640c4095013030340c441c50750040054440c2e011080308181d00103810302d011f020b00c1c2410303809040c05a10003812645500d80c0c0d04040d00307280d48107802c03110b500e945403003c0205000c6203a4050340c00c00d00b1900f001e943c05d50707180c9005140e0300c0200101c034800c544802c0441c0340014034141d001c000d080e00910802c20300503080f80307206140f5131b640703d10002d190602800015001041c07080c0d848a50705502c40c03510b19a40c012000c18070804a0381100700c07050f16581c943c50140c0350182000c10505040800603039600600c014249403049441d4480c0402980c6900d140002c01c010403400c4400c0503030805551540045204e03007010742031440c1600d118800e01040001403550010a1074400506500c1c2c6c0503000111000 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 178998084 1250 178996834 178996837
    0x10915050108030406051e0c06070801080a080a0503060a091a030601080f0705130204122f031f1409010c090f03031d04020d06151407051b1906030c030f02 68
    0x280c14840e4000740002c12170b06000c1c90040610700014101d4030b5090764014030445440c1c2128504140759400181040b00e8640c100d8805800340c21080004c206150040d901c2b00a10300c20366030790308100907001c40403c1181d03c03002c00140c043c000032481440b50315052a840103035004142107441c424816500005441840804c044000700410409070285a0408003403148820b5041c1c58240c0c902d9080200080c592100e0b0a49007426224401d20410004030780500c10503281c4414100d070013511142c2c584042940e0025805c00400e05886980b40200c0d401110080207090460998082401000801120b1030041d0b02592040c0004d440300f0b95410f44411101c0040c02c11408001d02080c044115110180d020754400341864030018005032800034415042000d035100da5001018203510342208a50282e00003420314180b01d0088852806c22519461743d50f0354490f080a203241c6000b601c001c0340d0040e1501540500701107485440040d40f01da070340300010002d003440000540001e10740922114141c02600 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 178999334 1250 178998084 178998089
    0xc0c0603010f0308070f080a0504090b01030209130f0e0604120201050f040308130606080a0f02010305010602030a050301051003061a0c060c19120e250605030c0a0c020d0609050109150501 82
    0x35844020706503504c010080e4000c040580b0052807014107039001504c4103008001200c46036030b0f03160b29140b400303504c04241c42c1c0c0e0031589414180180403ca030b164a4030100080301d010b032072801154000341d800320300740203241504000901d800387c0340c1000309119045051900c91412640200840d58403541545203400c4140d070010000791025000c54001d81e205003810394907a0042400050132560350440e0307031030004c844001321169180895a9400d540e0540f00c3d05005000c1400a07620f0640e0340840244544014000c2c10311030b02009103000441d51103a0f000300040c0000c41c4032581c041c09544003042d02900140100f0781c491050a0004228200d2070066448104190412400d52202186c0c00c0d95038142910382c0c1915140d0b5003090580a00c42006058651103080c0c0030003940c0b4100f0381503040c0700c500d50b41107041404420000c0c070240c00380f050202c0314a2030561030034803ca8445440000c07202d40910101034003140c2407500403003d111042d400184118072030120301100400403003200b001da0701d00741f = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 179000584 1250 178999334 178999349
    0x10509011a070f0804050a08060f1513020c0a0803010b0c06090106151115010609031401051003030f030f0218090708040c15021c030606140708030408072103020c0c060301 75
    0x10b100d0300000800701480c1c502050320032402c41341403946400108070080c182d0351105050303a020030144083c146100207980e40040411103961048a0b5400104031803900d80003040e2a69070f800110101d03186c41c180f01d48000300364019016139880d41d4504545d04a9002074401c145540140400708410f00d074140f14074000c4420040070724202c070322012010355200c0695150010a802411803a101110714101e500b4080c20740e58030b8a40d09a803c40c103001c01c2018103045030811681c904000e204004810940240403070798185048034540000c42000c9028003242a00030f9090307400420985400184028036020800301500c5000c4142d549181c02c441208042d54080c00c20030703030614180005a03494210550099660045840500307285148500c482481814000000d580e290305210995109913800e034403074018060603003031040540302c524051101400080501d1000201c02c000c2124421120000c1d032011114800f0000c0340510143c0a540700180c3e96115008544548150341703808001c1d6410f88426 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 179001834 1250 179000584 179000587
    0xa0309170607050904020d0f021b06060303040b0a11071202040b0d15020c01060305120c070506032401090503030703090f060926010b030601030318050904080307030504061d010203010509011a 84
    0x2d41c10107440603801000303855042a001c000700304891205028003040b006001e080160350395240900010074101110a61105420240a20030103a90000c00d40301503516401403a5034032901c001040e100484800c85162030390007003810000300203142000e44002940252414032020350543e0801918011111000300380c2c1d5034103038203c0c4155101c1ea01520303c01c99841d0001508e90303140c1d241d0030310f410310001c10161002c800046000c0034a00a10040e0010803050303c07500e01714102807000d0390800d00301c1d048910322441d0000e503003c8960f20030301d480001080040d0540b9960030340c50400500441607801180c5426144460009025120b51110700858000c840f6000a01c12088203003500242c0b11406881c0a40d00c82c00c3c1429280e80a00c01c2e80d00a42c82600d4500780c1185075405c210359110240c1c00148112140010000452038080499900200701d00d030001d05603076141340c000010401110007102c02c003030340345a40e100c4210540c01581695011244140203a0b0303078010000d264401200400c0340104c0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 179003084 1250 179001834 179001841
    0x90c0c12042102150f0702031501060804080a0c0803040b0702070501090b0906030a06030c170d02011a0f030a061104090f11040b07031403160e030a020a12021807020a03091706 77
    0x2c0407401030401c500c01080c80004e954072611102d0503800001c0002c002c4200094607a045240c1003003090541001e417017000405d50701d41900900f83c14002000544010000910410040d2040895880e041d074400350b1181ca906250608030b41150003122a031025210b00d0328081401e40c02500c40e102200d20b0180002c0c45e040405090240307903003000c0c100010141d04c810000c00000e00051300c080c05010703807001003d410210400001d18015800c001e001c04d591510084075810001c807040c03240001c00036600100d02e154985c0100e407510f8101280030b48081d00d04110b2040311401e900040044412500e8107020145900303100100319848003a01e4450030303404210410440500e9406403d078140607041440100849521a009030b40c17084031a801140c1070110310007501ca0b00498108240d217070030340051841865580c080f882c05280c42c001c02c04c03207052510001086559500c0702c1d0050124200c000350301410001ca029642c1d1a440070120046402c90b1800b0881020541100e984e040b00b5500800c40c90301d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 179004334 1250 179003084 179003129
    0x130e130f112214010f0519150c0c0e040803040204110d0c0806040c02030f0403030809030706020a080f130c062a06050103021206070212030601050d021c180c090c02010209090c0c1204 80
    0x14070f201c00940341001207850001c3c0842c00e03048d110104a00c00e40f5084500c8951f407424100c403048642111040a1019041c08049401d4005a0303074001c1d4161000107403d0b00320001440c00d80034003042031403118103144000340c50a5000c0c151038040d02d0296014054021b602d10240c0c0c90380a42c10302c50100c0310082c08100040b83c454091107400c4000300c402c0d03070301e8802503803289002c0c3e0740309410602c085400c06060214402242d00a558083d16a21203a94207152540e28000452498800c1c0c0040101100c8000c100707180600003080c4030300c00c59651074204202d5184c5100039000c02d1205900c11341c110000011030032030200e44517109643d6980a882c80e104022040c13034068101610641c100101070000248490140c40107040d003411507502120070107400240070b003d681c00c00b001e10424111916000c0d0008404803810302c1503424500000c21a0202580101d0080c01a00080c03640588150103005013601c04a00500f0502981d1050320408512404141d525200d103105110540e684248100e4280c1c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 179005584 1250 179004334 179004349
    0x3060d02040603170403051e0d0c0302010b04061d06010e010507060c02030f0a1707030c09030609081905070b07020304032112020f130e130f112214010f05 68
    0x8a100a1000075032a03120780714282d59458401500b030316440c0c0040d05200b8003d0410400c0782c8016411044440b01c030207108000e844908801c2d100c014061a01507060805000b904181155440584200300890f91080c8050502c0d120500b0114035034410804600d0651040c1c20901030f0340e0068695510740710803035075900000d002e04c040031021030005112840b80a03001c1d6004290350b601990300c0d241c40d40440741c2814000040035102606052820030a005141c0c4c11084607000c0380e8224000140418031828081c2961051801c1d00004240346210307041c0c0182c2090213043c5c0c0034014020001a650b5801c801e9a072031003039020141c9100c00b80072440c064a10f12401104204840c3c0c41c2c9142d50204034240302d02039801080804050780b4011843c0c111720300c0759980c5a0024070304080340c44c10f50300f080014064400c25007400a4405581c80800300c00344201084498030a542c0907007010540a2200842d03d41403500e6503a1944040c01d1085a69028541070100c03070607102038a1180340014904010046038 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 179006834 1250 179005584 179005609
    0x901050105071e08190f020606092205010204060302120709030b160c02030a0b010501180b03010b070302030c030304050d08060d050d1101060f030c03022e230a0c0c080d050306 77
    0x49400091444000480b130001410781c04200a6140c114851003080280062004429401c1154401340c02c120055a41031070f6250003401c0041c0400c4140403c080301e04aa00075464003038600d41c00000c00081c401c0d455070041401200540041c501034588040c00c907142c9280d8030010385407001540c0811820201c40302b1020394443c0da0b080c80c190780c000f42c0d80441d040c242812410f0700c5892050004008650300961400e120f03600004141c0c0c4540d080428494282c0010700890f90b0442e0089201e03003c040c02002210700d03d11642003100e481c1d141c01d00c0e00540c0c81003c2800e050001d603124000c01d4450030020a0034540c241c0c040081d0204040c01031080351440f8440740004101d40d00c8942c0001c00c1204482ca0002441c05000350000e1141140144072580315442e8050044030380358012041807605401414660344085c0c43d2510303150707955509040c1301664404002c086d18400184140c855030b000320000e040588074228039480316554044081c0c56017066400360700420740c03c0000602512b0403c40c0d0544 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 179008084 1250 179006834 179006873
    0x60c03140702190305010b06210c0906070602040504180305181c03170609040201020703030c0503040f06020d0212090f0103020c0307080301030b040507050f0607060e120a0e040506090105010507 85
    0x8060042d0002456507203034075820480c40c0190708050090210a000d00c004c01c1c00d09645241c03800064950140401d4004241410b19174a00b0020581c0c0c0c4614000301c402ca00c01c0100a941c840b07003282007000082d84903204140c07049103000080c80160082480360701009030140c4920f270500125644110070b11540800031680101c0840010344000200c80034544c80602a07a50040f10002d05400790302501e4003c5c103070911803041d0707008020050fa070000d409000d40c0c2c1d062420300c240700d11500c1c10f0341c40c6000c2d0703400a0a18080102002c561540c0c0081e81c20300700860342d42200c2c00108681111800da00c11012580d400c5159040848001d5000c0e40042110700e4202c001c60741b810301d0546400006410071b80048402030304210511052103810410700000d0101200d50461781c2c0701200c000380780f500c28100e00a1140342c440c2100c0d02451410701c1034001d8020f41000c021b40e41c08002c44010f202d1406100e425104900d0040403e60a04bc1180d07220306850042c0c449515082064a941c1455a1100c15011 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 179009334 1250 179008084 179008087
    0xa0b16210c03090c0611010f0b0d030c030c020904140d0c08040504090c08030703320706090201050c061005040c0203090a172503020a0e04051507020c03031606060e01060c0314 77
    0xc00003041c08100c94000c15540e86c44805201e041c00d81542510aa03251203003606c1d0070104200d0781c030f55484c000969543e51600b400000f4094500c0d061311204030041c4003a500c05420300401c000d000140440200841c155803c0c0c1c5ea408901c01c40a031407061010320003404282c0140030503c04c0341015440088207502034030350000c3c01070351040e42a2940d801072004030001049140390440501a0202c240002c1888072201d50148950b0200030583e03000d90300f006400592101c28000569003e4400c840b003c00c065016580249003104030300b0400d1880e032040d14041e030329005404407094070100030340300d0b511002001040c03203901e0650b540d03480340c851100444060040030080c6600900032008086007402074103a450f02180b45004204414850394001c0c0c4007903940c0380c00c200014601085030200c02409200302d8002d5120018202e00d40607250203801d42520000400d103aa8000326268080a43e10407101844226298050340d06022028071600011600e41560080003074090b240030482404140c5555 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 179010584 1250 179009334 179009351
    0xa180b0601050d0204030516060504180c050d05070e130209011d0109172805250b0705011e1401090908160f02010212030601050d050411030a0b16210c03 67
    0x10220ba015920880f0347e90320580c1d89144915010700c0b2030300284070718200b45003071902c2e140440c0c1224130318003207808501e56075071513a400b9507000341c2c1500e440084010f010015460040d001414446032040f0181c40f9103074400949116003100d000b100c064240682d100c52030741e421349406003101d008200403207050006868020603100030000360144020140130052120038280a4803410130303000c1450800012452507105070119100141c2e40c030120440103218820301c00c0c940c101c01004074070f680168200400c0090319205100d01504007183d100840076060307a003551900e0b100d004403400500703802d03822001000100280c2d00e460f170081103524014420a4500913101c141052403814140e001c6a0081c1d000078440b0655038100308002c000e01d150201349241d030901000103081d40c001d00c0359141005490700300150070802d0864182c80e800303070003508403001c0b8161403804140001d405c8030800b1103014400d5150188620589402080c65540c204081c265200c1400300c002401c0b00050801c241070b22204c19 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 179011834 1250 179010584 179010607
    0x30308150904030206010e01060503161b0503030901090b090105070804080a1101140103050f07081908120c0405030d02030910050c010b130204081e0304063501030b0a180b060105 78
    0x2030610503480f0b940504425810b00000500c1e59034180c200c401003002c2441000140703c0300911552046056060880ba4011a01040081d0495080c0014141d020101c2400036418054100c001124401c10700b284856464142d80d034200e800469051001808090101d400704001c00c000b007001254038540602c00300c5181482c1c5080d18105128604041600c0740108103210050000a9605280c0b82c040c005080c030b004100e0750380d107244000e00f4a01c11505180d403070400c14820b04580311003003071113010030b12464002050311054003e40308040c00303805508882902584040112141c159005004014014a02c0400c44068000c1410201503668a25082d103207a6210315405201e55121071015070f407503042823031290a00d1466002031510005140e1968840c10f00403080d20142d0300c00c2c0c40c25040503084902801440d9228400003101e00f90111000013076915180d0700c05040e070740200c1810032540c03141080c041c201c5402501d541c174103000110b08000020045c8807000d402650501d007090401c3c441a00 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 179013084 1250 179011834 179011849
    0x303211b030c111b010e09070818030c19140a05060123091f0602011a1207050a090b0a061b1203020f0c0708010e0a08180307030606090b090f1003030815 67
    0x511048400c10380c0384c0c07516603030051420fa40c00d603050768900c402d810580e50191102034058294111a0f11190301440d07855010400c1d0782580d80b05204440c02031540c42d41550400d07040050545207241c0803402d100c444500020340c0303854a68000001c0c41c5d40d03803821806980c4062030784468108941c100d11014010742d110800640641c046030f13402103100740c0002134450900c2c003c0d4002000c1da410b01010380c8074461184d4649965580640e00200400b40c440c2110342082d80b81e412031039101480c0240031a500304d00e58849041e82d00244c07482c00c003103030311640160b50074110043d5906c61944881e000300c000030212079488451031003078107000d81841c07827540d0484541d0f044081c5800d05540440c1c0208881d040074028a502120f6450107040c40b04076a8427080610700c46d001c01e143d1400345c03200151b03c0940b000c101120065801800401490342c40310080c0d0060b26884c44128400c1c2c4501e408100301c40f41c54010180242e00c8900b400c0d05140c510b030380a50303604000a04150f121070800c4080d0714161200807 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 179014334 1250 179013084 179013103
    0x30602180a0f14030703050706080901050f0c0a120b0303030a02210601080403050a18061715031009020109050a1403120901051608090a0303211b030c11 67
    0x400561650000d809a00c1040d08105803203204003150030040100c00c0c518115002914400b2003250305152001c03010030f00e0802c440d40020090b1103014800981140d028a0281c0100c5207a0b00070f00c0301d9125001d9116140806550762180c00c0b10402c440e90482c0c0c00341034003801d02806044082904103010000030b085400c1200d0b03c0039600c0d00050440300d80d050552003285503001c0c4401000c83c0d130030014002468031600074001420710200048855605000701980c22042d5a025038100d20b00d0b440d408001c00c0c0080310341c004007030f103030103200030441d01410204d030850f100d80080c0c000c0001c90f1064082101810102e074050b418800f400c500410142c54500c2070307201912030311407014080400303181858500030410190700d800e541c1c00d000d4180c0b540c0e032000407180d462440300307843d202100d42828118010310035074407056405070044400004154001449000c0044001d0002e14003001c850038000941d9041c204903411641080ca009010074002e0340041e80c031150707502d010002d901101903400e26226036507 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 179015584 1250 179014334 179014343
    0x10b10050c01140a0b01020f070f06050304020303040f0b07060c0c0b0f1503010504060204030c0b0a1b240e061006020a06020309030717090f120309040902040209040f0b0f1002060109020a03020f030103 88
    0x105c181032500d58040001080b001410001003405510341500e0041e20b001c5402810100030b8000086002d44d1780402c2031b078014100385840b001c08283e45600c0908958001a0300300c0d5a103080060b113551141c060fa04402e00f1a422210011203640c40b50411043c40a00034203080480c441b41184a5261b1402d2040300c1c812880343c40016502c500b14207019900c8603c4d80d110013700b0b01c1c1004000c46c00c0750301c4030059031741400f0040310181035100c07441d100341c440095110302203260060701107080e02034040c0c0d0071400042e60a4021b27034005072281d40c840c0c0f42c6205140180009030f80720080d0003000074a44d90003194410300310703001c1d00c0c100042c80c1c0d54000c00d80c21003904503011803404104603201d46001c2111841000d4203c0318101010061170b805031720303400741040d00e40c4a1552413003044107548031a0102e500107180101308024142209190000038054141e206005828541103180070342030480365514622020703002030000ba803a14031b40001950100310340b842015002d00c2006240405640a180030394400d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 179016834 1250 179015584 179015591
    0x10170703020301050108010b130902010c0f1a06060405030d26090706030b0126090703060e0d09231017040303020903160f0605070606050a030302060108060702010b10050c01140a 78
    0x2036004260a446042c6c00c4044a64075007800002950b1ba09115824610711002c0302003060f200f1400140c1d03d00035414000380c18242c00040b42410482818143e4030310010581d45600c15444d500c0038040c19000701d015440c0c15034000d1061141c00750007a08044018940303e10070161440c80a5540d102c80c410070790300700d10644d101000602803a43c140c05401c0070150280f911980c00c0501c0700c109010051100e541d40480c418060110310072220520481c40510341020060044482d08001c00356111917500703240000481251303012032401400700c0c00f02c1442210220503030740c03e040d100420480b200222072200030700c00482042280b11150481c860b100360302a0310010388412112040c1802c00c0d4181c0303804240741c158001c0612102d0f2260489106070384251500c0b940b21000e07842c1c400010101031f0040781d03201030344003800002c040d07000540f5416181c80b001980c0d06a100c01d0400c3e82a15040c4103250b500c1840c0340710800010344120090711514a5007070003c903000c0310309101070254007016a901c0381160b40713 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 179018084 1250 179016834 179016839
    0x41707080d0c08180a0506310c05120a021e010c12020106091b0903060c031509061505120f07170717011505041404060315090201090509041109101707 66
    0x103503c6540c06044208001c1e05e011502035a90540f1042c008000400445141e84c1c048030784010451801c500360b560b9580b8030034203842c0d41402013160304a4802e0900c14843c1890050700c01201181d0b07203140300d84c080c02c01e00c8007180c69080d0200b039003010340310181000b516001ca000854140000c00031150010b03000061084e042c03030302c12804c0d16101e02101c07050b54694a0003900442e40400d91004030b0350801000260480c02e81c8003240500030b440c61a09440300141c00c08118500e6650010007240d10b5180c0c01c0e91075001e0005e00f03442500410b0300c0122100c52000c0090603031442c0111940d070085e154940400c0c810007500741d00c21620350070383e0030600280d00c003080508900c11854500e4007501584084d00007550150320001e103075110701c4c06200c18407000440c1d210015212600710101a581c00706a4cd03040c407100510310310003403105801c2039001404240001505060410301c5901660b040b5040702c800150712814003040702c0014021010041c40c6200004486c2444281c040341c3d4949071010b40003152 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 179019334 1250 179018084 179018101
    0x110303040f061a1305071b0c18060b070605040501060e0405030901020c0f240c010e030a090b0906040909020a0513020a08090615100908011503050d0206041707080d0c08 74
    0x803030060203e5590a00d0080e50384440d07980c10324100a00303105501c00301e095076600134110307021903e20a200644222000c1c0d080c0c200300c0070f801030303005980085072000780001e1100c40006c1659018032802d070007440d041007078402152940d000154031a00540010814a41d15000800401000c035020b603660342001c02d200c0300c5982d041c001200803d03070403200031b41c0440e0360500069488845803c164002000a50000c02c0085d410003602e00d1342400348020411103045c1010242c40c0e502c41205034002882d00310700891021035820540d0b9243d040684898200350808a0150041400d0394040c1d0340682c00d0700c000141a40c6120b1048001c810200000d6120080c1c0040a0a01e600240042c585500124104440d50583c0e80c0c1080d0501000c0300e541603941020b1b88140c40d204283c3d08005419400c0249581520110405a504880c4030700d0072a501032810707a0040381c80b6601507500170315144016110100f03403079540780a880300d20302401c001e0b4504100e0042080458a00054100204015404000c3d902 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 179020584 1250 179019334 179019341
    0x60c02331c0c080a02131203050a0f140d0203180f010b0a060908030306040b06120901051801050708240423090a050a0b070314040f060c0302040605030406020a110303040f06 76
    0x803500541d05100c510021000589003c8005002c41c901c96400b0681158100e07141240d440100780c9013444e0420b07401c15044c0106030780e20040c1c144020a00000c00c0d2140644214000c01d013100700345040f0b90901400d022410065440a840290280d40c280c0105011280500c02101c00c64050000050884500014000c4214460784820184100e104c82000310712004822690301c01c20854002072a00507010002da424000c0481c0d05d42100101c804210f1161f0b015801280034480f0050f6000403d2840b5807450f00303880040316131078000703032868012503a07a001e02c10a54080344101021400070180b548085011600c80e0030001d286666080041a41e90500088690b0401d26040291605003e6070300c50543d1481107100051800c2c02000006100350711031340c0300c0005146446820f01c11401e050905940244042109440c014a82102d915a8a02030b00c00c0b24200e4420741c4030305046507181e4032140000d4204904007801e10401a01001c1c40040a00046114a03c140400715004405040a4084 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 179021834 1250 179020584 179020627
    0x7020105011401110a08030604060b04031b0b1603030e21180301140114010c02150c1203060a050603090109060204060f0237050c040501060c05010b0901060c0233 71
    0x5111345019059002503000c0381e8804c100790403610407075480c0c50300c5012038020000c0e0382c0103011b91840450044200480348411810340442d54050052441d01d07404605e200d80b01d4008054803030300008003250700190207a0400c011984003c0203a8503401c1890b03110444941070341c6014071031044001403070001040ba006124000207030a034001c20207640d0660548000000c18042c011803840c0c2800c541c040c0768403c1c018a05001d40c09414a00800300b9501c84100b1900029003058090180100c02201200c3c030710140c80c0304032002050103011914090a000d59035001500c0c01c0d12135500c81c0062404560140003d00003030007680da98550710707198218028101011042c1180d00c0c00801460300d196808480ca10642e1200d5034047c50300d58544600c0d0051070510030000c865001410715000166058002d00207981e285d008000a0003960f200208000a8901c240907402c00301e011800f903040075052420300944901c11010800e55407581c01c2e00618856282c40c08184118400003400d980002510b4006511 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 179023084 1250 179021834 179021837
    0x20106081506010c03120b030d030509010f09050d030e030f03010314120403050c120f0d0503010906080a02030a060915180606080c09010317091302030405010b0d0b240907020105011401 81
    0x2550300b010340008042c101c1079500030b0104207804944170341c042a0380e07000b04080c580050459241d280d034641c0140141000316401c07455546420a805030110740c6d8014044981da101e409000122004141a4001c00325004085814031051141d82503035511480294043d600035040b086100b0491141186410700f5103000c80c50302c1d4010b200410005400081e103101402089030407802441c5003039860b515002e00801010001e20580101c079640d44d410800450694011240070700c0826212400959624294840250581c0c08403030428046401540704101891081d01c00102d006141030b07045d000d4070998182401c119041e03070002d404002c2d1354402d40c6c001304045070180131166500c0c4d00107541020144000707005442d031181c400c1c3c080d1407114100c41d40050020007080503034907209a201c000b074004980448042d860924651000d28059210818040e403042d0581c5030f90b0382da2040310940c0c048c078a601001810310b6941c100d0442d900e10034418461180d40c1c1c000919903140034050306007001c40190150 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 179024334 1250 179023084 179023123
    0x1c05010b0102030708161403130906080127170415081806040b0a0618060306060f03050714040605040e0105190c0903030309110303031602060f010b04050d030c05010c02010608 77
    0x3400035172190141c41c500d055000d910035110006003801410f0320649071110316140800100031200c4072030211650182c3c1c3c07018a007000300c40d0301c0c0c0f070035103007240d2107500c3c0201c10700313214100954001e021460b000c5590744612529007080302c0c0c074030150201d60860b4001d140d84040060030300503500d03800211140d00c48103003120380d00b4404444421545400002e080a0800c102040005400d019113401c048020000b60030181001040140c4100c01040d850100f240d005040c03d4000a060070304d0b0b40008140d030380020140c084540342000070704445450b084881e80258803044009500d0f56180300f13106074007605170004150342c07400c400790440c2d480c0c0384102c044000c1e00c2c03c41c000d0345559001494500b560791500b0001032101e0641400f0030b841c81d85540843c3d162000204102d9105000144043e081645408451990b100c83c0c3d1500030360b000074014012803c034280810029450219448814a402400c006404003419150f880c02d64128004482c0903039110780040004141c100309a8020744000751070203 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 179025584 1250 179024334 179024347
    0x61603021204060914191104150501081f0306050411030a030f030e0304080d09030c060e0f0d0618110f0402090f040507111f0f02090f1306051c05010b010203 69
    0x1841d054050006804680d99140590810a4204c05d4841c03800c240f07000c856100041d28a840b00044240c00116101d1042c0806181c0500300707070080744044006c5854040b42e190400004441c0507900400f070703152a815151500900d50742e0704000c0ea01540c040c1c0c5020800d46000c1c240542415001d00c0c049010354002e8a4274004a5030191440e4956041d500c0e01151050b02c0800062841c040d13504041401c2c003030300145080480e0070401d6801240e1041c6c120090a0313950300b509440801c0d1110300c80740c1091003042000f41d5072074000c030500705040c403450000640000c2c03620081c040c4084480111000b4040f0714210000d403922040e20502424211800c0d481c28410501040c088c3c82507040741409141c85401064055008010010f00401d20004440e04030802e00c2c015088900b0070f030750300340d4050310700f001c078401d02c41c558002c44401c500040c00340c844021590080c0514640510340003500c2d80da80d4400461250323198016540209a070441064614109003021400c440903408445c0c155030040140 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 179026834 1250 179025584 179025607
    0x714090d0201030f020409111b061b07080c0d030c0908010c120905030708120402090a0615110709020c0708010b0906010813020f060a110601050306071d120102070506160302 76
    0xc0064465081c03070701003000001c880c24400039000316040094000e04042c1b08000e00c0e12000c0c080c00301c400c8402060700c0309000e6140120788ac0d4600343c2e904094110503241140324108003600401120307100340a10b61078203440c00030090074256410f00110000e078542c030041009075480b11420b006001300138000c0040a444000240540d03508a0303030400121745840311001400000c1c0140c410454000000300c1d603400e103504003101030f40c0e01101e049100300c88903004aa0541128803034141900d103003401c50107120040f0b003401e0300ca140340511740100e00e2081e604085030009240c0003421008042000403e8501e041401003401e4900c3e0342004d5005138a2002040196a8414803070758001c000c04410b0144003c090020501880c03594141035045240000c00400745c41e4050740f064a1540340005440ea281d0b26070b4105900c48109641c3c031800204480340040d80581003e101c0c1c501c00c0f4000700390004e4442000c089500707a804c0520113a0300e40d08840104202041012021030784000c043c5411480c0000724000e = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 179028084 1250 179026834 179026849
    0xa0b01380a080405010b090403050a090b04030b04020d060b04060602030c070801110406110102070605070e1306030302030f130503120301030b1f120203150c0c012a080402130212071409 81
    0x1031281c1000452004101809000e50102d011407601501c640c041e45400e0070040c00300d0340708207900780001d040404000f403200000002d0300c0a82c0da2000320405141c85540030400342c0c0402d00c84c240c0320160756121488680c1c2d258403e100040c6929005907440d491125107203400d10759640d00c401d2069040c49404598444003804603000d40300e1071308080b600c012005c100c0e5402800780b010020a01403400082c0540d054100450f400200e40855071500b03000400d1074100c2c2035030160b2100602503403042c0301035084007840300c02030190b5a103840d141790f0025a40d040001e1a0052511071901d42031300000050051041c2000800d40c0202d803003618041c51296440e0048900702644103400c00702e40110704400031075400b4400501e60001400300c8081d5804c0400d4054060750056075030042c55031900d1b0030820824cc030856000c0c1602d10f9a051542e903007403403450645491500070800ca0713120442c003000e03801c0d41001c0e00c0540b040b6000141e42d650f4906e0550300107020414900000c80d001103091250aa25035a401c0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 179029334 1250 179028084 179028097
    0x1e020403020a15090f0e19091a1f14010206100602150415051501020106050102010603020a0302090601030219030510060e061b0f0703060905070e04020d0809030a0b0138 74
    0x34450300310030780414041350000b5281e000703103880b41902d1400081c01654400c010707010755001e03600c15680384070b0301d0302c04821a51417900c02130048408a941c412004440d040b1300d6440082104100c02c50380c01200030904850300380c1c00c080d4000d0a517926084c00c95a0402c59542e0040c113260720080c845042502c0603640d60504041c01c590b1400c0c010000d82000300c41c840301c001034101d01000b4040750411201100711070071890140c0380150300c0e02c800090b4075841400390701c0859801610307601c0c80c1ccd030940c1c0038440c45d82d00081842d03051540810107941c21036150f140c104081c40981c2d0b40051b007420064001a07940025500450801030200c4600001d540e81c0e4080742c000520840781c1d8403404034091281402c0c035507290310030103160013020b0740002070200d00c1d003006650b944902e0030b032203165131038502c001d0003001c0c01d60700070750003011905070500010b40c00350043c100c40c1c81c001c08070b07403075042c140d0394a422109090700200f400c410a54400e170000c4a840c0d81c02064041c1d000c0c030301d045202c9078803001c081a01596 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 179030584 1250 179029334 179029349
    0x2102100905031908160315030204110702030d0903260f160b0112060501051c030c1a01030f0501050f16030903120e0606091609050105070311010f1e020403020a 70
    0x211281010803070300300203d031800c002500f5420043d02e03480002a080042c00c4581d00c0c5400109074030b107008140320348501c2c002c8210711000d08070000d04540171b100c001c0c00e2044001004220030017014015035402c102445004d1000e684006615040d031600780c0403014114000c1c80000108440071100e03170701302c41c00c2c0d03441656580e41103915030026902c214100524081c4c041d004040c100300120700800d44100184060340612018081a40d80d035044c04202000c02420044450900c850080002c0c0320b00b102d0700d03540b802102100c003554403926695080322802ea000b00d648042d00001c0200b00325081c0a2076501c51a001203402c1146000b06800300071703200700307031502007015070b103861140c01c250040f2400d80c030015800e1420401d01002070b1540f65103030000e5980d180b03e03045510026492030280b01228402d52600d5443c00802841e080054466801c02c02e011000d114202da0380f080002c00c00d200300c140d046504076001c07400141a245440700c1c08075441c0400c1045004010503c00368039103608840441e41c91 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 179031834 1250 179030584 179030591
    0x80706050a0e06090613080c03160503030a050337050604020702010c020f12010e030714030c030a0302161b05040606030e0a0f030309020d050a11060711010c0302010e010e030304210210 81
    0xc0000f443e61041140511070380784003010209910071f000517410900d6205408441072001040c2d03900560000314400d40358540d0003004800e9090b84114061a000712b02041d8020740860442130880201c0144013070300300d11102400c800c502901c618061030b03411800544045203010070540000b068491425400b80c0903d401d440c0c81360032502c410700307800381d46052030380200300780e040c0746001c80d460754410b940c155150242c44080c00c00c03c0c60003104072001e1a6950004501d00380c4d00a006501940101e0707409181da0809103400030101d60b101562003c40b900c11101c1c0c0c280113060104000c00c89640343c0103070b81050f252440302d020300c42d80021929003072500511500342000103864220003a20080c0b00094001d9420401c0304200000080d00d0800340303110f0300b08940040b24800030b00c000342c01814400790000c00122884c0b641135000e0001e40d1501c034028070000c00c50f83c980c6008142504c3c0c03020340e401c42e01d038000010481400382c2c070134200b1011401c4030110034507082d400a0007592051a0818121443d40c1c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 179033084 1250 179031834 179031847
    0x14010c0203190303090b0c1903050a1b030c0908070f030f051603080711010206040f031b170405040506040207050706050f040810050403020d03091e0501090615080706050a0e06 77
    0x50801107510503110400b1205524909464020090701034880300710381c1a540f6001254000a4200568010209854902500703441e000350840181001801380501c00d82d48400d003841032240c13540032180d6103c8a44000c00c41446540c0020105480781e8400301c196002050700348101407080010703100712500009048280200f80c14441e041c440d05040802080c0c17022140001000b06c030b0400313409024095124002c50604e10001a619010300b1200105258842e54041e80081d01a074146540000c0f55441121181600c8d958184035820f9075000f5404290045410452450309010300707944400291000c0d03081548603640c1607034801c0705000344000e003c40491080c3c030100118042c1c900402c094411908c0361900000b0380d030300406040c0c40587c0180221000a0250b0303000380188000c45038408400b5194100c00790f80c8010221503402c0450b115503c81100d0305c0401e40c1801444405cad518180c08240071440c1640c2c0500e80240c6500c00814808140440e00350542c2040c41c6060903103042e15459a64003 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 179034334 1250 179033084 179033089
    0xa0201020d0c2003031312120e06150307030b01062d181d010e0c091305091e070510090e1f050f1311042105070b0414010c02 55
    0x10003105680e598070700b22010004a42c4a00e042c034146040400c005410040d44002a0301c91104170380c02071112078551203103400a101400050200c1c106840c0551450f01c1040c0c680e000e42e000c0c5802c91156500c0642403003291200321520000b104803c40c000c22031586950f84074650070b5014031030300741400000302c02c0b03100005091400c3c140001c40343c7e00b42c9000d44514107010706003000940300d180c910240040301042c01d4646601c1d414402000d4021465107130300c0d181308810344800050508084070800d000e0300c400b07034464200013405500242004a03030b900c4c0c08000f4034500940f251031000c8a1000d0705400c400d00201207168400d0750301c1614040c18071007032140243e81050180d449124a242c260080055404e12140302d4984d91100c0aa1316041940e180d082000c403800c03c05541c0d620504050602008240304d6000308000640011f0795420300d6520070b01c1c000315615800780c000c44030000c001d020040190a00120300540991215942454100011b034945410f20820361414030101c04201015907 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 179035584 1250 179034334 179034337
    0x501021e0c120f01050f010302030a02090405031b01060905070c0201090618030b0406020307140c0709090c03060507050a0f05031015140a0c0218010b071b12060b010e0a0608010b0a020102 82
    0x10740c0c0192281c0348851a4600d000d030388050060001a00d5481d0601103a21001882d84550407680c0040050a5000312a000c0291368a00175208441d284400c0011009101d92000f4540000500d0030001910f140780910a2040d101c000301158108200c9000d07501c0180c0e0403640140659000e8900b2a080f0440c06038401400041c2da00050030304402c5900b00700411219400451103a0401d80e0b0300c0701c902580d200b0100705800790010201c8a81c20080040c41720100a500c941449030007030168100459803a15958211203042d1568000583d0014070214a030b5001095220154420704e4001e10350318020200c0c203081006805002194020720307540281c0c0c0c7d4414048964124086804540c2d19000f803200a8401e95031208103d00800443e522881260203411002d812264130f030b61141e141c0b50113950b03270307087c401146118440000329100000c5040b9645070314140b4510700c40c00c00090400d03643c10014010308280c103001c0b845100714940500070b5640c422042d504494080409640b07598102d4003d074060b = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 179036834 1250 179035584 179035603
    0x90e0a0507091712070606050316030302060115140c0106210f0807060e0d020f070501051809180d120b0f01120b03030403020405040515160804121101050a0605190501021e 75
    0x4c101021075081d0501005c0da12020841e034084044420044494580c12880800d82c48040c0140e0415001004102000507807106580b50707614102617078840d40c00c010121904610051102a0354458003809042c008403038405696a5444026090b07080b00e6450320000480c0e8040244a010081f072031004000c01500802d242d50500019a4184908054004c0d6606d0314062064014030429000240a5014030708075036078560707141d03120104000ea810038841001c00241c0fa00410039007003805c05882c1d4a080c04945809021651580c0181c0451580d1405641420a0b014071500b00c02d41c00841681e04020410340c2911900408117140680c00700013411800b455002940250074a010042048004203034100402c01500d00e52440d034860244418070084c0c0307415900003107038240d800b00d404a00b44119410300070105d1700d4070341490450040f01c0c609442c0180c4540302200c2d00c0306d40a00c098644034401c0c00100d151040c2101019240c100001d640382101b191080403140305141020200d030043c1f0a2a52 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 179038084 1250 179036834 179036863
    0xd05090609120a060b06090306011205121b010c140904050c0409020d0203090f0f06040b0613021c0c02011e090c03020307080d0f031812020c10090e0a05070917 70
    0x2c8107260080d82901d8003150003040310103d18004419080e407030404140c07602d01c1800744c014038040c2c0c01c10203460a508a841021f031307124883d0401c5481094011402089040304207424280d16aa94008082c255214218440d05000c01015410103200704176003950704180b0704907004150364681c2c900d020010b1046c0d801681a0b00d00001c1c0302d105e0f50b00d140d00114002c502d034004644510402c040d1103501e0342443c030f180300400d410030340114020410030041d10340c0040004001d0100001481c0d5004101d03803080d00000140c3e0321000d14060500c3d0588140d00e410302032400203200440c123108c001c02da503028048940c00c1c402d6940f21000c09001d81e940c10603000e56400b8040302d15a50301d83c54850707900c82409906c90000ba50861351901458443d004050f4209988004042051030784d03038905d0500740101c14840114425054441c0459171000b8003d8810b46464541458040c18080305180e01d034801400001a14180310600c0740643d40300400c1070845800981060314282c80e00d04150520340e14480141c0c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 179039334 1250 179038084 179038099
    0x7080a090f090e06060a0503150901180638040207060603020d052d120c1603030f090e01080c04020f0d090b0105040606030c1e02010605030610090e0307050d05090609 73
    0x2d003000071548250304886941044031402c0c1da9500805c280042130f0b00900390903800a480d01e1100703440b103030020307504610100008030350040400603840c40d190f0b81840698100761501466862001306801c095074000018902045000d0121400300030440740d130080a0041c1c1d8006603a20074003840c0d81c40702e005580e0003015800031105038108507035212540845007445101440c1f051280703172180301c0101c00d00c482080c0a8488040507003001c0490707400030030f00103059000c1c1908085a4204011038200614407d440b1007038044c1410700d0040106000d5008110310b0380c03070741005111b5090b0001e9888524003040f100580e564805c4036000815010310b599070410a400c1014500800c104004031505a0f131050360100080e55480004406403084000084080349540601014280c01e80311105203543c0c0381d0002180095980300800c0ca40302c0200d400c641444141c40c014410100c050040003003103940c1100a50815400e0b4460716116840c00d01481d00b80000040c48404d5034480c0b105031003036540000e1108 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 179040584 1250 179039334 179039339
    0x5090301020d0c090501050a020a03180e040606140d0b012903180c1c020904081303080d0c14030c130e0112021003020a09050f150307090303030b030c0607080a090f 72
    0x50020f8480202164007082a0f504003043d954890002c1d540806150750050840c0c3c01e003034030184e4100242c800354804800360207001040c5402c0f40c45e4041c4c00b4074441c1e00c00055180c500707280080800e02c642d1300b49100e1940416030a000c03520200c00d072815112030403601e010781010700035561604d0307080152042a5003008020010180b00c0720400b00c41002c0050f00b50b43c00b0300014000c1040300c400082c071240603600c3c101031910260814035240c5030701602c102c2c002c0e4603011110080c43c88803806d81e801111f42e42c000003210303590304081d400742c41500c488509014280050f07a081d1080720740402880e10300c0698005c01d8480079101d03540182002003410300070046055840d13180e1002c0901d10960242d0089683d1516240fa6a1203442210059007150f51500c171420305001c2041030030141c01041503886401c1450030380030504400c2c0118010a415141c8001141c074514018041c4c0d0410401a4071a811000da405295203032103040740c661943c4046000c0c0c2c1d607229075000ba02c0111003500514110319842002 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 179041834 1250 179040584 179040607
    0x1f150807030b0105010201020708032208130302120601030b0c070c0e0f040639121d120301030f06022107180e060a09050c070f0f02040b03060717070509030102 70
    0x311400e80740196101142c5a80322401a0300342d2203601c0006003510010400904c1880c030010012104102103200340c0b052980315254404c00d904804450f04140d1aa0701d010821480e20180b00f503140d5000030041c010941c59516407075a03d100c0100720f400c103020300140365401c02881c0740c2e1300006800810001030301800d2007076014401708011602200d12030310305950b2140c1592021f0a2004174800706050044604004503810045040c0064010500828010001d0485090b0185900e80c1200082e100d00921009100c03919000361282c0004130303840200b0041c404981c9614130010483d03080600940d0b5040c49801d1500d013000d50324000c50b60b05130b910003404840b40e40180b03030000c1d8900d4410300c0c41106480d00710400c42d580c002c1e9007090380b141045004124011054000c81d51061151a1490034810181c4801c01220382d0b2032000c480340d80d0402c0d118003c46c9490310424416420540040ca21032510341e40150900b01e40038845209228484001801980701c4c40845043d000058020341d26130700e80c501c0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 179043084 1250 179041834 179041843
    0x6020303011418010b0c100e0a0507060f090e060a080f0609010506010f0504050427030f020d08040f020918030706090501050112023304140f0604081f1508 68
    0x164161600320b1007514119842c00d401d04810041000e401c10495919140d0408020380c0100c21040c5640a203c019540c0c0076505c0c8150b0707090000c400050400d07100380c0c1c40d00d42e00708070450b000f001c00e0210081d036030400d0740e6000f0a80030070b8034040b00170311b00e881d1a10000030714503504503807003840c01d4818110f20f02030809001c24080c1c015086940240002c1d140d120040d01c0440b03c100c000b90006500344420040c07032038560000c096101c0c0614400b6000ca0844010b40301024003c081600442d40744040c102d60750390304000081c20314195150003002410250ba900422249868000e84644004408120a1141c3c4c20650b41c20500d207400b2a99140c1d1503103003100203002c0b400e03015196546400d00000f02c66940e03000d00c00310694010b20b001c5001040540c0c03a00300b2000d01a071100943e0b246039850014070307003400040c800740400440401c2c598040c030041085010b60b05005500a850030300007049a080d000a88801022004412810684041d0540c0700103111049070f185010a8811780001c40030404603 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 179044334 1250 179043084 179043089
    0x3032208040303230f160c030c0e01031209050f19091505090c040e06010f03090503040e041401090809010e060904020d0b1201051306051504060902250b0a050c130602030301 76
    0x3042e80c1507003413440b1004480d020382800e89400a100300704821107070205010407400c4522030341034110000c1d204d803985042d40300e0a802c203001040002c4014030502040040729001756803945000e881c05070805002c2160302140d20455805030858400c21701140b81072500d4100902584d03201000401d9080c0c48181200c02c0510509008aa20304080f50595041c0300403036007541c019280060468941ca80115030500c545800c080401da070783e00ca0b45001542c240f000348020314080f180f03440300d41418200440d50807000f20301e860450385040081030010b0704200030341da0a44c4090901407403184451001c6580e0f803041c455442e50043c400901000b174003080303600c1644800c00582d04084103544c4c54156908840d01907407803101034083c614101001414540040354010f01c018841c2440c003003828007203001c0c0c1e49940c012070f194940125032820703001d0700c5041030132040740130f010303614080135841d1250742c01c444005c1e060011498030b84c030005603540c0e40d0004841c4c004011100181d011a540d0b28004d440750403e0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 179045584 1250 179044334 179044367
    0x1a0106030e060105030705120304240906030e060a0e010e1212061e0f0d060e0a03020606010c03051b0a14070603050a02040b030f0a0b0604030c03170a0203032208040303 74
    0x20340010740c0e6010010b405030603a007001e4014101c440c144800c000105034810b090628900c010440403071001403e030014034004a82c03c00702c24076008031840145c503000c2d040e04024201880c0c4078017040300140014140c1d030000f99203c40014203403c060b65090141c4554074984401d446810644101e820182000f030111000c40c0303082c0b402980340d241c1042210a402030034200c452460001081c1d4a140c504260031300624000d04071404441c0c290784600503035252103000181c6030040303001c0005064041c44203035400042403914142074400369802070002e0066035408200b00d842d41758003c200000800c45000c6050304145d1040d040103c500c04a40c1e507132054003a410009080002240000340341d4002d840c10360b00c2d004100f81c1580e9a0b05210707007103100000c4c0448407458a506014180b07440780c134000e001071401448104506030450034a8006030072500308003860b14504201a032a00ca6021044c1c0b40c001c0d2000765188070604084443c3c01c421145510040c0c070403400010000105500810f61075900b04c800d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 179046834 1250 179045584 179045591
    0x1404021005041503110d0504030e0333100b04080f0c0f100503100506030c0c0c1504170f0714190e01060507021309050a03020f0307020d021c1a010603 66
    0x40302011a410301482c402c200018040240300c035101406508004030a050b290344082c2040242e81c01ea0003034035010b45040c0c004c148000011030a07400c013801135000303900042a10b440c00c00031030010303070b02001c0c0004140d411603814900130412046080410034000c010b1000c105444a441e040142e03242c048041100d8185d2064441d49002402d011302051050300004040803115142460203030b48039031004200c0f180c00d060003a004100c0d5501d40000c4c0d4060400d080720a41c548a60880070741c0381c021483c81309441150441111200800c21108403000c3c2c0e14100b10ba40140e000680700c9030310380340c0b0882a00300203000d024004603401004600046401004030740d0010a140f003002100303c00141401414101e4101c84018071601c0e0140c00140b0003c0c0c8041d00b01c003540a0061402001c0b9499980e0403112a00484200814181d04001f040118181980a50714080480e400101c200580e064001e004800b22800440140c0030301c80768403400368100d07000b0450030189840101c01d070780d400d00030a40170914 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 179048084 1250 179046834 179046859
    0x91d010c0f08041112010f0c0c0f0809150d02250215090112060e041221090807060c27030308010e04050307020a0f061e020607030c0e0301140402 64
    0x141401060350010003a111103071032001140089a400000603c00d07104600b100c1040007160700d81d4840d850b5907013208000043c4400340003400300103035412212540204031480040c071021400201144a0140d800040140ea8811040128000d04014148144901c0c1c0101e03041d410101260001c0444900c15030424040d034401b408640c0c0710030040b00c8040d410965502c61a900340200a008124070007050401d522518070313150341c98040d9110780e00014403504c0348100780010003010b1036150a10241605044007040c2001c10200641010042a102d4940d12a14000180a4074a0032a100e860f02300000380f0011001d08006030544407844280311650320084681d183d81c5000c0d040384000e40e0b41c036941d0450a6442d00481d52503101010b4000d4407e40410000000140e0369840c10b040208010000c0809082c0f0b000c00252103440d0243c000081404100203000f03400d03501190f4a44e1015043c00e0000c1d07280020030b003c840c6000082e400d2900366281500401e034080480100e180b20307910807500c1002100 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 179049334 1250 179048084 179048141
    0x203060604230a0b0a0305031c050417032a030f0a05060d0f1502040f0e01060207030804260d02010914030702010804030f1707030b011805150702060d020409 69
    0x1000040c02d401042405021541020541502903400000c40b500c046142d001510000f007030040154070448450784002200c80c00400345152402000d07400c154100018078050302c4da1a080d42e51892100c03443c130300000008109122050003007400c0c2c094001c103020020383c2803004401c03980c010740d11055909494400a04080317864010703180700c1d0300040c2018406100d130340d0700d91150388028003003113862015012071070145110504c0a0801015a1032014040520340300c0791140394201030304000d0454000c440c1c2030000c00c038200100d500320303480e0341314070090585240c2a56001503812607402180303020704880204401e41c150421894180241c4001c07490f0f0000381030b000c6e901e01c18107800078086204500000d01217405948044d101d2161400d0030780849040340030b44044c485040f41d59030080303555100e00c1c1105523401421500c02400000b0070114050a0100180e40c60010f4902d9444100b0f000424008545446065404010706801c1c15501e413500c50007214080e050740303030911100c50f521500d5804d811 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 179050584 1250 179049334 179049341
    0x30105090a150209010e0d0b06100507030801061101021c0c03060b070c060509280f0e091f02040f0b120c0a05070209060103061512060f080c0d0c030209130203060604 73
    0x2281d010318036420030b014600300c04002e900040642c906024110030070810548840000c000300d0740c0302d4104c0f001146403000c104040c10013a040f02404116040c020140040d8200b00c1c0207042d1134050800325008041d1b4070025000e403243e4900802310100c21900d800450310341d41c1242c2109091a103060000c02d4561555021038040e59402420b04a00d16500308040c5001d100140b402510241013420f0611411450b1110303400740000900441000020401260700c02c0c0c14140c01510b200f203010501e40c104180419641c3e030084e401c501070980710358030708a003421a80c0d0444000b40403140c0e101003400e81e11440700e04076402c4860312440076505040050035415001041b01e001d919592036041c20071a59030244072100300018100c50605540390008a400d80000c5209600c8035080d58800d90750070184440c980030b0301c0e51980030ba908600500014418054040303196894044281c0c0c0c4802081ca00d81041c1701d0501d19640082c2d002521b05050040c0320650784040c1c2441c0e80240d040780c4194031243e041c8000c5 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 179051834 1250 179050584 179050603
    0xc1e030804120219020f240d0f05072f0d020c0906010f0c110d02061204030e010923031c0c2010030207050c1012051f0506030a0e011a03010509 63
    0x4841c01c0c0c07200b0005141896042c1c540d1440680340310100d2440d6210020b10003071303a000b640c41000010a044208d20f260f03016668510300c94860521003420007250181011a40c280401d0112803961078901c040c0300590705100d50341c0d00d15001c0300e00c1440c030000e0181d115015085c845000d0000100000c10381d5000c0c12072075030024019035401e108003c040d11803141c3d000c40e03000c03010344c09020032041c81c01690314203014080068204a01d200f00307090506d4094040340c40d41d0b440e10305001e01d02008002031901510546040600c51041d18202c44080e00000e0030002c185c50b0042c0301d00900d115030031800d9405244809014403130501401c07000e030207101035041908803151050340003008008500c0414481d401500995105401321142000c8003400a60402d50901014000030622442d18040300c845019564002d203850b1180025004a900d200a80042034001c0c00c0c00380c080040420721707002032607000242007a80740b00208428450b003007880c05050599a29140300f503082c08080f920704540408e1321001d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 179053084 1250 179051834 179051863
    0x130e060901030312060801020f03061314060402160501060314160b04051215010b0306040f020c060c070c030c030503040501091e090e010905070e22030503070c1e0308041202 76
    0x9a103541d0f070444169020404905405848400003e8059400d0011300140c804038015540c0383c0c07a000007880b2000d403100c400c04500da42070052202100607000011504500c0545025a5650428081c0a240f001103200105158a400800001e0290b14610307141e6180c92101510a05c100b99415000c001d00c007401411120702d400c000c104805d28110341c0503040300610206540e85144002c00900f009031007640050307100000007040011520703040c0f0070301c0c1064003055000c50070a05e0380304900d036450000808042d0090000035081b41030054407200310008590010003542e2560316817500f6501c0760042d100702c0d804500b28040204043c400c08100c101416031944d10b441c841840e001c01d031000750102400f10515950782c0e0004a0201d4402e101075409461501c90751a40b41c203014001004111110b214800c0540800451100180d8800212500503450b0b2420004e1080d40e03041c122084280030480402103a08490702204150b0080704140c41140038031040300484400c010180c1e1030348140b115070304 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 179054334 1250 179053084 179053099
    0xe0f0d170a031811100e131b0207030309090b06120907030215070201020606331b0109020303030403050d1407020a030210060602070b070c0e0903040e01120201050d05150301050c130e06 81
    0x82c0c13414444c101801c40074143c6008240c15000c40080303540040c2c410804c1c7c41043d03d400e0219810f2100c103002841101c0d562006000c203e2854030010400c041501075610080d031214105411075940409680160160000d009280d0030508103440d0342d0000340c441240541d041c040002115001c2406071035003c0e4040c0c0291079950785030030410004010100790326051000c020060100002144000600041141201d5554480c1e00240d8016858072500104c1c02d40c1c1840b400200580300441071b20340150b03060514039214a87d0950340700c0549211654200c00d804440c00b0402050360000741a424140a9002e0307602c0d91444aa035a819903005011301d401603804003004004005840c03006281c018040c0c01303500821034850724480c1041e003050310704001650012030280180140200188d00600801100d056418000e0b40007031304d18001c0c00300f01c0b401c10741c0d940300040380c0502d06e042c8206903080081c000c103c01e1910844204554100c03030150340700481c01c0c00c1c011914444c1c80e59000e0003054000c200b04c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 179055584 1250 179054334 179054363
    0x30b0c1602130f0e071404020403050c09040525061e05040b0c0102040509040b0105280302010c031b03050c0c010504050303190908030c030d050c07030e0f0d170a0318 73
    0x80c00c2c54203440d070680318680c0c6600250710780300070740b280b080014100340162030b40900d070642c441c180070440c0e07000d24481c1380f041200304001500080c0c4520300d04401d491240099030f0b1810300c01c1c00c106011001b08640e2144240ca05158101023a0080035141c403919110544468032016440149084075400d011070300400042c0400a060b1300a4035520030700c03900140c6425211000320340c03014804e0702d080710f40a60400060116140000b401100310145c1d44a103186031042e6080c060b015241c501c8068140300010380c4d00014148a0b00d84180007460195450b19070b4203c034640203010382d01554500d0300e00d0180c2203003a0032640c4a08206c50455000030000d41c01d00003804000200c45c03401030140428484018800a4144411f2000d400404008405542c4448140d408201540c3e001814488038403000c010300c41c00260091001c100341d90054644042000002011403007568403030801400940d08044202e907105602801070040c040300d581c0c2070200c3e01b11602e0b420220090104000c01d03620610511 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 179056834 1250 179055584 179055589
    0xb01080708060f04060b0909241014032502030703081b04030203060109050a0f06081504030201060506180f0907170703020706140708010501081003031107090c020304030b0c1602 78
    0x141d0703030000d1005098081c002581000039040b141d8542c40000c0052010402c0301c0280340901030240c1c00b451280d1503d00c0c0b40c00301d0292400200c003600d0003c0c80344c410070018002192003a80450300703542c041c81405580f810000408020710124800c110740c013001d149000c3c13600d148080243c9010230340c5616207410030b0301c0b031158440c401c1c0327102c005600c91203c0070700c4000007594040241c68000c2030350210008590900d440c04505031034444030084409428407108200e440310019a00c0039481d200d00801e0066161807030101d0241c03015a01c055844400800e01011905001c0c92019102c00e0448200b40c0c24800c1605010081c3c008403001d40110724401805141401c2001c01e0302c2c0d10000310303d001481e00003a581c46000712540b0f190300018108002c0104040140c120300101d000d001c5c2420048040c0c5041220081b18406501000701000007002c0303504c6041c0030411440c0090550400c05114116103040005e603660071601c41030315805900b034007081101d042c89040316202d405074901d080368007610f5000d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 179058084 1250 179056834 179056847
    0x50102030a1d06071217060f0105041707080d0f0210050919080c06010f03050f0609030322020a0801021213080906030c13030809121603060b0a121110030b010807 71
    0x110350300310f482040f0450000b1054642c40164081c107450b1034014880034081080c131210018041405114041d10a00641c0c0c1c02c0015034007100c001c2c2001301c000f090f00100c000d051040071b60200d40e251140e92100500243c0180c101449040a03900b158017140740b11100000f070300e0781910340381c5d145c4d00302d03103c0c0341940505209180c110341d02814074545050342c0ca02009140c0036099102c584803604081d000d01c2081000d001407000004501d0007800c59013400c000094403840040d00944000185541e900b0000391120046903902e0740040001d085241c1e2101c4c154080d5214400301424481d24000299035440c4601d07400000580000c4002d0901181c031050000303650010300052402c800521101c46442c01345110030b000381d44100b45154640c5904400d02a40b81d9850420b0741203a04882440718104031a004070800f1070b0340201001c1000000e04001c40c2180225070482d5004801982d441400c0c0307e401116501026400d5032107e8a10ba0011011000c0b01ca8405c8d500c2d0026900380003182e1140c2c8100ca = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 179059334 1250 179058084 179058137
    0x150a0203070804150e06191101090605040501020307090f0b040504020a0905061b0d05041208090406030803040309080607080622020903010c03060f060801030210030504051c080f01050102030a 84
    0x1141d00d0001d0585a100c0b940d00268420114a80100c03090b0210582c400544404980700b41d030902c1c2448414040300c001c2c11441040036040004103203034a407207818250841440d10350440400c00490905041040c040c1d4001c4030100f01107032103100c0008050000c129103004403980d03280028105420201088065407102500104200300d801000c15660b82d03040081110814401c01059500d070074845260600c01075000c2002480420f2008006010a20801c400d045a0140ca456a074081c0d644c00100140b001e0341001d8030218003c0208001c060b0443d0803442601c0e070040403590659541c1e081121050f0023101c00e0341d049030001441009604800e444030000d00c1010300054100741000001ca42104d1a5a80010029880e0102040031b40c80c0c0c1e0715404060215454110025070441e0046a90000700c2100d9070209582c6034001801d2040c10b0144400c9000300300f403c030310701160358000280600303400c0d60b00107030300b4400000000b400d600004c200c4000c101c02c1d856200b101550744054041c1100f000 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 179060584 1250 179059334 179059337
    0x108060412030504021906051e090a050409080f070b09060a0515010503040606031203020703030b101b080d020f0408010b01020607270f030506010e0108070506090f040f0e010c0e0f150a 81
    0x190300d0b0071908201241d014020740f40c160303202c8e5241e10003001707905c491880103005078428000400041100c0d0f00c4500c2080c041e10402e0740c1c0070030860200d06d000d142c03910a40004050302072011402d103040240c080c0d1004e002c0c010aa045840d02d490f1004200100d600c240c442d03444480f0a94000b013a01d5020b0006140e100e4020800010324641d41d4550042c9031000c2072200e000a03070f000400000b0103806125600c124581030f9540c0380000300607079024200040f4101c001201c88039a540140401c202c001c200e4428900050056450b240318000740c0c255600680100d68680d403c05040507510351001510314032030f40041d07980ca1114100440b241652424044104116405140c4046100030304080f02100a600c0340b0010401589869200c0390340d43c0c5c0603004030071650000c60040000b6034500e019960308442c00c42e0b405a4000d04080000c006069640c14084034909000d1034415041c419404501821890348074101c1c64044001000200554004026441520204500040d00401e000703441c042085 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 179061834 1250 179060584 179060599
    0x20f03160201030f14010905060109120506040305071b090204050103050108030306010e0f03010e0f3a03020913140a050703020f0d05090309090906010f090908030601080a060f030317010806041203050402 89
    0x40d9200001030700c0d0907000b075001f494031341080c896296400007280b80108021110116100d07402d03512203480300b801900180801c040800c1c0c0e8070030300028000c0d15840c601411811a0042d54855020011350007500c12a40481c1ca1302e000007501c400040304903803242d0f030705a54911941980804015141d039048200075015982d950882184100070080440018032500c010905000803503000d42036014000c1c0c000c2081c541c820000d040c00f08500f510000b4403035140c200581c42c0c40311000440c0c0514580c9003810a01d50500c000103c02d641005c840030f00509000c101409290343e051030a4060f80700b804100c801042003040511f6103105245e11642e041081c0d4000d036460901d04800041d008101541d8409664210000403c00304a6601c000c5004201910341400703030304100d4a85840900000304014140300640f4001000980300d0750007180035080d401003280e8050f03100c2c10000c020030011700c01d14a149808100210350b00742c000603040c0c822903001341304042da4070708650b0840c050880988201c0c2c02200 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 179063084 1250 179061834 179061851
    0xf050903070b0304060e0f100b0d0b0c070b0c040b090922080406031404080301050d0201090b0d0c081806010326070b0609060d031b02010909020316020f03160201030f 73
    0x103040c0312400091a044042980741c2c1402c0c00c218044130740500d02000540d210521480c65400c001c2082805805990b40000b03040c0c40341008a10524404c1c03e004240d61510402c2014a9405c40041d2030424003460f40c00c801e81e91656040304030b912560090b41d607030280520204045290800c0145e500400e00708102d1144a602840e52152003000c502c00c41e0f85a0002c181400324581c18400e0f0710b101501441c1841445c00c00d1f8076000321602c010b000f0103002c0c40300c1030b0074902564000c070001c600802c00800000e546100f081544c000504180e030b1040d00050001012070f000c40740c031200c074000c4200908007406542c0d181d9a0341c02a44021480203000109550b140b260b200f00030030010701040ba005030303a280010f2030903004000502a00a1000784148404450880400d501c5100d449001c18443d422000e84011800143c2d24211298000055180000108504035110038403180248660703400321001144a0800e2549900403400e100b001c02c440340007010003640c400c0c3c0008010340401ca000003142c00 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 179064334 1250 179063084 179063089
    0x5190c0c020937020901081f05060307170a1b0c120809100c030b0114130b0a1103040311090603030309031206060403051c0e0406030203100903030209030a0c0e0117030a0f0509 77
    0x8881d450f0007804580c0030502d00d269580203100d56038401c00300003080c11041c00c4881d00c0005030006000d0340d401180c0100c0080e003683d029801250900c51036205010300e61401302210b401074003110080d450b10300c2a608940341c0c003034014880d44e295030790302c180c4001d08207000034403c07140403000a0503100207114001600c2c8403240345100e00e409000d1503690101d4445025400903041c600004036800a200003041124287c80d8010300000c16900002c69031590b8805082080350703200c85e60030303c0071024080000d00104000801003038151580060790050f0443d500e0004250b00ca000c112001040c40d0410480200e204d08540c2005902481c028205800c0a880c0c0e16214071b851004005402c074045140c80652203907801540003141d042c0304842c140000c41c20341e404240c41d000700102d000441a1a130b10b403901014000d4050311708816000c1d04542150f4070030f08003011400c1c5140f1522000041034000801c08101400c010244807000310b0007580340c241c80c80002c84503445000145c0040180c1400341100d9503 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 179065584 1250 179064334 179064421
    0x20f01090302090703020a03060b070201050d110906040803030906010b12070806032b110d0507020409060209030327030105040b0403210507050c0c09090601170c0405190c0c0209 78
    0x4c1c4c00366500140c80707000d40381002d4206d403120780140c110404c05004080c0140c2e809400c90300c0e0035111060110308022080c40124890044048280d41b003c40070401051140d80000594410780140040b19001d03641c814400d943c0e032040c254a01440c20300400051407090180c01810703040a005400c89448012408502c405114207400c0ca19200c0e50703002000c283c1c5070b840082c031101040c8000c060800581d000201a28074890582d00a018507151140c003001e01c86107038190755a881010b000d0325035172004c145056100d00c5402000c50f8402010240340503181c00d05208881c8100e91100710001c681e02d076520181c0b43c08000349250007620844000d2140a01d0203402000d028425541340c02d5103904404110741c3c10030200b40140340c0129003080c1040342001000030000d0440d400310301c00f000070380c0011426504102c800c1c960b04d40c106043c4401e005500300d92b51038103606151480810840354841c1c0b901110300000500c00654464400030104007440d0510901f0885000f150001c60340d1030b04000049440e6 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 179066834 1250 179065584 179065591
    0x601171302030d050d0c0908061503011d070510080402060f22062616031503120c021e030a0303020901020c0301052707060507030e18040605060a060f0507020f0109030209 75
    0x504d0120300b050780b13114203000341003001c811410022101404d00e6003881d542c1d40010500c0b01402d100228103117481c1c8080d0702c1000e11100c0d8924400081c18402492603a6503001e100c2c141c054100707000703141041d5201e441c000d4001d56005180519184c086122514540c201030703444111600d9040082000b09805064840100990b44514030f001c1e06803070b42108800c0c0da25408d00b0001c0c80c0141000704844503910701f6180c10328642070005941c0c9080700c44110804494100500d072003002903180042d04e40000b90085003030b208581076529000003104402d03031400101d40c1c5641580c84803114000090094000c0c0104c0b06c41841119110954140040d09444054a02461a0034103150600c105900000c2103095078003480300a0080e5490308100800d02d124454010301040302c42140340c0061713034450800140401d424080307280305060a0400d48010401a203e07584910300107400000c0880c000d82c1003035003420300760f00c406003400c2203034090040810440010b2810020104d0000c0010fa0b10042e2a07400f = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 179068084 1250 179066834 179066837
    0x3010b070b0606040518160c03021e030f0a0203090a0f080d200109060603170306100f0315090e0f0c1804020a050d1523010308130e01080a060b0402030601171302030d 73
    0xa007418080c40c6058030f1070111802c0401c100501d002040840d40000c0d400c180d941c1003800f044110a07404081d142335028800e0209030f00d190004140246503030010141420368000c644810442d595606108008074a62188071001d4000c40019416640580201c401c040c5800304400003e41030f45c20340a0864040700700071a01d003641c400c800e20a200d00c904207a0302d0004507a401510714240b2000041a14064550003410480484034002c0d003248a600254500c540c03803010710f48480d44429261028120051105c18980300d020554207860000190119450340054400d0070b41034488160304a611034018402da803c10041c900000e02602e0b520304c3e12010500406020f0003807850050502c00f9203d00f00c40b61418840044071010a604555a0240c1100c1c4e0090406035604543c42014200d402603602480b0070f1400d00000242c00e11021a103208a240b05280400020040800304001c80c0000e442c0c0e0350000b00341014920703940441d603984031341202140c03170071114514172076000918081c0140440e20 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 179069334 1250 179068084 179068129
    0x510030c080706021b090c0c1504030309030e011806030b040e06040506040215030601080703021b070f0501030f0510170a0c03030519030509060f220507150503010b070b06060405 78
    0x10f003a4107100d080b125032041d0009002e45c48809001030a2150b02800c141038081c0009400c6030f00c0c000030860885400300d9001800503529007828003070b00800600c641a40426002003d06000f5841655903a81e024540c036221240b80c0d04015044009021450015030800c2d640d0b00c402040c0701017008264031071817241000340300500c0c0610520598094008104d000e0207000d00a206c203503138001c4802540200031303160042c1c80b0025801c60020300085910301254a0260600c0801e14003080103102c400c0ea4001c1e00c0610584002803040400c90b44200c036292003c0541040c1480b40d010303103241c00da144940c0e001c00c0b10703d0351005460f0000328100726802140840e5000070340e1584205692a60341c5441071a044c100038900d050300c075140d00d4540040c0980d00d1000c3c0c41c0b00050300d20000c1c19003245280c102148000c981c003070601d400b544d0b404090280d42106101d203002040b08600c5042280d059a0b440c00103603041030042d60741c1071503a110262819a0105d000d020202c0c041d103d500503160449801035030381 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 179070584 1250 179069334 179069339
    0x50c1b03190f020c090403030216030f021e0a020904050a05070b04140a06081506130e040c08010e1e030409090302030a09050402090f0922081e04180510030c0807 71
    0x2415002400d403030300305000c04020b04100007034001c079006140c007506440059140d0b4403454120000d1080c40600c0c42c00701789500c184d03020f059110148642c200a00c0e0200c6004119400c00400c0384107042000c86540d5104407124401030806a044a030414480c0040b110358129a039545800e04c019600032002c0b2510110741082803600e900850000844296180654281056801462624002c3c052015000345000180a503100c80c0221038102d90102c3c3d04084207030301e07182c4c9518807003000e8070140d030b009100d800c000c1514403042c4140281451100010b000c1d10740180448078807110782c80003c1c2d4450006201c0041e10a40fa80151814944a03074041c560301e201541c0c0150000c00c032504024044c4d403040c0700d211810b84440c00101a2413104598000783e6a44103403c442d02c14074180f031000720b424448803001082040c0c0d003001d010308602c251018260041744102c1000b90b4001c0d84034503122140b5042e08401402d079654490740d0010300014042406645039194054030506030b074001d07006030f1301c0030204 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 179071834 1250 179070584 179070607
    0xc0a12030c051c020f101a0d020a0f08031e090303070311070801090b19050c030114030705040c05130e040b07030504060912022a100f0c06110304110919050c1b03 71
    0x1440e484076071800200a64047c60382c4800c11420506502409860080720301010349d41d55181080c02021140394464000e52102c1c840c0c0c1c3c4942194815415044040f0010300b9440340c040d080d1821480090002c500b0180300e51012a004141d122002d0424014000c011640e200d00313020301141c0710300504114134a810712074451034011300c0742d0281c3c01000345840c040c0b200050000c1c044904407a00b607144642d56440440000e402d0003042d5105036406841c0801d051071302c68100d806440c15107103c0609485040c0c0e5012032880d05a8126001841101440006082203000740d201c1a00207010300e43c0000d244442c1c0d603444246040340c241d041c0c0582e02013240c160410014042d0031203144a004600202c0704402800b0680038408510300350203025140f495512100c2c070440145202e20780040051106109a041001003603100383d030140c03502413440c9209444d5007807612202e070080c040749020000780203c1515050040c000a80b86206400e000c101410410420703182515182414102039980d0f00e4941d00d1 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 179073084 1250 179071834 179071843
    0x20309010807030b0117060a17060103170f0a05070f2406060f050706051f060509040c091d0403020f030d0203011403061006080702010f0c02030703020c0a12030c051c020f 75
    0x1000b04040c1404803980c45a64091030701d0b1001400c200d0001429120b600006842100540000ea2500030751380c1c03c00c0b01c0001c0024068100c0f4011104a508590440c0b14225240305441c0d00c0d07013801c0c1c410494042e00f684524028016903002e0500d4542140c01d5030741c8c241040607901da040c2c4c1040340000c94850024054400c900040c2082c3c00e1203846440c02840c0a0250300800d0000781c003103581d4100080c4208280040c03013442c051180a0150080c0e01d03850090101c5d00800c411a004514110190500300d000c0c45c4000141c82a100318003441c8490146c001400c2640284110114011111040c44aa0b420005041c0c40e01220402607100e41c100155200c40001d1111044d1099021400f4040b03100003001e080d0040d139400345030403c45030303072030000c00d07409084098002141c242c600039891040e20760101c05841001c1c843d5080d01c1c018080802001000c29035400b0385140e060f02e80540b680007078000c0c0790080040d0f1040d4259210190f816081000300c1452010f003a0250300411002d0840c01c3e020300 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 179074334 1250 179073084 179073091
    0x1021002180108011502070e04060b10050703020d0207061218020603010b0409150302060304080703020c06040b030103140c01050d09060f0f05010807060810031103030c06091006060905030d050f04150203090108 92
    0x202c40700405c5484100070741e07441c150311a13004c040003204045010b01107281c005900d041c1026041d49040007201100800c01e41c0140410780060040d00c2494000600c080340d54011103407250786000850340d4007481100207290380b9140d05c1c0b0b07840204548000586800300614001c140d0b0041d210380380d52500d542e140951390728040d0041e08000c80c08007440143d81d0081a42e80064016070800d8417051b081c44c00b60303c0c01c0c60b49400554001c602240028203522411f0045040e00d00c100c10300503c01d20035441c45540c034544204000e000c103005004980348c0810907808003544074004c0c440803682c0d20071a8490000c6461f16109070010036116001800019030801440008100074a4020614603003003042c103004500034040102195142c001c41c080036074040065480d00c00c0b03444141c0d40c0750704150220a40d14508018007100c11400c0000000d8007502800d80a030458001902a0051856541089485a01400d0300840b62003007030001144151201364052100001d81d0015643c8480720b000140c20982d004 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 179075584 1250 179074334 179074349
    0xc07080714150a210603060504031b0b01171e1005100b0f1303080a0905010906020c03152206020403020405011410111207111002030301031e020102100218010801 71
    0x2c0102c1c040c100072a000c40d5040201403810080264203450184450301510990051140c00d149010040c4009640240c1c003452082d11040b040c00c0c05003580c0805420688005030081c01c0d1600100a90740001ea0504445240c2c1c0c010380308050032240100c81c28403002c60704d44886a00660503246001d2040c401d954000802540c041c1e8001c0c80c011618446125003c140c1c0a5148040b40c4904011141c602e07050181d82e0144502e41c0700c40c1003041c024021040351103054006210b480000400034000310b950044528050050602968200240c5000c4440074081c0713100040310850114044001d0002030400c113200301e80140e07845295004000a031801a0014a000521115801503550700d10090090f02c501600b4102d10340c0c0c4c241400241065a10446c4200b9000c00003511010000740c1440c0c031951200c21a400002c080150320201d03668002408010054000420407440c041080b000c800e00c1c0341e1052040b6050706c010381c07203034200307a800842d0341d6144130f100310640710255a08045154058801d0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 179076834 1250 179075584 179075599
    0xb0a0213030f0c1215060510021005041704030506040b0a0b01091712030a0c0909020702060a110f0d1106060d260f040312020f0d0c02090603030c07080714 68
    0x40d452049162005844010701c0708070303200c54400412070b104038002d0083c110540c403410002d101d400c28240c1400c94010000c43d580c0b4003540410b40c1d00c0c12545841e1a03540d00d41c020300ca24000c512941c030081002800a407074400d07403000040c510101d100f00602c06144680080c05c108e0825103130400d003031503005d40040c2415061042c4a81e860360300580e004200c0b100896070f00c02e40c07482e20a8807810945441604000940c0010410080d2403003034000521100103030f641c5a02c4181d0758205a8100c1c0030341c1c10000c1d40b0030300400c040e0109601c10a442c002446401c415180da40c007520f03500c0751900d01043c5c1c4640c04211541d51540c00074000303120080c0d0090054829810f003510541c6ca20740420904004400014078940d2400c98448444090310445040d81140603541ca460f402c220305254001000e1000512440c03c2d150200c000114805020f07031120303107541c0e074000f21301d80c00c01090090052840f070300f500c0280101040a142046000007d01d1103002408816042403015100711841c0c1102d28000d441 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 179078084 1250 179076834 179076847
    0x11515090f080a080a0e0409080903070801060b03010306020f0c031204141f050c07050a050322120305030411031519020a02100902040902032e0c051b0304090e0a0b0a02 74
    0x1000303d56003440b40c2d401410b4555030243c4410a44800d8410343d10140c1051400e0b41c120108800d080041601001c22070444c2c5009541d030351080c2c20390340c0c18002d2201140007800100001150741c0c001d420309100c9901c1c510b0510b00045c45880c603640084900b01254880c4809120502c51aa1000e100d88056000980a0f00003020310050000f5000c03982508030b655510009003e6201c41e5040d20041c0750701c0030596200314040d040c0a0394a40006180303440348654041074504800200311721800300e41d1200d0181000c02040e0302e095990b900000c0c01600c207040f84480d102501d503002d000c0b250b142d0340c1540303000402c0c2c01d0081c0841350071078544c0101c0a100707104000c0035411580018000382da010915402040401d00e41c03000c00c0103000720950080d0588200c00c84c051551400d11045d520700e0354400f1038011144000304050055400c00800c5801083c0b0401001500204082002030342401c414100ca14107980c0b1460a01201c0001d11002d903a604484e144c4010000f070340c0341e644d800c1800701030203504048 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 179079334 1250 179078084 179078099
    0xe0a081c14010e0f09070b0d020304060c020d1d03070302040f1b02060606091909050405030a0e0a0f090c03060320090609010e01120c030804091e05090606010c0203011515090f 77
    0x4802500c1201072110440002e600c90108000000140c0b001f600d0480d150040c5038110310182d04140d804961160414421000003440000c0001c13141a031079503900321aa44034a507040755600e0500c0300075018041c4400200141c0c480d8040c056452103403050000d0400c00b10008003c8421180700c3c0306007103400490501805540380c0080d90f240000c2140c8a604800b0665007066080d00241e000344c1d0840d04003010841488070100140000b0103082c2c0300c0780b41e0302c0c110104103c0003500c0307030007420440c158400050001017569444005480039600700060701944a49583c04008001d60a4403c0c0000b021140e102c1402c004282e550400c1066810444650401410000d10340701409140c4ae07088640c02e504052203e44540d400c001c68005480a50780c1741c445802c070b405814404000a811161210003105801107445003620401000c400b13000980c6a000c01100e40e0310701c200040c1d0303056481780d00c00c90160b1020303502c1d000140740ca10701d283e03820603114001600803001c66000300003ca04000e410050031 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 179080584 1250 179079334 179079359
    0x10b1210051f0c0f0b040b0c0403050d030216020d060e1209060a03050c1b060103020901080f1015030b01140f0d050304030312060e07020f06090c0d060e0a081c1401 72
    0x62801c644a0041ca0003414003200d401d0b01550307000c0d10405168460000317101d148040103014030b009005202003999500300145032807045110040550340070011001c1d416100b6400b80000130080c91820f0806001030b000111344610100056030300e1541c074220902904400c21980345440520f50300b06044c2007503200018400e018490209051548540001d40c282d40032104480c00341a52541a07040ca9542c201c98035a1103809000480c0210341600012622983c0041c42c42042c9014000401800c80e21035195005420b00c086941103850481c83e000c00014100d040c024003910061180120088401c8100800300a2039030074240614020421100410701c003100f142c00347da070107040c504050078201c5400002042c090380140c1e6108030b00c50500c200da540c041808411011f95504681c3d00381c0307907000d107036480b82024218290300c50000c2c40d02c80700086c01c80d04050407682d90302040d00d2180b0b201d86c0300c07100903920400c0d401040c03420001c00c0c100710303402a1060346800b15846602703000ca5810900721705540c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 179081834 1250 179080584 179080609
    0xf0d0204020d060515030105011202070519021f020102030a0c09030803040b0408070209040605070e030304050f190807080a0606091b050c0a0804090b01080a09050a15020c06010b121005 81
    0x40c0c1d800080c400316025258000d10020007001d800b500302000c1c082c0b08540c0302e070420f0040a00180320039011b008042028001c0d65030450700300014010f811010700c15207840302507030032040b80c1207a00e042d2a148010101c1c1002117210016400142e0f403403600300010b13070449140706036640501031000804c0c40451605810f40782e203d075102040000c1358032503042141183c041d03e43d000b580000d6280400040201c2500124000c124940b1501c00342c02102c01010f46900440c0221508108611303104000740c0b070109182a00101d605810000c041e4483c290700e81040210b811030015a481440c940c000c000852080000401618008200707024204460039101740c0c06030401400c00c42c01050550043e0302c140201949113901c450364683e115641c95207000640a1806802d000c561103000252100b11107004032010300da80000640403035099503440008221030700d44d4003407410307509000040141d0400c1008501911403400300d15111400004e4030892820000c148809c03560054904002d80e403200c0000510 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 179083084 1250 179081834 179081839
    0x7050303040e040336030201020c040501180c0c080d1e110a0f12090b060f06040509060910171024150c050615090906070c0609031b0515060f0d02 64
    0x1a0914203185240e40e02d9105c400f03181c9a0001002800b80c054070b50f41e0014102c034800c1e020350744000c2001d005c12044901c00d1080c00940b00441c41c180d8580d201a910019001280d410318400011940d111344413a50020580d56080c00c1c4e55490f03130004001c1100e02110001c00185061001d103006019407081030044844220512646c94140007a04bc0200003401e0b10302c420400c00c020b44085811301c085034510036110039014107039000028150341442c1e001c4809440014203889800c0c0ca80606201e03903440005d212040c04801010007007481c0705400c0030350f50f108401c135000300b2071290104881001c486d44035464441100100010104035556080840100c440c10ba042d4031964a081605440c01c0d058a2802081401101c0400030744142020182480c21010344284d4504d5568011055a401c0c041d01d0039004101c6803042e140000b049a008401024070038a80f08030030b94207800c0da0310b00c0002c29203011130b0300d50031901c3e4200e103280c50400d84550184045840f0011107030030f0408144031018004000c1d0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 179084334 1250 179083084 179083097
    0x8060d0f020d0809090901061a04080303060d020d02150306040507080405190303021c020c07080111030414070b0a110f01050606040e0c09030d09080c06030c180406090e010e07050303040e0403 84
    0x1020f10000500351000458003400c0f00e9021316180030454002c141324010b8030302d000c42c0321280c2414030340090140c0d010b5070300f100011031842c1c8030b420401ca4a4801c105089a210030025608001070722020710030300040d10310b48140340e140d007805010001500c0d401420b01042180d12020007010940000340c1410600800e0050040400c0c20b042c114043d22070601002405c0310040003a5442079165401051150520001c0d1620661218209030031f0355410350030149440410702c0424040750010400740c61a1035650112001d483e52102841580d800c0001800042600c0c0c14580d01840030510088442c50390750802004140303800c0001500600450103800ea41452080000e4051b51002007242c0085000500321800701c044000000c0080617075004002c3c0744e00500740c005d141420400103036401041c0708903003907041a07480b54078207100c1e001c001c58440e4415140c810009915506101d0740b10500429400822030100c429202403501d6410fa1115001382d20400c02003040c00c4104010039001a03043c030f07115 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 179085584 1250 179084334 179084359
    0x4180b0604050f0f030f0a05120406020303180c03010906050106030518060c09030c18040c0801270303140109020301050a0f0b0a0c231006051c021302070803130308060d0f02 76
    0x144c820f2000c1103400d5018480e92210040c0d2000000341c586601c2d114404583c102010010726124030b001da0310800000d41c1c81070021440540c050184060a0302c0684112290742004900080c00c0d41d0320b1410540346140d5070702c014060154940141c0b544624412110041d0300c207500616507664100600201070746801040031542603a0a000d042940500102102c84404140a50b40c0015401340c4044030341d504510030010303d0442c180a00b001245c0c0c0d00b940c42500c510005080641c17668810000c40405503102440800741c088a80030310b02800c20031800585940c1082e0034002143c039280c200350000d0f2070700007080000820b01000c6840c0001d003840d1801c1881200d28001144080e040e1060100c81083c01c080364042000040d001c2800341d0501092002c5070b52842800159030100d070300d0182c4621031031116805400d06a01c050b50100c0c4541005103032080b1a05d94400d40d42060f135500e080e00d481804080140f6500c142d0700703074021004903050f1040c01620780e00c1c84d01080c02d1100090203080c101006 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 179086834 1250 179085584 179085589
    0xa0605031c050a21060801050f01030b01120609121d0f060301090f0b0a060807020118030806011103090a0609080f190b151003020702010201050c1611060f04080304180b0604050f 78
    0x1025500054082511920907605200d00c054480303400350800b03540c43c1c4000908a0749c08480105d040325000000701010742d003803620030060017086590641d00740e42c6a50113000020403c68108010f81c48654a01400d942100c8985030244420080a40300703814004100a141e55801304a0341101d02480300061400104035044016020001950340d010f0001807000400e140c20260841c45800958005c202d0b044012325202c002e50700102d40034000400010014074154010385203100030305a1441240c0c00c094114000a1416420382c00c40700025480b48020030000d0b004010001002070301c80041c3c60600c0c0000e89070191124440f102400d040301d10408640e520450402c904124000640007199180d01300360301402035030140b001280151b00e480000741554030b2a00c10f40c0c40650712a4161116042185c403582d000c000901b1445038025410003401c00c6e010103c50040001b4460340029545440c600348030b01d42d071804205851005142010042d0b0b00760b540d501c04507410740300d045440210203c07880c0c02 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 179088084 1250 179086834 179086847
    0xa06030602040b0d060503060c030a024b04080316030c0b0a0b030606030606031222060c0318150507061805071403120306040b130204030303050a0605031c050a 70
    0x805000c8900c0014085480c80b00500100b0764800d04050501180e9582c0b800d0590b40c2e0340880e110013410900b030021a2003003800c3c1c0c000300031410100c00350010a45c1c0280c031051140d04142040c10035840c1e0003a4030108008050b002282d6880450b400324240b03490b1070010b0391240720700105182e10000d00b8200c1030426000d0a503070b4550395003013070501c02d80e45088801d1000400034842e030507100344a00c50004d8032514001034100c2c8981000b401401d82e0666000100c11b003500010102d107002254443d104013400c5950b840c0e10010031482ea41c201d0f80d98418200a4044906102c889800d1903179003505004200c1241050721940701d251a00726605d40d03050030a40010103100383d8091510441c3c0d04d242041c414000b070010142e802080a104035225040c0c01c05950361081e84181140c03801c284001a003515182c3e020070a0000c0c040c1040700c0c00340040640c5002c986c0700740c04c11030100355500b0921451040742d2042074050b2000b80c00600100740e40a0301c40d6200c0c1231840c1e0780f00c2000700011b10040410301c80c44 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 179089334 1250 179088084 179088089
    0xb04051801110403050a030818030d1d0c0a06140706050a09021008011203050a0e030318100203040303080415060e0703090605070906020327100903021008040c0b0304050c0a0611060a1a090a06 84
    0xac1d60340702c45407404081c000c1c1c00c1d95200310000c00d411204000b004900841d00b0340384488014100016246400c0741030724045103031b501c01d0580003000e11983c03010452500841d40702d2545030034000f03036000540c8100300c03682030303800441003c018542d001808044108481120700b41d405003043c0742c82c0c14a10504582c88950b0655032900740c080814031000800e40780710041548402200c080e820402c281c1d10490b524040c522000d07000580b1640464041983c0b40d00100d1030f414180c0f004240d241e1a154a82e039501c3d41a543d0400290b0b854a40b801848002d1180303640014607071900c45c01051a00300004d541e80a4081d044031850342d17040d40c0040c8010300038a8482068070150100c8441001d0420140c81d0540c280b00c140c1c06450040707040c02000b40b050740c0e814416075001541f050103d040402511068200038006c55075413041603030104080d592000c1c10f90007420380b0780c1e407003440d041410314880c148880a440001d0480c202060081d4650800c04203414404050301c01a049a80c0c01041c07d02618455 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 179090584 1250 179089334 179089381
    0x1050a0f0c08010915030c290f041811040b0d0e0706080609131221050408041208070c0909140a150e07330f02060a0b040b04051801110403050a0308 65
    0x1404006409903101c8002d0042c04d232840c03090b030420100d094510b19284500101e140103140d080009028200c50121100b92215100200080480040c269041e040c1d01c41e42180300900c0300491480c180b41280e001c1c1d032480c20302c00d1000d440c4503460079101900c200ba014010b0b07032082c1d00350070026a071000809000c2602607080100c0d404500d440003c040c2c000e028001c064074a2100e00741c1d00c000b40004ca03004180c01180e111070714624152801180800c92007410100b10f85440d010401c45020548107603644001c2c000c1c8050000d548542032078414200b0580c01407151150b00011082d10125103490102e443d501e0001c0c2d008a017005800a0781420403100c1d800941e00603078480e603900028030b9050300c1021400c41c00340e01201c03c1102c280041c1d91a4901070070301001a4840c2c000542200d80070b81004880d11400740c0041114240c1c81b0001e030a544003260443c1c103178089031100c003402020034060203500400465005180c5803c5441d50381d100d102c0140080c051098000c041002000000d8a428803203501 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 179091834 1250 179090584 179090603
    0x80d05040f02041b0e0108150d0c08030c1f2a0306050603160e01021c0f11030705100501050d08030103060b01110d0f140f030a050601020106080f01050a0f0c0801091503 74
    0x2c441303a8449407414214850001130082d08258202c1d401030030594003507506d0550464540400004000301c00c5400002100d0700d0000480005004100b00050080000500050583d56195540d42590060004c01c00312056082035880d00d030080a042c50100300701d40307203103030314124840e0018240c010f801260b0010741c1084002042111b0341c880002150821107603503441c0041c500d109401244d54021851040c22540801c8050008079409410711030810400d0f4100307691290380740f041081c1580c0200b03105507000d4100c0da086540c101d2083c4521800340c802164010901056926066060300050100506e00c566400701550349070702401e00b080b03204240c2800c444003600b90344002441010991281000309100e0000e0358008200c84054030702145900b40c90905594404104002810010f018903055550b81c00c00443c1c00c1205100310084441188004a401c1c1400d2044104607490300f031038110150316061208090652201e00c0c40c3c11120508804503180e40070640e03003102e241e090341c4001c201005 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 179093084 1250 179091834 179091851
    0xe1504061203030504020906031519060e09030a020705010801080705010e0f09010b0d051320011101330605032a03041109090703170703050c16051c080d05040f0204 72
    0x916030004d51280d417094036910016101c11082c541d40e2041d1161400444080c1c00010340082900280e10307501c0c100d140d0b0085070040d40e80c804d0700b5000000b40c1d09000190000203604000d103404214000c001c20080ca042d40d981e40c9131015494075418280102c904002c4514035040c0e5640c0c42110b0880d070b58030000c0c690419560354100350b0f00154800e049200c080c50508001451754410111210020f07a0494168041d28411044612001540c1109141880030020081d500721100744035400c52350840100d1114441d604110b000040c0e5035415550211041c4e9000c103118855110381a02c1d00021100548020090b56400b50188040c810310503181012010080200b0b118510094103195038040e15054015100d400c012130300c4074600d002c098106a4049603d8601d0f21600c0010000c5600902c1d2490400203180c1c074641c20021142801052100c0400c000d2081e89842c180316000941a0000c1c5a4821015940c0840b01d00821022041560b62000010280300f04542c40156003070340180300300100714 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 179094334 1250 179093084 179093087
    0x70503100c0210021e07050a120503010812030108070b090310020a090303140c0c010f02100e0c03061e0601030902040209100314130803060d08160b0912040e1504061203 74
    0xc1c0d41c010000052240442c0820f0007266407080f101020286001030b8400000c0110305010342d8002e410450303861042200000105080942d0034554003603582e50103a4951400b50140d20301440d1149909080b0002c10040085010010b076103022142d802141e585c5441d00c1d100020304000002140c040440d000040300a005507111210100341c030721a403900542542c20300f0104031039000d40000c580150303010240220b0030358021043d80300400d080d84100ea0320013a0304d180000603112020b201038002e90101181590a140522080c2d03400342d09440183c0420003018a034140d41a800b80140307040c90b90703a07040c0400f552695012100c80c164090710140094010000c014020110300104440040010012450161450407505240307500050158250340340c080c200710300008050700459028008000d440c1c0664410020000b00038020f03c50044e031441d040d850142040e002c801061045041000b09105494214905a0b007007055005540203040d00c2c0303000302d0010480398209070505248100d000e001c06 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 179095584 1250 179094334 179094341
    0x21c0606180501050105220b1201081c0518010512010305030d0c05090a03031d0a06020601090b19060c0203010603080d0e100216031812030509120c0913030207050310 73
    0x7200e0412074109844101082582210028015203000a81c10041942e404425000d00c04440c04c9541e030566000c0d40d11801c0c030525921000c494015001007000400c100b0b6024804100440d5030100da01e03030003007515003000b0018450604d1180c0d0081344500d80180700c0e445034003a954a00400007000bd00c0b561282481566a004000ca401165042070900c440441c420000c0e1a1031140242956000c0e9040d96820f813140031402c01040d26580041c040e80b0a00d40e5260101401000c0c55005404194107064000081c0c400d10031103103024105054003203c41000384000c0d031044610518001401030b4252000038054a25070740058403c1c100448d40081004032039120381e0551000400711005080c02c0503252007079020315004184510b06508050000ca8082c4085800c10311407030b59a6000b00c1c2e2034079440908040040020340000e2008203a000490610810304c0c0c0c3c134815035000503c0e0b8480300070300083e10b2840080c46409a00540500e210400d8000c001d1500507180040503075407841072580b0000002c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 179096834 1250 179095584 179095589
    0x904050408031f06021f0f15030507060507050607030b1c1b0509090601060c080c060906060406120b060402180301060e060102070e0906070e0a09021813180f021c0606 73
    0x10110030f4200d2202800141102004907a016006404900350f04e0100d03040740790b084806041415294050360540e1a00340c40b0700b02400400294003016079007181440da24040d0b06401c684107018007002040c0204400045280e400b00d00740c03401140c01810715001ca11030328041c1f203807107007400320184806080290714100d1042880c64605032001c401c0d583c0c5c04000660405540750000c5d6004440180301c52407147e202012154000c4000501d8000c6803401ca5140940849900d101074100f80d007030011510b80740c041d5100403d01705002500d411443c0d00c4014074451b016282911940c4d0015008052208100d811405188004d0017003101d0342d50744918100701c0c08100c1d0124010300400b00040b80b581c111498050007101140001c4c01c45580d03156013030b00c11021340030109901070000b80700000d85140a0000303001c030a4511510ba0781003203110013401a0f4a606100400310203041c207116908242d0f603107504071100d0345c0000c55908442c0c5ca90012592030701d0030b80b034800750301310030458007100b401100c0c1c00c035104 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 179098084 1250 179096834 179096851
    0x30601050702190608060301110d150302060307090503070b07081c060f0902030603010e010c02120a03060b030901090c0608060f060f130e09070f0e0105010302181f0305060d03080c0c03090405040803 87
    0x50903031b070b4481014222500401c00d1180302e1400d2008181c2c020550340080c11a500300203070414116103035000200c0030313001100c1076400201011420300240c1000e21590b002804110281410810650384081c402d01420909054080c0c0b0f140d1800d82c102203030b400c420001c00c0c66220150059440d0345201d406540104c45041c0258203003810202c8201051089a4108129502800e00f50b00413001d56641d42e44040555010940c4804020618091000c0158003e45403100001101003007840c207c0c20020069010b102405000c40811140d51a0080003001420701161482e50b204c500c03850f44140341c0103100054180219107440030503103600004c1800c2c066429a01110f622640e2115502c40c03a03802d234043d001c003038401500100043d50094024020800b0320101c40c281d0800803030003084103d01200d840400c2e05003080c6404100c80d400d842840d400c1a800e4a003501841c0c0c00b900c0c05414000301034810007120000140d00b600e56582070043c3c5001480041c028400b90038141041000d81d0026101c2c140b = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 179099334 1250 179098084 179098097
    0x2a14010b030c270c09101d15030a020c0f07060804020111010203011208030403120509030405010909050c030402060705070305032b0203060f31020a170118020306010507021906 77
    0x6003030300e40540c421044040c1103007030720f0311041900201c803004000640651680303078007070042000c10398850514031705201990741d400982030150080380900500001116028054160340b06004180100440b076102504800150390382c4824110903151a20544050466018195011506640c010040e902940c002da880d95102812210707014202c1c0700078415418841921401034001030b00d698059030f8020300900340200983c00f0001014140d90003100c61064079000020700f80708568000c002500034011844003000075207020070f6aa03400b80310141001e4441e001c04281081005800c0200c40091760340a801e50b6207404849103121810301b1b040d4054a080610070900700c000300c5292080c0c0303204030002001400184190000d1040000b458543c43c604841e0071001c00c6007400c1c201200c0070700030080d070b640140d8400c100f40c0300802001380d5400c6a903040450000401112504080d00f5510803944d8000681d2500e0300701c016a514410000001e401c0340c02881ca0b50004010700e01c00004650702503c0d400b = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 179100584 1250 179099334 179099353
    0x602010509070e06040c2a0b0907050d1401020f1b011d0c040f02130b0316020606030a0b09190f020405010501090605040b09030f16170703032a14010b03 67
    0x110303202c0400e4014a03c511100c10005803980c6001c0d00120003000141c204084507043d103a2440243da560000a003440c11240350628080010008030b8950003410200030389051409e0100148001007283d201414000503040703095103503a03081d8111500010210340c455510040e00d55410070a080040c0c03000429441c21818843c8900a05d600d4600c21200700054498400c48404010040100100d140380c0b280c1e003400090142e41c907025500b4050301e090001d00b600d0b441e001840040e03d24005c12428115008102402119240050110152a0700010041c260b69030707400c06500d030401c0c0c0d509403500c10015010050501c14520b207844100303070080d07800388891381e00c900064a01e2003d80c42600002030080000b04181c00c1c08030086c01261400030140c03800142910300742803404c540b20410a04640541c417040003a04815a0340f21300444000c0c0c0942301c12403450f10007821140811150f00a0607180140d040071501a480103a1261548500900c80f400600b59250f8000c003040c0c0b008500038814034840 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 179101834 1250 179100584 179100601
    0x30c0d1a0414191109190b0c0c04060b0903030307050313120e04050a2a050708040b091e032a03060c03090f070f1203051204050102121f0501031a0303040f06020105 72
    0x100e039402d0715130705042da2411001c0d0040c040505002c004103141d9031041000400e403000090020300b0490150700062810b00c04120401048540c03c1e0300c8088004810001d04c05070b901d0200581b5031080c542d09205441c0c0d61603013510340c070508055200038044c00060030f44803511601300c1c14004000c80160740c10042640c6400060f0200e99a00c085001480410144041c40781e0700b01030036805400140c40d15a003020385d00d659611507500260401740464001041c2119641404403815035020121100d100d0310021490100741c840ca1300000388400e08003508141891a0302d824680c8042c03040290481b51946070072003510206030030030b0350b0300415801180041000701c0000030f07002c42611800f90101245170b18209081c3c02803403084c43c045040c04030501039000e5400084820902c140c1c060070000d650b5015078000b407600800010314424200118260781102c03044610445025503100303083c0080e45038809042000c65044440c8040d901d40310001d004130b50312288150040464602d90001c0c002601ea0b03098 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 179103084 1250 179101834 179101841
    0x3021b03121602070806151f05030103080702150c0609010b010e091317031003020901092702010516110a0f0810020906090402040b0717030c0d1a041419 67
    0x12a80294038400d000b00b0440c50b000e002861541c0d00a0044911680c0d9840149040c148201d0325021440000b2107160510305080a40c0c0300b21f40000f0416401046407000003030700e980010b02016100042c0450391404648076180c80100341c030707115125a03494007010740b2000d45c9d0300c80c2150121201d500f40100449154082c40829204d120300904c0c0e00040c4d85c5200110b40304511206003a582d20780d0404883c2d21110501000350300175041c0c00d144d03501c0035085005000c1d0310041a4013140040345001903450740001400c521030f0307208500c10016103010300c1500049446000b9182181c030342d6941c0b05001400c20110800d054400070f4251840c0355055030701d4001c401050002d1007201c5503034011f00c140803204003180c1c0c0200000720b00280391904154281010a040760026000050f001c40d0000b8a001030240030010b440e08066484811403943c500107440107407500542c2c107140007160301c6036000c88103c26426404114100b000d0b01c200300103000402004d1903c2c10940d10021550144520602c0c050007501 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 179104334 1250 179103084 179103097
    0xf03010b01120504110a08030d2306010e010c0b0c09030f01180213060f030804060315290d020f1216170c070c0e01142b0c03050d03021b03 61
    0x710365402081c40e04090b07401404000300304a0302c0faa0f409000b01c03090b030f0350b0090b102d001d442003000039502d4900c1c2d440701008035900d0311895000102991605404805010500d5601c8482031a2181c5074146510041e680a800c00c50001c141c1c540d114200482070070b500001c4c1a417082c044048603000d05000c1c0c0c0142c02c84500b40a036501e0b0240411074013015080c40150f6a80a6030385c04000102665a51103030340c01c0505580044580c1c0500240400242d5803500039080701c008403c00c414402803414292031010155010744a20a04a102d410345900c412903090310300d030609180040d9921801e0700c16240c01c55210f04e081008480c0c806000c01d181402c0b001d020005040350b03444ea40918103001d00e041c512030702c009002c1130006404000b080b00203840110700700024841e448050f0555414680c4031203c88440032442c41c061045140c2c060301072820030910342e0002d0001c4030380109030346a0341020424142c40343c03c0500329100300310710080340c154103030b000f050700d500050900d00c00303030910b0515983c686c850f50 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 179105584 1250 179104334 179104337
    0x1021801080915040804080d05030a06090506090f0709050d080c010c170a270609031103070b1b07020a0b030609061f200d0201060812030412030b010c140c0f03010b01 73
    0x10400f600d40809500f61560400d01a1003c030381040d9070350410b82c4c6040d0a020b203140c0010404018096078056a02a8038068010307000140118038180717001ca604c1c0d0b10014110943d441481e8081a107540c05185040090308018262072030b000d2845c100342c03207594040030721400c26600e003089090b5807501c524800c44c00010004014090354030b400c440d0102500200d1079004190000d07244100081c113607e580e0900c094803840f004511140d440c10701810041182e80d2850280d08100500c0001078140300e0758981c000f885070380d8084c0c2031540c140c1c001928040d00d0002500421034800108442480324083c5129072012104100c440e03483d2010310040103006128200c51004c1c42c0329111669024039031610b1024540305c29104c8543c1507035115031a10084048980c0580d54881c0d007805084018015036100c1045d4003811403441c03c01d99a8082c0000e510b50142041580c0e0322007151282e8131907a104100a900b00b403125001c013149180c0035446818030001d441c81556000b01601c0a818180200c040742d2205 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 179106834 1250 179105584 179105593
    0x17120408030304081e12060901090507050901081b0307210b060708090d060f0c0e030d081f0905010303050909070306030203030f0f0408100506130e1b03011d010218010809 75
    0x1240d80342402d6801c01c1440b4141d810280b00c0381d00040d1a01c20180c92011400a000c070854103001092180400c23040e002840010706041c20030134500e070000126440d0a5007841c080000e65101480743c1c0016039982d2070003e20180c004203024055030b01c1011104103d502000030b0000c032028401e1a012601c0014203e86c100740700748901c00c04107400f50041d080004003c1d0806c1e051405903502c0100720703840341000c2404207580f4a894815541d0181034004104070550044c0080500400f001c0e00050000b081102ca035096511015250b0815001d000010f00b12200301b42320342d50b120305d4080e00c4c80e0015641540a0118200010050361081c000c00085913000340181d0720700b19a14609076802c0d0710010307081d0011541004002080701301045040d031014601000040c2a007400c504201d012084602c902c84c81506124800ea007070345000c9481855a68041c84401340b201060000c03d024160540c00e040001022041c07003006c4c0c40c41900102480c3d014828504103416803a001510301c01e0040c0c450340b030076174803 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 179108084 1250 179106834 179106841
    0x90103030309150e071d01031112030d0207060c030b0105070c1e180e060606030108073b011503020408030d020307021c021b120a022206171204080303 66
    0x3a4480c2c60064095610610031240c1c54003840107442c04036140b08070590005a0811181c00c1c0d010083c5180240621591280d515541382c800d00e80801d8519240301e18a10001c8003964001001240ca080440c080d041d900c45506090140c018a10214540301082c14050a5030107580700740c0c202c0e0f02a5500c00c5811104504000c400e075034000803604616160f4112050105202e020080c2c80c4102c00252180482c030603071024100d07402c0513000380442d401400284014804841c01044a1080c3c404004030f0014000c0b504260403101000700f00061110f484510301c03441559040c445440c140e601c48581403242c1801e2000440c2280b055100d4086150002d01810210110702d400030754112180b0710440d05218081160300d40400c240079080b0000d43d104511810480050b10000300140c64102c84820205000b074083c582c4811103800c000703128040d00c3c43e629060388000704441c440e02010300400c1000b1350b100c845092406c544907400f0b0b12107100700000140c080078501c2c00c84096481080180d0704648 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 179109334 1250 179108084 179108087
    0x90f0103020616290a061202010f0c0201090302042a0212040e04020d21080601020304060c0b040228060201050609040302070e0c0c0607030209010f3209030d02060708090a0209010303 80
    0x19103d800480b004005801ca00d010000610320201070940001c0c0410b009080003500c4d48101c550941c0000340803580080d402e80542e822102c6400303400300c2414043d49100c010310040b80c207010039410095006182c14865101240b050461206048240c0251644400c032010241da07694003981c118000c54208100901c91101007903000c0360010700c00340c8001d42c0ca0b42140c0c0c0d21180300310301c1456a242540708103d0346207400d912083c2c19410660a0018601c0c0504000004102241c030081c00f400400c400400b2600b19140d54684800d4002c100c815041c1002d0101c094981014151280c07500560031f040218126241840c2642c0c01698560020060580f0b0403442100c0381400420b000c04590090105880c9038105020451061001c1c0c0d800603a100c136080c2c005421900c5503200081081002c05a500025203c0c420000b64038641401e4400348600c506c0341d03014613108070a003142d050300400000500444d00050210301600030703611407005580e1078040303c4e070750f4612245029500410a07001000800d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 179110584 1250 179109334 179109367
    0x8060910090c03020705060708100b0705061b19050309120310030b19020301120c090207170f040305030c030301031a0405030f070c050306100302010908010c080a0b04020705070e0105090f01030206 86
    0x502c00380c20b01504110050702e03501c0c20b1800071150030b40825070901c100304503000d211803041c006d8a50f403c10507041905644406503a144c00030441210f08100038554450015a40705170b501500403902e0020401e428008018503541050b43e00e0301c0e0032f01c2201c1c1c2c2c884001d44444d00f900c0c80340403030165443c84e041c40e5444039102c3e8a000b81142c00d403002546440001c00c140f5000441c0604000d56a13003282031102c2c82c0a038064940c40e445010400c6c810700400000407038400d00751800c4070811100036140c0b401c400b003004051003143d01c000c240b8440000c0c3d6213603040011014504036030044241d001000c5040d04100038070380040381c0050041c2c0081003401ca10b10950000760071010b0141e0002c44105807124003207441c0c80300984451409200c160010011076034084401c2010700a000e000740146028041c0243c204400170700008000c0361100064141a202c5034155042250004100c80d041c6549a5800003005028043c50340506080c400242800801c544024120399014000600e054406a640c03c00c1 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 179111834 1250 179110584 179110601
    0x60912060b060f0408161211121006080f010b0609060f160206070303091103011a012001110705150402090c030603010908220f05010f1107090504030309030806091009 73
    0xb42c24016140035a1114000d880540b0401c802000200c86890b40b60010540c1070703000308049085900b0701c200203a142c112180044500395420030403411041d5100d402c0100182c03605001c18030305400040c40000001d407484402c070b140c0000b00040710951013481514480d40504682041040043e0042e0445003001409c08890000c14042501d150354005451948418403e0303000a4070b034600c410510410080c1120455411002000030301103c90040e0b0503410b80201c1d05040c06485140302010100320070b9012904601c91000700607000f041100000c803908940d0741514180b07d8481002c015102c220001800756030010440049a6540741101d0f00c0f503400203018035051b540f18200800064081d0000d000045000c0001c00c001c08400706460340c085605910099201405440070001c50344c000b070780415101c01034a025090b90a240b8002071030803440364010140b49103072108100074103a25178441040c09200e0f541c5c1d40c009403140000c004441d00b054903049050264000c08001c000030701d0b8004441c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 179113084 1250 179111834 179111839
    0x801080a020612090f10051609140f03010e01060603090c230d020f030d23040308030103020f0d0b04030c0204050c03360303011205010c0203070f0312060b0307031401060912060b 78
    0x1519075180b2003a410200502518440547c80702e00b0300400b000030880b84c1b640d400c0c0318a85a1061441e100c0c2d4258264000d105441c0195008151801c03180ca080d0819046030324190002c6c01010713a2810014002c1600880544000329002c0003c81c0d5800841200e0380c3c500c00205050103111204010060450003401049a0205050b54820701a44050101d07804103440c0b0784800c640d91200304240301c443c104441c43d0000800c0e04100500c0054038503030940f4103403901074520706080d00c0380754046508900c1256019041020490410040691107521b10200034820b079002d006a0702c41c4440c81d11140019160410030801c1d00384aa1f45d0061070604002c248411110205003860b00c5036069811a4820381200c030010040702c4844051160901402c690202c203403004600c1c244003900c81248000d40400010f08010b280244190140c0e1203802980c0035104883d181ca070b0300d00b808c120140041c410710361608030801200000040036801041c050003100c5801040c1228061143d03038220042c0002030320240d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 179114334 1250 179113084 179113093
    0x615040509071e02011d0109020d06110909011403010c0e010c0b1b130504060e07080c0d06150305060103140732031602010e031806180301050c040302010801080a02061209 75
    0x1104400f0f80340c2103128a0308150000070740010f40449070800f04441d0401188513a042204c60801070300c4020301401e00308e03049140014240100c40d0b0103401481046a031036030050103d0008034803512001c1501c003098000710003c0120000e00001034402600390101307a80130504100002c03010410715062306a201e1003c18500145d02c502d90b1200500ba0407101c140c1c2084001c10b41c050206041030321034103010340402104070915140c02440100000d10082c01d0000c801800b1898000903403841d00301d4009032500f903c09403440491a2030003002010708485d9640043e05212904a820700c03441070b9640280c100c0e0f84d070040480c08086089031100b000340b02007064a2901007841e0080c2d0174810156020b420410900c0c03608144031107000b0f0070360702c010842c12402d4004004054120400300704a8a8141054880c17546800c00c0400d651020100150695090f508080403c40c100454000074001e81c1e00c00d03241c803407569890303c0140f40d58101c0c9105c002d410038410460034812505d03880440d64020340600464 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 179115584 1250 179114334 179114357
    0x19050d020103151715010323010e01020403060c030b0d0c0603020703020a0209010803041d1612020903010606030509070e22260403030e010509010210020d020d060e0a05061504050907 80
    0x6120901c040e8000c1d09011132400c0c6060506a061050a000c03c0d08520141469419912541e4540d0240d80b0f0f40700404210303407039191901c90290055068203034424001c5490b03541d2814040060003641000304000f0345030280200c0c0f246840c2401544031a0030000d8005081d080001c20341c001e62241c4c074160300754400d02075002c0c016900c11100d14040d0922801460726030745868a0003804031111869411005420810000d407460049103d0ba64402203107014080c0c440c900701c0c0c040081c03044180c3c041c0c0550030480c020a810303405401c91802101400c007100d48141c0d544588107030300d000035120390503000107141c03964a003003600a8107004024069060300d10007a0311142e000f1160301240c0c0361080c40e80c0d0041010014150807108500c0010400c0c00c03c1407a0410040c0000d4480044d1030702c14103516404070740c0c2d9142d011654184c1d442110201c004101c0d003502c3e040074910548044445070031042c1480d0006410b811701000364100c1d003c0b00f04826043c28181000c000000500070844810000302c1c0902 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 179116834 1250 179115584 179115611
    0x904020c03070506160206060603281506031406130213090c090609081c050903030708070b010b09090a050601021218090108060108031206150a0206090c19050d020103 73
    0x40c001041100c0045540391668505181850402049222030901300c20301c042600d50045a103941c08101168116030740e55600c2c040810a21141c880e1043d001d08021200c2c0455103076501c000d407041d0b9542214480030303994031001c409482603d201a0140d2000601003041c5040544480c01e280f84501c001500f800e007280160703849000e00d54403505180b501c5522440324141c20102e1075015110f1803030709a07650703410318100300d90360040180c04180165405070742c0741074070f4442c1d0181d40c03002000400341d070f07a01e031074600f018006034100301008d0392504900000083c607100403008036116200007811042e0155240c0080740010600101400d0650050190407414a115440205569a403c0300d4100005040400344003c00a05030030494451b0312500c018810000000152904182d1034140101c0941e01c22020829010002015603017044000c03908416964000c50540e11600d030300c2c41200c0350305100208101100c0e42070700045c00714591410040c88142420441c1845190040c14042915242e8100 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 179118084 1250 179116834 179116837
    0xd020d090309170111071b0e10030c0905150607050f03040303080405011b05030604090201031104060809100b010f0e1903140106090b030615011b030815011d04050a02090402 76
    0x20460008602c00300c240202010f80b8080001c240da040000c0084c40440b581141d2680f09204004e0100d0b03088107107854061508043e444023405504000d003880d410415450b9000302c2c0140000c480f004a601008990a8140d101d400d128000c0717403011140784070429040c013031140e00048090f0385074001c010314079406210420003000250f10950310303074202e0b20b03150a000d8211614602c140060458443d41c90380c642d0750000640790801000c40300050106d20610050380208901c04000d004010b001c540055083d4111134000e00c25104442981c0a4492100100c0102c944401c80b650201e80c8005800d60418400c000141c0c26620180c006541d040d00302400110291040e402210465800c815000800c0c80070b0203501d0003007800c00400c0c0080c900f0000084d4071071000a0505640c200380070713001c100e641c0c40380ca030781e000e041c1d1240600c3d6840681030070020070001044407101c02c0e00c5041e03100350a981d446103154001c1142c0104842e00030710141d0041002400e40075001054154090040900b140d56520 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 179119334 1250 179118084 179118101
    0xf022d040f06090512060603101a090f07020706091503110c0604050a0512090a12050a0b0a0504020a05060a08040b06010504080d02030405090703061a0c03190f0206180705060d020d 79
    0x11607040c3d8aa241c9010003214202102e1620200c0d000750040c0728a64500150b0801031801002000c581054810815101904001d00c02c43e8000000c20a0001d02c0b841c03110b00b20f002c1d092960035100240e44940050302c01003c1e80c490040c3c000a802120550944030781d00c01000342040e1501103244c201244206031500d030b402d0381c040e15560000c403041e02c1000001c011b04180314085019443c00c01e109000054242d40042c4540e04504400701c01400402c102403142c448107644c030015104032030605a5040000f0700c000c9078102d0280c1c0c1a51b0000c650381c40d00c1030607508412295030710004680e446644d004c0400102510072070500205100c04101800140003410b02002c05600640d19289018100100304002804078ad0a01d803401c070050081e014801c1d0260340c000c2c40c440160350f45480041b80700d4910310541c02c07480c012031007110010b40107a038407640a4114844a0f800c50300c40740c640c0080c1a040c3c08130550110560340c80003404000754100007001d0b0920003031203e401030910408950248c1901c3c141d4 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 179120584 1250 179119334 179119337
    0x409020d0302030d0f0e071208160b041704030206030a1a0306160801050904020d0314070b0c03010305100b030d111c0206010e07050c07061202070210030e010f022d040f06 75
    0x404c05418900f41880764510b00b4490303200a002c101d0078040901d031181c00d6070241040b10080c445841092040c580d048686155001d002c622141ca082e0074213282c601e2017540c04032014030300c401d01d02c81c040324901c0694082d260000d080c1451602d903030003210300510407076010349242002001d9600c1c4036601030000c1882140e500d1011040804010401000c400c0160011417144460030306110140c1c661004180c0780039410b0418048561000805281900032080000d2001c05504100000c0c4441c09000e103040b0781c85082201c410141201c1c5040c01c3da011201202e0300b65201d40c800d100381c284100c041507100c03040003059030410790021402c0c41551082d55020741c096032040004010362041948056400f4a4a10301503007402a5055075907281c10152069004004242e60800e02064207a0304454180368000d1105103281c52180000c0c004d4500d03044a50015480c2403034000c0c0602142c000c07100c000182c00c01c0f24440420283c03a0a1260031144a94a00003c0901001c036020814102d60340151000303 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 179121834 1250 179120584 179120587
    0x20f040c0f12110f2803060f06050a0c020405101206090309120302060c030714070c1802120c0a050c0601080c0306070504150e12010f091109060a140409020d030203 72
    0x200715024118a85040b208100c80b0301d488050078640142105841d0501403004007907a807003c8201da00710000141c885419030102240700300000094065015500301c0d0803001c003a0422035622502500c3c3c500a01003114089055541c0603801860268481c1e544614031040300c4000a07101c40c51001007a1859108850f0725540c1d1028074140b5400540f0315000346041103035400804242e942c0292600d60180c0b2451000c0701c0440403c0c60310f80940001a00d4004400c245070316020750303040c42402070b60103210341d407011041c0945091034800a8021640c404481c014403200584510110211a5000028030400c101083c4020035142c0c40620506000300303100380043c0504519501010b0074000090150000d02c4400c11040120300800c19072021200c216090030100b694120010a4100c0441c05420955500e00211041c41851560125015901802403039481d00900014014818001d59800358829445c003000c02240031581000001c006000e403021511094a0f40460901e110340c400c1240940c00 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 179123084 1250 179121834 179121857
    0xe1e0a0e191401050609010b2203020603091e0607020c010e0f06070c080606010305060d0210021524060c061303120f0b030f0a11060a09030516050a060203030403050a0804020f040c 79
    0x2c1c2405444e80245044400c6031103549003071202c00140c1328a041d1100703d81071280500042d02c048442c02c800864010303003490754903d060003101792a80e10202c5110000cac1d2000501d020042400164175106102580080015030201c900540305480d2301c280841d88180c00c88414401900d0324405400046d2240d0100c91045007020034031400d00500400907070405251108000080ea64082d011340b001c1d030159078540d80c04544150480c205039822861603000b0046000740000c035034071003801604010703050310325071000c61028007080302a1052900e00c006a500960100307440c0300110071030000052285c201000c10b00c509440c1601602d107055042110607030350710100076041c201402030b290f103c1304507400352845801e16590580340007140f840c113070300409020801400da0b6004010b180043d540100031221180000080305a50440274050076002d8451071030005907850000054030300907540b540313445003807050611080b00e160100502c141d034004030012010a607903c0c0da10600107140c1c0c5a0b92140d4030702d203 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 179124334 1250 179123084 179123123
    0x307030c03080708071209030302160302070504140405060c0a051e090f0906090708130209010801240308040b130e07080a0e0a081903060815010e1e0a0e19 68
    0x50080821050205144c00c00082c140d01440f0400fa442d8a400c1c00203464009007011002400380d100200141140150503e01381500040c1890880784115824484130403040f014142006090768024640d501c0a000719089500050140c411100703a40f0b03001c1c0c24640b641011850031307276405905800a142c005982c0e0032a08207450300c50f050b04003e0720000c4150030724001150820000812103001c1003820380200d80806a4825030a400e00c0c0c0040502120b035131140030082c000c04c0480741c1009072103110072a4130300313109006000a080340e41202106041510f40015001d01d6801500d0000203100240004100b1000380c5944c1c90142490b41d903025034901d410400441101c00d50b507030340001940034079400300c0040c4005007200c40004502c80000301181288205070003429540c1c000110600600141c407150310b06100c8814100d5003c3c0c51003d100c2c0d160465200c1140004014407440310000000103004413606403c40c4020a00700b60896800070101201171010720f020768000c0b03030b13300c003003481c04051007 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 179125584 1250 179124334 179124347
    0x6030302060a0203130201030504110a27140403030b0d0204110d0b01090b0d0209040906091a061806060a120204060302090a0e06030304120602040b0703030c260601200307030c03 78
    0x1d0400030451550501440340d4170586910b800003030400d0380fa00c0001d420801c444400c20b150642c0908002e40480e1140300074464251400c04030038102c25100200d04440f902401649000050291b000410b902c443e2011030250007101d0081d9004890a82c5081c0140c03035512804240d6000c000895440da170180a554003030f203044000d0641080f000020a1150070020411606500e61140d001a940c0103039101040140040c0400a4141072400d01440c00b40580d1000010b0b50706001c100c040465a501c3c002c009513a03490b200d010f10000307000301c0000d40b0b83c1000401403140008500344640d403000c1092080051f85d102d60888030010383c000c90040f055007040003000c4050310003084150031928100e80802d42e2070059105540c1c0d24646c1a081d075050041ca44e04803409010340720003d5560720310398207000c0d02901d141450100000c40202c910255610083c03c103c078004804010815517031104401100c0780b0708004070380e04002005020540321004104000c00089201740c60700039103040345040c058400b = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 179126834 1250 179125584 179125591
    0x903120d0c08010e0c0a1116080618120708070b0403202404021314010e01080318010302090a0915030501060b03101a09030d030b120a0206030c0a02010b0a090603030206 74
    0x1404000d200501401c01e10141c51170340f1203101804251668040c24045500220b640382c1241280903000c00613160080c060300d00c0c82561190703412112207460760000d107120b045980da03803801c00b0b4000c401e0aa001c2d03000394000b485014022401c031420204280c0b100d482d60238003030314210085110400f20740c45014501300d803500c0c00b10094016004481a9010344e04e402c400c6c90003d900603031aa2000681190340300301250300b40070080003081064100880e42d28010002c203000346504424860b00000350240f0001c02c4446c0d241080d0108000b003458a0019000b0f5080060103035401141700e48042042c40080c41044044000710640348261450342c01c101c1e0864560390005070910750200100281c070801c51070b0702000c45080490703002c1d038001d140302c0000d03031402180c1d174065160281780403501c9050b5068110b07541251048400c07200c00010520441d80c3c50b00c0d0a80025081403040c0b00080001c4180000340c1000c007164000495004070002c000b49001166401520046607542c40c02d105156040003940da1 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 179128084 1250 179126834 179126837
    0x1c05070507020d110111060901020c06010906051c0201031d060a0c030207050706050703260402040c050a020c011404082a0102060408030109020d0b0301061805090c010816050903120d0c 81
    0x1400c2030980103c1c0c1c641049400140c0b5150031460844416442200341c05d03a6035461005459441c00c08840084c041d51203107203d40e00600c161800072035600200e00c074080031114000c3c58540140e110894490315004c0d40c010688c141940c0c1c042080310802900c1550140c044602c0c003034280da20382400550100c5402240690030148144031010018030002412070a0303030b54a0915036107a41d6107181c110399000200e14800076115200c01b66004038403200b90614081c5100701e1f0140204035503944115494019494050016800020340350103550180b0400248511202180c52a194480a40c1407402c6200b128030710503a44158254056280c0c00a43c1016600b4248040d14007070070207441d910031500041c011040c1e0150b00103110000300c0d14550002c0ca035004090000d004480d5520110341400c08001920b505140c00c03c000070741ca4030320114180e050039030140c4078110542c544111805200c5816001102440401c00c9814540d0780d0400c030251030050549130107541d80320343c2e407000c2040c2d42e500c120160 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 179129334 1250 179128084 179128087
    0x4030227040f0f0501020403201002030a03020a051201060c0312090201090e0606070c080c210a17041e14010c1a06030a0206030405150606030c040902031b1c050705 72
    0x90090408041007904a90010160000740b5614100311503c02c51900c0010101d43c8000760000070800c05c6092140e11028094030915034030848003c2c00014041d41c41c01c900140c00c00c01c150340080b4000c0d0f005c1c100c07050f514a021818640f001c00b840b00e5000e401c0c1c1000000c5040340e807038003003010b9100e098505015514102405100762a50000c4c12886076805194481c1070828001003942d1038500541c0c43d110f81001c0f1103203203182d807041210788881c040710981e80038000c0700c03070503100e51494160519212007107000113114002c01c070340b60f880c0110403140107070740016070401c000203040038415085601081c3d5002ca560b005864654240160340c441582e60341408504060310001c00c0c1070150000c2c02c062031103c034079416078407140040d04100754074100a60222004c010300091110002e280c5011400c10004203046442d40d008202c0d1900048036040d0360210200420311403103a058000d542c0000f003407442c0c040400114000f8004c60340065403d04090710b0040074402c0c9000300d43c09966007014050410b41e = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 179130584 1250 179129334 179129389
    0x80114100b0f030105090615160510150b07020a0b0a02010e1b24091003050411090415020708130308130e01140607050f030316030501050105030709031101030f060b040302 75
    0x1203010520483e4443d610050000f9803640719178205030000100308d0000d980d10459454408058030300e8802c280c03221320070316152480780e288602c108051600000c0e40c41c44003034034001108030141e01c160720403608800030003000a003030001000980300c8800740b9000400d10707600d4001c3d034925103428070541001c0d013a459040746032103840c1c442504025048100c0303403000c0404004c01c20092403145103000d540290040700e403211843d6040c0c0c041800f5038494400042e410310308204100f80faa000b52804ac00a02d440c088a096860b19a40103014581c03144005070306010510072001d003071740141d40c0203480108001901641c0c0849054070070010302103c2801107415410a482960862003461038540101400241101485801c21244540070300c12005c4039580e180001c4120f2450b02802d80320702c0441c0c1810000b140ca503001e0803d4a1040c1055a5160612491078851900c583ea02c550680d042c540d5450400d8000030250081c400500710800f0440e0ba00c0d403a40c4180300c600000c03031208601070711186004 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 179131834 1250 179130584 179130607
    0x60e16090e0f100e07051e04150503070306030506070e030105100f09180510270209063706140408100e1203040b0402040f0203101e080114100b 63
    0x350b030485203121110100c0c0e52a40e00e6804080b15a80040001c000c481042100641d4080c005060140103909001911b080e10b007008840e40c05140032310600c010103003600c0c0c101c0500c6500039550100007031901064081d5280c07501030428400352078040000f642c1281c02150b82c02e003400750b0f0340c10140d00c408030a405407820b00103296022541c0034201e0300e40c0c1c481c440d00822140740380451020300c0c0c000c0241c03916100194003540045c15039031900d04002c9680b43c800a184070841141403840e0340c020b8030000311079581b04104000c2c1d81c02e88128841c40c24842c001c1d503804005849400f185802124850080d050601030040e1400346281240c2c015454200000d010380340021030b45041801d0f43c01d0010429000007106c00c2c1c241100220a00a91140881004184401841c046000e00c2c021b171001c210950412010b4000d0741300c1183c03502c1c15101c8800041003003c0e104848114031402c0104402e0b01191aa2807407030a403104e4008054140c0002c03c14040103004640010f0010010b0045a42c80c080c660041c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 179133084 1250 179131834 179131859
    0x10e06030c0307260106090b010212191202041502012705121317070e15090f040633080705090403050309030415020a03020c0406082d01060e1609 64
    0x610900c50400d00c0340041c482c018204180780013002d00000d1081644a815000042940070b0205005101d0900e01c0780c0034010900c21600500c0140b0700c0300c00c440011140a5403800c044041c0e0328106e41e400c20002545c80d0440543c0f80c850f610343e60000c145035460822804110148681c03070403900b69144000c3e40058070006070044030346005854951104964400b144810000c0e5020440d04100b44400c0060820041420302c01e4414001a43c40141c1310806100c0096402d00700c0c0329006502c503c042500b591030208420b901500c10031000c105601c070180100048480f8002e010b09224030b904400141c02c09090340c15018000d20740040030202d151000184150b440948082c3c02d010001000c40c095610a00c11940075018110b1064030403d541c2c3d80c002d58038036241e10150014004d41e1081c4142c0d01d090300401c82210b00820003070100031032050300ca41140c40c001100b081c2c888519070100c17417a417400307004020050800d519000454580070b60b8500c80003a030003d241c401c000c1c030701d04240f05040c1c00d9103 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 179134334 1250 179133084 179133089
    0x403081209010501061b020324160203130302040e0c10030605120a12050310050d03090305010b03072d050a0e010f06020303040c0323070308090a09020403080702040b0105040b0c0303010e06030c0307 87
    0x35031b14240c603a154000700307003400e1000c00b40340d10408500103030345240d075468499680a03600c3c02404000c0741804010480c0c50340100c91880c001894103c00401c01341c54250010103250b2024070903079000c54040700000d0b0a084000c40c5201c00310703485000810251501442c01c1c46054ac101005e010000380c1079a0b00c0e0000000c101c080c505012011002c40c44544402ca0064098030024100000c50074090401a00030001440100c40039828040c500141d8200400c1070011500313144e515200040c128000710408810509003c40ca2035079942c00000c0503510b2490507401422030050802042d410445407101c98041900000290b5001700148030000b113071200c4040071039801c00d202d0280a0140009103a00c0104800d50480911800902005024500c8020b02203000211800381c0c9213a0740f01c03284801ea01982c40080e0403001c0500c10440541031a03044040070301c0c014907110303180c85e8a6900f059200d41100380c11610a038400b00041c044042848030242d0449002c600404681c80c000e00003c0c0e030340c540390 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 179135584 1250 179134334 179134367
    0x50c0403140a0803070309120e0112050a0e1e061308070209060d05010c020d02010e07080307060c03020c0f0307020a060e0f0d03110a050c0906010302030c0a0e15040308120901050106 80
    0x610219441d18000d02061003400e0744662001c0c0d403802c040400030301400b01410207495204e00340142184140c00b525511180507410b071140203d0458000000b002070100401250b8079035210040d668449400303004020408548483d03040080750a410b6261034818003c3c0f02c0c510682c442501c82c4080780c0c5c1401981c01240d811248003640b5503616001c5180684a080002e02e29070a0a10307800030144c0200d040855241e295000b004014003440390190b482000f4451180140c0081080d0404240260048040c1d00c2c294100581307811210305501e40391000300e28a50b00542c2021071079008524055254000a03caa441c19080c80c5210300000765200c00d201035003e101e4400c040c1c43c001094058000400c8202e5204260b5962500310f00f0125200e484a0f82280e00c03c0c150440000d01c258000d10989010781c146a002c04d051035050750007602c12a00944829900060b4055101c50300c0032080300a0016501c900b421540358510b0703440c1102d000c800a4075010700c59050200500400d0780c0400c00004070400e0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 179136690 1106 179135584 179135603
    0xe06030d022107060e1905010f02030606090d0302250f0515031807050d080405040b040b0306070e0a0302060a0e100e010e06090102011407020d090603050c0403 70
    0x701e59503030346881d40c02d20600d00c10a401c01c0180c88141d104110000b4050511003041d443e0040035405511182146071202c406c1001c02c2c041d4001d142401d00e425401c40c1880b000041150280361f0b0070f1801400700402000615200700080c10300325030b00804501e050400f1411540f0318101900444c1040c103080000001c2d9400d105603032402c0201079980060030344d00c504030f5402170281e1450f1b040d03185118504000c9000d41e40c480340907440e9449a030807242e8891401091100703444040b88014415807a00725a910a5280803e0890b840303010761508a80080609001423071440c50390300080c0d003086010998104c020f8107c00f00c10800282156010f03228181000e084810b1030540f41110b00180d5411603461050600318060302c80d88005000100d205a05400400302c03280e011611500181e200b00c1d9034081c1c040d00320200c074000e013080707260500c042c0c604110300078028400d07448000e094414 = true := by decide +kernel

theorem cover : BRFrame.Cov 178956834 179136690 := by
  have h0 := BRFrame.cov_init 178956834
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178956834 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178956834 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178956834 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178956834 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178956834 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178956834 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178956834 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178956834 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178956834 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178956834 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178956834 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178956834 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178956834 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178956834 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178956834 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178956834 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178956834 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178956834 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178956834 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178956834 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178956834 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178956834 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178956834 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178956834 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178956834 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178956834 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178956834 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178956834 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178956834 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178956834 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178956834 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178956834 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178956834 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178956834 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178956834 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178956834 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178956834 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178956834 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178956834 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178956834 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178956834 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178956834 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178956834 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178956834 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178956834 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178956834 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178956834 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178956834 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178956834 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178956834 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178956834 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178956834 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178956834 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178956834 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178956834 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178956834 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178956834 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178956834 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178956834 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178956834 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178956834 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178956834 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178956834 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178956834 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178956834 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178956834 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178956834 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178956834 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178956834 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178956834 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178956834 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178956834 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178956834 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178956834 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178956834 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178956834 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178956834 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178956834 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178956834 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178956834 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178956834 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178956834 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178956834 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178956834 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178956834 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178956834 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178956834 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178956834 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178956834 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178956834 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178956834 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178956834 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178956834 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178956834 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178956834 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178956834 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178956834 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178956834 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178956834 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178956834 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178956834 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178956834 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178956834 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178956834 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178956834 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178956834 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178956834 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178956834 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178956834 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178956834 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178956834 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178956834 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178956834 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178956834 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178956834 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178956834 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178956834 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178956834 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178956834 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178956834 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178956834 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178956834 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178956834 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178956834 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178956834 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178956834 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178956834 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178956834 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178956834 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178956834 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178956834 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178956834 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178956834 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178956834 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178956834 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178956834 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178956834 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178956834 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178956834 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178956834 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178956834 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178956834 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178956834 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178956834 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 178956834 ≤ n) (h2 : n < 179136690) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
