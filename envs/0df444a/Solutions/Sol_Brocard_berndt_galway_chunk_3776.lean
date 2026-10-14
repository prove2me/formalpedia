-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3776
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:38:18.944988+00:00
-- url     : https://prove2.me/submissions/ece92632-4a0e-484d-a83d-008536391af9

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 678956834 ≤ n < 679136690 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 678958084 1250 678956834 678956857
    0xe012c030616091e12060902100306240f05031008010c08061c0b0a0218030706030209030d0807020c1e0a0f080d0201060e0a0c0504090c080123031e0106080f0303010f0506 75
    0x120078506100071404203174060040b00c0b81601c1e1380c0d02c2c00c0140c4410030840b04045c0c0613100487e24904003810700da0340703040140040341c01c50720b815030351368100340c11460740d69001c0083e2030080e580303030342c1c690480e49404419400501990700c3c280c1042d09c05039100340094054401241c02001044c5519204078182190403c041c00c06803480001c44e1102000380c0c0104403007648841c0d120315104021002a081071007030303881440070a0300000c983d142d51401b8007007860291910301b00a44a802d02100080d13807507c0207030746240038a07000b00b122400003900846011401c0c42c001c02442c01240c50301c02100150b03030b44e407148041510666003070504050042c05030405131620000c1074200b03030f0345903245000039125a0303840105015003048045031a03000c5014103240d038403060b1030f40c2d4815450314082100301e459561030b41101c100d004501c0f217450341c0c0200c4c0f0a10900c482010340300031401840c00840c014a29588201480d00c0794410031340f03003000007001540c100c03074402d54800741c0c840d580c0c0c0c00e018040c412002d0307201c1c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 678959334 1250 678958084 678958139
    0x11701020c0d050d14010810060e0405030313020d0f0f0308011a03130804050a171006081b0109120f060f020a0203040e09011104180b010e012c03061609 67
    0x40c926200d040031300b4500901203c04140c20100000305540c40e402078010b14900c0d005042d0001d81c02e403050260400800c00369881c01e500f0b1400f500c8440c1c80e8040501040c021482c0e88413140255a01d103030801880d1600050481c03004d1f003681c80d00c00c00140741000c04602044040000240d00003e08540340788003480442000c2c99555501c0c2441507154031620201c4035000c05210120306a140c00b400d60010300320f95005421b180c13102c1e03925145010381035416000318a0402c00d0500c00c0e039002080703490341c440baa00659044000c0c29801a92448142c0d0004800f8601200c1c84c101032040e05200600715038040c52040184840f8005000140e00c1501405409030303208100c02c200e810a12054070b64005401000014041a68001441264803d034010345c00c182c68030204480103140d41c42000b056207002d00701003104030301c02c00010300b4034216902c01c40111701d403210344d80b0044165880b00380c10901d0001c05851092601e20881004120211000800070710030314000700d008404900c070840c0030806000703041d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 678960584 1250 678959334 678959353
    0xb13150605030a14010b0408010f0b0a0e04060b040e01020a030e010c1b03030e07030f1406060a0b210702031e040b030a0c0c1b1a2a15040b011701020c 66
    0x181d8550380050508041660b80d0760311040f08000910703240c0c1c040e002c0354010564542c60082c8075400e48603284541d000315450400c40020076550440b003035040ba2050110102e213961103040040051042c3c0d034085030405e080900ba04c800d0030040d4010a59812107407000c001661400400a080f2104002d0040c081640300380c014201980055005030301c248246400b080031b14000111a0070a5619803048580d800300085d400708000004906407e0320409400502e590710b856400108078420601c9010500751002410000000c2c0002481d40721800c926840040c5081162009549a0102c18082c01403a0300c2c41001c0450130240086801715030104a15a0860302c40741c0c0001c00419207510341c0c00600030a1002140000d1440314030310301c10031010401c03440d007500d0018503c0050f881415403034010441081000801138215607450112a90385a01800c10ba030103050b100d26044900a00ca00e10319102e1003000308200c142c040d40341c140c44400d0365002d10428800750542c00d0380640d80580010b1b07040044007 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 678961834 1250 678960584 678960587
    0x712050906041d0132040b19031a060d1709010c0f030f020c030f03070f1b0305010c14070302190203070504020a050306090114010c170403080d0b131506 67
    0x19040d04030009158600d0156514440101d4449850948030014020401003241e1920521100320662040c44001c0f0181080c50442d0082d194011a5510565681290200603160f407010801041e000c45543c0302d561392282083c041a800803c41d1a054000e4100080e0090030421f41c100603141d4403808103104050b804802013501d4010007039140c10090a0103007000070030380142040700f0301c030b0194450400490012100a0900c02900c120500075400403042488400c40082180e0605801400752445407085141c0b21450000b040583e440540b9003400c048207118041d44a2030356011140c803a080028500024444031303008050001d000741c1c02c0043ea04500000c1100f200f14014402010b0340d0501d1f8407140001c0481c1c00400d03030100090008010440d650520305030141c050710901c900d207402403540000083c1580c00f0f205000309420301075044c140d13a84581130240e4028503444200300d40c4034040225a00018821948501e105450300902c0d54142040791040c2c0300c0c82e40348400818541c60a0810 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 678963084 1250 678961834 678961837
    0x20307060b030a0c0b1801090803040b0c031b030c010605030601030f02040e0a021207050f030c03030304081c09030c05160b0f160b070903050706020d0206010501030e0a1223071205 79
    0x1c0c0560540104000a0005440100600701403c03c0b500702646a1013040000802855844081c41c18001540400c0c01082c00000544081b1120040341c259203564104100307055008180901074811b44c50b592682900c100400901525614840204842a502d5040507038500c0288406060001080ca80707030301504090704003500071150002200e54510490b8089100c100703550550403410b40164005210034a03140f121881190030031001000107601080000ea20f80c40090030080002c440000d0041d004c954102110025407900309003003240311440c3c10060080d42042d50222038a00515074148049003120800c80142d495030031046040c41000808510a5401040f030700f164020780401100c0000e8a02002501ca0300aa60b240e200380c41c95454210300d82030103038100d84255084003003100447e50b40081c010f81100c0c0c0910b0b0201e001d106c4d4483c0c05007460000c00c000340103050b080001c6520f068001614001140d12541d0071404290001e9000d00140070361a4010301d01c40f500030b04e0b150010312850 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 678964334 1250 678963084 678963101
    0x30809011a1003390c020609040207030c05030c03490902090108030a09060203030f070f14030a0b09010605040506040306020d020405120a020f0d050c090a020c01020f03100504090302030706 83
    0x9001402000b21055100304010316002200d843d10000769002e500c007045080014044005e00300b03241c0020716a40028101d014001301c480c0100c1e408a07580c81818811042e40f00d00c160400f00345d9940f4540c0021b00c0f9140e0303100410140072140c2c460200702d10b010010f80c004031100200710481140354100d040088400340c480c0e4032101c0e80d40c3c9401004000d07a58510090303008190481c0203540e540b88090001c1c102c0783c1c150b41b0060641d0030520810203e48614109503900084910f030800000418141c2a01c0c111000182546d4a00d00801080502c4e0316a40c030225551808031640071581e07a0343c1c502101c66200f58001e00ba04090300b4842080040d1194002d80a0100c200310f0260605882d00701061149001524200300c03a0321403161407065042059191000120589400071440801e8072040d03519081e100d02c442c040c441103000101c081c4801c0c0e05640c01d0b0981200250343e18900001000c5036500151000034419040707690000e180c1c130305031141104003541034000d1803e02800b61550300007028440d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 678965584 1250 678964334 678964337
    0x90b07121404050a060f1518050709061205060301060b030708061504060903111c03080f0f010b070f030e040e01060f082b0e150d230112020a0f12030809011a10 70
    0x41f180d440c1180e0b00820000050440d034851543c08540246d09801641c4002e000c0405011800f041805240d030300890070940c407180401c01050380c0d140d5001113801482c2603407000702c42240100a010b0901c0d0b110052601520307040384c05041000f150000d50080344958401c520101e000c8050030000074900319218103100c02c0091072003405e8010035440004082c2500070860007c1e41e00303404c003c0f802c59100c4080e9007041414581e081f083d8108528030b0000d00c00c00b5400761070704405048a604052251302d0074020101c0191040c0100c01d400d203160f5001e0f25190086810b24003107010041101c2070001994213100c648101c200e4000440992913030358012004055a08104111918a00c070ba2a01180340c0700d4000c060ba991030b541c408880300602101c00540210a002c4215800340c2c01c1080c0c070400e00b9056803078003840400054034601c0000d100780c99a50006407008124040014800e01e61140d81100c0c5000c1d8550954990780d183c9481c0c2240c00d501440082c2440c0d94040d2030707903410409001201c54509 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 678966834 1250 678965584 678965591
    0xe0d020c13060b0f0304140109020321130807090b030c090a1805010c05040e090a031d0402041a07061410060c0201030f1509060501030c08010308030604090b07121404050a060f 77
    0x2180005803035a80000701c404c2e00200300005010820108400c0c02c0a01c8410000030000d482041c0d0000751150f40c020380070b5415450050301000c0c06071600d400c0360044981d44a00084c081d0343e0307074011500c400080c461003e415250002240043c1004960f411080d1340080c185445a41d400220b4801060310800d100701c9612940194000180240314403041052607803681c40d21145000c24110017460014020740702d035040100300400103038004113031094080d502030780b48608141c1103021400900855019144614401002d1000d5048400081c4801c034007500f018481c0d4550801001e2208105030355403003800e0208407042200a02c50749403040714601c14903000c241038580007102000e41c1d10148940d0382c6071088240c10000c0303102a11489005080a00342403210100c40200685906414440946200d10000000b03040350f54581c003034000745610040201c1d0f28182881d0081042896910008a144ca0403d10107210304104207854810b5900c100240045107042d660711000d0f00b01d0000ca50100741d103 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 678968084 1250 678966834 678966839
    0x40e0a0e010b1c050d0c082a0a0c030c0e0103120804031b1a24060705030c03040b031b1204230111070201020610210c1e08010e0d020c1306 61
    0x1c8050401c90706507505003c00b502070a00b410454100206a00040103115501e0003820000713042c402560110041c01a015070103408031240044130181c0f050924850380070341107100e000c03c2500010913055901880c0002071003070303c4004c90b03600c1400a0001502c0e0317851000050782c15511516002d90700c21f101c0d103880c1c1c00070212407050550b5164a540c0450b42d102140c40115000f000340010140d110211003c000c820007840920320318581c12035103002e802094000380c00c1041c8035040003104d0b9004141030880e40d80d01d40c0c90985070026002569a006c6840e408800c1c0c0416000c5030040c1c6031450500360030008241c5440da1105080340e03060498404212500c101007581e010207206518501603483c002c0d80d03444d4451f10009003480130042501e001e20b040001c080c0300a600000d9410a2400d00e00743c8103600002600f0628003a80f9030360b12401041080c4000300040a04148603c022103080300024403106444408040d207506240307218000582c400f02c41042249803c2c8500701032180a182c00048854 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 678969334 1250 678968084 678968089
    0x3020901030605040303180c230604060e120c151804050406050109320712020309160b160308060f06040305010504020118080d05070309231302040e0a0e010b 69
    0x2402640300741d440c10343ea007040001303140d098090714000044a40c1520f612603160f40d22899491100e001d91807400e20104150a100b40c41c1c18000c4001c078200820b0030f62101d6403400d0061600c5103101c02580982130200c5046440c89002450800c1c0d004010042c1d4068100701400078641e400003496155409800806c4526541704c610405000d80d015500c086201d604103910a401e9034000080d2594080711401d888000d4000458040c0101da081d640598035501c907401e0885003418a403140ba13603514400024032002010000700b000300300440d5020071100d2943d80d0543c1308135010b40000c1c544800c0d182640c10000901c11a500c41c1d20200003041604c01401ea41c01049054005810403210303603545009100c155030308001a17808645c1d0340c070650b0700000d0070120000e40f01d100ea11200030600030013045010405002d9890f403409810701101031004503554002c80b080f0b524008241a0050b10703141004072899030a03008035026203502102c5800c4645603541c4000042949408580040d50782d0410418140e = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 678970584 1250 678969334 678969349
    0x3070501020a0c090f18201806040e1c020601032303030a0c1b0602131a0412020d1a070815031e010216080c010b1c0b130c08030a0e060405010207120c0302 68
    0x1680031f000b400d00c0010145828001004010760b0345441031155200c8112403a0303681c56400c1c0e224005882c08075192000c02982c07498991070246040c44a500c0f01c4200310a1703035000400d03078101c0b030284030740201130002c0122201000c9150606494290410070001e002152a5003000c580c941d5949815000413034009105011000c01540403600701b900051181c4418122000481c003918204851104400040c43e00c0c225a1080d8440e8007c9150f0050f804415550741c0e03048640c04035000080c24540e60780d58000d8100c00c0360111003c20209882d0800b1642c815010b0240c40072452025000341488940703c0980024111200d0540d0403a43d001c100508a15132644050a1305074824081d0546403258a9042400c0d0707070000d2001c6000344500c1203800c03a0f400c1c0c2905039048081d00903248000f90380b1010f400c8a946401014080c0185d00345410006144000100800c0d94500702d64075140402512001c0100f0340c801c0f8826280140c1c40360b403040c0711845560b40c0005413140300d03004500c4290f60720340c08200391 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 678971834 1250 678970584 678970631
    0x510030209070306260d08150612060907020f1f090804080d091406030f09010207020915030d080402090402042309010c0908060403090b0c0c090c03040203070501020a0c090f 76
    0xa072a03031400c1102c0b00901440c4400ca81c02e90070183d0001c0d080007403076550341b00c140100104000b0b490003c941c0501c1c0301034001c401460b02824a41d501c2c40300030721801608606407845030007841050300180c1b081d440440d04008403040c500c0038110110260114107801300602c184161156640c04680c0c0001d5408401000204121005040c02e4401018050b005210315440182440040214110280d650303c08590348000303d40c1c810501c0391500003c0c0c070b0082c0185480290040140c00a1000000c485803240640d01c000714104c403100030440c02c0c212030561703054a000390000b8051010070300601d015004040b02c40624400c2240030028205ca0040c4602c0c15165801540d6595680c5569a07900c60100400b90141400612040c20113590003004941d061041c0c003401c3e00e012036541c24140050110100c0658001c0c01e8961703900300709005500d554400c0d20224845c2c03169403400a583c1d40041402d4440344d4200034071041140c60321100030701804a07100070800042d83c2d51001060448010a1300301c2 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 678973084 1250 678971834 678971837
    0x130021b100e0c101209060b03031c06150914040e06040f03030501090e031c0b0301020f0d0515011e180603020c010f020301050a09091509050a0b01050105130306051003020907 77
    0x1010319002e480319080c84241c0c011140101c0015910981e01034000b8601204200b0b4a080000c0c80001c03802c0c4040240500c000d46a4940000148480101c040d12509103211014030004c016142da1100d41003440c50a40318980b0125240c1c080411080801c038610341460700000c2d101041c0b500da100c095600b090710880b001c45120805020318414550b140c0700d030303d0140c1030b00801005124804031407a682c0e4012418000c40803994103982840101d2117400800c08400f01500130740d2101001c0952600780e80040c0307069000e0f54a0b140000700e509464000c1504c0601c2c041c3c58140604450509020001101403000030501c003542d43c0605414000d4506d102c02400607660042c0c43d009181044d0b0b0030740d003c1c840520891401400148210740d1640f0b000b00840e01500da001801c6c1009241603c10042d6000d0b01c60406490b00d803035401440408510340a280d8851035103140c180ea00ca0005682c1d0380201c406030801990b0b2050140005070b1980d00482d04184c1e02100d0b512816540c1d070010f0802d0804176400c40 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 678974334 1250 678973084 678973091
    0x22a1318030534052415150412021306060f050705010e06041103011404030e0d152a0206010b0f1b010c0f0f0806031005131b050130021b10 61
    0x4188802407007880005c40382041c442c02105458480082074040180c050340310940002c01072269642c44490b80c10801002111041d100c659030950800b060811708000c0e4000c01d946443c18900c0c0c11284148026590300303071278803000a01d60100445058010700f504070307825946c4511000414030100a9503200350311904820294004e59820b05080d070b10004504043e44010300203004c002a08064501e08034002902c8400240303a183c18802001c030b1008020310450b40c9000641c4158441d8440b11184c0401d644400b03005840f25400d040f03030b44480134851402d040005000580b2104407900c001c2c8849400d4105411540d44900d0802c2e003110020009040451046099488015041840100304c1c00305410101d1552070094042030307c4080c0b03448007070041580c507000501c103007803000081030700749401280060000f00c0303108081c1078440b500d006403030104619046c009014415450f0540da032014600780b0526461703000e401c0c10040c0d0400302000c3ca81082c0f003501c0e003007240410004d0f001034030500d00020 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 678975584 1250 678974334 678974437
    0x15061b0c0f032113050d05060103050111041a090d02040f0605030c0114070813031502040f0e0106050711010212071b0e04020a0e07022a13180305 64
    0x11903449055404640a500401e2881040b070343c500e0780e05a5011803520036a955861010000c00300d210050700096401b0215146001c10f210000070024180d03171160008200f5000f50080e100300300d016030300c21000c49480002c24510303182e4409000c2d1044040c05401d14040901e59800981924540d8281c84815551360604100905d403c1000542c00038081c244640c01c50507650150103684180c0381d000c0e2000038002180e000c000b01300a600c03002590031814590000303019102c801c0180d8032601c54102000407140300403441c049052400ca048a0a41d100c0518140d110ba0390b02d4400f1003c0c6020f6810340c000c03401c1690401c04c500e0002c2c06801d1180710303101c0b004000411100180030440d0442c0388030708414403c00006840e040016415102c82245a0f490b550382c1c040c1c1245404c0904201903c05020342c00c0b545030000c0703545903418159208582d0801c0581c3c2002c101400c82d00c0280000340354813002124680824018402000a80c140c1a110003100503559120780e1441242c1c14000c1070019025400c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 678976834 1250 678975584 678975589
    0x90507051305060c150c16030c0302071a04030b09150a0c0206090d0504180b0d0f0b07021f020c070f0605030105090c120106141c060602070801021215061b0c 69
    0x1540d020b0902200d21504050f00035440990790101140c0c6525444c1d2010003007490b00010740c096483c030341c441200d01150480319280c014200d02100b00110007500c52954007064040388030354400c100030f500c601420b08103851900e80440801000e4000c20340c500501030466400e40300b41920600c2000d90340c030041405c03030090600a20f4442c000740102a250845040c54480c00d9008003100c003152200004211421000101d400c000c1c10710101e4107610800c0d440790542002041c01c3c0060a4500801c00c08815035120003040e6240d440b020400112000e0342d01c0340c0401c1c1155a400b030f010f0042e40004031180280c8584800c4040c4070503401c0400415000310040296142403498940e00c122210b17407542c149501c81c0c1e00f04901600c1802a40c080c0034101c3e107a034080240c2e50b020f490708404413560702001a110512600020449409200014020507101140004d014007ca81c000d2010143c080d0315603580001f990f02c07140e04a507505034080740811041006200b11f078100036042c201c0350b000d000c1e20300da140c04 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 678978084 1250 678976834 678976867
    0x40b0406030302070618080705010e0a080d031b0c03080c03100b030f01030c1512180206071208070c0203210f03010b3403230d050a0f02070c060e01030609050705 71
    0xb0a0401000710742024402c1705070104234041111000c0c20451717505660003001030001e189903000f9610300d00c0340000ba008541c2c0e140e000b02c0240c0c1d000f0449019101003400d412902c22201c0000540410188e401040c60141c0240007036a1011030725880f002d21544601d042c200e554402c0c6c41420001c2c11082c010700c02e100103e030b52400100054580101c8004182d10003801803c0302000e50f035061962000c0c40318080d44250483c80c07032039030b0044c8415a60301480c50501030040c0034204240000c1c82010001c2c00d40d0b4010004480d2880d0001c00400b4213610b1101a650b110b000e4412031a0000428071404100e0303413403080914080d095145d81180c0ba8442134001c1c80d91f0110300c000c0c0828010241c0c031b4030441e000c0e0380044500c0b200e4061400685000010b181c070701d611040349003880000d980024081d503403980b20313074030a03802280301c40340c140403040c0c031030303022a06a011710b4102801090116030104055030013550b504031900810704001c60724aa8075600002103960446490001c01c40020f500c0400802801 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 678979334 1250 678978084 678978107
    0x70203011410030f060b101706030706050f030402030a0b0f0f07050f040608060d080c10060906050f09090f031204141c12020708030726090d0806040b04060303020706 73
    0xa00640c0346040092542d92071642d10015141013000a215070038401150040b00709880080d06840241a08141c01003248509902034020700a481020038110303d408164241264185d546850130301a001036055440e030f0020300120391502c0b0b541d03100703030008d03a014103d1403140300704c0c44690b8005e2401442d0242212801030400007040b40402c040c40c2d00142e00426501a07405524100c4101d0741c0300c4001c500c0e40d00810700040c0c06401e000c07803418403560000507400c0c1c03c5402000240489076444090300c054501c903004850380700b400070f00d482400d41042804c10790310a04a00888031050404200d250941d400102500e03940b40101c0c0c100800c3c441c422800c2002d0346580001410004800c01074806102107500300783c802c02c82c0c4c524481400742c3c07240d010380e1096508000d45a950b0306002c000500603070324605141c03140d00040541d41d6085c0404040e40fa1160100801038000019010411a4148001003507507500c1903580d5200048d5440d01e00c6030070041c3d03100350010a000341c00c25a02421002c1e564 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 678980584 1250 678979334 678979361
    0x90109020417070e04030305130f05100c0e03030f1c09050c0f100903030f0c050f0f1c0c0204090f120f1101021303021011060a0902040605010e1c1407060507020301 72
    0xc0c802086500e042418540d4017070307090700e030019403510307101c0d130148403c003600d0406000303420000c030502c00384640071421010407410707000e007041030340d920160541d0700d51040c211950303041e00f041c008180c174010074400814043c170740410b1490030240c0d0040e14904a81c0f04c000c051b1103680c402400c0c00020b042c0404a20480b18007269980c214600c0d01000500e01081800000c0c200708a40400400340c0740201b113680b85151703000e010340b04d043c540945860b60724900754214034600c0c0305400c0503c44000c4101e020080d00a15940c514102d12420740910002c2d24030300404480c2c001e6001e10751030108004a2069084a602d0307650321f00850410240204541c468140e4640164410864400c1c0d5094140c4440103c95040c1d805000903044044251542d00081c2c0d0b040826020304c030f080001c0401076034004000d80b44200c0d81005010b844d04011581c07860503111039030700700c01c171050034050314811500e49031b21062181c8807030001000e46110150a0250b41d5000101040001c20b4034411440c0a0140300c1c1d00c0030b1039 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 678981834 1250 678980584 678980593
    0x130f0b04050607060e190827030a0b060d020d060c1706240706141f0308030a0203100306020c0c0a090903020303160302210403110d0504140a05090109020417 69
    0x500c80082c0c1c6500c58060001d1140d40d44d2070580c540316009003c0c002902840a1b800100752519051508680e800080c01c08849200e82180081d048940c12003814008400380c0200458a2166500c1030764200203043c0a9102104124440c0141e80d00d5407a900c566114460204244000c45c00c013501e2242c00e076a580c4405e80120081100c640c071000c0100c0e0303c100c074264030748826a000780703413880041c4aa5071000e80a14140281ca03140340000160041c043c0d624591085503904030074910f00c0b001c0c0342c203010040c620101080403581c10103041d0040c5030400c2e42000c044584a6a0756141c000326030200040350701c56001b03003022008510302181008003c0580c1e54082c8036420035694007d480748001800505407200f800c810074552482a4180c98007055000141c2003403002c00841050005d80c102c4048000403029600104071010120b525080744505444150800d400d281c0b110200d000380c58000c03074002100c6600059660b0b2402492030083c8044040140ea0344d06080344014044072051003840c050f8070 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 678983084 1250 678981834 678981839
    0xe0703110103230405061b13060f0e0a030501050a0b0102120405190305070f0e07020c010c0b1914010f0515090405061503160f02070b040509070e06130f0b04 69
    0x4444091440c400c0902e40010001c0c00381000d041e04040310500e101c0407010407410403042241c0010fa02c0d004a14104600c40c605050f01c2c02004a842040c0b400c80348546070440800410b40204c108445c410250708100e0810159800810401d44140c0d0007900c9aa45440071b00c0300d426682d200d0035001581c02c0c8003500f000c10541107600241d01c20f522805001d403000c065480c1c1c401011080d90005141c2c400d046e120b00c0c0da540d51080400c02e0f0710b4007034510380402c550042040c850001441d040e40d02c0043e1030300309108140b521003010140b4000d1000741c4100240f16151811001032040c01d0141400d21030454082d41464103c40c142000c541101e4080d406010702040340c4aa0942600c56440f000c4902145a036207444c041a201401c2d0000590104008400c2c071040c605240001c1c88581d02607503990010310a995422a40c074085803103a034480003030400090003281468000a0390148241c00d25034281056040800d1043e40113064050300c100c50010140121410902580c0c02041400000c4d4242030 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 678984334 1250 678983084 678983093
    0x1e07090303140c0307020319031407020f04090222090b010b0c1f060f06121505100c02041821050a08010909050c130204080609031614150a0e010e0703 66
    0x400c1c0510348107501004512894003d000700101c5040d545e01030300b55440180e02d103104a0030100d5500c000ca0124070340174045130312107480b4420741c2c41b095002050304103c60810001e10008007200b450a80c1c0040d0710b024120b0848104100640c0c040c50000c00005641449007882c2c1e11405046e088059442e004005200325408006224201d03189054402c65406004801410040c1801d81c0462032304590700301d00181341e075008990900b80d090040c0c4140081c0f030540742c24003400c4030540201c0d94807004141102106900c0350540030f19891024000003078550018024662070b210300007040704c0c0038550302031400107040a03110744001c021607810301c0d0703050850000d80038280c02014000c55060907074401954060010411140c00c0c01c280c090099146807014090741d8020390311078000c0d02940d110341c2001c44c1c3c00ca07600000700c46814030706003180c0d070407a50781d55690340e0010181c404d18035591103804540c051480d036904005000d5130942c440026860700c180c0e4100c0c00e450315626041480d4025402c1000440e = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 678985584 1250 678984334 678984347
    0x20102070e48030105040b0d030f1b0605180d03181416090f0e06060609060f0c01020c0109060c02010504111908191412070206070c0803031e07090303 66
    0x14400b00484002c980d41d4000b05090401c200c8000040c042d0507a03406060662010002d40c140c80e03003503c0c1446110b51101c00d0001c6400c02520040000d8818040121594070500100324080000311000602500319240d54007900d10546402d0710310401c002201e05400c000300034040d03000301d50f41020b020580840071000c1000711100009490000c03450f80176100c1c09418008610115141c0f007850440c02d407102c00010013082190350206032545000303030090300072a000036101d1090320002c2c02c6501c0c002100051003500c4e00018080f5100d003000b80600b503a100d20038005010b84442e088000500c0990608001c015110684410b50079a4035010510000c540380450f042607180d002e55048009181c40182202890f01680c81900d0f140240c4148459000441040000150089221042d510321041a42e81c03240c0340c0c00c0e00648005030801030800103042440240c4411806190f40403c1c60f6581c08409085500c01c94240524030610800300b280300142050703290700481680b80c031641003411742d500074001 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 678986834 1250 678985584 678985621
    0x40306150815011208030a140403080402030d0203130504020a0509060a020a03140f030708180d050c01060b0a0f0c05030706090f1502030601020a082d0a080a09031709010f0513020102070e 82
    0x450000000103452401f0540102480601c0b04d4559180d6250030304005006081c00da40891007801001171601c5403602c000180c40501d0340b4800c4d080700302c40c17030003040200940c001100002071090910412065580741d9020342040030f95a00034041c1c3d000c040c60700034004141181110350b08a818060152818480700c2600d902c0f41d024180303005192607210303124410310070360107201c40340d4403540050716101540031000d0480b40605000074441e243d240c200d0744556004250080c0001204000340402c02481004a040031600850a5900e003551036140d84095a4000009070303011412041e4231010012008130040510460100071425030070302e200000d4440340320b5200600070b090701080a04404c01c4903008102a4441c400066050482d01680d80c0d403140c1143c500f030f10200300c584000800c140814040c81c54003590503503e883c1c0048402c5035008035500c1c058504003c1c4d650b60010420011a81c0c4145c038007a42c0212802d00d000d01481c4002072802d08141c1003443d5440440b402d100030129000c8001b5030 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 678988084 1250 678986834 678986843
    0x8010501021c1b0209151e01142107050c100603030e040f0e062e050a09091a09010209040f061a031e0a0501030c0e04050d03110403061508150112 64
    0x70400c1d070800320103c4612003000e010354011400c9045c011700354420f546a50b02e002090b52244051580f48400503e03418070402054007141c1c1c0509008050303100c0da0000c200e00c94181c1002003404840741c41800d41e030203040b91514081800094400c0780000304110a030401100da400a000450640d0b0300101024800c4400c10b00640d01c402d0100403411036500040c3c111043e080841c1e10b2840c041c0000d080c7d0011025104004048400445034030041c10b441c0c583c180e40700035083c07203c99032801c44070310020a86050142c0c0c1c1411104001036060701c80240d8240540744110000d03071188650000c100449120b541d5440c04585400c40812100c1030300e4001b0f0f0900480b21240940701d55170604c88980c3c5107103440304039411003600c2041040c071000c2580420f0689004581c00034580e5290100482e80d5001030f1005002e40d4400c03c50480014861b40003402e0800b8912902030420340c4c2d0ba0b0724070090740e156061501c81c09500c0340044c013600c1800c015011a114110104d42c04039450320a01c43c1d144d0031180000360 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 678989334 1250 678988084 678988097
    0x63403020115051e060a09080613021f020a0b0408120708040203011a09040f020111030406090906090b0117061507050102072a09020a0512010801022a0d0318060608060708010501021c 80
    0x1b07003090b00a540c2000104055429504075180801d6200101c84080408a20a440c102c0c1080e44502121a4002940c0d0b025001444e0200e02900c07180003501000340115650001005800c01009803481200d000314025140c0345c256060500c1010f0035500c01c100401014450790680e94000d55450504039082a00000b01540c034505500040b01c2810b5040024070891000203400100700e680100314100306c03403d0700c00811009032075051410540d00d140007a10300140704000c16070001012050403e400c01300080c220020344000c6801c500c0540c012131b0081c6e410b07035800b082a60502120726440784410541c0425030905101600340c074680b44205007d803a8005074041121000380e40940304440b8502c0d40e003503079603500750380d201c00250207036002d0b0140c18024110308592041d00101202481071404c540c5000d4000703803044d031204400500f2204685000412030214020101e849842600080c01c5001c015208510300610050203035101039016a04551101490600c210f09641410b0742c1c5280314034010 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 678990584 1250 678989334 678989347
    0xc281401051b031017151014061603030f06080f0d091205062d0a060303110d090b0a02011107050a0b100308070b070c1b06170105063403020115051e06 66
    0xb61804600c00c08007007880340407105204c4a034084980341811038410914031140140748c00705118050050490800100c203040c1090030019020340c01881d80000c3e0008000789140e0b54500716450401c1103035510155401010784100411307480000000505500480111009041c1d03641c86d5607810014400e0000407070f03184e180001c084045160a03010403011148103aa41085003c4100134581440110041187c00c0c6866000070750128214451700c4a5803100d40c03031180f030941c1c41004c59200302038580031550389062180391071030b1007005441418060401072454098a2600254080015202110100c0014020000154000b0071545856400b40701d03010030361035a0000703890034180d0103401004481c0e0400c40e8250300222241000c2103035070560303036089102e82640303481903585001c0c06050741084041116900c80300c0d400c00d5100086c40c9200c41202c13000d1006e1031401c8600c081c0039044005035192030700003040c1c0078064260b001800e81215000759200306441d2180000c802d481c00c1e01d020b080080ba01 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 678991834 1250 678990584 678990629
    0x90304080106080d090806070818010207021518060301081f060815040c140607020f01050912010b04140f060d02210313060201020c281401051b0310 65
    0x251802044140c00038010180c450700080d0300c48800c00210400117502400001c0e500ca4001055405142d0a4441104030788442c1408105420381030030705900c0350f400f0802100180c54419a05001107150b0488580b00e062440b00030900c5040c1040c0c0c07a00c00d0f1070900040c030400790301054885540803a03140c0e00c3c409582402c402c2c0f014046580c055034040c01040c03240c04404254078030302889240300c1e24140b00d5113611200000520342007140e08a82002d0240808801400d00c0092103440c0d06050503c6803e000d80d08000401a080380301c3c030328900c0e94407991680c219007080d000b8407691004441c0c1c1616149412100c42c1c505201c020113951107003501d43c1910742991240c3c60540c1c040420700c0481c032900705c440740b5295500d500180d00040464200c130070005409206100303403030110000c0c00c0907002d00381401c04880c0e4481181c1c0105035050074003a0120002805050313000084000c00000890b4900d8020720301d004100c82a00d002090000400410038403001c842440b03800c3d585207051362107030682c00031203 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 678993084 1250 678991834 678991837
    0x30c021015050a060c0c080f0a080c12070c03050f01110708070f0501051f0e04050d050d0209031b0118030c050d050109053406140318060c040513060e0109050903 71
    0x80030f60400362810b804034089038404a100c00482c0100d2629800350342d65040c20f5996075405100724541e4002010410004000758000c064405c0242d088030010182411522955030117004c0840e180342c482c41082040000a2148051700111a4003c03c8645180c91080010303206900006200100000d0390340d0400001441c1c1c04201900000208402c4c0f425181584848401c250164144044c0702e000142d0344026400c000d104943c050044d0107407504200042c2d881c0e8200ca00000d46c45c2d5001c1c0a40002500c040000b00b140e0a25101c584108072056000506451030342d5208030b4050f400b224090000c0380c03c044881003112400d644960b44070360b0b10b00f0402d004205074040140540070341c2940321468031558007140580c10b4004507144d270b1010041c040c07624802d01e61003040c000c0f03510044103100c0184050003440e401070201204d00880d1401074012030a0440495140c005110003040c1400b803414815101911400c102008000150504c000076010010510400d071a0549940004119030020300 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 678994334 1250 678993084 678993089
    0x290a1d01051201061d060702030307020d02010c08131805130305090112090503040303020706051c05071b030f0e0a030305070605060f06040f05010e06160b0402012a1101030c021015 79
    0x4821100b9541c40d0400142607201d010136000790007080e061184840d140c0b80c000c4070040c0b6030080040d460050f2543c01c2c0002181010400c4c0e040c00159030b0481d02003501c1000900311040380718005444503062410f25500c040e010101c0346c000c9840d000c100800d40c0100c2c0740007201c89400d402c0c055150202400100c81a03d0791300740c1161001e090242c00400c000001020b40140c82c880e4098403102c58840c40e0032111402414800c02c4007204d600c0318807010001c160b00090708201c1901d41010b0800c000e04904c1c1c02c070349030cc8000b1400502c44c1001c80380b0311544141100ca0411080702e01ea6020342c503648009000340207201d80a085691b856020400e941c3d10004084010346019110301d485503550340151800c0d42c030038820780f07010401c45c1c01c940e00a46814021a001e003030300310b113002d05180f18603150122281d0b030040040307042c0a56000301c000d44000c008044818021a00480e100c808841d00c1c1c16841c07a00d40c42e0380345040c1414800309050711034001c55040c0035001c40c041c000921001d4603512542144103030303 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 678995584 1250 678994334 678994357
    0x10091b0609051804020a2102090c03040c080304051014040504060f0f14060706090201030f020c010c02150c190306030602030f011e0b1801021006290a1d0105 69
    0x9000140c9a420400d0030303084640850340400c0000141c010300c84500002c440081d482450408244500c40c0d200310640c001d650b1a1000e034001c80b6066011845822040e140100c03010800b10030401003007102215000a0407010340034500789850301c004240b85803801e00301304c0180074144040c00c0005d900001540c0041000070024005155602100300c0504041d020300c080c41040510301003090406940400382c0c200e0003510f001c0c608102600c4d480020300841a040f8105170f00c030010841e00c6400360024280d881540c8000040240150380040d282c080744500b007080d0345c00c1071010400000e0b41e480a0343d0740c2500049030b9030222101e00000324010152034200a020380c1c404010310032409d005412a5051b64003c02d03a0201900c40008514140c442030702c02c10441d00d030104020b90808070001c8090b502400b0600448032020460080308003580c5d41d41e0060b540418075007070f54640d9101200402d81c0071443c10003046203400345403000204041d410300030f0158150340403a007540791640305a04840003403c1c4c4 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 678996834 1250 678995584 678995633
    0xe04020703021f0e060c070c03020114070209010902040609080c090a050c0d1b0f170c090d1a04050d09150807171005030d020106052112040b090102010501060e031009 73
    0x3a00c40345000307002000300007a0074810000006d400d600044200e950309030700301080480b40c0b45160f004403401c1420810151a0307201c10b10a160058880401c0640a41080303030000d600c960400341c00502860041c0d0040107a5071019030700c5009621000c041c150825003507007002c41e031981e0308483c101641c0701d1000c81c0d0420314580800b112004020111513001e40b085a560b41c0b11400754044111040e003881c4d100900002c8812010401e203d00c80002480039030405055000c001d481502e80306d0301e400d041042c03a540d0b0403400c0c08220801c4010b20041c40b4411042c20400e40039810203000b0140a11809a89014040712001044d400c60150b848108a0710082c901da96151412640640451061384280e40c0248070f030341e0440203900d0040c040c200039940003a08a81490b0480aa2491040a9003181803004d009a4149110012010001380007401c030040c0c1040e42da2100710002400c54a0503801081040212101940169808500754000e0310b00744ce00491b44950904108020000504050440c0d40e00c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 678998084 1250 678996834 678996883
    0x1911030304060f0b010918200c010614091e0601020109080a0e0f030601080c04050a181a06031f0e010e06130314030f0106140705030a0c060b0a060e0402070302 70
    0x15140c00030310f04800c05030818400d000c80d0000541c0e203c10395000e07000250314551460701d14107250358403029001c200080000e41190010f0025040b0343e0024280074185c1e5101c180610004c607085981810010040c0c466414921308126103041c00d0000e2078034032061180781800302d0f049170720035085840215000240907584050408001e0010b0461110b40b078000c40440684858078034020503564125090140606608641d02c4200002064024840e01085688034110180b84400082d845402403040c110044030401d0000fa592141c080140040d210f6441585601d0311b1003440e8081051000d404c1c000820640d2051280501425403088800c403e0b11907039080081454000c0200e14001e40691503403441c001c45042d84051500c0100c4030300d004110403500405c080c61180e00011b1052a80d07544c00c0c0e00703040b1155036460450b801007461400041264420005000b541c1c0324001903103e0880d543d10001d403806801804054052501c244a541e0100b81401454024400d100b0011410324550341c4604 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 678999334 1250 678998084 678998093
    0x90123030c0706230a110c060a2c030a0804080909090606040e06150d0f1a010518070c060e0a230115080309100e03010f060320061911030304 62
    0x10088803081c3c2d1228148401e90380c00c4010024021515030710b00300c005803a44c0d0380c084040041c00c0002d481075854403003005070303810701c22040c814503014041040000c15034481c104e4404441107001d02c0300d61070500d40c0c1c0c80004019280001203640b80401806c2c500002e5603607040003041800b850041e40e03042507443c010402070701004581d0a100d00011142003180d031403550b4140340d64440407140321400346502c0503844801d207800e030440c0d03403140c3c813038808410340c040540e544400f1054040069408400d0b02401403101d40380114a00316480c0c40300101094510b03040c04000e00100401a029004035622100950400414400c424185401c501c0d217407034200c1f41c45104403201500d680d181031194a000e4400c09000c81c0d1040c000100c5007258011410180c640c0c04208101e035020703400c0d01c1885031040100006407400e000e508841644014009140c0b13140d403d000d00e0b615000d44400e2180c1000550307129031a601c80c0140c036401c0241c910541000781c0480e000791401009480000d0007031002208000400 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 679000584 1250 678999334 678999337
    0x30c04060336060513150b060c150702120a0518040b1017061503011e23031c090315021204080706060902070209040b04020301110a0f03061208090123030c 68
    0x10f1003000104855a02e505100ca900120420001d00380e680008505144124a4001c0c0e6915100101814130304880b04032036034030301145080c04140300d051400401845a0b01882480c20b01008003c0701894070b5400bc500620b2881ba04e2038540d51406030841002c041c1d11076500a03241000c000d881d00102c80400c140140000d461180b80750214402200026160305240c008024100036240f600e500b5039081034a40c407140e0380300519224205180030f00002c0c24030511b03071500b03031454610151036405a842906040c1406208d80d43e0381980c03044900c18118050748060318401302c940000500c09100c04945800c4007900c5075010420b900c2180c0020300c030610800100608040b403086008002c9155254040d100340e005180b0041e600030100400580400e000c00e800c0c1c0d900c00e20040000034150888665410650491441000001d60009a1461451300341c0b144002800c0c0900340091070a11039a5400301c1c51251001d400d040201411750310645501c4c4642540303071140311f0041a9102d207001111100c59 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 679001834 1250 679000584 679000691
    0x8030a09050a09091e080705011b1101060608150111160807060c0312020711030a06020a030606090b0a0c140d03020918070e1e21060606030c040603 65
    0x41d400721500003815403801e110f516542580300902c29403c460081c445d41030f084c100c034000e03a41d01508005041c0005e00070301c42d1101d502c1114040d41d044142c0c1c18001000c0104403440000035a2401e0824400c0a400c110201d03408002c20120400d240746200c012503000c001055001c00c41d205902e11500d644680e692254180e0300c0902c11509040c0d0364500440300465001405070200e00d1209482c0d040e00400d40003000c04500075444820802800401300b031400d0541d4500b50f5005601007850a822941406480001c240303078030304020118104509508103110f104540340501048100c1c640801001601404046550400341c41070401c2a11010307029622181c0c115226031b6411108401030f04078a485c4038051a07881e075442452400c5901480503038030403100601d80d420f8004c0c10246480d82d5280324803c0e482a59a007845440605070b01e190325005020f030081740b06000030302c101b0a5442020040e2412a1580e240120f00f0101c81d800340108070900386140007400c050b442e440e1540c20500e50f046100c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 679003084 1250 679001834 679001839
    0x6031503240e2404032a0b0a0c0305011a0316170106081006210e1614031b03060c0306011427010e030c1e0424080c0d0b07020708030a0905 61
    0xda0306000382079818400f0003114001e02086185007003550744d0700860b0b610300110040070000c205200290326440f92441040b00d0480c0031540b00d0754508a4554140142401403c282400c2501030760440100e00c2240401080462072898007102040c03030038440d405d485118101c1070349402d02540c5074039004044071000c584c200810f000740720002074114483d07207080c941e20301041603c0e030304c0d100c1c0c001e80c00024010040078250315106d4003060100c00031003854154003c009031511703540100c0c4104203040c06d1610700d00750084c018079007041607961624045212075002c1d0703220803a01d90726650344005948189401e034a15200e10404500d001c000c03828140800c4148400d540440e500d1403c888c01100c1d0000d103000142c1d0140c0201c5014611410584a0800381610080303117206090b0000d4042403c449401242d800e42d40214892600740c8000d800010014000300c6024240200e2204085171b0711403600100240f410b0183e100107500c240c0b00b80500809000b010b001d0f41e07075500d032548000300345020b0383c010f80d0b2 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 679004334 1250 679003084 679003123
    0x504050601230f06071b06050913090308060d08040e01060806031005010b0a0c06060902191101151517070203091207080a0303020a05041205010f050106031503240e 72
    0x54442401a00c0050340480200050000f076030b00414008560010f8904a403424034504071004088075001405c40546855699140c0300d510700300800c5101c001480074002402e28000c2040e020941c0051941e5203c2d0042c0c0d038012442e04a0f28100b2840d00c256440007810f0002e5100115102d58480b540b280901d004608407610700521100d0300d01260003c0c8140c01c10010100400101580541e288030045401080f0000b05e4941e01c803003281c20f0741c1c06042d8040d00c0340c00c07140c0c4030318000d600300c00c0340c2c6480f2032144020070071502001000e5503004200d000d0011071a00303200b140615a88100806409030100250005040c01e100c40d010b5641d410081480f07225040302d0401c50864940050000c1c119121070000f0b10f90240c60303440c1980298040c01e250005c0190802000c00c8400c0d5480c0c20301c4540b8424800050400c0103070340c1000446074180c1000007050704100f51995559a4441c0344d0055070f400a550150300c015841c00d0011040d40580700c014103a042c82c2c0380541c4c00c5404960715003200480213044 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 679005584 1250 679004334 679004369
    0xb01080312090309011e0903140607031508060106120e1b090c0a05070f030e06070c0305100b130f020918010e0a0c020a0b19020c06100b0a020a0201030216060504050601 74
    0x960f00c0340526841c0d0390000310f4401342807201d061985907135011003a0700c0c2070801455849440f603054207140c040c12400d065106605211b0f41c56032506c2803503140f018201c0540f80640c00c0001c200d442d0b10f01881884100180b400e00d0710b1000390168414541540a00e00f140d6420300e9002c40c080300d00000d204150b02c21569040000d082c1c0b1b4281c2e04691103441c182c1d581a10b00302031542d41c0c5031910100c000c02d50402c03000e18401a2643c4032840245101030203210314a500310310318a0604d14255009440e039503030504000e441203090b05c03240018841d000c00042c0202e0340b0000031100710002d015a2500660100007216840099551045854140c400609114445607229103102d0f00365500d0020000040e800001802c2c0070503040c18540740c0010502d0440d0b4000b81c01c0c03c86400580e082500030003460b40082c03080c04042c125500f10344000b4220b0141c21404c040f602c40002c0e48984074142c010b0306040d0000385c1c3c60a60002c400c00081d03050f5100504024505042c2046940d600d001d0185000f00c0504411a = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 679006834 1250 679005584 679005601
    0xf0c03090606050105030c1204050c031e0d091409180118020f060304020a053d0e0102060c040b0a030905011d1209061c090f12090e0f0c07030c0b01080312 68
    0x80303034490700447c80e51500d0600180130788400d20350010000c1d1880c1c09800c2c0380c044a42c0c0c040c461903a03016031148005108010000e072245c10440a1100300040c008465070412412240311030b00350603034000b141e05040d00e999180d03100c0444650289a0032540d460400e418400c13800c40c016000e000d6000340d4914041c6900c41050202c5444240c0d400380d48010000000c0001d494203110f417140212600c000c0d2a0985014407800e02c00c002801c402c2480b12281694250f0141c0c1c0c88900314100c410f092008010078148100b5011803440303240252109480000f071070302500703402508510b084640c000300030440000ba0100c0000c100c84840c00d008914041d0030340c000442c041c1c45040d100f42c190010a003614011582030118414000581e07010041503c0d0001d4070085079003640c80790141801001030403a103400c00701e402046021950003500c03003010300d40244140e07240280840d96000d2085078540d540c032419802d0544400350300d014003e041c0b000c250008551300f00044041c00350226191080c0750307252140c0d10b1 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 679008084 1250 679006834 679006837
    0xd0201141b07080d0c050342040908070507030c061409011d040e06040201080c0c0601030204110f04150e0604032a090e1b010c120c060f0c03090606050105 68
    0x141e1140306000d01d104207940c1c820700d07402400d1040c4500031943c50b020000344400b0035110ba180d40540402c60100400581402135600c241c0c024100f0002c403500c2c2030141010b41050641828080e0a8550000389140030303895a5000c0c1140a07080450303035485429a16010b5500c0e44240804c881c0c181106c4c1e400500c02e4044d02440b02202c0803501c4260070183c0350070044441c64030211020f03080d1000202c203800d507078a4503c6004040a4414041d080070701c1c20380005801128080c04408035070000700142c840c401c0d0042012810750b0780c1181c005c204c0941d0000144034602948004080901c0002030000e00364000c0758100c54130b15000c2d102c0c1d107034015100c000c100c6940503078880540300039403981003002c1c01c0b01c0c5e00302c00b0380145a0040d41c0720441a00c55904408030390b503000420400340d01081138844200d00340140140314030024a4101822400e039540e001b4002c81c102d0b100c03800c0c000c05945542c20400643c101d250b540c0c28021003000140c42041c0010003805070050103842c1c0b1860308801040d83c1d4410f00 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 679009334 1250 679008084 679008091
    0x5180705030d0507050c131d03130e0c040302030d120b0d02090103081b01111e03090d1b050303130b071404120501090605040b0f010902071a060f040504050d020114 72
    0x1805000c001040b448266040e51209800700d585001d500c01d1480159609545017406850602001401e0603050744148c0e60740000c407500000a41c014484600e2042c0c0000b00329094640d008040c1da0305483d0340740d460707955000d1508000d500d40510003140300201c0e4841d5041c0203c034080f880601c00f07501c20300700307100703072107070645000380d0000200c80061020540f004003c0c104560039100f21601404540452800c50340440b50340100d4034400115600d8180700202c410482c2110015101c0c17075402c004807019611894005010b05214803002110482c5010400401c080e039040f5040d01d0340c03498030890340000a1002002107031a01c03134020115404a2107030281d00c44c00042c03141078070300e010700b0800d00d8103400d00e611808031455900d03114124002002c07401120300980c400d01407621142080400000220320507085840c14034818400c2e403003c99084005c01802c02c428105061058840c1d102107900843c90b0380c929508642805c0902080000004030307138201c61201c0e802045505440d05030031010010a4 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 679010584 1250 679009334 679009339
    0x905190203120a020f0a05101d0717070b0409020a111902120712080309010b010f02060408070303061502061b07030915050c07080a060f0608030d090206040807030605180705 76
    0x2c1d4407100740792440402000558810700495900c00704641c4800d207018110001100d06422210300c0d4102101e07039000f000b252012441c3d260b06940c81e1740038000d655034001e00c19108004100607a04070141c006200f041d0140c8080081d150755180c40c0e03503046029511022042c00018000f0790b41c052401c10200705c00d460000000040ac030407662503000c105040c021750180003e02d00404100003680001e08080c0103102e84603240d0b5035164602000718038211002e00c3c4801303050102c204188950303107501140341540240d10101140e114011824220000e0074943c0200001030b6840360080055500010154403400607403503902209001700b00c3c02c0800340030303a40c0011b001c929403c800348040c4500c8224076440c0c100e60300e4207508040683e51028a44401507001c0881074001e1217001c000e204c524003c200e40c00060000c113012403403810502c641c0e030b441512184083d0a03540d0f081031045686240844000703014041c1199003d580740e051030801000192015580740801740b0180d5112000410990100c5100 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 679011834 1250 679010584 679010593
    0xc0d0201050d0b0609040911100806031018060f050402190f030b0a0e240703090b1501090f060306050108090a0206032e0f1e0f060e030304180905190203 67
    0x41c40b090b10141c08421055540240140a00d0105482e070b8484c0300e02140c007590360341c07a500c3c0c001001d100e000380c00402c0f4001002401000c0224984000990351009044000002a80c4001c12010400403aa143c0c0c0144141d00304140c4041c10302468111601940c0200c600043c082d160354a40f00c6800342c11312a9030602c0082c0308040020039031480d00603900280e010340214654090800c558140700c850980004111a0000030180e041d600e10265907001206040c10032891195171900e0a90484c020310304040c180a0241d504003591003000d015005002c2c243e500b40560f034499202030054186402a0ba00243e030050000c0d250400000383c503400d29401030030140c40c6450b060502108a20180f10714410b884000c8400103002070240300300c400070944424440c142034180500140c404103103802030301101140d0704040c85112b0000300014100c03000c03824881146590040440d04501840d8012441c64885901c0036200e403a1940003e55414403501c20b0782c404a007070380c4c0c00e60101103150002a415522 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 679013084 1250 679011834 679011847
    0x9100507120b150403060c09140307050d050f0d02010f0c0c080301030f1a0a090204050a0209030607110a0606080106080f0d0503011206020415180503120304080d020c07170c0d020105 80
    0x55002c04060000a042c1c0c03490700c2c041104410460307109a0044505aa80d1681900c1007036004d00040042c01d10443d4070b050906a1600095841c1c00c0d80c081c03d84204201c440030f104100d41042011080c40c030420503510b502c1c480b11400703402480f400c101d0701d03800c605000b1011035440c03180b01d02902c182d0340040c0c150700b1642192201040c110410104581000c0c0411800d200c44100000681c403625050402295001841c03040c882518006010040c0560040c807412601c0d035004110b2942c048520318003915a07805203840d4614282d10702d14040c2103030b0300d0400081070550341900041d0980d28103d003160201001c0201e41a511440307010803c00051b014001404180103409860903581e0080c000507040c1030312402000107544403105110003048940c0e4500039111000d0300c100c1c005110440140c0700d402c2c25201c26861911005000074114280003400b20106001a4151a554120394048858150300d0b45030028030101d514551101b03030301c940d0200b01410715001006502190703042c2d445508080 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 679014334 1250 679013084 679013117
    0x5250617061203131e0b0a11032a24010e0a060e07170a1116150516020f030310032004020d02300c0d0b0a06050309100507 54
    0xc0c02410190b88001800c159245016081018141405100f540c0da015a1301d442d028110326143c1c4101d044070640c4a40081242c281540203503001c500c5e0300c1c10300b021036011102c1d480382140301e07130540e02561800b0030124200c0b001d010b0a20602109a40080f07441440001c8150240354480c14a00000911440d005029400c640d0010341d030020044080896070a458034100c82c40403604442010019910410600182465a800b144c000d809048200300c185098410314070584250800e6100c444a001196030411169490101c00034045280c10001c0342418074440c0b0303c140d0100f00020051040c0741420032146008400c03640586109500f020030940f5580c0c1d00c201d070380d0320300d0200580745810b2090300b00661510b0001b0401550310f1000141c0d038800404840d030344003d0103002d01184040f0327440030820b1660010903680c1c0107080d610701d0310340342c03130040ca1803201400c1c501c0780304c0d5040394050b01f0010360f8a411001450141c405181583d00b030740c1070348212130304a560072940030000800302c80c0681e6181 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 679015584 1250 679014334 679014377
    0xd091518030b0115110f21092205060d0c05010c140609030309060c09031b04090b0f101d041b150203030612061006050309030417030c16060909021312052506 69
    0x501220340080e04050148c40040d10071015510f040b010041449056515902d00348210380d400a404c0750580a0b01115445154140605001d03090500c02c0d660b0300304082c0801c00c0502c00600b240722044a03094071b0100300c41501c3c1d80085c2d524034402e200c0d800114180e0701d142070981e03038002c40140c0200843c1940030000781c0c5c0041d00058003074004d941c1c0d03502d81000c41d02e42e0300c44902c0740d80364466580e064204050000800e44c110340c0050200703401c560385401c00014250b4101d42103a0043d10504640c06013881800c04001e00e070344420880e02e80b03101c000c84d000c0d801102840c81000101c0d81c20a002c01d01104040d00c82c80f044501c4030306640310302c0081c00a180a90f014540013480c0004882c10292944100300d42c0d00c010007003815070303980082115004000c0402c071130311305800007182058a003850300c140980807194a005200985801141ca2605144904500e030000d00100d0f1354662800118117009882e0703041c840202483c11800d5080c84507048450407000f0444001c1e6480340444010801a5283c0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 679016834 1250 679015584 679015633
    0x40510020a12020c0a0b07020a03050f0703050c07030b07090b0a08060411040f180f062412110c0c06041401050306041404080c0d091518030b0115110f 66
    0x50007182c000659007441588003900c405a40e030001020001010304007802030300350041000d011984260312050000340e100040e6043e00180b81445502c41d5040d10f1b0940c0c040c041d46404c004540f083c50701c0001400060600f050148141f03403654200307a40c03640c0d0410a10b10800d80f9074004a1407d00c0030510300d0a243e88640240880e00c00014200768455800d40403a105aa00c80d03400c2840c420103030202c030000d038440d8540a40c41e02d00d0400159141011074503824041e994891081d5401c1094070708010f00840080c0f20980c40c12100300030045e0960307400442174200e001d080c0750910600040b03000f9810450200c0c2c0503500c00c81110780240d00840300441c2c141d0b000403d41a00b0a40f1003409400f030400b01040039009070300c509856620340c903821755543d2405540340c03890700802071441007c0004515400510007100c3c01440c11014100704070000c2c0703000c0001c81e840140f80c0c40e502d01c000161242042d01c08171418645a803001e1080c82880341140e80c030174450703c0c0c000080c1c03c030803900c00301038000f5200c6010 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 679018084 1250 679016834 679016837
    0x5060d08090f0f1509030c0a0609062016080d1103090f0d080a270509130615140315040c1e0b07030503070e090907031b03050f010e15040510020a 64
    0x3003d25600d4041090310301290203014400c0340c0400c0c604101d2400f0304c40b65035107980550b1a0036426103003000c02010840c50f4132641c810f00c00403511801c4901e00700c8000c070000740d180da030488a444869407400003400e5814818020709009a2080d03003030b8a81b017241c255420002100046082000000400c600040400d040c10ba00c4002c44d80340303e0010782c00001030300b40d5000f0303030321144042c040c1c20500030144d10044a5400d4192171415041c0300955a628000d43c0084021400c00158281d625200c0d00510301c2d01e1222511403900100000c2d84103006040b500049400d03026110713240d6003c2e040b000f5411090764002c14038403141000f0320070001c00c3c0607800023a00310300d506410401d40d5440c0115407548141e101f0b0f070014200104104070305030001400d40401c078094900043e5460407850203901c400d02c9000050080c0c03d151406480e40c10781e05241c1c800385800c1015a0420381041940038000c02168500ea440e5004282c0c0494041d2840402984103d4012002d82030807010505510020b6029201050 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 679019334 1250 679018084 679018099
    0x8070f021507020a05150105010305090f030403031803021e010921060209060412060b030d092114070e0a0e0c0109030803270d0e060a0207060309020d1b060305060d08090f 75
    0x1c002c64010408601c0780701b0b01c0a6440980d505282c001400c0e203034018a070b01c4a80d402034040d0744070402e00000b21022030390103181503d54481c045c00405c00d0010f0552000e58404002181110840040c0c1038050000400340c07110820240d80b11200388111911070007030420001c9280442010820300c0e0000c06070664010042464035466407048180703020345034419141d9a540e84140810760800f0007940c0844032050411450b0315280240c00641d8414006d00f00011604490321b80c0708000d84a0722005a0181d03c40c240c41c2c01e03e44032803103408405000c4403428442410000e034440c4054021510800382041030751801c12650940d1a503150030f62001e400c0101c0001944036644c0d080034802402c0d040c1c40d8284024208240c1c07407034001040d106141c6c400c2c038032942003009100027180e0001340c0d190803a080c41c2008038254030a800090840e4842420252040072180e51690f91041c0c3e54028030b0036140692410001e0351291b000307001407454141c1005109800401480b41245031141c2e00450300ba80c0107001d40d = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 679020584 1250 679019334 679019353
    0x10180809180f01030309080a0c090f06031416090c020618100615030c0e090a1109030d05030103031b02130b0f12010c0f0318061e06080a020108070f02150702 69
    0x201104441100c4038041c140300380303005104146d44086a00300030b105940007040c02c1011501c802210410a1184000e281e43d52000c80c0120140c43c0c00000055422880e48446a1240101c65450b0a1451039020050381c0702d45001c1010700e650f205151200006a0041843ea40d910309024805580318404001714032501c1100040982a4080c030405404d03c4442081e9001031800c000d000d90756031002000500000180d900c2603034441e00070182e804940c0e8100030401030446480e40c180c5114918625030180550340400000a80200045040703e21079951015041c0c4803c2c91023208c4450010000d52180101e290001c800c4265003260710111402804002c010003050002801740b160740b10300d109265107841c1505d07101c681215840000302c0c52400d09110a188154580c0d14455450100170300b03056460154044200d9082e544581d01c0841c00000c000041e16014080d6a4070502001240001c900c02300142c03095204506000309003491f60024800300380038807012104850018603001c111b114441c0d48 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 679021834 1250 679020584 679020619
    0x9030a1403070605160206060112060b030f04020a0f03170d1107050601080d020a020f15040308030f01030506060d05030d091707060608010e0c09130606050d08090310180809 76
    0xd5000650600110355621440c0b400505980d0010b004111265201d018492504e4012800c60343c808402d186c0b511f2503c3c0e104118400030192074111090300f0b01d010080200d010055a82e007070049008980040d016a610800c0791001d562900005000d41805412a040103080f0380252603c0c51500d1030104581c1e0821a02c5086504442010780303440e0700c480e00400c50000c082c00344511030040743c4060000003c0369004500c1e03117000750304014011a02400459001081b600960b130146503c00300031a92030400203a050094482800291240d001c1c003408100c007484c4c81c04a0780e6105901c40c001c0e500307261429240e00002c00045406840c848882c012902c19843c0c81002042200d1180e40c001868509000e4501c0c2180d07551500e441c4650301048401084d0350b2071810701e507804140d09000d15001000c40c40d122028080c964016038020f18800c50300810017071244060301c540c0c08141c04031920408107030310040656000341310f101140c14102c940f0001040d2140018108680094407403a04184140320 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 679023084 1250 679021834 679021853
    0xa030207210f0801080d170a11040611010606032009040e0607050d06050303040f0e070e04020a0305040605060d0b0105060a030e15010e0108150601030504050a050d02100b040204120809030a 83
    0x15070074001407030310407403440d42d41d04051118058a05100284180d80d903c040282000c2000001425240365610018401c03003040d411a40c403d031080141303035032602d03036504024041e0071300e112079a0299401d00e400454128030901c10001401d1004803036000c0020300e2900f5501680c8a0f511864111f602c941a80192041c2081058050443d0ba0b5820750b4407826420b10b00704482d09901305500c2500708000411020590051007415240b44120103001070302c6824007522500d02003455690000e0011079100c0c41503030154130a0303100e24050001030009130740380410403164012004008100040c001c0050155060210203003058032150f0400295071030418808501c0c018410880e1b02a4625000040c800300309403a590b81d005041e65001400c443c03481d10f21614122000900c094105a5104001010301604102e0341c141c0300e4104080c1c0700300e0154150001d4a03040182840e044c0340f030030810140e24030305042c4221001ca621140da8424030070a40c7d6548040b960003071480301d0385840f42a00b0f81b8040b605120 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 679024334 1250 679023084 679023143
    0xf08150112060b03090106090209030309060307180b07060f09170f09040501150e010503130b040c050d150c0203040f12020d02100f03050a0501141005040b0c0c0310020304080a030207 80
    0x3c1d00103859141c841a0075003520070540001001d1801400028a55100003050700c28102045850036100d507100ca0341107131404070400c40740c006c01e200c00c50006144c13292540200075040c000c607002d0000361220706640d0142d03406100010724189192203044d8254140078090101500b215211a1030b20101e8000101600c0d0203802800605020b0103900910310b8009200110440081c200b075400c40c41d0215540c040045e602c480640010880c82c00a0104000368280303001038200144403072480c2c005820070400800d807002840f01e0140c0b525074a900c00c3c40c0000240c508076058980c5050641d4244500740d4074030003244204980100800d400c82c401656822046111400d043c0d0369098810903101d402400d80e240985040c06003894000180f105544000d1000e40104050f1075050704d2814410701101c25200d10380c40a500c00f500814504059000070800c2940ca42084007100c8070961b500031880200d200603640102156000c0061040441c002d40151000d0b0b8000c10b9260a02560f80701aa0138102000 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 679025584 1250 679024334 679024349
    0xf010f120c0e0a06230a0903120201020a0e091009021e070b04060b0d080403031b0501230f0c0301051201020c07090203241005070602092e0f0815011206 67
    0x50040b4400381420304120707004240c246010342000100181d04503980407560241d9503603034000168409060f00401e80d0200669000c1c502d4500b01d01e900100074000c0d0080c04000e000030f2008884a481c62802105884c001c440444903501c0c07003860001050000d42c03211542c034884005800510b4407071344000c0064152140904072440c083c0c074145c80e00000300e8510f41c180e5413082c20341c4111800072030b10103c00e403000d503549403d0040c40740d10038204071800d00c0c0760440300805070340c02c1810380c8504404c0405400c1849800000001d4a0344600f8030143e242c200440d02c05000103c188010083c1d0310300040c04607001c0c9010000185071840500190703007841096040451110340020a20880b2201c082c441d5881d88410400460404903d00003d0324143d1030203411000c20801041e02b0041c00240c0c2d0417500e4080c0d00408003024140040d4102d0b1941804034100101c0308500c1075004000c0b0b000d4440907645880e6682d40c03091580d030340c1880328a0300b424407200764100105401c603000d02c2071062158201a0203103 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 679026834 1250 679025584 679025597
    0x70302030a0f0516020d0f02040609060801110306100e010507150501150c0201120b040e0303010314060606071208040c0e070e27040b0603010b06030c0304200f010f120c 74
    0x801d036025281c504121545020040204114800e0b00e045440701c20a042e0b04482c0c41c00c044c02103043c400d03030b81400c81401075800791400c040025413000030703400790040b102d140c0c000b401f020048190240590201301d800030780041c140f2010701c4540340704401d0380e0a0400141007031810a012070700d4100d10351100d80012070600d40d0741d00040c0002140c0c144031821580d00c6140080c081c40456000902d84092a05903a40040c7c848810682035034498000040072000e51301125140d40e928107040c0f91001d031010b28904940a540081962818100c007100c41081d0020b66103030070b118a030381085031101001002507840004202e00424004c1c80781203e1802843c0a45e207090b0050415010420040310f172000310300f00411a00141500c1d4218203081c2c642c440d801070710441641d5541408a1b0140c1020038034980e100d0b0f0008100f013145001d400286000c7e6020300c0410b03415454020341d5051501c490903c240d07000c064904440301540c1f0032001c0c0c020b0b20074946456003201d008024042c0c1030343d44c00b14144001c030b0365 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 679028084 1250 679026834 679026847
    0x50615031204120b25030b090a060f0b210925180504050102070f03020a11040501030819020115080a03030524010c05070f170c0904050c120a0807030203 67
    0x90800c02445145100d44020b442c29140038500030341d40c8043c4200802c01000034000405080c140c03000341e0303200d010200c8072101e0803036408001001012141c1c00c091250390040046071100c0403511484003a0303480029a0360301e00d410405450140d810802c0030703025042c05c03440d03801c1c4000700c0707440038a0183e00120000c2001058001c803803102944880342101c020141c0315410405164505098507000a26110018503a04c2d5400c0c0a07029116641020f049a041240340380101507001904d100c00c180103441120000c4c001c00c0802c4185d85003844043e012400520035600795140c1c001404d1800c41e03080c0000900c00014840e03c10a0181b1039000c10f0303032600445d2020341410b425009203540805c40000c15000c01c180c04c0d0b203a108510001c0c003080d040100c0e045085042203001c02101010303200c01101d484d41c2580d504013115415a100c0c100001502034925000d240b810009110790049500c070000d8154294034a052007000136101306507038a148110008a404501b2050040054034000da014554420 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 679029334 1250 679028084 679028089
    0xd0203010603180b181002070809030706090b0d180501110a02100204030209011a0f0f0a0f020307030806012709050609010806010311090717090a020a060e01120c0c050615 75
    0x1c24050382c00011030360740030300f0700000b1303c0d2135444651004410b010394166a2151314050700d400b6181130140c5070944000382000c20b000c5500c001d40b51110080701100c140d56210103048640001a100391000804244201e403000c100a0700280d40d89003141d0070a140f440980e440386400e640c0d035443e185520441c0002d0b03000600340d0500c0300e1030803010071801c01c3d850079141d540880c00107501489418030351540d07030020302c0300c00349c481045a6030100031090301e50322149803026100c120740c09807a1410208240381c20058199001200b9500f0340398241c0c4508680703555100054841051145031302100c1c48900d4040170312940903003503d00c041c20450100080310300c0c01406014a683d010703004404154407650041002803114403034084007610603038442c0c03920344031000d09503105524003101c6400c43d14a241040580d00b8001001c0c10605e008035482002c0c50342e502d50030b45a10890008190008041072401600460f03a9004103015911910708010306503000c0e00d44138101441a00c45800e50b0804107410b41292 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 679030584 1250 679029334 679029341
    0x30a030603060c05040b071502071209080d1e0e01050405131d03040509011502011515030c030b030a030c0c031e05070501030b01052d030108150c0309070e0a020d020d0203010603 78
    0x607111030402511741030400300f11005c0340c0a10103000341201c2c02000300382004221501911903040d0b200440d9602c0c01010300024002c4691401f5030300319070bc9444039440006220300c082050000120a034610b0040c10410101e450545038004141400010440007403a81c1700c0d0700300030000c4d0f5290603000550040c40c04a4000e440c0401a02054562090206110560341c98010301d04461107940103030000b4051403000e90140190300002c0d107401c081088000740481c1d030b41e0b48240e1401560343d02044a007080050603000c440c40d1019054045c0e02500301800003d0165500c00714840c003c4985d01c445581d81d54400b019841d41007040801c3c400b100e0049410810704100c00400b074102402c0c240a24000300000806c40d0150700c042030030703001e44130881c51900030861201c0c54101003a00b0380290b496071a00c0c2c10070390700e05100c40c00d82c103d420058006940b060700b090940e070243d4201000b074a0700501c0c1c6007416501c1103001d44030312205c0f68204103d444100840c40100354840d0780c40300140c2c6962404030080c049 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 679031834 1250 679030584 679030601
    0x3200d060806011a0a0c14010f061d1533071203020703083103030203090f06090d0f0216061713030e060a03020d050a02130f0605030118020903030a03060306 69
    0x20000f6000e40c00407501d01e040641710130001a142c0700c4a6a0024200075503040c42032410714a25520f070074202c41180c2e15680102055417440a0555540684285115402001142d0301e281c403000782e880c060070601c1c0c4041d80030124800b826488809100c03442408401c003651050811061000003042401c10000340d1030384000001d14101103060803159180905402e000800b0104124140c0440c000141580300414011542101c01c0359540c0005140c0a00254400e8510703644510031050604840f0341c001a0151040c403841000e4030703030700d880308000344c80460025151030f0540c01560194200d001007a408030006080381e5a07410440f0041c0006511010005440116200317404190740e0301080d044201d42884d0082a1102a56120191001c034000e004641c1d01948a904000a0202030403154000d40820180c0480c2c2800035542c4034410f09a449643c800d80010607028801004910b03043c2140303015a03501a21b01520f046411800242507500030405c52010030741d01d81c002c2c000e00c209403046150 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 679033084 1250 679031834 679031849
    0x424151217121302060d0207110406091509020706180b0109110c060402012007120510020304030f05031e190506060a02031c02043609020109030303200d06080601 71
    0x3500d82404040540600c0040070302a10300e40c03000800c41191500b4003110400001c43d1007c54a0780041d1800b1010384a404c24001c1c407840c10701c6400b2031030710417902c510304455501d05400158145840c10350b4019411403034040c1c0703074a6035800325209180300208030211720a1240400b030700b0942c105500340c01103484400146050400502805803d984c0000d0151780058090030801031151604040c2006521007034012035860013440800142192000c40001006104074143d0380c0c0c0900c1003050b0f100300d0208030340c0500001d00c1d800e03c4003a00d5005400442d0040c640c0b55903144011100c1c4a003040720102501c00c89003250000078081d112404500c105c030f81002003114000d10b0203440e42002507490045042d0130000d01120300d920b4950354210f038100c4000f0b00b0360b0304032000c1d4041c407004001807101840008542e921200f008480f8840e01134424032048650507150144200d04544048006258420780210004400450002e00d103070880c0151800c6400303c0e01c04100c241c04c140c40a400e0a0060380140c6 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 679034334 1250 679033084 679033087
    0x10030b040c1e1a16060c030f0b030a031709190f050c010e21070e2e0501093c061407020306010b03060637080424151217 53
    0x140d400d488286081c440483d0601c0c0d202c0c039500011102d501004c0c14001e01c2036242007003081005802d608060700d0070444c500304105c404520790074103844106210703002380001d15030380440006170070001c136058020368040100e8110070180880b4141c001d403055819112481007178070003001c11900f000a040c9181e82171030f01000d504d400340003198908640305114500d0100020503d515003104106200c020f085514102c1c18509100309003c020084a0402d0f029200b10890b1910703810015421610844506a4403a8002031805848507060402e00c0614442204a00ea1a0b00da4003403c42c4030202c11086080e4070310003646400c0019000c40c0d011040e4550300070051140300c0150307401058850450b04040c50319941d07580c4130360000d1941d100d0b200140c403002c50340004107410803c02c00d0180140000c1f403952081c0c6030080310f105540e00c4104540c000d107480c0d00f0100390300b4801890103504c168201400300c040b4850090198424085c43e00e9003024108011103000c0702c05015107026a030b20310a0580c1100c9 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 679035584 1250 679034334 679034339
    0x203091b0301150e0a0b0406030f171204020418020d061b1d0904020103090b07021510120615121b0504050f1605040302040203180609010612060510030b040c1e 70
    0x4003d0b845140c40360010b4003414500150f03035000aa004943c1104c4014010403080342c4034035044222412042d0150b803403050b0314044c282c8200e2440c0881340c0c86a01d20324a00240d070358550801c005040381e000300501d030000101201c1d005842d96400150854803d020105034020403144410030347c000c4c004010100801c49032880c214580850010b021048245c80406241d5142e00040c2e000e0440910000c000030060002c1040880d800f04042e003031858088407407030494861041d0640c0c800030310b005a00f140489007100c2c100048680c0e0240800c0f404c0c000c1c08410749643d49120441e448600c5500380c6260401110881d4868001e40c04580030702000c90b820451410004031b00394240c20000d00c0061008078008100c040d043c05841660002c60307000300305640d203180c84d0079503110610300700b1145141c038804c0ca800300d400180c0600910b002e484980c0010b112010094840c0005030001a1009280001c02d44020021038440001e051150740201d0010030946d00d0034a0910b007500501f145450103c9412009 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 679036834 1250 679035584 679035611
    0x90506031b0f121207031d030a0201120f0f0507030b03060f0708010509220804060e1027050a1410081311130c03060f05150307030e07090203091b0301 66
    0x148180a4815100340043c00c243c42a200d00d0b00d80102c0039050102c20205804040552015680c0408002d445240c0e40c0030055900341656a40d50b000c000340880d001c0303010307000041403d0f44199101c0c040b108000c10401e24040c440b108440c000d454420000e80c41c1c051442003818100280d50300909102203c0340c1074945441c0013400e000040c064984112440f0021071040440e03001141c417607490000c503440190b50240380440c41940b01e8404c4c41d0204a4440c150045441c100c202c171307076400c0e1032a01e85820b080000d26203586203543c0102e4149050070120804a100c1d11181c0700d0300040c0200a4480b6000012a000c01001140c600c05a408000512040111b8642000c0c08030a55a500c801e80c844481c0f008000501d510a001c0c49545140d440d2100741101c1e190700d6044070084400c07000c8601c454548480070300c4005076440d2081610000100041800c8a100368008005403c0090940d402c003602e49aa031401c5c0d0b403041d100c07e089544845a000704685001c0510720000004400800901d420a03d8 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 679038084 1250 679036834 679036849
    0x6100602030412020d1703100302120609060601030b01091a040602060f0108030409090602070602220518220c03050102092106040f2a170609060408070219090506031b 73
    0x2809141410440010850080000184c40c0d112110751b40d10391500742d082080440d0140b105a101e4141c2c2d04090081e10303070200e00c1034003c09582c03019200c03550351507005401500e02121800c5c100030b99982c0008585100120300e00c00d405030091003c0d036982c9000e00013803601c02c0c0940103060404000c0c0c01007204800c00421201215050700b4082081c1c001810400c0c0207018060b0040c159900020b0148018924500e145c01c2961851607004c00b250b0325401440746148246065201003200100407412011070469001c01c4a4a12603035103103140c8680d1307946000072034154411107060f074020a0301143c62420010202201d00f54240902e20003410700c1d4100c0c0d650320301900c040c003c20446031a10042c0b01c192412030381444039814003a036142e8044020410051468458a400b800b115041c525010790040ba2050013007092000a01c4a40c95548900030190b1000d4400c0b81d00000c031100020414025108820003005420300c002601d25028040c0750500220301044103e650b00080310490558400300c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 679039334 1250 679038084 679038119
    0xb030f0d030c0201060f090c020f07290702150c01060608040f080c07090e0d092103050307020a020307060c110103111e04030212210301060504050108040812010602061006020304 78
    0x1d40440c0c0c51600d600203034010102c80e00f04210814055030041055161900441d413619880e40c00c4030102500001016103400382e0b40180503441080d0464a009640405030400c1d400d1071502c5280d01d080a1540040c0c1c1400100404124000300030071b510018070801c0c455040186458141807486103050340d9998440f011401c001400100045800c40011b00100200070142806c600108450700144540c5540c0e142e80c0010b090004804c0200030400144400d444032071245d8039036000c0d010000740ea0b000d5445030402840541144613100c0c03030f440940c2d000c010103c0104015101c103179180702a03040424015a126108034103041c18080608511141c220440e07c01340c42521035049050807015007100079202d01da001961001105640c2d00b407541002c1050801440700c0200e00c0e8400a05030401c41d4071b030109100344ca011460500013084194018000301da8481c1c03244084038a04a0200e02c0060b42c180700384c010000503480310301000044150594110050700c81400158241407034564109088040f11 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 679040584 1250 679039334 679039337
    0x20604030e0d03030e07091b0e06091002100908030106030b0f0f1c020411030601090515040506030408041806031218050607051c030902030d0e09072f030d0b030f0d 72
    0xc00e40b0406140c42603008021051101041c0c3d03408a0352600a000940b000c0658160f000f000e1085900000f40940c43c1c003c003904011b070045003844d00c84001c100118140c41c14000541c020b0f0040400716810030300c00c8640701c521a0b44140d440e5414840c0040c1255440d089150103506800c5807490160b5070080f080c00c020718101c481881d0301c0344520181109641e900002500700e410b24001031a00c0640e070700036600c03c52003aa0381c0e154044e035036401c01051100c4ca4100d128029801c01050001d81081c1c4002d41e4854061000d9034074107035071420104000c00d104071450035095900e032000e0003000310489100c0b4941101e440e0142c120010101458048005449854440c040004201d0100082440502241d901504400b200c03a820184081d029000d036070b9040307100c0e0141c7c1c01c0f444003242c080e09441100641c040e219100c0d5079102d6800f078512184484207000b0019500b4000f81c650090200501d803481c800d1030186032902940b8840809035641c40c440b142c402d170445101c0d0024000005140c8003546480e = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 679041834 1250 679040584 679040599
    0x20f07081c06140d05190b0f060604030803070f09170c10050405030309220c0807020601080a0308011e0305030307170c0405030d140d11070b0a0b060a030c0509180103050706020604030e 81
    0xb1454001d29145c020140d130012607655031421800d10000c1c0f030380d503445800c460341da00b00e8640d149c0301001090300c100d000041c0141e0b03090001c212542c0c03180440580c0307508a410000ca00a0303c4032010340074145808103c031226409100f44d0f510505203070041c14400095030078000e052a00b40702c0044c1c6c40b0301031883c24030300807444002005130031034005031801c00524001c142000700403544032000740801000c0391540701500c00d50340001251080054544c00182e01661106070503400d10441d000314400703030480380070021140c10020010800c01e000a500a21013a21203c0c1003802006241046100090203142c80c0307441480b080156403004500e690b05100c0c00c5c58500451606280c0c40c001d103006589e0100d40e810b242ca007462440c11448c80007046d8442c001c002d1003138595560410070b800e81d48902061034000ba01400144a000e000703411020248415080035070a150340c00001c159000052210100a60084401001444070901c24580a003600b440544014075164401504603505900340f540a07000 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 679043084 1250 679041834 679041859
    0x1150e03010b040f020a0f110303040b090a0b0a0c09060207080a0b040819050301090b100e0108060a030b090106210c3b0916030b06040f020f07081c0614 67
    0x4080d0301060820b840144104081802a00b8150080d000f9032000000320301e4205d5559601c0d40582600030a43c080500207603d5640d0395642c96030a540b0250004030a4440c0b038100360000348444134150f12590101c0400282d5400085008002d0310507a8008403d6420050f000d201d07241e00412040060b1390090103030f0031340762110700c0c06503070078400d00603034030000740407244459110340e404001581250084501802003840020401500502c2175600f6008541d0f101c20400c0ca55005612181c4c0c010001445400400d940f038076240709000040300c8010340c5c0e075940c0106100720306402c80a102c04440800401a85c001d041c1c0d41c0c5d60140c500307401422442101000a85148900040c50b00314000300040004042e14190480c05a051801e840311103e50003124260b004500401d10200100c030740009002d14182c035002c040c0002400021024001e454003041007a403d900c1090041840520450a0039650362440c40c20110b07056400d040c00161b10b0403c04100004680c00101d40101ca4045813006072400 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 679044334 1250 679043084 679043089
    0x7140d060b0d0807060605010f03110d050601261e04030f21090308040308150d02040b040b10022a06042112090914041a10030213050a0b030601150e 65
    0x498502d0040400354002020010011160444811283c0070780305d80300801c0002d0000d40035950822000a840e03c41440a2201285079400954101506040500701455102101c004032410f80099600c000d00e0b480c18000754501000c102400c001440e041d840c0756007001d540040460b490141c6403403c01a0702c4203514000e10381c254045a540003150000c2100901620f070290562008075802e90204000c000000c03501910351450418000d00241413254950035035080000a1070803158a83c0c03c01da42d4a826201ca0300c0c2c40c80c4107220050f041c2c0003008411150441e0005901800d242c86400340300031844400240c4804007030307800b07031145090380c90796000d400c1c8031851205805e044c000d040d200e10900040714068200c0401d0003983c40c850014402c21580301c00d1030180b0b0405a500a041d86005110171018074200d02c10542c000300c4d4400c0d00000e05503a070300050240b011020007080d15542e682c0900c18003a0142c81409043c1c40160040c2100b907240c40d900e00588003051011704107025904a0800c2e85a = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 679045584 1250 679044334 679044349
    0x30918070242071e02120a3c0f081501110714011b05030a11070801020301150908060405062a1c0e1504060903090b1b07140d060b 57
    0x510b81080030011070001628000c554403003d031585004580c8403104c16280c64102180600d00c0e41c81c94000701643c1e01c5020b40803005a20024014040126819034509150b120001c070034a4218207000d806214000711442c42800c00c600c104030f0081c04801c4808556294006260300d40c0000b100c5807400115154000580f00c80d1020441c41480d40207411001c44d01c1c180d503240880c4182001c2e42c03400c0030310869000540c40622002030283c880e41c03082c4880c0b2300704d42c8140c070301b003031400003c00540b00d51079580d502050980c1c00a0b0001b420000703240d01c6208100da40034042c3c034001d080803001415130341070644805880d0007000e002e110b8800c0c4500d805900d18070251491999600c1c041c042c0030781d2104012210711148581a01c02544281400921301c0ba11600145102c800901150704030b100703458030790342c2c00014021614103d051042d407410001c2d603003070ba41c009805140220756280a40f00c030180b00d1117040c014181c000c0759420640204024075a220409a80f0309160310a000252008040b000642d00 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 679046834 1250 679045584 679045663
    0xd050c040c1b030f020d02120301120c0e010306050415020a0c060e03160c031b08030f070f0f0b1f060507030309060902030f03040f060e0117040204060e090309180702 73
    0x81840e07228480300309940034180a00809441d42940c008046c1a20100d803548240c0c0d43c100e00a07072044c00103000c1ca401c3c0e411110b400324070070700412802c1a500c0601150a1209074802e803021a81c510800003840180071120803240b0b0150403c52404446402c040e00d159008400500100d40d80d082c000306211082044070000c160351006a0201e10051400100304011400700700c801011854003144c4002020b103010051f54243c0019604100c0a0500b400c001d8101c04001d41d03540030205116404211100c001c0c4032039501400503030a82d860644907403034036007401100c04d41c403042004c175003005420790141c15680003030f81c035240105a0300550b0070100083c01740c0d00710196140c029040c05100140001000703000f15485118140c007c0c0f95201c2c0103a0364403e411480300d0200e551002c91524811481d140280e00c184000c0c1700203166034580302c001c00980c0d02165900705540c00054902034a103003111100c0005220042e00340443d1410310390094413241d04821180c03020306402c1c4200070b5101c8041d943c091 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 679048084 1250 679046834 679046867
    0x30c07020d02031c110c09040b0a02120f0402030c030c100e0a0f090212090a0210030c2c0a0e04170318030703030c090518040b0a0b19030c050d050c040c 67
    0x884801c0640130048504911903502160035494845072020000ca00b0882d00310f0f0041050780d41c1d9985881e05840702c03c00800c2d02c450a40e00300b00701c40450b8125503649000c0c00003411826401c2c9803502c141842d2112030001940b007648901000d0030190740b8100140c001010781d180c51410481100046402d01c1c80340e400c41040c4111840b00410204850341c050102401a41c1c5030030350507180d02c4082d41e10b5815004000c1c1d0080010300c5c85c1103510f4065002403440c801e15190802950300300e4181041c400d4528881e02035001d1851100c00c585180000603940a45003032144085e041c10070b075490462102c0c01c446448ac40600100008621405100e45488c0d41c85100066907a291400e01c5c008009241c1c042c422008519411070114147c107000e84201d40d15050381100b9803941c1c071203031a000c05003100146208075403520350a1204840e03c0d42010b50310003500700301204084904510b850395400b0300ba030300b05900401440c560040420f40024950106c8441940d0000340514103030f00895407910410b240d4030 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 679049334 1250 679048084 679048093
    0x120d0902030f03090418030c061802030d080907060201060f150e0603011d0a02040e040609061d1501090209011e031d030c0609010506060a031104031b0f0b040b030c07020d0203 77
    0xb00100084020702c41d0704000c81e0100030340014103902180d10204a032020300010002104030340000d609a01400031841c10140a901d140000c1c0d00103482d1085400c10980080d00076014408108810000d042c0034064a0000348095810602c0300725440110340302e1242c20546142016000b1130058003076a2100390b0103088075580c3e603151861802280b02c02c1115208003401d88001610380b00651003031710180e074650512000340d41c40c3d42c1c4507407015000e140400c0c1c84240d5520025100c030000d04090070400484030f00a07140ea81c0c00d8a02084003000142d010411113030041040208503a407008000318070707603110384001008ca0f0804004a001300120922100d11581a50030303460101000030241c51000486030032900643c6c1c92107001401c1c0d400c1554203541181c0700380100d5801e14041d400c4400503072004109181427a03902d45995102410005000d142011a0403081c130403070100d44101b0300075150111340d0350701d041c0c070341040c910345444020509101b41d140821001d045607689115034100f260005d040382d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 679050584 1250 679049334 679049353
    0x122104170a05030415231503070602240105150f0f03010308070b13020a09020a050d0513021f20010f0c05090f0a030203030421080a20060405120d090203 67
    0x3924950080c0d405603605c0f8204408562482c0b40e50080e498090404806041081d400040c00300011901400640034014481c05d4200c15860421003030300142040d81c0280480c0e8000d1081e0000640c14035158003403084804018000d03030322030340e141c1800420f0640e0815074484559800000070300174070901c0040319200000010501c10520081c20800e40103224100080c0c41d03009484101004a420007504402840380410980b0b9440c0d019003907070f00050902d07e1030064240b00c90ad08403442240c40300c2c0c182c2d10000d124025810000035100c0010651101010561002d10014201d1200c0d83c410070325800d4868104802c646c020341004403280c0c8110014414070714016400b0703045030084a003081c099070010043c80301c58602546888210303034018000d146858200602c2034182c5091030300c001d41ca504070301c03442d00000c1d019000520714229903590310300840c5000c0a808040c02c41c2ca09030705091364040300c00e00c00031807000300e560307829205807200c0c03030b50b540480c42120405084c2500c006507150041000c02c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 679051834 1250 679050584 679050587
    0x703050f030304140303060f040b03030403020918070b0c191e0309090c0e01090e0a02130f03020a14060d0b010e0303042411150703020d05011403122104170a 69
    0x303180950311401c0d0035a0140901307400785513240400c4552a038041030703d20244409040a62160254040c05000d480c6002e450ba0040751080e00d003a00c842d10020b45c0192000c081200130f2001001070100040c405281031250a080da40d154121340036800915815020001080030581c003514440c0d9980c0403002004c0441d0502429011007481000203071403d1080d005d400718130a81d42c1c2202400f0584501c4065030804440450b103410041c40050015820000c84400c0101000b02000030050038210003c1c06045106028404000c0d0780170300300860b4100d17140701c01591801e0903181408040340e40011a0155140100c0d40c90b40022032050301800000743c00300c0c0d0b901d03009018207000c5161102100115040300b030100d400c1d19030041005842d4111105e00303076152076203105050700035045180c00350400100400c404220b5100703a000c145151035035404d010085c242840701c00c1107108008480c600306490000c0c0c2200103c00c00d4103200d401c0003521300090030004440b011148510300001c28a44805144070b0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 679053084 1250 679051834 679051837
    0x130b0c0a0809061605180a031209090606083403020d0b030d0921051509150912091207030507030212120405040b1f05030717040b040b06030703050f03 66
    0x6014005062071000403425000010340318060034090b103184c14070210040040394541c0021001002c44003140880c904603948030410708000d0750168903540b102006201e00540b230046179030304c2900c2682c2414820410160480502548411103000b10360390204440b1400020000e109180c4880d442c00014a03480c607503065024101d0b00107034000411801d8012000c059542107035158140001c0d907000c81c18400b107896078071600605000c95100700b202c2c502d01c1ea60300b030401c00d007034161008400c0c0b584200400c0d20400c2080880c4111127544824003130400b480c106407144584103100405440008202c0d82588a80d4610750407091084203480810303441e440e09645594241c0300607445114441c0124242d13560214030f420064229000fa40d1a161405060102078601c3c0800c0c0ca610500382c4c03030b407106202d80d00200c02e4180740d0207640300c995034540680e010700f40d2706684040388400c12a141c100400242c01610305900140c1140155903199500c000081c42c200351900700a200703001720519184420750000 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 679054334 1250 679053084 679053097
    0x1021c2c040f020403021e030703051207060605100c030e061204050c01140f04050d020d0b070f0224010509180307080307260f270309031002040806040308130b0c 71
    0x40781031103010068204a0b09074021404040d501203640100c41d000b00307940540c501c2c50703002c001e800d4401150780c81c0c03038250400d402d041070a00c48a40c00140740c0c04100aa100e010054602143c60340d03030300220f545d801051500003040060078400c1091704000e541d6036440541d091200c0001d0007030a2854180341040d268240d00b4001030103c3c00d08012200d9001807070003030341c010500c0940a242450300c1d08042101c2c0c0300001070140e80103514210400046200f00366a1441110388c3e494108403030316100e000901d45142a289000c00d2901d404c40c07898500c012085440c1115421203419080b61a0b00d241100e07000f580c000d40310707494440080c0390310802039144c0156104200b55110954500c00c40c03241c100c0e0410340c3c0a003d680c6500da503070008811201102c0756030f03000f401c00900d0740c252005604005022076080700040c1070781d83c000300308014589410080c0d0080b40244000542c24a460401c8495035040301500080c2805110b9000032203100900f00941e050310b8200500c0502c900f41212444e046a0008 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 679055584 1250 679054334 679054339
    0xb10050408010b0a030209041721040c05011446021b2d0307080f0f011a01110a060501030c0311091b0f040504050f0105090108070501021c2c 62
    0x1452040781c1d0315144090108886c2c0241c5002459500d82e038541904143e5800701c550000d8050007584554940041e02003007030202c0050320003841c2001c3c189111051720b42e900407810011b03200c010b01050303000541601c0c10303000d0541200d0400d6140104107440d10088000c105442400d0400040701504c1414122440c80483c0d02135540c00c0000e00070303241c003d183c2e03441e0054209400225044a03514540308009944400c0040424503414500c0040e0a00d80c00f58001c040365403043c04041d41c01d49090110003c8083c000c3c000304041292400c1e4130318a8102c11040b00d05000101803503203100c0c00705102c80c40c50954045000c000c55038583c607007404c2010341c50100b034034a1074502020101c07508001d19610302405000e481c0a07807030150b10410742e08580c0041c006106086050000260035100c3d4081c513402040c0081c00b5551660400082c4001e0280592000096034424141040141d030080b886a04110000304812214000c07020140c58000c84c00102041440c8414031250f210b4202e0500000d425408 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 679056834 1250 679055584 679055591
    0xb0d090b0a1107020d05101407030e0606030a0b1305060702011b050a080a1109060c0105010306150e0c0d060e240f06030f040507031e03080112080304030309060b1005040801 76
    0x19010454100d50119103030401c2d01c907003040781101624002c134071052018400c2c0d084a018900580d4900705a400720480c003601444540140010303503405000c3c0c84c150500c1040140054603110001950301d00a0b180083c040d18600e101245025000e928030320381a903040800c075901800c4c041c0b07000307000b481c0220240744a50444103400506074454022640d0b60581071b9120030180d00d800383d90400402c40801001d204034030801045040ea140c8001504025100c01c00000300c641c55030510704283c50142c00082000c0d007004809000190090754a43d800214800f070300740d1205e1814401c9001005641c0203448190b41100c1000499141c14140190429180705240050103010007800414500c00c11181c2d030001040c00001e603684240d02d00d0750fa0250094045443d030990320b031210036518090f00246c40400c185600d000040c150040350260040124941340c412295150300c8244036030001a00c01010103490750910703024084650028003029000a09184903000c0ca0031015055030b20074469241075501303 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 679058084 1250 679056834 679056841
    0x22a0d0f0f020d08190c0207082416120e1b0103020a050d020913110307030509071d06040603061e1506020a080d0e0106030602040311040e250b0d090b 66
    0x30940c000605000d00d0340052091025a1406942800c4001c11401c01d04504410149038060031340200d5003130200940180441d503003003e080e1410441d04c410318400540c070a80d0b1404d004d15000f0b17902b551000080781881d403041d204440844080c0f45003001016468144581401c00780345c0803d80580550800c009024005060001541030340500070034980810740600c0703400b60b410210b800034a41d0081c02080c000807098030b6605a021904000c0302a08a0300c000300070401c00710340620409400451500c0200f010500c1e0540040009040d401807000707014189000c01c0383d81d02c0300d0b0045400395034008030a1294601809410042e4016030101e0a0141d041c1924450030002c0c2509000690356140d000e420a01055217517840030340d110307a40022443c0e0381d03012800e9603400e0030b115aa025600c201d00141c0d40e00c0ca1030900000503100840e2039403169103404146a50032200007144023a6010170101d01e100704185040c1c542d0020344c0c0c5d6002c2e405100780001c0c080c0241e8131a0380440d00c2644a010718801946 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 679059334 1250 679058084 679058087
    0x601200a2915030705040e0724180f060f050705010c0509030115030f12020319090302101e12060305060108010b2d24070303060503010509010b0112022a0d0f 69
    0x5011121507030184c0191000303010a0403c1c0d04410507402e03620302101e100035660010050090901c1400c060383c07140a4541c0c0040b5a48180d581800402c4a2480e604e02130810040407940c1245106500c103100b541300d4007090300b9000e081500d0800390403500802154000340d8000d42243d200b008414400d51030a011400c0d102c440300c0700c0d80c0980e81c100f650120f0140d030f940d03241c0d200d500d8071004100079440240503c201c1d4207008240044402050f035514001d1600e5441481f0703442003010208020701400200c0e00b040b800d03000c243c80f820b0942d01c0c5880503909607804006d030000c00494001a01900a807400456601e070150011650301d030082d140c0d07003c08803240c82c464004a01001c3d0004885528481c3e0900505d0502201000b80030100c1110303805070044854000d107a8401042100401e4a50340c003000545400c0c0f10b2a0707072002e0000024402072207034100090400781c803400e5070311410380c0c08104038a403440c1550f20120300000110000c0f215400380d501440c2d03669942548203000541c95492801807a = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 679060584 1250 679059334 679059361
    0x30e0f0109031b0f0b04060207050d230a080f040c080a060501180e07061805040513030906020105070507020607060b090f04140102040b0306210d1101050604050601200a29 75
    0x50341c000e802c13032608a0860343c1c1d4000c0c160010b0b0041e20300741d409000ca1008140188091004004191078594507803c6245a400d00300c42da515850340f1480081c4407080b075454100c0440d40d0b100365401c4015000f581e851030304100d0030010360429140c0c2d05c03c00d01c0d2340003080807943c0403605899962001080c40d20f10004a4001d0356030005c0d184010782c10544007003102c54084c0079454076198191901840781030708c8401042c02c484d822292400c14460740141e020078036803c0100000600101e2000b03104600e4039a1001c0e200e4441e070b400080c05540700094001c00e00005600c240c0000c0001001074201d03040114820000f107500703450650b42c0311508a10038007c0c44051080b5001c1f1011048514299034400707040120301c80f02500d0601c0e00f440300c6a03044030044070511082112282c80e031600802c101c00c41154500b1958000c280078015460031040c0881c1d41c2c0c00c602c0002041005021000b24030108128840c102000000000c054006c1d09101090707c4d040903007004000d9007405211000c9540b0340c012103004 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 679061834 1250 679060584 679060637
    0x100203040303081803031311010f02060106050a020a0602040f1829030c030d030f06120b13080c0d030b0907030c090306111b0105060909030703021c030e0f010903 71
    0x5680208010000a8040d815155000c0805052000d0f446074843c411810342d402110008444032030150704c44204070b40148050b0420030b0a00c0c0c0f07042d6200c030034880070b540c480041c001d0f4402e00070041802c120700c62080020020042c0d100c0c2e001d5407156906c005146c0110000d004d04281d1100c40c1500d01a8010b05101d500207200b04040f050051680e0700c0c0c443c140449040ca05150540035041d4410b0458804001c1c0040c015071940e00042c10084d041d40c48011a91103404c0051420002158100801c42691005030041201c100b8a0030707400713441c507250b20140300f2480c08d9642c0707000b590218055280c05030f04c0b28082c0701041d6110659541c904001703e04899800040c0800704404a2052021071160ba00410329900725210701c42c500302024030308012040700c00070240402c0e9191010801503042c031244440c1c0184c4040010740c1080d883e66800f0b9183c0300d1842007184c07034010954282c2a524800e030410340c8029429802ea520b10025110395501034182003c01b84d0214260103060704454058070b40c034031107 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 679063084 1250 679061834 679061837
    0x5030a0503180622060306080a050c040e0c2e0306151404120809101e0503090a0b090a0b0708090a112b030824010804021216060e10 58
    0x181612410b540ea10340d000300041c00d60048030030300403803142030f41c036141e2a0304070903120240048240c40c2c40e000600f1703945640c00070500c0c6d401c0030380d40900107100051005800c01c41200c3c08a00480001d580d0384c64040b100307031416400360782d001e078034404c0030721034040c4032881d11240f45415008101014285e0641f40741344560b0041c00841d4101c03e0040b4414440d4107241a0080b410030320707007555800c816025201010040d0350704d00707002802c0811454080c440403040f000c1d5040c44251010840c0350054106000780f1b0701401d00c40c0001c0011283da5061219404030340d8855400055070800e504520750b107003200c050403142c0a02c05004146080e000c0e1210b103226100c110300030495003829039243c491880c50b201a00b0b41000c1a0b42050000c090703140350600e00c02c00c04065084415a680c10000d0442102420328410350311054074158401c0b03030040048260318420300300200700d03890710b2000c01c40f42d4040c25186100b50140203201080100100500070485010b5030742d49443c045810100300780c1c5080c03008001c0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 679064334 1250 679063084 679063087
    0xb090106050a0311180f10090e1f030b06102a05030d05070201021e07111c02040f0e1b031005070c05030c0c1e13051b070c0e0105030a0503 61
    0x1080c03070300c110700804050146140105040400c0207682c500d81c0c02c550014808903c0c8045038113841d040004104840c800121030f80b00000c101d40d14064242400e03402581060b07035009000070001850b00c9040c1c4598201c1600b400040d07030707490404420000381078584d41e100b8140d016110071000d2140c2c010380c025880c41c1002d4038401503450032103880050f400d0700c1100c1600013442000790102d85440385920442250b00056940c2c03e00080e12031000081448181070034070309020501c0400c0302c0c0301055070b1015044d00c2300c0c07010301d048110700c20017121203180080d4410301b01000241c0e941c40580086000220000c1212a0680c0409901c05072241022801d034050340726001035015014150407054015489041510008070301e911624212785c070140138003060341c3c000100000d4170b00380a0703406018040d040d611044501c200400080380358001065043c401b0b1b48071000300d01c00848940c0c00d540780421003802a90381d01e4440c90101b05110b842c0c49060581180f000c00040d65040216000e440598003001a6 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 679065584 1250 679064334 679064339
    0xa0e09060a020a0c1e0203070605040f15050f0703180b0a020a0b04021206072102041d0402030709090b060a0e162f0c040506120705040207170a051c0b0901 68
    0x14003e4200060310310030031441000700004034925030030320251450201c0003c0c650300514010703d450070803103910180400000300310401841d4441c825003c165050741440c3e8030504100002140c05000789248040001e500141d120205600410403542e45201c520145030190303554450340000f8000c030303242c680168000c3e07800c00000a22505000768031600c014a14480b50b90f0000c509894107500319003103000300e0710501480c3c1c1203140c005112198030101f16025440c050800e0346000042c4554400c103c4402c6a22000c181155000d01521015001c9000c08110b034043d103040180300c41c201a40c940740216200d0001041d00c800d503041d0140300740e01c102001c608211403100111200717412816108116440050f254211083c003406015001d41c03020700400c0702031340081c10001202c40c0501014824003800c286480b0504000c100c4c030040391002c072001030b220b9545052940c000380c01081c10044545000800214043e048001f030000e01d140018440890040540140100d5070410803290380b04468a004 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 679066834 1250 679065584 679065601
    0x1b11010515061e0307260103080f2a0c0406080604170a0924030b030601050a14040603080c0a031b050c0d02180907050f0102150c03070c0816020a0e0906 67
    0x28450030a5844251801d020800940304060700240c48640000d02402040c01400b5250a42c1b410b444400761400030075545540d44042da070f13226212840301803100109164250040c0b00e0000003820000021059403d0384160060b0f443d110582c5c0018402c86c904140454010400100743e4400c0c1d40c0140c0f04004000b804503101015080404080c0800c21003180c0443e10740228008000c82c094a0b6503081507501c003c890140503a00382070011400b035400301004210704c0d0b840c29038100c110740507001c4051468025a0100c0c000e0300c45a0406000040c0001c0d00d03050800340018451080f23802603035408100440c0035524041c1800d004000740807580502007180347c6281200b00d9040706480141902482c0381c149540c14500c0300700301d0b2400500d41107544104201d090644004203000024030150030030503100c00f100c01074020045c0c140d9000180100004111a000d0f0560300390b142d820400d002d84400d00b1442d507500b640c03801c2008900440115100180840380d0a0b2058090120030300a059076640740c008 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 679068084 1250 679066834 679066837
    0x1a09030d030e1006030803160c11061308191e03170a0b041a03061602030315060705030c010507120b090f280b03060f0f0f04020406091b1101051506 65
    0x105030b640e5000c0d805041c0c088240038400d10000714404c0d6145626403400342082c5c03041441e669032000a020110700e602002404801103003d5000c400c50301e241e107500c50b0401c0201c1c49040c6c0d800c94002407080100c400103041e0907800220b10036220b1180c0310010058400514902038061a004000c0350612215031008d515180c41ca591200700088001a0003248c1d10004081c1d0b900901e1300665000082c1c01420507007000d00c1190344c4908080000c007000e8400c0d6000a6032488000c01c40b81c441c000f2480011013507a00c0c0b03070071110041d400400f126100c6d85001612802081c094079114007042d44a05180d58900180c003401c40110350061480f0b4080e89d13010448100307020018940e0b04e840740c07024001441090b0a18102c1c0303601c0c0c20700100103045405041410715095000d0041418000b02c041041000c5148205640d80225244080140354460f44086009030110303801950f03440342844800b10340844441e200c40d000c072a065a440003d00c04180449088032016103000311030061244040c9131608001c070 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 679069334 1250 679068084 679068101
    0x11070b0c0102090a090e010b0102160b0c07050409080406030c020c2d030f0c0a05090f0103020d08090603130b1f090c090306090605010f0801060b04050108190608071a09030d03 77
    0xc002528068046002031000c200035040145020364030020890345060074401d000820303900780014140c003908000d02a80b21034442c0b040c030340040c1c0000ba0f0042d000c0f50911085d001080041e000b40308152091138250900e400070700800740024035064501414510008981c800d21101170704058180410010560742c081324860b0059824150001072000c1c3c0d1004c0140012650068000c0c0112980314401c100200e4125031209102d03c2004090101005445560a0440780d040300c5d0900d0108940c07802d52028003409010503030284011080000060754040f5105607076108102d40e8050f9900c040901680608070310700391501e1601c454080c01240d071240d12132400c01d411402d00403110350740d075a129002c1c0d54440c0b02c212000d98484d030040188079103910950001d40405002440403e0802c41015694043c030302c555410802d03550081290b810310340803040303103818070b444080c4a581d407100ea02030741d0f4031214403821899040c41480c1d6401c4030482001d0f95178182d1f005010b07020035665510210701034440f01 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 679070584 1250 679069334 679069357
    0x90a030c032411121f03050610060c05030d0507180806040209060409121110060305010606031b14090109030501020a0309031e270e070207050a0609030210121b110d11070b 75
    0x620b030076030080e882010841c000c6d886103005041c41c2c6499800201101220340c044000d10075a001400c0000300c0110590f86d000007181030010791680c50302d00403600100b4500900d0345100080790b01082c00350b804204148038038000c0c0d884925944854051008440f80380d4400782c091002404584500d900c110880c0328000200c9040f9a29215801441412910163b0080750329039981c2c85c0821426806001d40c0d4069030034110301b1030202d6161070b0040d0114052443c0c9410b01703900001e2100550303001d002200b000e90b4010000315141c054045001d00101307a02e050a401007802410468480f5049141841c450313000c583c0c1d60044000d41940c0360ba00c0b504005280784045000030004a240c0e440c1c8018244130761030380ea0003800010f02d0442401045241e54000c00c0800509801c14009a00c03201604004003005280c4610640988080c3c00c00404580c0c200032408104201810482a4840b4440843c6d18981e01540d10080102006482181c1d05150500f4643c0003104100100a8200064040010301 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 679071834 1250 679070584 679070611
    0x901031e030e030f031210060906030b21030c01060b090f0111030c0a0506010609050306041101050307090b0d06091410030209040501061a0c0607080714090a030c03241112 75
    0x1c000a1306000203918000e60030350001c920010007812400142d03070002c040114030318030b580c00d00c0e800514030810b42c000d802c00d164403060030324056120120400001c0d1306407001e03001104500440d491b280c0e4400010b440c3d2075800c1c280003140da032410504941012000501b1034812060000040d5040908401c41d100540000d1010308a401c4d024042030456074400c1d8054400344d81065400fa02e58007135900814040d60001d01000000750b464891000317299401d003040f035105e56403000c00b110031032400d800c1304240040106004d0501001c6411a80a4411305101440313500d60000440c1d6888404481d8a072189040c000100007608094500c10b40050068001040050321241c2c0d02c02804100c0024490b0300000050b542104c130018403c036030300281d070b0b440c21081506000350010410980364003e81801d420000700b050156442441c1d000080d6071090a1055040c6d40e0b080200301c500036900b50b001c16100c4500d8050001542c1c0c402c840390a140041c0c80d03401d05a038401c0720f135410300c0e005001e01e411502 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 679073084 1250 679071834 679071857
    0x2010e0c0f10020a020d0609021206191a0d050c010905063a02030f071106061e13051005030f030301030b01090504020409140604020f030a0305031b19020a030801050901031e03 77
    0xc51245540781d25005030340c00310348103035a0b1042c0544020ac0f101849403503001035080c408543d21402c06401d6601342c03c01c000c0b032141c2d04181211548288204250380c80341d1055400e60800102103082500ca510036201c031307409903a9683c14013903030f880703200c1d20800c0c54003041d0601140c51010840d008803000c0150b5411000b42149900c1c0012a0310558904980e41e0b0034404005d40c096005210b10f0122612310b000d015103040032008104908911303034800110380e410520801c96512012030215129081c1c010034050b0381481050303c00c6268003401594044c2c011a1500c141640002089070304995025015102e540c0c83c001d0b041008000140081760b025448036402d401040e594421800c1a500700b4026041d01d06003481041401065941900d019401c601d860030b020a422400f940d5020220884414074070703411800884451203a1140030078500341d5044103542103540000d455034843d01c60740b03903241140d80300d50801070502d0b0b0901c0300602058051701c0c0b4440e14421002e440c14418881e040907144482d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 679074334 1250 679073084 679073089
    0x50705300414041805030d0f0b03010609060f0501020a05030409020307120912030608190204051e1f24200613110904020616110d080a02010e0c0f10020a02 68
    0x103101d5400701a000303084501c000340e140707000e1140f800e80c03450070060011150700b40c0c2d94194076405003042e00900c4a60f01d49020400c81c140780c0101e801c41d032004000300704090f112440c4000800240c020a0102c4c1258440880d86500000e0030412407038202008504040c1f5150b91080a54030007480c2d54100203801c20384c46808445402016480303441040118030b070b41c5d4203a81c01011074030507038050003503075004034000391016000342c544c0c0c41280d03010390340810319544925a420340c2340803542a00180700104420400d0050551044014800121400700c0f80aa510510144800d040d0b012450344600101380c1410107034018460307041017072099040c00d1001140036030b03c0c40c00c20508440b01d8070580f210803043c43c200442402d0100c5d01c0c45044a0310300300c600302600400c000380203d88a80301605000808078044c0408400100c104440c000e004040d151071614203800950070003070382000950308200329800300030780108851074810005401c0380360481d002800c02562110200c40003083d4043d4206410243c1c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 679075584 1250 679074334 679074337
    0x1e02030307080c061003030e041107320105070807110a12022d06041b0803030c1206040b011e09210b2a09010e12060901060605070530 59
    0x118001c02d000d640302c44103c4038031818030b040100600c1c4034603050390b01440001e07004040380b651b410b000e44000030079102281e10749aa52081130380241c010380352503144c2c0c0700141d0041800310070405c070f1840620304074060004607400d80e4402d0b2281e0001c5074181c00005c1c2018400d06044045003102000c070344003450240c40d190b0060007114442401a000108112002d4100c04c65842c01c00c82c02c5500c3c1500c4040080c551a00c41e540680001c04103d039861460b280c44401500c4031000d0540300e01508d549041c400c040c0205a401407807034042c100c81990010f200c529080c0b00e40c01c1110810303110001c141e00014101e100214510104005029552402007440c02888407000d0b9110641c100d0000030f160b050424040c0118000c0441d440c034580260f400000c45c46241007c001d0800400e2082d0b102d50003900140c40c05a07081d55a03d8100c007900c10784030003010000551600507000302000300000351721524101c03014440c3c440b02410551040e54107490219560b40c05617010080f03004202425003a1588000c1750703 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 679076834 1250 679075584 679075597
    0x31725050c0924180a0c020606060c0309240f07020406090c050a030c03022106120303070207140301140a0504120908031b0f061f0503061b07020f04060f230d1e020303 73
    0x21541e492211b0745030550100807603604401d00329859410004940c0310350ba901e10680e5200c1340034800d09400341340043c6220f5002d8030244a6840601d071650614491400345070410302050f4805c504210001840c98403d104000820720160303142c0e46001c9000b50268041c288101104c410198200030040ca14404182410400c144510000003d410610304106149058091200482d0410802d00258a40004d181c80807607002400601501001a0020340144026026690300980d0740080080300b00d66a400680b00360700c41e810204070300400c0d01b000c41e030300f4031035014188440d80100b10229020320070039002c0e20002a500122410503410100711401c02070192489040800c01140c1c0c400451100d03035400000e03007400e5004164074608000902e00c40710701d4910079003e84200286070020343d2641c0c943c00d4160343c0007170401d0007150365030b0241c2c1e80101d0480c45051080102940755400030700110364680030102c0010400c0c1e00100013500c40301700b20020b001200d6100d15509103a11700589081c0040d005 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 679078084 1250 679076834 679076851
    0x1421010c02060f010807060f020f010609050618011a18030a03030b030d0f0503181c120b040b150c0a0f06060911070507031725050c092418 61
    0x80d04520040003914000001c0c044041d1402c0040040c03129520000b900b10850f209840c0145020510400580c00d080c040042c501203542841000b0407141c1c0341e44c001c43c1c042c450a4842445e40d168100c4207a440880a0045140c0f001749291450040c180354400f4040c5c2400f440050100c0c1512800001c0c50503618903412004a61a0340078a03003140703400c0c841d0114020642c180210440b8090000a20a04c00240481c0817001c070350446070b540000802100200c0402803254451480c540040a0090408501140844ca04098200c0034504060003606003d00740030b06142d40405c100c00785075080d5001030303c400c03040d441812040c0c40452901d10301500094090900040da442c02c11386902c0694900150b51a061041000601c0c0016000214001203a8000c01801f090108840072680544a04016100c02c4400080d490350400c20305144010158451821640094076100a2110f0a80c5c00c582c1041c0c4403507448001101d01c10108041011303080d004107100d0401347e00c40c111840301e22007500c2151 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 679079334 1250 679078084 679078091
    0x1030e0a1101111504080304080702030a0302070807090e0601090b06130e0402030c12030313020307050a0608010e01050d0305040b0903010f0f23060a0501180803040303170c040e01142101 82
    0x4110b0b50300701c030346001d043d581007015040060040089154295014100034020b21000000405001a900640f907101d03600409483d824802420f009556080700d000e02d49003801900000a04400c543c4600304041358a0000b41041b6880d00700043c00509401c00820703000200ac20141c0c2d0340d06020030a840103001032880c0341002d42000c1c018145002c101241c000c0c050a410860022400800025030750f00441c07100d40705075207007081d1000c00d0401c0030a80c4000d4003d0021440841c42e59004010541a6821202d440c9296030380c80c000c002080c4d90400002d004500c04000c28018a440403005010044d8060300201c1c0c031801070014442120b240d6100d403010f444d0b9509020501c00340002031403810102e4660098020300b01800042c100c49400e204a50500c00d1284c080c554440018011000500140c01a60f4a0301c1e52424080e02c0b5500c1070140540750001e1600041d2900d0380d40090340c0c02d44003503200c00c858aa0a01544c51454412040c01c69400400c2c9a12010514652149194116480000070 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 679080584 1250 679079334 679079363
    0x52709160e070918060503030a02030901181215020c031804052a0a0e09040311121c02030601050d091103070609081209210c0f12060703050601030e0a 66
    0xd194861503421501c804415001032089456214003250300fa500c840075a807a010900108240082c002a440590580004500c281c41d40360084064000f0210a032a1008442821203007080107001500070303c01508282100000896048911654440760780341d801071500004856003407a41e0001c0500b40101071036540112304074200b50041d80e406c85030305040b40350f00796101c0c100c1d0001e1219600003001d102c0c1010800000451003450b1403482d858002d0704c0b1903a14205400c0041c0108900441c40c2c08a12404488418881c808401c070b4030441c440204248602c4003200d41c1034040d40c009000b00d0304002c030034481245440000e200b07a40c0c80ca0300c01c2c18a15404401031041c1400e020345907000c1410b01102560403c032080380850503a030b0400b80341500d00c0d900e4101c000041d0540414814500c107c806580b911118058006880c00c1c400c2000c4a08403090340ca00e208202584d8081e0b0a599625007011011984007806500000d80111050401041d1054041141e515000e0507480954050740f020840 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 679081834 1250 679080584 679080613
    0xc0a0504080714100503060d060c02010b060f03220b060105030a090b070c11010c0f0210032a031a2103160305031909080a0e0f060301120201080c040f052709 69
    0xd04d1001580e5081450440c94080c00050503607240500c0940881d80300c80301003812138400e500482c81e00c2e038010301c0c080e2a00380155540362b0b5600304440d00303c0c40e20304441c0c1c02a0803031030440c92001030a03070014030702c14548e03034003801150541c102400c3d15000035224084000022045040e03d40300722825540c1d00c02c14030850038001d440c1c20100d40e440341401070003800c0002088410240320100307170701030b039092a00e918841002c44c002e00703060400e10b2220744400300740e54640d00214030154000071742e5039050000144080d070800c801d2000d030703498030350103403c800c0019010700f900780701d86440c800d61400303030b82c141005007207804900243c16004500180000081013034000c1e00312031207d00010f24444c2040450180d60b0760030003a100d101110014410b503001a0400f95550500f8016070000240c030340c0c1c0e22540d6035a190a1a1640680e003240859240400140b800220000341d070116a524407507081000c0c540014051302000e000300000c40310030941c0401540314900d030001c40c00b409100c0700514000007517100 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 679083084 1250 679081834 679081849
    0x6140411041514060c120f071a06060d0507031e0b19030302211c0504060c03050610050d0207060e1c020304030308070302090102100c021605030a02090c0a0504080714 73
    0x1000030b907129858005000d4030b4050140c40b8030b244020303122035544a9840a40030718200c2d0259900c00740b5100041c1c44224441000c0c0640500b510031480084040380c800c1c014042000122052900035030207011601c0000b01c1a00300ca03401c11080d003800658071400c00c00000b20b03c245014144480e0b926845142c9003810160800001464044205610303982150f400945400d0801c1e030803186604400c41c1e50303040100010466001c00a804c0e407000c00100c2c40c1035a40003901c02200c0580f09185418003100340030b4000d00400d807040740001c00c0a110440c2480b0309558a8114030341151a030359080c0041d04c00990301d480f5012414160350020842c10b060180c0482000405842c1c203001c40d0401c0c0010800260081b0070740303030880d0f5581000358481c2507120041f407070402282a182203043c103107000225583e0f0045409168040c10361030702443c11340c8a42c10b0558030500150000d4000084100085811030030401410025480d45001c80c03030195119485840d040d400e0f08403110150440194000c039160954 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 679084334 1250 679083084 679083101
    0x1e021917010203243607031b14120a0209040b1c030c1e061406030c090408031003140705040c0c02010f080402030f12130e09190614041104 61
    0xa615502d8244a98034044051010201344101c0d11056401a0742d0741010030300801c1c40c40b0b00c0480044000c4c0c8228003421010a07601c03020f250045000c907659078828051900507a41d002d628006020950004803405030809041c4e121000041c8021185651961076450103804054001f603100e0056a041004030350740348842520500007840120252100394000c0007907075801d03013001e02c1c040f89075003400b00c1000300d81d5031241401008100202c04010f82c5502c0146162884060030089559810030f00d603841c222030501c1076200b02c80c5c4001400143c280300c01140d00225542d40090346603603a41d500c029003c0d02540346050b51f08500018460b5080c40d203d2030103501c01d103280c03220500000e0340002c2c00c030b000380c2000c0340c0030000c030341001074150b480070496506115141c60407100075040300e0314111701e145c0109990350107030300002c50001340900c02907810714051700042d0081e11a04c07078011303511030340d030960064200c42d240e80300c41c94024100030881d0160b1286001d64008595048000c4c20001180c0300349 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 679085584 1250 679084334 679084379
    0xf03070c050901050108040b060105160302030c071403100f090c08150a2009042703080a0603210909020304230604030207050111030c190302150f041e0219 68
    0x2c0010001a030313000102c02c1d005130b00000210425150500121007510614040341003403070782c64184504241d400401002100321520a964409803039449007903030060003d0119500da4441c1d410040041400d9024000c41d4121500005014020b40c0e14182c0b007000aa02100b5a41c0001483c003030b050911040c401d40c4003000680030401d081840108103420407001c0794244004d41c000ca0721011310789481d40701d00d06004109082d410300412a9032110f641240e05441140082c00901c00300300c502d00240202815a6800400301881c03c40c84000c81d1811102060840308004000c42d000920f02c0e8184000c5000364003480900810450301c1e070350140c40885628035484940c1c41201080003084c1e0202d6800c0076102c092034291310f18102000241d01d140668030900c0450b004142d07828142c61107034021400c0041c0310f902900c086000410110000701e01c22109500006030700d200040c005012010308000c1240300712061a000c40d0302d60046440350001010391170041100c00707020301c82d6143e130303500d91b405403900e0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 679086834 1250 679085584 679085599
    0x601060c08070803070509120f15040b011205150703050f06030a0309050405070c0606090b011710030b060a030b0f011406160b04080702060c0a020f042a110f03070c05 73
    0x80daa5100c049200380c20340a840b03402e0101c00f00b0301c1148298112082034400400c01d80041140554064880b011041155024400c1d0703203955820710f40000c4100d228035000305010106c0c1c0e01e8913182984500d001201118940224804600100d81d0050106d0140c0e06c80c0d0342c0001c3c1460000e201c00700ca00009049640311b9170000c00003c00096000c640c0c0d600b9902c00303072030200c1c8640b0b071101d054802d401e0f9070070010903150600101184070810b80e44501c54401e000d03a1040340074808002d550b04007542c161000e011140381600140042400d0810881d08040054000c8a1255481c4c81c0c103d00650266540032400079101d00400600c8040b020785002a801115228544401541081c040490301e00000b4075940188001800b4020560706a40d503054000e05140d40c0e840b00c40c0d9200ba110049080101d00c21581c42c030440c015818644a90120b40c0301ca1284080e00c04980f0f070101f04200407440e410805c004035104c500d07402040920202020082c240c009503200c00e0949490740c4109403541106026008 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 679088084 1250 679086834 679086857
    0x605090306070f0504173a05160b13051509190204020c0627010209060901031a1c0215090303031603061d041103010905060a241502060106 61
    0x340400c4068000b052410301c444035182c1440182c505001d143d10420f0080d0b2048010388840001165100388880813803900708401310003403220204028040704e4050924850a05c0c040303502c0c0984024501ea00d5040020002e02003107959804960504440307000c02c1864081c070070703030401c0000c0001c0050f80b060080405114649500103990343e0005503d0b0251401c8030389034000c25915254102c40000c0c000d0004c0c0e4400d0310b080384100c1c1c1300074030000c01310405010b8004600034122040c403e403204500000c00b036614120000c070045010741150341500c100002c10f28400c1a207551030000c25a548080c80c00c1c0701c00488404d004100505800f10042c40204004024801071a51301000300d070307441809000c0c25810320f021118124010b0815030090303c01c400f05410364501c4400080d4490348668405e810540c0c02840030801d042c2a905e07006402021588004080748183d011f030b4004510f81444100b450060600800c0d030f00b0305410071540910059480e4034000740105034140040c1c0c0c003400150a00d00a60079 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 679089334 1250 679088084 679088089
    0xf1b03061e05070c02090a1107170301180b010807030b0f030604030305090c040b0307060f12140a0f0b010c02270412110a030905040f0612060f0e0718050705070209040b0103060501060509 82
    0x1b072000706070148841e1b50f80098a050a00380058485058200042c052080380b0706680c3c01d0198420b01603d03e56090700c40e20300802c07201710300070040c5142041c0e4418046803144a41680988541d02c0d4075a400302114145c0001a21700300310862066000384e40c049038504002104506003040d2400d410301841c01e1a5076030b00c0b1030310009030f01401c80320a4034106408120200f0211001000d40750342040301c03400c091007000d100754a80000d41c0107640d10b160070000740c0b100032402e000300c5401030b1045021603580d078844c1d0090f10380000340e618051041e080c6000403800185c4e0701c45107484110307030460310104d141760000d01281d032001000c402890488000d1003400301544000c2c01e6422984112842951a485c2010032101c20f500200020101c3c1c030740307100c0080000e02c1c014014064012038065407615249038000c00304000981d1508841c441c60305100c40081c804075040213010f0091440c402d001e0700b00034440051f10303064070740da2040e0301a0f4400c048550651400380c06444060f40210200001800200d0055 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 679090584 1250 679089334 679089349
    0x2040f15170c101701050108012601021603020703140606030a121b08031b090d0f060b0d2406240e1009061403040f1b03061e05070c02 59
    0x158688116442416498403006180500c10705250707800006841c074803c6159007080d007030921800310920b2500e49a03251001110790180901c103e007540c0110b10b803006d0818203807490f00040b0071440303400540b80080070b40680d050858080700442c016400027108205102441d0480c64103c19840c01070041d03414440d0010796522076900f00039010001c0655034181c03060117103c0756440c6c006880c2000211365001d00300707007155400494407441c1d00c080c0c41d035400f5680da103030008890440000500701040700c40c0a840c1c40c000c07110706902c1280c0300c40d51180d405559540b074030420003100f031003100944130b046a0840724100c0501201041e15600c7e060410a0191107a82103400c0b9441020350007980c0301094000c01207a076030310103c100b603801917201d800e40045c0a03840310020056800d282c0300e04158040020b040340179440100c3d0050001400155682c0000741024a49541110032002a019040d2243c8802c022550103689604120484c41c5803406545000d024143d400401403c040e240342d400c94000c80c03110b = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 679091834 1250 679090584 679090589
    0x12070f061d031608060f1b0f070b0903040510080c07031d04062408010b0a440c120c0901020a140c0108090706020a06020a0e1003060302040f15 63
    0x38024401605048aa08520400d00103840181114006043c8a51125421406000e424828003440e4009048101065a103034040c0c052050004540850f15a0724400c5400c20031034000c030304d0800c102800c0072038802d040e983d028007819000343d40d44500d00702c02c101e42448400140c034244003002c800c0118841411066550060301801c0c0702c5401c0e211500030b2401075a1040d10309511526044c00491251065100c5030361840c0a08058040804007001c19a50f8030b00912070f0306003a40040126441d1548605030400710300782c8100d01c035003040075251504118060843c09440102560503c103020b00d0b0749071243c1e59000b00c03600441900d8000c1c54664114641c40040c1403000762600040c855610703134406c1195945141d002180741c808514282c0441c0c2d02c17402c2d012030a900244006001c140410800304840045582d150018040300d95145d0310302c1c2c0a500061036036010f0024a600c41002a102c0c0c0304141c10303082d51903600090f40c40c290710400003101d440c4000050804e10b84105586216a0f1580c0c2d00207 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 679093084 1250 679091834 679091837
    0x1415010c050d0c08070605040308040308100b03010b0c03070b1e0f090a031d0a0902040f0509060907031a060a020d020f0f07030201110109080f0c010b030a0c0909151a12070f06 77
    0x5100142840c04c0580f0a02c1c3c00200028030b8002003005041e80802e840740102d00c01e42d540b01e10707505c400c100a90880f000d40a6100584800c01c01007203e91605402020300d401c0110650782010800d0312100b0b4400400c45103400146000000205964103002403d588030b00002c41c400c1090411108481e903c1085c2c05d0005c0c2132010701d00300680d00c407107580e6281503827003401401048280e454440b0003010790014492040544503886010416103403444031148a134070081e00c2408160307541202140500300310503504904810940c81c44d44507880c2d40c0c00601d8400b203903400404d001c10316100000d140288102104000785c10211103409140d41c040b407501d04a0381c091904500621117506203d00400034084014002d000008013014080c6683c005040c0c0500034a000b00140e01751601416100c003416a002004902e004d07206111000859010803221405190b01442e030841104080c4c0417101c1920b00b94114202441e0003a22034588480340109210b0075030003a0a23641c0c036000c2104480f20aa004000 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 679094334 1250 679093084 679093097
    0xb090d1e0207030c060903140a050303060120030409240807051905060301060f0f0504050a030609050a060c0815190b090d0602040b0d27110607061415010c050d 70
    0x80d000e108202c000c01440e040207800359101e64858001c1c0414206200c07c658a5a042103401c001850101b0260f90180d04400a18650391b100e4004450345800c0c022035020241d020020540c07040400c10181010b4030414000040c030324106030142d550312100411444244c0200c1d0010311079144080f03550b100b110802d03180d24245100d011181000c0b45030b5504101e41040010000154150317108070703805500090740d290b00c2c600120041085903544203600034181c0117042507a042000a01945c41108154095025100c5000ca42d956000c10703141c61690f40c1d000110514140050b0380383c0118041070700e040031102c404800e031f0005260440301110388134035680358038041082d55254865000b1403d40c82d61042d0115680d9448512000e41900002849411603181402c0300c2250048110002680940d003810080700245a990b20b40522160005550b0444d07400c0c40980005000d03800303810040c142241061155250004804010350031040555041248010011003c0f8001103106c00344c030341c03492400780c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 679095584 1250 679094334 679094387
    0x9010809010e07030b060f04090f0c060203040f050d0f1a0a0c0203041413140a1b09121704090e0106030b0f0402060304060c090314031c0e1b0f040c020a0b090d 70
    0x1800d92203260650fa8006040c44089000c100400c1d07a094ac550748036501c800c0c0200d480c1d1134220f940380101d0181c0c0b92104c001c0c800c107103d40c3c034042d1a002c09092082d17802c8101f4903102c1d40d50444d51030488a9081044144600f481040d031141e024a141c40d9600d44000c40c102841d1030308048440500c82e282030300960503540603a501e581182c001032510b9041c103140704c0403810544090b4000b40000b500030703c8426480c103030b1707664021300c120071000440e4001070714046908803e4650203e2124000300401940d40104000036650302c2c4c6000d02c0466001707001c00003030340c00d02c0c50034032140c8168020076041c80f081c802010800140d50302010f0301d4005410070000512091140c9003960820907540001d00031048180000b44001c000000600102c242202c10034443d40c07100c10100c007611143c001441140e000525480c2c80400c925100390300e0b51100038138211000b900d09011904851180c0000e2005030000c04030002400721866956420556100042111200b40d540c0203040d0614036034001408015080170 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 679096834 1250 679095584 679095589
    0x1c0213090510030b1017030711090f04061a10021609110328020f09121219030207020402070506041211100507030f050a05180102070816020307080f0309010809010e07030b06 76
    0x881029007101b070030020600281e0302c050380d034a40011038101c03502c0080543c1c020312800c2400d400d42c040d0016410700300464032950380b903034080c085801052185030300c0e5180c070380e80e695619550074240c2c4019030040c00302030750204181003182003203400c2400e88bc0e040c440107000700c1108800300d903400f80070214503505841022051400e03e1100c40d0304005103600218241c5a50f004240007841508070807100f9041100341c00307aa03252a1214141c50a80c2104c0900c00e2080d0324141010f4507005000a1500611708880b6500017408c030b0b0440241034900d5400301e8200400c011241441b44507007100350610204602c86005c0c1c051303480c596014035800c060f4403000480c40260113030f04120a541c04000052185142c5080c0e094000d1100710342d20070a410b0711452035680382506108413050a03401c594003030702d00703181c0c01100100d01010020490b09841442c40000b00048103106038038130031003400e0241d41e9440e0464001058020060070300010703a494000300300580b160006403881126801005002690b850100 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 679098084 1250 679096834 679096861
    0x31204080a020f160e0105120d030e010b13090c08060903161106030a09020103060902071a04020612070f09140d0f0204180309091103040c0612021c0213090510030b 72
    0x100f40d0300c0340c4141031408881540c1d151204003992140c0c400c80328141c2e645c0003044003c281154003004650003c42c00108958844e4000e0307a4122120800401c40003030440c04220500d402c400110603555450150800300000407079580000c20360140100741e01e0034100e02540d124410301d000c6075140452440440c1c10000009181403000c0f50080000780c40386042403880c0040c1400c440101d00180c40c0000116950103a80300ba600c800740c02c6040b80200b02c000b5150102140b001500171399018000b0f00c074845000c06c418174610b00c070341c165a035032006d042d684040241041501c0d4001d00f64009104020140d0f6807a5041c000982a4000fa00c0407501444c07800440d006240400503090b03000505075081c8285a00400000111040d0180402c8000c9861840340b031203000c181c5d401806021140810403246100c0d0204406400014000500d010125807514401c4100d00d924482c6050300407840d42d51001d8134219802c001c181c080340911103841c2c0001d01482411660000500c03190200001c990158640007 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 679099334 1250 679098084 679098103
    0x1082e0308090a051e1c12050a020c0a05180a09020a0f03031206050f01050a020309090a051512030901050d090213091b0501020a0b1e070e040e031204080a02 69
    0x4444509040d100c0c145140c159218030b00150248228910002e00c80c20103e00c0849200c0d1040c8421006481c08000c01240ba040c1c1c40c0c038000314604040404001c41c80320300480c0b445c03c405848096840c00c00d460083d00300380d403c00080c0d100d0100da4504004a481e14824032007503a00080f03d1122030b650707071010701000703290340d01d0060340100b94020040707109004000e485050b00e0003030f1120740320540d405403140191244c6001d42908107501c5045104194040c0d805440302c800c40780141d0303003400d5900012400c01542200c444c0009501c501c1400543c0703c140c50702c4072a09100b510442c1828540c010b60642c0c85c460725001604001d000100c201040c034466201d80c510550003820030303035941d04202000c0b02030080c103003068800140f212080340d030303c80124031418119a0306801230f00e00110a0740301c48142681c02070000708400c84191104501d01000f44520303215132026100e807000c24808105000071126200001d0443d5407040043e0b0120030910000c45a12a610540311a03031141d0201c0d040b0b04025100c0c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 679100584 1250 679099334 679099411
    0x60e0703050706090816050103020a05070b0c190e01020703170412050f0706090810020f04080a03081f05010c0213020c030a0504080c011b061109060c0f07080703020108 74
    0x80012040000124101d0101c2d03007207948444c0d030607884d10300e000c0d100c035480c08141d412003415100810603075000e500544402c082e01d040c0a0b0400745940c69030418100c08a85402e40400d0009502c0c195501da801c10000c0e0300000d1902405a010ec00b00207940c5032014040078240103030b202038001404a407074040350b015110031640b9520b2120140b40042d512620055182c2082c0078ad201d000c601e0922400c200b0040f241098000d010708000541224025030080c40711084880080002150510042000a407642c1c4242d6840000380b50208640804500b4494102c50007050360740100842c1e0303800003401910f01e404403062448840211382d280020b21a4030000c4070b282c08045003004000b90054050002c03100b9440580d2541c182c40001102d807030010711450500011548240c201040d004d40c0710035141010108014030740001980050b40c65046044044510341c080390500b440341c40140040001402c5110042c0201402c2d540080c0c40610014041304035a81d0483c0e8003038421500d0b100000444209 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 679101834 1250 679100584 679100593
    0x6110408010c1101110f0307050c0a170c07090203090703081b15070908030a091403010e0327030604020a0b0f0d090b0a0510050a060e0f1005091507150207060e 70
    0xb52040504003404031010726042d0751030f0600b503a84000080d42103400c42c10004801074030315500c6070421744d581e42003004c1d00145440b60040d0360000980c03614103841001410f403e4207485007001041503162200d07a4210030f26045c014420300c1040180014201c0550350300402d02c03600c03603e1100040c0e08009040711122690b109810b0440c0c544031851a41d82c2c003801c866071328102440e840f20103480c0c0e43c2c45904511170004003462030410400c100d84100141d8200c0040011076051f510b00e402908d190443d80c0da8194080d14107020034034074185050004a40b0134141c0c0601518a401e0300061411036180c42481000c050000f004001a04241c048841c1c41e10051402c1106002d01e0a00d0800000115001403081c0e181034042180e0550280d9100200c420040010000606111045030048021300006822100c2c5c1414600250b8803440c1e03c40411840d9a02c0546404011042082a01c2208c0351030440007020803140010803001104000290014a8096905c05041c5080e800400030070101e56100c0c002c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 679103084 1250 679101834 679101851
    0x50708070206043b040210021e1b0406081002160c030308010303030e0a11011b0b0108060a1104080a1b0806091c090501120c020f030a1101061409040611040801 70
    0x102e41c01e0546181d0109180c0d0507035036404100914071001c404d40300c3c810140130540014014645000c03598804015032045d100003601f0351540d00d0211481e03281c0311603c0d8004031001200c807030040c140c0181e101011030301400340910b07014005864040c2d4000700c224050300010450142244810000740d840d52010411111740d83c2c07401c000303281e46002c1c04110700013420f0238040c10800c40700080482c46190050b000701c002800072001903410109524890800c611104a00f0300420b4019036a90b00030300f00303030014042c00e2415036890350441d55943d00c0448140420b100a00c000500081c0900c1c140d030340300500b00b240c0c48142001c82080340050f80845002e108803020403400380c6020848410340c01c00c0b10015540313448451019900b1100f14000c4da8001440381582c2e50305140d03182c100008012060060b10310b090014140c0a046905c451046408903240e10740f11050907000340318000051540c0c001002c140d030011300c00070b40d00c100d025101410301030316a004a1901500030044800604615008101c10342 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 679104334 1250 679103084 679103099
    0xb180a06110105130b070e0f0a23012c0d14030d1505010507061107020406031407081b120f0105010909150e03032208070309030b06040e0d05070807020604 68
    0x280380901ea0205508240104654180d52043c81c0d07151944844524480e41d55040221041c940d403000066201e0151080d40c0d060362240c41c410006400303c044100644903c1d13081e440c0d24070604250341410008480910a10b0031082c0130041c90160600300c0d41c00281c1c81030000501000d00d500383c05800350402c106003650b000d000100506400c203000307405000807141ea10420f00402d032184151800b0034010030a800c0092103d511202c2d030481c1e0550f035182000c6650700030404590103500b0448541d44070710f00e01448900104550f400038801e41008110b0952607401c1d00d03034005203038035207580554050340310098501800d0158204480c07944008004c1ca41e0364a0014000e00b201c1c0c20182e03844084119800c20032151030107640c00d5410180011071031603c40308000c854a030000b0282108480a10500200041c0d8103c001c0290038066540e2181c03060950130101d2000744041c0000341f04501e000803019054101049558141001d4203159440301000d0500350036074800c2c95002940f0090006011070440d = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 679105584 1250 679104334 679104347
    0x504050a0c02010b22090206120c0717041d060105071704061214180a082115031e19060606030e0a030504030210121d0c030d08010b180a06 61
    0x1101682d009010b00350208043c402d41030b08020b40c0c40c0c05038541402d092022682d641103860444d2001c2d0000345440c49203039000000b20f5043c0d0780308405281c00641c120a01440c0c268240000c212071000c50701d070624140c070840200b00d03035540310b04038079084c0400101580e001d41d040e150201c0e000742c0841c424410749016480a03510500680004c00d004400200d0b0a982a01c94038144445c4c0480814943d02e44440c150710319003c0035170380700c2c051082c00c1801c40000c80d400d01402a4009580c10780a00d89040d0482c4102d501c4010049404802000e0911800b43d500107000d000ca4000f0421a070042046222690308200c6014800e000c6140214052010403100f58410402c0710b01e913940070450742c4012800c0d240c40f9103840601500044060000340054903001030040c1c1d0403501070419011265403a0051000c0d034181810100007010f0a080c0c2080b207410902400040310012405130165035103d0002521046040c05407194982e004203004941c20040404081080d2000b450b140354140d5441004254 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 679106834 1250 679105584 679105601
    0x1303051e07062d0929030f101706060123090d02030c0a03030e1005090a03061e0c030905010b060301080d0305040f02030307080706060e070512091608072303071e0504050a 75
    0x408208003510440e2540f203170044003189212100c0300d469031311600200c0079071140251540380850300f00d840002d20080f071100d80f403016640403000f50619240070000505032006000801d80c3ca060082c0c60b8040117460401141c5a21104039142848100380b030011a1400e20f4800c401c5800c4039030400040241a04110034450444080b0751203841ca1040b828100c4a6014082c040307500038005920900005030250800769081e05207486945c84800c000c400350054a403508003c2d40441d0742d4400500a100c8c0a0061a02002060301c3c2c4602d154513100400da03540c3c0c0c510044d8410960342e20040b5003042012562000b040d03400a0480ea160301d44e900b07204036240d0140d0401c9805902c3d0590004800c483c0d0441c482c490704994a84900741070f940020b01080304002081c1c04505d0103496555201039480c5502e98020b40210310003803a1711401d0180c9000f0b501c3c941e140040c4400b103050318840c62a50300044207000d45000901e200840740c1c0940c590701e80d25055420043c2d04c0341c20903040000d03070b07031440c1d00c600e89 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 679108084 1250 679106834 679106849
    0x301170c0a03050705010c0813090b03160303080a02070813090b03150403020c122515050933120604181a18031303051e07062d09 57
    0x4100c4900e82004200c440c140b10040c620f40206204004c2e03036000b5141d40303003101d001e620a1894888000075000e00320041d034200c5070103d9994022007000d03081c1045454244132a4001a51483e82140c50260401500500c0d54000d00e400160142c200a481015a03060060f00081c415042c1d0303e5441c100701074220062100c1c001e1107440d904aa644030010f00d40750007960141c02424400842c00c0c1031090350003200840003040d01c25108103010400d0098041042944c0d890003643d4503505042140c9280c030951441001004014049140103582d2006101c40c404030106103413480310030022003443d52107070780c1c8681a920400400c002000200c01000d10b80b01e800100e500304480506030008044240c04c081c00504880c03420400703c0c000094800d0745d1070300004100745050b1000200310000f480c6038083e1003c850001000002042000b42c10800300310201d03101035041c900721981c00c03813003030352a5120300c240d0003000541c642040700d030100a02c0d0450003201901005d5100700b0810806040c014071881032a4 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 679109334 1250 679108084 679108093
    0x90c23030d0507110409051c09080106050307091503080f070c0e0f0f0709121a0a110f070204110d050601020c011b03142803050c0a0504050904031202030117 69
    0x859480d0101e40018868000d0300d80a00f803002a80f1a1303032500e6401080f0701d401a0303441e4040804108200300c0681040006400e00c5544040004000c06440e402d9005140b5a07060200601c540d50300414100e0555040c504d00003408941800d5074000000c0d2030f40702030b000d140300080131010848480000c00015002c1c0007001c080c00d65504034840044021502d128142142a0208101c0703041c985859070010711624141400f203407605c503412001da2900f9400c43c3c1c090b45148243e00c810300240c0c0b040b54803a0f610038040140ca1030311544941c06100c0c880504440c4c1c0000900041195901d500100082d51110101c03a1612200340790440201402ea6025025220300100c2c0c2c151584a01254000220711081c1c042c1d810340e09903400d4440c15504000c40e80d142070b00f88200c0000c950420040ea9452642c043c03c0007031003981c01070140458101134807074040140200a030140b0135401100700c800b02e42c025200507541c2d6495090460b15030103c903c0c0322030260f000000004141c8402b40303401c0c000000c13442c15207 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 679110584 1250 679109334 679109399
    0x1401140a0e040f060f0c02010f05011202061207030213060e03060a110910020a020303030c0712020309010c0809040f06091a040209030709091a09070f09140a050703090c 74
    0x1419058a10401d4480128000010002251125601480b610030600131a51141107164841540c0c0301e081008010b1390740e8189610494000c0c080c09004000040c2004001c42c400d8000c02c0c0180b007210745d00240d070301400c008240c07007510990446884840e85100210380549134140200a0420294501e00c030780700c0c5a000c03c484032254440c1e040001440c01445240101c0c40080c00550707450075030040e080d03000c1c080341d000160b01d09200030f520905d00d200409585407024601180507510110040c0c046603c20300400d030159030060700503060140c0185180b526455024005006420030005030107800c0e042c014000790800783c541000500303e14883c645442d40d1142400e1108a0081d0040c82360706511450307082105804c240c1c400704600d4010202001c82d02001c005090509905846000081e4050841005124212100080a0040c000090182e01c40c126481515190301624546525a072a404640e45030300070743c07101e0f402e541c0c00003030003081d640d948411500b010010003080d040034034602d081 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 679111834 1250 679110584 679110589
    0x2309010e060d09300f031e0203040602090a080601030314071110021501080a02130c02120f030411040c050d0c020c1509091003080301090209060d02040b03060f040e0d1809140114 78
    0x910941011303664980c15962035a500c11000b40100340c448519202d00c91603206421080ca000640c480e90051201507502c9440c0001e2240040042c2c0c032070f038629000400144002a445000c0301c03031010220b05115290b5030141815410b51000c2c00c1c00b1603200005406114102d5008104601c801100d180c40d00980c4c3c0e62200d0307454030741e500114001d42c01805200c154090310300960107144402c50910444840c0d1600c218000700d180d1010521041100000c4100700400c10520b5031215244401d0320148084040300001608500654403500750b0f072615142d0224240741b08001841c0d10250041401c00d03072800300c82c002c900552101001c0c4d8042c1000000142c150100c201c4110210303684959150b00c0c43c0c1c03804090380000d400154080d68024000c000301b42c851111400940050322050700354580e81d090110130040d4210480c0c11150065040012102d040000401c1d1070140340803078240383da031800e10b0040c188529000b6810042106181290070050100c46003842ca05a840c05205174503408041c004 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 679113084 1250 679111834 679111913
    0xc0201061a070c0803040320010c08030109090f02130e0618060117010615050a080a05160e0d0b01030303090203060a05011a0c0c09010e072309010e060d09 68
    0x651600d030420701e141c2a2010403208001c094040c0100c0100c1d2446444100450a541c8150700035200f81030035050039405200d030080080b00b22802402d0002c1e15110f16520f079110b5010501c603400910741c0c1c503410a070a2081c0300700c600910640c000c0c100020311038a01e8800b0020147e100142ca150310035140043d10b03011011080d584080c04640040c1401d030303c0c0c02c00580340c480780d6004054030b0755220703480054454143e01e14064029030356112142c5a0055080040480c10002c284d05038203400c05007401a1142010b62002034100f00d0320345840c0500e21324000c105683d15542c0d00a01690b80500000103055142d400701ca40c2c54030841c10740324103840e1940c6203403e98030b0a0041d4108411050103000540f00c2050042a0004a4600741d903600815040081c244c01c200b6800f0503070469010781040300c032561100038082c1080044a20b5a0300004407142844a0b0141032950343c14401800c02800b090703950042a990408103d03076050120f400c152a0400d8007824030324901f24003955a1001b41c41070f102c0e201 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 679114334 1250 679113084 679113089
    0x90c32040506010c0f0f12020a1a090a14030403060b06120708060d05010507120c02030a02030f07030309082808060319020103060b0a0915020d052b060312030c020106 73
    0x15248920009140200001400003910441c1030100886003000002c2c9188080f4002c01d025481154641c0401c0c184049800c81c2089a00b0440d000f080011001031031500f540480d07802030380c02e0b903817555892100301442d020003840c1c090400404440b039640e2040000008100b564800c6038180040500030041c000103014103030301d40508032580c000040c1c50b40d1150310740381e91120340102220040c186030f460f01e0b82100d4041c0c0710000040c04911451040300c545009517400c2800342d100551500301e2185c4029200d0040010100703000c40c001841c2c00a262007a040704d00e1140d040186a80e4890113041c08095517288207403601744442c110084800c1080c081c15a9610601000d0090006152040880a507a09003188124181651400c001c5000c5090030098440c0381116143d1245190a142c2a50080410600c01d042154441245032481d030b03522400740ca00c80c84a01d0702800c040030203600402c0c0321400c1046c8900c146440c21000100313220a00e00140091415524100403c402c5060203c1c00d844a50 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 679115584 1250 679114334 679114409
    0x4060b0a080a0524010b0d06050d030509030114010f1a09040e0706080f011a0c1e010b01120516050309010902130603020906091501210507050301150302041a0d0b04090c 74
    0x1031004000003807084c002440891f81c10b0350001400d58a440020b0f11620001e03c00b82c0020304049003c1199003024400c9d00607c0b102c0e40e900d5011989040394121042905004804804070002c40c90703041c44d0030390401d41d205800c0c002d10501001d40c0780045565a06058480c231070000307125a000c19125400d00d0041c6044e12104d640c0c40700c0c0f0078110100c8081b02e5002d01c1800407248104090900007943c880d02c510b880c01341200c004583c041440e03000419000400c154100042d00c0c000600245140c0d2481e403070400150b5080054580d03551084060042000d92006500110081c00c050b841c402a0360000c01624070032200c0302180d441b10700c180000058221000071401c90b0b84070b01401c10f9801a4212a098100100162181038503904d0000903240252540e03008104003100601c41c400c0038140f036800700d0303403d8507045061078a40400c2e0040f004550a60341c02e001e4000503220842c1206400100ca0810080c0c0203000440c010729084c007004a840c401c801c104400140f00700d5101000140501c082d0140 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 679116834 1250 679115584 679115653
    0x4180303240501120203070c0c080c03010b120607180f0e01150e0a05150c030c030c06070203160209041401050f0105030d051309110909070509090f160804060b0a080a05 74
    0x640243d0001b544080d10700c02c00d1010300c61103071000490440c01c900107000d40201809907214844113040c2550b100c0c41c2200d1107064620321801000200068540d0300403034504e41805803400428495280e103800750024a250740464001150303041d03240302c0150485496660b0040400c07070b104407c07a420030914800d250704c000660000c1120b03240c0b80d00c15030400a201c0350b0307051901d0184980c0c5880c507480440c0010890300045007400c020302080c0314581d8440e00500156242441d801c070b2100000003c41d10091040001d003003ca4140030300100d2012185407d04003c01403030030300486101d2a84401d00c0f40d24424410003211700d8a8605c6207042d100c001148243c0c40316000d04000d141030181001a5444899840c02d1000c010150b40f0446100c0c001c5003e62030780c41e62030441c0414090900c00c01442c2c036580c20090020710401180a880f801e15920440c600710010780c0f141c0c0b81450142a01c1c80a0941c006006000442c821201003406195103201c0c40c221000c96000205035144201541c1c030040705802d0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 679118084 1250 679116834 679116857
    0x610030206070b100f290403080d0c020a0b010905040507080f030f090f04020703090905010504151206062607080105010b03270102070b0a051e0c0904180303240501 72
    0x200003c41c0e07400c0440301500000d0a9119062014845851b0b804a10010080c0007050b28002d6511500103140c09010b01041c502821070f21281d0042c070a8081083c101e0380c0d40e00030440140d00c244422541c0980c000a50f4009503074401403000505400d6505403664042c651001444c0100050b184c2010407040b0059130070b01000101d84682c60300179070340d99038203d03030420041c0c4031980d10f0344001c0c04002d2098441503440d90403c03c084d01214016000507018500d08000c89940d41207000c82402200c541014003645003445140060113443c0c039902c41090b0000c40210146400c60000352402080d6040003110700d246d5450383c103682620700078030a4420004080001c503121100d2580c12b50301074034180d81500003c4414512007822a4000300c0709030380a00042047c000703074040341d00030b482d0400c4406100c611103448001351300741884009042c103400c5900010707640c80c05440707d42106a00e202c003580040078050041c14040d0243c5040b810f4500c190303580085900c10718505003820800d58038181e403000509c03135 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 679119334 1250 679118084 679118093
    0x8030a020d0f0b1f050712030522050a120509090a06060f020102090f0f03030415090609080606010e010503060d0c1401030605101b0303020408010e07170729040815010305061003020607 81
    0x141c4c25291020008204541000700e2117007800d002c850016680c0006285c582884541c1c0d094000c848004221400c0900100100c0d10005050082c1c0350000503444040d015214140c52a00ca4180070542151048040019500f2381d03501640c22950705480d0310340789450b801c800701d080384a2030101c00d900914034042d00c000c600700040280200c4102408507407a00b40c542ca40907040c40000820080041c40984043c0480d0303074044000700041c180d0100520060510100280001000450721810084040001601940e409140000f5207400ca60880d80003501d40480c40078111440195901107800c0110003d02d0341407094501100c0500c60f40c4030283c1a03880d04a0380707100c20309108281c0070580c085c8000b05d1030351020312458603100b214038010480140741a010000202c00201c200e4803942140d80204007041c203044450100348504004540ca450407007007e4121401550008501c0d0b108080390b110aa981200c10b850680c1e000380211542a40c1e01e07002c1c0700041300755000082d04030906015010001d07 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 679120584 1250 679119334 679119379
    0x4050a0909110d0606050a1502030a030f02040f0605030a0e0723040605150304030f020f0c04093e0603190903020f1c141905070501060308030a020d0f0b 67
    0x4030b00c40d03440c500d1240040d400003414100012026600656100c5007007080b407502d1503001c00200b207400541a180101c040c0d020f034803400342221034005d064a03941e611071415020f5048402500880c07400e07002480e110000240590002c83d00d03664986d00c0c2884000038040001418400c40d1107201d40c1c031451802404207a0b903045001411550819240c0c000032606555100010000180c0c107100d860b100c3c58a0306000782419401550041550001410742c0032580002c02c0705c074501c01007590041058890751070080b00c2c000640005e00040e14186625010f981c651884602d8150a004200c42d103070030b059070401055100980c1c066000c503040401e0310707000f05c050b60001c40380d0b68020b006032019113585040803401c04103c00e90940c080701e80c00c042000401c1d0810708024884404c1c00080e03040541780700582541c100001c82c203d00740721021800108200003500b000000d185e002c3e040507180c6c00c0034841500a9040000305076445410f180b10f8a0003415035100d85011224003d140500b550701c40701650605 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 679121834 1250 679120584 679120601
    0x70b04120c0c030303021c1514130e0706020709020a120506130615021501050f2112090a2c09070503061905070503010b07120903021201091704050a09 66
    0x1c0c0401001d81d1808034000e2841d1000950081d280580e48981d28601da4003030603c0740c511070079030f01e16014100c400000701002c000c041c0c8a80b4600d00c1400151500040c0309000c9080111094a0908042c00e01c401d03408200d801c00c40b034140d0201c4540980b210306181c1a8000e00e0a603800085c4500e9003903080f19420f070041600b103400901140e07400c259010f16241503c0c0e15400030110100c541c001c075107007181d0400074550038110b03e0403203104d15414000043c01d4003074a102002d00c5100c215994000440d030358030f0f6404441601a007155910108058030454540041103050f00c1034100038800113518104105480b80300e01d0300440d00450300840c02c481c10384601c0c0640010203900c07030000c000c43c00d0340f01080554090442d8881c42c4c0740402c007560201303003030743c01c020030742010800180010803010040078250780c0031582c022040b50a43c21503a20840d079441a9500c00f84d4403010802e02000980410740c4a152890300682403055519a0f0401c2c45c0d00512861041c0d03500300d090790804018006030340c2d000d03492 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 679123084 1250 679121834 679121837
    0x30f070c1a04060903120605090a0e0f160504050f0c070201120612030c020306060109121103010b0604031506060912030503090a06021201080615010f1110020d061703070b0412 77
    0x2800428208580c05024101d0702114495501c488000a040d040749103146c040c010b1034424040c4504080104003c9840980718011264503001040c98203881071004a00024400044030701540f01c445844203103000910406006500e8040031450026200003550b1003266080d004901d44036a075401140c6680c8048007010005e44d551402145011070000000a0103000c4e40c4c80701003c040078010075080c914045c00c0241800b800c20010880300f030901a400070419041710080320555143c1d80403a024207580d08146a0000e40040c02100b008501d001c080c502c0140340500308145521003a00350b408480c24040c421151004c034203803900181c8160002c44d07010040c2020340340c100301156118401c0e0b802c144205402d11104100601c001030302041280d40c020740c1c680d03421940907012000070b44070300d6945034560208030080c154800c4202d020010348030085a05401156113000c450041c80041125000d150796041c0340c071300700300c0817980000103070b850103500400ba07450030f078407960303250410025020031410 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 679124334 1250 679123084 679123103
    0x161e0c020a090c020d120501030209010b0d0f020708030a0c170c180a0b070201080f010605030c0903030903101b0c053d0c270303031802060705010b09010803030f070c 73
    0x141c07010950150f82009a071640041c1010405400d000c1e059840f10801c560b402450b203401000943e607080304450455000506096442251210380d10150200c1e0b10a9a10640009580300030440b00500a5100e00119401003100040380306085640d80129400d0511054035a00810160000080108140e2000a03480180c00103001e02041007990903610001d03c460b004503015040d541c002513400c0c0d00035020074460a01d9814260003030014000640407c9866102242d5500c2c281c070204100d9516200050440d40042c5a02c0c0ea140e0140c101400c100c0380c0700302c00303022040e4803500402c00440c00d25446000f81613540c00800d4811030301480030281228a540810309555203190340640518450b0f03502d8808030b01ca040e0107001602400c0411500081c918031000c1029008000089540c140c981c5481c0100c0c0030450300d41c40784070140e040080a94052000107856007049030550050141c1c04007501e041005aa03280384894513030100315091804081d00000046a5911800d03040000c24803550403107 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 679125584 1250 679124334 679124339
    0x10f030e01180503090306100b3f0a0b01020f060a0509010b0604030503190c020d020f030102130905100816091e02040303110120181305040506161e0c020a 68
    0x200300e81c2c00da400c002e440c40c1d0030008080c852410140101d55203d0480c3d00640390061415030b160403144070346039290b0701c5071a05d00705015006c280300718281001c440a002c204543c40786294202c00c0c135402503403103440742450006518803550010a5414901020001400d0542e46114000020b418020200205556518194a6075544660291014500078002035843da090a88400094003852440c1000c0c08803044c00440145d0750b01ca070036080154181c0b006164607180d0030101e80a0b003da18240340c18415488030102c4c00314650341c0600d106203450030b02e008440340d075401c006031154540070641d400c224070380500384003000d1550403140700c140d6201ca28100c5203c40c821070710104e0f08241c0080700002d10340a0780329803047c000d0091030f00801d43c65100e100c41000408065920748903080c416400c0c1009000c090a095a42c0c40c1c0c80c0c4003121229100b88510b00c5c0c00d240041c1c940c48110b8155207480550110714a02922510300d0546480d10490b82c110b480100083c140c40a03a505030f0203e91040901c03401 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 679126834 1250 679125584 679125611
    0x4050a02060a18050f090a021e0f130f0b220e07080609093c0106060314070504030807170d06170730020316060f090e06010f030e01 58
    0x1000b0040c116924a2030614103000360044030038442d0300180c4981c0001030302c070340c803a9500d02100780c006100c0c59005954104443c103a0028003020071940126103000305d00c007010910300304000c102002c442e1555914003a1030306403c1401d1800c902490307004203420310000303080c14a044d03804441403051144083ca099a95600c50380303440c5040390300c10700261490060220500301074a4a0f5005030f2200702a0003105500e900d4040391510010811003007041200d003801c003d10200310040510a0208001d00c41a91100c0f00503014024004048440e02450350024012610800c295810ba0760320000c40d41c5407803a00d07112071000210040c0241d10b006410081134030844c0040c406e00c0c00410140310140903d8002001d02d50518880e6404640c43c2401206250f60707078404448084140e540900c1481502130550000c00c0ca0310346110492034107601070480205400da00a140308400c84050b60300c114400386c4500b0300c080e00b48410b80e901c034041f6901f400c0454025020760800c50380100114000030b6600000d41c030 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 679128084 1250 679126834 679126837
    0x10306140106031419090f0602071205030121030e060310050f03010902090126030414040b010914010f0324090b0103050402030703030c03020102070b16031a0604050904050a0206 78
    0x104448859494031000101150030003018018038181c10100031210700310f00121242980100185121101c14500c83c105502560001140c0c58101000c2602c004c3c242c03400400a5010740c4d41500c40403203511700c00704802d2003081280c1c180e0b110040201c5490950204480303200b1540c0c4000c07410301164030300780c80590b1100805148100c000c517a103a0301e614540820700240c10505120180640d0400c030208025071078440a850455031341c0c00e900702102400042c0c22560112010310030f90710303020018000401c034a805d071000900140440f01003010b00e038110300640b4050400d20801100c26003481c0d403600703030b0360161030300d004030300c1c014140807ca04030302e5580110b4281e00c80d20b500d5403a04c0558018091640c0c06d22035608100381c00c2c01c2c200a039080c950006039540c155807000404008070080e084003018801c0d01035900180c0d00c200c5005036420304900018400c0030405004000900c1d0810310444000c403005580d0101d00013400c05441c0500740720070301140038801441511140301d0442d1900044c0c907000e0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 679129334 1250 679128084 679128089
    0x1020d02070f0b0f0c070b0c04080a03020d020c09100312120c03021804020c070e13060203071d030a030f0e06040b030103060203010f0e040302100209010314072106080714030307060501 81
    0x212400da00342c005140021600c0030152030410401802d00070080b4034441c24003160100f640103095043c9030b503694501c00046110b5a0004181409286400c0081503000a4507048100c0e5580030742d141c2c00d910106000b9a40d034102d924007819030813450b0030808904480d00084100a182ca001452032079044000000d41c0d40d414040f60000b640003540264804406140806658080341d09500e81402c40000c41c0e5521010300030840002c103800041003274512141440c0d60416440301c01903449107032098028204040384c0c801c10114810115955400345408140360481d16456242c507160401c04803400c960800c40001303080c0d003101c1c0401012850f6a1030138040c43c02184a01000340e81c80d81006400305c2043e03650340c000766411810000b03101c002074000c40c5501d4040701403100103072990511801200030780300c1914044074069076481801403041d44040c45144c00303440f034a000e9014180c1103843d03c04690184c850031145030003114090050291042500e0402e2400500309d03130804005440d40c0040711802e9 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 679130584 1250 679129334 679129343
    0xa11030a23160f0c0c031212110306040b0103022110080a0606061412150f0d0c060206091b0d03020109080415120c0c02010e240c1c0f0302030901020d0207 68
    0x50703258219540c0d22055503a0f000d40d144c601004114443e03500c518031200d607400010240003e80c49905205489a032850310306c140e501c40103200d03100c1c8460700303103206030300c20355407540601c1c09c000000d007965000e4002c84070b0003078081c040701b0700c0d802c403100c0880040200a800214603004007140040d43c2e0404110489009000388030001d00c682c60a88049d240412010414103001c005001600801b50201404c3c0d600000e0251004851184e03800021285490700882c503a01c05d80c5500720a0a00c035500000c40207807291502100d50584403455000da640300d4941c2414441c8805010081c0e550400320198200d0b603209000100f031a1040b540c5210480d000303a000728080050515074400300b240c0c800917540403100c0d840d9042006e0405600018020444240040e0600c040326a0401c0d881c0c031100c0000001e1400c980b0040070b0111a444802c1e200e900000d03100c44648035004105151710b0080302d90403612003683e154061094401e01068010390001016042155400d0000f48040d0300f00d40006c26074580718 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 679131834 1250 679130584 679130611
    0x902120f010b190b0304030e131b1205162003071407062105071e0507020f06090117040524180601151b0204110405090a11030a23 57
    0x41d6030a100783e8900402080410000c00d207000c1007001c071943c0483e60803581629000a2207103450002c034901d94050a500784215242c10b101080e14180d06940501c804151b17910b000c0005140541242a104181c420310507411000840b007880034021140c1030b1036000c07070100c0c0c0c10b4980110f401003825900004400d48001204407200001100b00f03100a0014100c03034100280d8580c0c5600d4504885d07030b801d50929030460303034860105000300e0003002024490b000d0301306a088071403100500144542c0003100201e005000300081c0c80b14620f00b034002c1d6110076034180e48001e1000035441c105002c0b458040c106441c94090b03895000f0b0011030554a507204100c00718180c10aa050507920280c5800720040c40031501d400042c010f004010b000e40080401c5410f41c602000240e2b0551094a026040310600a50251418080c0200e00407071601510803a10200c5180c0d0840d0396000405050380d0355807011100300502000000e50300c0004c1e41c040c010010441300c00104400080b802800e118100740c4e10001d10080 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 679133084 1250 679131834 679131851
    0xd060b19020d020303100311060d05040309080f0a0206030a02070c080f010c110105091e15091b0d1101080408040b0a022d15070512040602070c0603110d0902120f01 72
    0x10100308444400c540743c4019881c501c2c000402003004852404001c04203480e16502503415503400044e0789484404140400c103a0410b0f2401410a5030305100c1d84000d800b415130000740340030000c2412070b21640c02400f001d18568400341c881d8000d6201002c01c49050023080f00110b00303074800f080151951149039000040d1308c0000741c000391103030320241074407211a0f06041c10400803280201d00b440200007000d41015504445d40081d606101001c3c041074500d00c410001c00c000d81e58001003c0d02d1a083c0c01000c13035541074185042c031403060804400540800e154418198407541300f056000e5016010300289401c0584455178000503501841445005900102c1509480e4060420384c2c40d02640940321004440a25000700c1d40761a112080340c103507070b100040001c0c01d41c1c0c000c804944100e020480060702d245400c2c03038844000d400c10701c41502e40b440051000302c1c1090003807088800ca16002406c0c0c906002c03050b110603025002c40304003280c10101e105031711600050200b010981c185501000400c1410 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 679134334 1250 679133084 679133087
    0x1c02120f03370c030b2d04020301060f080702011d1011091305130b04150e0102041a13081f1b08040209090703050303040f2a09020d060b19 61
    0x100700203500021518200b0392945a0208050180e445000d0807804603840c503005200394020040f4000c03003074000140040103481d44800768140b103402e000e144011650ba06080c004d0104900003405501d02140b12100060314050050040340c1d480520340c4004500880c1d107802c403d501d00408240c01e070059108503100c00c009075160048480000340c0610300780c28202d080c0c0004540c00018036030140341540d24000f1903480041059400c00b121340000301003480d41024980740c1021080082d4192039607280001c0503048101c1030080320101d401c0c290558400c02031586034070f0001d6018810119460701459000591800c040c8030110b02c4034036508101d400020480c8000d02a60300c61801902c82c8511195003c00e03058000d510260000c2c1c040e1240e40d20303980c401400a01d046141d802c00742035480003008210030403183c80040c032200c6114510f1001d00c8003414200864006402d07080c400c11000040c0280001d01e211750203050950041000070510a5070b40022069542c000d408101c1030040e10804080349a = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 679135584 1250 679134334 679134361
    0x80708030f060d0c09091502210708060a151101060b0901030c0305090a0803090a14010c09121a0712110d060f0b031909080a02060603011b021c02120f03 67
    0x20b8802d40d10302d032800c4416962644810502d014104030350390399400000c00d0007803814145040f10081c40c421561844100440300214181c1c0e40c04041270011900041c044a204800e000c1c0500702c090000e000761070400b80034041c000d0b59443c80c1010002070121544111000b400344100400c010b01e801960740340d0410004007510103100724042814140b80920014000c00500c40418a801c9090641c0707a031540c0ca01d140c01d103400d185008d00400e030380d810104101a019480305458880c41c1e02c9405030725584041a85400440350405015080c06c0000c2c071001d04080703104954800d0351440c20343c40001d103d5030300d507003201c13682c20760340743c504001140415200c61180318100103014204502c2e03041c2441d29603031403032901c4014188001071400e80403c03800e003030240d04058000e982c00000d0f030741c40e034008400080d543d40003114214842d43c204684888030b202000360f07118011041d83e018100d43c11205402210100f604c1c08103604507c01c80c00580180c0d01260054071000c12040e490300d6480c20f0802c140c2126 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 679136690 1106 679135584 679135591
    0xc03030901020a03062114031e1c05220305040302040606031b080c07020603090c0306040807060e0c18040204150b07051c091a07080708030f 62
    0xc810190040e0044800d2550100032007546c600703400510150b4440500348036050300d58040c0104041150321154079400c5800c0b246050790382c660b00f000380c0204540710601000042201d640510b09450002200c28880900348540e05001c000740106188601040c10102000004041058001d0302a5402182c001b00100b201694500000d005050390915a844c90000050682002406941841e006513140000d06091100382e9080c042507074000b40000d0020b1185645858480e07070f0030041c2a00c6107200f03450154590b6102d16140c03060341d00c0300740d114607941c02c00701e007426064413407581034090008141d480341035544990001c503006090842c9441041f1b0b40100003c0f4012500600912007140314004072100d013450b0011400d48a2417004180002510318082040070301d00c03208030750038007400c5072310042d143c08960b0f40d072244150301c510011100c606001c0104100303030030307050034289c2e0 = true := by decide +kernel

theorem cover : BRFrame.Cov 678956834 679136690 := by
  have h0 := BRFrame.cov_init 678956834
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678956834 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678956834 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678956834 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678956834 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678956834 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678956834 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678956834 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678956834 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678956834 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678956834 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678956834 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678956834 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678956834 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678956834 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678956834 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678956834 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678956834 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678956834 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678956834 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678956834 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678956834 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678956834 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678956834 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678956834 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678956834 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678956834 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678956834 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678956834 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678956834 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678956834 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678956834 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678956834 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678956834 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678956834 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678956834 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678956834 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678956834 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678956834 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678956834 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678956834 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678956834 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678956834 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678956834 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678956834 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678956834 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678956834 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678956834 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678956834 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678956834 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678956834 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678956834 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678956834 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678956834 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678956834 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678956834 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678956834 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678956834 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678956834 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678956834 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678956834 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678956834 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678956834 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678956834 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678956834 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678956834 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678956834 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678956834 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678956834 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678956834 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678956834 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678956834 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678956834 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678956834 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678956834 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678956834 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678956834 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678956834 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678956834 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678956834 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678956834 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678956834 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678956834 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678956834 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678956834 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678956834 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678956834 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678956834 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678956834 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678956834 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678956834 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678956834 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678956834 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678956834 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678956834 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678956834 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678956834 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678956834 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678956834 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678956834 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678956834 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678956834 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678956834 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678956834 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678956834 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678956834 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678956834 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678956834 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678956834 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678956834 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678956834 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678956834 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678956834 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678956834 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678956834 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678956834 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678956834 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678956834 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678956834 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678956834 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678956834 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678956834 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678956834 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678956834 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678956834 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678956834 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678956834 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678956834 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678956834 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678956834 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678956834 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678956834 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678956834 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678956834 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678956834 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678956834 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678956834 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678956834 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678956834 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678956834 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678956834 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678956834 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678956834 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678956834 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678956834 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 678956834 ≤ n) (h2 : n < 679136690) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
