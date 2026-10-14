-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3159
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:50:00.349284+00:00
-- url     : https://prove2.me/submissions/b9a1d5ac-3176-4aa1-a931-e10e1a2e5f40

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 567985611 ≤ n < 568165467 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 567986861 1250 567985611 567985633
    0x2c0f0906100f090b0304060c020607050703050405010c020a1716060c26040f03050f0106090605060910030b060a0e1011060403051e0c03071401050702070314010209090c190c08041502 80
    0x1101c0c1e0406d4806843e42940c410002000c590100040b0703400000c107042440c00c03c0320558000700a48141e0040504002c0e06d18040021529003111003800b03041c241a03900c07581e02c00700d450079554450718020700e256440d04400c0040c440e40540d4040e0f4400d5040388586041090b0380d40400340000c458007030f00755545401c000005a030004807102d007010b5403184002c0c00c1910b6200300e4a600b50f5846400c008141490220304125a540e00e20403581c0c41c040948841c40c0101007040250010601f00101d25000000060041031180d4416015412281b00b2241d40e14101000c14007200c62800c2510f620071716130f03c8000460003180c001d84c0540415941e900c0c030180290b240741c02070549504000411441c940c804a50301081000421802440c070900100800072454020002551110303070b4800500025441c01445ea008a800c0d0112280324402504842641c1000300003c0308552200700d05908400d1000e030b212004030b109010742d01c01150072101c19410075042160f22040480e145c0030040c25445113081030a = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 567988111 1250 567986861 567986879
    0x40e0f060f0702060f160f03060b0a090620030306150d09030f2007140420030103031103040803030f060d0f030203130905090318012c0f0906100f09 65
    0x5441510307240e260a8403414401c4020b407030200080c0c9140040030140d020480c680b100381402c030201540e01e1a254000c400c0075042a40100031640000d4003003280041e2641085800030703000021110140d641ea400b0400e039440300c441d0b02d002c1c5082103146400c10000329805150414418a40004407904039180c6202801c004048510400e812004104415a402c1c00550046e003086000002c41e1070b05000c1e0010416004d480f1034150180402c41c60b10070403541d685480b6688952152840c1c0700a00c00c4210a090500666400174031085001401c030005c04034900201206480490300114000c3d82513885014403210381c000002c01c5240c11140008640c004034242e180460802c1e130094024664900784840e10b69280390403608000d47c20b50a090030b1003482c000000071524902032036940c442da680342c010b0040f03c442403e22030b04015603504048011003029046812030304024112140c0140c00030070802c3c0400b80000b258590b600041c203d18090402d40101c5050582c003900c1e14003108201d440d50609 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 567989361 1250 567988111 567988123
    0x2120f0c2b030c0806010c03080c09130f0b010504121707080304151506140307030e0609010b010e01030903020a1401020f070b09010b0910060f02070b03090f0106051905040e0f 77
    0x180107011014074040100310780503c01c4000c3d55081d071030080c241e403400000282c420b0450000040802c52120b00242443d60300801791000320f903000b058110044101c0c102840a01000084074140528100d2a100998012000c0b0350840781c0486954400b40342c02e03180c42c00051078541034a0001081000b442c4001500c410066100f00e10943c0c0d21590312001480b5002201c140380000056070b03102d1007040c400705800840e9a00c59440300003819070317a982c038524120041d00b0b609080d0713016413045d681480f010a0064010745031102003a03988107003040c0039000440545080c0e80c006000346e0040176044010400e4900c20707400032841c20780003615198024010a00c01e40c0400e80035603000b05020140600c05c7d0b0203005410550204849003496400c00c2c0c285107940c04aa4800e131000d02100c49140350459009206000c020548022003980b285400034030079490b0244001c11918551819101040310b00e0481400c25207805003c0702c581e4000c4c208000c0c00010040049c60401501c54141d83d114410780800c00 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 567990611 1250 567989361 567989413
    0x20a06020706050f0a0608030909040204021306210924060806010603091a0709180902040903120f060810110706021809130807021e1503150102120f0c 66
    0x80010b03913241c0b030309000c0c41c0c4d004040e002903407140c185036003007044840c00000d030740104100b219051044d898030b2000a00034440d003040c0342c80202000b900040ca50b41c024850b41f22102c101d029081d2240301c3c2d460440c0446d00071200041c081042108408500402400c18410039801c0c1500041d91030b8549031024902002640504006501c40301100d0400031018103100b11452880e00d038680e40c0c00e04100240041c5124028441a4802c554401d100850160084002e65402400400c030080c03203401c00403c03c0640508101c1d4039820025121866981441804201c8401d00060281e5a408243e00700140100079004035184c44188600030100341d52384000c040284003200d413214240d21341c2d010302c10b00c401c00074580c81986905c0c819220203d50010708070f4988541c11611203013642440100703280030855000029801010100c80e041444109000540c05140120030b0645044031034001240e0b900310b0b980007000350302000d0042c40c9500e83c1060182009500c1c04050750842d4002c400c5c861031400302011 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 567991861 1250 567990611 567990623
    0x9091a0c0306030d02070806010b0f1606020a08090a03080411061e040305011803021b060c010905061510091206110315011d0609091b070507050a0e0105031c020a060207 74
    0x4148001e529013000480340c013202d640003800c8850325184000d5201c960510800c6c1d010310001540300c040c501520112002d03101070140c0c3c0d001c0200113040660094000d1100300c1c0c003042c0d0300800b03da030320100001c0b420192503256a4119141e92150303503030300d00b4907048080d081d00b01c0300900000481d03c1d4601e104001c04080d100034130303440b03515606000303080d00e142e0f00c0c1c1000014010368142c0d0110b940803c1c0d45142d01a0701602d01c440490702800b2454074450081c50380495460301110008000c00410b000f40506116a402c0007840001d904018002a11888003004a40c0d8280c0811450b9a03140780000317414000c0d0000104171880c2d941050b019441128800e907a581501f410075031a60704041034030343c15081c80109030410f2a50a003c62900d1082d207040c00d1007108020001042c030351900749040d080c00c4040f640c02c4d855220b02d02d4035540d500900e02480344034920207100400c002030f030414554120b80f80140148a1503041d61807200b894030605040c1821405640c050f9030201d01c0e540010509030344518 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 567993111 1250 567991861 567991867
    0x2090402010e01021002180a05101409030c0406080105040c0806161419110609011406130609020a030e010e030a0203030f1302060a0801081c050a121e02031909080409091a0c 76
    0x3002c020042380c541d00050721660301c175a08080d006070f00540460201c0e00001c1c80941d900801c1002911300b03581090220303481820b04001044400c0b040d00f06034002c03441002c400245035100d11045840b80f03011244582401a042500700030181b180a41011003408011311900d00482d2138005500c080c20101401d0110f24030b108840203038801000b14030350007180000208568800d2905104ca5104060800391250840265074145c00300c03940d000d0001001942000c558640c1d1002c0050301406040721186600d510742041c0741c21341039000c4100c810034003465001d9441d581d14207440100d4000060704c6441d00c0d900300300b1940010303214940185022111600e91803140c3d032500318070518000032080ca1700030007802d4070178401c22150404290f41d00e5200702d00740a01c0d0440c9240c21040140b010b22144510f0030007440e03100319000b106500450180b0000c1c0c00c1000181007030440c606c1510001180103041c8003041008000c0383c0700540c001d1541c944030b051200540c203581c0340c40032542d5078162140800c4403000 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 567994361 1250 567993111 567993157
    0xc010603120f08130f032705100c020f0405190608101d0604020907030f0f09030801060801180f110d0b03010b010e091f08030406090306050604060302090402010e01021002 75
    0x803000307080d0708082910f00038031103141070000062180510000202500003046400042602640030040003034149689042d0038000403c406640203068402c0f00e000b81d142070508044503100c0c003a42140240c0180c4440c2c5040f5030790040c08000c04004015800030b40c480c0d07042d4900014503004010060801900030310030003240c0d50112007124400030000600441079400001821400700c2d03500d5101e038040341d200103641e40d1400306a014241c4042403885052600030086081c410300c1e80f1680c40940603545490440e80c85240a5074118401c0c040d1800b4482c2403080300032032500640140c2c117101c10100000c00c4407124201d12980743d411048080300c1c035a442e407101400a080900c6048100c075401d1a196680030302e16004504801400b9001504160204032600071095114060030020586002282e0361a65a03a4000b0003000c040d0108491450800c0007045044c40c25000318000d683e0004c21104d469226a401518000e2041da809415405039004100301c4084a1020b001031100c601c01d4001100300c4 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 567995611 1250 567994361 567994367
    0x503070515061807020c09040305130303050c010c09061b03021609050603010e030906090f0f0a0303020708010e01050403090b0a3f0e0304030b090312010b0d0b03010b01050f0901050c01060312 84
    0x1440030120800354443e002c01140b80c0d4005010400c000b001d030740d121215141c03418101c03080d208401502c10302c21001d000000030942d100e03000746007a01c40c0c00002c100300391084808a0b00000b083c031a84001071361700c0c503050901d012041c040c50540b91003030048900109c81c039000d030003141d003007588031403544ca940d0001c100c00c1d420280594031070059800b025506d02039402c0005815801284d44d070f0360140007040b000c2c800d15210500010718901006118040c01591391a0080d41e034840303070207040060750824042002c4000140038990040d42d240c1c80303c0950310300309076891106401c842162410408501d6101412201c006035558854560721000c901400952044014101c0b8419031900d1183ca414480000300c003002c410349040d00c0c1c0c451404180c0d615205e500c42d16501840c403000400c2803100c400001c2c0c003c4804020504001300d54002d00085c00300038109400c88254418541c01300d00104280c450031503c0030004c001c0003205060040c03c00030080491030840311281c20813100f40b031004d000c500c81c0ba50 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 567996861 1250 567995611 567995629
    0x8072c03010c080105012708030c0a02011b020d0f0305090907110c0a03080d0e03071e06060602060f0a0e0709020f0a032f09010c0b071e0201110313050307051506 71
    0x2c1508003039916514000c002405425441160001415840c10b0180244075007451040108440004c40c3d803140d03400e50070b20751580e003004c104902080c4106010101118080100d0185c10380041091958645130749555441c0c03480442c049003049030421007a01a40c0d20406e006000d015141c3d42c0c40d850010704812a440d0143c0039600a00c1026031110400008003100101c03841c020380c00501040c1246410150351940c0a4054000c02c0c00c104031101100800790604001c4880e40a60030602651350340d60820703603c0b44015662002081001c0f4000740900707179039400c0760302c012001c0400c603402c0541d28410383c0100c0c1c210b6100f0701a000b50020784c03401d049916000304464040c00e10b050302e042044031005d400059a5510420440310404102c000300c070381c02903400801c41504401070781e0491a00440042280c1d03000040e418124080004600c65103105200d407846502c0841401881e54407007158000900d840b03c8000c035041d00c010418800080c605120054181035100031803265414580d00f0491808 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 567998111 1250 567996861 567996881
    0x10810061a09060c0303130506060108040308040f02010e030d090e0a02090102190507120812091207110f0a08031309090f060221010f090f0203070f08072c0301 70
    0x6400c0040601c1828060030341e101205041c60103041d540d801070000300d0020700613603c6001d42400044100145150f4201e10500030720711074002d032091079030b07507074015030300c0316010398000d000185214000303000500f400e03282000c52801410103025000700b0f0300002e89441202010700001807100c0c14100013001c00405d8071500000400c1c029400c062032000001e546c0d041581d1903070587d03803182c0302110500400303001c040098010103c00c44035403011418a58140c3c0c2c0310074060702151400c280058130080020650000030040f00815078030380761039511a001c0000000c082c0d250320040450601034260746c0d244a0074020038540c0c01a540b141040c400b207900c0a203041d8007802405051200d0311000444400c01c1c14156a0f01010040c1c80d580c50440e4a10101982c41081e0411544a00081820041c894088084400c40442882030a0140300590306a010603a40880444d035484e0320400000e000e068056801541460700b00c2004c0035440e602c00392a00e80454000400752003000950b0107040030b0044171044 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 567999361 1250 567998111 567998143
    0x14010e0d03020604030c0c1203030606081605040b0d06050603040506040c0e0615030c0d060e10092a1209061a0d0b0c09030a02040e030d200403020609130905060108 72
    0x5020907140a5103407000100010b01304402404c9841c1000140700040001d40f84a000310001c291091030058001d01241c0143d40c0807899820018822424029241c2d49041060340c0c1d4a091038030f4100140c80c0e41e044002d024880a896074001326003512414082c44c416401140104400d00302802d1130602c0c20001d811621500500e101008541d4580401c140500c000100596980c0c1ea00c9180701070070750052074034211505003030010009040c1c4034002c00500030807502d405900341179518610481103840745152134420340b41941a410144011013108800c118103424444ca0402100030600110703001244103d0340a6070743c803100d041003444003221510703861003660811943c58840d103034000040001821501d0700c0c14002200302c0c103914284003921007240e01030014001c0c180303c076144035200e40114400c03100c080d152520300714607a07507504054003030200890200b601d098150b03020701805500042d00140c1102341c07030210104041c514800c294089000d0b0002c0e0040d9410030003001d0a0402060341c00c014 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 568000611 1250 567999361 567999379
    0xb01150203030405030a0f030e0d080907060f020c1002010902130c120b0d060b0a1505040801110712030b010314160201150f260d09090b01080708041b0f14010e 70
    0x560000125011403c03039080492661f40180800c40c050891a40c01741e503079005e002c24045082d42c011003071502038121a8241d031009500c0c0d403411140344070340300203070001039100259142c0d950501d050048403269292002081401060700441d8500b040b084454041e15a074a0407000341550000c095601080025030a0217200b240b0317000200311b940e1011000d014507940f41c0d007040b142d03507a260070080140520200d0f03a0319411036401c0230b001c68100e0f00c10540154284035003d20700c2d0140f02e0844004e00d620050074029149101c204900604142010700c0c1070581c0c5400e4200034981c41e00c50140315400d0000c098803000103410f0001d00b52540002469040c103c1c0d034400344450080511405c0c241c410302d080d4010082d105d40705404206450301c1850340b03140651090000e0a03a44145c000088c0c41d4040001e102c081148001150030010481d4a02c00141c4254040360014290014409980703c0a46c0c81010b959150303205440000702c039611003002e144800f201d079400780d608050b4001c0115030807a06a10 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 568001861 1250 568000611 568000613
    0xc080c0303071a1306050c040e100e1602030408030f072a0501050a14030f0f1b160f02090a0609061208032205070303020303040c21080f04030b040b011502030304 71
    0x80040c5a00040035243c0103e0000140c030824180070f076408443e08550184900e09084e0071905c0300303030b02c1401482d508500000008a004035050240d074101c6940041002c1c80c0e540700841d0030b180c1d6420f200d40078214042000000352500c01040a011901c03041d00754195900c5092620380240710007484490610458401e40c2c0000c98030410031981212028201240da40c00c0f41e00040380d0300309480000702e601e20004001d001401c030300345014034403a80b0110500c1c11b00d512102400d00601c225039030008041c64040141106d0610624050380c141441905545400c01c415030010b69072000c1103903040034180d55030404205110040c05042d000b030190003501d0300d45c00c850fa00c0e4014540300081c0000d00800c03000c1d00303000243e2280c03113090b0780c12604007058640060b241d00d0001d450745e00969003910303a01980500411103d00b491318400c1c10164481e504c0040000c035179242c0d0210b8010183c01c01c540074003030000101060030000000d1007030344903162405e115810815016803a4074121a07035001c42d031003801004 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 568003111 1250 568001861 568001873
    0xa08030907260d0509031f09030e0603040c03030f0507051c02010c03090503090f01050909010f030210050c06073009060f060b0a051303020d03020a0b2508090c09040c080c030307 78
    0x183c0454145482c503503410000c2c1c00300e80b034407603240b4540f82401c100c0f0300c0c03054244401d40d101c071115a20954441405082e04410000d0034041902c010303060b900210000c00c0000e00520180d00003d081c0d040c110b01745503803515118140396514a01c0a45940f42003409203c1c00c1e82881903421220703560030100950b0540d0307101d281d03803400b0350882d4900a0707203100e1100c0c0050307000b0802d40b501080c00602c507031282e607164403120504050b24402280208444120200007500030415564036842c00070007803049954108040719107840d05143d450360b10101c0c06115004090f440c614403042c82020b1800304283d40d00386801c20494600580110400303142c0783e414000c2a43c00740032182c546416141003600d401c40056035850500c440d0f0b100039400700910400004241c0c02252100459018020140084e0f41d0101d0421a080c526010030104034030110107120a2409043c0d601e420202c2c0d40c0c115000a0300d050045502d180041d90300361510024181d0030006403000f001402c2810005a000d10f051500541d202 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 568004361 1250 568003111 568003123
    0x40b07050c0325060903090906060503160f03111809010524030c131d090727090606080708060109060e130206091503060a05040509030304060903020a0803090726 71
    0xe4940b80c1e80f140200e800c3d542c0004428076220380010007040907100600c3c01030055501849101c034007a0170160000380460148054a200b0390703039500c0b908071420b10702c40126810000c9110071010306940d9074071108a09803400c09054001e0410900b5041e0219a908101c61440141d1005114070010100c00180580141c180000369805060381c517200e031591203001e015400f03820f0020361007400210001601c0f04c9032100721440c80d08140000d01194880c2c1501c2903c4100038084d6002c40408a00c4d589000c0590041641301188010700c00100c299007507481d035054803500d034400c0b00745902045041c0040c200900c85070b80107041c0e84004000d45450454200d40035000101b400000421301c8001100b59111101241c0d0303034640c024407420b130034000c0d081c0c1e91070150401d60390680a51881c1c10b0114075400c1034401c050040705003000035400d40d5219503a0780040c3c00000811811809074001c8200015241800b03140691143e0010305111401c0451072440c0d00658511000d14400b0305003103244842c400b04031 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 568005611 1250 568004361 568004377
    0x101b170c07140f0f01050105041107020901030b060a180c0f0906080712060e1003030906170103200d14060f060f15091306080610420503040b07050c03 66
    0x51802031075080c01d143c01c1101490342003040e801040b800b0113024106512403810303200304540c104044900308a038800b49004000000350003c1c1c02c07100600118442c41849130b8403c2000b000341d0b800c0358442c0100c555601c034a03030300000c2841d03d031040c0403c40794201000c3d02c201591450034010052074100d0003405910003402d00810b2040200c0f46504a000c0d68000314081d0141214144040c20001001030900c00c01d440300f5400a40d444001141041c0711341e24034030000707079110020304060342152100032816481000035003084400003e8082541ca13509000050240100d40c03124070712010582d03490400c41c0c000d06515510891a04101e400d0790303642e035a6001c8076001d803019201070a0300c555410300361040303400c1c040c1e01c03a00403500d502203c2202e8214505440360032f42600e0450312810100a082d04a501031203005580000690217007005020914202101c0007440d501218491360080b4103081e04104141d001400000401003407056580325203400442514141c0e1400c000980210385901030409 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 568006861 1250 568005611 568005623
    0xb0304020f0a080a0b070203040f0b0d230406060b070305030106050a09090515010314060a03120203120c120f010614071b090c170105130b0102101b170c07 68
    0x20506545880055040303a6001038002a01c0c1a10303080721540c0d40400f20003c81300030507442c00188140780301005480444031818011403426007001c44c0000b003070f004140291002070b40c4030040c04100c0c240f0111078100201d8030f41980ca0a05180c00c090003510101c0d04681580c6500300100ba001075400003c0324115005450002e0f00d0714960602120404840d40c803145445040c0014000100602c41000d07150b88401d8030104075141c1044a42031403000304482d01c5500c40c403c0d40080020500006404400ca85c01e48160303481e1810050b5903a041c820150b4440135881360110f103110030540c00d40703191504500440703200160b66141c02402000c88038854920f42a0b0940801d0240800c8641c560041da10b9400780900c404054480d40c03840b0080144803490300010702071640b18030703c134000c102c2c4c403d05a40c0098040d40141441d03015540c0540708100074681140709440e1400c107007500901c41c0c1f482c2403907034200d003040348011640b00501c079240d005940054106040d05000d40581c0e40e10450f55800c2d4061 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 568008111 1250 568006861 568006867
    0x1b080309090609070c050f06070e01080108070b0714030f040906170c1507060e0f010624030207110603330a09090f12050301030c0e01083f070b1f0b 65
    0x25070417180011500c0006041344036007492011050400311300940b04d421969218001090000011a002c0c0820312400f402c03a04644014080b0064100040500501528180100000305042d903403640e8000c103e040110f01e0007080030b1145000ba40100c000409041032500079101400d608203488a0f2100d0900c2d06caa0507618907401d40d404110140d0b4251780d001007042041c85040251281c41c0d4030050300b014885d52a1a401064542c6480307407141040080c07020000161500d403005400030350204406807810f100e84024180a40ea4420065105e90800000c0101601d000c500d51140803461001c8844003005c0301c400c203200c54462030f400c1411540c1e2800301003161807d40c10040030b451020744000c6c0a0701040001840d50503080320056040f64460f50074800c0305aa141040241c2d5031080c041c044198004c5a800d0001c0054062072a203030100401080c424400d4507911301c4481c4050000200c0c4950740810010107200d500300c0348503805041d0305864034000706100d04100e00f1130300d140a031a41203c0c000c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 568009361 1250 568008111 568008121
    0x1003150515040218041817130e0403120c02030a0f0c0c09020403201518041e14100b070201080901060b1b0d111c0212071b080309090609 60
    0x40050140100c0c1e0280003150b80302c501c0d104071810030350b040d401030b4040c906002d50102401c0e5084070b10042160001621590740d0041e1046c0d45560b48185101d5605100c0c8840204030009010036003802544039485205100784203c8071001650300d9921510f09642081c03140c044d100b500018403280c1c050461801c3e030084240f40c03070503d02e0505540c01c00c10145201040100c100440d610084148040000c0700c0c68101c100c0c9420080000c010313003c903102807001440406040c1e9900954901c2603080204041440b2400300d41120030240f0001014004589811568090800044500750405d0301341180c8400d66042040d0440c252048a074003c1c10404080c0004400442c20751202c2d010748210b18030aa900c0c2c26007000012900660600c01e6858000d5101083c1e2460040c0b01200851415501500d4031507503558400080c85640084102507001c0d00d2100a282c4062a004041c0c41e44a61103861a0f03c03800901040010165084034046500401041c41690f903400d61159201004446000d81c6a0b14 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 568010611 1250 568009361 568009381
    0x19030201060e0a090c081f05040f140c19120b0c190c020a09021201090f0902150a08160c060519090c0302040c09030c05060a050c0d020105010e10031505 67
    0x24a42c42288000d10b40350500c5140700c0c182d08030711441805a000341e5401502d452906844030040c40403818541800340780d07048440180e0f04401e0703100303006190520244066460741c3e0807c4019070503000458110007100310540c509424500212071548808899940c20003800f4041c0102c0395078041d0003100c006d0002025000314004607100741c0c0c0101c40600c1060b010903070241c030342c0341c0c0d00e40c049101d01c8040c070001c6980282c52090340c00186900606411503460861240002d201d000110158a5203a003240380c051703121980028440c0c642210340540c0e4105008004010003405040b96413200c0505135581081c0d03038400c0406040390380041c00042c050303e603080703124640c030780d00144c0701c1d41c44d800c2c03070741d914140400da4604408076402500c05102121010b01d084964071420f000080c0a4144140203000318106040540003a455508000b03280a905481051804406068440050b03442d40014485607142029507034120340c80148801d003045c156a070f0440424908291020000d40e50310028480b514 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 568011861 1250 568010611 568010621
    0x12403051222080c030d08072001150b270127180e0d03060b041e09020712020709020f03060409020f0405010906060813030906050a09051507031d010219030201 70
    0x82d05034014180603648690380c54072200c00680ca240b09010354071705030b030450340141c1039507214460a82c4d41c02c0c201070714072000b00c2c103060360019165529907030b9010040f4000702242e610000391448021403901e8440b0640707420f180040a0310314406516080c22a900242d802074000c40c5070707401810184080d440403510b082003181c00e40e8004078404c030325004c0c82511030440d903012480d100800d0059030041d41501c801038050780d00d40c0c13161b02c0c80b12000304400c0001004401c103001c4032558110b003c800007a84c07140a402039030042c150aa0301c401800010001c4d81d80c0410000004000e140800e504080700d800c0003410741d000041040b40280c1d1a48071040455492032000b030b0076808020406c200c00c0d612034583c0030003062103001c2c0e0008580d00002141420510368060b284aa40c195940d003191030401004580f07a804c0504518107006480e20f002c10607a90f9141d1500100614091590700c0c0c981a080c010f090001e45010a030b0000306020000e080c036640401e031120b0b802045600c402800c1c11a24080380106 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 568013111 1250 568011861 568011907
    0x6030912120613140c07060b03010c030b09011a0d020a05270f0d05060c0c100f05071d100f1106010e0702151501030902011e020124030512 61
    0x10400110880e03401d40c401c0caa640103070340039209070b41c1ca5009605464110b80342c2019100c03486075020005440a8540e100410b03096104401c0071a0240440000c2170079030354104800701c00b00380c0358401c9c01c4003420201c18150042c0b0120160f074684c0d16a400c6911114800c0700c20035081d898002a49804040c011011121a03071040c1c5024019801d0b074068008090180d040102c0c82881819250007a5251040e40030003195000790113081b507622204c020700120f610142d05505540a408001c000500103446100c1c0109602e00000c107140c5004903000b4680c80424071070006d100070910414000d51202601945500c49134100203203000302c541070941d40000c10b280b82030014421640080b0b0281c900e48400c0b030055126408445040805014500f45001c01322003c11941c010454004059031080d00208900750060514881545d00020b582c559201d840b2107007000344c0e460725000b41c10480e51800300e03003800484142180206045640301c503100d1082d02c0390020302140100f10229014000101e400324a = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 568014361 1250 568013111 568013143
    0x30c09030b070c060b040218130603021309030905040207050d030b190b0c0c01020c030a060b0613090b090c1e030c090319120207030c0302010c140102030a0b0301180201080402060309 80
    0x1c0d24040030010503000c0c02c40021a42c031814aa460191820079000b0354040c003031340258000d8041a0602407200754852003030306d02c0001741c03140400070150305c030f5512031141e5900c03800000c5121303100d904010303000e8150340e40810300032441084000086000850000711410040c50003041c079600d4040021680049240100816220423400144d00c0c00382d940184030040350030303041c5c1b03001c40c64031401a42c85034500c011464040e040301591200150301c5500c003007252030000703104900700303403902901e201940301c9034020040099456041d14000e1800c000080d40c8951850115480c1c40015240003c0034840d2110002c02020040081407403400701600f0f480310b0350030290441d00c6d4140c1030714156030b40c07481186003512810a100102e144140c40803034420280c1360070900b400700749460b41d4011180c3c03051031101500e0390400003010408159003800118020801410003003551562101010300311141d6504002d0514610021321f80183d810594090380035030110391417902ca07511809110708000c119542d150320 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 568015611 1250 568014361 568014383
    0x10030213060f080c150304260d020723060103052806020d2424120501030b06010e0d050601060503190e15010e250c020a080d0f090f06030c0903 63
    0x80c030200000c0040c013100c0308468134551440000000d01c510301c0103480152200000c00341c400114054101290080c412051640c3d1800b45111160006c0f600038801c12900c4041d2840ca03000b6251190310084540410034001e000f4652542c1c1d20161f68610b1122103601c1d502c0c4800a00d500d010500c00c4256043d034000c00d0666a84418104200043c0021545044017040450702500d088440a2150082d100f060359210340020200844108100c00b110160b010040d0202c01810b110f0524010305009510030031011001d03007080000580250a8604100e000b020007000c01001b195000071100e045a8a40c2001540c07a1101c1c001d240640f10340100140a05003441901e240b18540000c00d07103e200c10407000c0444503621014428825141914203070f803031300b0303003101030404900031646130b14182001070618844216143c1d000c26081c84032a40012050341140f4019521141c0003102e602c102c40c21490030620203400e020000f0b0074494540034040404d9510341d442030b1000c0c041c04540c40990703002882070359 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 568016861 1250 568015611 568015619
    0x2010617010204030c0b03040c2907050606120309131116030207080c0105070807110a05040e0708120405030703150f1e0b01030606120509011b110601060810030213060f 74
    0x1002c1e6129110841d0341402044000030f929804805483c010703584510035010603460003e82051030f4002c203540070010710507400c84405143c1c60300300030440301b4071400142409103002010001c7c88c101420301c2040310340081110041c1640d4001e1081704900344c55100013500c440c94001c1c82c149006440e00303628034a00741e00c840414035400082c1c000448211038202d03004d480300d60004403030302e00070314034000c0803c1018094076000451380100b51200b020f0180200c1851659100054180c0709003c408404035000f46400b031160b40340501c10b4030a01c01c40000e14500e8949031002207a55004c0511001d0203500708080b01c1900c580035500091b603103411401e800e21103001494071b00c10040403400d01c50210703503141c0080c518480d4000d0160200300c0b29291100300800040e184020701602c80242600c8895594009050a0035242c4140c40d0030124180d440b80d240c2481c05420074a400380603008141409008000c10085200009060055036816141540b603076416135888009080d15070002d41c15403580080c081 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 568018111 1250 568016861 568016863
    0x13021602041811010915231b060a0b030604020907020111070b1906080d030f060e01080a020a090212180a021f030c080c0304171207030209040b0103290102010617 71
    0x4030020b0040c503030b04902001ca80019210020f492152103141d0b134851216000b010301503544140098860880201f0100c400443d801e81d41d4000d400c00c0c400344203c98010407428104000c860b60000c0c20b010104400212703100001e40d540b00061001b88140807044c0010b0b00d01c0d200790001902040c07c00111a101e10181c0703810710001c07800300c80012a0004424018a144c0294061802200d00d20400340c01d2500040300e040f80035201048141c001540c840b1400036020058101d10f0f030017042104050b00c44041e1510400c4014140d40e8420708180c0d0060090100d203400c41440240c104040100b40c205d00e51040300801d04101c01140080d600c400d011960b01c11400800c43c4071034801e849541d0030042c5040150080c2d4441074103440c078800d014005d000003030004080b581052600c0c42c0c0b401c40c2500300a8a460054034461044950300f0019401181e54004c0741807500070301e20001c509003001d002c9508042450404c029491803540d00d261110340c5e581496074002e41c8640c024042d50f03541400490740d40710b01c2e2 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 568019361 1250 568018111 568018151
    0x30403061b080702010c08040615030203030c0330012601020711030f0d0219020d14030721050d0b040b06220801090201080f0901150602160b091302160204 68
    0x807401007448440003c1c02c491041c4290300304120141c655038907946441d19900020700603c2040e400e1034003a040c1c04405607038100041d1502d000b40780000d55440118403000c80c55070914803c030f0703681c170359074159079045150210301850b0540d41c00710b0b045a0411407145040c020b900700d50b10030a2655200040100c14480c940d0b00c3c407071100c0820f4013100c0054400c14061951121100702410058008140b80c0141c018403080c4082440e0004020311680c101540392440c40500078418200c45500005041040000c00060402d46041031028144121038503080503010f0310401030988001c5a0311030301003201d5655035006512210b000380c442503c0341203080b1000303840c500741150302402018003107000138011014015000030f6581a0b455404988070510002030b40c0310007920301c00f41552141103c0074065422800200201110ba0061480c088216842c000c514443e03000711190b42d004010802c0c0584403035004021400c14040c0059a56002c90b00e1101d424000c40030096005003003029405030040c0078180 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 568020611 1250 568019361 568019411
    0xc03090a060c06201b030c010e0607020c180a05060111031306090b0915070c0302100504051f020303010b0708070501140f0a051b090d170d0e030c0703060e03040306 72
    0x41044404030441d2944040c066606440c404200300300b0107100300c0c03180078445da01c0348458040702e08001400001030f082d00c0200f109604030b6070001080040b4582c1c10080030142da0002e40e030b9440300d40454032801440060061001070f040303489a006c2941a44280d015441004160064030f49401c404500c060321840c00380700311070020300e01030b40c08264070240e0b4048410707101d030060250f00e24108811480000e60006070007134a11600800300040580c84d090001e4400c0d82c41a9aa1a40c4908010030406c00c803030f44203414039515503104003a911440e000403c61703040d902d12038480d9817034605520b021041c0e803142900080c80c40d400c001c00032824000c08816140140c4501e0030400c1c07141c2e25901d0410444108440c140800d40030300d1811458001040002d00c0c2c004009083c0c3da52502e00340d2620694856881c0094403582800940340740611014490003404822503006149072229440e80d25699040a00018001c1d99403441040341920081040700c004590207881404179540070324490042d4015000 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 568021861 1250 568020611 568020623
    0x50f0601081605030118020f060d180b16090303110a14030a030e030c030d0f060302091311010e060306090c1b0d0305010b0a0c1407120f120c05030a050c03090a060c 72
    0x22810345011b0050081c041c8800443c0b9606000301d808008441220940b2950400c00801c445480100c8074060958280b00f20f100780590907882e41340040c00608000c2503007640004030501d6600950344a00c10b40c08403501840d00d0002d0460b03464003d0b0600b460003400030804011102001103108000c0085d20030480360f501c080003a02e146880180d00c03445201704040e0303d50420014201c07000c80541c444460541942c030001600c40d160b602054211038141c509606800c0c60b544440200100e44900d494490320a180503080d200110000c01d00707a000291485104098410008801a40318415142e0040850f2000c5020014186440740c4841d1401c9000000a080c5800829090b00c054101e40b03054102e80d0320007140d080c0c240c4440c070101d60400658010ba00417000009010303000c0800071001c040c064400d0004184261400401175010400c410007800001c0750041d01295011099a94001050a14507910340020040c01c3c00c0d8421401c0340d0b9401041035401164203988030001d003001c240706903 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 568023111 1250 568021861 568021903
    0xd030506221d120d020f0d06081605030c0a030f02040e12040801061401090603020a020a0b01090f0609060b03160201200d1404020a090908070602041215090203060f04050f060108 78
    0x40c0410340c03115064001006800810405800813020741d1340248020207804c2070f868244426080040306503101d5a00c507900e543d200b6150090460352195170880182400c80060208250207000303c0d100381003030f03c006030205000d0300c40300e4255140c1d82c2011a200c3c025100741c1da203103a002c040003109a005030141c44003540c40c190022806010412101d003100005848a001051800b00100c001e50321551400c402c50041421402c00150034a0750035029201c41038012a80d05076996900b4211011540861405030421108000500080d0701f200d80115a00094149413003007240d0a9024240840d40140e02607401c500c8101070450702e42c050700385500032403030504c100400d50070005007401341624042c0d4080024201044640c40d83da02c40c1d210303541b003841070500b00051398644d40120380080d0320941c001e05031440c0b40c000304407075000c8183c0040c0c0f402404004003405034011a0342c0b60002000508039041304000709061110401140c1104a103202c1241d40d03e68407182090f8407403428406240c01030a290b = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 568024361 1250 568023111 568023161
    0x80405060f040b0411180f01090e070b0703081806040302010f140630030f0c0105010f060804060f110c010b0a060f120c050c0a0f021806030d03050622 66
    0x700e86681d015580080c00b080b8281c480c0e40700d07a04041c4548010981c0102c0c10800401c0340c84841c032440b03210b0224004405400e62600c103c0e201941d640e1000311a007a0410041031040300460016a1100c5070103192905c03c41d541c201500e02c032002c803440c82c02e41d9072040e18104010544d054014860444054409000d036110409185101b018103482c4294071884140c990004024040d4030b0360041020250711440000c18150300ea401d5501240d80f1a00310180081d141440110901896004040c8000c03000455403800b00300404051b000707000109040d0b00c940090a04c1d90150b00030003880c2a13404a0a0754400b0b000e042c507402040148000740c001e504c4203800242e82805080002043c503100e840b00d042e907620003260000108800c01034881484028040c110b2003141c1040305191152182c540c0580744041801004404034142445080b01d10a5004000c401c2d100814205600480d0341004202901c45030001008040301c0810701c4c1d01c640300006440017040d103a40054860300307600310440081c0c41d56 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 568025611 1250 568024361 568024381
    0xe031519110d05040c15080610020c09190212010b03041b141c080406021f05010b0a0f090b0d0204050a0e04020a031e0501050a0b0306060f1e01170708040506 69
    0x1c807030a040c200080501c107260381e101494020a90191143c0170b1005503503201c8510084800f5501c944000040500003088414280f416401241c04541c0c00185200903d1500288048000900b1224000b10a118402d2060b003580c040c0d83c12607500e1080d9460755038442c0c0b44019660400c5130b041da41c020380e07880c150346542d10b80c500c00029510044440c803400b0740c0075020302c2514800e0062404902c6207892414011071840c5000e00040c041d075901804045a080340d030340364402e40c2094403a2145142c1001080508911011180498038906100f0078060110301d05440d604005d44c0802c0c03d900d000203410960507120350040080d2101207460300707800da444e0115480c4545044800075000004a1010b10100d40d5010041c008144044107a00c2d084002d981c846080d6182a83c51928064603040c030300c801c914090050f070b5030100050b80c031612a10031410002d100400c030304005019140c42100c2c20b03903480e44694507106110b03500302441c00950914100007001200d00b101d003515640280c02c00301d544199 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 568026861 1250 568025611 568025621
    0xc0127300503030604111c050403021b10081f090b01111f090203031c0b090c030402010801090c020a02040204150929250302150a060b040e06010e031519 67
    0xd0031100039420b650303c0d401800001c005626000340c1c1240700b41f09400300c007020600312030030301d5070000c0300031800741000d182c0645801070700c1c640b0401a84200c40314540c191504104e0012440b4285042031080d01e41c91440320444203544528a4141c11380c150105030030307007143c011f102074400a9030350894034107400c800305840306070342c2200110b40014942c1c085013245d03441d0410889940000c003601d141c505c5003000c514041c08410058038031940c40d0102e06a2524041ca0240e90240206003114918502580000c254031014050984069500c2c00c081070518401c0198070000750340504110b40e52525540c03000000d801c04031040000440110002c203804450440b014030700002000704184030714036007550014a411010905810300004d4a022403001700855070385070064001c6d0050200a210b0b10038600781e00720000d0201a0b1141042030070001010170b00200e804031507007900482940e45504c40101d400c4012500803030742c14480c1c0d0320741011200503005007d02440707807210030100081003040c6540941d0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 568028111 1250 568026861 568026863
    0x903111e060115030b0d14010507030c0804020108220b040506060604030213050402060f1b0705010206070906030902061e03151008131113091505090c012730 69
    0x14100c80010043c486000d03000e00c140740c0c0b441c02e002c608443e000001c03450b883c0c41d60206035002070041102d156040400c0c41840e411220701d180030701241c04031410140c0311440240c0000e04204502002650f040181c1181c144480c0450601a1641d505400e0001e230310300341501d095419000c0d0001045440c13a151f8212803c1782d03409000b054503a01490380d404024407001380141d03041002002059594080d500c005d1030700646000900d0503050300420128905901a00720f14155070005c0180b00400381c000b203204088524074580070540c940f462010800c0c901406840c40d2841e440e0703513580001c4280d40d201a5100e034100084005094507020b00700030b045083c9484041c0400c90740000725200b2200c41c0a00004240a0b070110720071840c0c01c0000c507441101640300201c02d5640d80c090401001003100e03408240309a114020300050403e1a06142c98a692038851410700004510010a0101e0680d07c0710910398401c54482d9019500c000b106080700c5910a03071164001c0c80020311a8800c0c40f680324091071 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 568029361 1250 568028111 568028113
    0x1006030b010e07030b090a0c0318150e0c0d05060103020102121204030503090a0203100b0a0e090709200307080114010c030905090c07080c070311061903051503010903111e 75
    0x10341d1901d0003442e041c41d00500346008140e01c81c3c030034100603110965294014010610300240240e0140b1000f01202c0792140d1201d00b0030401c0b003007440880c006001880049035407a0000402c07d5021712020303c0c05e00c0401e49540c10038408840d0b4401d04c40c010030002d0480b4002e0b02640d040740c1001001c2c0340c0702e10640081c404009000c40c0420046032050b806580e010302e041049402c0c1c2500d070380020b8039101a4000494030300e521070346c0341c075618106005440f008248461200f00c06082a201c4151a910203000e4412207a50352016141c076207562180a840e0300078021030003075507410f0080c0001d000b86006d010743c450341074240070300404035445140034241040d010394841807134909120402108480191031099540c4042c004040890b0106006040c0444414002e1100c03900e545003602940c07140c0702d4080c1c0b05450610684000b109201030404040d92503181c006003d5840c90505944030780380c055400e42662810050408140d00b080e403407040e84041e6411507103804074001b032220f12006488110300340303 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 568030611 1250 568029361 568029383
    0x2030103020301051e0f1806091c09080312040204091a09060105010509010806040b03030d021305030601060f020d05031902040303110616021f09060c09150801030206040b070f080c0a0302100603 85
    0x810315034150507c1d044803090601140a00c0708030700306031504100f5589400342d5084808000b41780c02c428040b41844d01c0075410010003143c0b41c00b982e030341c0b24040c20031910b407203410410000d4115038540d80541020359101c002e040b564440040b01d001c00320700c100d1302c2d00c03000d102e840004a20340d80220103840081c1d40507540d16101d030b6281002d000c064036800610980510040c032a40664008a0001c0d2140243c072041d4182c0803841c000805141c9101030707001c4e07802c1c048034040c41005a9808603000c0880003e5041c2140d03030b030b2036226007000c1440c28035900c0c4848601c081000700405500049000580c030b400001c50307c01c3d85412810215040c10b2002000c00b50b80301c6188600c0c4030002c100c01100d4641980000541a00c0688070700050780e025500b58800600758502c180710b08130010000442003101803510104644c1154042841480b0f50f0203a80c904c15000b0a08404000c49140c80c204805d0b03100701b10360b4030f4050301841706550700108801180540203001d80443d03008021720030740e800c0300c5e002225161 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 568031861 1250 568030611 568030621
    0x140c090c070809010903050616021e07030803070e06040e01060215060f12010902100305012103050f07021c030503070e060306030c040c2307140c130c031e02030103020301051e 77
    0x21803035200c0fa000c0b0b418030190b00b2000001c10030a00841d44aa1401c992120034800407400007030400741c3c4969000100b91090313100081181002a180054a601c02500b680e2034480c3d11041d1482d42403225007c0d8040d000080104516407000c90b458101c030b000c2c0d001c40d5800000a4084c150070441201c1031500b040b58500c011009107000d850706070042c8402c40000440e2a455000706002900384283d4501080d1298010000e03d503580320743c03200b500f0100150010036079a95400a200348294403642003150310200703010041d544c410081807108451814000c9140404d442c02501c103030030481b00300000c5002c400b0b041e240d40c2041c1c0112846588010041d0644404030002c020041001e800c0b40c60030840c0c00391120100c0f02c0c1c44a0381c0609074244081070f5845040f45d24001843d03c0708500d03154420b8116002080d41d58032075480f10b48901c100e450000c0b40d0703140c030640c00310010445006005200070211040300d004807d2940218180c1e40281c00074840e03581c5d10b400c1c00c5500b03e481d00400f11082c0800001030 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 568033111 1250 568031861 568031873
    0x121e020f151005130b010e1503161202070b1b0c030d11090a0e0412090302090712020c10050a0c050a0503070e0f090a0219020c0a090e1504140c090c07 66
    0x2a0b40401e82c454010801a240d80202d00d040c18207582c802412555070082c1e00603582c01400c1c5110300c06080707540744280c212002000907079000141000040e00c0920104400180c02031140301e1000241d60130031510f030522418040c08401d4243c0320151039582410020b0441c0001c1c00844080950001c0114a020022400880181403888802400000910003000140d42e109160030040401c5194500d0b24242400e1501350902c80c4414581031002c01c00080005850f004401c0354085c0c401c3c01c194480114000c0d00c00c2c0a4800c80d0f80404041c0208045841002c1503980f100e07018a128980400c980c00c0b404200fa03425204414180010440600c00035505a00c2200d035061242400303480304084151080105440010a076605400642c0224046162000f00844140e810301ca600c011f00a006101020a010000500501e49170a0b121201d94201010410170703011800110525007a9920305030605c0716448000d4001c0519a016a4407424403610300080802d0203603d200c10b180e41fa08503155070b50 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 568034361 1250 568033111 568033153
    0x50c180613171603080a08070503011a03040201110d0207031401140615040b040303090509060a15030e0316050d0f02010b01020606042a090914090d0e010c121e020f 72
    0x820b41d407151458920001c0c003100031240045120f0074405854091604020703040c0b400040c610400c05c001440104400310112480ca001c1c080b5490702141d0720307140c03400106d4150461107030104040c8a050208000700f031b400250001100d010380118941007020981172801c0e68080c201e40000c1800c450081059032a103c81da0100c211a000700b50f81c9400d90b2a0700c1c00c6c202c0c1c1c20503071055020841c107200c02c101500b403e818440c1d00502c2142c1e034580484c101039101c1055454071000300304040d500c5c01c01180074138003002207034501c030102840d1115101c2c1e40e20740b13240d881c03410801080016088042d86030031580140150b9848100c143c01400311039858005120081030008000070114a12140031614088400340084000d2441d40da22075207030307007400808130035a000460f01c0b84280c095101040800c07400030407124081c0300a89031600c900d1040740c6c0121088049903c003d018007625010f1080c142c0d4010b00c0822000e802240d11341c2405e104240c0c01d98a48440c450014980e0300500e120691800b02c1d5880 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 568035611 1250 568034361 568034399
    0x30c04090509191209090e060c0a12090c03021207083d05060a150c02042301060f090e190f0f090602090312130b030a0f050c180613 58
    0x2c456030a41254002c04540f4011001602c514500481004001d40d00c44100005049102d2060100d0b1018081650355421300038070390520640007013003071420540315605c1011465542a0140445112070a1800440c1410700c000c0744030310541c000900d02c0c0340d0301103030000480d034858010303140244d074865464030300104050740c1c518149890304a038020003039403065081c0c0c401d400c0200000c2c540380c03004c00c2c00001c840302c1e04002d5040340d010129645040e80048070444075a4103807404100100002c007101c0300d50491400003001d801101001151140d40302c904240c205030301c0c1d61142c014a54441c40d03c201c014003501c89103280000600040c2d024611074014280c00c68503000700040ca8250b80d82c082e411a00c0400080303070a03d400150b071600034070303040040c092076036248d40100345007240c0000c40c202c10010601c41c00e281c1a40100011313600f9406540100c107503250004c000d01c1149819803c600d11940310009c8102884500886100300d428004295420007005007824140d050428003803440c078050941d4 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 568036861 1250 568035611 568035613
    0x1032007050a060c020606190f05120f06010329040c0509100509070207060914090612070b03130218071202161b0320132408031905030c04090509 64
    0x402180001c0c494030941002a13500d601801550808504100d41e2418458021005101c90401481040341d8401a101120300445003c148420541d4440f801c1c240e40a04420036401084c00000900034086105882c10703030245900610301c501000d0b20741c2c4101041d83d024041030012007052142d401e0520006400448002a1280e05139032070f00000c0107118215071020060300300410030800c441d0004600030180c500184160b0420f419000401c840440051400d4131070f4030f80014a60444030240514005000d00403502e9a907464426105d407084910481e080703024640d5500224691027042403ca40220b210f83e5441403603d1201c8040c01c042e42000c080000c00b00d0070250b044c4005401090040c07401d0083c0400c040b103c40ca1414034080128109034441e0981d81c80f6403180751543d80d07021161521040703c080c001440008844417488000303100c44001d0001021813804135540340000003825544229a8100e414080703061811225070101346c4804952980a0109102801c0315802080c1e102040030 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 568038111 1250 568036861 568036873
    0xf1d040f0506070207051203030609040f020a090c0201021b0303070e040506030f01050112031119031404052706040b0a090b120d050301060f0c3302070308090601050103200705 77
    0x5101c2074145401510f842004d640003003020007603402e26441c8240421201c1000e0f50a5141032808243d40781c100070b000802c0e0340c840d080342d60210740d2001585009408440d108100103107141102034005d42c0044404004124140c458200c80c110010440e03100e068a039441c0c25401c00500c0600c40501001350007982d050040540f05a007420007482458000c080320200c510086d02241000380c4185101441040690407003400c400032504241d00441c41c10b64107143c44a6030100c100b144002d2070003281c224a9200d51008000080852501c000e056046a00d5840c1d002035201d040402040780d0b6044801030b002074460000308400c040a6020345d11000c40030305100d8101c0040c3c5011404c26002e001c070200400c40120043c030071035510150341120100039080c4407270f00b160144c80c9e00d1544444209040041c0c45816011091758071020908562f201e0700d170400b075440d0102440c0c042c0010761b0840e61003040c0c0c81031400000c0d156210b030058041c2081701551580c410180c00a0041855002243c1907900d44181 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 568039361 1250 568038111 568038113
    0x41e080903250504020c03070b0408120c0a020f03130320150c0c01080705030c0304030c05030307022b0c0b0a060b070804030203190809010c1a0a0c090f1d040f 70
    0x90040c40c148440c105850490542c0581c6000d07200c8841c0d4100741e02030b6105121000e00d80c200002250074580c1c000100d01d9150740d41d807030903041c07a2141e1450104002005400d002e00c0001d003002500841c415902911401e080a81e480c0e40c2c0c83c060040c010907030030780f821820001b0900d658220442581105c400f070141c1400700b008990021110070002d0710f00200091034030740e031f94800d00183c07070261424a44908175060a401c01080c0c0e020180c041c0c011024000f02180805014201d46501558445d0650341c0381d18003900069151030351036100c1200b00c074998144940e2a01d0000e5606034801c03142d00c86c00204d80003070310380301d0007008000c0c590701030350b6552040810b440e0604400344c41e01ca031040801503600d0b030652040c50b09101c00311602d8a03000e00c1d00942e10000880000691f40380c3d400a10700036046002c03c2c100051000303121040400c080200310309118000d605038101d0f840c0100291101503265594205141104049229081c00c82020b441070600d00094011603030b4205009a60146154003030f = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 568040611 1250 568039361 568039363
    0x6130e09071e05030d050c0c030609011b020708070611070f0305010b180601090b090121091a1015270f050604030f0206030402010c050a0c0617041e080903 68
    0x1034450284581c0320440411807a444076014404a100c0607402107416880c04022a0343e8429214858040c01400b0840c44081b0b4820400703c0459503009080350300c2801d20b10040341c001c0c80425064070400e048000220074260001994204950001000f80a800c0c6020f100b11050a28100003520350b005050000a01303004640440028500030f100020b245c62a003c01c0101007000440c4481e041c12038501040002d80e0003080d03070400c079425078140c2540c038400d21b001240d02d0303029540c1401d40071a501106001c1c04000d684016032035845071684a10b040d41c44811210481021100d03519503648030740c0300744440200344c01407800941150400107603003090214503180031500a0b1120710f01c01d51501003000007001865560000b007505650701454103085072074400308000c007018007900034140080410b00310b9201d2620001002d800c50103607102c60b44145001400b83c0700380d100c0e1400196a0304503d0500b5003041a001c3e000d03c0e40070402440e48150f00600348134204c035004056030001c005205940050318 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 568041861 1250 568040611 568040639
    0x180501021e07170c011805010c060906021c0618050105090705071106160b0601030501150302030c04050a0b19020c1810030206130e0108190201050f0c1009110316050613 74
    0x30f0f00c507014241520950700018182d0081c0141c0395959140e004d020401a600003440070943c0b030300300302c012400b910f590a1100203841506018140854820180303000e000142c2d02c0281910150f10a6280880c010707241c0d60300741e031028040d2550180f60000031584550164004004203407280ca905000300e80d511000842c03680000c480000411100c200080070041400001039100d0002d09080003a541401e852140700900c524014060603030020101e40041c0250b01520001c000c018480140305407500010703441034010000c008000c00c3c100b81403000b0103001040308141c0010281094511441030180c40c10140f4001e002502085d0300703c1c0303004c4050b0b12400000c118001005401d0f004503491710406152002059206c0c050b50f03001070004130302d200c0881083e030a03920340900c3d000d5103c0e9010ba242c6505486201c500b03074524417400c030503803520f072116400501d60180a91403090040c0c2d00036050548501885407580b42c0c07001140c100b07000a00c0e081001c0d001c6013501690030b0a4058440081000c415 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 568043111 1250 568041861 568041899
    0x80a110f120a1e02071a040911040303020d170406091401090308091b03121e07120914180c160b04050613150b180708010303180501021e07 61
    0x1c08002040440250400108400410301824042007040001c0c1d000703403540c081d802911041d110f01030003e03441080314020b54000c3c0011540400010040c00c500c0003441e48244021000350041c8043c0b40352040c0110802e40b510a90034000503250398450782c0d50801000066803c80f021040e400d021170080409102e2041d8141c0f2a80781d001407030030300d4103103d1700c5c05142008842c000880a11043c94544011170184a010060400303581c440c0800050900c1c0c107030b01c2101c0b06881101c0814241e0600c0303202c03140b0140070320043c1c544000b0241c8440d01580714150441031907800c81e40c4495100e030380c04101c110040c1e01c000e99514050400d500d80e401201e141d0741c6043e040d01c030780101c1d905100500000b405942c1c2c112075400010007913610140d50300000701540c100707a4480e2039a200d100c40096110a141c1c110034500c80d1442044501d0401406001c64000380810780000740344040d150820700c5c2d485940303016150142c0040c40392004101c440545040c580f00c0488543c010710100042c10308240d007418100b8 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 568044361 1250 568043111 568043143
    0x160c0b070305040506012106020903010e1906110a051c110c06010503121908100b0c0f0705010207210c1502060a0c030506011709071a040501110307080a110f 69
    0x10304207130829524007101070b00001e007000549000700d002510b285d0906402d6540c008005030301d030300f00c22000a0041c0403178080c40c0041e0080d0010300341c29000d00b511884059100d040b00f00140103034001400c82d1030152107008000320b00e00700310722212440110714400c483c0c0c07a64400480c54240c540c4803414036070400e8030401415400b03500184141e1400f449180074550340306285a0409d010a5010b03008445180198011721500743d01203003c0181090060010b0109880859501c121a5580d00e68801907120481e481c1d000c0d42c600400e8a40c4041303648412182c41c900d0315411154030802c691185040f20004a40c4941c003098000b480d4002c1310ba0b164440c0c40e00d60040d18243c030340022403074140d075554100441014504400c002e00c40e07802c03001c0d000f03481078020322a480c42c0d0344149000d40740c107000e504030b40001100300e40c0803074083c14090f0040043e00c03400c3c0d80e14103482c0c184441ca6030356030080d800c2c01860803109024060001c0d10400e08994058803200465403000d81009505082618494400c800 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 568045611 1250 568044361 568044371
    0x702090a0b040c0c0c2907030e030604030c030201051320031c030b01080f010b0d020705011d06100509012301020a0b01081e0319111005010e010305061806160c0b0703 73
    0x17402460302d4650300400c5440c03241100c4e848106541300c044503440741024420503010a42a040c540f141098803500d0030040d088409506150074061700fa00c65410b811001582004000b41c0000031220b040d041490380320307401102d0070f6034a150b8820556282c100d210340620889090595407200265440d00d82c0015450026000650300d00041c4518001460f010f080028400100500030008084900c641c0342c1120043e1151542c1c50624054030241c0d070540907164420031440c1d0307c0302003c9082ea01585507a000c490744266200f05100d28070009204500d43c0c1d2030801d800407041106900540306004052040c1e8410403401e680346000d1001c284c022400c60f07400030890705803880c014445144030b45ca00d030000f0342c10a00001c049802901016042c00204504d15002c541e080310100128401c07501c00d10418412582c48614000f00e5000910050b2503a118040200e001c02640d080949015808075028020660324004882d4016841100c10b400300f04544545d0000306604e0a4054054142e40e640428 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 568046861 1250 568045611 568045613
    0x71d060301120c0b0a020a021905061c06060f05030a1a060c01020c0706050f09150903011107060c17040305070c030b1501200712020a0e041406090606060702090a0b040c0c 75
    0xf28900080c4c1100c4c1c2010010045150000d4000900715411541154800d9502c92141e032081d54144107580301a4018001065154152074048207924207010b50060812840780da80c9411100780309000081d4012034010808500c1e00c801c20b13000f40314209800028011003641450100f01c26600036150120076035030110b0610600d50080c00510001c00892030724a0034000006407890052040013000d5120b48441034418402c0c174000400d44094200c01402048006d035800c95046c51584003140447d1410b28107080e05a003280030f0382c42100b8241a441d41d030741c156640c9580944555003e00000c0d1001c1140781c1d40000041d0000d1401481000242c00403000d419180e0005000503c0c0e082d0000744880710410806600480045c405040700c2c11400b107601400c3c080d0000c0782051103d5006140301503d540c0810041c02444080d0000e01100c401c215001c99441111f49a1100410345085174030031000c00144000d8542615055005803202c0000070310242d01c2e100080c201c6141d58148000f0400d0f00361024 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 568048111 1250 568046861 568046873
    0x5011202250822050a06110a06180c1e060c03020a050102130315090b06040209061306020102031008011820041a030f0f10020a1106010306020714030909071d06030112 73
    0xd260b54200102000b10760305040000c0c4085e0840e009039410860f1000d1001f085260070050802e016070009d40400405404200007494070012403c140c0c0e0380100c14100181410b001d0703540c241d4031641040305a040314100314044a407101c0c0700d0000d90461048280020100e6020b200506011004100142c2c5031440c61800942005c410813807920351600c2c090707000011401d02c0c00c980c1c1d40010202d40041c2d07120a0200000c6881c01113100c0b28000402c0090b010404580541c000d501500c64428a40700c03d130358520301076080c1c80701040480c07001d0a0b0800c540000500d0003000011850074221200840d80c004070100b01155241c4403001c03500c02e0700440c8070708541428040111564955070182ca4480c002d160300c1c696614002071090085540095a1035201e0322909031051000e00c008203440c4a075a4038106100a90046c1d84240c8000342c4100540c411031350000b0858550102c060041d0005e9a6028000d8541c0ca0f86c5002464203808180c2c40c51a00d980cae0b10000314040e00703c0c40c0c2640031800f0a41071003 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 568049361 1250 568048111 568048147
    0x1060305070815010e01052703011b0c080f121006080612070e06040207141b0a150e030f0a03021e010c020618031303030c030807020601050112022508 66
    0xc402400310b11014400214052180085400c10a0a00e146848000c000403a8a0b1103085500680c0c00e5100c08202e00728900808103081810040703000f844502500c10392840a0f83e03c0900407008a442d0f0745100002401d8000648040a005e65a41c2e041003640b84030044c5414040f29042c0869060000c24030046800010b030070b03004001a1000101d01c0300c8080450307516441c5015600d001c16440c00050303055a2280c040340c90b1160300044036030310030451201d40c50b075903418080180107440e40d80e400f14115062140814044515030324044908084100c0d0680d5500a00c42e2250f815004035407002240040410681c040f0701d1003a80180301c868074000c2c080701d04a09103103492060342d05003100311180030384c00104181c0002d961841420aa116900882d18600c1600900c0503034160f010000420325420141104580380a83c85d0090035503601403007283ca4a10902440f0302281c0720440054011406902812410300c054031003a400c850840f01c2ca1070080e818010031070302c001c230004c0c1c1c2c0e08840c0311082c0c030 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 568050611 1250 568049361 568049371
    0x140d02130f06170705040e0a05010207120905030109030e04021b120a180e0103031101140f040302060a0501050a14040f0f0b100c2001030b0a06052d0f0717030f01060305 74
    0x42c100103c040c11001e03988403481846811301c180e0f01e80c1c513011040c10701031040c0c00c511a8010021540c440c410b2070990148144528850040703030200342c0005039424180a9268046d50658941c92586860303000c00000b50031004200c820443c0e15020552941400c0040402042d02441644d86a41c2180001000000032070803404041002001c10004207240314140350660303506040402e003130901402c1d814010042d2401129000200b0418026100700c04881980214025800d85840da80c4054866058610a03c2902c0d08061580320810018031343c5c5204c211203000c020004920785400940600c285c4044444d104c14896a88060704414600703011a01c031001c3c801e00302101c07070b0300c5c080d11003442d6a82c1007508242c40c12420301c224145030388298050205c130304005203400e48040e16200003c0103900400c841c0003110030700d60300c4258409421014a01d00e02180c1401e1481c10201c2c40c45100c0c5a08104001c0701e042220501001401c00d0800156200f200e44013104048c81d031401e40c009007a0b0f14090300c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 568051861 1250 568050611 568050629
    0x110f010c031e090c09020915070b010611151902040b191106070806010c08040b07200103060803030406020c0304051e030613031d0f04110c0d050f0301140d02130f06 72
    0x803d19000a0250b403d00c42101c0680c98010b0316402c2c20b102141034007510010190380c50740e0000d610b03c20000c00b911058143c1c0c4a80d554407040d41400e031196135880c0403080c4440100350031003000904c1e110844d4061502d100328114094106991080c8042e041d4005892501400240c00e001c13400f0507910400480400859800600d418101910302600e0404090049410030000d40900c00c10302000004450003400000c4086a4984c058241103414100c40c20340b104403101c41c0c40c0490304035842402100700f5145508040d5184d03440360342d142c030025881840c4903040d0340804d000006040d62854080150030890100d4000300300e18030b10070141448802030542081400118144001c01d600c01101c034412080c1d501c25880f11102d010018505034044001c042d485400c1c2071042c001308407080080c0014141440442d208207841c500140c0f8140030312008040c03031880130300040202c0d21441d4450051000c0203851400e055025030042442030444103c01640740f0f442d026041c40301c0070207118900040440c41 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 568053111 1250 568051861 568051871
    0x319030b04020409141b0f03070e0a09200c07051c1a0f070203030c0a0e011e0e120c030c010503131505040b0f15010c2a0303120e030307110f010c031e 66
    0x2460038110f9008207007d11a400c00c1c00310010304128000d13201c041c60011300034410000181d441d00000060301280c2507604005110010011041c01c801007511003002ca51030142800e41d0600052100142000303280d810211081115000824007811441c1c52001340704518a4443c90110312102400c0d0340078000070115803040042080a01c0780070180c03006000585040e06c0100b40c20384c0100d03201c44080301c0180f552040a040310709110f801020340710189400344c03041e0b030028032240340c4951211164061140c050f0005003e09080d50b00c82c2e03004550040e184d04504508030116282c0301200e549090005012542c0c0e242070009004502e5034295018181c00403030116440c00d600c01c0701c0c0c0707110400441c1d4113010980c482d103070400c1510001010072030046103846d1a82c1d61103842ca40640d8181d484240c020920580803c1080c01e001c0c05806106404d51008600e151030f192401c50740b01413810300c1d00360103014089003044070810030302403603500d20000ea6003c03801140907000303203444060320201d200000f4600 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 568054361 1250 568053111 568053151
    0x11120c090c0304020d060c08160503011511030c01060815091b04051801020d0b041410030f0201051902010c030509031606050a0e0a0c030308010b07050319030b0402040914 75
    0x31204581c1d104082010103a1683c031144040b130b044005805004210500b0041d108182690040100d44247c0078498a191980d42224081e19644030078081c003100e403060034544080c01c0b070044040c5820000301000312450401e40c54007282c2111011b07001001c25802203898210880c24846101350070035a590082e062101d504080e000817051070b40207082c0100e44640029200c5845000109606e09060b4000e642d00c280d40355500d4020302c0403a040701e1155240a40e203240020707c9440e114480d034003000c007450140341940c0301c50180c01c003035041c100e0411008014045107464100b0400c404d0204139000440d0b5010b6842e07010b816a40028a488400e034000d002c00c41918651540d4110041e41007140020680c461a5400c0c1c09850b12a6140c20b44d44101c4c403503031013000341100f2060100c0c0d010313a070f40503000c1c2d807070b803190b070303156110700c00e0054a1584207100340c840404410240421884080c10002420b04c00c13440402c06070b0304603900103088640e6a0400341400150600d0070b036803201c240305d020400030000c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 568055611 1250 568054361 568054369
    0x507020a0609110d0b0a0509030a0801090f0b04090b0a0b03013e0c1b030a020d03050a2304050328290a020a23181c11120c 54
    0x104a201404290b120504070080c41a000603200c0d8000000c2c0503c9826100d908081e00210b03000d40d25040744918190001f07a0a10002c025102009525520182035902c1e203030210000e80210712407014441c3d621040c117806031355603200e18480caa1182c5e0b5008410720f0040803100c121000b40035803902a9041210019888013080045100b09100384510301101c09880b58807205e003031040605001c1c0290010380c641901500050820360010000c41c08116141c1000038543c8480e21248000d4101030040c40e1580040d028034060901c5c1070710b526220b21025980b5080841e0719040351070580c0c01d03500001c6c00340450f08050008031009501a11040c94285036020304142d13040901c64054132200450100a403820f14440459090750308800f021103c078140540840300a602c400c6402d408200d0709003c1040b40c2e1010340300c00c2c8110070f191036142d050254000147c041d60483c03142e020340c4502c204985c13004039080c0507050340c4080d001d11800c882503030782c074414014040140c0703019011a9100600110140d91 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 568056861 1250 568055611 568055623
    0x1103070c030f1806140f0f07050717070b03091501150f05090f0f010212030a021b0d0207090c111207050d1119061107120e0a0b040e07020307050f06060a0504050702 72
    0xc854030704418001e000d80000c0c542070240c0d07002824000000648a5903003005200036107084c274080c60564111030f5580072011102c50443d6001500e0b50880300c410001c081005c400b85d5480b08217141903034083c8001841c01c500b001004d800411841e1f402a642e08035040c0e0102c10031091100d241042c52404240c0c4e0000f81c220134600d242a40324541060070690b159100b40802013100100030072a540b641090308030f40000e900549000f800c08544094034203508103000840c0c1650b54496005804014140001da43c05001e5407500c0009000d078480310300d41100c0041010044903100c045103261988054a40681800c4c48680541c0030003569240800c031030318011407048076030b6840551598051801e89010800f4004c00310201c4900c1c0004542c10b002d11a810604074460070099850012035405502005026169802031162900c81800b060103a101005800ca030460410700403a81088282e82d5440d141040c4401081120b070046070034028241404d50007400680300886080c000b921701400025030b036036 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 568058111 1250 568056861 568056869
    0x6101505030414070f0e06180103020105030a05061c0503070c14061605010906060311152d0f0403050706090b090904022103040b04080c0f0907121103070c030f18 71
    0xf864600700403211281005900010a8003c41c0200103a03500d00810b6000041242c2c50303030140d0084000780d0314000740c103000b580c1a280c0c140c60301c43c159101c03411241d0080c0401000c0036041000c2d200c02103598180c100007000424411801541e483c40e803490040d4281c1402d6112501c00701094510555654490342900c10003190100c0448510000b420303e14007401f070030032015140300d2825101100707119801c044906807240940304c0152400c888507104016200f144000d4040024070b5038007000022380b02c00c0d0000340501d420310007402c0503803140c030b0252035902c6940110f5403948414010031035190015171000c02004042c1d951420300d00d100010544040005000a114000d1744050b40035110340c25255401c212a81011039860755100d0043c90400d501c0b03070250302c801d0b01c2081001c0807285001203c01e050366101408010490300c4440e026510b140586100154064407079800c1c0d90030443c61000303944142099610000b450f461030034040c040c44148070080d13080104a01d10021200310700d5108404071 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 568059361 1250 568058111 568058123
    0x1c0201050a03060504020a030b0301050f190c02070e07030b03120406140c16140a0918060b0607080313032618010905010501030c0504051608070503070903060905061015050304 77
    0xd8411080850040003c1e8200715070040c4003140c4111010b5056202c00400c24081c1c000b0800d603100c0c0302402e01c803000c0032584110184107002192401105640100c20040f009004071190181c40341c03100e03484180300f1580500020f41c0c0d403101d0325561808100006402492400c614506820440c0c0200189842c00b00302c4880e4400080721070f0030030320400c1105104047c0d00b2800389443d80703840900000b921440469442405111804182403c1908c10345c142c485076400c0303484000b840c9a403210040c25600043e80d601140c1400090007003101c94000310b1007400b6260400040c1415464040d14120041c8003020801c596807180083d8405540106a00102d01044403240401c3c00300c061805000006002812942004000420040141943d03015607508642c18070a40d5200e407080d400e0380884461100002e400040841c01c4c1c030707008400031900701d849480c100f00d4203900d9485140c01e440101104541a901100c100328070034001200c8000a4078403820044012600c1103c01001408064000342031 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 568060611 1250 568059361 568059367
    0x2071a010b0703031a1002061b04120209070201020714010905010c08071b050705100e031b2803021c020103050a0c020703080306030f010507020f0714011205041502271c020105 77
    0xc81140903280315540c05c000300042d44605c04044020b4031450183d40b00010040301d83c0060510064040545050b01c010b4803800300004250b03001c0166611000c1c010f03005655003009440c002c03602001c415118007034400c0010070100408e203005800c442c0e504101600300084001444000d03680102004c0412858800041d161130143c144a81049071b0760384074590000901035040c2c203861b00540b558819171000c800f603e41401c0c240502407007841380303030406c0b541c00038003040344484c0009030b0250426044441e96402d80295103d40c04540364041202c10030340307000d010400311011076034103021305035002100100601000c900f5001c080c1da100c11600005184100100005265031010080300d0b084205110090049041100d0f02030340f141609482c650717450094010205180406d41c070541034001040e512069180c0c91034146038000c02c000f40c0122218035403450f10092040090014200600d61100c40800c0385091b8050700310600c24400c0140c0c0140c0c0d000c3c04180143c8400000c1540302c0c1d40a00703040c0c0d5 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 568061861 1250 568060611 568060631
    0x2c071209060b030d030f0509030304051f1803030504020405070309111e03160302030f060c0318010b0307060509190806060f13050411010801230f0301060f0902071a010b070303 77
    0x1000c1c1c00e41007840b0740c1510981c481d080c4d09940c0b58000480c50103200108002a0312215000740e00c912040b50301800c03039400950903858001200c00c01702c0c00203d00100001d66000307210280301c580c5999030070950000b510b0f04103000c190316003440794641207238190404011003107155481d01204601c0340680e9214a50003001701180c45080c804c1c10b084c14400806440000030101002c074150101404164000e110303207003184803000000610140034000000c91039045903aa80b40741040400b00111414695489041103a4030b0703141000080040d24544d00c41545804000d028817119822010401c40c050740d20440030003040038082070884c0c20010603145804e40f10000e40106a00340d0502c0d80c2c04482d14903080400c41404501d44003d840506c0990b0742c000c0d9640da511469030705920100340c00c0d5001803035084001040c602070000555006001c0c0020414699171104d8100026440d806001c1094000600f0700800032424040d8507522007858050031954181035101019014220b0000c042c555075849131700c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 568063111 1250 568061861 568061873
    0x190305090f0d0f0303060b0f070f17070c05010e04110706050c0412030903120c030e2808010608010f0618020903071203050c100606050a030207060f062c071209 70
    0x40a60040a03240c0c01d0350b00d04901e00351902071030701c00c003e400107468030f400854000c044a00b01c1d20000d82050310541480c04980303131440400742407203048035100c2003102c4e40130181d401c0f040600f91b058018020850405e20b404005045241c03085071040c41503241c425811141d00a40d010b07100d41c00d8108c00300003140d030740e0a54000c0140c8150303001813141c4041d6682c0142015032100702c035020b0300e2084032204000380c9040d00581e241e001081000b008201d00482c900c445041c68910304452111001c0703a00900310040da8158803201c0585c2120243d81d45403001409030346003d0213503120920f00cc00d002c1210b140307818052810903c0500a24507116000114481203503420440c000141c11041502e915604c024034000d00035500ca0004812640034140c4800801050b6105450489209031501403070080031010072402907200c500d040390b03541c0d680c6404101140c032a01c5010040d09074a07403440c294004481f0000c0e40c98000302d0382011103006003000c0052059000c5071030b10f80740350390800c0850301900d58a000 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 568064361 1250 568063111 568063129
    0x12020702040e0601030c0e0610120b090a0c020f0318091513090317070203031302031c0903050708010c05192303062b020105030403021c030204060905010219030509 72
    0xe5400303800c2c0402e805803400c01090480c1280c0c40f81d1a00b161059031138450b4001c0780c0040b21995403101d004080f038541c00e03000b414680355481264000185501d281c9002a001c03a105480c1500b20320303900c07144035500319010002d81d002048214000c605011003003503400c1a944a202455000700445000f1588241500c0d41210342064010125111200060301c031000800c1410815000a000d0a4052086562501d401c80c0148010740c051351840d5180451780d40c041c0c20945040340c16106244607056100d88601c0b1211a00e0306035610030302000e20310b045c010302d031908681080740300b80d16010000d03940e1904801102c1060003009100c03e0030702e0704d0640c140c4108d245030b05100450040742400e40c568034128001581300d0003040b00d413006041e42607081c132140c04078116441c0c1860500b601e5540c0156008401843e40648a841140e0403494017918000080c65284007003030210341c01160a20505070080f00ba040609400c1c4020034809074000207200c400301e81118080d0030b1180005448006840d100701c0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 568065611 1250 568064361 568064363
    0x13090819030506090a090b060108070c1a16020303090a0b130618020a0807030510020702060702060408030c1c08070f12021c0c0807050d1109090a0c0e010816120207 72
    0x31244811000240240c00340804403101481607280e940001d003a400a40b00320f0324030f180c12401400c00c90b0f0344c103001560088405815401409403461090000864081c22400348142c07160b01340509003014600884104d51f80512002950404d008001c101000015604070707040c2c008040141e240c884451003115803c1100780a02841d0400c2c6080022191100507803a05620075500c0d02032070307a40d501e071083e11040d503400010919084800340820400d815005400b08a00007041249458074560000740741d5401548145550740010464501d040024422121404051443c0001800c2c8001004041402c014010030521100300c0d0060030045c858a02285034142c1d164003196100e00407401500c2c03815038902040450b6052100e040f420383d204a50440c001c80541e201c81d0f003488882d1003a04041d144c54040c407035152000344945055691100c8215016000c903c0c0005820902d101d0003c048006e8080d60038148400d90080c0801c80d440c5603081c20030058a03191000381d070303000c11006001901c10030348 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 568066861 1250 568065611 568065637
    0x50604030f0f1b080f070b0a12230708040b100302010e09040c05032431031b060218030d1b05070509090106080f160e19050a02090109060e130908 64
    0x21000c104c5183c0040c81e142d008060008454032150340d442c2081070b0b071159240b490001100c0c0e40e5444146180b81d006010701850201c084401c901510914148251080b65164001440e4105000034040685101e9410110b000034412041e419900040d00b0b05076003c0c0a076004140b42c00004090100b15410038012304002000d40e038410f603241275103103640444144601e0580c02d0349000300b0404540c5c03c000101102c1e541c0e0b044000780211460005d04408881001d4050202020850301d00100521001403940c3c8180401a180c113156664003450070343d9440404e0181d486241c1200340280c1000e41418025100750200b50085502e1034001d042c19a0303a403050b60000c40b000d06010400c6010b4000409445c103000849840303040c1c400c69503503500300350002d004461140150500c84071082c0400d03107511005030070700303003400c0d108050400301214001c46240d0140e550208214620b0341e030101c0c01500800851070245503103480c0d0000111003290041e0810102941e0b04140b40130090203d02392441119441 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 568068111 1250 568066861 568066913
    0x50a05090411030a0f050f0c090d1502070606090b0918030403140d0e19120c08030a0f020709140c0d0605031006330819110405040501050604030f0f 65
    0xb0b2858115400664040070346030305000b503400705044640324081c89090900002055170b180e02210150079400030310090b070030840214081001c14072245a9400c0403296050041e0307070300b90300c0c18504202c03074143c0c014408182c1094401e00007550703840c8006412a020505c0304031044030340d0300a540385100300d5200928407a180c400c3c0c5101c06201284a141400c180d4886180d0800c40381d0400070b80b040c070700300421000340742480c0a0058180c40340c0d44168040c130500c0d000304c00940ba8010350b03141d0707008000d050b00010380c103e240740b114560505c41a0002c0803420000c0c045801d0b100f0f0707a00e0b51f01c08001e000403940b24006ca030341c00783c540c2e807a00b00d1002000050140c4d0352603044030300c00801030030703550198046201c80c10100000f08000d0341d40caa078401004010014144140c5481210800c07000361000b011098000d16008402c0f0052262032030200d29182c41940d110710b0301e0140410784030142d03c11885900e052000704003103074500143c0300c81e05a0200003040c0007645450210003011034440e4174510b4041c24 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 568069361 1250 568068111 568068131
    0x8070306120501050f090f100207020a26010f0b0f1903020405010b0c01050c0708120403090e07030f110a0203040302090a1811120c0f04180b0408030117030f0a050a050904 75
    0x10744c0300f1030144654901112141c0c0d600c481c440c0c0e4512490070a40c0c010390100400074585825940a024424801007001c443c4036501c6c00d01441d82c03440aa0480504040800000c4000009100c0d45421104030141840000d25150001d0410042c00388001d00414061481180100351149400301950b40200200115612024040c150303400c03200e4200c1d00c943c80c14011030380040846044e50409030744442d0180c609400b8440a4501e240040d1084003400b910f44001705120415201c4a441a0743e2690009032140c3d03130131001c2c02514616822a5504c240412050701101d03804001ca03815a50165014010340c0c44e0340000328001c004805035418180f168440d0351080124081c0782e0121508111101c0030100002d09016459564103c400341c1c0c0810ba4641d10102410135811504140c00e40e146103480b1500306450310701010700c0c03c40d01180e100c0300000041c002a000c00e03c41c080c1281c0200300860504c6610307001c0b00068800c0da940d4600340301c2d0104114a0442c400c2084943c50800540240b00340024 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 568070611 1250 568069361 568069363
    0x1e0507050714150c030a031a0a08060718030b16020f0609011d010203190e100e0c0109060c0302071e05130c0e010c0f020d050111030708061c080307080703061205 71
    0x1802c0760640c0308010080e034203410b0301d444200b9525003003040d80c0618500350341a44c09500914001403154481130340c91503400050380c0c81844030001010b802025148919100000802d040042c2640c0c0f008a4081c000c03e0021a8000e001e4a40c000c108078014a1307010b5240c4000d070701d8003c9614072418039102e620100070507054117400000c000b1aa02042c200760310302c1780e400c450917030104071180d81259400030403c0f11840a030340c00208060701c0c0c2c02e080e40d00c0103080404020070384420900d0b000e000d0707120704821b004a592240081000b00441c0c80c0401a403485603030025103404052050a100a40b0f000610040900102c100c1c402040c006114080c10140340c0019400b44c241140500041000320140c01207a5000c0c04680c203040e90f1042e0508038030800c0360b0801500800c09881a500c9658075240d2900c03158400c0001d500a8685440c0c210740780c40c00408008200002c170801840200182480600090481c400c0c0c0e5003000b02c504100900741e8607500200c000700156071000c42c1807403003246e400c418000 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 568071861 1250 568070611 568070639
    0xc020c09042402040b160204020d02040f030b10060210020a0905130e0d0905101103160f110102011e05090c100e011107120807081303030914010e011e05070507 70
    0x103402d0301e02114071942c2c4140c0124015403041c80c4001104101d121421640201c20807003043c4020001801c20120306c0e01c070380072a007007a00080110300c8022028828400000982031703100300c9114002a030a401c00d84008c1d1590f400181c0c104140da00440c00441c220301940c1d18078003400e40074114a44900c00040054050070701e225034400b840c0510030182c103009100b901c808051750701c040c0c0044800130408204642d5081e2200d0074410700d0100b44040114070858000301c000d0203001d0341d1108204c060900308400386407614540c680c15a854800d040c0c00080c1105804540841d06440004407a03640d550f106007040d0312405a280e204090352407920076035410548500603501c00307a90340101004100c02d0103507a05901e0140240614401c03141c1400034080500402a207403140801c5801c0c00340ca0b80b030580c0c41c421260402c6020500702c000502c00c054528680c400039540920f4141116045000040d02034110740c800c6517280c040807105040514010422144a55400302c100c404860391103907440c078221 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 568073111 1250 568071861 568071893
    0xa08120a0b0109141002100606050a0206222d03050c070b280212041d0a1404020907030e19030f02060123010c05010f0b0a1d06040c020c0904 62
    0x1500e00064001d4651055110700706460480c003604030004400e404001d0100ca0070403403802148524142140112054020758000300000e441311030304c0e5024100080c0c10308000804504840c22000d0020040050304c991503101542c11045010080e65421101c103412010704580502c2180b5000d28401010340c404000d1040c81a0303607040e2850030741c46251091103441050b0b61a01d9090074405110640300301000f8180c40d200b43c50048070307110540103001c4642d5820a902424038030010306c0382d41962901c40d1122a9000c01582e03400c0094018406a94a1924020700040d005004160000d000d160017030740040c01940000c41200c449101140c55072502e02c100b08001c40008101c1e4070150203640c00010300d507058510904242c2c244447c58540346035040c6030315400d141009083e00200c004504203200300c5002d030302061000304000f04c1040501140200581c081d0002200e4800340030500c40ca090300c140c3c0c10071402c4070701050040c1c40d414100e24100408d00c00e1944400014240400c020920700c0c80c1e6060 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 568074361 1250 568073111 568073131
    0x50903030315043801020708100203070e040504081b01020918010302120d0906030509160602030a031b09060804060b060a080f07181e1a09030f16060507050a0812 71
    0xb050401c1c0c400c10313100c800d12421258200a25120f181108141c2060100d0300c0e01881141c24095852094a151583c503a00c003c0741c0d40c0d800030500540b164014500000091b00341c40500540c1850760320414144584c2e0351260107103000d03090a040044080d012038900243c0100291201003c010110540e0300080c03104911a80c007400d40010440b81c04a04035510302400d0322046c103100e02d4500146c000e04001403580345940211100001c1507800840400044c0c44c01d0f40c000c43c1c403010904001340440310652166088206050000040f1562240d0303014103503601883d10351495212841c10343d001d007644030070b102e034440c1002c5040400240c5c42800c8505c10040035a2411458540045c01d0304c45500403038030400c81100c00304c0107000215407041c45c10740d981c91000d8000115541e40d03420410700d48078941042c5100200107600046490100034803039041000d030014114070a42c0c901d4055406081d44503e00c10720401040350000d1100500c0212201a044400d00d50388000389409600e50300000c480700b6600d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 568075611 1250 568074361 568074371
    0x2031503010b151603050c030a080a05330402040306020d02070c090b030a080714160f17060105010c020a090203150114070507030b06041d0307061103090703080a05090303031504 78
    0x81850f080010702440c0b20403002c450300d045080d0100c0c2c2000207a400e0140c051000811100c1030041c4c082000704201b190940d140c802d20300b4201d440c01b043e200c000e80f08101c203100d90300b241c40b060000d001d18298400c1081550640032586030340420064001ca03400903000c20710205404d0f03100743e842d80041c2909841a81071104803900c0b00c1c10102204d540382c0c400364145e800001030000107403d1300028550325008402e048038550030f26185624148100e203403100318800d408401c01113814841c0401000e132007840d00030300702d03c0706011895540310707030502c211030402c81607180031400d54807840c1090018002d201d8040d940d030f2410f070f807003103010464903007015000503040c80685000c02584010365400903170000142c980e180c51922114840032014050340c5c0e00c0780d952210809040c100f220186175500088024640710429414848102d9440030040314104208004024004401092000c00d690f44400d44075160085441d04450720301403810711b20f4045c480002130009090305603c04404c198801c940500c0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 568076861 1250 568075611 568075631
    0x1203041a040819112206050d0302031e120a1e0c020607030b040e010915050c07170c030d0c05130b130b09040906020a1d010e1f120203150301 62
    0x140c1403180d4414080e01d034001103145098105501d202006443c01445182c208000340c1c80000c280c1900303a0b01041c2d8130160700310002c4a650503802903000a12007203407492062001618082d48030f110307452404404082002201d4078180c015030980d55481200c9951548900d403210006d8000c0040c410116440e0720700700300300405d11304503000d40c0150f24030660280c092a06c1d0460150044c182d081c45499009480780180c040d0303c0310034800c020f041e0b4060003803454240e80301079080c0c040350000341400440c91400c000b484081591080c112410035081400c2c5947c880d01690740c00d0450081d00143e800450070300d010042e1940d4040701410302003400170a4070b02e40039901c0c150210907100760404001c0c03071510000204149a242c038013621f400342e00540f0101e00480b8903a100003ca9004e08090400300715407c01010004d100261402034080c402c0c00d0440d6130b1a20100095404080300c0340c08043c1c415034980802006d88545400340308200c0c0b000c410b644a080c1102c490303207005180000b15000798030780181d80c0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 568078111 1250 568076861 568076909
    0x6030b090a05010e0d09090506010212210a1401031e1e050d0f1d040e010204030308071e1b060207020d03051b070e0c1303050d03020d050115021005060f120304 70
    0x81e644116298046c54500c0c4c5501c901c080c00c00100070a055008469043e007440b4504c00c010050381c250514501202170104d0a4500c3c40e0101508192240345007030304030481020546103650640ea00f0a44440340050549203640581d8140e08006103070280004142c0920b450841d00120424030039015140c03a0000c0c114203e94046c80d0030b002c1030004131050680e10b90700040f817051240c400405440424000d84041481d800d90344135510490014020314100900c43e83e0140c0001007806a0a102d201c030007607140c0000b4000f0b001c80007101868510800d000c820050030754119008254007802c641d10050750f504000c0c0c5150800c074084841c00c0100b00b0700070300c0054045040410349412a070b400c1d4070354640300203820107a0001000704010003480c41010000c582c0420600c0c030442c2859401680e03410001100c00305603070040c2d12070036640e01c14400c1884807640100301080c00030501600021a607440e00000303081085213150180d04894171040040404002100400645d4010100746004040c104041 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 568079361 1250 568078111 568078123
    0x30609090309030c19050a0e010618060906030203150301051e0606040e041106040b030109060f05011d041a04060e0f010e0108031207051e130501090b0d0504020406030b090a05010e 79
    0x18581c0f40e0803044120341075142c05070344501c19a0740b6503803000442d0b803620046040d9400301c1e089007040c20340500040049940c0304091905107011031405c945101c0c034202002d000349210340641c5041c1600880001d000382124a0030050f240d100030000d016904114072000000c070038404011400079096000510030b42031102c01c4800322503055292140d9a901d0b038585010248002c1c5c11a0b5121000300f000042c2c0325600c2010794040c00030304100080305807611007494580503499120a05000c0102c1c410380a03154101076410a440c403d940c0403908002180380e004640700c000c403880f640a4905030300807400c0044003400707521403d040400c020403641c80c0c9203c10f2502800f446000ea04d0b40c000c0008103414400041c285401030010300345542001100800800d0040301156802044080070400e203020f41509540c040080000f030804101582c00c000c2429058441d038041401039588582c0841c08644450340841c0003550804641101030425500c0c0c03d4440490600580c0d40b9800c04004e101c038240d0100b41 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 568080611 1250 568079361 568079377
    0x1505041a130821180609010507050d0e0c0a0602011406030c0a0317120f07120605030309041505090c070c060f0815010c050f0f010c0c0f0206070c0b0705030306090903 73
    0x8200d984607103079991004070342c8021401003c44070008044428000b4080700103000310305600210261083e00a100c03407501500800c1072500b60f041c02c09110031249c10101b2620140c4076420045941d200c034001c801d1500003280b4446030003100751080042d03465810f600031041e001c0785c8000d01032107881e2001059a84c100d15035180b944419001c0c0104005a902d000c4103240c2c9031040e0140b800d06082d070301d141203803a004442c0f07104040c0b8107404002c4140d074010032441f010246210108422030408001c20759030f0040625035401031b0fa03201c3c1501440b4070081c2d004801800c004000c0049031400c0000b0394003681005070115401003403881c0c040351140c050b04640310407059540d138281241d0f541880400b245d11035601035906201e1400203550100e8014020f40344403026010081c2a0311421000075400c4813035011107107003002594181840020101c0540b507001e2038040702c2e119114100b504244030788039119441240541030024410b0208240070000d10311458040b541c0c28503d942e2079070096100e00c81c01503 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 568081861 1250 568080611 568080631
    0xe0d05070804140a17010218060c06010612091b0f0501050c032212110f03010603020d020904030e060c0c0a050d0f02090912070b09160e04140a1505041a 67
    0xb00a000c61020f0740c201501c064002800910065030310085034148003461060b02c0001e9400260403c8180710100c0d04440300d9001b5102140741c0350740c18881c151900d4040c041d0104200300d0311503038845003000e9003126002d07036006043d0b000700c0e0391100038512505002c0d2240c400c3d0031345401800683c40d802401070710f45110307024015502c1c0405042001c0c1305425511501d0305180e8828002240410559008980d042d12640002c072556910408101c5590307030b40c1c00424800c3e81040410b000580b20074048441c2141c1c141da01b0003258965140913a0035a20070504207030094408502003c2842c0c0008014541c06002d0b2004140c0b141c458007804103208100038054a0207460350b540b0300c0181462030301d05e5800916801942c0042c500c40000320f0b9280d126400c155080000390b13003800900541401088500c6204425401c0c00d1840c041294118410061014151000c040d60040b00e10509004589100c2d86c4004500c445c3d44480200100402d82543e05881d01110400140c06070f0a00381303605801050200 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 568083111 1250 568081861 568081867
    0x15060914130305160203120d0c0305010803040503070308131a2805032205120c060f0402010804030c1a040804090506040b0303090609010215091c030207030f0c03020f0a060e0d050708 80
    0x1040480d00c3c0c081444c012038140c0700f403501980700d4400d040d010700203107168100081043e21004100400766030741a046000c568004020400040e139000a0320000c0f82d40c0114059221030940784d230040b032051903a00801c0100f02c200104104c0c07004840c014815100030b0400401052003155110b03954545601428000c00d504001041442c2c080e200c140500185523070300c0510b11240e80d502d56042c99020000d6882221303001c107a500300340c001400420780c00020000c0803d4507280940000308100005400941405807c10b980418418611800303560101c881d941c0500c603051525000d00c1c140e00c54801c8000982c030300004607040d0f1070580201001c45070020b0056040548103410000d01b9403000300054150703c00d0b107012403100ea0004a03000e126944403005044d41c02c21460810046840035203611080500c1001044000780d04807a50807030040310f40c40c0c450140c1e00070345411b0749000d00c502124001d51040790700041c20803403180c106442010705c1506645080b0341203c4c040c1d80718050b46900a058403418 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 568084361 1250 568083111 568083127
    0x30f020d1802120312010e2d011d0f0c0f162301050f0403210e03070b07050a050409051e04140f0d05040b4e160c15060914130305 57
    0x1003100e074009041e0004407078102c00c941d00c04405800710642d4001c000d08c0d644010400701e400360101305440c005440046c1441d00e0f00240385400e10000a104841551000c950013511a2942040d01d81c6a400c41500700c1d001c54250403d05194800004500e03003580c0101c20030079001c0d0060051a00810100d1014015030700c82c0d65041d60041240003002c2d40c40840c42c150302e1007810300381c0505d10a120040c0003440c2d0720445da041c0043c81302e4000f0a50000d2100401810b4000c990003011a0704a51045100184640f1481030303200b0803a5858042d40342064403c1c05100c1402302007a904054110440203c0c0c0345002ca00302e9041e1524a1481c80c140403031000c1c032081107401e0307150000b8071380c030181442c0c43c040d15482201c030f104045412117002d440c11011030100501400102001c20394964101d41460505d1400400303940201c1c0c20603c0c2c110420004201c80c000b0444480705215a601c4020710612407079840b0096007004181d4003412101014032000450400b00c002650380082c160103079241c0d0314020311 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 568085611 1250 568084361 568084379
    0x90e0c040c02190308180102040e0a11040b0406050c01060608010b0a2f0a060c1407060b01020709020417120711100203130e06030c031c030f020d180212031201 70
    0x100c2000c4198003c0761184001410042c000c3c80310644661242442400c0c40c46940c2c055107070102c5c03850f11030b80c410001807000204c1000d80945c07105000b8008034040c141c1d00101074690145501025600102007000301d451a0041c0207040c0140d4a80d008000d41640d0304411075844000388a01a2008000c100002d0000e20500c02c2180c4410042e00151003e50707441810348222401005682154101440b107004000301c0f03025849490450b4a006a2515000180b20405205080d00140a076a0368000e40509074028440c001c01000280411516165070345e184141a0b488005601c81d203001d0301c4c8880d040c6004000503154130300d0b0060503070b0001c00e003c10107104003135800800d40015480140440c245d0350904000e040c0262000c4c0c0c0700480d141c140241070518044400c504d03036229802140c9503030121510203410100c00c40403481c01084140101318202d000f807095030149040c9500300b0280403110b50780c0951381d10080748259407044c01e00700e8004095891b4000c108504191414000041120300b80e = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 568086861 1250 568085611 568085621
    0x1a060901091d030a0f020d0f0905010503150901080102250812040f060f1d0c1003050a020c0a050312060d260906070b010519210f050708070f090e0c04 66
    0x180202c0d03039500c1c4500903009540356811840051000951110f44c00e00526414420541d180b822401c0c00c503d12007400d03e014141400c140100c904100012002415a040e110008400c0001c0a01180b48070f58613000c00394040c0d80900482600b8040d82005450314103c0c14000200e00e80d040100c090501d4800c0d280307103840800c064000c0c2ca0a4442c4800040450b1301d604c505400c0e03040d84031001070900070107880504040002601801160030200c3d01a410352a9441801c12512541c0790004055a0f0121100c00070b00441c7c00000b600c1c441ca40b515400c00000100800e266010b41d0750160159444c502000360301140684000e061410300304a103144550340025a0b492000720030340c1c0b01d061400e0368010902c6c640160a00382d82e08200b0341c0040105062010000403c02944850f2a240c1800c203c03034613454100b14079030a6440855025240c0521280c140e000c0e01e02c542c800d05607007180c0d950f1801c0302d690314072601507400043d001500018801c1924861004805e6041c4050301060b030340d000400000781 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 568088111 1250 568086861 568086881
    0x4231605061b03030106090302130203240a1a07060605040501080d03270b0a11031e0907090905061006020a0b040b06040905030f04170708120a02030f0d0501031a06090109 75
    0x110b808040303403000c80700a002a6001e01416612040124030758010421041c000c146070205048c410001d0124000c1921400c070b4101d00180141101d800022000c9030343d1120560207414034000000d10400108440802000600d005510a110301a2101d082204840c400e01c50000207500c4060f2080324140a600808200310110f040d2070340048402010043c3d90140c1c00c4d08484c03410501c820021440d08030b225085104d83d0259201d17080d0b107005800c20400080c0760501d500f0859101000940d840c00130010759001d000c01000c2800301841350b14006070b036180155610300e15441e03408004981188001801183c0a4006448181c2611075880c0e11060080207410a50842e407180f5071003020440410042c60000703554620740f80d40e00e15040d4003810792014140341421503040400100401d400004050014501c3c008401e60346000c0c00782c050740782d17104914a02c8095400400c0070701b505801030b80071034102c2c1c5c0506108079a0343d00d4001411003000d01268003d900c413182d50b005000465060740120180 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 568089361 1250 568088111 568088137
    0x1503021203040b1303051005010320031e0708071205030f03060409020d0305040f091104060806220b1f0f1202091905040b0d0c0b0a05120423160506 65
    0xc1a1a4204060307150b200354124452040005805c004001d010050b6141c00f004c03000b8100f180d941103568080c5040080380700d03e05920b08591a261590b0b809000d44170140b50311a10400106042c0c91035652555000d105210142c02800000910180030540780035010380c2c0f080c0514038051000000039034941014002c0c54009a4401d0b02d900141c685045c54415680240c443e16200d520384038050030107104580007440303154146210300d0f4a126810065900b40c3c1d4982c1049141560f5030300118034126241040402030243d00c40790349400c0c08042d848a000c09009842061004040090840401d000008810f0000714000c5415440d144030b02084904c2288030700300075250115200c00117060b1120101d00d0800c02c4c054103c2080685440e00c175030a004242900d21400c00c641c3d540707960b88004528402c0524884000451000b040c0c0700c1c40840e13054445003414018a0704203406e202d09030200520050898040d010200d15040c0c1e8001100c80b1440719200c0f0441000f4104014001260031201070b004030 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 568090611 1250 568089361 568089367
    0x1204060e030304050105040c0b0f070f06090b01090b09180c01200f010f18021f030605060a030b01020d110c012f0a031407030c110f1c151503021203 65
    0x1200c00c051005600841c001d10012074181040d0130015004c0d0140e5124a81300d00c020010740f02c1f008801c805031500300d500149544c00d03c2010341000806041c0c0980c0080080320140300100e40e4441c0d96004241c501020ba82c0c074000380e6030b00800c80d100104003040143c069400843c44051542c4144503008240030a011303010850b9684226036031038450245c003100103076515914880800300c000d200c1ca0606000145d026000c0c4607044d00441e080008102d07261a2000d0100103000c2d0590003038101900928019120340d0b0b8503042038400070010900f5038034981c0140280d10304181c130325202e07130841d030641100c90f00a84083e40003d40107543c182d446202005041c0c0102107080c0342d200c0380c04440f147c80410b90001e011004142d150040c43c5594071084130204000074482040865400046005082c2e8003040c2d0221042801c1d0019100c40d1400040680c44100710222031004110300c00b440c11a5449048000c0403507605100304019296280000400c6000042c41003015103040c0c00d01f41388180c4c0c00019245 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 568091861 1250 568090611 568090631
    0x50402030705060310031a040c03150213030b040b0f01031104020901020f010c110607031406010804020d0c0b1806043b090d320901020708150129120406 67
    0x1003c0c0e0001c071950555800512000c10074022002030090101b0341080d04a10a0b290903074130501a200140405009929003403050035402900794101d6000061100f02691000d64900d07040c074121000f00c03012107115803410301140507120641403041c1230b654031040340c010176041c44003408025000029024110310440303085040c0d52400b8070500c1c4080311a40d90b102802c011281541c2d2414a028001a081500c1c0444122070100c2034103940381c008200b460004015110360000401101d50f030840070b0448150840c0000d8908044001030009454020b0009181d1018400300080360041d031084a03c0d40d0100d00e111094062908043d0302101e800e0a141d604894016034007650303654080341d01e80c019900041d099481c0e00c0d000170601d044031640104080d8102190501400d00c04e003e0038404a940c400840d1100f5560b0080c0b1404c80901002400c07a40a01007043c8500c0303056800703100d400700d80c1840360040b1404500f00142048983c01100509182080416502d4802440240151455a80c903403c400d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 568093111 1250 568091861 568091869
    0x30a06020a184e080f0d060e0106141c0e0a03020304090f051e0c0c010c030b0f0102070506041205070e070824030d03020706110a1d091009050402030705 67
    0x11001d0030010003d4001c400e05503404004a01220254007009690301c200701440060180c0003505070445842401c189441c240b42c616924028204501c11008022441000382c841c00e41c45642102e00e0030f09001c03001e9a9494080d2400c002c10f000708040710008001d44c00001c460409140150703422454006a24008140708130b0034a00a00d90440040c0c10004042291903903d0140510a1800c5101088203080012014480c081c2c0c000003035041c2802c6c80c000501c100c01c02d5090f40c41d0303880000c0c001c0c0850340e81020f00074001c06c1785a11480c030800380100b40c1c091319480081d4501c00d44401400c40c80c03a181c2469610441440c028108841500c40d1000c0412000e8401c03554900440300390300d070078400d400c20240380001481c8108103c04078410880c1070320f51980c1d000810742d0306140b1a090042e40ca000c1800c0210203842c88240450a150000034104007440d4482011528410300360b80e03c0c0d144d0b843c90010055160401e80305c50446215505040c440300406030b01490b0050b1000301224007071603a60000ca = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 568094361 1250 568093111 568093157
    0x8060a030f05060106020d031a120a0210020c150304031413050d0309061d150d14011418060a050f01050c01061410030b13200c0a061406030a06020a 65
    0x45030355803c20703401000416010442800400260304060108030104000498900f80042c2c41c2441034031181b504c000701c1d002c00e101e80d260064010b010401071100c07902000e95540d01c1000343c1b902410015030002c0e010030200c000d8030b016590558801ea1109840c40001c415600000c0359100e0000b04018005881d80d502000c5c960080c1c42034a0b1002d40e145000030240a21f1564914456003411003484900741755104114035071424803d400c115107550300d00d60f0001c000c1c106070307480440c414a00c4001149130441201c2001540b6412208086001181408201b2042c0f055130760f15080b02c01150144514074100d143e0050f83c040c18544181481c5440d2001425600194400e6122005144070031103242024503107403101c41d40380c1c10300f803250f01e1400d03004c0741071011041d4000f8100c0380c1c0d545040200505206150202000e4000d20f1034650500c800803039140c1c1800102118618074181040c003121040c0b0405a20071600103000c2d012485540d150540030f948503200301d5040088040b401520392480c0044 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 568095611 1250 568094361 568094363
    0x10e091e0c041e0504110a020a0b0a0e01060b120606121512030a0306030c08120d020304050313060503060a0f060804021018090f0e010b061c0212090303070201060b04080d08060a030f 80
    0x40c00300b83d140360606110459190b94100408544200503038049503400103020007119034044001040c4c1d13924034210b030f0010a03540509139500d501380100010045031100207007502c0b100c0e51100828544800003040395904c650080399900c01280c3d0001a40b03444607c14a54010a010384008580720424190600b150b00406024011995130b1106101b0301402a003640050580800180392240b0868050141c0e0b02928180740c42e0303242c0010009040101c14025185d0018000c2a8a42d50940791603010382160002c5130b41e140141c128040c00a8803a034400400d0084a469450b6804036858540034401c03901c90000022085c4140c62010400c01c0610041e184002d1034020000204c840308009a88140e6211003e0420301e40e0401c103c0301c12603a500001c0b100a00890701d00d40800512401c4000c000e805030b185203000c181c800008000b07442c100800118401c58169008118140e00d07042d10300501e00480c00340691503804411a001e00c2d9000d40388480d003120004203407a000c16980d81c0c851440c2003810340 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 568096861 1250 568095611 568095659
    0x703020d09060603050d110106061b08070606030c1802031b0d2c060a0c02030910030b040c05030103050105090604051b03120a02030a0f050f0a260a0605010e091e0c04 73
    0x2180381c100b0307607c050300c81c1000c0c200400a000f250300e4510010310510007542c40f4a00103560803100c1d810040d4440031145416030221050080c0359503070900080c2d03584148161042e68a5582201e04966080d2084a02c201066203002c02c00745510211040c0741c1d00000da00650782942e40c00500088100814840c04904000c2032a4405400301059142044005402c0296050800d1003884055402206a0344907481c282c40d419003c0201c2d4500b04d002c4e10700c0701c44c0260032901e4000f20f0038400c0da108004506076806400240070716107610701c6042da03850b001c40703001d001500540640800380c40c1e41401100240401801c03031718a01d290041c8070000b6804910400050f0340002500040590044c1c001c1c218840d4030304000381450024a44d8462612400800c034041025008161114820784904460b008201d9401c603480e515121a40800a04140c05480d001c01e1608040c888540742c1703016120b11900b03122031040701da0315044010440c102405040584206014040402c00c48007031850071042e858502 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 568098111 1250 568096861 568096873
    0x41a1c0c02010c0203181009090f02031611100f0e100902030606100f140c010219090b070c03081303050a0501091b081f060503070902030402040f050405060703020d0906060305 77
    0x2990103821191410f140000359081404841d5410345031242944007007005541da80480103004200b2280e40841e60081d00c0314610748480080807103101c0e800755115080c80000c5030354000004000b03544440d01455600c01d80c1e0703c40c2020642c002e2040c0c110082c0710040c0540803030301000c1c2d4010a800c0c4039421190036074035a9520a070b0029841c080144940140c0255002c00e0101400c40c4005c0002c0b005068140030b01c01040801d40707010014804440c00004108021911160106208000c0401d01c8021000150390f0f090049030b103030200000c640f0f455501462100e05c0f14610780d42c080541e0007501c5c4400800400240010105005201d0a64124400d80002905422034900044202d24010007070660b04034030078003848100700005889000c4030020007118041d410380d00d59400600550b030403050701405642030004840c041c03500518015482214140203041c030081061007201c40c1200d010344141e04c501c0100b03200c2c600170303801422803e83c3c401010482070382d19101d40082c0c070010351044400303600c48 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 568099361 1250 568098111 568098131
    0x21050708031c050a0209180601020a1e02040c0801053105010e01170c010807120e07060c0302010b040207080a0f0507020402040f031515051c15050612030c03041a1c 72
    0x24401c403540450f060304e00b1403c0000c5580402c06c0c1c90202803001813406102c0c000310703c460b070003080568620ba42c0101c0515540e181c00c103035044040c600c91012030017107007030600d01c0503100d0060f9940b6040c2e810140881c3c00c04180384108003180a55100d6900340b00c6268240407000d1403060042c075018014125800c94554500380817500d9900c203039403c110041d04410000c4606a80c4081420b40000e214a001d0348404c42d050021801482400e080c0301c0345119191001441680100181e00003600a40007000001c4020b001e0005910a00708010801313601000120b4205000c0c10101e10b026980d860070b142098207030b43c0810700700c1c4d005070080d0f0300340c5401030002c104001036a241e09055210880040c0041d001d45200400e094074540a0544240c400d003600d003102c04110303140140125002113081c521004c140b20880020074080d00c00c1030161800301d0307c0c10b41622001085072a0b07500c0b4013000f14079061400c1050003402d00108805006c010080040c0c0114684241081c185d144e2101d200090034402 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 568100611 1250 568099361 568099417
    0xc060a0b1807090504050c0c01050708070216050d02150c0a1506050609010e060d02121306060b04080304060f0c06021209010b1203090409050a0b011d07092105070803 73
    0x450441c40407461500c1080201e501c1d401035098088460a4034045184d8a5650030804140200b8420407900d6203044108a1500d074004142d9024068540944d2280482c00c4526590680c0034000c1c42d40000c0c1d224404401030600041c030210b036039518016a801d0002c00c2400078201100c43e20b050720350350400204017118843c580f103102c00400c0c0884d50507103060f46920020305060700c0c0300c103030301e10400000c65829815000d030b80490302042c0c0449562051468000c0c00c00c0704464805806640c042e01d015408110104140c0881c0c0550745220000c600340303450700104698504003082c8103000c003c1080051400141d4030300280014641c0102c28036440d2403e040d030f190031507051100591144000c10040043c0325404030885100ea5802c1c1c030701040078100d9082041c580b102e400b20080040356500000964034103841c0d035103a01c59107550218051600c2d0008101c1c2c4014042c0603d0100f01e0400c1c50038180c0c00c0c81e4448480003148100c2c20754164a580300340c950708580010101c1c001070070000550070b8411203 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 568101861 1250 568100611 568100629
    0x10c05070e0402150a020a0f051f090b010b0c100e0a12020105040b07020639030c041401080c030105010c032c01080907080a0b04061404030c030e0a2301050c060a0b 72
    0x41350640240c204440350100a6071001030990240c0800c00585d006000c0c88410b2200340400c400800010903072500d905050001082c4181007039031010140b20022030094030040c2125440c15202c801045c0222000d400c0c4402000f0405100c000c0d0310130b05c14580f001031820340c1d0818805083c1d4000295a20703185c1000c50705514028591811500075030104908449040e4140881c200600d88805440c9070145640809001c00080c0013181000401001007903485c3c40c0040c41075500200600c228034081c1001541c03490b2054604124130b86e401e000602032544070394103214186003c1d04d0508000c0700e0405403100030350443d5807080315811600301c9a29403545c1100c4103a40101050000f803200e07038605000b03a0b403503403202c2800800f20f68111010a09002a44d0065140107281d401220280e081514029140111108046010840c99907108074940b4040412000320703089000317110105c0f41011540b80040260a0442c0e05100c01884503100e04203080100600c0740c01041400652803920754100f0580700 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 568103111 1250 568101861 568101889
    0xf08090f03011e0e1204090605030f161229010819150b060408030c060a0c0c0c1a13090501050102070b0708040e250216050402070b040206030402010c05070e0402 71
    0x1a0421040d003065205034000c83d1055003000c94001140b954000805003042103110105240c100e0100d004902c1041d10f62104084031421800c403a00001e106407882d8440890850440d10207492090030001d005c103030090030310807a11030820503800c40140005008201c4908152500001014005104c400c2d4100100120107086400d505520078207955104c12501d4608909140b06442d08450700d120f45902d01618041c00c10b03902a20745480f00b51507100e41d241000c4030003d61003403d080384070019034003550218043c96000103d25160034180b2200d260f00d4244000c10344941d100400081d00480c6401d02e20b039015100948002c41c05502d8080024a0254940c01c9030240d00b808001c40300004d0200c45c1158112852402081c4041d5034403a50702c0e501c01c48162817038298031081180c0b6410142d02188400c03200202c2d84000c051a610b0740c05110483c0201e24008204d07035902c0c40860f001d49441c00c0555030040c414501240e200030240d8609041c45460b42c019100c44111100348021454404c814120417 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 568104361 1250 568103111 568103113
    0x43806040b031504091a04030e090601050d0e03090d0b06030c06091e012c010906090f0306020d0e0106060807020d0e1c050109120906020c030610051c0f08090f03 71
    0x503080c0500c1c441c0074400545102262000241500d8240d15035800a4403000e03042100300c5010f130034140c0440c1410200319000c0340000d00c1100c88241c00e24100214500601d07041e1740d900c1c2084640c500e0200240325120360010b03288401d0048404598804e001540900e2060110b002a0300780070050500d0100c2c003100b12403044806004495098450003444003407124242d6000c0000d40034103005035520150f06a00995052180f11061800c0181c6581c030390074928283d95074869259154800c0b50000c22130701403d020461904000c03c04500c941c0c01a00010014100c00202c20900c2407056085038050360020300481c49400400c504a03030148038030841038041d828a4a40c407510000051000c40441182c1d103600400080004103028007540444103042e0f12500641010f0070358100038007021500d2240f01e0042c4680704029103241408101d440c0248140940c041200e418541045507140158492640c0e1001445034480464004900c50040502441300159075610400a001c0708509501032180a = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 568105611 1250 568104361 568104367
    0x1a1b0a030c1709100924050d0e030418090308070c02152109160807080d05030714040e040611030702070506090409020a0e060406171b043806 62
    0x8039400415425880b5803140c02c0841c800e01c0768210700500e001d15050244c120f8104520586415006021003040d0780e2804092036221100c2d0380c001c2e20340030041803110300041c42804a40798401e444e400c460114120401941e003010344801803584820030642160581035110b04d55070092642200100b0703000001480c1180307410400340c001c91000c8002805009801c82c00090454107181040e0220040703501e047c80d64403007410a03c80c020ba84d48020040b00e0b00e840c0602000040401c0002441d8040b540680090416880e81800c1550181c0000b40031307005000140609170781542c150002400500300300b100808840c20300781030640072100d18480e60f004080c820024400581e0f000280c5e80c0072618110740841c0d4139034410011502601554200940007a8008804a0a101201c4d612031141606030f41c00c0283c9076580000c0c0601d8400f0f02307072600e001d130040585100841181c9103400e15600000d04003003102200c00100d6208400c0034190b440f90040181e005000b02e58402143c0040380f04200d0309281 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 568106861 1250 568105611 568105613
    0x506040c0e01122105041e1a0a020a110604030807050d020d030b03061306020c1902090627040c0e150f01020610051c020307260a0f02010c06061a1b0a 66
    0x36500d000b500c940754055400c0713110141070714460f004132405403050783c1225195015030f1040d58280362140c02001e05803056494a0380908240401b500e402e007909034000e2a4a4160b134980c82c002c0300948080940003001040b005c800704420b9002044c501e44188020042e8114180001f402c014130b00a40004141c10203008118603030380020299080500201030400c1861140b510710000e1040855114490081c404c03950856102d441213020003500030346040c100c0e40d8030003082003117003007003104240c411022a602c140b44000c20142c82551207882100302c1030f079203926200381074503c40342201d6076020540c10062150841c01c00752140083c079034080c00248040c2c00c0071640030311100e03141d01513240240d880b20b003201050200841c000600701e8001d0255018261640080e4003030482140000764072046114841a03e0200085c00100d0940c114460090ba0802c41e401103405085400c410744100d030700c60101007010200c00074000aa44507210308603564003c00d580704052156000003620003600040b0240c8 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 568108111 1250 568106861 568106873
    0x70611041502190803130501110703031a030304030f03031404060e0c0d080d02070606030b0708071b0809040e03070212030d14010f1401051908180d0210180506040c0e0112 75
    0x43e07841940262220784a030385402e0f10704009804548003038425801d0000c4501c40c0380c2500c1c003d084460081d07038240400364910b01c51700100c0c00e03441201c0fa01684200020404500c40c1010b100c102c5100f0320f0f0200e01c00d006640b201c080d02105860a8070f0040d0f071010b1f811960b040c200864000f0401c2590751258040c002c3e11680000d0103000b07680404030b500001c6140401540307a100002441d4400104411030402c0b103001460108211648008a06042d0540e54240460044080c11942c00140e003403034145403600f400040c0802489021440c44180b001d1001607495500c074401c0c0c441080015a107500c2441820825140500407100302144104010300403145580aa1341c00c6c1c401004502d0000c06413000100d405128000190420811030103105074081d901901d414043c403080040c0c920035090703a41c02640c40707954a01100001d640482404d1070b00024079009160310000c0721811240d140039940780d05090080488040390240425902444007041c41014180509290b04844000c020941d81d14 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 568109361 1250 568108111 568108153
    0x10807110c03100b03010605010912110d05010c030b030610120f02061306110c061206090a0608011406031905070b0c070902041706070305070c080708070611041502 72
    0x82001031010150403040010050000440310190032501400d00307800c0e50f64014030445254070711a5080550020710396101701e4421042d41e42c2140904030028660352413049405150390650f0700b00510940d007402044082c8640018904152004241c0c03824010416081c260b0090803400d02c01203803202844243e0341c1402c007090b455800a0042903810850002034089d016500001c100744e00150400701e00c1d5640540d107400c480e5660303000c0718115001c200c10000c0e9401528003204008056a000984a19110f141c1301d0b000700c1c81c05400a41d49807981034150a40701945100815030368002c1c140310b82401c00300701c107060196180000125080e403d98591761541c030144503041c90044040b540315a1114117002610003407180c0803046540340c0e80c0d40300101540308020a40c038058002c0d480010f50070350180c05400d10076032090b0395100e0501e20303554540e203468200000076503a508050154100140d11445144000c242001445448902c0c00c0030009240e510440c002045420020710064084003201d02 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 568110611 1250 568109361 568109371
    0x30a030c082a0c0a0c170102040308031f0819030905030708150c04050d0f05101103070c0c120b060a091e0e01150f060306050618041806090602041409060108 69
    0x94140e05020a000c440b40303015101e4800d400303014211200040101c203684880c102c41c1200c508400307040c0d900030080d08030301941c80041c064010410014031000502040e1b00d929098510000e1035080c0c84100281c90403031043c0824400c8800c0d04480000c0c0354010f00d201004090440c010081942000082a2280301c082050501407003a180490b00c1c09200d0000d0f02c002d480c001d4609050007103d0309044035181422041916a40a40c07150041c0c002c80a0140030410181c04202c6440c540ba010021240300054490684541da0000404582031900c43d12000040b40612034011150424000f00940c0d076601d5032107a0340c403528080305d400c88550000d00300c0760a19210040021a040b05481040c0034100240c0300392040d4004042c0860002d00c1494000300395035442d5010403019464009020503880380310a07e584690080080801030b2805410507c850b81030002d1418400a0750f5a0304025a0803010080342d40540210341032003040303416a400816807404940740455420098000780280c403014003 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 568111861 1250 568110611 568110661
    0x20408030a0309170a05030a050a0b0f01080907091b020706050315060313050a1202070501020706023f0a08100b0d050705040b160605130210030b0307050a08030a030c08 74
    0x1100c40c00d1081e00c00d113110f0340500030003065039680c41401000300503070b00c112403190401d403402c80031980216141c4208002c1c1d01d800342403100702c83e4038000103542c0078800070f1507200c0b03d200da65404102d0840c240a852a800c0c010044000702c07403c41240a0b040100a4200c038041100620401c0b4801d110f07d0740100f5041020b4400035900c4c0c94440d042c18060100b041e01610900c1001c11120400c102032400c07407003054540c6d00341c500c4140c541c00126140e44140c403c07440141e01100301030038007884c1036403000b0715502c240c2c000030314000b01c1c42c1c0350648410b40311141801070100803c0c0002c02c2e1350000345556001081c1c102240442d407c0c02c4800034070b8019080341158190b50340c80050781250040701203a02804621076000d84440203400c013410445d1388803004a40042c01d1201103011240c501d54900d180590080c400714907000350f800114010900b500340c41c0e03494454400006002e8880b4490f42c8081c040340300241d5a1a03074000005020b03210704009035000c100c102010482c1041d0a280110704600c0e030a0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 568113111 1250 568111861 568111871
    0x607080406110309060f010806070f03020d060f170f01060e180a0203120418020c0a0b0a11040f06081503031902010603140105040309081612230102041404020408030a03 74
    0x400c18000030404940e082c4440380b0004148403407a0400a8114821900d51145c600c1a03a200c2d00c2490301c2d041c00f684d0a0f808106000450380d003e41c000c1e000741180d281c42c5040000c04543c0c98230907500340d030080c3d4400b40684521214004612030b06001c10317044105058000d0100e2803a0003440545400e004042d45503410001d03020b40070001d01488034120740703a0010222018107070160700c055417030341c40f51081501481d201d142c00700428516000303580c441490680178100c1c8150a4480d01c850b6840148801d600c5039403084200d002070751540141000d411442c0585a06a0038450054260300b0060288007044442150801c0d8990700042299540c2130452624a280c0c61081d4083c0c0c0540015040280798100d806605450808158411031040307000340d50342d070030540e524010607894440d00c0c5031040113112203490500910001018003035180d48110400c05c0c02e45254504110a0301105000c00c5d06650001010041c450443c1400101150b04440c210301d8140340007401c82d03480c41003c542006041d152 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 568114361 1250 568113111 568113113
    0x20301032607060e1b0a0f050108180109080d27170d110909010b0406090905130803150f01020f060412020c0307090903080f060303070f060e0d0c1101020303040506070804 75
    0x2a0607a42d05036409401407041d80001540151566002040401030b84070490f0180310707500c0c00512070401c0300c807821402e041017418403004503880e40d402131100032444040a280f10100d142486066502c44c0540140c94881c507184100c6001d68540c5140040303000620700801140f0140a001001c10030303480390042c40ca40c0102c3c180c500d46401484500780c80301b0700d00046880009510402440030500c200c03151251130707803a45005c1e001030003180525400140402024000c0450716445160805141c8080140c0308510703a4231204194412100102d01d522420341d5a501418242c0800039010801d001519105031f8040240e6900d00c40100042e0000390000b038800b0707005000303000346175000358040d068031401911100313200090103001c1021000104203000154480c544c2e64801c5015403001000b6518083c10b07510b170240c0584c0c89482c166030303070303a41c1c1ca611408070002000311100004103615003003009445030800c0a6105901c0e816541590404c10810002070800300f407056008542d400c05020b01c1e04c403 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 568115611 1250 568114361 568114433
    0xe15031b0406150210110a050418020409020409021308010216020112150308130b0702062d0c0708190201050a0f02070f260c0105090d150203130b070302030103 70
    0xb99800f50a0b1104100c01c101d800315404100c0440d1000c4418040c4003410180d070101c081c0d4071600341b5450000e201400244421068101041141e6107071482c05400d02c0c2d00ea000480803640154000481c4590000c2c10b1a03860201d2225040200703250700017141000700159a004401c0307a440f6000b41000304030a8041640d03105a48042000c10705004009144c070b840340350110103035010459681026400c54400101c20080700202c42e0081d50290805041400b07043d0702c00d490f160803011040306100c031a00c8208005210b036001c0c140700400d80c802006040d00d014002414401c16241052a26890491086c00743c1d81020403610064101d24261512810185049040400b03c2d084034003070204140000484035079614038411074000408180c18100c00052403182e48000c82e20100c2c0c041001449140d000c1d161031408003800600403500410204041088041241c2c8110303045200031004d00400f46c00d208605d5109513000c0c41500f8114555415501e0f2022a41141001c55110302c403400380903454066 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 568116861 1250 568115611 568115621
    0xd0804120c0206130e0405071e0506030a02090306090721020f09061f021c110706080c04050d05010e0c06070b01030204110f0307020a110301060e0a0b031903090e15031b04 75
    0x20a5540c0c001c1c3c805e480303401c8410015025039040e5641d00c600d81010031031740c0028010903001c0c500d011803c030400f480d04050014a0300f008084d864150750034000c0200b1900c040c040180300e0140080a80940c90400c44203441c040d01001281c2550342e4507007031203030058580400c2c10020f407000700c4404243d41d4400000550000c1c011005040104420001e11242e0790002640c0454040125110b228401451070480311502d00f04528041a0301044042104d81d00400da040d80200351041c896207810340b00c0b0003064a6052881040711540e54074010361503144824000c03010048002c5440e24a03015560b00c40080090040c0006885680c0d111411030b00404980120340d0702c070210907000340d01c80c90428030107901c2c0c00a40c2e40c1503038581108c030307804021880e040c41a041580e003a500c144085072240d081650050241c1c51407140c01d80b00341c01800c0f000c402001824500c2c54446d58a08a089060a000d00d44142c40a4000390f03a40070070100c44a42c80e80c0105400c0395440944816614010400d00002d014003 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 568118111 1250 568116861 568116877
    0x9180905010902031906050f040b0a0b01230c06090a08180a03060e03090103050a15030609050c0a0b0a030b030304060c0816080c010b041a180c0d0c0302070201020d0804120c0206 78
    0x72049004517912402d107101c8803a000d6000328010401c6594900140308615011540200040202e00006180a40e0b9600c2900404e0062401d5012600c201002c0f40109030b0b52540060401004180c10114000401081d98042d50810140c034103290280d44120090080d9044000801000348204001d5100c51410320003e58015809004118000000a40305c2d03000c0310070180003d0424001801c0311000b030050700c800404241041410600e1911503400410120502700d40500070300b0f0300c0c82420b0781c0300486403000d40085030340565103001e031002c0607045445c0c0305401406a08144001c004140c3c01c88a00000d42d9000072016950b0340c0c409207504020f04969400404c0c0300320104071800e52000560084485400c02d5808000d0340080d03298410f24a4600c41c009540160541c01708081818900382c03080d04a68106442820b06844035043c9041d101c3c20401e05000907804182c0030290343c1d0402402c0800a094201560b032410b05803141a15821601c1c4090300b807000881c0c05000b1511901300300ca2401d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 568119361 1250 568118111 568118113
    0x309010e0a061a03150c090a080604060b090f190c0c0510060503120408030901051b03370e090c042729130f090f020405070918090501090203 62
    0x1d8195440c01d88010507180540618803040c0426400701c9090008402c4c2ca99142c1480c40e8685a44e81507041103940d000004007030300054441301c0002c10100030048940030f984180400b064681c00d040511445140c010107900c0c0982d000428008807810080d6801400000d0b00070101d140c0c2401c500542c7c548000e0303c4010818815485201848042640244141c0383c0490907240494403180001403c3d0085001c1c1c4003942e0810010801550b00480080c0030b451600d07030030800d950b4100c100301c50544d0003c8040ca110303090501c0c00c42c04550309150f081600000c10304041500c00054150061205049565260050b048100031a00c00c04c149010b5500810740080c010359083e04d072074428200e0104240c06441641c0c2131204210000100b00404a0881d0243c001908142c0007501006004000d0310020700205035140e0401078180004e00500035118007611a25090210780e10500080340c100400b40403c02c0552841407283c142410118003101c202c00001040f100303e18140a0700401a0581c000c1d45 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 568120611 1250 568119361 568119373
    0x1031205121f050d0b0411040c020c10031d0714010503070c0201030b01110a060608010e03070f110f0a09020319020a0e0621070804120509010905060715021803060123060309010e 78
    0x4200725160002c0c41b44d4895105059140a01c1d070a00081e122110340c0c10f4090307000b00005400700d003070121008144070041d140100349542100e8180b0842c505603084c0084c140c21034241404a402c24001442c0e101e202840c2c124554602441d00501884003441c0090405840da10002c495078850480e0082c140c1168050300d2001c119845c02000a041c00c0c0301d0a041d950030100007002001000c800d5851854200d40501e40c40c0c0c025566403210200c0403500580d0101d4200604c081513140c100706600070f020034101c0180d40f42031109080c1c21101c11100c10020b07075130040040c80e40b603d5000212003c000c00658040340c07284c555074403082880045080a40c0300e840c10800300030549501004a5015902032111074114100c00b1404403500d11980c400180400c1406000b0800c5080c200700611000c0e0080c3c800d0313420400304481c1c1409aa0244201c04010423024844100301e16003800414010051340c002c5550860301008406501c2c18071036401417044001000049000d4029042011401036080555903 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 568121861 1250 568120611 568120613
    0x19051005090102071203210917220308091c0503120115080114120c09070207091116060e0304031b17010c140c1504060501031205121f050d 61
    0x111075005a0a070740e0051144000000f42207140300041c1001907055900c0080840c801b4200800c940a44440d07440165a03800108001c180210683d00410020040b0b8503500c81c4100d89480c030308541410103561a890a500410000f9500002c80b81030100590764201e0052400f098504013003680301d0301401034000021450f14030017010104c076068402000741da1000b510001e0044802038000d0294117054200302c1c1000001c0c1c9010740940104070440c03411100003401c50004540c10500c140c40140242c1d00010040c420481c0c01d0052200034110012042c1c140080340e4800d00000403440c1d80a80b030180c0d03603102d201d0382041c2401100c01541e00408401400388406002c40c1580ba000c0c45217032000007140ac0c0343d034032000c0c0600644002100e60758032411085010544080d4561014085408030320a0007100495241c6180c01688118001c181c00a0303190700d541411910100c0400101c410040c041102c911603241c0030b015207400c01080803d0b0700c03252009284050003040150881940302c0d4031a500f01c0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 568123111 1250 568121861 568121867
    0x20030103080705010e0f0a03031104090e07180e030414010509060c0a11180f19060e190e0601060503061c05030304060e011109060d021213050d080f06190510 69
    0x40300314800d000800078122250000b5840c1c21030280b44140c1a00600c0002c1f0100b84603420801c8004038036848640340c503964405100850307854841844440d0003803401000341444c00e80c0424a000ca61100a218900c120501962284114016a9014810350740c8001701a4030a1040c0ea51120002d480c8558500012a005580b0b1001c2ca02c00c8070154000052041d40d0b041450802404104210441c6443d840d841150002c0307807401402006c140c00c03540900d45402e1542e0081000400040400d0480c03414138030180c2ca91154a0008a0340d240d09200e448205101c00040041c11607071207180c03d41e1a512907400150303520000c00784c10304003040d4801c2410203201c40400118015841101304012000000801c035003a03c00354840024242000d00500500313043c148014034800c802e98000514198800441200d113890507103180c02c4401c80d0140d18020850200000b5000a8450034420081e1400040c11410390070003c02841c02485041c3d040c106503140020190054080102840a0407503441402 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 568124361 1250 568123111 568123117
    0x10f0e15060424140304020103050703151d100303050a051803060c0d0b030c01080606091311090108012106020901050d2a051e03070207031202070e090c0a092003010308 74
    0x200e80701c000844204000e143c050307415403130040b0243c441c05042d9902c0c0c0d0015001050000d0107075080c0340c0c645203d110f0b5454000e40d14000b80c4121800400405922041e091a040c0010801c1114040b2003606102094001c82580d41c1b0320b159107021952154228541c0e1003181004040a40503c01e4506112003100280c01604034030406400c108000101441010354440004130101d0100c0c42800100d20541022030013402c410710050805003071280300b0034000b81212a10910108031a0003c5100d0340c4a40e480101d40d4014142d50b49400003020060300000d2000381d801000400c1c030340e400a0400451707405401603503103001300c0e0282080442400c1540d109400c030303003280068051821041c0741c440307613005c0c41c21360384010104000e4520360302ea402150205580302500e01c200f5480f40c108000001042e42c1000c3c1043d030744a0b405085040d160044007440418007070302403130150b0010f5048034625280c514003041200c2000f1404502014001908208010142c4440280c06400000402800401001 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 568125611 1250 568124361 568124399
    0x20901031a090604050c090306010b090f030a1a13080c010501030611130b07020a0b0c0313170d0f20010902031212130312180b010509010f0e150604 65
    0x24030900c200e44480600e600e501010140c1e208a103200440c0f203034181540700030b91021040c0d112511749010100001e00d000001d0f40038202e00c0b040000c6508507420107419a8003103020640081402d0540b13a5130f5034400c0622540c05181d0b00c0c00020014444c0d03002101c0c0e0240c03031a00039400940c6c6504001241d4080d000c02d01003130b650f0ba400c0040301c289486848040710102085d80d030f500c0309aa03040c9411101d203588540f0003a41d02540201d00858200003c40050100d22a540004c0d6999602c00d02c1d440303640e51050748011101c21406010100200c2c2c08100680211254030700b014516510540c140d80035580003415812050304c26010b6031074510150700c144a210f008030b04481d44400105800c08e400d1040001011480c1c0309a070204605201102100700903d10070300300111000c3c00c6020310800c0b6092403a200164003403842038402030010714400107000d0441a03076000000d40c180740e01174030300b5103103403240042c1010314400103140030a08244034000504002c10342d030390300c3e551040110440c6000890f = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 568126861 1250 568125611 568125617
    0xb01030f0f0213230709050d021f020303070801090b090403030b01030912020706080108070b1603112a0a230a0f0303020f0d0c0c0b0a1206080105071d0a210b0406020901 74
    0xc0b007800711100c2041051190015070744241c1c40301e01f00814842c03511811007080360007907095804442402d0326403441d0102e2107915801035840e8580700d980240341c82010f80c090b203081490b10702c0c041d92684801351203660140c0c03d818003040103071030640100c0050081c200d015003a014001c1010b011542d0210304035084800079035400c4a01e90300ea41040c4d85500c1e09101d0304026000400413040e817002c11181072075500d070081c00c00004140500b5251420800d03951001018145400708200e0016650021660b00c1c040c182d640351126402d240b50748881e0112030220043c0181600310a95055540701d04460162003038100ca034100c27650701c0c60301075928000421b585040b8014156070b0300b051440b600240c141d040d040404d1020741417424003400204e502c00c903c200200302e4070b00610303821401d46010304001000100000078140c9021a8001c040070480b007206180f05400c080e000b04281d68000f45402501e050700c241c84598800711800c1c040303c03400351200500130303490309007000280102a40907052442c0e00f80c03 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 568128111 1250 568126861 568126901
    0x301050c0a0f170103110d08041527170a06111201050d0f03032003040f0b0606040e0f0601111020070f1101030204050307031115070b01030f0f0213 65
    0xd0701507401c00283c400040d041e50508004101041814100c1020002e02400d4040142015140e455903940071b60020b02441d0f42d008001d903ca039074040c50103441c01c0220416410310349c04080c600400041d0074841d088042d1078100c81c9420f400024084006400e40c4032204110060348510b81c40015008000c3ca10030070101c800c000070301030404c81d4420180c0c607804428620300e10919907081c1c0007004041910703640000d040c1d0503c0700c100315410007180118000e202d0182c1d00341e0136150405a150004140501444081c4030820070041013080da00d40101c0110044c0500e40c1d20800100c0302c00b11900350000c3c8a10035540050992542540320907174070031a444003103003000074901a0301d441c2d00c210f0a004049000d20050000416040300006070b81400500d13001d80303044d94460000b440c000329600300303490400b500840c800152405aa000c09030990710321400b0300302105a218510b42000502c4058040800450000d08201880f01401c0140d80d0040400d80b6081001c25000000c154103080d004100c5200 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 568129361 1250 568128111 568128137
    0x20105040c08060c16030c0c060c02031e0c121014090d080c0a0804050a0206030c0d0608070b0405060c0a290f0c09011805060d0c080a0905060a1a0301050c0a 69
    0xc5071141c0b240c60f9460030340d442c10a01d0041c407844180c40f00170582c01c00184040e81d200051600c80407030020045171344e0308011003403503004150030b0a1440072038200243d86010a0f072224080840c80040003001110b000c0c0104d40440591800d10030034003548141e03a450300f20402c40c9040c400d00807901544045040b20081c401e2110207035602481500c445020000c1405407040c05071103044147d500a105605590040240b5030104009400a039a803807000c00010841e00c0d6884020b2140c0c4000701460801007000600d041c9600ca400e00c110f01400f40911030024041103009000c00c9104891a4002030400080c1059205c0d100007000c03007034503140081804008034070040c00d0603540a01402e200000030f443c0065840054600c1c24044003c11580161035030005800d0391a072003d0400b09144035400704a000405e0801001808010945103840d0b150202040c0414000034026620000b0440005905c0c14020503011480c1c00d00007d0540c10360a1030100074080f00d4070006014200042d0b16102200c6481e = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 568130611 1250 568129361 568129363
    0x81e07060810030f020f130507030c0206060609040509120309030a030f02070215090109030614060306011d0f150d03030e0c0d020d0611070b150102100603110906041b020105040c08 79
    0x756004004202e0040d401d00100300d070302040145883c4000d024810342680907000c00e6000101c0313000c08424941e0b4004008145030940103a4070350101910203803c0318500a00002d809028030440e503400380782e5440c002544440108203030b00440d24080c2d0349540381c0c64503141c4035940b42e1000f001200040c0c00d118216103404103e0081d10861a402440800c42c2040307c41c00300c500d500141c1d001810454800030000104165100c0c0c01364940c070924030885141b41020038035140030410b0307000e800000d40582420903401ca0806181c0d41100a203010b440e01c549a0b618411202c00030030b0415070b0b0100300140d041c4c0030150143d02040c1c070b4443d0f5005503200c18400e5403c00c85409405440a500004014100c0000412075446090900f01c9510414182200b6031034602c2c03a00c40881e080c41c1b0000020314a0320466804200c100050b082e200750a000042c10341d69005080c0145007401e0780500c0f15030713011490903682c40d001404074442c540420283c079021208000d018060581e029074200e015014041182d0030 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 568131861 1250 568130611 568130627
    0xc0603060810090201030b1924020618152403010b0a09180f14010f0507090e0402030f030d0c11070503120a0e0306070f021504030e010c030504081e0706 67
    0x80d4031000b07881c030b10210452040c09442070100032410556200d29900d041d03a241003003600300409444003001c0181c1003103070191044070203900da5100b4405c41e00100d8946075000405640c0922040d800c1300c40e159040c00a41d160600219807140c0707000b1004108a2004a080025201c405140d44258100d1036410241400c0300c0210b844580c128080400134041d454140d08003001520941026142c0f6003801e403100020320304108411500840c00c88000c8003c400c00340a503442c0307000007100c10440342c1080d030405485030400b4814611034840503c009010f40d58103000b4070003d1480306003660340d21110604401c0c01130150442400200c5d0001103540407011000400c0800d4074005001425020529513450046401114180c020458848820f440301c0d142409500e0240c00c481c0c488050503030510390080c0c1080041c0502c200314040c0402040082a0700c00c22540b1203603001e01b070550b11740b200d600303048a00384100c0c3c01035145442141840c41818040c04a00081c0d41e8815050702c8021341c4a020031a0f101c1 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 568133111 1250 568131861 568131869
    0x30c0f080408030127020309010b030610050d0f030519031d0304080d08090304091503060f0b03100b0d0204060f0e09060705091e03160e09070303091a1b06040c060306 73
    0x1600500050210005010340c5d0070310300c12002c076160091160207035a401aa1b2084030040c03e02d0351180d0303107024242810441242c02200d007088d107002060600001c12003000044030f010740f135081e45139400741c140b6020340304076103181c03030600203102c00c0389103000700a0060040c2c41c01c0361495501210141d4001200070042e64207441e44400542000c00c6e40071000c9521500103840005207000812000844040910460003204041224a0146890350420340210340b0822034a070103d0b1b0400f04020310301d642c0456100040f0b00050390010704409171002040041e500b400009400502d030100105a068040c406002102d055003112049a543c422807241c8905082d124000860b00520250707241345001c4400d00c3c04152070007015034640305094000303803034100d03562456030404079000b50038451494085007803036000c05a030005054091030366400030482c0c0c045105004041d03260400e03610388061281e007128042c0781e0350032620322070160000c041d40d141e50301034400316040a2001300c00138580c1c0c000d010b500111 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 568134361 1250 568133111 568133123
    0x1302060d02070507050d0c060306051e01081f082b090e06060d1410080118060b0d060204030503041707031a1906060504140604080a0f05150106030c0f0804 68
    0x864104000c00180d08406001c45a0380616480405c0750b8803000c00200000b4010300104036000c2c036010024003210700c0c83d0440c0f03000321142d103444005d00d1441031118072046002e29000d9225070761030849104452245c10466201140300000042120001a0030341c0c0d50b815404003005008a0080c0d0040e4007280030781d202c4e002c103140300030400c0034415040311540d0101c4094070f554a0290385d001500122071508410003080160300c801d001c1c0460f01c01c285803025206000080000c07803600f0400300181e40c80031600030820758a07542c6450007078580858000c1d0b901d50105086d501c0710703164940103403260010b00801c00200314400341c0c01c118240c00202c0b0401c41e03400840310803420303041d498100d0305010024000c20460242140c000351507603103441650000d000a44c2c8054403242007012001c603100c518900765101d22000d002c207011107040440c0700f05010758804045181c1204030320b00340e400c03c5440315540081840c00b00000400030f40541002d0b07040708182e641c9898124640c8d6040d21829000d031400750070 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 568135611 1250 568134361 568134367
    0xb06040f0e0907030f0b0f060306242409280902070807120e01171e090715080402090a090c030809060c0109050f0706170601050a030915050f130206 65
    0x4218038144001d504400c0320416680c09039200c0c0c441440e00348820408403031581c082e504000b84806040f900729084241140030f07040504100e41d0703034500c0ca0030042e00302185495407051009147c0c1d0700c2800c84011407000e40151030140c103c3e00c26814540001c1102806080300c0e0b500a500300e0365029298030320082e0072248038001810000540001e410040003202d80c40c1d010081c080c0828034203802d4119811859035064100307840c9400041051548003640240ba00140b03041c400048110294400909500414a4061760300d410301e05140480c1a404038910029407420f000600754070140452090f4000d451a41c0981c94881c440e00842e04100b4029108a059903c2400094110001013030350200040c440c600b003140928010b0308481e128070045443c1c0d444080c0b44a0039402c107100c0a0028001c0f820301201003104203a20448441e0014079550401c500040c505e072a080c0a03a0080d00b4150b0800d140001003074240900d40001d000603105001652400400100b9a142004640324126405809103003 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 568136861 1250 568135611 568135619
    0x25060f0f0c0303060b031501030c03020f310801150f180c050d0c0815030a0308070f09030c1503062301110a0203010e060a0e1b220507050a030b06040f 66
    0x40ea1a0072071000b10101a2900e10000e4000c143c40302440c058021945500c2d481c840d0301c000503044909240505c410301d1b0062121006265011b03060703a440c0138032050300c20544010705800c80c1405010780c001040000c040b00d0003082405055004444c41000c00844090b07185c1c69483c605004031141c4964610300c4459004421041e00c540c002c041c0c007a0150803c03c2c2048070744120007058844004920780040d1140307080101c2c07210003854001403a2000d0340a04011501070301c008098480c028036400c00e0056003042d50366118441c814020003983c01405080756203888130410000282c0b20b80b12040084c0c148039010440703429411081b40c0307040000c10380429002e584001501d011003800c1206126005841d0035a015850038010501c0d80603814018141c3d9142c0b09070a01c0481b40341101109a0703500a00100b25004803c298058400b44203e6003c01074000c0740c00b40702c01c80d00703a41d03003200040c41c1884d05010700160004040e144a040d00e403405d010240007101805000c3c056480740540da02401e42c4104 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 568138111 1250 568136861 568136867
    0x507080d0504030c2105010c020114010914070507110a0f060809060907061107050d030215180312040f06060311010908150103080c0a0c030305090f0301050f060105030603070825060f0f 81
    0x7400170700100c450300781341c01040d44850703084441c4541843c0140c1d4403070f0340e040144450808401c0c0584451741040104000c07040050176801c1c0000c204100303101c0d00040083c03d0280b54a910708a03010700400010040b5101c103c58880100144600d50210701c0700008515080d10211f015881021061700620034145802d0081380e14088102081500703014103440855180c0720444c15041e200d000c1d400810780d20034401c0440030351010081c8161000444804e003802c7c446808030403513001540d06050b140030f54807503003060310081519901c02851a80782807400010001004248031390450240c07a820050380c0d4540909865030404542303600100800801400003c0103440500366120034002280e01c0010903a60f24528448190020307008158003203030607001071610341f60040060005034028046420708510000350700001415041c144400400007600c6030f2010402c20000b041904103c0d80340614000c0c0900c48040340710a0034043d901c8211002c17801e6401458800c07200c0303140d6540c040061031120021 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 568139361 1250 568138111 568138139
    0x3020a02100b010c1a0f0606040e010510030b03100f050a0b0a0b031f081b0a061b020402090303070b0f0703050907091509110c0f06060d060f020c03070507080d0504030c 74
    0x6410302c0304400e00d10021175102a0300700b20500c03103181e501e021410321960b105100b4038001d0485218000801c018000c1e85001d440d400d045075401ea03006040ca40d02d0141c04c3e00506014121290148162912003c000303a440c0c00900c020740107a10100110748034500041c056400e80070103550001d15402c000c10582040a00442d030012900003e44048110162400c0310140141d0042902d90b00c1540d11044040760120a622440710171140c0414152030000046c2000344212030011444090030024000d54a41c0d80448440101c0141982d40d00c104da40303400d1400307280545e0813420390341a80c00000d03c880c0c081d2003254004c070560030042c414a031400201c8400782003031800300d0380d41850382c15000441000c14090350001e01404080700303403542c030100241898004583c200d01202d50041090200d283c8800803034944640c3c1264022940190301e5106002910032040c86111502c07000408009106c404a1020251001d11040c1d6030041e1741c280c0c0c11102030045010251860580e0002046003060500603 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 568140611 1250 568139361 568139381
    0x4050102070b01031a07031515031509141003021804030c0c060f02060f0123040905070611070605040506120a0902030d0f020106050402030c07081c09050a06050703020a0210 76
    0x94a40700a03992500c82001c0c003079000703c4011408424205092410b0840f081c1c0c00091860308105010b4200c5450800300c120784900c82801201030f40c101d5803244240c002c004a03050202c1c500c1c0030190365180328001001a2030390081d20f80c43e110b000c07890148a40c10050100d039001000411012038190075030070741100140089043c042a5400d00340055901c1d00f50320024078090b20f41240c54002c88401034100030009107000d8007410101d00512032440c141d03100c141c1180203528803085172007040b130105005104907a005445449404070015072140d10020706038400352403409032814a981c0c1c95040d6001c0c0210b009980d0304c00028061541810b800e0010643e20469174880404d16040310b0700400e091a0030116840c001402c004280031074903409000e400d006100c01c0d80d00f10315514024420401038044c12000034000c0700d0018603e01403561620450b0807108090700f04000e15100c070b180190b9074030141c04049035998141400100013034040d1080d541141d03280e802600308010503458030303c010291084 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 568141861 1250 568140611 568140613
    0x21e10060e100807152a060203180a0308190f0f0204031403040b07260705061519090e070f060f1205130f170d0207021e01120b060d02071a1f0e0405 65
    0xd000c076065400c68106d540070900419005940781406003010140320600100041070307510681c25400002d0b40318004d81da05c01083d540d0b80c030442c0081680000a40012501c0800450030065440c42100b0a41d0080017182d00c91071030540034140c0805440d890380941d01c21151402e0060080b4804a00c000e80382c1d40412007207603400310080c15038544594603500702400540b4594004030400a1b800088003600e1001401110800308a0300702a91820120710a4000c3c402c01c59100c1018121543c02000f000010301114440409240d859810003001d1201c0c41000c1d02c0040c41c1c401c12010b13032072001d201e1540252004216119091800d8551140614a115040743c603410140c038128a003440c007601901030b90b42c10707400150343c4088600411202d04020790321100d816420380240c51a0342e1b08803982803411041c0030b4001c5400720021000840b5801000000000750b400054010200000d00402001c82d010800c1485e41d141c40b410451036000300101d004032010005842e0501161810404440d84113120354 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 568143111 1250 568141861 568141907
    0xe10020a0318150b091306020f0705071205010614010801050d03021c0e1e0d0b071404090915060b04060c05011503060b031b01021e10060e10080715 65
    0x3a151801508031018240c410303400380d19680c0002c0303242c0e0280800245041302c41c4e00c05d60400103600c3c0c4c03908480000007080b895001415044010540c016a42d0706c0d074020040d035034100e5841801201e00048030034100d400307500c3c0010118518220344d4000700400c0040c5c0d00e040c10fa80c00d100c2071105070302c59808103505601c906030a441c2c0803080071081703246da018039940b4030754046259001d2007085051200d01c00841000155800110b49841448280c1b00707030000c10000c000d49078108145e84080d00c4260412201c0000280410719030895040038031035a109601910b504141d4200da00e048400c28010f0100040c0304000821035640312b040d8074603000f8058400060744000404200100c680b45501c12900940c40d03401d041c01c0c52409000c0100d61843e5103102005001c8001d00007516801025451003029078514054520b100e0104405204244044c030104200b46e01c0d054040142c040403101481400e204c603401203200c40000c06d0702c0d001c644400d185000102002c103401e8803200c8a000000076032080d04 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 568144361 1250 568143111 568143131
    0x140c1501170d03090b13080706020c06040b0708100603020c0102090d061b0f05040b030a060522060f05030709020d0e120307030b0d080d09030e181503010e10020a03 72
    0xa1244500030114808449503224070000c1c01030824101c03142d02420b042c40d0030b50f00b801140b00072110551001000405100c00b1465107400b8106009640010b000b1324408951024440c10010b00c560081d4006c091041d05642c4a44040341c0140701104c4d400440d0680d04001c114a50194000d04043c00d100380000d0304010484000c240e05855136181543c6280c0c480c03105800fa1040d20041003201c100501c0d0480c4594070600b4040c0c05c81c0f0807440f43c0c1c000f280380000026a15283c5a21900207404010a0340c268a11241d2040321401659100070807030500c1c1c2040003079008216003450040701c202401034030300107160000141c001e40269107075085c0e040e260200c040c1143d100f030001200040e125910161a400c0442c030080c12201c101c00454080c10741c42d0900d2011038032120a407010030020601c003103851a81450200e410101c55402640c10107034842c83c541c13101100e15140c901c246103561030308040d91100340c02c240c00c3e0b4032040815421508038001d64800e20040e60002c0c1410002820082145130030 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 568145611 1250 568144361 568144393
    0x90907050d0f1202030406091202030c1c17030105180901181a090a171305040e0a1104111621030f0c033e040305060603060c0703140c 59
    0xc81200712400303401d42c03010b101000340c10011001c002c049440214109030600718007421462003800707400f0300700032501c00500855504000c600d0104001a100a94031284442c030280c0210000d41c2c11a03038100e110b8110401d60040d001034a04030303140184080c2a42012072010118612b000d0301a0029540300d10f40c5444a400000340c404005105544030703280011360300400d80101502400311170290300722045840105814003241c004041e03500d100203586200780342108510703c0c01d940c0090b40090600f40200c03001c50001c12000100c6029129000080309008200030443d803500c0490580304c00180042880040f610f41300c5010359124400c03100145081c4070160954091420020001a48410208103125118025034240f10010b04042c8041d500f5024120792503990b03001030220488107110152040c41501000445049180c68119501d580341c2c10030b1515048100c4481e8061710519005c903c1c44000342c2e080f00d00003a0541e8074118400320042d2410f0203544041d50030009445507503400300c0f030448 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 568146861 1250 568145611 568145629
    0x4050603060a092603041b060e060d0b03010905030a030612080d150803030a0518030c1b030307060908070b0c130e0a0207021c17041d070c0804030c060905040209010e09090705 77
    0x3080e030080c0c5d440f49000e15141182c400c08298200f429062142c0c10000b69030002804070720454210394003903d40c1403e070400701c02420480c0010340d1541c2000480f41c103211020004095880d0742c4c1e80c050145544070b06d180c418919201300300a00300c6000f0044c040c4414001d03485400700030074280501c6202903803012002d00d141c000380c501040e51a40c44060102c03244a0004900d007660703c040c09141007682b00b8800e0360f142d01e032400c6944800c1d030802d48100d41581c1c041c802c0342e40c0154803c108000c02040d81c1440b540980226204a8001c980b8201140c03540d2406001c0c4e8001148440500c900c50b401c1c02442546244003030520b4401540178069500141d440300380603440210301302402594180d4500b0f220515810007400c44429060810081c005003810500d0705807a042d00c0c03035440542d81c4070b40c07104846c18814140c01420040b404200881007101380c2e40064100e03a11551045501601c4004110891041151803030110740c0b90002c5100e05d05104020340d6000a1000545000666490115031428 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 568148111 1250 568146861 568146923
    0x4030615031b0e060a081525090f0501021911032a03071707030308041e0302030a02011a0616060603051e0616080c030c04030804060309020f04050603060a09 69
    0x841c050010310403c034220344042d038403a40031034140d1140e03490300144c503444400401c2400d031a2410f01e000030b03011284402d1403803c803c011201c1c0c02090246030000602d43d4106000d20440400c05110001d020f40c03001030124408410801e11303406000e0300781d840012a8801c0020203415000e446c0040d59200300018502d4905944501000310000c01b000070182404c285400c0382c44e403a50a40e0b03008402110010f804030980e68181004201d40c0c07a242003036850402c4942203a030038103001034414070402d64040060603000c80160000d0105402c220b6011120816241035150005410711a403140810320103001152107002e400001940c2e0340340d403070721810107070f00000b018022280c00a000100312403c104140c3e200305140f0800004044c1100010700789000500074010000c00800441d202b69510000c4800075540821050f0f504c03940e8070005400340c038a4420681c8a01214200c0a13074504003405441e2284034024040c00f401d0396158440d0b00141607200094071030302c00540400c280400c414000e42414 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 568149361 1250 568148111 568148153
    0x5010506161e0614072a06020403120309031106010810020315120c0a050901050d03050703170403030b0112050f0f0903070818150a0507020103021b011a010809010204050102030403061503 82
    0xf80030130b00300c1013452a0081d040d40c1c1040542140d2900c2d03c540b800300c03040c40e1825807144441c440050301b8814040e00441d00040c0030b04234000340741d44102ea050342c0a1540360348251210b405040200c499180c55510034401c440c00c50304142088031010758141e0046a11001e04020f80c03d1401784d0402240c81b41010745040c050603400503031441424686822003100404003203400c4141d0358100f80204000201c204401002d026000c03909100700340c060400e280303980045440c0018240340a0600401070100044818007160211643d4141d00071280a000e11800039001081c401c0d8841243c1041048001485801070b80030a00104000400e088014190b0030072440c54820403215060400c4160540345410f203142c444200508045140c019042d10032a6409082c0141c8682c0d099101c05107031684018107000d95460724141310004884040031070510003080e80c5951035940c40c81308403801c074810b40c01100c1c0541d000f4041080096500d80080200006115001036856600c0c1e44030401003000460303082d25 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 568150611 1250 568149361 568149371
    0x307052508031218031810050708120105040615020c09040305092d030d020601091e060602010c02010b0a060c0b040503040911190503010b0f1303150c0306080105010506161e06 77
    0x141e1207101201128440b0f00300590310b4a04a10301c0049010006c501030760141f401c01c440002030034001c0003a40c00d10f40d000000241da0b00c0c400041200929424001c2a11aa10b04a0003040396401111040c0e0301c41d8181d001024403190364401c100918030010f100714200001080445040d44803644148005840707101d81e0002da9201800c0ca890148078022424002c7d4800d0408450240d400a001411181040c031b000804a40c0f1411041d11740300b50601d1889180c1c00d06500241007070b8158800c2d080c2c00d81d03550007003142507600000c0042000c0c00b403140200154900030804049040100340ad501f19201c1c1703040300d00d400c3d5030300c48003000d448070182c0d507142000010540611409140041c0701050005191113843c2d5070601004070424007c0007071700c1e01070311f00c08036007410801d01403079142700519040960590501d41e00f14019018150400400300044d0401c08000b40030f40050140505031180100310070f044c00d8a150b003c0303040d40300c0d105c01654600701944034969030a6060002d034031524014200428 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 568151861 1250 568150611 568150621
    0x30b0103062a0c03110d08041b12080301061814100c0f0b06090108012315031002031b071203090305123408160e04060909020f0303070525080312 64
    0x1708611041c0d5801c0c20b1500310009220303c0d41da00115603035026a200d113040a040c0c21101952503075001a030003103916a15003c02d01d03401e0000d030b039000e07504a680c25038460b2504500d083c1c1d80300d10b0011900c03400b80d042d00c42020101c0c062821208444c2c112905240001d012202a00c1d14201540410030036100c04c91160240149070614052503805003514034004d02c903040c00b00c00d4255920706040c0390510711052910208070031848903d854902d0b5880201141c07000e401d4805804002d40c01541c0a041515007405501001d0b9400320a03110002d4101001101c0741c4440031007500584040c0308120100301c0308101188018205c410024011107401410800f114088040151420101d04440f0500382c6c110141c41034503503000250b15030022540307910a9034a50041e03070a9607030400c0d061074580d12500b044000b1a02880f43d60200700c8042c000c61b0442c3c0450030710002c0c15140d00c50784e403000d46280c0144502000c1403519040e511304048441500e00344180d07603203140780e0864008c41783c40360340c1024407402e09c2 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 568153111 1250 568151861 568151867
    0x619142b1b08072c040c1b0b0c0408060f010503060601030c05090607060209060403060f0c0309051b03030f0c0606101b0602030c0904141504062904080304030c030b0f01030b0103062a0c03 82
    0x10306e00280d0420f402800741410b00d405a12100f80c0005140301c420744001880701a082081c2c0c1d0043c01c4860455030f56080448485c00014002d0141c00d01034403405000407050f40c40307030080e4500288039480e424a0404c4580c24080e20307601a0400380d908076001c0081c0591900c40b2002440210300039000080d60381042a1420150707080b091080d010103003000e07918004520045500641c05045404c0b1840d04180343c8080303421409203c84e4140e000b00080f8840400d03960100304284104e004032000804480303402820341c2c080030840b4144120100c1100a500055111f500442d00400820000c6040c005544001000c1c0c41a500fa43d011400214060240544480c0307001c075803104046500740300e042d08024401907132030204480188003403464071015031a03401c507404441c0641617020503299502d480c2e091181e40b0440d1740c4000c441c40020600050400864408041c0c1a2039019509445a03441c1d500c800c405850000040040b10100d1010000403500260901c400103070252503c11540c0c0540c2130203 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 568154361 1250 568153111 568153121
    0x5030319021213090221161418010c0c030507060f081e06060a2003070b070e0d0f05010b03060a0614010903020619142b1b08072c04 58
    0x880400c0c1840f0107003c1c0718401d40081d003621000e6000584074081442c8003150401c440c41e9164251840000b4001c01413083d04c8100e040541d0f680320030101490601ca040007921070002c60016000002980300081d44c070949401c120740b8081c14003105000d4994988504000b000d40c40700c80880c1840142480300c0780c02c928020350103d6010b0b02100d1421800c5590551001d00420141c45a0000140d0150281c010032a200320726028548101201014245845d031340d9010380810345510144200086c20140301c1c2c054800d8509022300142d0b1100301607a21560703820074201086500e0754075900622010b48042000c90700c507449032140820014644817101213600320350341c080e50412042040c1030025071101e108540b0030f90b0046481202080c607480040b12540810780710544a00d500044407a00960f443d00c200460030100c001c10f08010501e00c1c0d8510444540d0300011026161440d801041c8902600419900040505102c401a464080f04103d40c10340b40c03000c050001c41d054510001c0742818494 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 568155611 1250 568154361 568154383
    0x80c0105060a1502100506010903050703080a200714040219031d0714090a020708040303030b13090201020a030809100908041406161202031204080a03110901050f130503031902 77
    0x800300f48034011000b5200c119041c01300400c6600d0704007048099101c0ca02c03003401180c0080c00e68a040383c480c81d0185141d880041c0180014607201c0703101e501c50080000721040c88141c0c000401c0c1007485c100c0003000d02280c4901e6564055400d0054001400510012042900c55507900003811114002c1c482c046420070781d604025503100010a2000480f400b02c6000d0b200d9044070b208045a0711058910041d1090303443c01045c504002c60000105178058204000d40b80048815001194481d51240111002c41c040a030040c2e028181f004046070041c003869030000b2000c41502c400d021902181c1c070944241500496661200080402125182d188070442c00b41c001c0728a9864007000b110304034902c048244014003074500100c483c1021070700800032680c440e02c003944240040e1600e824140c025800200015000c00c3c10141a4841c80d03888808030740c0d014105840b644e00b80050782c0050ba00c071b600500079890040400a2001c40e880c0c0e0104081c140d144080c1c803000450301002c1c50000c0c140941214 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 568156861 1250 568155611 568155629
    0xc080702130c02160b0d1806090c1a0f03181501080a0501110a1e050910110f0c030318040e03030103060204150e0a0e06030316050606030f0c1003090c03080c0105060a 73
    0x54140071640d4444100d03000c0c800fa44038081540400c01f140351000c1c401c0440d00905a500d080d01d07000411441008000c1118242050005801101c0059808910881d10b000f04401003c00000d42600c3c10003000c1403039094106c0071a485824205150103110400b0b8005609a602c40301107841041001d00400301d034920540c070030b00c0c103082d00482c0c00382203082c20300c24140c3c0c908810048804207034411003c1d24007804008080c161080030301c0380d02500920010081040b580603400c2001046600020521400c0e10080c0c000c51502d1a1681c07010041000c1074101740d480364640d0340c401116a0104091800386000b01401a03603249040740d10462012030659800600451054000d02950740701480000c0380d8401800604a6903050002401c512940c2014811201011a0007043c424002482481030a0070f40c1103400350000b0381070965603004292002a4010003c100f00b003041c62203a002003807018429003540c0c11158803583e4910b11500f080d1240115a0b544008018940c5440c1c4055801400001 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 568158111 1250 568156861 568156903
    0xf02040302090f1806010e0709050105030712020d06080604081809160c06020417160f0e060409031b060209190b48070902040e070c080702130c02 64
    0x5070100300300302c50040004410f00c10800c00a012020419003107124031a00106440c0a036846000e480ca1400050b103d0ba00000c18103180031609500400440340510000d03192140c185580100c1c001c080d5200c450201c00c401c2d15440b0024124008020440c056403080d500c15496803e000304820813103030f0550a55108401d04014003040e815046480c6006500700d04d03104690f8609414240040c0c4201d0744900c420803460b0511014409006c0340d0340b41d0024000442d8000340350f8903200070070322072118003c02f4000ca2410020032180d203401c4e8015601c0601c42c2c01c1c119403e90513600c1001c0301c6900e00f03d06803005078000401e08180c1c0307850180300807000401070032a05183d0518101c1c44a500403143e9440b48151540e200601d08030f4071202001e115000001c00014142c1300d4140e00b0030040c0100410010351049100100d40c51803140251015250342c410004216510f002c0c08681500c424003040d2071085c2d042060310050b880d40e04001504072080350f0040b840c41e1640c0c01c004d15010f030b10440c18031030706100 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 568159361 1250 568158111 568158113
    0x620211809040c0306090f170d060f151805090c120a0603031215030b01270902030d12020d140f06010c02030606041a06181e030a03050f070b040b09010f020403 70
    0x83d00c1c0d40d07400d880d0041c0300000e01c2480361400078400e1365a85400740c081811070481c818400040401802152107240060111680d00c07500c00b10f108081d0f02449100d0498401070b07c0800348510328040c1e0a12244010300c001d142d0b84da02203141403205544400b0485000182c400c003031750050ba041d503048410140c00300300c180d00e1510020041381e00c8036000300d000c41c1c8510450a116050075500300141d501305000001d84c1d40c1d1031000f00905883c2031442d51803580c0c8a400d4609015051054050454014010340b5481c0106038044481958a00304000c000e0b600303009180036501c1900c12802065046580351045007042500003800d07040041113241000408014040107031404140b1680140051794003080318207444c40c40022100744110000d40200d03000c24407075240904140d00b65030b034030b2007079498450107160540c8114100c0040f00c1095092303446030440f640060b10520081036419800e1035a24100706090b9540c920145040d0360540b9106403913002d001202c1c2c020720a0040ba4030b040001185494a1 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 568160611 1250 568159361 568159373
    0x2010204081e03030714070b0f151210020c1005040507171906020c0c06071208090a030504031203110a080613230a0e0d0f0e0a062021180904 62
    0x10050640c820006d80c41080004800391300b0940c0c3c00b003030f8008050440c51501010a1447c0c0c001141d02e45900e20b082c004200d400c0c100740c44000e039041e80303401c040d1002d250500701000c00395200075036940d800e1180110b070741d251004c40d2160900551143c13000d40030052400c24a0485000762010640e8150010101e91114440030300d020081c5561001016845000804869082040d92411260003d10024509c010000920089000c07208181c0365110710b0303142d2038500d03552540346540050101d08104420700102c1d142c004010f4504809250100f1132603120701c04a04a60403c01c00000421440c5040c4074071450602a40c14840402d508100042d1300c820420300c8004c031100411040303044007900844c4642c14180c109030b2030070264104580840b45070760001041c1c860503400d00400a510850700b0340035460003c101000710707815903440300491402c0c007013004442038005c011303081e56100d6150501ea0441d80c02d000e1000880400003060b4881842125420103803511050741441840441d0410000900b = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 568161861 1250 568160611 568160617
    0x7033509040b01120218090906160503091c17070806010923040509070303090b190f090e0916120209040b070302120a0b010e01031a15120702010204081e03 68
    0x40700c000c91034000210060340d1404242c811840307020b00000e40360807203040c0c90215030110203003600d01d00050740e510442151206801e5902c15030880524460414151042c3c000d980c00c84018404d5540300c4140d060185020000c5008900c08181e01d0415620100249601150301241c1c5080100c92842e1180c0000c004820600496404e9030050200d0702d020031998500c02078507030020b00100718508048089960310000e0784800c40c0091030504001c1801340c110016540c503607121510220195248030b50a0312100d0720012b03040c04110188400081d03d0b007a140e00540a410a0f4016008148003511456000f00076500815803c10b81c2200714001610348121030f5510a4011241c81c005480300c50044019100d000385064100d030710304060104036805a485505914400d1f00e1702e0b0028020800158143d8030101c00c501690500829140d01c03504007011201c800070b035030801c0300785495454031807000300440590380280181c2d070108060088490401c40307510340507217210004c84d604115603000745d034a00c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 568163111 1250 568161861 568161877
    0x15090c040c11010c170a021b0109031709030a050415230c0f16090b0102240a0c031b031e0612020907022e020f07120e0d03050f090111070335 62
    0x7d5000410716244440350031034010006001d4001d07c0310b00220300700108180816205510b641c48180b010075001e0000100b00c58084031326490383c0342414a040c00c00008015120f07082000e21444e05803040d03444860140220782001460704194544a000b00305914210712900403226590001c2c1c001d01802c080300c40004101c0e00c103043d02040c51a0750301c004034104185510944c01051554400044d6001040300d45031080828900800c01c0704060182101540e400459503010a030352803500090280c0700c0c4e00141900b030250030710020030324001c4101204859056204811408a684c20a401c51411070101500180144010064181000c04803503c545032881c240840d01c0305403007080242451a01550f1202041d041b800b6103480341c80c10442101550000a01c0006074003903081c4805140c5551484040c42c2c040c0d550f507003440c01440509480c3c0c1c0c05120740c1410300c414040f441440102c204100809984510b0800301400300c04805843c3c40e00ca420074590541218020815111209d030050326240 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 568164361 1250 568163111 568163131
    0x14071b140d061a090f04050606061810052104050f0a0515060a030b040302010b040b0a0b1206041805070e07030216020f0a0306050c070c14010215090c040c11010c17 72
    0x8288039000f1440f000500002590040b100004111040e816060003602c110b001d601560380d10303561102044410b1044aa807800113591814009525003084107020210303881c181840c9150003031004244003482e081692074a40c1ca00c15504110400000340b103c86081d030103450040944410a41d82c0d20340360808003800c0001e03254500000f800d42d5950302124802190031541c1c581c224203090800a01070442e410009000c0c074140005010542441d070107080c11070f0009000e0a0508503000e28040701c40402900c595407180d29040aa600300040040303103141c0c0d9200f24005c2000f1441e22000c2140424000c101c80107042c030500008586402422010020541c12200c502d801e00f1501c2c000f0720501556000a403185281004024140300c00c40000c000c0c21780118030700c0c0ea40c107030340745120aa148100084940160005117020120341818001650464440f5099600f1661904080780c102c81100e0074007000100c4160a0101a600038842d032190030000340f4180d62070245080804215085c082d108480c3d03 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 568165467 1106 568164361 568164371
    0x9061a1c0804210c1508010b16020d052410090e03090409020d0501020a0302040612050403200c04140603060108210a14071b140d06 58
    0x3509074024200d070310306420004400440c45449521400780e8002a55090014640c1601840136100c000220002c4149562009255110680c00f452100074100034081e1041e10350381110300041d030151801d038818016031510914040e0107a040108403100c4403960311090a035110028012800c02000014594607245400c00303c4280740d0070690303140e000b0056640181003581000c40114002411020800c007544ca41e41d003642e1040440d00700081d40010144505a04034400d00203002078980108014035042d50007900360000801095620f10301c0c100c4c0b44070500e0040100440010700580b06108101d001544262050000c3e603a980c883c0c084d44001090a000000c0e20b03c6080d040b0701540e103500030110303000d60000e0744900040b008105030046005003408a00c001000040d101e0b080201203129200f855514010b079542101c4110000154a0051039039018107034807200d45c1260001403 = true := by decide +kernel

theorem cover : BRFrame.Cov 567985611 568165467 := by
  have h0 := BRFrame.cov_init 567985611
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567985611 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567985611 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567985611 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567985611 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567985611 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567985611 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567985611 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567985611 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567985611 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567985611 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567985611 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567985611 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567985611 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567985611 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567985611 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567985611 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567985611 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567985611 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567985611 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567985611 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567985611 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567985611 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567985611 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567985611 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567985611 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567985611 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567985611 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567985611 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567985611 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567985611 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567985611 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567985611 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567985611 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567985611 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567985611 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567985611 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567985611 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567985611 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567985611 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567985611 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567985611 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567985611 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567985611 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567985611 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567985611 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567985611 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567985611 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567985611 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567985611 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567985611 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567985611 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567985611 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567985611 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567985611 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567985611 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567985611 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567985611 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567985611 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567985611 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567985611 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567985611 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567985611 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567985611 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567985611 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567985611 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567985611 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567985611 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567985611 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567985611 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567985611 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567985611 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567985611 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567985611 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567985611 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567985611 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567985611 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567985611 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567985611 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567985611 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567985611 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567985611 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567985611 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567985611 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567985611 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567985611 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567985611 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567985611 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567985611 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567985611 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567985611 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567985611 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567985611 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567985611 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567985611 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567985611 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567985611 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567985611 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567985611 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567985611 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567985611 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567985611 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567985611 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567985611 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567985611 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567985611 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567985611 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567985611 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567985611 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567985611 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567985611 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567985611 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567985611 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567985611 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567985611 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567985611 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567985611 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567985611 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567985611 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567985611 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567985611 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567985611 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567985611 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567985611 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567985611 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567985611 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567985611 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567985611 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567985611 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567985611 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567985611 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567985611 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567985611 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567985611 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567985611 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567985611 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567985611 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567985611 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567985611 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567985611 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567985611 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567985611 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567985611 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567985611 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567985611 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 567985611 ≤ n) (h2 : n < 568165467) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
