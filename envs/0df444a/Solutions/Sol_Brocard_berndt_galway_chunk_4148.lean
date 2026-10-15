-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4148
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:42:57.448864+00:00
-- url     : https://prove2.me/submissions/c9153069-dbb1-40ba-ad28-6e05bd7dc4f0

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 745863309 ≤ n < 746043165 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 745864559 1250 745863309 745863311
    0xe0c03070f18060e041b05030403180312050f0c0106153c170906010303090e0702071a04050604140906060f0d090809040203092b020616140d0f 63
    0x400701e901030314402402a0b141c6500d1021580078400c41c0d01c995003075040194014004101c1401403042e004542c61050311b00400120004204810700d6080210311451212003c24082104c0c90340c0c9503050700100d604081c81c200030001a00e103030440d1494007519481801c1900030000715030b6a10608800000c2000d4400200750b444551029601066150708014411b090340700320300e1081e21600442d884030f809074050900240102d80008d2440440160b4840c070201c40c02404554110b00300601400000d610102c1002074040c10004025804584078044400400e10300401c08200441d1800a0160b46c2056070003820101300001d8480c0a1108403040d0308068600043c942ca0b20400d0100902c51016400394076041003102200980703d0b031384103804076802580c0850402c11010005003c1e40d1098540207070541c4402002c2807041c1c00001a10300e070f00c030b40031180c0d8843c40700d913800a910742d0401070406920035003400c9803c4a80c0c0c010741c4000d81009020203641d41c3c82c44807030b60410051001d224185a0a = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 745865809 1250 745864559 745864577
    0x5090d1118160912080d0207151e0b010c11310b030c1c0215030c0a120203151507060203010312020d0c0206090f0109050406090c081003121103040e0c0307 68
    0x81c0340600011000ea44902c19008070b20400e45e10340300085e0780411980b1800d15800c000c60303400314000d050100c401d0246030002003000c0070fa0340d69106c81a084600318400740c500d0442a00c009a13001000d051007031303a208110702e69121214001428141d00c010300f003104002182044168a01d100410203403603c0111420400540a44145aa10086c800c2103940151001c40a1500500c00100920a242c03000300420f4503482505464010b43c0c0054441e940040300c0425081d403019085985e5154840600300e00b1410344c038203182c4141d41c1903080c03401e882c029003003248000480c40400b8101c030107058000e4800d659a5a40b850514514000781040c1c00050003190120209548145074000ea0b0741c0d0010b00c01810310a40c03104005040d5000b81d141c40c148140722100183c0c0ba11180626002401d500200240c80b204208000d000024001d14041081d03c040c041440003072900c05145c074a0540918015105040304491705256101d16003000100c007001400b0442d49000c5000214403840d096600d110301 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 745867059 1250 745865809 745865851
    0x1511070501060f031220011a032a060a020c21060c0f0a0509030f010905061b040509010905042d030e060705071403030d090b100e010605090d1118 64
    0x40403c20b000007000600003507083d02005104035040304a0700c0d0790420602040401010007400c44001d01c064507441440903040d0a62881e082c80340d2050000101188800d42d8100c180300060004045407440c8a1800483da00d4020b42c401c20410488000c05040105107038580501001c8000c001414200301d489001c0002d401025070f18141e840140c13041044600303200c1599030a641c0f58129440700c0b9010300c505d0700b054400103000d01900118034020f030050141030421410010812001881c1c49413424401c21003080aa1152103845044a8812800060a446505e1320201c451300c4d0400400058101d018442b0000e400a004161240d00c2600c0350150380700000300f440101d0041d04070144c802d80041604003e80c040f00e10342c0300300419005080c1c0e460090340e082e0940072a0240344043e40c01c1d0760158100169000c009006038045c04c10680e019116600d4004c0040540c454600958040c3c62000c1c517a07402c00400c4400c0c4003d01e40005c04201d4814105a4a0022404d0071100000300d1440001c030040 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 745868309 1250 745867059 745867079
    0x30602091f0f03020d0e0607031416090302090403350f040b04060c09180614010e0d15060509090109061a010e0603060639031305010c151107050106 65
    0x191051652902d501040141c0300580c02504550f8800015907203413169080341150a00155114004903100081c160390441040700e8100e00082c58802c4204400845640c1c07103030040741180480368106d4072490a50346914049880c40d64901200d06e42c00700129081c10209000d00b030138020f41078540140322241d618642c01e20f1032614113640c040c05203010100030501080e141d8101b4a03150740a0300701400e40c00e039034406000906d100005000d203001d0b0ba402040c040c0b4900c0d29017403c1c4088091030201e0a42188200007513500d180703280d004200ca80301d420a00d0720003400350450700003040300171310102061421002040c044d05410401315045481d04d690810782585a8107050358860042c0d590751404800e10080c001c0c07076072015082660002092101e00b180081c07d0a85071070a02194408081c1d1800240e8400c0d113618410000d06040d030001c0c00b03800000802c2404050488009280c0341410210384c1c200f6100d10425103200039503130b07424100316298008103c4001c0001ea03200300000c11001d6600e0005403 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 745869559 1250 745868309 745868359
    0x23211608061e01030f0507080d030204080c240c1f0c0f03152c0109090c120503120402011205152403010605070503040f0e060a090c0e13020f0403060209 67
    0x100c0482c1c5940c0051003ca0041e81c030f50100c8a1141c1c0460b8456a1a10b4085181c40030001c2210b0000c1d0700058103014810781880400c4140b182650f00340342c0701c4942d6041480c1c11102101003d80c400002c92181d0400000700720401c032100d09034110136009020503405034080c0c42d80c112910042036983c00c8054005102e881084003800440029541035030030f11101d52100000400c000c94080c0800035444030141c1c48140b014000c010403180021310b800c0901d03100c0d0928003154001d40c8205070080851020480200407239050b0382400c0c01c1940a584c481c40180c80721281c803800c02c1640c1c2d00d010308002050040100070441e01d08101c0700d050200a40c0003540741860002108140142014001040918000d4010b01412403085090b40c0c18680c603418040300c00d203016840881003c2c450014803241c1e0420101400c042c00340e5200500c00303201c80c3c0c44068608081d0b0f00f0042c0c001c99102c616101a020f00e0760546000c00000e00c009070360b031607585c00e064020390800c810035403007002303007601050010710420168 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 745870809 1250 745869559 745869601
    0xd0302070302040f150b070c0b0c060402100c0605040303150503070f090c27031a07021506060c01060b0c010b040b0102060a0e011107060212012321160806 68
    0x344501411a828031010b0681813260b400d03120344505559403114040b601c1030001d806280d04450b2100480d05000c0034001440d4401e54881342c00300524903010a001c07070110340c440d030151110b01c81c9200601d403c44043c50f840c1d01c05001c01d4903003005c6c0005c040d8140c02c0309580a94804810301e085442d1020107031148118401c41010301100c1c81c0c100260429900903500382001380c10501440e03107001c0c44810350f062241d4001035101b03031109014410040215403283c8889005608000149403460010f507a0341400b8400c0f03c021800c2000184807651800c0c12524001c04510083c0b1a560b0307510748281c0d0a400c101007151565090007403103890303420b0522600c28080c0b0f05038000c150544580c200c000040c6580742d03c840b800c0d500c4550043e0304d001a03900405140b40705010040e942c260900c00c402c0c00303000607041500034800d1104101107410203552004072803003049442c4880c140207541012240080c81150021500071040759004083c40015920222444502910803a03619011191820a8400c2070 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 745872059 1250 745870809 745870813
    0x150a0602071203080603240703140c160f0213062108041809080f03190e060a0209030a060c0e010f0201050c04182c0f0606060f0901090f060804110d0302 67
    0x728002c01e04c24503c0540040014094071228503049040c03c2c295400d0318542911000003c00780309120b54075100d40c2c0041c54500c501c7c0d06440c200307840c00044512400700e02c001c50b903482511140078072030099982c13114160f000304100302020032001d014020f0b000b076200350645c11500c0800f0131a040c5490720359542a950001c59940380a0800a00503038500f10303002400c240582d660355540010700c20328020800080004d800e1500c07403601d042c030030360600c11480061000a040c0b00440700741440021f4001e0700034410000150f11a5000300100381781c0054100041c2500d1300307141d03003998400e41002d100c81d80c1c0402a641e5020b0f910035103406a09948092f01c0c0e4000e100350402c4200003c0c0f00d050803101d104088042e0200c0d00b8140007500d404c698010340d0717103a80c88504e07000039864000d20030040c030300300100c00b2009000c403481e181780051040c0c0213000309900f08110004080141c0da00c40e106420150418140d260212500c41900410030803040781e0844c0c00404d50814401d0364070300210034600580e41640 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 745873309 1250 745872059 745872089
    0x32215060812042c04030801260c060a0509040501031110050a1704020402040806090607030c03090506010b030a090f060507080709051315080709150f0509011703070605150a060207 79
    0x25031042c54003141c4d2018043d5045051411903104510940b4501071030082c1c0c1c03a002c05505082c50f0035009008821311541c091740c44c008040000d030300441d21140610046485507111900320005441e0741c130503845940d0307100c5d28185c0048104010301101802100e802d8916079055629140705441601c202c61208000c50705410044151813080340007154400d01c05000541072660310170200f40b4044040c3c5030302456400030010440002c2c0d061050709a400003034502844011407a45034551514010301071a00740c240c002002402c40022500f19044a95000d00f00d94440011410f004c1c0c002d0105542110004055502003048188110085426180c00900340d80140ca4410290070041c80401c0042d145880c00080000d50b9007414081c110013020b550f1030108184070302c9402000c40b210395070006e001504001c2010310040d11100c14580c10b5644c40c5101d080c480801190309440d5004030540100103030f042c81d0800680040302c900107000c0354410307035106040369203494007039845a00602590b402516106 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 745874559 1250 745873309 745873319
    0x623090112060b0603161e090e0a06080604050304030314090a050d020d1b09050c0a0c1202030d0f24080c01030b01111207120e03030d0203221506081204 67
    0xd2000142440784900043c030846400200350300f41c008072007811b400310804072903200c0c0c1500b04031200d01018054101c040001028030000c1d101c01994010741c1040c06c03402c0c000441c80d007110382c01007014005040446d0081d1803d460065035a500c940402c50000780e00c01340307804102c070040c81076855102004016145150408060040f81d04540c00181e80c000700e852a6040800d00d80042861400c0b403407441130841c90f06205000b420b86001a01e501e441c07a60411200f01c00d03903400b04e503041001e507000703980041e5101c40380d82c124a10701444d524400650b20b45641604110380c55400084c1d5800c8410390203001d0220500410208500c0d88100744a80e04605078000c0b082d8400e500c1130340e40d048141031a5000040ea00c031010b281100850365441c0640001400c0018844e00c80d5071250503001904c0c1c104109008200426103e0240c900b561403916000b2010600b0f8a210800c62000404240142d841c20311766414040707003000c542c8010303031a000e05d800808103420034042401000b80001c0c2144c103190510345 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 745875809 1250 745874559 745874579
    0x161703071101141201080f010c0c050604020f0a08030f0403060f141503030714060a0506091015030b03010c1205060102030423030a0236090604060e030c070906230901 73
    0xf54003c0c07162a41000300c881054a031070b221a0184c41207000811180c2c9041408900b1a2440300d001d0042c420390490003000500002030090303003d9415180c2c2c103545c420f1400400c0c90900c1c0750b00000f00038000801c003010298020030241003103a01400d801e1200250111200c0100c96800f5180c005550141e000203d00310b8400421904550000d82168940b01c86074680421a042007459004260044c0f002d0010608090159075002075040341e442d040c2c1d041052841410205912400c9002840c0d003096038400c42c002d40c840e40c212880035009201e0025503902c028490300c00032003c410b0262820001c540c05510004c00e9030251050665403201d12108861520280c031021840d156040c0320f00c049510050b25401c017541e500603504500303104000040f2a0300801c1c024100e60540d14078a44d0b800304130740700b0b00c0041c425401541160340010841000c2800604622418407070340380600c103280002a103000d05610000440b00098100d1b81383d0340213041d012054180040b0003070b5100c0c50030380041c4420200 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 745877059 1250 745875809 745875827
    0x50303150a1703040f080d08040b06130e15011a09060d090501060e090d05070b0c0c011401300206070201080a0902040908070501050a0b031902060c161703071101 71
    0x4002422440c0e4a22031500c0d0b149401d46400480d07000031070100000755100840304040c0c400321026007440700b030900008242c0b8a000344040c000381020030208185488110001c402c91100c020300f0700c005c03403035180710030794944140c46e034003d002d5220400043c5160008040510980705201c901c2e10701513103041008496006141d1107141956180101c80015000b441810010011101e034983c01e407810a8103d414403070520302d0001885410001c10740000c0d12221480d911082906d002e0707032034800b01d110f550f00402000c00d10600c026003150011a41c07040c000303402080e0300c0c4144090565003d004040202010344d0f01002900007405002481c0107601945800303621801c3c0140001d0500034907000101900c1600f1015524200d00148181c1807200c01c0c09020340c005203402041c02030740383c0346010079694071381c000c19400d2007182d90f55000c3c02c550302c20040700c6410300c0071004c8414042d81c0f41d440c805505000d00c41d980042c1301d500c0b2080e4100382c0c00310030764014541069441c0754019650300150f0722004 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 745878309 1250 745877059 745877101
    0xe120901020f0f0f070e09060606070602162001020a0215071b060f0e01021f020a030209060d0c0810120b10080a1103010b1206010b180d12080c0304050303 68
    0x240300d0b0644030344003042018101c0c00f580d1000034006a000c140740103007400c1264001c3c0030035282000400000311000141c25820510a0714403d944a40c1420107400a000c3d2080d0300c1c0040619000070310520150030300103000078042c0a00c01e01e0f421100e07401039940c3c400e42d4100a41050300000280c40c15180c00003d003000768080c11f440a20f00030440030768290340c0c0d5075810a0022a10038010012181e034840c9060941000a0000703204212124841414081d100071040302e090341c0028007107002074417030b80680d50150b1024001685800c9120a07000280504501c00d600290100c80003032505101c8009840468407080509200100c8949544400c800000d181640c11200c514000030351038030420101994074050020440c541038102d08240c01c3d20015078106104050184481d4164800803600c02d0441d21070013003041e656080040c0e0a0508e090920b001c0d03600030061600c050030f000413003c10000e0241c1c1a550100b1683d0f4254146209020648001d013095000388005401803d481c400412296 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 745879559 1250 745878309 745878313
    0xb01050f06070c060c0302100c0e190f0e01051309170a0e1804060506010306051003180c1d090a0c14031203240a0b070b040c03060f0e0c01030e12090102 67
    0x2001d940c4850003e00d5160f4030120010f50320510207400d05506022442140c582200c0c1071000700ca03441c0f002840c04004a803428441d4001c181d8886002c214454410024140f14101c154034036656524502040002d100b040e0090110b50908001d00f51341d4840d410032184d0002d02c145400e003545070000c019800000840b0140003041415800a90302d80041c0b50260b2a0001c242840c2c1c5000d00c0c00005840d005030004e130502d400c1c200b040c080c1d43c1e203044996441c048140740014030a0f0761042c2650600d5103410010b8000d4198260109010072401a41c01d0581030200000150380c684010095490418210107007029003001d4051002c200c1e8070b2260403040e00c0080032501441e40e6100409041d900941e8241701d10044070400142d5165503008040070b00c2c0f012110010518609004070040303104004009000c3c1c1a0380d40000e00300800d189410001d10f400c01d9003081521920f203120002031071505c1c3c9151386ea10031a01c180c00e07190b02ca80070380d1080c41c8810000e8201e006080c0c1c4035254507080705130800d0641c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 745880809 1250 745879559 745879567
    0xa051e0f0709021c0603050628050403030207020a080309090402151b0606100c020303040608060a1a040f1e03110d020301020316090b0f09061315021e0a0b01050f06 72
    0xd000100508005000c21800060b0784034968024110030b440b004441107612410040700304007144c40851840d60010040902c50000c00d1000c00c140784800901101c01ca0b6145803500340404c0c180d0540c064944d05100340c881090080d16070905941d00e010300e50100340c0c0004e0302c0c00050018180a840520440300031444036060848005540040c042c840c0c1c1c203111698803200801c41940780c03a80215912850343c0c104007101c4100798001c83e882e44520301548050043c220045a042d031154051640280011460015504048070203500c1039807007481107201c01180ca00b80450130140603405000b0070300d0310040c1100814515980c00001100e14229940d122090342e0750040076071020300003584902010189404c1910070554040c04130080c035048114000c0c01407240150343d81c0804100e418a100407143d40b030311031023983c1044a41c454a500700540784c43ca00d03a41200f4442d00040c603c4047d11400c46060307940d00860300c030b1590303942c55500094888040500104005c0c10020408680c00101502c96031070 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 745882059 1250 745880809 745880833
    0xc030904110412140d030204050105190c020a0305210307020a110312122203050d0b13060e0f0c1305040209041d0601090509061b0d1e0e0f0a051e 64
    0xd103c182c2c1e10183c5094000400c61000c88a0921a14101260b182000c40c00c25060400007000c44c080c82c0050316910600c0422007107000d01907240c0f10a0942d0050a0710303507080d101c1c82c206440302d030080041380c06102205040342c01850080c060b28801d172a29402085a8520b50315004d2550707900c1c1c0b5681e0b030503004044601d40c1469403a0010148003040d0f00b0120403a060000d403021007032500c500580e45c0c00e0f1103600400002a480000c070390746090141c4d000716402441c44d001031402404451000f00d07051a12200040c1c000e282c00000380f01d04616040e000140d0341e8406441000e2042816020040c010004184040d190580c05042c0c641d802400020705000841080c81c5c41c41d181c041074400316440480108904461409501c2c2e0010207000580303050b003481c05089420f4001100c084031850000f040e0140900403e0384401c155001190b01240c00810150f0500001e0485400003045400f60081140ba101d00019070081070647c000e0082c103101c2042125110304580c03400900082d405000301c0c80d42 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 745883309 1250 745882059 745882079
    0x190210050d0618020c12030403091203050405031518060118020c07120506040209070905060702040f0209030a2105030405070611101e1a030d03050a0b0d0b060a06050c0309041104 78
    0x143d0444800005075540b240d803024030318041c01004024200740040080000007031f030145801040f59080300701220300c500e8a02e4162480d0140b50000c640501c224003007442c20794082000d03035011b0003c2ca0340219040c034264900f140c03580d5090041c4121801440d40c0385402480690080ca41d100804d0142c41d40261a501015090503100342c0554280c1e00880c2130005500d081040310303802040d91b0400102952811000c074031240510031003e0311a60791080215203c0c100c81e011107a0440c80101502c850702d00360300d8034580c3c1030042c158042103901d031101001241d03030003001100e001e5074014005002c43ea240002c01c4500450100e40c1658900580f0032014100000e030003a12007024586003d5034624021880034003c45081c0c05402c51040e004403c1f12a20362804902c0d00320301c0c8014607021a00380e44240d9100003030141c1c0251542c01c95800e40d8503c0601520f43d90603402104210742c05900c807036880c0000c4070321f07001d640007228180d0020070018038645019807154180c1c45402e03114504003541c0718bd40324 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 745884559 1250 745883309 745883339
    0x10e0a1a030702060705130b0304020a030f051e0f06011703040b030c270105071101030e0d0207170f0607050c0a0804091506090b0f03090708010617190210050d06 71
    0x10803503420210070301c4a01a01070144580c04559403500500701440301c1c401103110007541c8a41100c0080007c041030940d1a066074450107550041034080d26082a8601555604400822040340815480031180e0030000810303034a23107500010000300826404c0c0064030702440c000140c1104188001c1000007144020500a140f1900c244d030445611041c42000f40e088401300764660411003a0342545951050f078101080e00c91190704545003240c4100b0280051b8010004102001014420f03199a5154a40c2c001034503420394840c50303448900c062003810303ea41e54000e15008041c2e0f64200c04000380149218401600041c007004044509054098461940c19440364002c90982500e0b05c49901d01544800b9065005040390710b824258149481b0a00e486406920010040342c00004041010070b24100401d9024000c00300003008800d03030340d04414240c481070a50504403401510b208071011080c0c9084401da40e50050801100741600c840100e0301d0303501120005241c107554103c0401d170120b01003110 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 745885809 1250 745884559 745884599
    0x50d0b0d0615090605011809020901020a020a141e090106080c07020a0e1e0c0a1d06120103031209120e04020d05090f01240927060f0b0d030e010e0a 65
    0x450070807400c00c4018400d50710517402081c14032a911070200340f140807030b031640c00403102c0b4110016298908240103e061070307071856002e507004140722408100d01040d00d40213190400101c5002150840b60008048007a0000040c4e55201d64840c004004060050b02190740c0b01070300400261805102d07074005042d420450308400c2c50550b807171040102c180c400407200c403a0902c00c502d01c10028903100000001034468401d48000b0032800750f060281100c01c1d142604090301e0028602c64488800c2005408424024441075000440d05e074015502803103180f240301030546d0048002e80002c469008107071485200000d00c8dd070015420010724010100620444d4041e1090304060500e07101c1000d0400c0c01d40d6401964120882e041606001c602d20b501000c1c00203c0e0011040410310305a0030081c050011442001c01000301203ca503504100304469006d08206114454104082004038080c401d08140100000f03010a100038954102c039030107a02c41d06030001008204c1903445071603032a4401d1100e807030650 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 745887059 1250 745885809 745885841
    0x90105040906030602040e0a0e1b0315190b010504030804050d21020109030e0102280302071d01050109240c151a090a050c0301150306090204180b010e01050d0b0d06 72
    0x1b081c08041c1c01c1c44212034004080316001d00650040c03240d60f40d15808072031030301c1d200a0305110781d8600310b49061100c40c66207960341d0420f0700245020740c140610388420800b0f40214a29007100303c10198003039010360342620740050029050508140030300500c90710480c0d0035070b0482048002c0030a484400780003201d11002940c0046a02480382c5405042e40031171034480d0381950403d4400d41071880500102e100c1d1840140842008020541000c2e410700f403264110380c2c400c0c1c156000307400f40551298013042c121202a80d0340320b010f42d5150000c0c0248101030138420b140800b6600100d036201d1040f100d00d148a8002d00300444d04100e400c0d070381170031103c549842c50300e5410070000c4081180744c1150160790080e5440e100303020a280003c0c4242040c44140502c0c0040d81419051001440c40b80d403180010700f00c0044215075464031070000145c0c00304220881c01c03e89082c2071810400d0b5101e400084110381041e110b00c2d040c206e00003109001b601500c034a00d074000c489055403a001c41c000d805045e40007040042 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 745888309 1250 745887059 745887067
    0x3030207030e060418050a0b0a120308010e0f0f07021e0106050103140702030a080c040e072001060503060106050a020a1502090a060305010510050a030b101107121205090105040906030602 82
    0x5070180c1014903581c261032089005101c00c01444d80c500c903610007080d10070032001510340d03140b001c154001c1c98035640098002d021441c0c0030844500c0800141d140324065200c0040c2d5a994800003d12084125044400c090904010800210440d42d40f1a088201c50042d00c2980401c2440c0c140042080705010915039100e940802155804d0f00c14110b14580e00c40c002800791a2506000e1343c6c82c03040a000c84100701144c80000d056203c1003043e500644401440604030b41000c48000b802d41500e03e288010082401b4510503101d1130510a4900700d540141c00780c04c01c2e030729040054882d03030461420034080d0300590140400140d240c40c42d080c410104003500503240d4881c0750034440e2030041ca410031018140b40c0f0300188013581d12540c01e142502020b2801c29984c071410081100640820000c03107800c070b50140c407d140d45940014071540d0388000c2c0b50881740c20a44c1c400301359081074503101014002900c969018074a0728450300c01842e4018040c14854079040d0345c0c92003202241c400d944103540f0158049 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 745889559 1250 745888309 745888313
    0x20f1305011701270311160e0a022b020f030c0a2a1707020303070506040308420306180601052d0307050d080909090703031e0309020d03030207 63
    0x1202d009a94207403000208001d003200c1e8144c20440c504a141d82c0d1508281815000c01c140c42402400c0015942030181c0d0211204030300c0340c0c41424070718000d110818200b00d0005003a9011407003030324546d00301840d9254405004041210402c007c0c00c041d0403c0a800f04213020842c2000002180181d03507407290103a941e02d964100801c02c1440d206c00c0c0d084500b00d010340380344081301400b2007038000f90490304c1055250010406d402007440380d404002c2d0540400304070041407140129071103220744d0280e2550102c0d0f90700c0300604500440000645085903c0c68410004e500052004401e47c1c108501d0240f40d000070307031000080c6004800c03a099075609a00340850503040340c0c14070103d801020305842c1e4030110340004641d51035070000c203204620076040816000b8566a400c1142000802c0042d042004110180c28080300d150b1003400c1441c081c200340d0380807079003683c800940c10301242d400d55101440100c0600f941b0308564040302e0400101074a64058502698519480c5a0240d100380c400680d2001c0ea8 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 745890809 1250 745889559 745889579
    0xf06011b02042c07080d210b031c030c0810060203070f0213050429150402070606090c050c19030e01050a021c05030a18030e040c02031b0c0111030c0a020d020f130501 73
    0x2040b4414100b0245800c0e102c041003001c15400b158070802c04011401c00b00b0346009c00c0c41d0920402400038101d0984100c5003120740c06070300a104101441e82d51012039540c07060b8084100d112031003120700580c004c00c80300740400d800507144180c00e13100404090701d03025460b080000b076501c00e60b401d83c0e00c1080440c00135a40103841c0800001c48411410304511803a101114842a1070104601c5000d26000180c6c0020064150b10403005082c00060070003d4815045004156400180e00b55905104034003020b59183d442c01b190b02c410b544c0c1540ca8100b84030803400110744680108010009501c1400d601607904546100b50f40001085a82e520340c07640341c0248001c0070341d20100e140d280506090140d80d40801d03408070b410044104161004120300060034000c0f440c41c452000ba00b032001e594100c10842d4841d010500d48040d030b100f40da400c0b5070703804044e0b205d649a111701c036005c0b1199441517142000504120303000101060009052207009881c03000818203200c080101001090b030754000521150485e = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 745892059 1250 745890809 745890823
    0xc11031e0f0606090f27060718050a030204020c0a050703030305061c050a0305030c12010b121b030a11090409030e04051e0f0603031605060f06011b02042c0708 70
    0x711a00402103401d0200c0400c8956201070705810010603e240003515940c40702078032110018000d4040c080500c05010142c3d01c802044d1785580000300b41401c90703006c0511a00c1c4c043c0503144000c1499a02e20324650800009522400e10b00340c46000722a41c4101142d0203000300c0300154060744020074507103807003020030602031f0504200140034000b06a02c100811400120b20b03e855505013411070b40d035151142040c05030302405003000d0140d001500003003909100039000d44041c3c2240c03070f040400e0351034020510f9150a400c1a64512540041c0000740c95400720b90894840815421400c501c0c0c6107840c400700342500c0785070b0002d030080384038400364500608052082560110001040b040c42d0300f980b401201204402034155040000428040340d20750b5400e00440f07031020312034620b010118050345051074481c4030444000c403c01484000007031300395004002e52001c3c412107100d04508000c07941c0c20003000302100d010072900c56125103180003050784141c0582000c800814000c0100030b2a00c1005071030584 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 745893309 1250 745892059 745892083
    0x13170106030b1b090409030e150d06080303090303160e2106070518011d0909070312030204260106050913060608030a08040f030e03011a030c040606050a0c11031e 71
    0x2800ca8807071903452000c0c3c0d0075220090341c101e401140343e0200d803d007111001210b00c400c95210102c02040c00020123100000c00d44038510f83c074180042c03680c900840f9124007084801c017125800c104002036940c00d0150741004168154200000303907028040c080740318420f0030340d00b100b174507800c8410101200c08104000342c0d01c41c0c1a031070072501c1d114030002c01459824011141d907060240c8890300c0300c0380b1070944140720030504001d8a1031000d0320b07101500c6035817000b140c4000d1381c2c0c030723112081c0d24400d40e4400e008980598030008520700f40c5a10031008205c0c3c0302d9192410a629550f44d0202044503a3743d6444079024907141306001220010b10b052040c12106960721545070f41d8005c01507440100e8000c3c884a41c40350300003101f0040c1e094182401c0d00e40b0300c4c100d60303c141d042d449d0400c01c1c0c00c0c41950300318078051010203070200e41c0c0da00d040c44113010844010b400782c6000310f1014814002e8407807107030038401e100f01c1c0701e0942c2c040d40003620000710340760104244041820400c0840349030302c203141c20032010010f05 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 745894559 1250 745893309 745893331
    0xe0a05010815192d050618090a02010809010b1e1005211e0c0706050c0306030703200a081c051c02030a021908010302010e0a0602100213170106030b 65
    0x4240720f50036000100e40700c48402211902e0740420301108841c08401e01d456940950703041c9100f4402100500140750448206115070342040d40482601b0346c2c040300354802c0407541c00601d0b00c01c00719001503403d10740c01041423000359280c0508004e1525240300311040ba440c807040e948411502c00c2c0c01c018a0f9001d64511104000c0240000d605110941d00b90403010010403d0400440d1584081002c040001c640030fa1511900780c818001f0010034400104111809a41d0811441d124003106000620042c1c40132541540031600910114030302d102803400092100c1c1c8a6002014500c000c200b507107240d50700c401011703005079614840d0104041c1c4161884013541c9021480c0009600c502c200c3c815617810406841d550110014841c503020b030781103442d001c10300110b40c1041141c012009107003900c2400304a0000742000c0c0c51222070304041d1107007010780b90241c01624051524108060094000c80c181d80350702007460000040b680d44038a0030f1304040c0c00382000071039181e0030350800040d5030300043d11039035031301d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 745895809 1250 745894559 745894561
    0x1b0c0c06050c030403082212050d0c210e030f03030906061c03050c0a020406080f0d180509250203042d09020313020a0807061202040e19060e0a05010815 67
    0x112004021503050717131340c0b120b14542c842041c2400e1002140714109444043c082485003c604420760749404089244680211001013884030300c2100c1c00c195510000b066911605048d0221200c0800300d4960324020746481c0b1112959038000901d0403844407401e040d9a0400000d1041644091010030380c0000d040d50420000301c07804c40e9015410211403805000c010b4040b4426030081d0042c095004103507002442400030307903140c410054440300c441c84003019501c524000c0f411154052235140201c0e981203100f2055071841c003828000383c4040100005d40000d801c040340441d240c0c031001465010b80c101e500564403a8205a80400551481605800380309088800c1010941e0810883d605680768960090b8030303031701d5010240d01e1604131608000d41c420658640410440d5002460701c0880d03c841d07494408150301e500343c0d54128441c4c2c4c0112072a07d17085100154120415051a0000810310300e4001a02541c500c1740e80928202560300030041c0e5165401080071031003c0051314a0224082d0b000161 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 745897059 1250 745895809 745895827
    0xa08130f0b0712021908090601230f03250f23010309060f0506030705191a0708030709030308180d0e040e030414041d0601050d061b0c0c0605 62
    0x6030316501200421904074000020601482180788001d08800b00708190348030b40c1c5500c1001d07419101c60b40c0e20000140c03140d0025900000001c3e5060480e0203003080d0700c8580c0740c0030510000d6855030118082d00501c010508c00c4d0107403000c1001044070525140314854a6641401100000c045035001f4a845444000144041205000c0c8140d0400782264014101310a03580140c001d006010342c09400149805508407800a0302d41001d8460f010840a6801032a16030301044200c4460103480d14101000190512001d180c07280500080b0380720509450510303600d41d86010703503a4421a0901c0010f038401108008240d0011280c5811440000040707590603240b000b099903032010009100108209441850419211076000031160f096101c1130729a00c41e21000d142e40c140ca1300b030054a0180e40392110181403680c20016552100e40c480001c2d0196910b0003040001042515000b46c0b22a0360b501400c1070000c3c126400e0701d4010755561034042d203948081c200f801048090760f02c42802d110040104200c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 745898309 1250 745897059 745897073
    0x30402030c150a030f0905101e0614090417070503040f090c08061e040905062205070b0702010909050112030f050301120b040c03060c09080c03011b0518150a0813 71
    0x4100680d510700000c40c060005c8115002e01000303c0054218010210518402c0c103d0781c1120300408010301c06003004902d013801e560101d501c144540780d00c05e0510381030009540b406d6008207030043e010f42c0c2c40d0350500300c00c125240020750110300101c425a0000404000300700c54802e4001c0108403981042020401c1c0100107821204000d0100d031141207005040500f0b0122520301800e00745018000700495005890182d42d20182501d80800b508540d040e40114a041800103140c081c1e0b020014041051a00030a0002500080000c0b418011441404100070f1440d2041d24003d11042d075403203460074024100901420303c5883e20000301700301000140440e1285240b400d40042c3d210003001c1007541d80c1d040001c0b03041e10b1a08000c0c140d900b001e5150000d10303072040703440d8151080c003010b03603015488400805088442c001020554070315110351120885004002802400c0c840d0b4a00100c4d108041001a5464280740404c03d4101c1010503000c0c2000d40c07050381c0075400590940060029045034403106 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 745899559 1250 745898309 745898317
    0x320603010b070c090507120e0f031b1c1205100e0c0901180905041509120e0303090406081018080f071b03051c02030307141305090c030402030c15 64
    0x40340c4070000040c09000c00a0a82505009101d1345504003c82c1c00e007400000c1aa00c45051810702e09810101050b42d1030201152036032440e0b480500861808581d049003005204440501c01101d01415107588541d285400d100340085010f40d80755000c10558040b050222040a0000740b03c54401203428400b07042d03000842a000441c210503030782c66001d100012103804c14005409103d468424000240c902500e03000ba500030740c85002110440111900324200f140c0050034050f00240c40c0a0b240f45990f4042d4900a003642d4001e02030f2441c0c403185401180c02d4410550002d0100d5000a01c0009155075034410740700d00c0c0154a00300e44011019844441c00ca0107a500b8040c003000700000c2c0e200400c444021480d0158100d000303006001030740c82c20025100c01a10600302c03151000203040085203480132003100d10480e010b44407060308488003440106507400c640c0d64000140301c480c9000c59590b1703c84c0500d512039080c11419036a070740303044d105050801c0d0780700411074080c100350805551040d04603020341d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 745900809 1250 745899559 745899569
    0x3042109091a0409080c0105011505031b160515010504090b3603041e0e041104060810090210090b03070c1112010b010f09050121060503030432060301 66
    0x8100c1046001100000c03242c90603405034020710f4440a4820805003501601055000c00300800042c0c0c0c0c5c4003032110205005000c008005401000010324102d000c80c1c00c503406907103100c0316500346030401e1180302400f4100181952236a014a42d00b0081c1c200001d0121b000d4417042c2c5050003684800d90710340d42c11101c00381150a0394400300748406800951340300075101c081c0c58001d0010190103102d080a449900030b00466083c0c0c52420075100d41002030320702ca0400c0310211070403840d141e6100d03190000d2206541040380d030f12545450340022454010003d15005840030140010b07010090710402c80316481d00c0d20171005000404604014031034410382925449166400c02a110160328a041c14114000040c4203520135902c00c0315020910f015481032010780401e882e095902102e0110a44140c40303140725450016407501c102c030700c1c411105664906c4c1c0f0070011001107034513522500041d045030855040524501c10403159611a03510500c00403807901c00d1400003020b1a00c942002c42c407148414011 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 745902059 1250 745900809 745900811
    0xc030d21200f0a121104261c020c12150c0706050c0913151a040f0b1c02030f150f09070815120627030706020304210909 53
    0x41c1181d2080d24140112840e001c2468040d0380d01d08001c95150b29070040054600040e040c0c11034000164924810b488581c95003072002801c00d03161818200100103112110410300944502e840080d05007080040b00e48031032600c81e2500162415030080c505000082c11301d1040541d0342003100c01a8000c50500b03204003d80b40303c6803440e0317a0f803d02c5486610070054004c01c0c441c90002007101100f480f0015040a0b10210b07003003000c402d80d02100c02c1c25504190790002c8c2d00d5a45910801502d0171034111f90484003021181709042070f42e2500c026040074803071760001680480015072018103220b80c8000c1611401d9044003141141040d100d0541c4000703008000c190413414040c1d0034881aa50400c6034170a000c4001c1c0011954905402c00500020301074844400011400c1c501c0c001c0c1d450102c0941d952980460000d00c210f59507403005103101c12000d800403901c2c011080c0c2200220780280000d05150307014500c00b40c0d503400c1520380702100d100f0383d448562850240d007903141051a84002c4920440d074650720 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 745903309 1250 745902059 745902071
    0x20c1f0e06040e07080709060507030e1c05070e091606090302010f140a090303020c0616060209210303091506181902040609091407051909170c030d21 66
    0xc0071401e82c0c8075580056500c14110380401401e9940010b6441c441c900d540e54041001c5d41d942c4042c3d500b8010410000c000c100103030740d400301c01e04001031841100d4404d01da0340e00c0c40d04c600da220103080c49407603081108260420703010090503402c1085000b8141458802943c1480d01e0b00200625407015800001e04201c01a44c0f113288083c4584044946010049843c6a035400c600da005400260184000c80141c0034190100b04a0301d01034090f10074801840355a040520000c1d91524004d611680166910015201c0103d00e001104480a4001540f140040d43e0b2400c04001c1245060000c40111281d84440c0301003092684614581c1d6881400d6440000d4440e1504805582c61407207805032440d0480c404900025102d81c005034410803140c403d4010032118801c103640200300c01088070302c00007190b0104400c001c040f0a6450a0340c000581e887d00d246603588070600c07000480402d10440c0c106911000b402c8501e45824801c80901030310905240c6030344a0100244501b440341d4128801710700d86d40b14 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 745904559 1250 745903309 745903337
    0x2070201030912181512020714011112010509160302031005040e0d090e010b070311010b03070e18060114120c0603040305130b09030705090703020d060f06020c1f 71
    0x10300b00000541d4001d503868000f2000f200300822044094846041d080d041d60310000c0d03e48408540310b040511075646070060358040301600401b81d80405400c4452044503950307407800c942c00b0321624181c00c02c001c003401d40e5001580040449800c0680050b407088100100b030003c1042c000f9100e40c0501d009060240e00d030380e2040550003c1c1d01c0380358843e640250900400d80d0440030040391403007032600729484000b40f603500e541c41c80840603824010040c2d111000c0180b500840e00030702c1d00c07100602c0c07042d001040080407540440c0c14030701c86034044410741c030700d41d001d004071304801d02070010305811001c0081c8103e600d0225444410360714a848140100317161443c0303613421001803051401840c40680180d55034106840d0003030141e131040c0510940844480ca022a503403240c4000c640d00c0b08001002000c55034144000c1002605003d005001450f908003d2450b0480c0c1d24000d000041c241c403240003a42e1490721070701a05291010404520800034060300301e1100d114400a030381d9403501440c0004440d40c0c41 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 745905809 1250 745904559 745904561
    0xb15090a0e07120b330409080903010608030c0f01050108071707180213080c0a03140a0602030903090a050307030305031b040e180c06070c03230a141606020604110310110d0c05120a0207020103 84
    0x611894065090cc4404101000004003c020402207202140c04c03882215a22600301c0e9001c0c000c011540e0404c242c104071900b480856a12440240019140e20300c1d541c08422010800240000119a80201e0038003501007044050714020b00049025040a140e6000080c03545034140c000100140d5880419400004080144000e86688a0b408558908080410300d9607a04001c0c00c0ba481a445807501103000c1c1030208444007265031540320103046440e5030f40b002a103180e808401000c0d40409000024a0b04150b043d080c1c0501001c1946100c8200501c1000e82003400400486010f03200410198001a042d51143c40032039401241e116000010949111410541d101c482c071480e119050402e42809009040f101c2c44070381503401c80c2da080000c0c40100c0e0b8050405c0c0b00c1c0c040560841e00028011031a21082c01e62483c01c020161100540019462402c5461030600304214034008116019048081e01c079051040500e0b06119080188064410350300e42d90040200f03440a070003155840c116402 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 745907059 1250 745905809 745905817
    0x9060604261f1e02040803182e03050906091905030405040501060909050610050714070b0a02011a0910050607110405040605040b15090a0e07120b33040908 68
    0x40d224400c000b0b1440381554102808036406005040b030803040b10000c808502e80700f10740840d14031101450030640301d1000702c41c559251494060f000324880340c05c5540064064036101d41001404030060448038201030040441e5001402ea203166407018042c1305424400250382043d0705881764401781e2a0105203030180c00d502440d40056040342c00e00d800890b40c1c07a080303038294050315404003042115a071440304011400941d0659600861801c01030301c000300390035154603c034030301d4008111094941d4031203a1182e0369200454910040c7d40da000000c0e45088003041440300540100c60444d02070502c036038902032081a62180c0303032082c00002071001c02c000c6811040680464010401c02551420341403110242c0f904840c11a0050321080c0021030b502c00b610002c40760460090010f400e00e80d6000ea11200500c0741c05400704952044e28400124015001e07502200786100320b59a0301d850401380c0700c001010608a07044940d40160b080d440c581c00782c0038025100710443c112030110b01d0041070705011181d441 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 745908309 1250 745907059 745907083
    0xa1b200f010c20210d020c06010305010c0318080d091502030103030e04050a0203040b1b07050a050709200f13080d0801030b130b040b092a0906060426 66
    0x10805400d102c0150b00481c0b940440c03010070f00701501482d5201c11070f5840c0d0b00d80e00c0d928003030321410358041e01e40d03140c20030054861984010070040c80c10741c9a1401c1c902c0c000c400d030700440e0307103079141c000c401110741d854042c00151801860000c5110ba0240e6104079081c01505200d04150f656910042c0a00c4203101d582200c04040d1042155a541c60342402007050210902140c002c40c14140030451224251003164443c0c0c0d0483d007480003c0d00c0e40680c0c04281c1b4114071140300700f1001400040041340082c405041424450001449a41e1515a640056801007480070180070350030b80c7c123200c41c0c1d2502c60445040680300d90416940d107401c1003642983c10312540100a4503c104100c500b00180c104181c00d0507240101900007150751551100305080c05e0948000b030031002e054003c03c00040110782c1c030766008080c3c202a1015480c900503202040d88a205820260161544015150b800d00c480180c0c0c005200b0b4860700d20f880d09211300300ca003545510310382c80b14080152008034101c1c1e60502007588400 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 745909559 1250 745908309 745908311
    0x62306030703061a0309070b03090d030e0c03070603020702040b0d050d050904110c03030709140d112701030b01140108011202131a0906100807080703060e0f0a1b200f01 74
    0x1241081013500940c000315101c0c1c04a00c039880022869100a00a49209480e00b03002400c0010200904801414100710440b00c140316840c0c0c0039826940c14044480901641c0d540141c461110b801003106a40d80c0c81029409907582d8100c14020900110f4118120b0120742003081d9102d0003680810000c01e02c00001a01040000c105414103c4001c170080d4095101c0d030703880714034070303522900b52403100c02c18404402d034028040d400400014002c03400c64000c0718001801c0032011b000041c4024040c00c003039981c442c8580f4074100180104840307400d03094054000c1d01c2c0c1c902c02551f07624001078080305041c0a84642489260050001c40d62400850b01c84030f0b012030010300008820344528200480000c04a40c03007a0804d01c002003290a1400001200326180d03070f21080c054556413002c1d0b82c0c142001e401241050f4980d07d000c950422446541400b03030402507280c225926148004100700d0340c000c2c0034100e4010f00c0d060754030b00743c170b034004014541d20340000c0c03203c02c504078403201d10391424448100c602e10315 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 745910809 1250 745909559 745909589
    0x15220903110105090601050901180209040204060302040303021203070c06020c010b1201150602060f0a0b010c05030a0c030f08150103050601050c010e0f0f03040602071809141006230603070306 84
    0x141d00c552405681c0201500070302081d142d0075540d40e00c0380024018140c01c92031040040100024007540c042c40032a040d0001850310b007104010509036030007500302c100803075000103080080640c1000a62161102804072a0079030400c3c00000306041c11035003000e0001d98012030000f640d880c00b9448001d058000410501c100c440c0c03618054080c2070070241142c900450103100003070081c00071420510a00042088011030f5851480720b4000303000e0031035001d04010206c1001000200100000d20035560f071030f158178268442078074008044104034031301c1c1c004016808040c01400c0c0241942c80a03402d00074203003c40c0c5a540c180049034207006000c0e01d07030140d6017040c1c1c2440d11050041030588070503101806a51250880c0080c1c0e940c0c0e03210b203104600c01644044402c0024843c02001e840040c001d84201040010140c0c48600c030109000c20031042941101d07480b01d240c40410b02c511001486800c0b007200754007280c610f06205121038440c019028140c00400101c8140c426405400070b484010844000 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 745912059 1250 745910809 745910813
    0x2061204060b1002010c021509160603090c144504052517030f040e100807180906020403081201031103060f06100c060e1f0203152209 59
    0x80c0c00700360850ba00401c4808103411001d441070080d81d1507410240c008044d40010190071010003134008002145034003480c071140310b0b2003015000c0040240181c1c1e40104100d02c81b4100040724001c141d0141b00340c04070311407071209141c4800020140c030701038245100da0452542000c0342c00400e84246030f0401804000014000c161480840c1030003203000708100c5555a418904802d080c14070500a0750038858042420414a010006980081d900703c4050300d06104403101054a190099000300c00342c1000901000304000c03c0f490581b0041000e00001d1800d1860440c070000003411810203140001e8540c5400d405010703054045034001c6a102641c2ea940e00d803500f501c03d80300142030000f11050100141c5440d020310380000c00d40e0103544d034080d064040f5203802c010440030307120382c510440c144040c0762044004142030b440b5500d8515000000380070032000c1c031541941c2480c14903106200c428070600902c01c0e0f408200e4000d003c504030030b0b2008404074040c0601202080500111507013400c0c140809801 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 745913309 1250 745912059 745912061
    0x1504030507050f0f0d02120405012f01110a081303050414010516060203040209070c08030609090a1b14060c0303010501081e040f02090906060904060b0109050a030b01030c0b04060203030703090206120406 89
    0x4001c8809901f90754952000080917440c900c80d5200d04c90000700c0034010b440d1112180590b000b01380d14005101050101c40140507800d603003d8007081140e4503004110148000d0700419103550000121004001d5819141e030050401c0c02540074030801d40e0078203502400e55901070310440c0e8428184c40510300200031149002c1c8069401210102d001e0000c2d10082145036009241400c41690700c45203075420748c0e41d403100740000090020700c595164820403400f28045080801e4600410100b00d21070816113041c40d19101c0780101c0a100e0700e000c0c00003045490301e09003000c41a203064070340c00d00c0e00c41c10036155186401d6070000004550005482d512041c8010005100c00300900f80b442900c1043d110b585160416840d02c0703080300c0a5800c45405400030700001c446a1080401d890141011201c0300c4c0c444000c2060070743c2980040f50746100150061060001c04001c010050951200d2985800e040000c000d440c1d00000d0a0001455100c1d0400011035030344506490907810548441002480c1c0742c10804 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 745914559 1250 745913309 745913323
    0x1e18060c032a02190c0e06310b1903020904050a02030615090a1103070804060e0d02060609161d01140d020306040c030509071205030903071203030e1504030507050f0f 73
    0x84050700c2148490798000c0201c400c03080b0b80b5174011404511a03032514000c07010002c0020501d075800101014598030121881e07907107c010b0389204130754a030400304000265040342c400f00300b868881c82030b00050010708101034540c6400d03264151200142070b11f9518096140405109000350f00d0b008001c00c00c221441e2841d03880d84c0c80b5074100c0314600f594031400703014801c4400f180e01f01c5c42d10301780400010749058001d51a07650824880c00e0001454040410403606000110b007210300181c11100601c9103078580700183c5500300b81412102da00c80c82c1c01c0c501c09400d174010600060900034600110f200341d40e0080380700340700c0b5558000011782d2b01c0300282d1203417000358130403500d140c4142d142042412803075101748152841003100000030014030341081c490a1448255807800c80b41480f0402105c500d5813000c0c0000d1004100841c82d8050402c414034026090b02d4000c18885010751040100c20340c3d440c540c8180729040754040c286240e0761100d0303041150801c075060004a00a1040c1d004c1f816084100103146 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 745915809 1250 745914559 745914641
    0x1080c07291905060f151e0a020106090f060506030112031412061311091c0f0503032703090d050a06050f090d0908030d0b0d0c091e18060c03 62
    0x42001d9655201040810146801d4980d0485102021b500304005624001d1030254008880b000344884003200710909a40b00c1015107006075101c070010005924a03020300c02c15506215010f00020741440003041c41800140f0a40004c0d105504001307003414040d45c01441d0203a096541181c0d584400c100d044020390782598181d020304c00c901c45201682c0418480e05051240c2c1200140c5400003005c20403201000c1da01342d25500001030450714001406c3c110b8010004c61240e0051a100c0c507002540070464030071b40700c2040c11100c0940701e0103001c4802004070b500800c002c42c2d400742d850849040943c078218244800810140c0b5004c02d00000c0320701102241d2042e180e0004031085000503450031906401c085c4114680390340144440c598491031900b000c1038400000c0c0c034042c2c40302d01da0b844111000c08183d110301e8040341d03200c2c43c41c0c05040f070164030b51000d850404028465041050030100c000c002c2940040c044640e50f9074100e003007030f1180d0051200c1d2074400389980ba652040c0b04000d03000480000d09 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 745917059 1250 745915809 745915811
    0x3011503111b0c1e0f01081e04050705013f02090310050117070f15210e0d0507080904090c1a03090d140a14040902030103050a1101080c072919 63
    0x1021130340e0310401c010b5003203000018001c040400180001502c0030361b8085d00c4462141c2010113001e40c40300130134942da0306c01c600420081c0f40d064603040c00505054003944c40081d04008400400310041140300c402034050100340231481c810055461320320003e000343c06030300750315024590364550072159540005050f034013072041c02111801c11030b007615600c0364280f260207040c2e030a00100704050380c085c0b0140c0c144c28840341030508402422203061300c0ca8404c041309100b1090780d94130200e0916202048503555130041404c00510307007141e03602d80324081d01030807140302d214079100c06800c400c00c41100c04100080841c1d4805106a689204482409401c01c403072602141c819190441400382c400c18803411121801c80302079107042c1b40781c1001c80d111049188114a801d80400000aa500301d07840110b000318050005020038001d18a8000114180c0c0c0704100e040212034424400500101000c45919643c00717803030b0175500d20606000700020b0090b0192444405802030420000711111107202441c2d016140c0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 745918309 1250 745917059 745917079
    0x1209010b06040816091e09020f0603070c050d03020a082701021c450c0605040503010e0606010f03020a02070305030a090807062303071716030e0303011503111b0c 71
    0x2c40c550480c1d8403160b003840e0940003181c1c810540781c811f03401000020300250204030101c2540000c14215031058400500140608404070140030b801c1c013910345034100d0341c9019485c0a580000081c88104054010507114002c84010300401d03481a032040122022140295180c0c85100010380d040c450a00c08000418100710210000e0080c40c1c940d05110200c0039803c0c0c2c2c048800c0300344190b018000036503a60324008400150300101d8403001003100284910f650b080d60b02c6040c10285420358400201819095200301b00340140360b030304480d003512421a00d150060300c484400004038506102540702601d107000004003034518940c0302d0071500030784401070201c4804a9a9150803141c0c0a441d80345c43c0c03400d0170400c2211107601d00d584002e54100140745042c00110400481031000d004040c1c0300c204401c404011003006598250140d03100068030714010b1402c40d0314040c1c5d070000341081400d091301050b0740d850b0040701c0101d0364000c1c1c0701b90184484002402c02da270074260a54407000c08603036911441150b1 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 745919559 1250 745918309 745918319
    0x151e0a0906090317071a10050418111014040f090c0203030f071209051005060307050f0310050a140106020f19030e1e0d08030f0601020a02061209010b06040816 70
    0x103002c1c220780e44207200c004004840b1244800c15000b4040446144c840048400504091901c401e40603540310301110300424500810841191080302281200c4e01c0e0030020781011482d662041480b004042d681c010b00e440000c003084503040050000d0181110002c94041004498041041d042d619440c40030403980035145400c1c1e9880c002101d454100032207242c0000c0000d0320a04540344803074200f000c0450800c8441d07440a00b8039606c0b800240b2804e40d1241000700628080103004020002510880600c1da03980010070340321603900f0000503585031500007040c5181c1540e48004804442d030021524a540c540c08000d4442021800348005407042e00728101c0d03a031039400e506c44c4210f50715803100f640d07030f1780ea0030184164000c0352100c03400b41103480045030829031240800485518414803100340e407481c0200345803a00c980f0181546046510840b1010f0040e1038100407104500034421038002c943c3d80b0200c1890240c003200101c250402c07000f2800041003500090006454042041c02c604210380719 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 745920809 1250 745919559 745919567
    0x18100809071404060504060e48090301060308072922051b120102070302060718211505061c02040908030f04031e020a02151e0a0906 58
    0x503254140550402401004004000c40c6000241400a4804100310795180d00181c01c55000d68441e2080d034195804003c120b05c0c840d020203000c4442d030800c840504a10100c100101d10440b012001c01c12411030f120070a00342c0804c2a6010f980000700280101500c9252451642c0c000b03100c105e6180340c18002c100745c007064450080c00c4420414071a00d0a560b1541c2c6100a0082c02c6081c1c400101b6695101c03001090b000d006092410740003944018846140a040c8204002400d40c8291103901c180311840002c3d034085145500400e11385081441110014007044400107603520407051640c00c202d80001d5880c0384040c0d1803683d8004c2e070030101c0070b282c1c406440741501c4040342c44070303840b2220114855031800c590540003c0306002900000303424082c0d580e030082c2944207803414011000381408110405500c120241508992811601020b11441001075520503602c07200030f100c0d03102144c011103000701800030b4604598402d240b00c09a0100610100b003558000140c2c80c00181a4445c0440d042e802 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 745922059 1250 745920809 745920811
    0xe031308120712080637050306011208070c17060703050112030c02010f02030c060c090a050604031a130501021803011a010207092406090806010e06091911181008 71
    0x10029030201501e40003804c80751800000d100a5001c05000c1d401541d54507840302c8104a6008204041000c401c0f0305000740c0004c203290b22041c425440780c40140707c030b002406e012445441d0300400e00790f1035804134a4000007846540d0820003910101c0d04058543c22000508580a035105807000c00140c0d80f01e501600c3c80429864015020500030001100154480d815050314007005105880c03d0200d00d01046062560a48540d00078030004145c403151842c00d82000b10082204a81c2c1500c3c1510b941d641d03013060326200c202d00101003005d40002d000343c2c2c100d00b241200c0c154000300845d0380d2480f520545401500c1880d40301e00035032800f58180d020124070031421140003c140c0081200c42d182040e42d078040c205080d0f03601c1d0795612409c110340c002404d82512001a010686401d9402401c0140b06d91816105900028040e03c40009000c09904d581d029142c01c43e0306500c00740910300300e04d059071000c0c00402d100c04402540004461b40c1038040c0954401e020302d0204c0743c03043c0701d050300d0f0740427600d090b0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 745923309 1250 745922059 745922063
    0x30905041a010e06160f05100524010513061101060902030705091c02090f07080c070c06050702040b060c01020a020c09152e120b03010c021f0e0313081207 68
    0x8002100380c40d82d40c080d16000c0c900300d00013460103103008080f81882401e9000c0100456542c004940c0300710400c074051149032040017681c1ca0422a0b440e015400d042d8194203080040000e030040c06044140e0b034412422588035020121601d007003a565458000c2c40c03240d440c0d1414034107500e03107200407580d00224001c0720300840080d69080d0a1515043c1013050315003120720f0103411203513005000f000580b5100041c1d44180002007613507071945030141e4041c0407500d000b0301100f110401000020001000000d910040e9604c610703200f610b4482d1480400c00400c0000c2040c1d0340004049140000340c10150000c040c0d00503140c0c250382c1150241c0052020070791007907074900744402c4020301c50b54890826158400481c00b40c80008848152865a0640e11824266100e0001034815400c00280802802030008845068000300300baa540440020b4640c01e014450000680704601d8102c0081440e40040100e4081d6505a82c2e60f0138100019664000151091401900490108007400e00d00c0d00c003070f10b90703c035 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 745924559 1250 745923309 745923341
    0x170c15040614091806130b0d0b04030302130807060e0603040f060209130f0207020109051f031e0e01060306110304081e07120305150618130b0603090303010303090504 73
    0xd410040162100110041044661a010301250090ba9a480d01c0b03d038000d80035070b0f40e04840341403410074421401d22141e030380484507092008060703590321410030702040c0e01d40110801d01079448601e4201d0103032281d81e08100b07000e10804030208881700042400411034155032154982d0070702003024415140070440d009403051040020440100d4855002024030000061160814145c0ea5402d00e0445140e010081d13411680418a0011560031524a0f006490304480c083c040054038a4240c01c83d04400076184201903d60070301440b6444805001c03860400ca505040c01940400d010181c02131803030b40720645590b030030442c4440c021990358080b28040c42c1c0180c42245005840c0030b602c008507034030b5031101072190b5040107800c0100c1c10040e9410b0410f82d066401140360305000741e1b4074070000c0f00024260310944042111040c00c40c540403c0c15041001540c02140e41201ca942b40c070700914000c1d0046800141c004100075503540b000c8000e5042ea44030342c441c0351039182c54006000c1201c0a6218040395070b = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 745925809 1250 745924559 745924567
    0xc010504090f0b03160e0a0608100c02070b12150f0d030f0c060612060501050906010507110a0509090d1425110a09140c030f010312021204170c15 64
    0x4005a402000105080500103c0c80500741000319161030549400e41030340e00024030060100380d0200b094690407043c2850700707100c550300b8581c03070b580c849a4000803c0d4110780e9620114003a28000d20a61009000c41c50710b03503864080720420106244011150703140859401e1005640d94508090740303125009000d461a9034026560360161415160107000d103080c0101e4480d800001350180c06004050140d86291014901c0c5601c0c0c503200b6134030183c201c00d114403d40070030000300b664008280d07102e19401070020309a080c50321000c0344d100c94040d000180c000c183e20041000d01c4034001007031417001e0100c0d031301c1180e141d8000e001000580100321604d001f440e140140c42c219054500703854041c481c011604d807105511004001101512558441e080107a155005020b4002c2960001a40305900f40001c40ca10324041e001c00a04800500000341980120120419180e05c01c0007e40900014800c546594039180c1b40300004c05010b4182540562080b0070b0680307040e01340100c108401514584100e424 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 745927059 1250 745925809 745925819
    0xf0501060c080f040b1809071409040c030609090b180a0819051b01230f01030807080705100b0a0603021215030a0803130605100308040e07050403050d120c020c010504 73
    0x7440c0d000b40b00d0b404003c14140408030302401144020151840032801d496510601082400800080141001c09001ca0014001c24501c4480c00b01c0e003941380c003110006440060100c0540c000c09041d0421801245042c2c1020204490000024098440ca1010078503982110800b5580c84500c110700400000c0103118030004007039900c2d0703604000d9910b030611600701004070407510b1540c2d440b01420b0126a449605440181d41101740303941c0e80d8040d005601509181c01071001080c51418440200700b1341001a102084c420044240c030a010f03030140954982510660306000a0039030b503501184210480080022203034000c1c422035404100304407408049a0310700c8001c040742410b68403e183c1600609015800180f1050000c40c4102098000014040001d040c080e00700c0c1c03001000000340423030540c0c041c408221504142c408071203a080c07000d10740e035440e000c040f949406164001026841103c200d045940d422030490500d02510690030010400c0c82901281e40c0ca5502d441e09010903010001484 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 745928309 1250 745927059 745927073
    0xf060b1c0807061b0216050f18091f0902030105151003051513200901170a0908030903070b0c042105010213080a140109030e01050918011502010f0501060c 68
    0x1d2941c007501c000a482a8904c140c5052098030905040058010040c031440700b085040c5a0006004151040d9810800c41404100c030b4074503c00b082110001240d001844650040090181d1104255074401c940140d812182010b00000c142c102c0c072950030480010b079490780170720701c0311881e6000a05040c0380c1d1040c500190020000038200020b01042c5400d03400a540b612060303003890b504801400601400d86409644003503101c85441004000200181201a0b07401489206440c0c2314412046007906c1c1c045040f0014a500d201c018880d00c1d020007004805800403001e42009801111201443e40c2c0301004c9040a124a0140810440659444c1102c0001d59041108003034810b6000500e00311003600b2000ba240303d181d00c4082d0581c045807040d01000160200c801d22809200300074002c0348801e41e0b0103001908030301041d83c1001008102000c07186e481c0401280c40300e14101c0f05d0341c0d00e540c40e00082c000c0541045603103400341d828400002c40750070540c41418100c80039903842c01000402591703240 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 745929559 1250 745928309 745928317
    0x6060b0c160605070b01031b0510050a0e0d0308220219030501140c2a060109061508090c060904091401021e0c060a090c0e0f1014090712180f060b1c08 66
    0x238016108100030904c1d858507074401d102000740d52070f0715030bc0c0d4110100082a101282e07c58a0003800381070003420000e60440c07240c50700320100d09035509001800c1c00b44164100701350b50700654410b00c01003e04500d0400088090160b038002d10092020100022440d89099010b843c07038001100208100000100b44200420385162510405505411620b0b10306141080a81002801c0c0da80c5032410412082000f144032051030315801c11244030710f40700003500e84a048600c10a40100800030740c3e1506540c0d01c0c2e11154480d0361084e0800141482610000c0c000d400140960392351040d8061315010700c03201d8106448007a00c42a00508295a41c0b40d0365001030000b4000c1141c080200388400b03d040210100c819200e080041d075500a00e2602111200300301250740d00480707250001010361040384d168610318541c400e1442c00c10b000d00c0100110b0035001042d041150215110082d01310404020444200044031800741d20207202e107001a00070403860315441c00020f511005540280000520518064 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 745930809 1250 745929559 745929593
    0xb0703290a090f0b030c01080408070b060d02130f0608070b03010330111c0215040507090c0203030412030203070f030f110c0c100219080706060b0c160605070b0103 72
    0x110a0b560384400c901074070104140e04000c16203030500c0c010300e420100306600c0d4005091178007400c582041d481d18409481a40c3c0c1c041d240344030010005500d51510080801d075560b01404c0b1070700c034000344a1803500410514048410042c03c145000400850010310041607903c0d400d40d0900d564a140c0c1c45280661031080c940b8400e40c0b00301910080c2c1a401442078000030400d80710400b0307400000f4640c0e41001807a4078030799108401031903201a8182e0000e540e02580510480c0c1c4000350f05d440c2025407130681141d04c00702d0018102004d401c40d02d517012000e0360055109800545c18100e04c14829016400102c03031100003d250640405021480381d0080d00501005020002c1c51440300c420080d0305070322030062000300f40c0c85903606040908080003a5034040c0340c90300c09007079141843e805100c000f42500d0005841c0b10320201e1140e091201c0c550100000b44900480c10b43d4480700584880d80354081e80c0c01020403800d04000c006070b094010803c8078200380c0d0007104607000c0c0c1c0c20742d502d80003250030301544 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 745932059 1250 745930809 745930819
    0x70f05031b0301270c270e010b13060609080604030807050a030908030705220b09010c05011b0807021b03060c0a02010f0f0b0310020f2a100501030b070329 68
    0x64608020307040030300303446504d18070400302202d9100d041c1010610030907800202c0403140341220031005104045007036520360007144007190a00c0c20036980b9002d082040e0b04076a000500c0c17400302a020185038002da0403a4455141c410282d9590460719864260445000c1d0110b450980051038191141c402480c0c0005142000540001c5544034400c4a0f0811145040800c1c030002c1c8428444030200b1203094000c4800001409181c1407a2140b40d0f14002c045c20941030125220600c1d081040a42001c4024a064070101500f10310140d801000c440c4291283c50141c0282c52201c4c804884044400e0322a0401030002d2a481c0c0300d240f1811b217140d1003145141e085540c0ca03542110000e44074000d60810b860991408994690b00d0b40806061825080a4408442c410450b0400401c50301060b9084880d074128141034188000c105000340041ea6246201580903400c17181844050507402181600d0007100d4404072680c400c042034040758018030a481401c1242894450803140390091030f0342071740780942 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 745933309 1250 745932059 745932071
    0xf090503181f03020904060b1810030e010207050328091e0b0307020a15061206020f0903031c0c09031110021e1b310605100809070f05031b0301 63
    0x50b0049444003400e60100094000506010320700d028001d440c05030002c040e007680391510004d004d100d030303640410f4540c0c058524110315403030b842e000350f00c142c0c00007017000e009540d1101980341a54580c0d0090f030001c2a015611b42c41001207202c00900d82ea41d042e865110a41c9060900300d200040b051b1010310740c800340440e4040480d0408074500550b003e804036130028044802c0624049000c2c100c0c5200b03004002d13141100412200c8030300680c80400717035042403006944584089818829101e00c501c040d03018440011000c006840a9000450a0740c0c0304d42c0070081da543c0480d04481201003880040d010008030040c4503220719103180361200d00d0001d4012108038001000150840c5003542c0d0b8003c0d025003086c91442c60040d40d812100c25119000c07541c201e04002203003122201c0901c0e02940360109000b40381a00100e11f4907a00840c041d1000400c1c1d054808480d6800402c490340441d1150180d006802d4002003c01d58100e400055490003030145c80b01740701d403100c90094800700c0281c141e41592204 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 745934559 1250 745933309 745933339
    0xd061119080906130c0e1302280501180603020f0d06060f0e03030a0c0b060307090c0c020108011a030412140403081804060b160203011e1517100507121401090f09050318 74
    0x803072500404190707000900c040030955903200c2e1120280d10ac10305005032250a48031003841c940c4034405460450034010384501c065100801e20f801003038014072000345408004620590406a22400d44045556042d005810001899100e00072a40d041005c9030b1261030142c0002c1e008030450740e004801a003201c6085544c0d1a141c01954000054040810541c1080d0403d40d40d011904901425070804082d041d180806d0365041c0c0c3c0d04c0001d00141c40100e091820b0f04001c1d02ca1311700e00c2950340c12085500c0d1500d0326803d00031030a40c0b00c0c0548a40d032112564250601341018010f960881f0100140b050800c42007440c1124801c81b9518102d0745556030f4616004507040f200c4e002d20a81c681d5040003d4030913035603d42e4a0203980c00e6002020300b1042c00d5030315448090001412803160300e038110302103815252800140d981c00724a9400000060400c850074802d02c0d40a000c4a0483d112500184400001d40a00c1c104980408001900c550003c00c641b10050000c1035000420303031406400c000c04c00c1c14503 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 745935809 1250 745934559 745934569
    0x3050415110918091203100f06020c0a0602010e070b09040e061807170d12290103050604060308090621040b1b090d061119080906130c0e1302 62
    0x1601840d5445034049075254083c02c109080c414095544440c02d821800d00c2821590340d9200d00b280c0b10007040300040000d810b0356042d48480000c0c00240080c9000949805019494001d18440ca0380a603424000008905205020b10000d50543c44081c14006050191006165010040044e00551250340c0c0c00300f00001041243e114100c600740300002052040442420941d46903c400102074509943c0820703100c2c0843d0600c00034605090030803668450f038180c1070103000c40c400c1c606207014040b2101d458128401002c004030083c240c2c0c08011640d608010401168800d010103031214209010508190510000402c030170703400d00000140000c058641d1154038001101c1c2160b03004050020700c0340a4031190709104c40e2214415410b4181390112001c101412541c0e180540025201c40200e01c404440c10100c0341d000714040c6450703040e8828064040d200c1003095030201c03040c4c031900340041c540d000c0c03040d220400385074020000d08040b4030300f43d0642000c6002604c0708600c034009426072001a622 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 745937059 1250 745935809 745935821
    0x1305070803120f0f0f010618031208070809120715151712070809060d0b030d02030a08150d02010c03121515110c190503030c070e18030a03050415 64
    0x34400d500b003054074028440031a911030141c80822014102414040707418280e0180c503040d5521841c0005032141502e54003200000c00f82c0c4050002890440107600540d0b0100c1e0781340c45400d050315440440e886e850600c903070b6a201924411925041130184400060300c103504c080c402c1c181044003040840d4a010b041c10403202ca40e00a403200d5948000c40f1902180500003030041e890001005030820b2340585400f0707107900c2180c42035841283c0c0041c0ca640003449560082c007100c100078049801c103486401001c0d6690303003c18022030105441000203105c1e5680180481d00040c8094204042d401581c1c0c0191006c94512004405100200c0d0415010503128410012219401c810103550340e480c00000204081414100034100001c00240e1004030380c00181602070783e00180e40700e80840100344803841030f20300b0a40205515010000e0007030048a800140941074600f5018800ce094540704400308a40094004071401030f0000e01c40042c540d8029170106900c00d01402c3c0b58900004256801000c030350b2 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 745938309 1250 745937059 745937077
    0x501050a0207021509060307050904201812120703270302040507030203132019080c0a030b0c0a09180501060f1803080c0f0f06040203241305070803 65
    0xe8086004019850120312003032407002542120717440c141500d8046100c1d480001c0c1608188540020040c0c07498889a01c50158010524010040741c058210540c40b140d100010402c030031208003603a0340d00d078074003204e0400c4c40d1040c03c001040440c08100c90102070b0740094034180c09004018131551201c2401c06410f051103407590000040715401c0d031040000316280580120100f600c18020807100e031300c0034050b03078a00341d4104040701200351108980c04d400791144609150000b80b01805008800031511000050382c00341400c2c0c0d0007029002d030a00c100c02180d884082c203180c04143c041030341c0000840040100c0801498215038040d00c0d881c0742450b00c0c03540d00c00031124541c0d44004000150340700c0f01c2021921a249804141c42104081d5880c200089000140c00442c0c0054012802c190401803585400d1082095480042105800d903444050840e0161302a0069591180c02c400114548440d0010110003403841c6444910210080104c001400c540521074980045540d0500b000a0240700e4 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 745939559 1250 745938309 745938311
    0x503220906090b030c010c050c030d0e0a0522090201022b02060105040e030a120b0913060b010309020105040e07090503030409062117130b04060305041b0f1701090501050a 75
    0x24580003544046450300c0e444442d08038a80001c001150340c0200324a140e06009181c2030320f0744846030500f00d05000000b801e69600d4410184502102ea800031008125440c0032140285199502c3c410700a803118108101c85204080d1204031304019240e6100e42d4041d8010706c11900e920b052507000d003024641c2a079400c4215a03914600988603941046680c0c054407050b14144400d40360510242d90380c0c050303c0101c0051004070b40110071880d15540c0280c03524407008103008542e0810304081c0078035000c203142c20ba4440f814412044000d5000b800703514071041d8180c0d1003900d800e1919201040790b06001e4490400c00008443c00140c3d6038040010344041c242c22200051010303e4032201c43c2100c0950b2115084014049085801151540003048480c00c80741400540d200e4208428091201003a08144400c1d0408240841c00c640d00d40d004500c03c510881c1280a1401d45c80341888141c4014030801100d00e009072404c2c40034055000914501141d0100007081c07840e900e0390380e142911f604890ba03040341 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 745940809 1250 745939559 745939627
    0x507080c01140a0c0f082406030a020a09060c02010e210a060f0b0904020a0b031b0409050717161d03011817030415090305072405010503070e0604090503 67
    0x9500a04c03514002c50110b042000b403014428078050490f813001000c2c803180b101307680000c24404140d101d4076034030300c4002003020350380303241550100c00250041c000400000d00383d15404554a07005640d26190250161200ea2903c400281040342400d000980d4903805032007262a1940c07201c04101e03186c01184200804242c0c0030608182c00211450029031a101780421000d10000d610f51005220698201401d516030f280da900001e40f40002280c0285400c03c0400540011031300c0850b4004d6020b0241d568641090721040c015050f00404141d070000b84090030700b001e940b0203e00a02c00c0404c2195002c84010040c00755800080c02c40d0403580b030b095440030240400804020b8580c0f2a0f020040d1000b20300c40c103608041d02e50140c50b1054500a4103400c0c2c4d140c2c02c40d81418011030660f203034981c1c030502444101e408016100c540c24100d15003110f0603400c200000c5030914001c24210260752171200c4e11159980c1d0b440410015040d651000e1703030780e40030400c1007080030303030741c1e50000000090100100544 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 745942059 1250 745940809 745940821
    0x140f01091203031413020904020f011701170106091e05150a08011407080403020712020105070b0406020c0c120a06090f060504081803070f03021017090703020a0819030507080c0114 79
    0x40c82d0401400c010401c002c03800c041700140d580880b0b49401c641c040e07508182940307075040180c0e4514031404824840100207000024580c045100c582110840311000b88001541d07103a07054242c8030100d95000b001d00c01d02c00e086140180c00d51209912011203210540403251450124071900020307080085540d443c1c0c00d010070441210720b20507802c00e54500e07102d0018034042d14025151007260086854021440c00c015056a10500035120041e0f081a804041b904181c9040701c000e52110500072414042c00180080340c0c83c2038003030304d043c05020b10044c102150f0a940e030310005040000048500f40b88540d01c100105410b840b030319118521415115980d80c00c0d0301042003a0400d060304980c031960244100780030401c49440908100c0f9030546181070300707038401201a900100482ca5100085d0036410400088042c0003070640100c0b80241d40300240c2e2500e81e448140c40f45003c558100c00c100a10461000003817080009110050041c0c0c81c6c0307414034a142d055070382943e10307603081c181d00d00c141c21040c400 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 745943309 1250 745942059 745942091
    0xe10050405090c2107031e050c0a0609061101061505070b0c030c070210020a060f0c26150a0e072003070f08030a0b03151e01140f0109120303 62
    0x1400903102d1004000c120b42c07100028465075050803044001c138034a0341c00c0701030b914001c10042020b1688900808081c100c07010074404100e08454066820303109049002619081c505410801e03114103681c3d90fa601400d01409440b0a1035a070581001596a12000036894101c02ca0b41c0d143d907000e03036a44580d210f82030b052080000c8805829601d4101d410404c4c080405112001c9506060781925501c1007851500801d905140795807001410040c1400c601c480c03009003681c06041c0f1402540c0b6038102d000700c0d1010190380105004003404608888002240d4200c0048880c0f003020100100b044038240d41701c5284002e920020b8554070007090709149107860b0008019551016180540010341c104076098071102c0c0910f007100da01905861000011445201c203076004500c01c0c0c500070b4102d4689000f03980304408085c000321045104280080d0642591402e14842c00303040791010480c8800c0002580100f140c80600e032420981031282100000904800301050412400d020740c8001070100003020100d9 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 745944559 1250 745943309 745943311
    0x40c0501021209010806040b040e1c0e011205090c06070b01050102060a020a0c0f02210c03010c030e0615060d0c0206041b081203040f0206070818010215041203060e10050405 76
    0x10303041d50040000021203020315415544500d40900c2c4c02402629000082801000c00c5d41007243c000741041070070181a200002c2c3d03106041909504100c41d80d01c02d220403a41e007031003c12218000f4400d09100182194981c001036008850725094851254070840011201d9008103001c40e00c1010f1000100407075a010b001155101c005070106515107a2941c900030154404160001e081403500076456040d91901860410580310741a920050103100b09000d43d039400d0451141172103036003004400c03c039a5219000301ea9582c948a4000c00c140c1d01c0d0168407444841c808400d454125a080c81400c1e2140c001c0e004402d18525580c014140c5401c040c20808286801d1011500000001c60410420281c00140710030000180001150721f03a00c0c0d91410078400d50192700065070200021a50206000d11107006010240c0310f540d03158010b40713040e8010f82e291844a000340100003111000540800d00c60003d1040511092070f0004601d512180f9400c000d00741980d40b2540380211540502083c24584681 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 745945809 1250 745944559 745944569
    0xd06090c0e130309080321090708030d061a07051504030e130501050108060411160f050a0308072a0818330f0403170706060308030604180209060105130f0806040c 71
    0x5545000a124902001c10b03440d58000c10720881c4041c0026123980b000e000c150054640714096982c2d030b86030f00002d14050240c5000c1d091400070000040075100b0341090031900395230791202c064890196043c0b002c1d0f85851006005500b07006c1d0b5241450990ba0740e200600d414006003010004e441d5042500040c031080e00108040d00480c90180e20b40a1907040704140c6150703004240803003640d1540b501e44003c660b44403040c001e0080c41050080c81c20150420341c1d042c840c0b07010740c0c0d498181c5411034142595034105e01d45545d10042c0441981d0000c519a40000c068401d030780f581d00d920644070600420314184c1c00d150503110b510f82c404e50038a86403d83c4000141201a0054034070704045003104950068811880010107161189416024159850059840041c5c2013201000040e6a03030900b40a02e600c01c9900501c20303864551050004d9096000c0440c88513005018841103039501c00056950303074403a07511108110488a030002d0300249903030640c000346c42508054030b41801c091038401c038601115004 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 745947059 1250 745945809 745945813
    0x41716080415080f0f0412020c0a0e250e040f0603140a03020d030b0108010e04020111030a0320071109061f0e040b01090515070c0e090c031b0d06090c0e13030908 71
    0x18418905c0c0d0910b00c454106400003100c0101542c080002e81c9000c0d041012150050b00000c0c000540c11504840c4a101c3c1c1c44840981c4264607031000b110045100c0c00d0074100c0410b1881f030080000382019408030300d440c08440c00c000354031600d0361034041d042c248074220055160302008140b8105607040c0718007a02d50b00c41e030505203c0c000c52640003a0203284140641032144810b0400036055a11420040c06c08941d1a420740c0d07a103c0721264010081c22040c1c11200910b0f010b014000701c9110400119403000d40c01100c40559212503c0400005440203800395600c82150554400210103040d01d0200501598450744081c14600060205545c10608218180844102d00700881d449403081e5207458a41c08a65a41e05d6400307103402e900c0c0390b51a4100d018255920020004403050001c0c50f2605201d040301200c408020701e002a0004c40d4440b48941d40202001c49201c1c001074150300100000c1d48203448084100d5201c00c001d090140040780c5955995940a0f00303d001d040d009501c100c06400e000c40 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 745948309 1250 745947059 745947061
    0x80f0706140703051e0304030c1406040c060c0f0602030a021c06060806100c050d0905011e0219050a150b090c090303091e030d031a0108041716080415080f 68
    0xc071210180141030002d82480310010380c00c2a00128036856020010340c3c004810b80741d081c64180200b8030981c40b00d04403505a85240326401030000092041c1c89580c2c400351703c610450401c20100e802d000d202c801190313a062074036480c2002031200c2c00510700c01c2003002d100680f64210803da403000ca40055202d0040b5600d40042404413a504c0740996510510940c0c01c841e141440340704c01c0301d80d180301000203000750082481002103560b05c0340a800c101e80e000d036248940d4590b280e200710410200d0070070010144c0d00c043d40e140005c08084940400103030281d801c1d502070507065201c8034002c1340b012040041c099500c0710040f20a10b8080000c982140301307218090308100380b080c0400d59901c2207039911031144242d11194040800c62030300807500e018028050f5425000c001d000600500110042040c5640c2c03000020038245d4480e2410768881c0307811681102c1051442c1b002071181d5405040310601c01000341a40c1e0001c294002c0041c0001c00070183c08800001c0760b40c00c0105165005400c0b4076402d05080 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 745949559 1250 745948309 745948337
    0x50709050103092d0f06020307030b012c12150105041103090d03110d090f0201111f09140708030a080703110922150306050c0a0f0e0d0c080f0706 64
    0x50080300a0b1150009410140800132489522074406001c00401204015902504103e01c58000c3c2d4020340c074a403010321080740e20350015600c10038000207544071500703c21003034620000081a0070f41510006802600c0c0e84202c560820f0400300c500d06d40c0e80c0582c000c1d0300104000d041c01d220304110065000704560440c00c00f00f0500da00c4003144c5103028100f6858240c1e50305038030400b5003180c22144602d8020030003480b45180c0710711074000782c100c280d0124000e01d10041005402140700c000321895000545e05c0348200039045c100601002200740c8114020b2262103051281c104002009083d13588000e45d110307548180001c20080000700355004040c100030003000c05400000607a400140308903507224030b08480d003c441e24109111405460000d05145c20300c2010118102000f0589000780401d00150751389980d0160b161260340005000101c221025000c05480740340005040c1c90020645c03103594045807a40c0c05202c1c1e454101404680149441c42d6003034404124480042600c0c0c01c03c40785068000f = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 745950809 1250 745949559 745949573
    0x1030c060206011d1510021b03011b030213080a05070f140f0f0d0816150218011d061308010c0305100506090307030b0c04050306010e090a140a0c080105070905010309 73
    0xd1110801d81d5031110114a52a001c09140c0c217100502605c261002d8201c2140250f4074100d9141040459001d010800c0f803034141800355004090004042510159003064110300075404900c204000701042c4801180107507042c082502414003400c000c00c1150700340740e00c090500107035074010030300c2d60100c2c444c14202c0c0d12030010710a201601242c10103e05010760011807481141000000c01c50500064031400b0440300a41c5812514000c15800319070850b17203078885c0c041b4031030040c04215010072200203054541c40781220810145030130455107604c00842c0e010907419040309149890030b60341c0070000d004c41c100910030f001c0c060086140c140060309100100b840035003200c0c00703118020304001408900355101000840000c0d513019243d64424586104000b00b2030f0460700070144203000d41400001d0044030005018042c0300b8880c05851030044542d1110210070750a038a16505000b02030312100810a94001d03000103181042c008105484e14410041036000c06401a0b0f042c1454901000003050078 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 745952059 1250 745950809 745950839
    0x5030609010e12030a0219110706020129031912170f0402091506130e0c030c040905060a09050901050f0106020d0c110109051309110418021e0a0602010501030c06020601 74
    0x40e40320300d550381c1c1c640d1a592006441054503100740c0c2c00038030500d03000741f5900c01c44480c240d00c0808107507402c01f40c64290403800d07a02e40301058005401e031032003500280c40041c1203013451904006c04803813903880010380c0d520b000119101c095880c0841d6495003000d05810455000c2807100c40041c0d041c541c9804070b01e1044141001c0d00107401001030800180320084003403c44881c0310001040700d40c490381c0c01752109408070102d0055000c051080c00200f4018016031050702c0c05180b0707c11120303040c141010311032001080010251540483c6500001585406500c2010b0141d0070000000c981841c0c0b21040252407441a4410021507010b82000251031783e005e8004485542d202f0030800840b141400129031802d00398001990003103040d800b040f080d5109902c40303902544030f98486405011407408010840e03000c030310803011100c00518000018580030500021000d940c04c5c1da2507800d003212011414030050385c0c109030b015030364560043c01880f29041a44005140c60f1004004d40d60401200f050b14840c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 745953309 1250 745952059 745952083
    0x80a0204180b12071223070b0f090a060521060303070303020306040e120c0f0309012010150305010f0c050901080403020c0d03050a030c1812110a06050405030609010e 73
    0xa582d032480c0750150744041d481d801800401080300c1c01c0030b403030b280105103120f01d8607000c6540c01203442141869804d13224a07101015003110103401c0c00c5141508440c10750740b191503140345d0b640c01044210310694401d2114005041c05030340756910b58030100707154481203002c2200001e0b62a00c40081000c607540010441e07416550600d405605c2e07860f2400032402600b0391360f5000b1518042e40c0700c00d03400860800040c00b6500b180c482222400049500c0e6261031340300c1c0d002e545000440308075841d6100804c01011150018130141182e0210252400c080101d0b40005401440d00700f1040080082c400c0c24011280e000100c01010410b074030340181c01030032500c1140342c464140320b0004000750526000703116503140071102502c1402060001e00d0001d15550144024070003081c985003030441d03410300c20000d540700440001ba80014035402d1100540001303482c040101c0309804040c502441c41e4807040b000d003004140d142c0fa0151034608040c00c141c1860342c001c0980703c0c1c6a2611b4220150840001140c600f552 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 745954559 1250 745953309 745953311
    0x3060b0f070206162a050a0b031f150905030303011d071b08040e1810020d020c15070e0d0b060906120f0f060717060603060409050d0906080a020418 65
    0x75440c0c03002c241140034480b400c588840c03c4000714014844080503100318150485002401c1d08542c4084100310f400c10f0040c5604004c06c1507090080d0780c4400c0040d5040100c0708210013000303440c03076201c903070380e030200d0300100d5110b03140e41c01c03001400fa0070910342d001401040703010f0350866040c990014041751014180d011450306050105606500544920444014010850381c00403518140000030781d00a2285405440301000095144d8900e4020f2411460700074000c3d1094080502184010b50040c114a00c8032680c200304180c610041000b5011208001d890728009510f0280c41c0034203629907590318680214200f03803201c80000d40120245600c00411114080300b92120404100001c50000e40301c1390b54402c0000b110303c0000e0006d651100010058115200e0703941d10380089032071140308074141c0d94620030314010500c1c41c40c0134005143c1c80b4001074000100b20126886591600c2540b040072000704c1c01c080d1b02441440e40c0890f0441d0f1090581d841585414604000111407660803d4103500071 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 745955809 1250 745954559 745954567
    0x4080316020d1a0115140904270b0a0606020703081209100501090b1f02031803030f0301062a031403060f030601090e15060a0506031b030a1a0103060b0f 67
    0x40d0b555100055859420241d50303030307100c5083c900c1214850f07000c1c015460002d480d140801c0403184604800c140103da2000f1842c200020f21007400041d02071030700c214900451800c041d20790304104990030421030b401103401c1025401d20900140455a450700501c0854002c0c500600214002031300702d0b0760300f14201070301c4001c0c0d07962654200d0400100c80d5070040d03141e06240000500003400e8001011400d81101d1045003154070303800b0303800c0c00d4090b0b1a40da00035170001d004030034160020314404007400d1009003d9a11788501e6910504076940240c003e03501044444034180c102880407070948810f207050441e50001241103880c090011050801040003140000001405945903120620300421010301182c1c840e5841e62070690182c040c1c0782c03a001740d034032130b0b1000c0c8541d030b56000003100d000b0100644a1100e00d810130b0305014442d40001c00da41040e0700e61050103044c140341c15001310b200751415440020880e5403018038115800400203098105070815000b4015034019908440060380e50103541d41d03803 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 745957059 1250 745955809 745955813
    0x706200a0c0c0e16080a14010b0a26011d070203120612100c020d0315260a0308040209010b2b0b040f05040201110313060c140f0c0901060504080316 65
    0x8100b05500a83c0500c2a44820b11042c0d0880d4801c641c000113203929060380c1d541c0c41c000914111514142000001402c7d40c0040100059a00040c68004064607101d9003103140c941e103414070b91061084aa242d826184010001196508181c0005c2c001c0e807440c8268500b0840c100079900d0058443c0c0100f03282d148000700f0015980d103001d85043c80038841c2070703510b985a00c08844e4001c0860858103c058080d214034001c02e40d2180c4141300c0c141c0e0f03211250368000c5003007900c260301140c0406840440034204a510003055a0104003810791148a40d482c00000c2c6420b01c14440403141c10b900c400782c110b9050200c402c00b4a00d00ba019100c030304c8561070074180c940c0c0104101f005070041041c8182c00c50b14040d55800150510b0300082c0c030a6000383c882c18100001b40400656074413801c018560140b50325041402403e21a0122040b082d00a5000328840407001c10071a06006a800ca240c426038040c1c014400705080090034030b4010111420142d040c14070340044a5100d1080804565a00030407200d600c1c1 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 745958309 1250 745957059 745957073
    0xa0608031206100c05100903020d11030403110a051f0f0c0506060d0302030409090b010905070c03021018060f02090112050603071703070b0f09010605100f0c020d0b070201020706200a0c 81
    0x4074aa0800d04444041c41d61006c540c00905240f0000c0e0010b020307103042103120340e01a1941c0c0404c43c0381d1000940c0f40c00d16544500381e04006440555600140300e040014072940c0c1c0d65600140b82d0740100f180d214000c614000940a1400d410350a004d00c650440a10b010520219909500010985600444c04040c0c80e00300d04621581d040744806a00e8001c0a00034440c030919041e05a41c43e05404101d161076000050342c1c95500500000c0c0160f1244007e80d82031003503900038519540000301c14035207900c3d43e80c1c0c40c0b8003505c14141c83c01501640c00f1030f1124844d81d2011042c5040c12200f601000740b420407101007038860b643c5010301048503018802d202410746041007210391003a0001b01d2404030381061101803406c0002a03843c950303030b5801c00034041071a142010000044002c5500d60b1404a56450415103200d600c3c00c030103030390113840d807001c013000f1942481d00c140c031504050f0f00040c3d17252903030b25140c41140c01813a1103c807100307260406200782d21190411540003e1860500f032240d44241d1402003 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 745959559 1250 745958309 745958327
    0x50606040e0a24030302060609010e0403212d050103151a060408060603160f0501080604020c060f10080f0c01050c0a0c060c02090717190902090408030a060803120610 73
    0x6000c1c050b51181d810311440c1404074900940c1c0c4258207892488d142c800c01c0040c240020f005410b4161504004203001a00810f480e5407089284d921400c14262a91034610445085407032110900411202e80c0305a02c00b000340c0b251941c064041d08100c1d6504540f0342c54001003c40c280a5145656000a042c100e402d078a07070300107030701c0c0010003059075981c813004043d4880d001038070300742e00074410405170107000040340a9410030341e9120401302d041280340c6001100e0300e090203400c1503001582003102f40e880c06803e01c03903603108061a0000c040c503170405104078a4888100e03030010703500e40c204034001502c0850103d103148038280d0034030b401601e03107206400c021304013451028000c084003081c2000183c0e50780c20103291203201d4000c03140300c10140da4454060380e82c004e03450421001b45215100042180380d03401e10507610b001c00b06000154200b40340c5c4c0423070325182d81510300780c41716000807080005084e501d0041074098806c50020b103082980c0c40741403104400f00900400d2140c5000c0b0f18010714144224003070 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 745960809 1250 745959559 745959581
    0x3030311121005040507050712030b0d0f1416230414150102010b180f0c0c030f07021c1e15050a14180706080411060a0f08010504050606040e0a 63
    0x81107090801d1000d00d012a5031900c10b06004a06041c00211200d01641c191505184c10038155140c060754420b0450003010a007151a40c08060700d120400429402110700c100c0d14445d50103201d0700c2801e20b001a2919808040d0034814011440302800340002d140d0880111510f01e0028007202e41042c800140a820816440c0d0101300c0b0440c200003070390b95448040c01401400382c008202c000f11282c2480f050709100031164001079100b401203610328620442855102e010450501e0520050840359402c40d44840e4920381700c00404181c440c00c2d8a01250604600e0b180000c0311140320405c0e981d078905405071000c00741c00201d10a401a01806101c0c07012059030400b03000104018138003190043c0051960074047d07441e002e41039001511800e10f281505030b01202400084c00031501c0e02c1012900108000c00c04c450360a000e540c40c1b15961a00b4015001007280d507121541513401c0300900901c3c60710142e106038496424030051207070340d031620000c4800350380340d03410740c4607240c0da400203090054543d02c502 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 745962059 1250 745960809 745960837
    0x2090307120803010e0c16030c17161703010806010e0c0705030703050301060e03010e0c0409050316030504150201020a08150102150f010f082814100204030b07020607020703030311 79
    0x4a8104100b40e0001c505076003042c08640d0054842c07072501400d500070120500c050514144201011034010120070204031700c0b8402401e20fa103d460241c8410350480c4040b4001003002441e100f0401a0422070036100409010000341158501440d06960b40d5040c030031002058109008107203100c0b140c50440e40302c03580150031640d82d81074074540103026500911420000815140310b25646190601074044035442c500300510915003c0000c20004203280c0d542110340744002c00c070080780c3c0164003081401582c0646c99158480f46030408a11501400c050a5003c5900c100130b0f5001464000c04055000281c1d014002c046040d0074005034600f110981c0c41248008482c000c006501100300b060754180c841186050054075590345c1601c1e585c0b400b0099100d0100c0c2102c6202100e2641d01207910440340c007030310340048098150a09141040d1110b400081083d400003402d20a004107800803c1e080310881c4001c240e21300d4504002519070b0064007005003095159424581c1a422490650721800e01c0600 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 745963309 1250 745962059 745962089
    0x10300506240904020418050f1b030d0e0928060e07020607140f1c0f0b0f221803020a030f0903080a08100807090e07120b2d0712110a09060302090307 65
    0x2c88c06030760b54402c48009a541c10032003500b441d41e0a0110354415140b0054a81442c02406a0200000d5200051240011113904000340700d69030b1107440910444050114005907040c1400404a40003000034000800d41d032220052083c69036108650051201e0398010301c0b91100c406039411046441602600b00d044256062190050502d550000000d03514440e000c028901082090280c0b044203064019440855095099501000c4802003000144030b500d001621200d881300c901000c041c07040f81640140d101107000800c2582001d00303180205001c0c03c04e520072900e950380b600c616100d0160303e4010420b200c1c01040b21a941188020302901d00d0805584109440c1c00c95103004150301c1e05504240c2c0b00303031900041c02c1500c0c0402044030700d800503041c0c4007999809280b00405440310000c800d09201e80c07400c400c2c3c1080044142ca0062981d99502000a5032001044007503c1800d180c2540b4000d08211404445400001400c11108541405601c6441000009040040702e50010301c070000412 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 745964559 1250 745963309 745963333
    0x81b01020d021210060212040e090a02040e0a030306121110020a120c0506010f0f031704030c170105090607120c0c052409061030050624090402041805 66
    0x10141c14030411306400e02c4070099a4484040340d80c2c0b1840442c00021140070402801009511010356910480243c202d4185960a41c049030480c1c03002078485030305030012008201095450b004090007001d141c4130800c0e0b44a9142c5aa0441c001c0c0742c881316102e14249034101d01103600900a80f01c00c0c0d60445455600303440a002c0140c00f51841200032500c60040c8400841c14034100091003060710290f05409484605517541d40c2050f922002800400130414400080001e004800c1e03080170300100c002c0740b440d40364480526401d490b030181104440341c10440c1013101595000e62180724132022104081604410b4800c151022120040d010708503001d814110904c1d00301c030405040241a460705210038540d00c1e0000b99072642030603100001140e2800344100580c010080e00c110f4900e0116400d40e050801c0c2071880c0e0f08628441c101114140c004130200a0302106501442c20040c1c001708240d1554102c00d800940c2d09440104002d208960742c070440b140c5460011b0981c50031991000c100d8400302c0600c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 745965809 1250 745964559 745964587
    0x210020d090c03051f090b04080715110d06080607080606030612061f0503061306020a0e1009060912080d020d140f0901060501050a120b060f121909081b01020d02 71
    0x400e498060b00170b4134007080600c05107502c20241d0860300f1540c10782c2151150390ba01d90f03003a4001e10041c1c825510543c85490502210320035400c4445e9034101d640d507140101c21120082d1180c96000c185560003403010000d41507040a40f0907070154080764110750340e60740c42c000540a072a5446070a00b55101c0d10b01003021140b00381c0e1003050089a2030400b244d405036114201643d03803004540104800e210f40078800000303281500900342c02405410400109100003003c10008940102040c00007002c82c1d408000f03a0360041c40b018040c10f034040e1a11007246054503040914442c100c078090303030a0760005010707120355121391001c00718603140c500301d1000f41001e0360921911041a034a803400755181280025466010300200c41403042e05071280c82d995134007600740320000c2429504560b000342e400c00400a030000008000c0181524003d040d03072031402e140c0c00444503482a1040c0074059840c01412001050001068421080000ca01c59001e03100c00c03032846007e40501c4801181003400815111034018079 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 745967059 1250 745965809 745965823
    0x60305010207060e07030507030f030318030203070204111801050c0c041814010203150d03020a120c0b0f010b041701020403060218122b20010605100f0210020d090c0305 74
    0x3d62004d1000c0c00d0410103454036000c1c82c2c4030041c69540b02d580d0400c0013a254040501d0a14002e043c001540c4121000700c40484a81d4841200141c0000401200b14541480760310036000310280082c0c100303280302a202e4140103129421a05011021400b440d4164040190f5032144a02410038041c80c604140100640b0052090031a1060103440e00c4014084051081c1c0c1d10405290300141802e0000d24144100b00081100540c114000c880260b0b0200e26603e40c20007000e0040c1d91182e14403082030400003007440002c4c0c4200d01c1440f81000402c806c03a0481305690030740311108229503103480c50480850080c071990b40020001c5001041a1028142915030740680c00001d07100c1e85800b856070200c150701c400244801c00c0c0c40708140d044025400303900c81c0390440066080e08001d19824410341d1191840d400c1081e182d1300903915560240083e040c89800000007060505050020154014000c1d4507848803159600031031b0f5000c03a00d1080b028654020202584d0084040d08060b030f1641002629000 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 745968309 1250 745967059 745967063
    0x804090f1b031404080c010b0a15090501030b0f12210a030f0b090412020a05030304060605010e01080c0d0f2909010501050c0616032711010f051605030d060305010207 73
    0x61454110810700e03019010304461481c07585440d540b10f50b610b50b18051203401c0785840000320341d03903201224529201d03a0010742c00381401a682c1b003441000c41c20000c007101c1080e00098100343c280081100b03143c0722803016a4820200b00c132000760044011124600e400c00f215480380c001c0209050162a901c03524004000d00c40d9540d4040c441007602854030001d46000a1045410010382070015020402c2c0508941d0742c4800d074815200400e4958541c985960800d550648080e41d179440e00300200c1d80c001504208806080c200240c00e13140c4081500240d000f60300710b50349140d44620160203c86a00d074490b0078500307101e420680700c2080348018200c4201c01400554064000280040f94946c05402076418030320065000f03004d00d0355465601e500c1d44103000070ba103080c1a2652140465103110f485070010480c08500351030040c0c1000c1c01e00780c40c56250b0340d1280f0b06228030401c01c0343c1c80076802022a1145402d400100003204420302c0c11901d14403c010007202100d04d49140481000410b40042942c0c038 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 745969559 1250 745968309 745968341
    0x130e010f0f06080703090501020c030a09230d03050c070b0307030e15010b0a180e040803100905040b0a0917030c0d150b0a0c0c0b0403080c0d0f020c0105070804090f 72
    0x2648607900314818100c40d01034100415a810002010303940301b600008803640c0f0a000150400806800061558200d6905e40022601c000018030040e41c00d0507420030484031344118503c0c518984c01c0440c1140b8605207020f401c00c04009640600650100450402000401c54060f0703685041c2500a0080c0b211507039079402030084c651200700c0c24410031505816250344a50700d52a04c18160401d40c0d1b15403454144114542c0750072000120440d80c49901882213005e4058580d803450a0210b190700c48186400074500340d171608040c000851000e80500d0780c0302c501e01400165030078041c100402401029040c0e40b4200030004204081d038090307003029080b0031030814814401583c2d00c01c1580e81d90141400381580381c00043c4415405148101020300ea0a8014001503c00340d46815004d0300741e40c000d0700309a03042c040014509038000d50402900744281103d02d003e0280301000310009480d003034072916040c1000030125040082c0300c030f18000c0301c0c02401103020800c50340324410b803420080c0a004252000039 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 745970809 1250 745969559 745969589
    0xf0821150f0a0302010207171005180d08041104020c010f0c0224010b03041b030602120411180601032c0a051908030a23040c0f1703031b130e01 63
    0x50030300064070400d80344c2c142c01400c12070703040503919107001281d00c0e0700118902c6480038010144000c0d109490141103060450b1486103407028910745030800d20b1104071704200c40403003000040340ca101c01e4100301c0001102c001d6940e462440300c440c0509107800f11000654505040c160352641c00040d03880f40e00270480b80c1011f080340152a4100c2d8a05c0074414546030752401c00010b8002000200a07120090244948940c4a07171a512010100d03004095640040c58044042c482440755100001c04d1a810444845031b4440c10f444084080381000b41581d030605803a001c8030f00c0c0709a285504c00400d14011080e0990f45681c1c2d40410342d66050024003500d0740c0c00354201d0701c9c41c9091039581010300aa04810954515204c0048400042c040908031a6212400c0b0092404a28000c07540381e016034001c118000c9428144011660101420760102c4c0559a805244051100020007500c0d402240800502000004041c8409091090b0191200c5540c840354001c200042c0382c080f0326050354800d0041c100c00d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 745972059 1250 745970809 745970839
    0x303280b0f1215090a030e0a03151109042405030d0503130c0b0a030b04110c0d2006070512060427020a0e0a091a040f082115 55
    0x1196022801140c010680700e96440003410b000b01d0b02d5034080301c80e00445000100498080f41001c0d02038610610341d07080101008180365201c81c04010511048903c0c11003186550381c0c4031000750001d07074048c481780d0702d8450300e0301411100c03002c1e41d180c1440940148030070800d900725040189460300e19000d80101805010803581070000d000740c1f504a2940300e1610b1520703120074009076040750b01c100b2900d00c012004082500c6d0400d00c05008c40c0202924003007100d24146080000359006030050824010040c00b900280310000180c2c143e244140d801c0411104031110840d03601c0203004812401300d80304070000d0024466001c00101126006040852419250301040006598070f2242400d00802c03c11068103460380b040b202456503510040c140310019594288407089004201c0d81c0d8a03803640d4a440d00c40c1072040c0301c291040c00c144001d10340000d915250b0380c0c45403001c0c0314240190944a01066070107400107100c608000d18190380101e444640381c080341c0d9030351030304100072064040e00205000580d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 745973309 1250 745972059 745972061
    0x50601120305030103170f160b090c1302090604050a0806010302100c020a05090a180c1502011b050a022418150a0c050403140f070b042114030328 64
    0x100d02985681c8503455646941c0381d04c1040100003c50314010704003002a41c000e10305040003003108040c86a05214035036514205104201401002d900c100d4001ea100c1051558070310194904101381c100d001030725108044041206801650415a0000260100400c80280014034a03040320b01c2202d14a1503c0d01c1010100c41d42840c00390001e42140c1c00030710500040c80d00d031003025440841c2110006502a030450b00d0b01d42440c41030f43c00d80b01481101c1051058014208060303451511a000a0149007808040100c14200d124881010444040b4403004054401d100c1c51030805601f182c401071600301c0c0d0703840c031030003545c145d034005242c40d050058002c1f20000811103080000102052501035621a500342014096414030001040801c20002c40012207060201d0501d0040100801c8850b140c800c5480c50010070780c000c1d03510a002032204020f8102040341c8685540c4d4071424607070905019183c0342400c00c1401018100c4d901000c4108054a00700a540e0b0021a83c00501c0300108111000b20300 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 745974559 1250 745973309 745973339
    0x9070302090117060606070807110f04020310030303060803160b04050717030c1605221b090e062d0a03081c060504020a020a0b090a0203121224010305090c09070903050601 75
    0x1c10b100300a104c58404181e5544d001c0cac00008000d861070481c01d01c4400041c04a030300440341d802e600e08a080080c01851392511409000d002d08500951500f0318040409012080f0000d00400c5100343d040001c0030020184046001094031924054103210080c036895101c0e04a00d06c0c003502c0b84100b1491003016150b1030883c0b411504050140844006030070b14030f20219140800420450b91a0342d0400c01104040802402070000c940c8c030100f4440c00c0c0102d070500e00d0009041c59202d40c41c2d03207801d003107450340d9180220100e000000f000c22418050f0030200301049560350000e4030030790010a101d05e108203c1c8540c0440714a112000300407440c1c940007040300f00d0048017031050050740504003c8002400b10041c1c507410442503401c0f501c0f00145580024641200344001022070038001c030702c403082100103503945504451100201404d030024035845245401845003564101a00c440100303540b4032060241c3d90a81030080d0641003140751070400508826110312085034148910400000c042a09050131 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 745975809 1250 745974559 745974563
    0x8031306110901120c0c0c0f06080a05010815040303090503130608060910060e03030403050d090f15080a09020f0d051c090b0714120a0914090610080907030209011706060607 76
    0x5030390807004130340300342c00a042045000e014082942c040101140704c010280000301401d5403a040c82030309104c00144441000780802c0c49441c200401401000004204464a08680084081c8560701c0303040440c060000481c1c0548103001c0090513099550200418a003540c0d001c0e11002c00c00e4031041c0500440030002c40c2c014040c1703035501405200e107a10440b44201c462400504403814580c4984a050031f209820b000000030503182e25081051030b80004400c0001d000103000004403443d10300d030250600900400c142c0c00660f46655610440d9031f03400c000100800d0243c940e4041030103a1819594a4200f116100e0f108e0140031903040079640308010102c2030f00c9000c000710381800101ea94030f0000cae0020303443c490710740e014401e540942491046c0281c091202c3d1a90b0303018200f45054496003020310504032260150801c03504110740e80c1c403829040750003c00c1601c0c00402c59030301c05d030b03003107003028a250402580465182c00014602c15540d50003c80d112286054036401d0311900c0800c0305a10a50b000 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 745977059 1250 745975809 745975817
    0x110309030d0e060d0203090601090513030903080a03111206031b0d020603040804080f2a010f08060f12031c060e0403120605091e06060313060b0d08031306110901 71
    0xc1e8500c442d12030007021000c1400503202c40e04000c90310300103206981003221007401d01c1c0d00c810010000180c1500446400481c040400e150340c4841c1e4500400c600e10b94000500048000a0070350a0140300e980300004103207032444072540300c202080820881e82000e0b54031600c00e01c551621080180d005000c1c4960707480000f09250020401070307003407112903040100b054824100502000814050500000400d012150090000ca0044054403140c80c141c4c0c00f6105080e540000a009050340c02000201c0d0b03114982c01c1207040342e03070362a000600a041c4c03003c44a0300b0100301c46021101c44000805003252040e0031488008110170412814119451841003603a074195003000710f0042030041c43c00340b1850a01c0b0602049258980c1e0104410000540c1c445100c400740740300c269058604001e4003604080c0440301985942000700424080e03518409029001703d0381c811400d0b895039200c03581d00d0b16195215100c40d1f01c9241105810b0b03040b903030809044d6030043c203003c10640070302c1d1b501045503048101611 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 745978309 1250 745977059 745977073
    0x1110316030504020303070c0f0326040506031b0a050d1404020102120304050304081203070201050f25030207060c0314010b040303080408030411031006090b010503040c060305090a2111030903 84
    0x4000c50242c1400707070003640c2602003045250301181d00104101d004d8600024140c1c80c045c5186462085500340c2031501d04001c1c0b01d1421400500900070407241221811103d080d02d13516040c005080410020400c46451140092250251070b00500a03000151100c20200940a2114107600344003108480007030040e04507080d8012050303030b050055601715008408507418180c0324a41e40c1d10b412a0030701c06040c2070202000304a00d030361703090250552109140b000720380c0c1800d001095403d102418034060174081e00b8125031501e1144aa4156220590070403010f0000c192400d0b4043c00403d14107182d403030090031a800104e00c0e20140001c440440780d0651300c14440d0307501c3d85c80c1d519880c0c0010b4001c07100b1652034810355080769030401001036590103116000808a152603024011900f401401c0c41c10301406104004c08140412a9141194070307a040100d0141e54009607141455011714005114048500345441850a0f25620014441c03564803015503074054a5441c1d40d403070049558040e8507511131a = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 745979559 1250 745978309 745978351
    0x80a0e031602040c0507150b0f01020a020906012105130c0e090a06050402270601030b010306030302030910110708160509132d060b090f060604150c0f14011103 70
    0xf90111300c444c3d1302490928184040350f5501114a001c200004000d152110ba00745041c0c0341c4080c08a061000c01d00081c40741c5001540130036244c150040001e03040c0680c0c0f14212901030b0640b8241da044880e840400c01c100c0c44e2800c24840c402c0038014007688c100072200000b081d4120015055809503480500034071403c0540d54520001e1701009001b260804007941c0002d200000c40c203c4002c01106000120110713182c40000102200c00b551403050401d0300308041040440c0e00801260b10302e440655240d840d212241d1019142d01051001c42c40d0a13100b2140001038901000c6080c2c1c5c446800c540c4040d21040c0c0d11010015011030a440c0c02c070f110305015006c2c2000079030003d82c03504411114030b02d003042c3c2e01000140d500310050079141550301d030761904c601074070714a080b4400943c0504100c940200ca4185071010a416010703030701540310403200100025076124040c1c085c1c0f001d016413050a2034151900c83c070386803c11580c94503200950b582800d44003040c2c9071424007528171501d5000c85400a0000303807 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 745980809 1250 745979559 745979561
    0x17070302150c1603080717100b0708070f05030c1605010e041e060b071e0807032303070c11011e21060906080f030a1d0f0d03080a0e03160204 62
    0x107041da80c4000340c104400d603c254204070040700c2082c0251940d060618145201600003040e00306102042940441082492811208000292003960801ca901c4007001c0c50005134a01c42d20201401e9010040b844804000d0001300400c2d0402944054035030440720f80040401b001100e00030b507400305201c10f2030304405091541c0072250703069100040340c0003a80004918001c83c1c3c055007140c00e204d440011018240700803406c0352410b42084490041d81c0c001a5141c1c0c2000c0e0056070402801c00a0343d02d10500705c500d83c0c03202e99004d00000d040007692130402e8203000e807403c560840c08403403140160201102c0d541c01146c40d500c03e5400d40c40c0c014680c410440c07084810780d03100e03a005110b0000011514039030081a104110180603000c10009035142030040007840d1003640700c03035440d480d4030401100c82d40c0c9500805c484000d100e5034661000040600000444130a41904001e411118032075002c0c05140c1d100c403445e0300446030490104080340c4030100d466164401c1c40c44440b542c1b0301c0c581c0b1590040c206 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 745982059 1250 745980809 745980811
    0xd020303093d020901030606090506071415070804060b120c040f060f03060e01152d0801020304030906181d0606160506060f0a180e0309040204030c031707030215 71
    0x5412441034404042280300882c0841041c001c4240c0e80d001c0f41d0b408565801d8031501000e4006803c10801c0e440c50180025094846c0f00c200400107404950311001070102001000300d5050001c00c0040207141041e00100507690807202500c00da41410b2040760300c4d0500141608603814040050000e200f081420f0002804c42d0035060b080141c1e031400c00241900d01d9090b404061840740c3c03c042010b84003100c0807825100d0342c6580d0345240741815400c028020300210403a48540e0280c000c2c00c408103841c0800e0400b0720183e8080d0b0a9035000004100c10980d004000006a034100d458000c6823000d80e10440402e449940210707281440c0c580181081c2410180001c0c0d40030000814080c90b01c54400da0030009503401c050100ca40e61300510521640d450403a0f00761141110603203007500c0a81c90403148072690041e42d120416440c0d55a4554005003d05004449100d034014106540c0c030b03544c902d031440c0e91803928881584c89403215034095140500050441e042e0784d070103500405040140c07128071403900340 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 745983309 1250 745982059 745982113
    0x40b0402010e0301240806060616081c05040218070f0809070b0f0c0f01050610030f0f061514030c0306011404090606033201060c03050904090b07020d02030309 70
    0x3181c441082c55903409004401549502c40b44440e00100082c2c40e00401d6010707904403024540084d010411251101300030340b01042e0f200940d20040c034007d420406110700c101c088801601c81c924001241c003213203940005015a101f070380c95000302000c80c0c2c02c00308400000d441601c001610240c0510300d5030712031900c090300511074030243c990903550340032030014950080224591011021520b00000311080c0800d203041c0740303041c000f0710603481c00300c5c00a808134100c02c0d0582c05140d95441c3c10741e44203030302c4d51003008200f12404003044001d8407423a4840c00384110b14001c00000e51078054102281c5110300c10b41c0d0207030800300009800c40c3c0b15000103442c148651a213400c0d00301414400021024070700c0c01030b04020030490303c00003000881c0034120706035043c40040d4005d800d0020414008581d08408509044540500d0400b418441c24a0220743c2485200603140e409030900f42280d090140034048a400380e117060702110031640c3d000c60241e03100d00086405405a80140f164441030511040490700610 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 745984559 1250 745983309 745983317
    0xb01090b0609030f0a02090a0c0f0f02100f020c0c040209090c030606160f020f0f10110f0a0c0608010e01030c12020d02270604061a13031401050a060914040b040201 72
    0x60b403200100740742c168000007041007940941d00341d400b503041074024903801100d0818188145107002c9800341911101c0b1100da41046103204548140b20720902c000030f0001c83c501c8003405111070342c04541001e5001040c0345d00880c0100345030946030789020f1084804a183c06048118182d0700e121314413105400060880341c100d403080019030307507154030180740000c55403003424403220b02c0509005005e20300c101c0441c800d010320400c0503890f6050341c482030b4404a0343d00520380450011a4844003038145045a001582c00744103003d942400c10440f00d900000f0317030320140d8804001e03a82c2c40802c0c3e00b80003401c1c8000b070700341022107000740401303e00c22190072511400035162840a05481d808240785184c12000010801c10326108100a11654803015400401c12981800254100f8907907160560749a441003201c0c000014181000ca1140c464036001150002d00d0038803001070360403806001e04821110340704540e00c0c005001c82c8902c5270344940464000320003031a200550380c6070741344422898050b1080c1d040c0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 745985809 1250 745984559 745984567
    0x616030e0a03080a0617060406090c05060a090806060102010b1c0305040b0d0c02150903040e1902071208060d150903210b01080c07050c01051605030a03090302190b01090b06 76
    0x1031001080003640c014826542d801d610315140701d10b00100c032815000310850b81e0036608030700c4403070000141068000b5044180060b00941a1829001c148416400b00790003160208031410313205d808c043d08104440a00083d2041940ea0750012402c0312010400359901c11030440d880c948103442c120681c41d0341407290600c03030303e0300b0703201e080561054004180c0c0030b01700c0303480b60090b0207030544c14049003c840c1815803010040c2d003085010151240143d0061980e661400000516042c0f001c008201d503265116608550703842140c00c08804081e00075120901141c8083c0114010b401d200100c40c03c5039420400c3c00c00c0a4010500140103071440a038150b0400081c8800d0b0f900e03640c1c1108640034260700740800052001d880034009880792000501c07045c00700c5014403402c8081100480ea54040d03480910305251780e4801c40412501701040000c014089210104220f0020ba4060384000002806a021500c24006065540300d251160600081c0f600602c5001004802d0583d0031460788032600918a90030 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 745987059 1250 745985809 745985831
    0x3160510050c0c012301120201230306030f030702030304090f2309010c09031e140a0c1d041a0c09030105040c0f08150115030e0619051008061603 64
    0x6494041c0c81504031810300240c9444407079824421040480000300550302c59961503648205c030b100d01407241e50040030128a254007160320850f4080584260340e410902e941191000f0f04a0039002103450364068420144810a422800000c0c2c2d0003450780100210700d407a09000500024290b90307842822580c0e22040d185c0d402c1c4000e00307803e4144000400f0000c610f40303424007a450950b000107031000180b10004a0500200e0031908214111000480205804220341e25024804041241ca140d21070300500c89002c0400240e40c1c0e00c1c00464070035100f1155a8101c11110b114448815103000384000070b03400c0c40700300002010011561250010040a0603e82c0c01c00c0481e0940b0400ca13003c80700154881e8041c4910080a00301a01408445004041d203044110031342c00184010b000e03070038540028440181c01d491080e00070291041003c0c2c1650740c0b0b030404030020004428010116600c003800c0600103109240c81901100c12030b1017400c0140f101da250305000f655100c1d11056208205503c808000075 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 745988309 1250 745987059 745987061
    0xc0c010237021201090516030c0911040b0d06080c04020a020a061113060207180b03030301030f170c0a02151801050c0304030b01061d031207151b0c061a010203160510 73
    0x400060107100225103903c0d685032041c00c00e24506080d800201f81b110382400410101e14040040d00c1026030300040c1c1a1030102654900c3c022944802d000c0324000442500c10407a5400c2030782100ca5a00c1146c10704691703541080164050000d00b200168410780810004c90110342024070b008085100281ca002c00115194205846c0d03504100e0141e0302003001040482c030b20540c13004510b0718066081000313010200010351070388010b200c00350402e0b0700420108107100764550380c1484424245405a501c4c043d0515161301c0f2000d144045e886011200000c4002c2c1c0c14030421124541c0c180902200112507590054549402c41c1d458240d07031f44020f00c00480003e05e0100303424060695911340342402d101a110002c103600e040200b141c0280c000d0b102c1116040e0140d0107440fa044c3e481034110407102c50500ca1100100506818029a420140b55aa0f420303a0003800d000c1e001406148184481d0010510240007610182c4082d80140d104001c1c01c0c804050120748082c41c3da03c00c0e001d0718202821040000 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 745989559 1250 745988309 745988329
    0x506030f0c07032721050d18080109030f12060503030d0905030705071202090c12161e08011d040803040308070504030b2508090a02330c0c01023702 65
    0x1e900082c14401844851003170001c0301781c2c42c00c00502104031041956211138179000780410f0701090004552804550a40c662000070281000030001c00c04100a401c00038000c0600f110900003091052074030000300c428a001b10f5095030b2001c2c00841c582a98404034100034240c0c01d40c03e595600092003464001017007441140300801401031081f041d0603e074010484002805810440062001c004043d4486884034036903500c1082c16905440c074920103101510450080075400e070b40d2982009a2007845a0070034001410381e4010030180b41c090034199080d0030030080c20364018144072000d20025001034412210942d100d01107103886820130340e40340c0e5414011481507070701e81440c00790407009403226452101500c80c9140103241440c3c42e400d0908444d81c40b00070555001c0d010f6004c014400100140040941d40404041d1040803003a103030070704a1400319006203091552501038511404c1281d8070000e0907045d5001e04030030b5010b02c00d5100322111f18913003200c004102030390039038120080541e54040007a = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 745990809 1250 745989559 745989617
    0x90903070c060c0c0501030b2709060903070308010311010e1809060f01061d0411040801091103030f0d02030907230f01030c0203070308041b030c0f0506030f0c0703 72
    0x554403034030303203280102500c8469000300040002c1e181c181d2000c00d000090100c11504282000202002ca18003c0b818000c2c0c88040c11003400c2c00000400d40203881500341910030328444058460546894032241d859203e400000380000e50004014404964940015031502005041c031401d0069180b010412400c0402d4150803900300326810060707414014800c1550010b00c2d40126803003503040c8940030301604103c20100402c0d102c40c1c40c030140e1646403a4008070784490b2500344107849581e10700119000e061110000c44071003035081d401d2041c0d41000000d880031803e100003101e040200800101e002504000c2c100358091003224000036484d44803108207101105003c04080c1d1860007103050040200840901c981094a0711030700c0c861065000c416a8825641403404500c243c841c2c0c00d100101d24664a030414918900c1d250000400c00100114011039910b40504215140d54104025050200f11074868001c50b81c40006404605420000e11a1506c80d003006100000d583c16031084001403080340d = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 745992059 1250 745990809 745990813
    0x2030403110117040b0a15090c0212070c0e0702120706061e0b09010f051201080601081b0f06070503190509040e0c06071e1208010e071e08060f0909 65
    0x9000340203001941c040e58060070700b801401501c000c0e805500e840f4000f48003418444151012500c114099000f00d5a0b014804001420454945130700c2d000404c0114a2240544140c1d081e40c40030507000c1c8165803c2d25002448007030709a207005000b10030000c00911000450060b021801c4e15815280003520b801d07809520001205801c0040310340c1894860104820147d40c0b00b0401c00c40060781070105d4100794020b1810803480386502c002520540500c688501e4420141d0001180f0030600180150403604403608035608039000481e0000b401140b0b04640341c2000c0700000181060030510014041079200b03600702e91030700c00d041c4001100d8440e2107400000086002518181c0c5140c1801400d500b510070b82e0140c5450f54034400001c40074070450500400070680340c018485801c036655030030032816420503064044504480401070107103070709000d420300441224001c11145807041c406441c103207a07503501802601044010565200d2001014290702500017054101d440d01c4080718a0f000b8100800 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 745993309 1250 745992059 745992067
    0x40b090108070c150b060c01050a09030e0a030309060c170d0903200c0f0f030304060302090901063209060c16090212010b0306010201181b06050307090e0903090d030203 74
    0x800103104840240c80a02080752a40300d000c042008044580c1000705006000030301c1860007004a00c90b400758260244140d460402044411456030300285280c61182e83d800440300c8001d81008140c0640340406000200e0014060001c940651420f189660041080e00c3c0d90425202d00c400740c51740300d5614000ca5640390f0000208060304240071281c80140700f44501052505246550359a43d400304001c0e11503054442400035075114525a0840d10a0280c00d40b5540c50f107c1c240070740a944000e2600f4001c5107207070300020b055031290f0400e59994604202e4046400c044541c003250381c1003441310741c1100c2801000489041e988080090040e01c094070081c1001c0d2028040404020801d540100c02c4c440c01084000120400344000505407030600c0d40054407078079041c0c0102d005010b40d6189100260304618410148604124a220340f650854481840d4580300c1c10119900d020648081000c501284018001020b03100c10103544150b211040380c0c2130030183c400150820414032416800350704002 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 745994559 1250 745993309 745993327
    0x80d0213090b010f031a04090c03020411040e1b04050105031806010f0504060b040f120c0801020304030e031011032d01030f030f030b1309031206030b2d0f06060f040b 73
    0x414132011309194201040302c420f9603003048544c00202d0311035500c11503903010304004000301e2001d441c000d55005001003241041c081c05807100c0364000d004200c020200030000440a2010341c1440144804130081309003410315010054503150000790016051001d02d03441902c980d0f80c10010540200b10003544c84480c40e141c50148012503d89400800080354100410b1005c0a505a0014115020303400004000102410300407903c451a4200440550000090006240c0c0c08449250700780c00803020750312074486c14290740c01150a981c0c2050480d030414800030b124030b4004c0c500181340c2c8681040c1c0701c40510801d00401403041f0242c0017200c84044040400c818507900c4070300021481d550341010051508858009044000789500524002d92140780d000c00b014418003443c8489040140144400340d26482e18006070f540c11582c24116101c4600b2140c040710714041e0700410000d114003222495140c2740200200d1000c014000c5800c52020060441040701110060005103014405103880340c1d002 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 745995809 1250 745994559 745994567
    0xa0606030f020c0d0c031e020303060f0303090a38220b030a02071104020a0f080702011103240904030302030405060c0712120605100513050616080d0213090b01 70
    0x800c0440300705481070010388000311001803802203100442c00c020303049505038a41128030345100d01802c82c4007000c645403c0c191a400002441c0920030403200c19000c81c00c90b0041c95503900498550071340c030240d107040c2040300c010004c00494003d9410010300c1da2600c01c00c5002c2c0880000000034000d001000200300e040032081500030441407000aa03c2e800d154038000ca008510700015110140b62030b80052400208506a80d0201c241d003005841591170b210380180103860a902d50100300301240d890340010304c0b100c0c41842001181c0c0c0145000c5070454403680e843c21540c80c3d411001004103102e484042c4055038032411098440d034031903500560380b4a043d1034401c1c05d00e00e0140400110081c20300904c80002c1280003420b0b0201c19a1403c02d41050540c4000400303070045500982d040000c0d071903488a0943e0060060100300e513400040f01c000c4d6640c0b01488014458030424005030444060807800242c012001001d0b180040d55001d410441101c1e607031010009180c0c446005c0745c1c0d841e10066125600 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 745997059 1250 745995809 745995821
    0x906060504051c02130e0705041a04051501020a1502040b0f0c101a09092104030302070512120a2d02060a0c1218120809100903050a08130b0a060603 65
    0x105030107550110000c1e404203007461402ca905129441d1070346d84000224004000c05001018001c006209940c1c00ca0041610000d116000d10300660400c00020f4450200a061144000d01a40208921906034490f126001182d24110f00c2e40b035000c10001484600c254007078001c0c10261a08581c0e14040342003250315005000c0c0244505504121070144240310b060341101540030140c2da4105a962016a51418032899600107852a0704102c0e10b540c0324500c0310b015009807803080c0c00300c640c2603440d00d003002008643c2d440381e201941d0100380200b06525064018007103c504d5070a14a110511240183c4001818101e103a82445603480c0b100c02c140707504005150704600c00000402811903215401460040d4580301680c81c3c903202c00040420340388288a58041c680c105294818030807000800800740c01040c2d80c0c20701c0360300c5154001c03840d0000e94807804040c40c1d416107d451814004c8072060703034102d0005140008514404284802150403074404a1190b14401c400040c10340c24410081c0c1100c038 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 745998309 1250 745997059 745997089
    0x120a030501170706020c120f0a050c03070e06060306013009060c05210c07050a110306091203040b060d0203031206090a060e010b0304141516030e100510090606050405 73
    0x48200f100300301d003030740100790a80c11080a0740d50b00f2442c40107030b41d52450102c0300010505c0c01e1145400d2002441400303d820999000100d042d54110341d0396405403030000c04207446080c2d00ac041040401d01c198001c030820440080c42840070200c0300c0f00da070701c0306031026500d505024081d03407030301c0e80d100410659101300345020200703040060a01c60b07102042c010754405a20000185500701000c542d08007195000d81e0110380d44042110201107207440c3ca00d14404001c2c0300c480c068858440070641000001c101e482c901c1400074811400c680e16034690344019107000e861141c0144000e9400e0001d6101400244495200404000e2003410100140030080500500206a452a00e03d0074020a00e40c9810241114081c001c61600c0f40c50310305024808030030071080c420343c0d48030301014042d20351115031502d885513114a0081c141640b0b08141070b0141e8078001298440364100412858110703440d9841240c00c40814884840c5003a01c44c0440002c442558115601040e80406c080280346004100106841 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 745999559 1250 745998309 745998313
    0x126060a060f0c020d0819030f1a031b0406050a090207051e370c031509121b150609150311060318150924060111120a03050117 56
    0x20816000083c07901c8000e0070028401c42d1000d02002c1800008010303544801c809039030000511005240280051868410501d0701c0c50400c2d0380304510b040e00d00e0315050f0403840540540000345590429403900054607002c240e1007590b401002c20203440e480e034a40c0213480c0311180140d0b220041c0c1001898034008443c43c1c2605402c800d4024800503001ca59080c1819240d8500304064a51540148a98000c0d294100c000d02480c40310801b41b218807101481220300640400550021580551003a5041c0c040041d03d0200d1420000344100c6c495411035800d12000601c504141880e650b8a090035240d02c4a101016620388500f84185400b41c03244915120018103001e1761680f40d90349880c50680140314881c85081c3c0440003031030108402580c22190909003064030281850300304c0b030120074140cc0d120002035109002d18103044040a030f0303030401c5041260185080c2942d0700d400446085c0342d5100c21915500800c0342d4081c90300c15000241103650255100030540b503042c000002c41031050301e68084529 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 746000809 1250 745999559 745999577
    0x614010b0d1b0915030f1112010f0b070206090d140706030b060c1e0a060606050715090b04060b01020109050a060b0f06310803071208090c01020316020126060a06 71
    0x80350304201c1c2e19045800700c0b500b44e101a01e0b807a006500821036180b00c0d07402c00741010388100050f00070030000c00250309044080407807662283e811100d03260307d5014030b01004008012040151900780040e020100004080581000140d0b0700d81c280102600a816010380c0030140500c0015018022144560400d0301d15908005684600035503ca001e0343c0b001b40010710001c02d00c01c00d400c052120241003504030b6418000aa910000144140c1c8900800d840501c00c0554454203580c4038001c40c820f07650800d0355a00261501e40b0f6007130061402e51040d40c1903650790392101c00040c1c024030020030164051100010b0b82c0c8203110a00024607420214a03100781020010803242b03203800b0015130080441c1c01c41e4001013101030030280f10031100c07541125020b444003040520410030070008403800b940603661000340e42d4881d00c0100340e449444032411405600705100f03c41140c42014207401140c0c0c01490b11859400702c04190210790040101080c461001c50700c2045113604000443d01d0042c600d13880d2040c81 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 746002059 1250 746000809 746000861
    0x3060b0f0105030f040f0b07110c0d150f0204091d0705100503041103100e012903070501050d060b071208070804120c02011e020c0103060b0c190614010b0d 68
    0x22903c0010105512006540007090034400410285090540c1c0074603c40700d82d00f0218005043c90714240312202c8e140c0b06003042450f490400160342c02d4100e901003103031042030442c41c04442c0506450755040d240641e0a120000b28503c0902414030001c015040340400701000c8015507003804841d0304444e000d14800104652220341c03110440358056009620800925a032000180c1403c000b280030342d014600f08850100c2450041d44800740e0508403840c0500c441a00078031701c51152180003421039040c1c010703400070080d075400f0707900620404855140008115407607101d03a08486c1c01c1410241c0365038211007203502407250020340d45500010b20703040038201d41c585655240e01001014030910b040200042030344045902602410ba4001c008242c003425203075001c04021350352900152a980064100580001d0380d001a60032038000b01d1010340502801208185203483c3d81483c00c008031611a0740c1c1074845900200e010105020b45001002c00750365071030107145034090711510002034403000600001810 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 746003309 1250 746002059 746002067
    0x30b1e03070504150e040f080d0506040b0f0102031903110414032803140d050a05100e010f1401050d021201030b06030105071e18030807031713060207240603060b0f01 73
    0xb040300c11704803050003980d43d82d1034901010f01c0e0f4030030002c081140c0801c84904078100c80d04100e03c1103034142c5081101c2d004072030401141e02e0f2020f010a002d0f03041080b01c2c10800c0c00061404000644504002c565541c4400d0000d403e40d01952081040210340c1c50105241d02d000c4c041581004060415110344042030072490010305680040201400b6840340c44e80f0700f401c001c40a64034142004035041200d481e0a0791f103e006000111031155003c0844440440c403010002811816a00a603811a03001420220341e108103443c5441c4290601500f8000064400b000303000500e0301100488180e51994510b103800c184050300900b02c14842d9060600b0000600e50281c41049600c00690601100070280700c0295680c00159444401050254201005200504008042d06d81c8682e640e0002c0020740c40b045803021344d0070340d50000364030250600807001c144290090110345004611002417841901188040486110803413003045071030794401c00c2840100c3c8141040c0303c8003500d140c882207040c000020 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 746004559 1250 746003309 746003351
    0x60b180402030402010e060304060504050706021f150302030703080a140909070806120a0609142a2e11060112061a030604420c030b1e03070504 63
    0x303010300c0d03000c000502035a100da0003142403080d01a19590340c078103046c10b140000d80021101a590741c0303c0c10000060301c40c40020000070050a084c10f00900703080030389103403024086032404403000f256100008801359a05220b00801180b15144d502d5036500340510261002142d00c00d2001d104206012207103041c0c6510059550098a40c0307842a02a5142400140161848000300c1458030808280504110240e0311481029025040310b428050030300d86280d0341e41c1c503161440ca24003145d9030f001e0a0011111411500134080080681003414401d8200c0440d00c555180d200c8404a000c11900d071031150440001074030482040f000e0002903051020b4a0010800d055005207402d940e42d6082198515107038800802ea0001416500641090304084010384008001a119800183d800030400300d4441d1003240c29040b513541030700c40204414401c0001b0701401034148149170729000f000c0407544e60b54285010b018185800ca0030f40840c49000e00d407810225401c01c6000c0d51420510742c000c0d514082c044 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 746005809 1250 746004559 746004607
    0xb0f0c070809130c052d2512030c0816020c130204030c09091407030b0a0e0a0203010c02101d060406020705120414040e0a03140307170c0706060b 64
    0x2407980d6180c000301107426001c1d000c0c455102140b03020841108145c0c40402480300355a2003200758420710000c40703c5004401030702500035440804001c00348905c01c0e4814030010101030204050302008480e19000c442c0c2c1da50102e0507000aa403500d0001100f0b070848141504090405078422210f211360303801a68560f102c840f01c40c0725042482c1c054003020015012034000c0d40c6d211100c06005541d038000d1030b001c0c21241c101280d1021810060040310349000400c00e0407243c10951481040e10b41103425801440818024003160040e2000140903842c01d01428461034110340c0240b5141d12840d841808075088081c003140010030501c06411900e0b0001a46a00241c01c28070050f503d24841c40c05070301d08032100200400786100410700060a09075071311144144201030b5000e204681f01004829201c100028008022130900da1030715405250090246501401d82d00709101c1e0411700410030b80e84110111000c1100e084005440d40400103d07004010060444030129414600009080c1c0103660302d600e25 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 746007059 1250 746005809 746005823
    0x606081917090d0c092a050d060302030f0604020405060402070c03080a18180c0c020102191106040308190906170405100905010c1106010b0417010b100c0b0f0c07 71
    0x1050010081e0703a04856a0041c01460585552594900100c1418062144590b114a0401210032401d0011048980d1104c03c001000e80840c480c1c03401d403500c0d00220b560800381541c0f080d000c40140c40c10800d40242102000042c2603510b000d01c108020360f0402000d030360003180144841000108046518010b0741d50010509171036445081d0101c030504600c0707034040081c0038014800a00001074026890307900b1f00c11202072000e0020210180d40c1020b00010080c0140d118101001031101e959580601d414841d80c001d04400b15190000380c5140c000c2d4100b81d945503c0010201001410740039400748084490031f20300352040c43c0c2000a030802e14404513664016800c20000703000c00906009c08404c4062820b010004110342d41881402402003194a03000700d0842001703c03020400026100b4100c4601e48001ca01c2c1506061070b00040c01240f02d2400415922920456602da841000c0c00d00202c1d401da9504032001000e04040c02489400f60034034044050070418000586030794001c50f0380352a08016 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 746008309 1250 746007059 746007083
    0x120903010f05041b060302040e0a021803060106050a110d0206010b1b06070908010507020f0c010c0809090a050610031a1215190c05040f120c0b1606060819 68
    0x1190251000500c00381141d85814204010840c0c1c1d5000b9000c250781030307100c1c400b8182d03e42c0b07801c1d4102e100d907000c1c0d8011051440300046040c603e680040000b505074200030302d0025406000b0030324101d02a0403c42c08100003065860090341d1021424030318084410003860754116583c0007a44800060007000058800002c0003c80615011940040700c9c208504440c021f181500c0001c0c403110703403405001031a500780b0001c02c8040344009038001d19003a548026244c907000000041d01e00381e00d88602295458001d000f10031031940c079508421b114110140001c686440c03d0010003048084019500d402d00d8600035011582c0c0c402a1f8040382041c83c00e03510a80510700713144c1c005142805091074103646203032200410160012011074441c2c540014003042c08403001c00d220988450003280115012840d41307010810001e40c03594a010740300c0b07010310020940213454400e03591807030380b00040304800075900c565130f0001c1000070700c0748400400440020f490422500d413984070100d2489107000d4040203141d0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 746009559 1250 746008309 746008327
    0xe1b04200d0209040c0f020d081008120a0224040803043813081c06080607030921050909040809060c010905060c0a0903080309120c030d05010906050312 67
    0x6004103a200101020356110841c44000c08041d500c038071140c41c001c5003040400c0c1440d42c01000790142143c02c54020f440b030303040d400c1401c48400308014020213410560b860001175411082c0600a04115404400da503980c0c500c0002038036060700c280d4031019270340c980b04175102d180108660301900030f58041101c0d40d84e0307200c50070500d0200080c50391040340c408014884c060304d986040c401a200d0503142c04159100c0c2c2e6910340c8211080084078010b08000001c0004030344210584070660b001403d81100010080e0700c0302942882c0800448040e00030a0b580c2c0031800511000c0300034007c41c04a81c0103c0405825a000d00030114016605014000c0118001140400410340156400074502800003034440150303040c21030207403000c2801074070326000302c2c000311b9601e203054012102078004507125030140d9031940d9180304c40f43d0300003000e86041e4040d809400750040e030700320024520300007120b00954680108901c1c0904584c4180e000e50b11240c070340b483c02c1104d81c0300850000700040b46469600d80b19150303c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 746010809 1250 746009559 746009591
    0x602071509260a06230109060f0315060306230f010609090b0406031b0f0e040b040f0609050d0801081b030c0f04060e0405010203010f2111060d0e0c040e1b04 69
    0x1003c0051485040010300e4103072085240300c202e03145840d002c0521312030360f0307072240d00702241c20364040d01100450319001480803803504a0303a640b1091450744000380317240d0750ba242c902c216034140c1c592a42040a60304180342034030f0158a000d03045485140b80300901d51412501400c440214410710010980f40d13050380c2042c2d503456102d80c00541d001070780d4070341d080d00a8805c0c0700410006d014128860b480c62501203000b003e80030240e8425070740f20740007000c941c4030b6407281c642c40400794400300c1d059901d5141c1107001410030310170030501900c40e8440d104d41e035060861903407d001e0070b00c00c0030f00c0304101400c110045030340004040c4d41440c0c054690148124070b110201e005404d00b0b420a0b1041803403141404108901540154100c034884900d100000c0e40b548801e10070b005003034609201e400108904200800c01c40f03451035500e0718006110600d00080f0815003002da48074204040156080050b5175039042c00c5c1401081300c40344264001e0403411384200c100321502045c9003005802a80d81d034442024200328 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 746012059 1250 746010809 746010823
    0x140115050c061005010f020712140a080a020a031e090e072a0611041a0d1b0f0e010c0b0c0c0c0618010f0806060702010e0613060207150926 61
    0x158042e41e03514034011014001450207445007600050040107400c9015101003200d0098543d640034008500310261203c09440319131007581c00b4207004200f800000110603200a01c60b00b43d4680240c980c10441d0304000d01280000e481c02c2e00c041c48107102c80f1030346580c02048981a502e031400001d50a46a04008032014041c60240a00d49540e018608031a010805580ba41203845142d040c4074040b00046405100c0c004c2c0e00c035002c1006440c00c441008050307500090b21030f001e014040001c00140c00d88440080d070b40250f0040020036074001542200303d40c041310800030440c00b0b080607400104940e40341e000740c60000300090840d9101041d4040f07441c0301400301207501c1a00829507500c0340c5400b030300b040c900c80510501501040c1128001d4a8082c060790995110703602c0181007074100a600d800540b0f0044002040c140d010354100f06180c034040b844031032030001d046c290380105541070500741540382d0600885104024022400b030100520a24142c41c2e14400e105192015070301d140080f041858140 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 746013309 1250 746012059 746012077
    0x40f1401020d090c0801060902040e0406020c210711061602040b0a080a0b0a052401080406060302040e0c13022d0c033417160f060b1314011505 63
    0x100700080d5400381304689903d181500c100800070031420b5540c099110072840759110b0442c05588040001e0b01082441c0d01925100da120350550344d255106180559001c0c4100740d440390005e02c003003240d90a01c60882ca481002e9502620360516001c0c03085402c8080c8100e03500024840d5071142d4440c11a0b40300e00e081c1d03000800700101100c40080c954a48102c02100c01c8070340042da645044001001017910640c54144891403c0c00c0079100e00105e8011118000000c0054510342c1e11000b0000040e10b1740d02c2441000035910740544046604e180400c03012044904001e401c0500502117100281107000c603103811054042402e0036000c201000140e554064040c003c000e81c00003041320b000b99500e20392541d103a401182c03840380080300d510320b050030740a00d404c6001d0308140c06402501070500c040402004500c406040c0c00c24021425515420304030703802d440848841d621003001e210607060a8020306040b450301102070042d00c0549015011200c014440e64100d146104090480d5900074006c40340019 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 746014559 1250 746013309 746013311
    0x31b010f050915091203070f0e03120c070509060f062505030a110d09090f06170c040c0c05030715020f0a0e1c05100b010201021306090914040f1401020d 67
    0x32074400c80d401c1c0c0303c0c000d070b4520342d10049503803000550344040070404801c070b201498115411622440d404442c001d00a114a0061007180c5070303401c68550b010010070041c02625464150341d1440781b40a54140f500c103912150207410807400380655903541d9901c06540c81c41c180d0303000c0c0c0c40b081e0303c001120000280c003170000101501082c882d0107200d804001840040307040d8480041b90901c1106903550340c1c40321480100018000a0305105031070041d0416111721002c0b05003c00c05585900f2010b1543c684181d9005103035024035180955410280501d6465210a0524009100d425182c0d0f585901c510702c0010041c03140c0c480440e0029200742d0503290b0045e9019000e03070304c070f241e4860080c14104c007a40905200b484602a403407003c140c1d6500e45810b2036031140103040a045020099006070003542c184a05554090041100403610803d64100070041036941092003458000030104a420042c001c00c0c1d039000c40320400010981101d041142c4a82c000c940300a81d001174074100d4024002d03007185030915 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 746015809 1250 746014559 746014561
    0x40f08090d0f0605010e0c03070f1e1205010e010302150a03180516050301050c07200916030b0a061e0921150c08040f0c0e0c18030c03031b010f05 64
    0x80200c81c420004618403c1c40300b00203e91701e0759004000c903e42121050021301e4204001000c40348640b0070012034901320300b070582c140c00d8005c20044541901c8404c1e440018138485072207240c011503000b075038014071750042c02003019410350300840d000306658030505000b110005455800c0301c0c401e51202c035441982c19005601c2e1405443c040d0744030020b000140c06095400c107404030f07042c6018854140121030101200d840d00b20380b030382e5898542c821120b40b00b206689102e442c0c1c903a510340ca0040c52207521004070340d04042c1204000135044580d620541800b4054900c0306000841d045140040010300d280c6400c1d00c0400382020480c1c03c900550001e180b100b0304101c0302d040001140101a051500c03415402081080150381c040440d17141d510090001a42400800d010922400c95840c0303c601508282d10603e8441808000d1214242d40d50320740031030700085507208a5002200c89c4d01c2441c0407800303828805024000683d480c000c0e804212081c9220341c3d404103c09100f5403150302e01c404402c9041c1311b5 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 746017059 1250 746015809 746015813
    0x280905070c021e130c03020c0105040c032a0902030a020915040602010606050c0607050f0d1415030a03020d0809070f0e041e030804030e01110115081c0503040f08090d 73
    0x58010032071040780a420604003184060045034941030310f10304090403410003481101e09040181100629001c1496400c100c981e0a491080c014144600d000300b40d208610780c5945419540e1045200e016030b0100240103ca0310000003100d00d2070704135040c5903405070301d9841c1c1148038402489003100140d40b1401210b500a04071128030054002c441541c0c0003008450f07900e010643e00c9114104040307490360050800601c9840c0100043d2078001d2148090034245401e83c2074840454000f20344001080301000c1c1004a060820911050010404d401900921480e507038040d503070b0b801040c0b004045c03201110004019440412400d4010084255004003641e0703500c40d440000070042e98240c411240005842c0203080d50000002d090503803640d501e90480d6543c3e14100d40d80182c1c0749030356042181440700384418607003d00079100c00170149545c0800c2d551402070024580190001840343d03c0c0f000c201701c441e6054000341903d5100303400003240c5020101c5450411000d1041c1c15006901c0141100e00100f = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 746018309 1250 746017059 746017067
    0x1170f04030905060405030c15070c08060a0b010e0d030f12021b01060f08071523180102010b030a1707120f030605031c111f09030e040b28090507 64
    0x200881c0261250b0240e0b0b40c4a10611601d4031442c0111038165005410030240d504001901e00510161842e6850806091f0303138640d05440b110350f011010583c003560a004111134540f003818249a001d0902102004083e0b0120b60310a04000000d4140710112000c1142a405020400f5507404146001c6540c0c042d01c0700060443e5880e000002455071801c0703800700e41078042c264180c095808540003422107526000e00b030703582d41121200712010000d44000781e08460464009492400b041e00900c140c640301c184590600147c00000080c1c11a8180a1010f01c20b40780070603840120b80d00840405071100345075003420070350b03c5080300c0240002203034888071400b9a4416040b0b0207201d650366017485065510407c050703540310401103071282c01030740c0e07142e0240701802140ea880c0142c040300107840680c000341d00071440009061464600c050340b0b400d400d404141e4400b1a059105108403010070034468200d012039181c403040620a007074022180d41101d039000710b01086000800d0911001d000514103894014 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 746019559 1250 746018309 746018311
    0xa0501050a091118160e06180f0d02060d0906140f09070906260c090108161d01031b0801050907051201021c11040506120105090c03010b160201170f 65
    0x10300d0100701506039641c1460000400300501c03413200d030000c0e0551a48507896030b1403003046095109110100300350014a40390310700a0580640748150604000c41000180b0400c0c20319545110300c01d018804001c401a1380740c40983e001c050b80d0800001c0c5081b25403814000418049402c8100000c0035000c01040031411051140b148180e0001c1d980310030b030f5413000101510200e0246441c070108018180b4402c442006061031400884011a80e40c0c80d02c2c000418000d035000c1c0c00034100c1d034101c881074901e288030500f0003500424210880311000d075040da80c1c20b1041c0d001070000901d400407021074400c1d940c1d0303030313500c80c03c085c02d0031074001c00490030004a16a0786070391911905d4018400c4209032800103030103100b035545e614039464280c104141100c503810000e1646003161820300400348400b1071640c84100192a078a449004003801e154185010801d0001b0003d000d0300d5000b05c204014005076454209a0794403042006e00029580d90610068039000c0100b0103c82451218808001282c0350152690b = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 746020809 1250 746019559 746019563
    0x10201200304021503150d080d0c090f06090e040f022b030e10231b030c070807060912050a060e0d080601080c09130204170708070501020106060903060e0a0501050a09 73
    0x880b8100c03400d10f410220f0f41c0406c48009010849080714210241040081c20708403901c141500303440c195000951104849a280040d40000c210b07801c2480304105c4c18551001030602400e1582d02107103031403c10844d050009000401111201e82904115101c2800c8048960050b504201418400d100b0321044500030280c1a00010810b186048090401c1e2241c3c0e044050b480e03841e090880040d0300306222101c1808558800032030100804c014a01c00c0f500110060408100070f9641c1d820150503980c40d050960308540d540d5040b21100708412500726514204440c4009114030400c1c0240c01d0040c100707440c001c005002c03281802242c801c904000301e4a010b2a01142d00c610020b902c640d001161150b000b1100c00c80c0003401000104902e00e421036a8040c0c2c190901300140ca802d4541e00c1800302d04d40306c1256000254441482840700f0390083c0140c0015080130302c020444680b03000760090400b07a1620019019035038841000e809801c0074042000c8641e00040240039500782481c1d0407000340901582 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 746022059 1250 746020809 746020819
    0x1507020c01090e07032313150c450e311103010e1509061006110c040603031d03070b12101d010e09010e0a1101020120030402 55
    0x19484550700600a0340291042280310b0380044c0d69040d400c4e07004111240c412a43d0b00d254040c42402d1207000c442040c400c401e041441140d50303441e45080080d40d0f404040c1c142c04541000e440d40c6050b540a0325203aa880f50010004a4032609100111081080c9910f4148886402c9c10407410030080340211000b2500750b2000d4028a40d0380c40c040030030011070000308414031f4130040454000340c81e80c41000303002c0b140100c0c000320b100706640e00002e084a090f8082810950059007003502d1640c1c1120350b040d444561040542124a40034514201400841c0692810702440003184604000c040150700486d24001c0c00c104401612800d024000c0c101141c4a0900c18034400254421800c001c40c9020481c1d15a40d907590900700144050086410300070401840d81c020010002210ba140030a110040312154442c104c441d41086010a65200010f101c4441c507030400059204604002545200107500030011518a0850000403030150562070140010229400241c420703034240c8400450146200302c0f6 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 746023309 1250 746022059 746022073
    0x3050c0f071b05040b0d08213c0c031e090f0d050f16060b03060a0f050a0608030a1107050621060a050d0b040614040305030405011515110c03150702 65
    0x20402c402c2e40c0044803110f802c2a00c2c0001d91001503004000390000608000c00e1201204103550840c0d40d80d003045801444004107040743c24504c3d44180d040276004483d980500c088181d00010014440c00090840c18101c100000051803111004108002c010104500c0c81c0b50390900381d4000da501c0200034034491007405184844030409004004441081301c8a04004d420000b240c0300e200c001881d00c0406840e666260301c00d0a5203039600303100c640d00c905607500740010210410300ca5003044541c020401904a440e0010500000700000169140303035806141c2000f24070542e2032947d0600ea4140d03c015000100454030342680c00601022070070903035011311700162a40d250701c01c010004c8034510446810030003807003020740822411541641e019000c0c1d6804600c24010300078042c81130b0421a016000141d011040c482000000c1c09403521100c0212000d400c4541050703032a1680c00161060352060222b0101062031210080c08481c40c1104010280c41c1e146134104019050000100c5a80d8010301440c4 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 746024559 1250 746023309 746023319
    0x80d0903080c1812240709080102040b091905151e041202011b150e10090b07180b0a0c030915050a0c050a02131a010201021903050c0f071b 61
    0x50564603e0b01030161141204504081403080d00500701c11120b0441c003915a48080f440025583d11000c4000b10200030391500d00020002c060820f6034104500c20f0340108010002020104151035501408030b0705402c40c900d6001e00702c030790040300383e100640041c1180700701401400b0680191011441320310144a00c0c9218100f8030505100b035000e6691442071040e070000143d4407076041d000b48488034524020521841d0384400c40104001d6042400c1d070741c0c81c0c4801009501f03043c0b05000c03454407521070600c03905006a48000101400500410411035443c800c082042d4401442000500c40f651040b03650b100388110041070064212020b0b0f0129088a400050804001c03031740c840040443c0d0b907080c0c00d200320200c04a43c2041006402d58040c4190595007016949100b01c102c103922801d05c000840c3d8110025185030b1015050025040d039106000384039840015107000807a004140c1340005a50307072481c0810b000b40c014015844004d1070003240540802c5110498019402c619a071043e500c02c0c1d0366 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 746025809 1250 746024559 746024581
    0x509070810020408060106081021030306410a0b090405010e010305070510050c060a0e0d020d1205060612070c0b0c19030c090902160209060423070c080d090308 70
    0x44d00c540312051340640c004001107031091030120b03040120111a41d60841d521f0750200900303020209104800901c0041c410101601446000c00500d0050790b000c20340c0c944c0f089000c241d0360032000300c2d10034840c540f80c00d440d001801d08141e45100d20003d004000c52b5894102e440901d030400c80056024900d0903001080c0190a800030504a075408801040c24505010912032100d152800e444144035041c0444030f03542000b8001c442c45003540001c00543c0200080b82c10785042e107060441d42c01d540184074030003d0740b81d0054007113060100702280400c03a5101e01c0040b40683c8904058001c10b54860001c0c401883d9001d680c40b0030b4180203042040854480509840b010320a511034282c100340c10b402c1c40c00381c0c50300036040f1256100d25420f103141010b540d00741d0356069900c046100451102101c0c40c1c3c10440c9000c803079040c2c000d81d056908003c0d0081143c25000055110040484400180720014841c14400e03200b52400f560302960242e212003c048021010b0404d440088010910040000303903000c6031 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 746027059 1250 746025809 746025817
    0xc010e06012112140403170d0c032f071205120603010c0e040509070302090a0609052508101d0106170709210803010b0919060c080d0906050907081002 66
    0x30042d5a07400c4461401510444030f00c0702d5402d04841c081c031000000c1448050101c2d1107050002c240d588d28403510103000304407074a031400340c4140340c079218038070041e117140800b030303840200448460121400d4a41c1e5103003190701070355400130038010840c03040d8108250b02c000500350081114208041544440013014241c0fa01100e0080c0007860000c0703c4805c0d450700380c00280d000b24030700c0265008103071a5008900000f00885103119115110403003000124041e2041075480107c4031103124004c0e0310b405800e41200c12000304d4a003001240e8000c80d0980261000400090494a010301221a0509208002c0340406d200e520f004c9504e040103140c02c45840b89100307201d84566a980d841060401003d002511034040700c00000040e13441180000803c00d05c0254040c2011541d125290603000080205041040d60040369070400c0e070034104002034000c2c03091033859504c81c06071034960f00ca80c9000d80083c1039402010789481d05080c10301060240c040f51103002d445052040e106c0100b9102d0f034506c20703842 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 746028309 1250 746027059 746027063
    0x101509020f0d0504110907110d03050c0318070902040f0302150a14181507021f09290d05040314120402120a021206151813080c010e060121 61
    0x1504210000030055a036000c0760341300c0c0c4074002c120755817400350000c42d50000b0129020300101e005170303000e459901002c1000c0300c9408040e00c2c041c8940c0c90b01c0220440a400050203032410003010820342c1200c4007050107000c0c040d051a0004640b61542c0301c400c0c030f00d510254403081e4024145018038160b030900d51000c5514070140387e1030f001d81884031500b482041d039200140c071880501030281c90709025a1000180101c0c0c010412015413240818010040c0b208001c800c01304910f00c1443c288941150062a1682200c3c8014020300c1713911f8200c0c81032101007801d101d01702251440047c203440d0032100356202c1d03809140070350350319554441a520307980102d110340c9206000101101000500518152503c2068640c00c0b0064501710b4207107a01085d010000082601c1072030308484100200c0c1d04007085034041c800302c120f807042032440c1c80500700d100501001d4820040802d04111020a0240800403501101400f000820070000f107003e00f03d03290350082c014110301071841c1554480307205089080350b007140d0b = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 746029559 1250 746028309 746028337
    0x21c051b100e0906150426010c02010504050d03020a0e2107090c2705190e0a0c0c0f021f020d0206010503011a101205040b040b09070e130303090510150902 68
    0x14813460204180d180008800300211542040089160b5901e207d0110f5030030b0128445c0b242d5501c44400140c00c1d03400407581201168508001c100c0400c00005211145442a0034010380d20000c02d2011101d4000130340200d50099071080320841040c81c050420120b80c041501900ea0b10360319502d0080948140c450141d0000e0440c80c00d01d07407090f516601b4086000380c11144180300c1540c1d40c0109854060384100300c2203103000124200301c0450040651076000c4d4403110200401c0c4840d11000d000c020712820003401011990808604546901040c030107000d003060b100400305041c880e0001d69030038518880300014003c0000014250505014070811800382da04c00000341070180c02807241c0070300101500b5040004204c07120000013498030603507004a000b141104840e2a0904000c901000050045072040c0e000e80400c01051030b110542c180c1228184424405184207400c0c120060190454080d00391300881c0ea20170281c084036407002a55085460138012034a80d03034054002203015907101020380d0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 746030809 1250 746029559 746029561
    0x1305010b03012309040c051005130306020f2a010e0f0a060209060d09082a100f15080115050109082805030d0f0f0902030703021c051b100e09 62
    0x2001c0608456416500110035036001180d24800054807440d003550142e41c220300030001030207e420250010003046403182402d9250a003c8401c000b1404810302c0042c1c0b4640d40803803041040c0c0c00210031a103510204110024100a01c42920160204404014441507291040440314200e0108904400320848409440c0030740700f50703d40102a611109a541d0b0140c000c1010f481c07142c45920030040c8960180c0c4d8a19201c6041520300e9102c0d00600300407041c215050f00c840f40101d0030028414420b4036507980c01240f5480302d0350600014002c034200100c2a041c0c140d81c0030541c20b0f0154082e000d0800c4504154082580c0c030001034415450364003400705250404500c02c401301d01041d200b4683d81c80b0714511030f00c15840380d88410b41150440c541020640c0d8071400302c41980701e101c0c000c1846e0201c03060420090340c8010f07800a0390fa0b12007032000134010032014120001201e03108070041c0680307410405071110060b00c900719042007a6961903c078407550181040044080c852284201d41080240c261242c03 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 746032059 1250 746030809 746030819
    0xf0610030603150b0f09090f0d0305010506180429180906040b04030c02040903080f07020c0d20030a0b09250b030a09080a0e01020f1903050706060b04141305010b0301 73
    0x107080003401c04c0d6000b2890610346081c5484600da910700c901c0510f805844d03400583c0c40190b0822040d2083c40041506000040c0400d40d1104210345030007002400c8400c86d545a10f0204d4003414003448a46006034100c8120030445000341d40140900300d045074511003803448000e040980c072a041c1c441c5640d5600540002c0c001541d00500190040c2c0242002416201954005806e84858050490000e40032105002a000034452103a820101c07500152428594120100d28600d9a80d00f000e0400d500c9401d02034100c0b4500700c02480c1021000d420f60300449003e00b0400c450f18800d0302c0f4000e59103d40d150f60114020b40450820107100c1103901c00307103e1850284010041e030005040c01400c0da540d00300c8040040d03403250043c034207414203844101500c9850000681440c49802c194001c44e00314521102100e0b1020100c0500550705041c86030722407000307003864030041a15402003013103020001030218103000b41158018103024200d51180101c0990310301c42e010341d0820700c102201d4600174001801 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 746033309 1250 746032059 746032061
    0x70b0a170f1b0d061802071209030b16050c01020a091a0702031f3804050f0c07080c07030c030c0b090310021b0715180e0109180501050f061003060315 66
    0x29007107400321804038105480300c0c140710b03100800c03040317050040d0380c00202c1c02d0800c070581c0303000d034001c44681c1409405949580c07104d842c6541c00401c1a01d940307a42c1c50301038074007034041c0c0c00b983d840c000350900842d202d8460758400362100400c1c4c002d403202c04c03224890400c0184852801c603001035601802a100c2c10480401b0030140405007148804615169070905c1203100c400624070100300449601089004454a0180c960a84000055015505007020821812004003140350001000b0701c13481da075012a81440c80842c00b03240082c1c000341c0100c020000c14006804441420740340211b510555865644401000034810700c444207415030001c110b5040080040c0d805000890310610340714040314810701606003444013a4101d00c1060300c014940d03030301c41a031020b891418100c06c040d01c505420b0074482240609a01441402c40c581c1e21040d08a0700100e400760000f8415034000002c2c0700320308000450b01c40c048000c0382c02030701134040d401c1c000011f54802c2c000c0000b1660041020311b44409030043c0c0c00 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 746034559 1250 746033309 746033317
    0x106140307030906020705010c0e060a0c0b2502030315010c0b070305100f0f0312030606090b090112111801030b0d020409141f05100303050417070b0a170f1b 69
    0xa418507588209000118201c0e000801c800347c4503900000b91410f2440c0050003d5410503040e43c01807905128414056422072a0040f40c9078100d5002d02d103ea0702c003510748150404550400c03688068010800f80041c0e000000785005000246230b088640c0108801155101a40e01e00139140078520300114030440d010768822500700300ca40c507815008940b40d03071601c4210661503010801200c0e0181e0100280640129980345000403440c09104061170708070001c000c1981806105181c010005614070240c0c0141c7d9205601c0401c280c060107218401c030342046160b0071815a0090350b070f808044040c40f6600ca4461202d0310319000700310b10103558203a000d010042c660342c4022074a5860700039244031804001c2100c190f01180d07100303c20070b424003021140d07815118058a441440c054191042c00041e030030100f0780e010355610001108460641900c3c040c40c0c55032582c08151044000103021080c194060382201d64607070a103441070043c2c1c4803840b0202441e0412540e849411015003184815110114028 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 746035809 1250 746034559 746034571
    0x6010f06080609011e09181b050a0e07020102120a090221030a03020d0b0303070b01050a090212010506300106021b060f0f120123030a030c1101181701050c0301061403 73
    0xc2005d1515170300003800702d4030346420041c2148043c0e010702041021a40ca007251020308409109141441c00000c1006a07009004503003526100340d0000302d4640c401d42c1560141c4901401c60303003040c10454808801403010f10380a9009420142d4480142c06200c585c50000384840300046141000d858400c4000b0b400034850201802d450b91200a0150340c208098600e140c05400300400303135450441000110b0009070f01958a481c01440b0350b205440a03048164112142503c0080d03490000b01c8192001c05090250343c040f0b421000c982c011800c43c001d035882d0680780c942d0215400000c0880c241d0512514407000f040d4410f00401c050040255800302600c0c025800a40503400e04132b05041d4920394040036048040010b2600c40031300100821010194030000d42070340604044803607501c0040c412900030f0400740c00310b46c2da1031400c500c0f0391184092000c038203d0880c0118141d625001103085c45440100150300940c03d01c4045002c0c040e245046904032450380c1c40302c281c1403c1032890000241c00041c52 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 746037059 1250 746035809 746035859
    0xe0d17040503070e091911010c021f030c110114010b07020612010e0405070e1509180118060506030c030d080a060e16030507020601060c080c071706010f0608060901 72
    0x50952010442c0c1c0b00584404d0140b941145410403c80e407030210000d481e1414520844001000310f500104141c990140c28039008840440600100e000701c41645103c00036201c0a00900510796850b920a05c2e00680c159035000100001010301407c0c2c4111000c0340066048800041111205100041807094409410310b41424060344e02059035001c2640f105c0011400380e010403040207800e21001c0c024183c03800311100c99003000303407002070f0751135045104034091741c0800042000c0301c03944070107402001c0c0c3c00b200a00404146a4680380c1004036114201d40c9203081c50041030b85841e01041e00c0c0391402024008100c2c010303864004403180710380500754000e001d968403004a002c2603120368847c843c0d0300d8514510a5104035240c02400c03104001c103544115042040180082a8841c3e040c612650304039400946581e50074400385d00788003040d0300150515001c0641700c18100f00120320740d41217030811582088a995100000d4458000c12965254481808001404412601540094a000780c1c0c11 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 746038309 1250 746037059 746037067
    0xc0201090623040303022a3d0f020f06010e0c09040e030c010603020109210f0f020d0b011806050f060c0106120b0f0702010605062a0f0f0f010b0f060307140f070b070e0d17 75
    0x65142540110000da000c000703214114520100c0d2b0701042115480240c24000740001d41c9408665200c81002a00341c88500e04002420502c685c0c40e03800c80004000c918007601e54894401d0701c1c0d64000c001341d201c200c1c0070600b0a0400102c03840b1828100c01480d07101c02c0080500052581d600a0703600601c40211603d0f84441c0e0720902507141c0340780301000303a84901c941d80500d5051000c0c480900d1910001c050541c0c0c2045420700c030369122074a102c017401c0c8081d6072241d16580b21074001c6024080359044000313034100171801c2c42c5c00e0080c619103d902449003035035003901c0e50700d48400483c04d0780c04901500d034000307104012900741c42d684004002802d034115000d14001c054480d0150303050542190155409a01c60003404400030300c14040e03090f02c60b0550700204070405501c00401e40b4510030340c403083d12035003021002500e545d000704036043c1404a0403950b03a5454501d240105d030b141c1c100510599511071800005a403442c0581103c3d864800c0c0207101c808100d01039903070f0542c500346c0802900007004d4140 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 746039559 1250 746038309 746038399
    0x3031302133602031518030c030304020406050604081b061c0e060105010221071109010f090621022e08060f010c0201090623040303022a 60
    0x11103000c0b464401000810028104a0346941c260100c40c0b00b262a1250400444030050360300240c49601824141c0601030666106410b400701003038842e411200c18040080c007000c40391800f00c000d40c49203101711003c000d10340e00c95092024500603405175010607444643c00801c1c810071800f115000707000040119180c080d014005506d2803460b40800364829844060503d528842070040c80d000d044207200400c1c0c00480780c1c15a041d00e44e484030045207000c00c000303107050601900448811249501030011300d03095950f0400d1b5403900419200e00e0202230b241c131001007030f031400d0441c130210031240c1c1e6844c8412590140d003c11100341c000c40158002c0004501d0040c1a41007541d0100c020f004aa889211891604006002d2465200b0701240d0400910609810050781c028648034281c5106160404a852040c3c103440351145940d00c116141020100d000020140c2c00540001e00503a181c1c0c14a8811074100b10700d01240341600c5506074802003a01d110003850303020451004c583c103804110070315502400 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 746040809 1250 746039559 746039561
    0xb07050903070b211501120b0a08010501030b0709060302121f0801051806010803040b0f03041406010b0304050f010618090516030b040203190503031803130803040618080303130213 79
    0x40003400c0f0281038138641e0750b80e0328103140810503448000b10301c00421700058900003d000140d0034103641c40041d954200e00703e4a07101e2184d80c44c0908080402003099584908011081050460345680000c004180c04074242d03100e40256080c3c000c50408111850b100c0c1c12080c05e2440c20081003912541c4c031202c0c0052041000d001e10f41c05900d15107010241c140c1d03109030b21360030720320141c2059009500c1044100000120581110f00c0628060303542603c0303440380e01c7c19121a0b51183c0507001d092290b44000b00340d6050200c02140076900c1007088030182641c00c0b1001b03090392494810102e946081036070180c0107070307404e400041005201d40180c82842450040c50910701895030015140b40840d80200011420304100100008100880015000840d80d83d111354030701c4001c08403503d030911081c4c08990070038100700392001024400d0030310002548815416640e44c1091180c42c0020300c03081001b5036080d204020701003c0d505444080e6155590344209020140c080d000200d801041c4414070780c50030034407 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 746042059 1250 746040809 746040817
    0x11d070c050a033510080f0d051c02030c03060a1401080105090705040801020f0702040b010219020d150f0515010e010c060203062d090601030e030a0f21050907080a0b07050903070b 79
    0xb80100f4013007410320010708034588280c0e40107100640d0240b149048203940014020328880340030301d400c650700c9010080c01c98410b8541c0e40c161180d0703800481800104038842d0095032040006550320f620241d41c8401d5902c101e06140001c90100300420010300986c1082c64020b03602442d035041103032810340c2d9030100758226481000b140f5183d070400b01e400700440c034150040400d0300c50244020020066008812071583d103180b00000e01c21365400084000f0050054803c803600304e032022040100502c443c40003405083c04480669002c2003010b001c0c90b2642c09280308158000341a59040200701c0d10340c1d580381c02540301402003a8480d421161894840082c49120307100100e1071811400a8141d40c42402207056024041030b05240c00c001d09013640b8000007040d50b086c80c0c0e05182140100d0003100c42552900031101c4400010004000b0005018000745c20007801241d5075821620690341e82d000311764581c510580c0c0240607031402c81c0440d900380e101c0d44c050040820024180c0e05016070759034041d607031030f48 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 746043165 1106 746042059 746042147
    0xa0b030715030902090a0504061407050909060a150906030b030613121403150f0f01051e0c1014060d1502180405011d070c050a03 57
    0x11090300201c03c01074018004140500b410385801c0702410048400b40c031060f0910f01400701c00c0405d81a2584241c0066440d1f9040003e01810000c08502c06040942d00114003100411300c10315052410404107a1900c0f6466410716184010317007905e1024601900c6600b00310108041c01035042138400030203134048a2140410381c4003005840c41155100e400c10090404010458a02d112041c0e04102c14803c032204030070740b03100e803081100e40c07510000504d000410900203110420000c28080d251071000e0641d840c1002c503404030b4546001c1d5680c80c41d019241d21401021541c081c0a041141c0241081e07486128182680d118010110f980203951501258001444900b420060340c40d5018035100500920665940e500030000026861200800d04079050000ca800305018518015549500001402d07030b269507918251152650b07524910400101c00d624090510000b0913461b410b88 = true := by decide +kernel

theorem cover : BRFrame.Cov 745863309 746043165 := by
  have h0 := BRFrame.cov_init 745863309
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745863309 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745863309 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745863309 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745863309 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745863309 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745863309 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745863309 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745863309 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745863309 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745863309 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745863309 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745863309 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745863309 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745863309 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745863309 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745863309 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745863309 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745863309 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745863309 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745863309 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745863309 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745863309 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745863309 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745863309 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745863309 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745863309 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745863309 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745863309 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745863309 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745863309 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745863309 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745863309 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745863309 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745863309 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745863309 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745863309 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745863309 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745863309 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745863309 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745863309 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745863309 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745863309 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745863309 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745863309 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745863309 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745863309 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745863309 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745863309 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745863309 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745863309 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745863309 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745863309 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745863309 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745863309 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745863309 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745863309 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745863309 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745863309 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745863309 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745863309 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745863309 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745863309 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745863309 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745863309 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745863309 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745863309 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745863309 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745863309 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745863309 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745863309 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745863309 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745863309 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745863309 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745863309 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745863309 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745863309 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745863309 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745863309 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745863309 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745863309 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745863309 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745863309 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745863309 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745863309 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745863309 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745863309 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745863309 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745863309 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745863309 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745863309 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745863309 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745863309 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745863309 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745863309 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745863309 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745863309 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745863309 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745863309 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745863309 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745863309 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745863309 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745863309 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745863309 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745863309 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745863309 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745863309 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745863309 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745863309 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745863309 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745863309 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745863309 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745863309 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745863309 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745863309 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745863309 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745863309 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745863309 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745863309 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745863309 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745863309 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745863309 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745863309 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745863309 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745863309 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745863309 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745863309 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745863309 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745863309 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745863309 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745863309 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745863309 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745863309 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745863309 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745863309 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745863309 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745863309 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745863309 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745863309 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745863309 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745863309 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745863309 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745863309 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745863309 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745863309 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 745863309 ≤ n) (h2 : n < 746043165) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
