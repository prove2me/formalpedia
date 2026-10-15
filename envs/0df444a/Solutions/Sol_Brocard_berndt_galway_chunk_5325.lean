-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5325
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:29:57.046094+00:00
-- url     : https://prove2.me/submissions/203ba77b-a01d-4c20-8654-61a8945e91ff

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 957553956 ≤ n < 957733812 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 957555206 1250 957553956 957553979
    0x90405070903120e01020106030507150f050403020d031b150c032405041518051602010b0a0b0a0306240f090e04030e041e1e110d0504080403020a0b090f0109 69
    0x14480810041304401d080c140d001350000c402a40d8814107031aa6680c0350f210110b02d20060300c0241000030380900d2913110050090301168143c0f40c004c1c1400c42c1d005615101504c402507000401d54580030804429008142104107842c4566403104c804580302c0c0800c940141590301a4600044003245540c8107450312690400917022288241d40c04180100d85010035012440382e40d000c803508005501d43c030341c1042c42c1648158495a020001d90401403001c4d10100d08840548900c3c85d0042512041440000c240c41c02504120407a40780204000c0e4039011081c0b01c00802901d250030007004100c1a0040b940c010204441c0385443d4500340c440d40386130001184a442015001805204030407003e5002c1d52915040640c071135130514101c080d03084000913040000c02640a24800700c0045141025100d1040c0c021716062500a1100c40d04204405000c0c1c801031101610465000c1410000040143c85414286008040042801d030302c031014441402010b610f090946410850815000d20044500c0e0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 957556456 1250 957555206 957555233
    0x60e0d050d110f03040302010501031e0305030f060a0b0403260f16050109062d0e0309211c0e1503040803040317180f03090906060703030603021005090405070903 71
    0x50744042100c0354035615281c5a031092030407012070428000708100a06da0150420340c1241c0c13140849213400e148123000328800c98408a40200007a50400108503241c41c01040180c02c0301000307000d085106c9e44c510a400311580158000c480c52040d001d14015454018642400f0808061450a00c0e010050815800ca0f1203003c9040141c800300c1d545900a000c0254040fa00080d0310071303402c1181c0f1101c82c801d0303440706003e0b8590203506409403480007680050b901441903040c42d0390f8000c604081c1402d082001c0c41401c0c202180425911840351105071800300f002e00b00b1104090701103045007070084802458590700c030107001d005020300110004880710010440341d00a80085800d0b45940b0f6a103002c6130031203441152445031210000a0000781810300f001140907401c82411168005615a0b005442e0300400fa880c9034060030715400103145081500023413540310f1081c0350009850f0307200c0c4d0002d900302141080641c0000d0001c6079006480c01c1074454a90004c02070305104400e10301d035681d0a00da59000 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 957557706 1250 957556456 957556477
    0xd09031211120415021305090601110c100e06040e01050108010f05010206041e14071403070e041101020f0d0e0f09040b070e0607060e1b011103040605030c040504090609060e0d05 78
    0x2020000381413102080c100c0b040c0c0303041c10000790355034445500004d983c4070260081c1c2d84036051401c0820040c4d03004401600281c01070b0b2000d031020603290002c1080403000e840c81001442413a20b9074040c2070361040020005000c0c400300841055041000051602c40160081c0c1c040480c006400c2c48540e030002015a4420f42c89241c20090240d1980303c6a08070394800300c01004049030360a410315401001c01e490003528054050980821040420199201401d2044407202d6031201e0220300414048983d40c0f042103c180100e5101407800d00545203070100c420443d40000d01c58003554400c501d4001c1d2101c14118048406a841d0300342a201d03801d507840c010300b00310700f8018140320750103032604d0740030689800e5031300507504004090200100b07d03110041c407030020745c41c111001d0040011358020b0100c9014145c050340250b04080c10302d07000381c5507680040c000c24a0a141403000280540e141d001d41d1500d03a205400100b9855030300e25004055414004214525800103000e100b40554842e040d100d00c60030 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 957558956 1250 957557706 957557737
    0x304061503030801091a030a0507031104020403231e0105160807020309040c03062c0c0c070303031503171207020106150e0f091f0602010c0c0809010e060d09031211 72
    0xc6107006c0203101c00500201035094000c18201006101c000310b400400c4a000e03561180c422500034040104038841c90100801c078100301002c0d2110340304880307802050401d420041707609070303049030042c0c01000304c05480c0d80410360b450710700b0000703008403880207094011403a04000b00c0500701000d0194a0f0301503503a800c0c1c02a5500c0c4940c10810b4030a0700014024100c81d8043c8002d03440b58580703c41e00d01042c040c1079945d000c61002040d81f001442d400c0300c41d034085684c0a45503642c01c60390214081c05500c9454003100c241040e000c404561407100c0a4600d05000e9103e6036135003961008030a4503100204207105591500a040110030f5840150701f044070306078a0312602e0a003d410000b80c840000c1c1541c69004030001c400c200b1951040c2400340c100e008490071800e81690348182c00c909a0700c08075100710000e010400b411001900c000c029000b40c3c24141019015000140046031264000c001400310a41e1600156414107411080c40416045044c1d814040d04064a030800707842d200b07084d2102107081 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 957560206 1250 957558956 957558971
    0x81f0207020d030c2a17070501170c04231207050307140a090e0c0307091a040207020310140a0c1106011707080a0303140619090b0d0501050408030406150303080109 72
    0x40303a00481180c9158602250160500c0e0540d0785c8a02601d0b001d2207402c2c024101c0c4001d080c4100040c86401c90340705a691040510f241c030515105058042c0001802c00130078007000c00c045a001d00d40700602144058168508022101006418601c9807003404182d08405006e200c2a100482c040d401e5410f107812a44400c03c03840c000c0703482100d103640030080d8140f40c1000d807400034001040c45006210101c1c101c030421033300c0b410700d01c08448500340604200703841d40090704501e041540103800700c03500040646481c91440b04500e0295414412941a03041007441048184245403003541c0d0400a5803400302a48001a0703202565508103018040d140564202140e894060410680c00903025000940f004461240b60150107010000482000303240300b000010010304281c1a42540340c8400c0a2002e141807418001c41b00034051541d1058101800301d104c40081007090103a240a184104003d030740d00c0c40d0608200c42250903007404419002d541c12020404203030302402450544d58454800607580 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 957561456 1250 957560206 957560213
    0x6050f030709051f0e0601080c0f03010e101d0f012c0402040e0d0909270f030e1908071d191503031d0a060531081f0207020d030c 57
    0x2100f28500021040c4414100481c41e810400d017010b02135a401c0c1c03a125015207a034014410a401101e00b050300d08141840108810003003900c600d9006140d0b01e10840c03889403142422035480c080705403e0b2100c3c101032003c0c8640740e040b202d15540100021641050300b00f01080304034a041c00321024251800c0d5000001c14155556540940103641d505012a52844044607003d07080c01c0052180c01c1401d45400458088034000301c88411108640d1682044c0840c090740e5100030b2030b118600e0079000c006851311542e40b1030312030049040c9908098040804101c0c42e100006140403a25040040f40280c6141c40042d005c000c10455a0030621a02c1500b642249a82d0351030014541c944040c5420903e49400109143d0840c00e07000c801c406406807100c0d014900000d0082805003071081a0020758200301a00c3c0c40d501d09418140909010720014038107001561480c2c00039491030300445510f800c0243d450f0181412000700c0048881c0444047d401e200e41900003c8074460440406000c0c00440344c0b51388200b = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 957562706 1250 957561456 957561481
    0x121303080d0e011b020f0309010906200f160b070b0c0d020702060d240f060507061e0e070609050612060d050610080d050403120e03030d06060e0406050f03070905 71
    0x2c5072490003009620301d003403140c01680c00b080b0b8204000d0300600d490740e5001ea5002c81103d2840c035040c3c5421003803e2500c2070072501d0040c01c0d10b003243d101058820a00789281c05020918104100c400240080078031030040402d1300840780e1101c214011708005181c0003680d0104441c8d48010a21100343c0c4901c0741c0341d503100292150b400c0080d804080040e00c2c12503840c0c99400000018484071840401024408010b164000140a0719122a1a4035420040e0501c950300421116101d8400410107500c3c80c451103c82412011a405820346c0b5004401010300341005030f4402081d40e032400d840d030381e441d00c800729001e407023072110481d0700c4084d00c0c0019072140c9981143c0012103074001d0448005141c096200241102c45004840c40f50103030b81114038895201e9030070749003503d8001d03034000c00c06484403074103071841c4280a2030741e509800309124042090005128010050541e51100780c900111842000200e642903041188035030070344000c015041d01c0008030b020031754540450006554450f03414080d034 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 957563956 1250 957562706 957562721
    0x1f090201090807230303090102060402092a03010305060c0a0f2d08010305060108070303020c040209030111070c091413060905101505040e014107020d02121303080d 72
    0x1e07100721680003134110315600301c9010100180e04050306040070700080585a120307803151300d4010703880500410054500b00610035000008601d151498500111903d00384101084240784004404401041071040c10700020782d208171039440702d5140c0311482001400303507c0b039000081b040006140c0c2c540300456a042141c41c1c0070b080b4540314840b80501040080c0005002d000c220b2b070780d000c1d46000080031a0b0014005080d2507042d005090404201ea09100094203e2019254590340f6414100d4031102d10100400415000c5c005c901d0304642021f05407001c5d50510301c1c17510000d060120400825a042c50440661254003d20101d41c025540c10007901c0c1030250b1502d04031803854000c0a20146030304424900880300300303940600181645200641c00c81c0c4140f1142c40b0082c3c0703d0454000404d0700c0c8035030b203443d074100050011880c0300b8082c61103180a408a80c0c0c440980d00115844039014bc04100034103088a420000034903000910000624292551200620319440419000c0400b100c87e041b410 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 957565206 1250 957563956 957563969
    0xa061a0c07261002090604030807050102040e0112030f020c0d0303050709090609021c05070c0807260d0b0a0f06031808121e16050306031f1b021f09020109 68
    0x19a042c00740d410035030456a40c585041514403d10004019032403d900903038902e041c00802070340c20b05185494654140e4400b5004540e00e540c2048042400c0b400000e100d0b01034101001c4940f240c601034640940480b2030000b90b4010f641c4091012402c60362003c220512550741842d010034540c0720110155034400503034110100c03860504501145c1c4000503130180c038800481685010b0545c000c82e54031400c40c0c5c425181e40002400111606020580d03060040440034415100c030181004100c3e403846000c90b03911507880c100e100005000903960080d001d0605242800c0342c0c0c00540030b02e00715101c0030303002c2c00d44952010b00d5195001e015064644c00c1e15014101c7e049803801c0da540d804c001300812806000c595007080c40228200c1000888810361455114010515828505400555041c4c0d0030350070003400c0302e41c540300d0b0b032482c074100180005458100d40c004002c04180000d4a131020142450041c000b0f90855004400809403600d14030000001e251200b040041c0400c031600049818110603007101 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 957566456 1250 957565206 957565229
    0x140117130f060e121c0b0a0306090f0803280b18180a0f03090602120913022101031511090d0503070b07050408011802010806210d020c04050a061a0c07 66
    0x62042456060040060701640c4140c00c075407174070207607510007180c414405054004411920604c00035507070f507008496140c01030380c1c00c0b03030580310303d590b00102a8030440744c0319201b6045507480300c240140c3d5000483c10441c100414030040d8803002c0412a004001c404010307212108001003440603d084150305496003124041d01e540c40003074181400c0c14036014104170005149100000703580c81c8040f40d0b0036199000101c003189442902410000001001c00d40400001e0782000302e0004580030070f0031072001a14042d000001980741d030800140c0c05d684910404640750825040b8842207a01400703e81c08504202c503d0035035001c035810424a540500300005041049000c20711810580001c0504101c072031000084c0001c0c2c0207159402620000e825000f80452514801304040d07140608440c0c4070000d4251454291200440304c0f14507202031060200050781080f030700d8110b9414a03004440d8000c10340c41050050b9441c0032400c06005001e004000480c600201d0a8071300c840d17040c40210024051070304031 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 957567706 1250 957566456 957566473
    0x121f050607061b0315030f0c0f15081501050d02030c040b0720060a090b09030a052a0a08060f070e0a0e091606020613150501140117130f060e 62
    0x80d0006080040d581401c1d8050349860b0300100748203020300c1851031600440f007400140b6503500c003c880228501f003101d005000c07004c0441d02441c1607022500900030f0080340340261210344409421250090559070388503441703000760503042c0d810a04880010480c200c0050341ca0362103032910721f22070003950031410707060f50001021014040141d820040412151050b4800a03500e10100821440342022800104041c040e08000c0c800845018007244c01c400b80955001c0300c000c0c0c1c1c40c00d0500b0800200f422810483c54106146120180745c210410b41068920041c41c03410401e103980d881c1401405601144130110004021510030460000d0802000c4c0c0000d403041c1e110050305114071402c85d40d0485501c81c9420031400301e1440c0505a085942035005050705440f03031801612505420340b4266200322090383c003030054144c1da103c0d05000b80241e45042460000c1100018000400a400000e440660505114051905000d10030340d05900c420380b50880030280c03400d5030280c80d44200d0700c000c0d402402702 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 957568956 1250 957567706 957567713
    0x1205151005091903050d020f0d030207060914010608070e01081b01090b030f0103020439110304031a0603070311010c0c08060702100b0d03021c052a12121f050607 71
    0x2129080c1e91051007942c0181b211500226075401d1030b66811501503101c0201c021007503010f03500410041d80a400c0110700c091807500c5190451541038070f440d00e581c2d9607820070068640144002c6010744210248210513526007001e06035940c10401e41e03124518000141540e01380e01400c510700044c803203080c5064807071810404c465101c2c4024071080e0300036070521521041101d55032045108203c451b1040d131030fa1450301c1d03088010681040d480081031241945041d2080003040001c2c00055110b00c10f00c4801d40021000000141e0000d00f50a0003584684002e0001a10103914044900000e03e0803a41d400e502d4240705c015000250312580e2640548028020701c640e0104400078080071596090000c580302c5010710600b15404d0401900581143c103000c00c0c03a034000b005444c02d0100c146046801c2041c052240c296501c458403500c2104500302d403012101c400140913a400e400100d240301410f1035112070340301c018120300030070500741182d44491407440d0038107421098001e440054205a03c0c0d014924 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 957570206 1250 957568956 957568999
    0x20909090c09010605040e13030e03010f150f050108190f0207050d090b040b2d0c0a03090b040e060918010f090b01050409031e030e0d050a120515100509 67
    0x38002800740d00048004200e44d0f008000310b5084400180201c0a00d940d000404500c000c2d180400b101000441c0d4001a40303640c0034015442052001c1c2000243c45038111046098110207500481c03e01d02d004900300b002c1d0b81c00014480d402510480c041e00301008401915004001d00c3c190411200d1020070701100b40100024044d01034400c689a4009080d201c1c56440c800780120312840c106a41308002008840c0d10316a07200608001d1501501d0501030000c00024458004a80030200d942c040006041890752241c40a401045000c503e030345854240160740710200401440d01c1d01808c00c12002c2118024110806440e00d00d0703200003040300c1c01d010030001d4090b0000c1c04082c1c1d101d1160700000b00c0c0c41e250034402c100805c0c1d407548443c800400c01241d80c002000a954481081c1035646070000d031078101c2404500300c2100382c0e99840c0c3e0307500301d0f0490241c004100c4584020000c2e103454104034101ca000d1200161200007142c0c4c80048001c0803800b01c415224150345c49810090502e00d9001280b02d09 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 957571456 1250 957570206 957570223
    0x12191412040617061f030b040603080a0f08070c0201030b1801030309150e130b1503010807091d0c0105131d011d0c0702150c1524010806120102090909 66
    0x6540e511610a0829076021500030113407040b039400f980d0400030000c070510b0910565403074406810080788080c84c400c002021690103a1003601d2005002880d400001e86c0b0808a029405150801c060141003400d17008100385400301000f41419a1012503103900e54488100d00001c14100000e0003496071070345401040c0c1180c1d40701d000c007002c0c0d00701c0007500107074052444903107001005031a2100280e0030b014800c01070300d0b408c0c000c10b40003904810145070303407500800118042c11044c00100415490101d03c0d000b29021101c1d10f444110451046090b000400b041000c6684000d2034001c2d01d640e0389110f0208410495072040c001010b001c140504403481c01c0c0040c5048800080e5164070b01c0b0325852103a105481c00320b078040704a172001c02540c0c005152000d001300f0400d24415650f07051005a8800a03e0900e444e4038a6079061100010021111100c0c1507000815a00c0041d40004280500001c0c05800028021324818a4250010f244103142581520102807009018445a05011402a4481c0741c0d0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 957572706 1250 957571456 957571469
    0xc031209061e0e012003190209060c0f0c0d1a09031620181605090607060f05090d051e0904060b07150b100c03021c0e040b1219141204 59
    0xe280c2d901c412031740c6030380f05811107204031004079245545160f100c2229505c40c0c1d40c003e41c099421300001c0ca454440e44040c0412021810040c6428820051100d14007441010305d50b205040641c84140003442c02c0c2c075510b100c54a115100610303a201d002200741035001d406100446034081c3c0800400b4080e401c40d20420281116a202c00200070602c1072004c03610030055034251445400d000314881c00381c0360181c104c0c8014103103405810b0008803030000d02503a001030000c1d134025488800c0303402041000e2003890340101510000f4040103000900203425401010426068030b0a249240c200461f80d2100304c44000030300402c00c000399502c800410106800481c001c0e214a083c141d5840b4a20704030703114441a540c00185003150680c0c10481c216200795064004600314001d04440010901250b1041d5151201c1a150540040900801e1204032803602e40141e100710201c130904c10401c0800304520384218000200c0c2420300b4810708144044e880111700c0901035210f81080440c031009000b001d00240c0b03c0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 957573956 1250 957572706 957572711
    0x10f05010b0a050901210c081906080705010516020303160b070903020f10110601060305060f010c0b06011b2108010509041104020a0e1302040311010c031209061e0e01 73
    0x200c41c0408101c50040300409000705000304143d04503980240ca101400301070103640c10212008541c5c000040d40c82c50380e0a1408241181e0504c05004201c00e40740004001c44402007004929141c0840c0e0303907a0591003102d041c0040042c4074204160303036052a0560680140440e030b82e4001c8096080115031019005030b903403002070305c0401c1d0f00a01c02c1c000c1104036600142403810902000c0200680c0103802501a41400070000000809040900100d8024203454400003010728000003441301e2604c00d00c151904008440020341d0000742e0365424242c011001380303032800003240d442d031b202041e4240150300603086146c0901e10f40c0d0400e0895080c000700d88c65035074582710a030341c0e078500f4441000d200ba14020005481a00c01000d50304082c1d000c1c01d4881070618241c00441103220100300322001001203001d00540004050050020203411012264002e20348140c904a0035100103194600066440d100760384c0f224854002d10450360010180088200e030504c1c64061b101108000404070301001000950 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 957575206 1250 957573956 957573959
    0x180708100605061303121205130213021e0a0c0c03050a0303110f09010c0c050a030c08120f0d0f020d0203070e10050c031c060321110106030201090b0703031d010f0501 73
    0x1410f2096454031144d00c06040c03c06801c503a11000c400c076800490b0410408020580c408200150168501031407003010500f8420105006010390213441842451005004110980030ba01c0c482c009070344540c8825201079115010164200c17400605c3c0040036044a00c0c944011081c0203021887e24030b81c0d0300c2600d0410100303008424035446400b46030700402c160401440820b8542d40030300d905180c112b129003032108032a03880b2000990b02010300d4005035032a50601d03205209204040010f01080440351400c14100402c440202206114002c404001c240c4c850304542100c03000f680544540c0d01400405545078503207810000c2016000440c3d4912481e1000842025075004078221045040310101035440e0820601e482c02002c0c05101a4003d800da0311034001000c500a0b120019030481001d00c01164132000041c024801030b01c61f070180e070741d40e490001c08000507170704514604219026600c00301d031030309114102980140040b03509080d15001c2d1449220100c401035200140080d400d90041000380d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 957576456 1250 957575206 957575209
    0x308030408030f01060f050414010e04180516080601050d08040801050c03041b0308032701060314160819140a05010b1005090a0e2a090414040f060203180708100605 72
    0x6c20140b680540800c20411043c03042c241c49450540d035410060400c094000ea00d10003041c126511066049060450f48182c481048400d0100b400120b062000d03c010050401c001942c85030010710802d0311807215030004004200d0720301d0948004045140c002c00a514140f00d5104541d80308980c02c9500c1c5401701d02581c0070880030308500044c1c3ea00107008030b0459442c4141901c45407250004002e6000c019018040c50314024040c00024500c100481d2081c29054034000d0324000c1c160382580f040404c4c003071041c0300b1180000bd402c1c0c105500c08640311242c50180c1080d54000121014a91403801140644814081d0541142d0f071549401d542d1603040c0050b078041103802d4040c08200c00d6200c0f941f140c081104902c007081f80c0d0b03004162610801c1d02c110030a0510a00845801d00081c00180d0201c3c0983c9145862301c00c0c00713609900d40464068604d450b07a130742890018203c0c0c005003016804804140c46250314000b46082c0e4007520125150552141074460303803501c070708608584c00380c18188003040e00d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 957577706 1250 957576456 957576467
    0x801030c0e102105070f141c0b0c190807090f120f14030a030e01111206040f0b060c0307142e09020d1406160e0909070308030408030f0106 61
    0x14036a82003481c2c102500b441042c0001d4511110b0548403815a070f00c00d038012850074840440149034000c0340e03072129840d100c440c00305d810300c0c044441d1044410500f42c0080603840003031501c0c4990f114910f003140d070752050404200340c0642104a060700065407001030b011a0440e82c031900800f100e4440040c140d6881c00070b14000f180a014107000d6084560b44800021816140e10210398469840d09200c00100c2c0072461450b005010110002a103c210300e1141e45001e2045803076000032901d10314a0300b14000c8020003040c401900440c081c65554000f161002c5090380300307143d8080d0090025a40300ba60756505541e17a001681d060341c000400f40780224244030001506c0901d04000030101078181d4001040d0901c11440c0000640c2894039184214016510b000c942051300b446907290030040c162600340c00e40360420060842d0680211108c10f0341c4100c3c1c1010014401d810102c541d0320142d901c004603242491420f40c0014100341011092104100c490005503210302009000d9186980c0e1320034080700c0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 957578956 1250 957577706 957577711
    0x201050603162c1003060605030606102d030f0506091b0a09092c070b030606090102032808150a170a02101e1e110a05030a0801030c0e 59
    0x30050341e80c208100108110396008084012155510840486000c009070403c0080303550418800c2d0409061041105910900002d420240e0061a41d40b501d98089519000100e04c40700c10b0002413200740799031404140b5140700130103240c01c010700001c00c1c070b26000e005080d00c01e00000609091400240fa5818282c040300e114011240a80580210007012400d403507101e601d461041246800c804940100c1c1400781d2454408415104a66881d0040d40001409a803410100954100041c10405101c002007941d030044821070321290b4401c86c000050703246214107540380c00000c0c4a00e00d05450480c0ca2140304220304001d890340d4200c3ea9400031424660042003005551206038180300344100003828800c0b1290040c84401c071040c103100c1c0e07000903420200c0803a5000c00903030103440521a1001e481219404100941810840081e21484200070140078591840c10080040e400b0b8143d00c004001d03180f10140c1000541c2d944410702c590042056209020a44540100a80014403090001003451 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 957580206 1250 957578956 957578983
    0xc1e030115090b0d1101050703020f070e0103120509011d010509090c030a0c140d0c09030f0b01081902150d062402060105011b320106050301050901020a0f0305060a090f0902010201050603 82
    0x400030645c030005552039007000e10107504610407050a004411410450300c1c0103800d1050840a03150300d1458a01c4101d030780310304d2010030407209200610443e43c06c28049050011514201042030841500484e018066280300650025001c0180803410100200840c00743c005c664042c88500034801081d1940142140041a80001007200d04203140c003a07402030407144114681391001942c6c0b52034008030700380300c2d890507603003402150010002e58904010041c0b20414a012000003806c4980019070591301c103c203010703e408800551082d2443d65680f000380540080010107140c400f11154032103810902c88002800740c4030360700003c2120340c0039070601924103140700541c080007580380e070300c010400554144050f00e00c5942000380006440c108207081101c880500009500d41ca400c040500307454024040c101c00740d104010001c21560300c41425032070802181408a4540c0307400000c1390528165034014502c0c185040d0032003500c00304071f801c0a017646000760f0092185803114420107403a12803403910754 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 957581456 1250 957580206 957580223
    0x207060e01110d0b06070b0c03060a09061805040809151c09110d02011e02030c011406010c0b1021060f050121030309060501060e0a06090303020c1e030115090b0d 71
    0x300103d09a0700003071a00140640582d0406059640d0080400001e03260740441030340210410070641800f00703c00004080041e81800081c1c41d0131007607080500541246c407051510380d0005000d100400c0215505a5405404005121040480c05103560012425201100310580b500c0440011900940e4503280e0812996640c0000c0031040011710080510200d0601140e283d07058540f50f0040f4200b4684d51150300516514a00b0807561800c4500d103ea0300800c0031804400d100182c0d0780503942c210625400b1040c49541d4035502c84154001d0300c6940311103684480c18211a0749403000d004007858140c0b1615003804600702c000d5075031003079030024043d000039402c1e0b0030401001c215100b5640900b842c042d09002400b0f045907100c2c081501c1090300a41702040c181e17002d4944504069841200078101858040f0b0168155a0025161000c00c0c610ba84905036040c50102d45031580d142d4a60340c900300400030414006420010f0480381103520540150510b0624440742904203102101c40300c69004030034 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 957582706 1250 957581456 957581467
    0x90f0d0b090f1b10020c03060403030e0d08130206030618090102040330080a0f09060b010806062d0c010c180602030a050d0213080604060623030d0c240207060e0111 72
    0xd00100a1313103001050118402c0344820105501c041c0306841c080d81c040d0380d0119034000602c100618100c000b03500c00742009000030810a40342c0ba1a505050100d90444080d86e0b40c0c0c0b01c90f0b00140d042c000f2003d1141940344894180000140e0550040080b64032815841e040b0800d03458040542d4503c1c0811031000d21044625a200c1a1240003442da00090f26100042c2c12094003034080106c8026000c1160310640d203d074440b15642e001400c1e02d521950444e410b91404c040301888400c580603880580ca0481c640750003071140340e070b480415140b115403014020001080d800100500c000c1004042d540403400b10900850b071a840070084804002083d21001d1401001c800003e000307500050110100c1d00c2980d2000c2035a220038003106003c0e900403100421003074107010303080074040c001301c84a525004d82c21034520429100460141800f4020f4285850394040608200e48440c1400d441010040d03812500c65410000c0396016000c0300d809000e00300400c94400f11150300f2552242c50a10b207441e0140103 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 957583956 1250 957582706 957582709
    0x10c032d05040c1205030405030705040c0507060e010f0f150b09150c0307050d050304030e040501050d110f041d1905120d090f060207030305060f090c090f0d0b090f1b 73
    0x21164016104003d920200c035950760700b40c8000109000d00b20390316000000c04215900d41008840e0103130508072801c201c09244c61001034801e02c51610001c0c00345441c1c1d8001102c00d034080d40324146001501e02d0601100400f42c1c5100b00a00c0c10103200201c44200c0d00f0042201c40380413099500c6101c000e0801503401840d500c03030340030540109841082911081200d6000601c6c1070010005d580c01d2502d07483d84078140b62502410b010041c416150140d490b00c4010402d65481c0c6480542458000d0795403207010a80ca00441e070702044580701c6030741040c10810507500c0e2040c0c000c124424074104109655048800310102000500c40c400301801340e900000401007140c00120050010206500001480101c240d59406100340c0c401c10959006901051007428503415015040d8401350494240c1c034101c406100040c0d1020000e005100e901002141d030899070b44803d5080340011000a024500301c2240c2e26002c07101103001c950fa044280210210312000d000e00140c082000851900e081850811810 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 957585206 1250 957583956 957583961
    0x1b080c0418020d060203040b011a0f0901020102070b0c03070908061927061a0105072607020a0e220f080d140f040314090d0f020d02030f010c032d 64
    0x26901c020400c00d0741450300503681c24400c00c85540c810720015071240750070308022000c901c0590001d03180c06910483c200380e40b81a070341151004080310007110303107910340320004034024050900c0003030494030030794144038000000c0030103140700d0395142c1d4640d104240c885007040d407603034000d540000c9103142d07200306000d40000c00c1c0c004000e244564500c0ca031103142c0700c00c0390300c14000d00860156900e607515802e540000600054801c800309080c00c003035190136100d07a43c0348580243d5500030346249420090030b00096503440700300c6019903002403084850356100c2e03507850034940c0309a40c1400c1c0300307000030345202641c000c240c1820041500704425003481505911042d03420741c00188c08511142e42e680c0140250601d429409000d85103400c1c03254418a413500d03020301010551100725003500420300502003203995214000c80784a502114008480c1a1480820061502c0a40c000d505004002c0c0303047d0b000d02c05512410610109980601c5001c0d850282c80104007210506050341e403900300c0140140309440e4 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 957586456 1250 957585206 957585221
    0x1804020409080703030606030606081e07030b03070306060e1005030d05030a2a0905091b160503040b030f0a020702060406081302040e0c04061508060111190309031b080c04 75
    0x2520200707400031036a0340c894240c0e01c62030040340801c5e40c1e00010302003150b0505c10b0724050091b5080550580c200300031a405d10031445920044540686000500c110f0303c260081e089410020707003100c2410340c581c68040003600c142c0c0244410840001c0c0001c0034820310b01c0e1030800302c0c0c00c081c0c05001000d2005100304c0359030780300030007498006440b50000c0b004003104a03d0444080030345001c0f84252507501e41d009040340c485070701191050300d0180500890b5100000b007185c0400480120a0b43c03030260b20f040c96003030310816002810a01004c200003c151082c50002d5100b030305403c039080071a648484000e800c80c0140c40000c0d41000042c001441100d000d036032400d401105548541001d60150381c0000e041e18200e2480104c2c0ea0828100e58150b820075004034405004212010940d6203c0042e006003a0200201542d0410424031801201c001003801080110152000d10852403082c41c20041c0c00c904503880112501031114940c0d52007198420b661a05840c3d07890b0252030800841c0040102403d241c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 957587706 1250 957586456 957586459
    0xb0319020d030c0b040f060f0c0509040c020f031b0d0302040612050703090f050304060f0e30070f0315050f01032306160225030f03050c0102070c1a09180402 69
    0x14043c2c0c54080703814941403922481c4500c2da01c003542242d1f0719000d02980c040094065520b4203244000c8003851300542503800880c010348000601c1e10f5242d0701246070007821034402c4440d01001810295083d180002c3d0507100c01d09404a880a010120b412000c0744210b204403400120366441c0900c03003401641020340c002c0080d26010441000c90b44031801c403100b1b000c0b0308030f485c0d03400001c1c100b04c080d0300031856035580340944c240703440250300e1400820448000080900c02c00001d1001441d10703420134441030380603114114115400140c1f07544c01c10384da4907850b003c2603401c1001d00d40b410031504c209001d0715120f09548002c2410716481d655654400103001081510300c1d5551500302412410f082020310312a01d5414041a80c200c04464040e0a207035141a480c079491683d4805240050200041d0004417540f0805403810700c815824221058005d0441c03c440e0355000081e15401e016a07070000c48260348940c01503101811040440103442d00c10141ca040c1c0090b6480740c4124060380000a50358840d00 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 957588956 1250 957587706 957587717
    0xc070f06080f1b04170a110409080313170301030308090c042a03020f0705071d0603030f030c1201240f0207030f02030715050310140d020d020a050a060f030b0319020d03 74
    0x445c0c82c014480b4139600d02c98211503610465101c01442002000181c94000030fa400300b00b500c04c141c4429a6911000b8070241469a810700a882007104040310a00800710424003261030b0350311792a009001007004d8518955074801c0d60700504180c5070038415140702040031104030a082d488801003440112641080109040e0f003440007480301e031081e5008252483c407a5028242440c1070407007005030384111401072107185c50a0001c0240da500e000085600303004421608984940e901816402184903c05108854003084000000d8204810041c118040c81820540156809030403080b508103d450300440300580c40510100085145014040020750001d0700351040746449004140003452020011400104008100030a00b01450301c8800a0465011900b80708298980041c1c01030301c520790040c0c030904e000c402030421550744044c030f0402000064244400035a81e0340d0040c014081680720800442d06244881401303240100b105c5115010b40291442180f41079000e02c081c20f049094110b09204 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 957590206 1250 957588956 957588959
    0xf0d020f03011505010206100501051c09021e040b030c091501032304140a02030703080d15150201060f03320102161103160504050702070b0c070f06080f1b04 69
    0xc40c00c2c0a4144070b26180c143e0302040900c0c042c002031034084014520000b1a060407000d02041e80e00c20125900050a0801c50403054441c944d0321008281c50b20000f5400704490741e4401c520041144c0d4004202c5045604000405240c0b0034103841311541280a070340542640005060842c40301c0c220701481606140000c6c036002440c51084080319101d507400d11881c0131030100000c101061030051103c90303510000d031035580314aa010940c2c0c0e01060000401c3d441d40410504109034559100088a1040b132110b00f4005030b0780d28003071500c9070f00110418019400e000c40841c403114804207410450350b11002035440e501440c4000c3d6441c00c13400720500d40c40131034003101d03490441090000d4044003c102062221000709032030b1982810b200da08400d402600545200801e011321011a88100d400a8901084c1581e451108030704100c4980c00403101da010103e8030141042c0d00041c40e01c151202045501d10042e202d5505031a1500100c46041000c440d03e0000f91030303c0543c5034204074040d101e04481d4280f6 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 957591456 1250 957590206 957590209
    0x80313051506090105010c030206010b07020111010f05180708070e0405011b0509030105150108040f02060405270a0504021507020a0e010e041110020703020418210f08060f0d020f 78
    0x1110424641c440c01a40d90601c0002d1400070490750050801b42803040c02c00155a5019490b0300c0705215074441302102260900c00c4d640600314071621542503034020000365504130381c40c10044c0403d070303060b844c0c00c503000716020500d080c005076440c1030b10044001442030526110348003070b2480c1c004108503655526190801d61500b80360842d46449202da407120354807160220145400c484ac010045010f04014468121103a42c118400e9074000d03070800c400f20051070490010691500c259402076030026088140501c02d015070a80602991840c051191110384452581c90103440090390040d6100c8c440030300c280c4510403031100a141c010310181c81960a076941310691403503070009a100d0601104250200000c0002040e1510681c400407120402d1114113804000d5859a96020003400349075030700c003541d00320390b0720a0440f0f03e10750340300700300092040c40d518080300014130301c51490002c01c03281004c0c00200b6004d105410320544020b4941000592008108059240d1f0064142d800407950701052826 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 957592706 1250 957591456 957591463
    0x2071b03050d030b0925022d0f01060311060c12070303090201080709032103110a09031a0c1e0c15100501050c06010618150305060103050c090d08031305 67
    0x198000c0010b04100300e00e280d000340507600740c442030303900c904084c104021390750100c2a030000c0355001c400c0c6c800f483e50b03a40c1c1c070059207070907108201134841c510680c0300030070380c10070b00010a0484910802070707034079024543c030340f09007a43d1450100925401d140c0004a5050074420042c01c0c1e43c0f80c505046440400c0c0d103940744880e580c0513910a80c0025110481e110035541c106440e9504044203242c2000b80c0791660300c0e4544442d00c540d1607240c403030501248a503d0b4505c60740010506040c210790300b40d5580041140a050186540f00490f0008410a0700300596014081c0d000d12032110000000c2c600601482c0410301c4030060100c000440f03400b40012080003038108241116112680084111810144000e0f5038140d8a91b020a04104007004503005c2d4010100d001411078100b4284007004400900707141c1c4424101d130700b00600c505580845214240e9240c0c00150180c682a00d003042140c40b224003212051282c00d01d81303074002d01b5040905c80050108030080d5401148640c51191881709030b0360f040d08 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 957593956 1250 957592706 957592709
    0x121909050615090f16031409070509011d010911071e020909030f18040e0a0606030605061e2b050307140a151e0f2f070602071b 56
    0x20303680e0061040180d10380d00b040d10b074030070b542d4110703290415481c058005000300707500142080403203c00c60002c445e015019801c0700441e0780706051001030924000d1020341e5542901d228141c4100c17032540000800c11080c08600e4014a0a40c185194507824486550302802e40500c10041c1070104200b2403000c1032162104d4440d0000c0203612031200c04043c0108000c0c058084c1820400c1c0d0420450042a4141c100c01c941c0e5045a007204661058030b02c8000500070805010601034601034000954100209a4031602c152889400c04008036181c0005103e0022405c2c50044140c180b0350346a100b01d4a84054401004d1044001254001d80420400c8a1203110301d9411a110f031b1011a4403020482c41420100c005440b16004107041501c9407540400da158030040c982946580b000c4400200c0c2d8003103400080e81c02c1100040c4801e2100a0380c09001f0421664165404050b0480100f404009102c00103140707108642075a00781025903e402c00203605c450ba00f107600000b800c4c5e0000300c10b2051044030f070 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 957595206 1250 957593956 957593963
    0x11d0a1e150b031b030d081008030708070501060905190504110a06020a17070206030c0c01020d1103090d02060402031b06040f151409030706030e1608010c09050114121909 75
    0xba980c11800240362400000c0c8000c0b4102500c09402801281c0b800a02c00c03200d51900e1038405d00039200c0d10310a0142c3d00007034201a015010008072401448001c1c03000b030409621035402000099030301c491920481e00c040da01401c1400f0024a8038555a41c540c010940280c09108010030310100c54000815200d00341c2c0c0b002002d07801c03082d140f90038014000004a0101280304840b850408160b0000c1c40e1448002c140d040d11940100340b124108a0941c166020f65076484810403000004800d040f040d46c20465080c403540c4114152040150700c00320703459004a9000e030062070780c41381440c9111111452080e40b15040741061100081403880300c46c49070300414000030402d12519200b20000d050032034241d203403482080c1c2000b8500c000c0c0c90025841c0100d80880c900065225a8405c200b810046107501890100c00d00e0359010413180f40640c8051440c403141d450f01c0080999880c0159864404031500a512030801d0004841240044d882c80d58400d0b04007165282c81c03c82014402c0c102c0c0c09189054 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 957596456 1250 957595206 957595211
    0x20108041b14040f050115031104092a0c050d031a0d0c0303020105060613120f0204050f0a0614010e0f030f030a05090108060406210618080705011d0a1e15 68
    0x2009242421312a40b00d000c0d003424801e2040350305020ba4010310f0300ca80e180290070165205484c44888141d2002d46002e400300c520140800208000000c002c8000c610001d6141304031030b9050070010f4001d48044601503404005813940030600c400035401415000d081c1c80302110800d00301d585a40e41c401060700d03010b1141141a60180c01c505000382140c0e4000c0583e4000c480c100b100040b09152020b4000450b08002806503403000070b49402d181c6801c0c1103400075003090400c820310030340e1003a222080d03104d01c61804081042c40c2c0e580380900103084069400f140402d107000141e4002e8104800e1084282c0c8000c1c2c04c49107100d9108450b03a103580d0141c404d40000800100318000d66603444070b156500701b8021601401018141454019401c04640701c4244d0300b0080c401402c02c1105981260150106101e03080340324070514180240103900480044840354030b002e0a46200040303a8420081c44501e8a00402d9402d4090b80c0744c2c0c56990582c50303001090134a0740985400a82d0600c100b60720101c004901 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 957597706 1250 957596456 957596489
    0x3090a0f3c080a0c080d120510050405190b04050606070b041a191103010608010b390105061807110309031b12010c020d030b0604211406070804020108041b 68
    0xc603034040aa60170558084d007004048498060307204401706080b840c034810010b843d0312220b6140e61401406d038400c0360420b040604002480c06413005480d031607039440b181405084042c90030482243c03821100140d105c041404090f01181d201803403642d000e0700c00c072400c0459551940310000ca80d10308681407081400d04003201501d00041340505003024080c0703600c10b411941440009032520205000300320084c0400b080304041c88008428a00b0124508411421061902e14005035200c00d40074225103070390b0a1402240c01c03810180568a00d1010704100b5414688130f00f040cc030b030590254085039101d844248060021030340d05004c2e40014516440541105c0000742081c0481c00160100c10f01480c1d00d480303400d41d0310baa0040307100d11007221f40340340005851990800044260080b60401c1c0108402008002902200d841d160501c40340a101c113002940c40c1003024035610300c1e04803520800100e1700745c00b280055020301d5001e5003151045412000d88031010340e12104d004501e6118001498090380b0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 957598956 1250 957597706 957597713
    0xe0114060f0f0301031a06030604060203040320060a0e0708030f13170a020a090903020601050f12030714010e070b27040203160e1e1003060e0903090a0f3c080a 70
    0x71607886d8510300104d500081c81d28100003600c0d07500040c40500b1068001001038200740c4540d0b6103181c880f01c00c20017481d0340412108001c2e030302c42080312950b42c0146004090b03c02d0790b01c0010540304445034000210b203050b400b4022216142c010715409800c14510500c046510300c81403408038000b2080c4002014105183c1c010002040c2d0f0341d41c00104090314003480000425400300d07450341903e034160781d10b0382c1880e050000704070800503030701c036080e12800003050080070032106115103a01c1180103c001c0c00310111201c145600d4030f80e20701c0f42c1884403108100450140518135a82d1900c0340a550100240c0e2010a002c80d06980c401c03595611410034110504003480c0e004905a1075412043c0e03403500b101c4d2401d214400b180003460042611900a20b107040c100944039400c00c002400b003190078081541007104c21140c0d2608403000d030300d210320b0750101c0200301849040b0314101100d0001c14800c180d4a001c103102084203d1024a07400940315110349a501d009040520780003c000d00f03401440350404906 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 957600206 1250 957598956 957598973
    0xd0527210c011e1b0e090f0601021906020403061505100f0201060302060c210f0405011b051501240905060325051b0304270905150105030d0305010e0114060f0f030103 73
    0xd00070280700c0041c3c60341c17040d078803100c0703020380c0c0280703040c042c2c507091b0300c4080041c0c0c6418040040002402088068201001003a802500031244503002c240059a80102a14001001d0303009054100880058451190744600380d4a0a642030500001480c40d8494010131110b03846031400034219440b210400100c0265241032038400360500340018240a5049404103180c03249114090406c40c610903000301041000540ca03030034592181c112400c684e084007200400e04000d100380c490705810b0208a900310031942c2c070340110141c0c0c1607549807080c0d42410b04108080c2c2014040d03034210740444d040f09900700d01d0b048060040004617144c06807201201a200007080b084988074080c05e8209000401280c10707445120000780c1428100754000010140b003c5005205601c8058068810440380c00311001c03005d9141410380302d003030b403c0e114540c0200304160309071007080c030235180160010b50042003440d203042001851395100620b15850425000381c00340c05c3d034001c4000d503000f2a034000010400c000150 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 957601456 1250 957600206 957600251
    0xd06030b25030b0a06120f050f040b0108030306010818150a020309070b04150f050c03030c1c1815060e1f080610030201050d020d0527210c011e 63
    0x70b14081c84200b4440b03001c52005030f1a0b12401c2c051040621084044030b4642e00a080011483d050411852902805880034a00144c07001c3c0c40c13402c071304400824428000b200301e074070488040e11509802e807960b0029400f803040c81500313061280500048c01d05051601c0c004280203400001d009612800c01e148000c0c105132140d44540640002000304004881410078850707002da00d203040007404000c40031400d0b40c1e144501d4132030340080e0100008116094100b02c0141400311409040d80401400d8400700310111603403042c0210b000c2522034031a100290030143c481075030030640c0700b020583e1946e512600c0d079481d9040e100c5440c4000c13584e40c41041030401401650003045420300616460500c0d0344080004400c0d800041e041110000e11030000c0b08141d012225444000c1c00708210501d890b10002c2342c0300140c100400d5401c182c2c1c0c1024131700c2e07400c0003450481c6e05480c01c521040c20003180940083c035038040d10000c00b05540f80c508904910f034154041001205d48140045031480715105141d0109104 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 957602706 1250 957601456 957601531
    0x70804110d0f060f15080303160503190f020c011d0d08100608090c0d060b0f100203090d020a0807032405270f0610030b06040501030b04080d06030b 65
    0x1880c10340703404a80125510400e031500144005040740c184111a8080c1202c05a98a9424000d80d400510008000300440c42001400005c0381000a004411a0540710a42e1407440000100200356a1070f055507000003d048009100140f03800c03d50a00d89007561045c2c0041d90ba08900c0074049d481040c0c0038400c60f010f41945240c00c0d80c0524040d0711041c80741c07505004a2003003101314000502070510400040020400c010b04a40c1d0100840c03415401419010641c00e005015800d80c521960503c0c8404120205454024504001d0000c051207541c418801d0143e9001c000072900040d105828800d00c0c020b50b0040351400c40d2405412405070300700c28902800c01d0388a00c1c2104110484041113100429010303101c0103040309030070700b00300c29142c00c2030641c007003016001d00c6003800b0750390344401581803c6a1080341c41d60790a551b0b01041100300c420074403000d005020342c4400180012401802009092012903000031a50740b0394982030780c140011180d030b09000f400010300c0e1480c2c104000c1e644820700070 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 957603956 1250 957602706 957602719
    0x10b130f0b0603041e11061206040b032b0e04050c032202010813080c1605011112070206030c0c070308030609090d02070314070b160b130c1413020307080411 69
    0x341940c40038103000b10f070107005d83c0b001000d02916040111820300c41803030800080c00182c4078501c20510301e41c021010f40d10075108a25001d550f00c1c00381404507030b041e80100340c242d105148a0032003540c0e076030f083d00c21400c01b0100401c0304007600840c2c1d00ca1041500400203c413000b51a45004500c1c0c11411440422880e425840c000724400140e0348241d2076640b1503040c40c25489106014900b000e4640030b04601d150080c0503092201c59800351a240090455500360b03190030010794800d00c82c13916000d8224003241200c0d010880317080507050680066030000040054a03140003a030103015030401c006604100c2d880c0100009201b80f600d0030302e800c00e800035420406000c0c06e11103140080e60302e0000344801000340d03440c040e1581c440300c02800740310f000380160300c01d041d81d5a164608045a004966004423060000c000100e9016200c610514040d260700c0174070b000d00c29040c060800b800030000c40409500c40c2d580010301e4008102800034600940084d2644d08045c2441e150840300003c243c8940c90084c01c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 957605206 1250 957603956 957603961
    0x117090f07081b013207080d090b1018020c0304030c0902040905100806040210050d1a0411031614161401050108010b15031f03030f0806010519030e010b130f0b0603 72
    0x144000b0038038480790007030080090303d21003101805c80d86000310b0310f01405024000c6945000b203100c40d081080c4c807910800069503207a50300a102e0300000460300440c0311407050f000d041c40c1d5200341c035401400e40085090440c0d003059038035640c1d800000a5034010720207607900480c0c100f01d20384140c060550040d00720700c829142507007400911580c400005101910071009460781c2d048540c0a4001c40381000401013040c0540030248203400d032850800200303d40120301d08100c04100c080350f40e09030317070240403445644d41c2c035041e1a8134101d880070303550506054840e00400141c500c01d4140c110030001240704016901e2507010281e0504e0860b84141d00c1014241d0404440c4162a60b0741000750540c14600940107071213440c2c0d40c0000510042240c0700c1241304001c04004010b01d40c000c0d14031818a441031703440102664485004465600407500da01944282881c00c690300c05010740c001c0301c0003842101c000030b40d00440000280d4403410452000840a5079000c003007203041402c1c058085025000c5e1020342c83d50 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 957606456 1250 957605206 957605237
    0x1401020a020d0224040f061101090506010501050a02011116050c22090c050907030e070821034506010b0906210703020910020a020117090f07081b01 65
    0x4941e00c900288a030300c4a80104100c1c085004c1d0140198000c4c4445030303181c5403140128440e96201e800b40b2004268444414940c0b05014094080d01a500c100501416482c3c00015940f580190001c10155500c40200c5044006240054003803200704c591b06204012960420508103100141601c0c000c274031a664100c00c80b08511811109540582c00002d41c00c421410042049075450700060b40c4200d02200384400e80b503141d0001e0ba0b0003984941a60102d580d100201c50b51050940700c0c03242001456540d40c40c426014902035984410b5051000e41e00094824180c48806030b007641c00c0c2151211a5008011034000d2840c2034540d480b020000c0c50a54145404dd461500030070100d207100380c80005406225407503c82c8805a0b51250f888910000e0034040d0b0301601941100310803d004030507908049443e00d2002602d0445250181c403036000140344480300411440e002446408a4890402050200281082080d00500c084000307441440000400b9003a121a54600c1c541000b180c2c06100420 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 957607706 1250 957606456 957606469
    0x31e080c0a0c05011103010e160f051b15040302060c2b1509020c0105060f0f10030b0d030302121303050d051512150f1017150c041401020a02 62
    0xc5880281481c1d120003070004111000c12401900800d503509185241e00541c0d10800918181c0d005118020001d680b0f00a070f80201520200600000031151031201c2c0714135014100800d42d295203088440c2541035100c401919040318180d00040b0102658200401d142d41808641e42140c4440011440c00c01c2448070011114507120980c1d001c000c80c0306a00302d46904503889048c1c0100000e2010003440c2d501c0115030000c1d04901c800714429401d100c000340c1186000802d40e0034000001741701000c440d04840c01e2100c11803440341400181035680546403065030f100300c80c043c05180b290f80e0150b0345040990a2960209024003140079204020b40d1000020b40c0200c141c641050303c2000014480c0e840d0700c1c2410244140c03440407504204407100c00a109130001c10700c8510005007000104483c2c44d1022040c152031001c44005d040028401c00034400da0b84038003190307203041c00a0340880c1d92907883c404071409000c03016901c4003076013503000408010511140042000403030003400035250204550b000b00d81e1 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 957608956 1250 957607706 957607711
    0x8160206090c1c12050304060f0b060d0506042a0306150206060d0611040f0806100303091e08160503120c0703030509060c0115080c2e020a0f0b0103031e08 68
    0x208032501e03c0403000d084900240d00064035080758404103041142d50340500240d20a47d4155000d50a2403090303108803480d4000c60b0050f01c8003400f4280303441140c50150b0010100605680e0348151100030780c16030080700c511840945001c44042084400c480c0303c024080b91143e40c010f080105c0e0700b8000180260700484c0c02c070352200c030549140495108510f0407030010151540b40054007500801e0205941c0c0d50030071040180d071518001c481d202c0e21000c13400728142d41240310003000155800341c1404407856513030014141c085201140312081b6284c407601030406400110090103505020340400003441c2c100b26203e034628181040710303c1d10851207400c60f103440c1c25010217824000b001130745080c907883e50310884028101410003007020a60300c00c1c070700010303010302e206030100c5200302215000c032817410a80003910303154603210012044903040c0400c00c01c0b11040c0111700640c0680c03034815021803004000c1c2a00d140c41440d07000001c0d815460068040000c519000100d03001c59142040040e8004202d02e4 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 957610206 1250 957608956 957608959
    0x10621020f01031121010906170c060f0409050406020315011b08090d0b13050c010504050a0311031204180f0506060304240e0303160203090102060c031f0608160206090c 74
    0x213075000301c0541d206400d100d070103107100c0fa0300400020401c0c0390f944019400e0685040c0715091144035569602070440c0301c94221110002d030416591450302d80b0380f6000801706441110310560825030751308450f6046510803242078900d50303000020000046070300b59103100e404100f4201285c44201c0b012550f01002c0102000400d103400c0080d89142503070724054000050356000c00305404910f800f051886440c0d01c5850110717030903c9074161150b407640c0a801601c0036100082c00303003001c1500d9034490145a801410185805008007107410911462840080025280100030001e4140300709400c04212440a142c0051042c609000e10645603031b1a02240c2d00160803a9245070040f4079151000c2c4680d0000c030014240c940b5000340948045008005141f180e0001c0b40c040880c2038403880305036104d11806140c1801138010314005110034801401858010720401e0903030a845500f065080c400404582140c00495104020400c0350303a080340c1850750052040c4054001810082d08055072401c542285a = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 957611456 1250 957610206 957610211
    0x11010c171f0f12030207050405130b0c0c030a0512060d031b141014010e10061b020301020708030603010f0b060409111909030b0906040309060503041104050405010621020f0103 77
    0x100c1c214407061800c20301800365418200d042e141d444100c0e140748815010100d001d4014124000b890340b40910440e071103003a030b600c07081c00d00100b66034130320138180c0303005214034860001070204800114080021348038841351031f00c4441d99507828040ca03d801c1c4200070101440b440384560340b4000a07602500741e030090301034a180c1c5400300c038040c82c01c000c20400d4840503d01c1842445601c0c0d00340781d0b091304900d00594008100d20b840ea602c2c3e0a2080004100702c820101704d03106440100070301445940c4100d120a040c007465011030350603500117801c1e03902104050307820b00300110130312030309240a01c141d5499441e10340c82042003000c440040b42141c011440f8087e4000d5841e103102c440d008400c070032034a4044031000e8100303042c4400d110180c491000b0340005c2d00e1841c0318600040c0983c0d80014042d0140d50151103802d4840d203030480465043c0e02c020403c83d103803140d0800103c41c1e911a4007400c1e008510410012840c64200400d10306545541c0781450070440140302400056110107103451100b41c070a1802 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 957612706 1250 957611456 957611491
    0x110d0c030b0409030806041811060a020a1b0905071b06051005061606050903030c0d1d150f070207030312051b0307110c2b06110a11010c17 61
    0x398000c10389408580d8105041405000c20198841181c1d48038460407501080075806200050304160b41288004000f002d07100c5c400e1607036140c484060200c24130b0901c1100e01c0034500c3d0b03071001c900c440b00c05a0911002c20010052003003050b42c2c05140c1c0d00404514051140704032215025a0618009001030105a60750380422449444e2003407041c05002d000e000c8540e100d000c0062508165a030803801da0b9120700c1c1c10b002c1440d032100401240e02074040c410159003407900d0900038100900010414222004c190340c2520408402840012482090400440000c1c90800c954a90b0360400402800840d0442c1c02c080c400281c21044200d84079850000000e45031340c1d15440e42d00c029000c0b03105110039000c0030081080c0140d01040003076400784c00c082940d02140000080c01400c005400d040e4210102c86062400c600c0b601c90840854a070280c1c1c40032441080d40c0740c00482543c0300e42c4c40c0c1c200085248840f6100320600340110b9002101b2071500b00d050318040d0750300348004e502c06402c505950000e50003 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 957613956 1250 957612706 957612731
    0x330b212104080106080a05010c0903030c1b03060905061f0501051209160b0403110a0308180102150106170f220512131e2303010e071202090a110d 64
    0x103a901402e1860001c000c01500c0705c24150341c80a6042c01103070300d503082810400005101d40064011a40d144c1c803104184900759903960743d5199002d4800c581201481000400b00e1010b008100081d4003c1c0050700440c10404628548142d420125441003420391108100b0359030b10170129034000e1011170700c0311029220242001d0600c09041c004055421802a0110f5507011400080c000c5910038401415261402c0040c02450780c0c080c84040d01d00c1205200e0b49a06c0600500c110b08200f41c148180c8180c2d0b000646415140502078000c0c800003032246030240d901000070300c401034225803607514040292410320891440b440101c8041488c01d080f004014041040811a500c44031000b08030a9445011898060300354616a1256405c008100311480b085001c058941e079084e00c3d2510314110411283c2e444140c2303124072a00c0300d99015035130703680d000e1503400c81030000b10003038080817100d80000300c100e0040014428015048821041c50041e41030714418a4404403100032594410210342400b2120 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 957615206 1250 957613956 957614023
    0x71101080c090625060e1005010f032d060b1008061e1c1b0902090f010315080304080a02030d080928061a03010e011107330b21 56
    0x96241220762003103002040100941041e06e541c00e1540403030700003648032546841515400c0c410606241c00381a01400466420314241140d0305042075040303007078207a005411208041c840003c0d0b070f4481c2d50300000324161402d041e50841105103441c00e9040d03424500006010034541c08050880d0a0360081c1c80081a280da441742d03071094900e401c5094041d1b00e18148030b8442c0d88003c0c00b40155200004001c120310a96100b911101e0802501000c540c00031100150014211161300100301c240210f000294104200010405002500080c21141031b4902c181807401440820340018001d40c14204103c2100000303070007014610446540d80c02407000005541040342d48800904050b0030907406540706004c2900c0300704980070076002000200c000420700f030300300c0e41c0014001c5404101085280c1c041b40c44c0c0320000704001c03200d40186014060042c1c03003800d1904000d04001442d5120b02042105140610005440c0076104400d440b00d0015013803507644400182c46140820118450702d03044605241 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 957616456 1250 957615206 957615247
    0x18030b0c03070915030f18050a0b0c04090c09140603010e0c07030c0b13050c101b05070b04080601060e03010c050a2006070504030b0c090603010510050708030c071101080c0906 77
    0x396042e004d240e6184600801500b0310941c510002e5090258105882e001ea030380c03074522a9040806403a41c06400d50741c00400680140510002e070605000210360503840d440341885000c265116021442d00c0d016a03400203200d03188030203100352414001003125034180f65085e0751001c1080c0441d5074a0303602d886c050311044603408002e45404001410041149000102d1410150151040311040e035010410441806080d00101d00001c948500c002c1f00700c103049400701142442002a02d51840d00c51080607000c0c0c202d0340c41072449600c9000100f04c465044070040841c840141c009002c4c021a1100c082c05904c01c0c2600748040100d04000c812071003600f0b01101d400a52a4800c2c0c540030700300360100a101e80c1040c0400e46020114001090030b40716010b0869015a5028004c2400c5078a071504010150300e0781101071003480010090400081d40391801148540d4800c000c864581c1814200805074a03208404241480200001d1064030b02d6080705417442d204048903483d035211b404038942100300400c03 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 957617706 1250 957616456 957616469
    0xc0f0703210606020c0d0503090d0c0e27010b030a02010c02130e06190b0a150207080601080102030106120b1806030102040e13020f0a06050a0f1704030f18030b0c030709 74
    0x1030035110a100c071540d00400219500780d403c03640080443c000700008010b190800422950041110b0a0306040c244040303000b86000d0404008042c0d40c6411040200b8011554060042c1d406c03030302c518050b088a40300c1084072107160001c001150079107000c65940d01500d040681440081300f150030455581030b030f10304404611700c00103004141580c100c503644e51000341e5807007590b011500700b251002102c900c6548035161000f44102c880b18038000395128080e010a10440c00c42c05004404100b240040058a000349800f00c00141e60350b241c0300d0001c00300c200c03c0d034031049040e00f480248911540c9501c3c5019507d0762503c0c442c406511346400182c02841030b5070001400480c5802044400059a070348111402d000782c0d82c071401c5118020400483d00107a005660204405100140e0350b03e11800306070080054608059141040e03030305d00350501c61821a801c0380080d01a10945945d80d07030050b10b4480c14880d02e4041c0030480e0550f908c03500d01903401400304080007404000104407501c10304404006060 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 957618956 1250 957617706 957617747
    0x70203010207120f030b06030406051b070f020310050c03070e120a03081905090d05030403031418011a03030406050f090a0b0d06080a1104020c010b030f0a0303140c0f0703 75
    0x945151010000f00381c0554403021400c007800c1003080c1c5009001e0300c1015180100024035507520b0381e0300c0c140203000280101d0a0412901504071304514140001d0005c240640704252444042d441014540821712803080301441c10041030100150f00202134a4000916003800650b801e03014000c030301c241c011803420740707014821800f00d1014581c0001c0d00902032002000e00c210034030300840c00c440550764103885c0704080307621a0f01e4846c03111344110055500716101389004503942141d0072841e11003409c15101ca0303409842217500c2c1c4804075000d1242003882a034030403062240d01940800607460307001d148a40414000c0c00515080c0d0a00042e0449509240080034038464607260b011040158102c005840d140c3c9107403400104800c140040c2040d08140d1082041e8890081e200c1888065040300100c2280c66481e980b50030305030750302131006021400364840181204d60721418000d090303404148880c1400f1900e2018440c010480d0030846101685000155554050500d0b007110b0f40c40d1920f6444400c1031 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 957620206 1250 957618956 957618967
    0x30b0d080d0c080901060501090302091306050103030f0e191404090b0f040516050f122a19080303070c0317010305070f08150103061109040e010606080c0a080f06060702030102 77
    0x1d500003038100c2c4840e940c425040e52001041802c0740e441e400342d40d020a0f041c500410040c90b00c4c22604d0761104606042040d6a62660382e07102c213440080c0c004401054030040d0411036264004a1101101022550b0b07001702e41c9007011307000e008880390180012840d41c074800104d4548658010702c81180d485009080301d8900141c0b880e00e03c6030251000c99060241008903001d1103030345240f030016121300504018101000c03004004a000d020900c43c492030058800008884501610707800fa6815100502c062101100c0100080407100b44c030000c1441c92030750740a20029000000b52030b0b00800900701081c0d210780c5800d0175699503000050746244842c0d8200040100035001c2507040c00c440d862081802d4103625540180e4861040c8400c42d42003410100c010000314046812484c000e2606c03911151070701e203c00010034140c4507904048020350303450b85010001c0700c1d44440c0c615440040c02041d6400d00c60902401021800046c0c5844040700012002c9000c80d0f40b2041142c0030f45500800031940c45 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 957621456 1250 957620206 957620227
    0xf15090804030f05060f0705091c080a080f0a0e030403060e0a0203120910030b060304030c02040b0a06030b243430090618030f05070f1208040501030b0d08 68
    0x3056001c0f044850b401144e001c42c4030000140314082c003c203629103600c4d080c010f0700003d2240c25655a605485c54040c0c0548850121385603900a01d013018103691131600c02d20303001c4010000410040c1520600f945444074004034214080300703032800d990f0f0146000c280305c040ca44403d840c00e910344c800030f50305004805c1c1d12008460350500400c98100140c1b82c420003402c41403c25000c807000e44006941141e82000001d0000348191200c200c0d1910003000000c86880c40c01c04034021602c1d54101d007005c2070b0b4441c00301c0114034205c800da600c13068403500004d4000e80c1c03030042c4901600030720541c40040b03524444c52054017081003458480d08544900c4180c654025400c00c403620f000140d03841e0407030f500201400003d000714042c1d0840c50b12480d803030b103820482c0342c07903800c03600c1e86400c0740014204440c02601000203100c44601071425401100188403141c1041c1507613015403131070b40c4a9002000da2400341c2c0009000c02060300e045850034200001c881c1c240f100403c10003090b860004020b08800981c4d040302 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 957622706 1250 957621456 957621473
    0x30a0c0f12020f12090a1203090b1803010b12150406090204020a2001050702190507260609010209090115030b030d2003040b0403060519020406051806070f1509080403 73
    0x840f40340030101d40d02100c468420b880c241c461000126008200d4480500000d04041014900c0390300c1380c5428013406980b166207240c1d507005650078504012045d01c1c646003500d4240541091040c0486000b407030340b803c5a00c801c0e620040c0c503007405604500000010280000d96000f6011540c01a00035940c400c0700b010002e041050a5188c120710b040400d100b6000310005114181c890a200d80080c075003140c5c881285a16562104400c940070b00c02c880000c0384940c6c2024804110103c801c242503108488500c10354245180104904581c4c0e2041c0665a103d66031214520304490108131040c1c0c44070710101046010b016050320458152140184e00301400d03a1200799407d0480313034030080c102409001c55295072030744a94801c005189005020174000310b03650b40c0c015038011040d03d020303958580034800c0c1d010a80c0c00a034000400b06074046024640f0036000000320498020446810345020300c156160b00d40130700d0ba10000b44c80c40718a041c0103070746c14040da031000940680059285803501d036646002e03510f = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 957623956 1250 957622706 957622723
    0x105011b1703040605011e051e040e33160e180a06050a0e04150e060108060109060510201011030a06060c0201120e0a170904061403030a0c0f1202 64
    0x40003403406000040b07a884008004004031502e0307034003840300c518004c02c01427038810341000101c4002c0c00c1c000e070401c02d9035503103c1d0310703003903900a4042d010001050129210140c4100d1070706850030025442010703c803074a0514075501c018581c00c1240c8401c409041224200c40a0004035000a145000a0201d003a683d0070b0030b116080d540313010b0041d5038890b018030004c4503a51154a02c29031503080410001850b0000c065082d10444800099000d0308003070091910f102a03101d502c0f6030b00940018003c0c5031050142c60064581503480600300c1d038a800d0300030018495902e5a4040412421a17009815401e1000c000c15842466042c094003404000d0400e0642c400e6030480034007480c108001030301a015001e20f039031003501612040c003074002e141d140c88090456030036000301c18020003962030005601080c1010b00110444807403900c3d9001c0300140421102c0581000607610030401c2001004c1d6000001c6921200b928034101c40c0740c2c2c1c8203140202c0e80c66000000140035141d5265001d0025900042444 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 957625206 1250 957623956 957623963
    0x41502040803090f0616020103270f050105090c0d0303050406060f090b0a120803060913170a020c01020a0804060e030a0c0617071e0503090f0601060305090c01170105011b170304 78
    0x102901c0c4044c01c0041c01d1080032484144030b022205844013643c0aa446076034640c0b0012212040b00202992110600005540843e03003008000052424442e00344a603592081200000705154180180000c402040d460002003c040d11000058200b0400350080d00003070580120807894151145034a501134074494421a00809850380c0c00103c5180f5441e09010040d0030228480c074640381d02d4103205543d14010301984200301135005200c006100b42c2500c031040c002d43d06996440b6510001d000341040c202100041c110b5004003544170100d401030044608851a50414180036042d10000c039041c00100c0001500b01800c0703190029032039401000d500ea0b00301240406040755907604800340c8041d4074000c104072000f484803108020a42c02840210382002040040790340c001d248540c12803410342c0907003201780026168414009442c004022841e00a031090803e003600154491207494480014411309040151103058013400f070340f9007000544140d1300040c0c41d12000d0034800f032a1160f81d00681e0200c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 957626456 1250 957625206 957625219
    0x909060601111911010c05060a0609060602010504020f040527030703030524010302030408092805040c1d01050c0d09081b010c0201120615032702031504150204080309 73
    0xc201145010824081164600c8002e10035903c0c0c031307152000c41c0f80e401442c850500001d115030201140c001c01c00c8520506408202003074071810402e0103400e0b0b4440d58021015607040c88184030069603600c1c0f0304155a0010303140001e0f180c0c2c560b021744001c1c1c09086001344c20b40c0d0101040000406001c0b0040c10390b58081d445c05d10158507580003040c00e040341c000305544a00018054940c01b503110b074008642050094403590300b00b403220400103010446800401c41c04054071034078404400c600d02d0300100248000c803810041c410040b6009460845562140c03002c5000541600a0350f0303003e031056440301c2c0304807011100d94084504024100810300d0142c400984030b4844c8950300410442d5850280d2001a940c8017249906c2d94019503210921484068000b5114403002c41c007680500305690104025541c0841c5945645a045001210746549904502120823808015032030000e6108203010001340c400c3d1542d075450a118a4401ca10b0915454940c000100081c904500002a01e49190200ea04 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 957627706 1250 957626456 957626477
    0xc0c11030d05030109050702100203130605070e0d060e070b03090d14030112080903210d060f080619021201121208070f03090804080604081201090204031106090f0909060601 76
    0x301592440c1c11200540041c0d42040180503c5c040ca400c050f410000d01d0045aa0511280c2d40000598000329552074030000102e4007441801100e0103520b4000780141040da6800d040c00002c01c0d139070070b03000001420362912883c0040001c40c08200c0040200b5000d020f00780c0300e08241ca449a1071340801d010a0f0005404407034119004d00540301160304031540081d404070166220303030b10490543c020350b02c03070b82e49405040000030400441001c0d00a135002d040365140d69aa00c11880101240c590380c1005030f030342717034140406c0c440d00c0c0c2c002a4071508441110840041501e00d011000c02920410301e00c403220714413203000016542c54840e1000061489200319000d5100b0151040310745c542c00b111400002041e80c0782c41c1440d0f6010350710526060f07018010103450b06441302c2004c2e24008003910304840705d0000144288024824245450141044140651506146441d143c5402030782c114505d201f2200020580d10030366a49040d40e2403184068a111a145003000240b91203035000c440c0c680c0030504a002 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 957628956 1250 957627706 957627709
    0x30e180105030309010c1b1e0e06030a0b0637050301020315120709020705071e08071401050c0a1203241403010225261209100c0c11 58
    0x1980c1a034001070015410145000011166040701603001d84880309402250150a511480b25502070131202016503928080b074042d40d01441041da100d00e4103540d50f40180015907401013450300c00c42b40c103d044094039440d0440010030403801c3c0c400245240c1060704400c0d910304603031101450107240c004017510840e603584041c1800d0b0711046960381c1c440300c14141d80c9880362501c1003210010300d00c09002c03640c5080d100c503800c0040f40d0000c1015220341d44110400c2107140303e031000c03200b01550b2030403010505501d040c500982c0c1e00820b0156105c1407540481e054040d0348a0415a01400c20b0102141c4101e442400c080c80c0f41b019034118400000d041c001070005403030001001c01c403031076014107916058074a80781d05407402d0340100e030919074155000c00c40c1e002d800f80070080e0160240e08901d9541129a19450101c0f20000d8510001100203c42c40e081c180e0031030304609851080d140c001c401c0700c496488070891400c1c9000d00e407040c40c040340381c00c2050307600326844400018120310a00156030454148030 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 957630206 1250 957628956 957628999
    0xa110d120c03090b060d0c050402120f06061201270c050711010323040503070f0c082a01050706061a04060909060503031e1314011e0206010501050c03070f030e 70
    0xc01400303628a03800816000d05222001486d11406001c44208003911500040c0903a4055050b41614030031400912103031070801340c036054100d0310071221103280c0280380d109985480700500c00d601c2e2400031941403021188110791207220611070030b4010818034078104005001030300f00590a03038441d2030008044007554020f00c03c5881185111031b01e2115585031446440648000a00440b81c40c001840760100007034030b84040400403803082c02603100e081d0400d4215440c2002d4040c0c01d00c800d100140440249410814000150341c00c03c0c0303041503961145040c544040c290903400a2700f0b03200c086801420024040015005443c0c440c1e88880110f030ba14480c002c1030311042d0083ca1f42c0340d00100b01090955404504103500e00e48107198a6040c003c2071a45040c078140c2c80d034428a15030101c611980580c0da404103400101e003002c042000303640e00d01c091000355122014000e8505101c40021464100031040080c0c0f003a25601604441d01d4503801d1500618481524480502a0090054404c103a2403041d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 957631456 1250 957630206 957630221
    0xe070c020f1005040e010b040503060a0c05030a11091801050a17100203062701171c050a0c0507090b1914060d1b0c030f0c020310020a110d120c03 64
    0x10800c04601044400b044246100c1c200482c092001c00c11000030b82413014140980209012100903864502e0041854148280105612070561900c0039004105421409681e0400185d0b9000100f015035401071580c50301c59291020341c422008110400092000030740141a69415140792414681e00d101000e1224030501c8400c00507001403102000c60080355002e554082c4004090369003080e030f9881034003456440424802618200b010051080045844980d01c00d10483e50081c420207941801050b101640e098801c4100b0030b0004121240c1441500050b864a4000c030503a03852039540c03101c000c010050600d1841c0111900c0490505030081e001202c411549214042d98000700000f0404c0303801c0e8401c41c0050311a03540c440c5080e071075170410116040440c2107500c0340201205941009041084045008000c00c4550068080140c5010031308541000b6403500140e101c001041d02514030342101c0050403458450b10641070700f883d5005020034030103c114a001c01011030700a4048041c1c0d80301 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 957632706 1250 957631456 957631459
    0x3090127020306192306040c0507110d060b03100605090106110d0e0607060612030e220207020f040c02071e0b0405120f07090207110901080604200603040c0e070c02 72
    0x40c00080d41082c89085441e0070030341c2241002607108920303400d4080006a0445e001c01c00c0901401300062400e003445144141074407410141d017084003558034002d5404000700e001c1e02031180d0032001820800150003505044100405403062102401c3c2050008c08840c454144150041c0c0d0001940a000c0c6500d040c8070001e840c0a00035151600b00143d490400c0c0101198000000b040f90034041442c501c0340c071019001c01d00e43c03015841614200189681c2c0d044501e40e10504444e0110032099081643c6c0700354100c031900000d038994801e4000503c1d000f01e01642036800c942401c0c41400c0d004c0c1d0201d54901070307076009250b403a1b44506014030880720345541c3c055010301c098104824402480e00c54104441210404101c90280200e0b01c0058201000380d48803500107600401c9844c100030101303000c0c00000c1030982d000704080d131502e40d0070341d550729015101920035400a4445007418a150403036001c1f00310b010700307011365904144ca0007259001342071099034152010303203000c51a42c80c840e08aa04000340c0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 957633956 1250 957632706 957632713
    0x6021804181e050304030c06050d050604110306040902010302070501090b06130c2307060c050d141905041a070f0e220e15090304291c0908030901270203 67
    0x2580031260b020421030280c10745441c44180030000015515520400207041280e4401d511101c0a2104105840c0040c212521440c1004151120b03418480f00342e0f984500211008100c45001c1d000503002442040b0028269508100f508014402c2c00d8100c0d5001d0082507502c1c4a00c1c140c00700d02401110301d00703248100001c01d1420002124009803003102c42a41035520094540f810f41d41d06d017012103003000c11040100e800807070b1344140c420280c842e0a050968196004200345415510301102983c5050061480f941d1140030030184518130080025250301890074005038102107802501200c41c8105546c0089c2c40300b81c005002c1d00384200952098448694040213010144c1c01c920080d1003250f074104c00703c0c894024540604043d030400d950003107080401966845051600ca0700c80743d0782540d82035032148904002a42e00e203080b132040b1880550101034a40e9409100c60340100500180780f0017600ca03135808000d00103110b1040d0f1051031108900b0308091071780d003289606100305460011000c0d40c10340 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 957635206 1250 957633956 957633983
    0x10091a030a11072d032003190806090133050d0c0801030c0b13032915090f060d110406050a06021e01060302150d06030602180418 57
    0x5608001454005290320400314008a084072016010342185009954000034040e81c0601421000740b115034010414541c046000882d45018000c0408114080d10203014040881840341041c025200541c000c54041c0e001103101010041c0f4411301640c1182c0700300050000043c0c962484a00e010340208407031040c0307a200d001c120b2910016802d4942030014802c0400210030040030f103110340310142080b40c464007030701d50550501da460341400c0d070015420781d0000c0044080d0030440841c0001143d03803083d005000100c81941c501d440440034140d1140c90170048041c8490808241202080000181d5126071580d40e42d44812504800c1518196040000001c0e40e80200c0c003a400c904600c1040980040341e0308c0d030740c2c4002ca82040440e17400040144c00c52000413119151080081e20b10000c004000d00c0303150304640000b5088051440500b4240600095502840031560000c000664120030115140d4140c084242000b58141e52114820b91505418180384560300483d0b80c89250032401e07c1c40d288 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 957636456 1250 957635206 957635249
    0x1902150c030403030b0603130510020a09031e0b10090e0c011d031501080307051501050907030e0c03010608031803031c18140703022e050f0717091009 66
    0x551000d00b055082540702c51a200c80d0303071524001940a6407400c00303c2505001c1c0d60800c0e07130502440c032410701c0c40b480c01000304003141a440300158055030341107410103002034241340c070f140107a1016140003402c90184004200310008030141c4101142d510b07140071b01034068140a03079901d458100c1c01d0b05001c100050142071801440400c488080344000e4116001800440010520b420003644054980c0e44009210401c100090140801c070044084070a03070103504280000d086400e005007007004240e41c4114050100c041040481601c4001a00030041c02d0707100d074059a00c0c0e510088080c8484001d40740c101d0031500b0008102c42d010028a40e285a5000a05040d04041c0c024040c451001e0000144032601007031038181800d003162a080c00a02d034542c42c1d0b1052100f43c03881c0b034602e1400441e8225084215642055002c1101d003200d140065a40540d40070000300380c051290050604d40c01d904420200c03407200c4000f030100c1c0e5402c4a41e2003000110050454810310140601183c031130440403e01480c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 957637706 1250 957636456 957636481
    0xc090603031e030604110f0915030702030d090f12020a0b0912030a09060b060d02040302090c123403050a14011d0415020f070309050f0609010e0d02100203190215 71
    0x402001400803411900301944170000f504042e00387c840801000980800c0d03440c000c910161181008406c1c2415442c01850280d1a400740740b109100c000e40341c1405008111149441003a0b00358000e100c0711000e00703040c030002d5949040742021200d80441f200452000003000a401d075805040003201481c583e10300905030301034403110708200c0e282511400c014000703503106005040c00404c180300c01611507242d030041010292015142054034001005030485d908006542c25520002094000d0540407204196403d4001503d440b81704030480071075060b03c5aa0305800c0320380519030020051008094150310b290901a0a108030a140d06100d00381c1c6411201000c1e4044d40180180e08241ea200c3c1c2407182401617905c4144110080d030000202103007011713000942d401c09040300380c0e90030b102200c111001c40c1052180300c107483d041c0840181c543c00300740d030f0b80082110056030103441242542c0004801964a0b048150f24001c690039040d20704140d241f00040c00c24a03071080143c50b006075200c0c425011103 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 957638956 1250 957637706 957637711
    0xb090f060315150c2e06030c060c02030715020d20060118060b030c04060815010e0409062c070e0405030301030618020d1407060306050f0616140c090603031e03 70
    0xa03018000e01082e00c00e01020303c0140c2d03104074556908800040945c421180041208105c6403120b0300d4800107002144c0b45071946000e803030035404c1081500055000080ca403d24a51080c4080448501c0c4810190344c04120a55000b13055100c01c0d82030008503040020940a480f001395669000c180104030303c1001d81400210305813040000102143c41c0c012205d00703a8002c890029070003600190420503154040e16081e8003892280c0d405240031302e4500024110340d40240d61900ca50740781c40500c0c05110060380700c141110310a0650909155040340c617141001c00b099801801400b9400c00000c0d2085c1141e5160700c03d550000c00f81d46160f09640d6020010841019004180d80b42d065441005880300d44621140c00c2c081c0d855a264180382a80301440c01c2150b4000310308150800d03d00b00800c1d11081003880c103e00e4221202a04c0d852606140906006414009044400482882e6030b201901290002ca100d000b5100c0a00d035a5030303c4141a1b5a01c0b425010305a12035508181b1418040352034007564 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 957640206 1250 957638956 957638989
    0xc012c0a1104020a17090c131404110a0509040b090c01080903030a18050a0b1605090604050409021c0f02010201050601081311060d1e06081504080a14040b090f060315 73
    0x1c003100207003054241c05d00002c13a01000c80307605c49440108245801c048201084500c0c82c002c3c88140c100b040e00880e4a4405800141058501d0200c00865500d0000800207031101902510161416090040c3da840c802d4070021181d01446007500c001e9445600c0c403a202e001e81c1c0c0025440c503110034085c0d000601003a00c404000c8036200c01d503035000031800c0c0002c0f404103018500200c400c0c213100706c88a080f403040421400c20b1100c20004611720b5180d690691302241ca081b2400a6007500301c1c0007180f104040c41c88920041101c940c1040200300c0421708421a1038002c0c0c0c020001c42d030716480150340c514030560781d201c40e821401032100300007015485d240d41c8111000d0200d50074001c1d1444070b45c05481148000700c89201c407080300800d40d0443c07889468002d1484a00400d000c0329500c0030740d2840c0340041c1c8060f0400310000b0741e501e5501e000d0519003035411030340744044c0e590307a80e541d44d01d000d503401511030310b0710a40101030004124034040050f04e001c1d03c207180c09840758040d50b00070840d010801c20281c0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 957641456 1250 957640206 957640217
    0x90e03160c031719030b0d020409140d02030a030c02071d0a0603120f02120304020d030503070e13020702040c0804020306060402070f0210030c120905070608060301020c012c0a1104020a 81
    0x2000080e00c0b41e025400d910310902086440d205002c1c1c01c0500c4c684401d00f407108051504c5520243d81d50f42c0e84907a0b03e4250181c40001d4003045078202429112146401c1c3d030018820742034446840e0394004010010f0038103c0d82e0400c08240054012a20f6000c28401c00301c0300309014490803030f20404459440c0e04a03200f50030009186a4a940e41c035100c0b42240b4151010030240610f40007210b406200541c4403106103403110f86140741c6680000c00110080001030204800840098041d60142104000042d401001c0240d00000d0080d108080e50142d030b0101d01035400c2c2101804440c2c01000194083d550003400307003d00e5a00e1b0414040250010701064490702d080e90244409a00d5002207559402281d680100d012a001030f8040c0038a054840e050601d54503004540021402c0425281d0035120585803000c0c064a4490002e03000e802489070003c2d55500e00300c034101c0c11001c21041c2298004034243d804500d01001d1a08540b02c0c91395030700c080d03c0c541d00d191040619260980c0240440c05650808 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 957642706 1250 957641456 957641459
    0x50712020a020d030306080f120a0e121615030905151f0e010e070f020703020f060c010f0e251a120403030b130204051e010909020d15090e03160c 64
    0x20070001c03070500f0a9012903a140c1052186400074802041c95003d80c40040942085022003001184201c5044000704941000d0407102030703868182d1181c16212001c201d500e901840c0f60300c0d9405804601c1900040b0014070315140050703029001d418501070b048009000810050301c071b6081c3c800c0c8010701c06440e1400004c105c90340d00c2c40c3e030040c5402030883d850900d10b8641c1444069094032030044d10260074130411401042e281e41d8000341107016258107640040c1540c40480c0440c4c114000c9100099140d4242105a01449500c0e80700c09054000390089441c0d101172041c8802a400011804805614964a040c003465448070000069600307140c3d9014907002d6a4903952328540e400340c2d0201c001070f840d4a207030300030380c41d2813480c1079400850084c0440c5464030380000101003500d0740071802c98070318000c0b903d003482d03a02132950390004282081d0155071b030303560340300f0329500a20702110700e0304600e841c0d04000b1407034100c5480f841c0f011b21803000c004c40c5006180b4060300d5071000403150855211851000 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 957643956 1250 957642706 957642709
    0xc020102040909140d02030301030b0411010201060e040305072a03110a03050d090807060503150108130b280204061b15020a0801051f09090c180308040f15050712020a02 74
    0x44110590203504610080d008804005041c5621701c220081154024401407011031200c1e41d01e6500503a0120007180714114400040c2d0141c9003960110560325a960104424141c2200041500da4894000c54031030492080c028240720400080c400c858680c02c0307100303200003003a00c1c2c9840031001c0020044042566680e890a02d4440000e055800059030001c0c1000351001c10052003028007110b017003031070171458141c14046d040c40f1400d26039410083c0007000325160144160520700983d400280c140040e00d0704109540c1129040030f00a41a48000c103010560482a442910b064a011790b86481044003182c501050300513101c1d20079503060003ea03040441801e1144000c010100c0d15440700002c540c540000c01c000c0c200c1d41111451090705190414000d03560110310300c42030390700e6002c0004083c1200c0b1030840f0111441c01c82d01c41a480c40040210502c812031000d84100e4124403c13015441c0e40741c40c54815003455644000020620074403d540025810030699001c3ca020340c8121540d95140d0f40 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 957645206 1250 957643956 957643961
    0x2060a0c0b0a060b180f0d03032c120d09020a03120914060d09080c0105090105010603061401140a17180c0109080d0f05120f0a06090902030c040e0102040e090105151002100c0201020409 81
    0x11f104801181d40d03080b0920400708250109002c070101100410004803504075040e8030394407002c242d0840003d0010707801d02e440300540c2c041e41c0c0584d00540a038031148e441e41352904034900c0d10602da0001c680c0c0d403a4002102c0c0c116190780b1011301d1000d8030305400c10708021a41d001402c841c11080315420014003504156200074820b0740d108280260011071154500400501161034541240601c00c0b1014102c03541641c105c07007220240d41c66464847c0e034941803d0b008a600104192500d266420300c0b405000903800c00701d8156180140c07080075074858100d5203006642480b03162188181a4020040303024106006005991100525041c094600f40c64400141e000107001c840e4135440424039014461030640500c6031038081d0402020820100905400196881d000c5614491182e0380311040c21aa4035400e406a500030b08140451180c01c1c105403c000d806020200c40d05c050031900319601c41320500e4250070020601c00150090701000070480b2080010381f216070890300a640d004c100024150300c3e00c0c03 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 957646456 1250 957645206 957645229
    0x1a09041b08040201140f0315040e0a0503030405280314090d061e020f18040906090b0a0f0212010e0604140112021e0a06180302060a0c0b0a060b180f 65
    0x35503404000b07140a10002d42900e40d80d06100c0a09a4203020b4540e6801c0b429007121380000e1007000a40740a04620002009800041400d82150080e0b60b120010080300001a40c0100d00c25015500418201e00320181d20414604603941d01c0c030000755901004c02e00420301d4040400c0b80c0c540141c94260300001191310900320501c2140c403107030713a141b43c2203d850322000765101c141400002503241c940e070f43e1360140080c01490320340340c429200340031243c103030341c0d2035504c0110303002d500c020144000c1c0340d9401d0000490500302c0f40305941a003468103584000340140b08851301032081000c1e00701d05901b0714034050010000200601d40240d030f1042d0079040b100840303481a0092286100c05a0f4501e40340c41030098402e03103e48000d03065410340300342240c2603441c21510000da50030303450140b800c0310309890000760705402d651019402c10400101001c0d444e42c00180450b0440c001c0c80d12038840d0f03e5045d420000ca808502c24101451810b000e21440d80703241400c00b81484400030000d21103d074007030002440700d4a05 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 957647706 1250 957646456 957646511
    0x1912020f07030e10050315122509061211120109120f020303100b0304020a030c06020c040612111207090f0203060102010501061b0308040311160503070506041a0904 72
    0x86070020400d6840104020500c0307007592816418065880003030858000130705000b403100000700400c2c12640700c480b2541d481003c640c00b221142000110040c09290000d020074418a10440d4080391541c99401000200c440703240d04008000619190002e00f00008803100358071803004502c8038404d40007401483d8125016207800740c098407040d600640a45510752500b001e640041c010440b280032603501d100c00311a1200031403a526515032000818407c880d410003000032241600100383d081d40002d01850141054070308008050702e98200040b61003800400500c40001a00e00c840c980c1490191001d10f1101c5c182104c041c507494085010559000040f69800241c3c040200401e0b980d09003d0a8010100c60402407080c41030341042c03800d0241445000340510a4243c04101014460003038994800b404000340d0307511900c0101e40d0300e01c1c00c1c098429640b0a100c4c02d000410380e40b81c064115805c45040e4143c5c0140000f00b5541e0307481c6a003003501601c0d48a5640c1c100714405840d0484400200c105 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 957648956 1250 957647706 957647737
    0x170412030909061d06040203040f15060e01170c0f040b040e0a0c050405040503030f270303100e01060e1c0209180f0304060e04023106140708191202 65
    0x1440ba1030400c642040d03000c03a1510b40440141c507120307130348665116001002564090303a00e6940c0c2c248a101441048401828841850941c0b49101429030204050300e03004910100540d907640e0a4201d6221159149201034001c00344403402441d11010b48411020302400209501c2510b40c0020700f11040155603001d65084040000100880d00c480c45d0054801168100202e0415884456603030100401003030146207501c001c903002c11003202c0d202c809c4e0852011298200e10002e002d841c5c507500142c40d2840d072071008400200d50845000e030140c0c10b031203050707840da5603000c5203508100c0000b81600a0b07a401c0c2c10058401c5016844d5130807124400e036000442e482014183c044c80c2460b000040c10b524415800c14002030003040d074400001640114102c40168551100d0940400100380e8a82c03a170f003140030604a103200301e040c0c29401604503591030b1200071421a0b4443d0307008aa01c11050000c1616501f0085022045242c00440301d680f580c0f446d2505001000c200c5d1a02280e20a8240703a00050 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 957650206 1250 957648956 957648959
    0x1e0f060504081635070b250308061309060609020702030d050a050d2318100b06030103060203100e040819020d0c0210120f05040209071701031704120309 67
    0x180c003000002c0000005010307512070f1519104000e03240c2500300800c5400daa1000c10f20b811107441c0350030f0006840c0301884c166240c0035990029000c840d030000140c4413640341d01241c1d000c030030b481c440c1c06a400640c154958090a943d02c40030840d40c82031540032400901d60b034418120210381c49214417006003103043c10059071a001401050318080110041808100d030230007003241910b40c03040035191105010240450380d48a2140f0407000c803649800344584080009040003e081450041002404941019266080f80024420069850f40e1580340e030841010401000000c0055000316480143c2070180c03e0301a840b0303224208000800d0340c040e505103401041c0c075100c1d0100c4003014485220140018210140c07000c030003420725501c42d00040e03c81c05041d00e82561150094074a10381d030000a41c4100628054043c050ac0200015541a030080c01c1c80d40000382814028a1503811250068101e12102d030728540d2021135941c9104042601c0003014000001d807007803117140c0140707071b50701c20b4a4051805 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 957651456 1250 957650206 957650219
    0x30a0501050405011a0d050706230c0d180b0915040314060703150e060d031202040603061a0a200c06030f04050f2109041104030c03060b09101e0f060504 67
    0x810101d0805d5109403000c00c91031000503000105141121a47e00344540c4031910310f40103d000c40071212100849840c0080d0b20021481c000c81c50622200c0540c0300c40e503103035a2a0081c501c3e684a140070345190f810040145908503c4c0040541d8510041c01800528090300d0b039803440044059200d81500583c445001c1c81462030f0940640c0c100c030000840345103149494002d50703080d100000b40150f07026030b04c1000846d003818032400001045100100f420355440d6543c00004004050724411030144810140c0e011009200e240c0446250180555410a0454540140004d1100401c0480f0014482c08170322640c55156940550310901e0840000002031030a814043d08010024072039103043e401180e05241d4500466403c2c000d1141c0401c0c0300703030301c40c80c0002c085402400d0a140400300c0b9032000c2400410810380303950710700559214000502004e207880c024011500d40030703103104900c080c03c04c00c00c1c01540b10319400d920b500007000c49d000c4441c55403403070703004a4400607820000010790001000c2c49038 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 957652706 1250 957651456 957651491
    0xd060b070506161e141804060b19140408010903080f1302300709091209121106160302060115050f0d02031b0f04061706030c010e030a050105040501 65
    0x80d03004114102804a0160000d113581d010701c45a036002140210080034661040301040b980c102c3c02c2d49140e41c2c400010b4111206010b804003000e11850038404041080c075840300c290f0340c108a41d403613002480040104142c07003441c00d0058040ca243c009000005905d5000d02540e5030040c0291600c42d40c505101040c11306420340104090340080d076582081c2c0061f25098a041194159a42c0b180e03072050300c10011001101c1c1d45e580f4240305214419022404198540c445100507200d10501110218071180540c0e12100034800c080a4902a1040c00c01103100110125440e80d4010032544c984103c02584500c500d00c905402d9006a2080c001804001c81e801020035211510b402c0c140d040c05a400d03066400b510900034140a03090300407000c10700c0041415060008070100b000b503691155442c4d040300c4180c1d000b038459503001601a9510010103a101d20b0002c4c01071401030040e06441001e90300640320303a64802203603501441a01c071a100410000e00c00c113401107100308004520350b222211403200 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 957653956 1250 957652706 957652711
    0x1017030f0d0b03280309150905090c0409060305030903160f0308070218070e1e3010020a020c0d08090f21010f271e0f0b0601122f0d060b070506 63
    0x10680004c500305446190000c1d049021102704481c0c41407199603664a4170498000c40e4088101c06003420b40100c20001c0102c041c1031135820960440d0b01e007a400250744070721f00c841e03840360034a60a00e43c0300c2130012a8080d0000c100d11070000e40f0b030302214032100100454844089810400041c41c44004071003510700580c2c0100ca0b80702070342115981c2c1c5150b00009020391030032101420b514811507890390001010180b4002c914404a0642c0ca01d481d010030b0082c080e602484402005000d0a082080300d440c0503215002c1c3c09401c0941c7c6418400120705003d00e8000c079840c129803050109145410520850124051903041d250000c41e2244082081d0400e660f850403001800e109003040044c800d021080c141180309401215162030201c50940c040b0103090241d00103441400d068600d0400d0045c0da00c01070b40a50005e0340c070410034040881318001203d0190416400e04035140344030080122414452650080c84015081d14002c0820400d41c2140e4443d07000040780c0c440412036a0900000380115603 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 957655206 1250 957653956 957653969
    0xc02010608030904050402040e0a2d0b06190510030e0610060c2010050304022106070e0301062409060302030c030408030403171017030f0d0b03280309 66
    0x100090420525985a003d8071500601960f9540d00003000d5640396004010002d941c0d9042ea04038442d2030810300c180000d4821000c21400720b008680d81503500854591805981202d00020507450b000204000300c5c0e50f20f5081c0b16111000c07500810160f440c0000c1c241014025200080c640080552050610b8070090503e101d58812000401c1080c0c1c0010f4103050560b84100f2141103450040c0b91085061021300e0380540003644240c2680d091500071000b1805103000304c0c0c4a0208101e40150850034502d280700529641d0030090106406d28041c05034600341d541c00500109145480d120410031105503440404408046101c1103600b03035811000344005041e1514081d4510f00e0030701c50810081c403010700001d016660010026003803500c00e20700d402c010000c541c10000141850346034100d88204030300030750001c10640200b00d0307140480001141c1e506004860b611b420702e03000040440050011284142c1c0501585603017900c030441207584103580c0103811031402410036213400c00030304803840d541085 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 957656456 1250 957655206 957655211
    0x5101d10140612070305030d090b010509130b06030a0812160804030f12020f0310080d1701050d0f0b04080c07360f15081014070c0c0f0803030a0c0201 66
    0x5807441112882903507121809440300c2c103078032000701c0d041e0307150000542c8090614000400c404007000020b80100e01c84500840c1103000598903801080942c0b8015966100d14103107007285200014004901e50398080781c0101965044080d6440b11132250380070b280310010390f5041e00204403503107811006034920346000c2c5c6031100003860640d802615040080800c4001d01903040c03101c01d018035980c2c041301c20b85034000542e85c4d12801c00390002c04444003980103d96040c02041416062140324800c2000020842042080306901e0300060002c01e10b44130200741d8968032500081004601c04091403805688241091507940c50301181d22428080ea680049030300c1043c0340b4400800c44094101020000c4c1e800010140655903103e10f01e000786045071001c0b0ba03007410311700950201012801d80d00c00316009182940d5041e0407940780c010442d14421a1410340b4403417000450b03801c0c2d2254603130351034a51240340d861070444c1d1186802d00f042c003016400030103294030010030001181e42902550350f0f8001d0f20f000030b = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 957657706 1250 957656456 957656471
    0x5010512182b0c02010c17160f02010e09060a03020f04020906030c0403140a031713060e07060e06090a0b031f030b04050c03011b14190509011d0d06020705101d10 71
    0x21312506c2c0444000e0315800342c82c5204d02141005030102c52898481c0502840c3c110203928080f40005000042a400719422000e000b03204c0c240405124403c0790000c10001c50141550308108101442000c101e4000f07509010141e0700d501c59000950291818554040d25185589481070060714a66080423442d000312183c8000640c01c007001d41120000030560b5101a5501c51f8020164590306901504240c00c200b040710741358fd40410190151286540c4070554400700c0c4050100364817a08440540040c0c900004000c9919008060358010490201010300070190383c40d80d114616203500705964038200d54060008111381000400005d0100354001e2040381a03030310f5140d880d510710300b25400902100407401d10000718107034101c41642c03007810340c00d403010201284c00510a0300f0245009000c81c83c0760300001043c50490322810b002d650020a15800704d82e099031030320040e410030803044916100385444091404884e000740b062440d07000340c141c3c028481c940140f0b49050b11031071030b00c00300c1e0780303480366 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 957658956 1250 957657706 957657709
    0xd060f0609051008091c0503011806051503070c3c1119090212010f050d0507090c0509060703030c080a060f030f020a03080c03090a090605010512182b0c02 68
    0x9814001c50b0080c100f0000c4c641d00d480c415400d10350061b6800c0d094048940108400540120145041e1011041c010180c0028442c61808940d41ca00905500495801030050400c02e000c1c015a440f8100703150407011807803213541c0c41d189002d4060354004008036131010300e15051002c003034841c032009540030700d840c1c8829152a0b8000251030103044900509400c41c00c4030114119404101c001d242d030100855940d50442c200454800080c05401c1440c5103100c0d001649103020581c000c0055046030107448494540070080d0014600510b440040c03103820702068025035140300103020024003d840105480101c0d21009009900c0204440080c070b2411006102d014003a240c901c05403130748a100501c1c80040b90000541c2c50019030310080c60a0400100484481404800b9020b110b070300340c07440e0000c1500c9030200c0040c0ca050740509400600c0074000c802c0c031002a0510035410008040c0e2004c9188121400075042524402d4920a50301c6045c4500d8901480300e00d02d4140c61b11903107401a580d480560 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 957660206 1250 957658956 957658969
    0x20109150501062106150207050907020307080a0318211812080318070326031e13080c03090112050906040210021009110405090705150a030209060d060f060905 70
    0x136454081d0350583c40003c50707402500d81c802405012030200c01103404140c9403000b942c0754000e000300b07401600d41d0700124410a0001080e1012268492030303044c185444900118003c0030b0610205540e0324000d01140040b8540d40041c1200f05010a42c042141c51010301c00b0f884070a601c0f0155164038080d203010400041150500d00c003083c2e1100d95030345d0301d450302c0600401c1c204900c40b04418900030304500100300400804c68141c0101c8100c00a0340541681d042c4522a000c00c96100d442da10f50031903024201d08848174802e50042d0b0010b040082d401254482c0c000e65000b600c5588010b62000610a41d0f42d130704540301108842c0340f000244000e02c2d21884094031041c0c081c0000b405510080440c01d102802030004d0012aa5040020006400d0302d0a180840c00e44102002d40960720303040c085181010081586015604003070b0005440703286036002031f40d040d4003401c800010103509008101082e65000000c1c81241400740001c02c940742082810a0f40c8490381e48000309102111100300450740340c06 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 957661456 1250 957660206 957660227
    0x20a0215010f1701141e010602060c0405040b0d0501060303030501050a09020405030307080703140c0a1208040b010303120f021231020603060604150c0c0603060605030112050c0d0302010915050106 86
    0x40e404880c0c95680c1002c9140540300c032008509600c5017440c00c1084445159125a0100e246002005070700d0741c1c2c0f03d20581e21804203480190f4010701c02c00c0f00b8445070406401060020b0405044c0c0142c8030150b4540c20b0845400d078000300e0010740c4490041006192100c6180d002d060440c03030442c9030500c0d240c0001d0341da200c0c80c440100441d00c003203042414940944615210504440d0030640d48924288007035807549019101251120000f140c4050014400c2c010184101d6202002c010582d0868900382c0c0c13079068100009940d0b548581d0800c1200300e0600140100700c6c1d0b1210441c1590134924800d00c06408100807070001201030b868068080c030203034500702c0e41454050340c1481e942d44034100810700034030998000c40250aa03d41d1541162a4880c4505030a5805181900e0816072103503411400da81c090b1103400300044091005000380f403000840c0d508494030560845000c0310600c2c002c504040c1c20f618060303000d40d5450a03504c0c06d1141c0d5100807980c00e000d001081000b503041040c003600d281c600 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 957662706 1250 957661456 957661469
    0x11104061205130210020c04061422020c070e0f010b120a05070c0b040b0402042706021308061810060612090302010e12130e0c0f180d06020a0215010f 66
    0x40b04042880701c1900704070400119005080c001c0941190800603680303101e500f1207680910710340701c2c2c00070b0109841c2318400c1240324000c040c80c00340300e0280385090030001c0c68440400c1080d0308014800d0000700c1000315000404031b84d05628003a1030480c0c0b856190940c168019551742c4070405c043d2802050031184581e1140f01e0500010f0180c8550108550500e4038010051002c07200c2c4081c0414492100c02c41840303144212424008049490300721102055180181c03400a003001030301c0c2c000030707104ea005000b076078100040c4440d0081e5a50300c034130725060301a100e98200c40c071404c1c0040d1422a080c0282c80302c29031035007070a00240707103420801801902391616145080359501c100800f014400c0d0801650038203020205c6903110301c0720304141a141e0001103540e0300f82021030b000103042014207410030311400807211054181030480041482d56404452050107502030705000030b03066a114014900d005008410040c1c6450880354043d1401082040107010540014010007280c4406940403058501 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 957663956 1250 957662706 957662711
    0xe0f070608150307030311011a0109050d080d02070f1202010614010e0d0b0f1f03050307020909070806010e161d04020a02010b04091a010b070b010b07020f03030d09050111040612 78
    0x4a640b561200015000e80070359260042c00304c00420b03d60721100c5084c00c4140380340200311113040031042c10100915019502e01040190404206c0f514240048000c001d0194504625214030b1000000c220781c0f10640440e0026840000f94080c4000a4110760b1840c0090000f00540f41c104503110303c2482c800403180c0d04010400704d201c4600e465400d032480b0703510f511080f890014242040c4255214408032165a025268003504403040c120015a40c1c089036004400341d841e004040d0248200407800610b10120f81c401e00d0710008944000b0400103000b8200d1191082c01070400030700c8145d41080040110081107038688020708101003103090042403c2086800503518140002d0603400342520103041e0381d02c00d1a200c056400c2c022000d408100318062015900841e030780301c445e0608a401903210150440030601c00500040c5000c0e0010909a8001000d4081803010880040d156034131540b8003152181d00c80404408110090107400f10300650138050310f06090030610003c20340b480300e110980c071058 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 957665206 1250 957663956 957663961
    0x705030f040f0305161a060402040e1801020f0a0f031404020303090415080d080603010e0d12021e03011d07020f0a0b1b0328020f040e060a0f090b03010e0f070608 71
    0x60040c4200d482c560944285d0005242c02806c01c072441441030045040303036110410000e50036240501c21202640c80c0c5464104c0d0f15127423040400c1000d40d00c034000a0507907608002c0c0d60328a83c00c00e0041e004c007a40503561404402101540102911290b92000f00c2d20b2601400380300041c0c0c1d021068504484094900141e54030310750220700d1007903609500644580c0034061555a6060340301040e103100c1c1c1016002880100a861041c0b5036078010350802c0310004645540078140821580c0080c64651110644103480200304010000c043c1d1080e402803600c803a562101c5401c0540d1200d0413a4401120300140900c6101c9a00103500c440664400420f074000982c00504142288405080c3c075031520440c0d182c42e4544980640c01840c5034032110103281e031041c0c40b4056050b03464001c4603210aa00012581040e2030101071040000f00502480d03404120601d000c950340600400e90740007000001d60216019030310109050071250100c184112641041e000d07a05034500001d6400101d070040e01c0c0292156 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 957666456 1250 957665206 957665213
    0xa030204060b2d070f020f090112021507021807120507030509011a010203040b0f130b03182b230a0f0c0206041203020a050f0616020f070614040b070f0b0705030f040f 73
    0xc22aa244043d40300030510300104403040034ae40b1f101e083e1482501c80035001084011075081c07600130100300a60001e1b8401610010f04216042e40b6080880e50420507c1582140c01c180203540781140c04000080d9500d04002c1890424020814408000711912620b88410030000b52203101324003d09212200c00901351f1103aa0031981181c94691540404589094440390302c1348859206840180e031410303803018078001c0c2000100348211641941d6507804000c164200a9502c0c0400c00c220010a1001c0354003007102c048030700b6005e58040c05600460301e03901c442003d000350980c400181400e08109141c84140010384400c012101550180607043d29114101d140403072808041d0700b030040c811300a003145618841130008070349010b814081d14981c0210351076034049980c4c00300a880507401d94090042007007100d001d01d814402882c40b1107501ea140c940c80e442c1900095010450880303a101c058100201401500c102198008945140107890340c1000c0c10102110b440c0500090400041d60740d4003403c2 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 957667706 1250 957666456 957666469
    0x9010c020303120a060e0108030d090c05090907060f0504050f13060f0e040b0a140f100b0a05041e0302030a150902040914010b120703030e0a030204060b2d070f02 71
    0x240d006007229600d030499070101e16040000d460340d0030741c0ca007841c00110707100442c120b040b41a1000c05005504007070fa00f00188014000c8000e040e6044c1e90801e40204068a820005500c1007401400a21220389001401021050701c48008000c1000c244400c0c0125621400c65845c44402281c07002c45c4242c035210b002c001010682d009101c03170040224001043c040300c5444602c2980506000a81a41c852100d5000d80b0a2091000020b140d41400941d07000d81404a40340c00c111120007843c05a0384490100856074060713030f0050041107012500300001403000c0c081490980c0d0300036607a54401e29540c080f079502c408000e4004d00c1c1c02c8600180e03005000f0554409811281c00810034412801c0c9810109400700f04480d16903495400c0c0040300304142010b05c81e00c0c0c00c0a86c054000c001043c03946c1c8040300d20070480e07e4215403111400c20000090380d9039010b01400351900400259a800412030f210f856003288102520120605008006044031410103135555180c002c03800c40300d83ea800780f00003100c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 957668956 1250 957667706 957667727
    0xf030d1412090f0f0705090a1802211c0203070b09011b0903031b0b061905060d0b1206190e010e0d08071404080a030c02010c0602031f1215020901 64
    0xc000c903505042284005001030000045240f000664090001504071541c889078140250b03500940d6240216484181c0c2d5406180303002c802d0b500000348820700703a0000c0c4c0d450122110810003d24145098812100107001610311405101c1407101d4903400d84101035241d006000026241404900010300a8402900100c8100000085d05180090300b0b0780c01611005143c0000d80c0060140300c8005907a115851030810203e400220425480c1d48000c1007105c2c1040d11078510301807001a450019a94071494080c02c05030b0440a80420301010705024014500c1c00220300380c80302e900c0031047c0101d003010003e400c160941a414041181c3c50b51491007030150102214001e00c510405900300304a40d40310300c2c03460254051740d44801250fa07500d1046000b0b4015130189800a0700412080c2d40040d004aa0202042c3e1040c14403142903107841d00c540003260412140303000344171b00d440d10100680b414140b61070082d10310b030707800d070240f0840d03689440403810705130612400403980c001024012a17004804080 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 957670206 1250 957668956 957668977
    0x270201170421031505060a02012304060509030f0d02070c030218040606081b27040803010510030c08040b100503120d0506060909130201120501150e0f030d14 69
    0xd080a103080e1141c2c6405500410508026803150420030b807203801424004889803003459150760402e410012a5480300d68103205541d658143c4160803030741c50118003900b0072800340d941e40600d001d00305541641e200509100854008200302500804910240e40c55a04030000041c0ca4954034603003c0d80007039440d000a5400103521000b203450a0700011118410303403052205100c01c0b03642da0292545c6d005481d8159420000401e407007021030804240805601c00c0460303902c80799007250440d480310310406440a9540c3c010010062149003058480e03000980c0c8107140402144140c2c100040c250300e401341000b0845000c560208440c1040f00078810042c00c0018180d9280c1c039540000c4003400d40c00315010508150404c3c0000301c4514000c4140c46655102614120b03070342d074945980200c043d501e400200c0c1448410130a00c03103c1c9085101b090b0180442d0202c0300030400150340054610f80114504500c1490910080c103101d84000c81c00d01a0b003002d50804486044680b00000c00c1401000303543e0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 957671456 1250 957670206 957670247
    0x902090f0432070905090a0609060305030a2606100c060c02010e0606060a1709011e02030f0a0b130b060c0a0b0f01170c12030c012d270201 61
    0x24480d504504000304245420700700d15060340303002030044504480c0100c0f984004102d0091040010b820000c6c18564400040c4100290300381d103500101c412100e1a42084d80c440d48041150303402641c0280d8203c1040c1c0410340c1c115682e007542d50300c901c250303040242813500414000d10720850540c0103000034200640d01c65410303c807640d4041002070080040711080d04061159034003080301401c01c00c00710381e0344410035900c034189880b051030860840040074020300039665072a011010103110403018214000006c14000d03a1340d060070101003001520103803a201400385403c0900c607065603481c401e500003000801003c40c0703000460000804c00e00034001c03249000d00520041004000840c440c1d02e1103200031030104d1800b81d807103105140740c0c2e150060b40c0100c240d0248944281f107190101c400310441040400301c900c0d2aa0341b00040742500c95108008503484820403501c128003a000440b002400b104107002c101444440100c00f41c22005803400f00304c0d5890b030300040029644944d091495603800305840 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 957672706 1250 957671456 957671471
    0x12020a1211010b0d05100c36090203100e0c070606030804170d090603180f03110105090a260f0307050a020d1b020918120403060608070f0902090f04 65
    0x904400701e08100607815529040c641c0302d483c6000c103250031405400c01c001b41056840d4298410003440708000240a0200c210f0100113443c07620824010007841c1c510b8144c1c52060268500000c40010b5001041d170035005208002c032072180707840c0300e0302181c0502c9002c0150361601d8200d960940720b44200607024608041001c014008004010002c890f000070300c0314070151885070f91076211440080c6580000f110360808201e9103200c1c0d040f00300c00c7c003c941208100707048141d03180030011001640c120082158220000e040708401c1c42480d074084000d0b00545000341e010758505906809106018440d10040f9201e00c004448410646904400070310311150b480c1040e56014200b50050000700c1c005100c0c0381c2e80b28480510400c07900b000c100f20155003250120305030b801c1095624000300680412001d2030b01b078210000c0c003001080407140245c00603a44e00e505604141c82a5108c0d6000a2140d81c0f1442d810020b4242d03030098070342210a078400050b00d40803131800048415604080d21a030040c00c1600 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 957673956 1250 957672706 957672743
    0x32a081006030213060308161a0f07080c034317070903021e131b02070e01060207060c03120603030f0e090702060a0906060f03080306090106140712020a 67
    0x48103081e03900032100e48159505640b412030540d0a103010040140380288403402281c52003496104e90340d031049c0e81c0d08142c02481d03142c80030304034001c4550660361201401403100c3c0300d800038802501b2220721180c4c5491403801c1c600d682c21a03507080740512041130700310000c41110131910620025084040402c400307c1028004002e01d5a292040840034101080c0045034a15008416140c102d0342e0281c060018540ca10b003000c09603005020741560003158498846c001e0b5080e5220320718407140e10240b50030408041c1a03009241041d41d400c581c01215100b00140000c58000981004491b1389103001010f040c0580390458241e20840742110610b401c15002008040d0008081e495100f0903968999590000f4420031441342016508640507810500c08a044402c40750031004000380610b42c040341e0a03640e0390040405101c10361080d10a04008018041c0350700d0310602c1d9a0050400745444541c1000c811000d40892041e4034008003505482c0075001c43c900d000740580924582c0000c0b060072503d22104 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 957675206 1250 957673956 957673961
    0x191e1106071a0705190e010207150c150c020f06040b040609080409020403080415031e02090a03050a0b0f060937050907032105030c09120d02010c120501032a0810 71
    0x241c07615000d40708086210203143c4600d5206e0081700c016070042c0346003840c2c418080702810307050925a040201454080012070140c0300100c444203c0020005400c0681d018001e04000e4040349000681c4c00020502c404182082c000c96041904960000361000e2145000710a0340305645c4401c440c0d900201d8004284440722018100311080c00001d02503401a121007141211f007201c40503c2d0404105020716001c006a5019001e20324028005050154480d140d161900000b00030444843d41c0344c5007003090342c0041d40c81c9150445070940b02d527000da04146140014624444500001c007070f10910310105c00d510075202102c080000120108090b081400d4156118a1280410790b0500c094420449048812489034018481e45680305410340d2034484020074a9030041c48200e602844200c59405940d07070070301903000c000b507840d00005858010740001070980118840074007116403503c4010070100358851030f0b46941222910781c140f0b50034820150064840c4658200c0c1800e0700c5450100d024030f00556 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 957676456 1250 957675206 957675217
    0x9130207120c20240304061a0d1101170f0405060702070f09020705010b03010203190506180103062418110903030703050d090203191e1106071a0705 65
    0x10140c101035100c041c0801d0b550744414250003888200940142000440d9103030600c105194001e14410140c4525000d80c4400d00844043d82e0305284000700b070100b0400301e40724590720680c403035611605c1d4100042c00214019150140540002407112401eaa140c0c03144e20380e20522900101744540303e04040326090443e600444044810f445128003082c141c80c00001c48200700c69a240515500c0350616910700060b410a00d01100d09640f5041501c04c6603a0038006144100c401c8003000c01004001c4107540151070014003818080c40c0582c0c401e60359001c515030050b042d039811607404074091340010081c105c110745c0d96864250850100030b010500a403840c03c0f0300140c4004542c1401000c04141c10342400f0f1050305000741c0d06500402282d400617004901604405408a1000506004a401190424592240d02030a0004404400d42003204001c10340d222816190401c03c8803641c5681c40c1c0c0807038040c800082d44510000304003041000441c1416604c90400320019034600d0518080282903a00312 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 957677706 1250 957676456 957676463
    0x609051516201f031a09040302010506130b010e06180a240302160b091501060806040608151f080703120306120503030a051806160e0f150f09130207 65
    0xa05036200030034604224841d58510070148807149081840500380c004041c0355a5505101707080c01812001c50760f86260380741c8120700079000420240380010800a1503c02114040c0782c0c245880e85d0b0060a13684040a0b0880840503288940d070f4140006082d810f80c81e5402c4501d130f110940741000300f41034800350100071103e403e4008a032200c41a00d04250140d005484038007841c80b00440301440400d035a82c081540105d5020305840041290707401054409900360003240100c1e03c1902407042c142841e01c02d1400400e520070107070014140045100d0300d0b40341c0240c032807004048842484039585103010a4400107107281c030115a0030681d285011120504450165404680341603800550300b02809030150034a94060050b52542da5503400d0500200b00c0988016000921410301402d60030b002c02589010304442c0b401c1120040c98200d00030141c0ba42d50203d9400b481c1d10020740d0f22640c41d09203000c449114070005480d25444c01e240200d4141c0500007040340d020260800e04c0b40c40c0442c0d07a00420b480c900 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 957678956 1250 957677706 957677753
    0x91109010603020c1507050c070603051b07231204030302010b090105060f030117070f0611060c18060f0c01181a06010f051e030a0e07050a0609051516 66
    0x3680d600580481c0120130806500340c0203000400b8409480710300b82e42d404249400c1060611511000f418039000c00303a082100032a50703e0f01031242820b0600c020320b80446211400e40d141c03100d13590300c2e005540300b0050681c40413500809000280e103028480d1f4840b11a0003800715484598030704000b400780c98200c01075405480030313100200701800d01401b1503902c1a0b007081e8580c80e40c0d1900701e201c4541d4081209034443d60042d042e01040100f00041901c0090001d03980e0b42c1008912022414144400601481090f4804001c0b1601d203050000b245a4580011281c0f1521501491180310240c0308208000100b54605401100d0360090501040f08490048004402c0226a01c400c0c0307241c000300741c640ea4040348400e240d2410b801d1140e4001d0041031001900d1a619080280590038aa0000e071050f0142d00d84456203d4540a41042800011300d800c40c0d440759000d141c462f000e8010001030080e40c0c0100c0200f610704070740c01040c904690b001007905802052403941070a0105802c484182220301c81d52 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 957680206 1250 957678956 957678959
    0x2070504230a0c050901200a0605010e06010804110d0f05060a1b30141510140912250e0703020901120c0c050604050a0b16051804060909110901 63
    0x82c0900c0b600300041c00580340c0500c0d00b441c3c3c80054458003000e40c0c410080c0e0070784030321754402d0b44414410310004500c40c2d0030124ac6541015116140240300811780d43c100b200d06410040070561200c104400340405550941c081d0040b410a24181c103494180540944107101c01c1c007140b88550350180d01180c003181d100840158048104560180a1034500e084001000507584441c101d941e40b04225403102e440c0006000c0e5800a500c05641c1080b00c459545040042142146081020075100144440d140c5000e40810035090b408840c007480c21010b004002d100d42407910a0400c11200300c0a400d01d4100d000700300e010a40383d0001c45203c0c080c03401449a40004114154024000d849008070140c5800355004003850450006000c0385285c2ca01b00001241044003084040c440e99014601920203400d4442040c1000f0400c140050203601011900c81c1c40800519030003000c0c1c540d40c64405021441090300d89002801508054000c0e8030f5032440c0c01040310400c08002c011141c0d88401b50343e2440b107607 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 957681456 1250 957680206 957680221
    0x50606010905010f080a050c0c0f2d1b040b0901030c0f0e0f07030c03022a19050a03050306041409030c0601060206072111120108070b180904030207050423 68
    0x200300004844041403117403022036850807454204030351044403070000c0e500300b107080043d180c078110468031140d22070341042d0501ca149800515100000402142d40b00314018900500d860ba10b20078001450540702d4001c245060f19076540d00507640014004240280f00e50312800c08800003a06d902c070344808911000f0001601102022509200e4040e848024034650358050040d03001c0c004401d02103080690030005901d1000c0d0300107024001c9802c902e0b00501d00300810501d5840c1c01a000305500c1445003000c20394000510001e8100c101c2c03a40b5191450b126242d440200700079060300e00b81a60711082000801060540c0040030340341c41c000c1e54086410a90341c0c0e290503a103401040e00c40d100007a00d4003035a000d44d080f23200204421803e03c4840054110040c00e0800f5694102001c143d840c140301a0040003030110400c8004007070904003d040c0c0c035005406a100509009441045000302910b000107018180207114282c02403002500074048115001110079036000044030442e101095400400d290 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 957682706 1250 957681456 957681467
    0x5031b0d020607090311010c0b0112020a0512120f040905010605070302010b01080610051b06070504030212030f04150509130f150b0d0509030c0d02150f130305030a0b060705060601090501 82
    0x80c03542621401e10081c05d545800d4141c0300c6440c0305a0601004102400003d1144458075000303000210500010700501e1042101c1d009055214030b2007080c0014018900e90f070040340c8c9611500f5902c200590b0740d001f40d65880030602035544000f0b06586401c00006096030048000c00c0010b105c2e500800c03001800100556072144241c520903005161a03c181c2e018600502c002c080d00c0c3c0c89044449070b102900c4104c1c13450000c00301c2d1898005a40880c0402c11030038100286000c80403641d010311308010701c44032441b840e80a18454065003040d002407044141c0d010f101119083c0d440a444030240700ca000e0380710070140151144d00b1180038500020034219110b5215080140e80340c0c1d02e401440c2c0660310404901804015010709101c2c0820844500542c000308030080e44074400790044c0003606075094004d4100c7c40700401180030311841c0070400801c100076615403101298941406a1640c40f11040302000704506081241c01640004d00b40082c468006025849100c0907a296001e40e903d03140119032 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 957683956 1250 957682706 957682711
    0x90b011106190507020a0212071a0307020615060403050a060b1306080c0f0a05060a030603050712050a030c06111305090a2309122719030f080705031b0d0206 69
    0x29414030800c0426142882d6007010341c109030b60b4030489041c1c68054001540d40c8058140d80303038003580403020400c410084081446500c00301101c8540c00c524060b4000794a0fa400100000392041c0000000c09540e580c02091340c020310b0b000001c0740e54001e21444c5c071000030049000c0351441941c6211046d600c8000d80d003c2c141c15101d40c44090711800d414141030200d40d200b0f00b1000c0d54400e640c13017400f04082d203d00c0e016140c008100c2d41d01050503880d504000d2b048c01e8641d0042520091480c10640c0403c0001582c030003140d40c50700c0c1c038003812039079400d1540c000c140064041d15a02400035041c0030080562002d1010b0392000ca500b43c082d51a11441681100c01c1030008c01102201c031040d100707100380c0c0115255402004581540c7c041c2d0601040c0010a900890420b03984003902031500d000c83c0f0395643c3d1410044000d0b105081001034201034000280c009120080c6144d807040103503000c01202109466103039601108894850083c5040303003540f42403e94410203140700303051315082c907075200050711030 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 957685206 1250 957683956 957683971
    0x11090a0303030b03011413060509011a09070201110d0b120c0a0509150301020d06261b0105040306090309051005030c040302060306011b030e1206010f15110106090b011106 75
    0x41440d00e0340e0341c298003604007240c00d580d05560b40d0610f880c0c466141030307206e44030384000f02004030740b03c4061402c0320440300c0c0a00b118040b40c2c074141c8092810860102620085e03041291221007954039407a00300d01504905d2444a100780c800300e00d502c03022665802104100701c080700c10300e0104e080c20803204da4a8002c0c00403140d000d501401c0400690a0004445810031b805072018103120b42094042400da03032020001e6070700303031780c2c2c3d10030411400a040400b803840408200314102a00441007c660356949000c10190021082541040c0340e17038016801c0724000c1d0740c081c8081c801d841841c10060010080ca100712802014040841c2c2c0613140700f1b80c03c0703d10544802c0b00850400e4290b8082c0242da0f0001094181031040f0000d00303c0030007a05a4155519030b00c260303524201070700400180304d100403095045003490340c8074100600040050f80949400d07204d1041c03442c4120807503020121410501c40b021030b0401e52070940045442c05a603000309603000420389820307124030213210f0205d0740c4000494260 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 957686456 1250 957685206 957685219
    0xf0b060307050a1416060c02010c08070806041418060f040305040909030e1305010807060c1a25110c1519200601080c03030304030836101109 62
    0xd100103004101400c1030f8001032602c8120501504020803540d80171010840f42000180905000c010340c902400c244500548000e004015101101801012000d0400d6060002510000b03022b501d40c0c0d03122150180c081c00a103d01c0382880c1c0f035002e0507031500e455648c4c082e003d040f00140800c0c3c0c21030701c40b43c003e40d8103643c0c0d5031510340317494103560041c030711b0781d0302101041610b6100e03a081d03036204c1050440b400c0c0c8402d0009078035490080307810301d400b4090303000c00180110042d003600840c6001022030110312100a845d607443e49e8011052071b03603100249200c142e0a1000410740301c4260b2040b400854241ca40b021501140d00310010006094149104008200c0040180c1c0a48544c0d5200c070850350701c02820500c020384805010a20150464082100180d0080b00100a01c080c104490103104c00182d000d1469401c05131001031224400900b0402c000c0014042c07800c4d0390079000c100c3e900001c6540e19940c0310ad08800354080e15004503070240503d85042095203500d079800401102c11150700204007 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 957687706 1250 957686456 957686461
    0xd06150203031b040b030103080c0c091012060b041803080c030615131a0a1220182706090f0a0905030408060a060e010f030b04081b070305030d0f0b0603 67
    0x40d599201c1c40303e80003881030f000c0c8000918141c9142c082c40c06544107030007c42e22520780181841c40e1401d4003e107030b4440c0d8055410303c00300d4501071301810196503159a42501e011031504004025200d020b00441d005403501c402d03502440040c180600980340710765076481040e216590f0b40d20320f0340825111a60301c48929044103040c0040340d401055640042c01c08808000d6454410340401c05a04000c1e480c070101c0025502c450a070701c041c0c8403203001c00e560340c10811800328840420941e10040810300f003d220000e050704500c031000754000c520100092001d44a50421084c515540b10b1190000c02c1d42c1d065003010408602d4848103852045d06000f84401041d9544076018014001da000165182e0004100c042031000c0c09212041c0700301c41030706011036000d02e40418040e81c1c020503802405410090a4184001a040503a03660001c1c0c004503156151481c4141e034002c015a25902d8040b9841810303000000c2081c0400a03010999a8036010400c00b940c01c0c1c1c881041d00c900c0401c0d180e020604100 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 957688956 1250 957687706 957687721
    0x80f101a03070c050604030f0f0504030c09050c070b0a090308060d02011e0c141c0207060c02010c080d0c0206010302130b030717070e010e0a0c0c0b070804111003020d0615020303 78
    0x40c60740140703245001c1d007500b00961201d45c1005020380d03050b4002060042501c80c01504101c000f1140b000340c2c50301502d02840e640b00c8100141036409569162510f49002c203010300c1c0c000c000d442c29240c100c80788200900b05210614000c4c00a501c04502048041000481514100f41c1120101ba010386480c802c560b40700c4180a0903c254000d03e000303109d00c42d0300c1080400c044070160001c0d20100300007003885480310100c091104514800c81421507000038028403a4541c800d81c45010740ea4282401c000451440ca401005800f44c500c0750b44501d4502038402c541a40d0025200341203a009443d002038105911407840140c4015400f00e54142c1e2000700700b0448115081d91000c10703501e01c001500c040302e484042d03409200000380d00c003c611170000018050b00011910445000c2100783c10b00340d21951403503541c101d0b451001007000050001c00000101406212084221901c40c001e00b100e541c030340072842c007500070b4001e4070701825400c1c6000008100e00029801d2800c03810003640096065a4130074a = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 957690206 1250 957688956 957689009
    0x3030e0d0f06051b0c0312010b190302091c050c041109150711030d1701050901060f230f0a0e03060f13210906030e0705010e01110a0210080f10 63
    0x1300310190110350090700310b2480f09008054140d09510801071079481004c004400500d40c01030304100c00d00b200806c20301c004900c00f10000c4611036200c2c280580c0b1a014200021841d113a100c41441e000c0f540d501d0324004000c80031884542c0010b0803502004940c0b1280c200704951701480c40b809400c550031444c0340d001000d00c08082c054151042c50340544540c0c00c03c0119061068040300680800c0582413140c00351058a80858003508065911710000e40c5050802444200c101d011035040c84000da07410142c00600400445800c94400005551403061520000003907000d5143d0500150403a1200060751070046105030041c3c445d501041044d440389503940410941c040d0301210703442410f400800c4903e6416110400d25241c680f9005c2c40c0c986803410103019111007400100352a0044c0c0c00920043c3c0c2c2086200270719040c01c0c40c01304001e5030101200741c500814040080d40c030841c840a00341d10741340d00c04101031041c48138103030403020b40e10307081400031040c11203001c1c030740c110020840f5100c00a002c55 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 957691456 1250 957690206 957690211
    0x7120b150d060b30100e1911031012110411041e060f08042301090501150311030f06040807320f07050108011e081603030e0d0f0605 58
    0x280750000c2d01650740c0810425580c055403915a00c0c408544205603180350030340c8801d4180360b001182c10458503041002030280400e9004400000086601244071010f42c0d484851040c40c010344104000304108070405500d070001c03103107420380e40ca00745404510000101440f03c445540580182c0e03050000800b04000303419040001480034005100001c0c03800d80c0070030090405d00c10899900080c41c140710005200000c0503000d0402c2c480508107010001f0000a903510600f03031400b9410f8a032081c918080c0b030140803030b40303400790540d030038a50b1aa00c1c40a00404a60440c0e100f5550846146000014140c9032038803540c0150071500500c00003030102d50518010308510384240c00400c52484100b4288200328040401510741c0100c0301c44241403600d0400c081d01a0b00e201800400d6158601000200311500c14000c0b2408030080c00c8004021750483c40d401c4000e80002c00984244810340c0b030800d5802152440154009562503d4500071030424440107407a060700820105080c0305580c40740c50150802 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 957692706 1250 957691456 957691477
    0x26160305010b030a0f0b07111c0221031501021006080f060604050106021b06040e0f04021504180b0414091c1706010e010e21151e04060b060a03020307120b15 69
    0x201d240010907400910270403900034000c1152078040a20510003d2034440382656030031030001c0e03059038500c1c100850710981b58400500c4114101604017040100c1c18144d4824141e000c4070704001c404100d092000c82c0d4440202c07020000c83e00c055442508002c1514828450700c0d025801c001c580c00406800d1020b142c14006018084515090f69144aa40803078000c540c080c2446440000384000c521b401007031042c0e071810006580741000e00b0030030180c09129003820340d100155621400c8040544490704990304050700d0004084061510880b8540c03544200303409880345014180711f0f07024090240008450a4408a110701c00540d2071100569641e130000b036546051210603040b041e65130307441c049560f082074910b0800700542c8400002c401c1c5800d01c03001e5004442411391040081440d402800206040400c1000b040d4644275401c0140041204545041d08200001079030000c2603095001540100301d01d035541400d080003a01d01b10200d8081200a6a0081007005c8610000010101800c4035140 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 957693956 1250 957692706 957692717
    0x1170f010b0d0212031e0414010309050601050f0a080a2405010e15010201290109060509030a060b060415441b0304110901061826160305010b030a0f0b07 67
    0x400c0c0d0241308003100041b207148101000090900160411000c8900218400c3c20701348102c040b80c2d60b410b0707180c0c07805025060190040030401c40a581d5030010000040040e0403d0328070b5011541006400c0d0300c2c20402c0781c0054446030a0035100741240340719840c12540f01501c0c42d0500d440c4c449140104d65511800d072411036403202082003c3c040a15500111300c1580705170b02c0300028131100054602c206941c03090701444030502c070914054402003212070a0980c400d10010351038900d10009040d40c0500d811a01c40d210003c01e001181c0c0f50000b519280340301d4804045881c0781302d0444a0541c840c96211070b0b50a41001038a542c900809034262a60001c030151000d0172289940082d01c02540c0003150150342c0d04009000460503030904040c01405401c003441c00c1ca0300c2445030311900300080f0311442101004180400081074807010a0103080c0448000400c0d60f1032011410803030030018031b0070f0005032201d51074940554098540001c09002996001001c0406030000341c6030a0a0210020000800d010 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 957695206 1250 957693956 957693967
    0x1050c07260303090c011b0c0e04050f03070501140a020304020d12090801090803060a09060b1e210a0b1c080705012307030b09070903020d0f080301170f010b0d021203 73
    0xd100344040c1d446038107204000c1c10900101170004080c5941c54503500c14040c0704003d8040402c001041c2502034450b500118000354035180341c00c5203042042140c882060101140403810000190401183d2142ca050308802c20382320b04070303504100c1c80241d80095000156610b01800180740042100e1080c109051011805540e60340c524207403801007204451491000040195502d810040c41c0003500044a0030814a4140140703070000c2c1c440c0d5001c07604541913801c5a808801440b034216510030080401c40001e00204801080d0901c0c4292030100c5002d05010f8058128280500031600000c0030000d00d03030348a0525141d00e143ca9000000071754003035480b114003841e501030240c00b2410a000c91b501c0714041d86000c04008086500303044151f880740018000380111503603c0032510080c0e94049581c41e20042e0307685040706510a204000900584000c0000501e08040b000c601c0c195021a41c1034992305450f0540c02802c076002c001c0f009511201001444000d8142454200304070540001244d2800 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 957696456 1250 957695206 957695279
    0x21e10050d0b0a0e363a0c0501020c0d0809100504030e040213090e0d02191112030904050403030e070b07020d12022103040201090501020c1305150d06050f0601050c07 73
    0x5600080b410307003156112407100280302002c0b05a01c46c46a5038984400d00d5104418650740c14845004181e00070001c2c983d5100c1c040c8079081d030444561005c0301085452545000f1800707894840221411105401003546041c0021010701801d4400c5500da61802858410f1204120080d00402c10714004032101070000300d2803c40ca03100b050601c2c500030004201c3c801c81c40000070315101c60701082d0b0666414a13001100010224185070700f64800c00c4501d10090340c511101180b45000b11080d03150b0181c201801d010070306070135170300c240e80c0e1480707203030913542d213a9140e02411006214010340250031802c8800b2060110306581e000c0c1254142c184140d505104040c0c02c031200320828801d20b47c0f05194000309000c00c541c2c000141c1c1000f44403c1c0040d05c0f00324410800030713010074000c4c0c0041144680320070001e60700e951400d0303050300d950400401546c5050f0791030600b00c0060000b103074800012520900407800343c1d0b00074001c1d01c2c001c4c07902200900d00c65040c083d10b00303612841d41252400c090410031000202 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 957697706 1250 957696456 957696541
    0x302121b0c10021e070804050f010c0515072c150403050703061a09091e0f0706180b1303060905030f04090c0e060c0307021e10050d0b0a0e 61
    0x190100701d030142e190000c02d40260f49503401318040d010074132020070182001030031050a0320308540d07044030000c200500080040c0e80385020316100400500170003149040034030050324210700540c0c296468980c14900903400c1409000f840308041c55030144070b040c18140c0d18000751869545071035103030103c2c10303e41d0703d548461810038250400c4440b140c0310a0900d801110003e08050001c0048503221483e041a07500141c441d62484080c4501403015000321004201c1044060030703440036582107850450741c0780001060180d0600341c80c5020100428006000c400c0b200645403a00b0300c003860302c6105071540d501e20004250a60085401380800c1c0300c00001c08190324064401801c10500118071303102162030003810f05054840c3d56101d0101404641e440600c000203132420a40e058924150740c901100c05400409a14048558007480440c0703c3c203000d5500c0000751440483c00b01c02841030310224030400c4028007450050b484a100c200c4000f66200b04c0d16916080828580326400443d140070740c40d034161 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 957698956 1250 957697706 957697723
    0x501110a0503160309150e010e0304061709060105060307260133080a1a040903030204080d0206040825020a030b22020d02091b0301080c100302121b0c 66
    0x218a002c0b08210303403800050104001401e580c0340400c10300c01c103a90b8410b0b0304200100b1ba020996a5280c00074408030003588070300e0704080340d5400c807522642d94003001041094620b6003403141c5010700011643c0c044c00041d20701d0581d42e000300503030704690b01e042084940300c4040c0715002402c5a4010a01c96103200702e04017034060602d606400030140302c0c581d62001d80e40050b80203501444480800c41000c2c681c00549103810a01c4180c02103039400c0c401101d070010041c1c0719038041d031180c54a40e000d010550180c4c010310481d44444255001c1c420200001e0b85c0b145012280517004602c1007200700141062411a2180c80b00700c211407680003001a0041041820315400c01c543c4448c2c40c106208008041000d402241601c3d082c070001d049029901060044010510007401640c0c1100810601a440392600e8980c803e00803240b0303100d60b50342141a03a20001120304030b008210006481c0440c9109008032003440106011030403141e281c045006006610340d00c0201c0c07801d182801200d80c1c04000340250003 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 957700206 1250 957698956 957698977
    0x408070e0603100908032403210913050121030e01181203020105070806060a0203090904051f0903031b021b03071701060504051602100c03061212080a0e1207050111 72
    0x2e840e450207040d0f03120521f1143c02c0d1034880c10741411242d4880c0d40c00240e44c440940707001c00740c1074001001007400c9490b0300403170a900354812800c01c110142180a980050b04942005296803010118180418000d540e003550140002d50344c0c0070160050b5024580000d101c981000340b030040f069540080d08201814a0001c40040c1d441d0400c1c007114980c0400c40d2a000101124a00d18109074a203001c0d55078400c4500b0240650314020002d424000c00b0f00a00100200350150340511140c40000803005106561046020910f8446038424522502c1600e880311b008640040401404581030442480c0741c0d942c03c6035252003180030101e4030480c660381c1182da0800f00d000102c0e0141c10704081006031038000700354620000d11071202c1c862490b40094144440800c4400c0042d0142d0078010440142009030000841208040315007002c002031912111200701e21035454a40c00d484e04943c0b47c060361000c4203088400c1d406804840c1e4442c3e492002005094031807000050062081c1811110f150003a03400403 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 957701456 1250 957700206 957700223
    0x5031611120d09300309050304050621010603060e040f0501110c03070212030f190507050307030c03080f24032d1011030703020d090204050a1a060408070e06031009 72
    0x15420000d4100030002800d004482013842e00c030750803400c812400410843c9a04050b100c05e644002e1150600445010b0f21010302240d9441d009181d02d001c040d140d5502503501907161400000c0e94511912400080d50b50521a401e02a103a90f00c8010003007030380c000140c071503560340d0321507040c0150100018038100c44c00e8400746403110b001d40100002241d91604204040e0000c10141c1030400e0076000b1122020018104800c03c0240c01508031614000d48200408a100008860007499080007500703140c94440d0707407410b510341c2e20300314088000c803001d940300d8081c1c44000407001c0b661264a0a050342101001c0d0440d074410100d40240040141541004410541d4441c0e00351a59501032004260b80fa20f50740050007245140f241203101ca2100500782e10415602280340305104810742c101031183c50b0010704c01d01072403e1010040c1d00408031641280c000c540b40b07181c1a4100d0030000b080e50100c43c41c1002400d90031346032551f55904c030800101001e80c0760042c510240079040552103942d039414002d2010 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 957702706 1250 957701456 957701471
    0x201020c0d110f0c130903140c0303192a02010209041104080f06160806121f060f0e01030609020d02120d030b010c0506071101020415020a0c0605031611120d 69
    0x480f81480c151424000072504054041946500d4000551419941c5010001030074015800e045406a140c84103d9540c22000165440c0381e040c00006540112182d07494900403250030b1072042c08448907022001c0000b10210342d9105600f0381485c01407080c0c05140005850404e9650005080351070034010095540700200e000e11200c141040010342c444c0111008140a04103034420b1480000611981020041103100141c035686414205102c0c41440104442ca122401426030410201c4501001c170400d19000001074240400b00c01a011512035150741003242e425902c44402030f10000d68123a03041600b44850380d00686848100303540e07060a071005005219242c82c401401c1c1d0360040d801c541044216010300d03021840c08070f0b9107134200403241007443c44000b000852902900440e4420310900b4060300105040a8003c11500740440c8107000c8402010786840060395a0301090b076040b03610391540d00111841760700036240c45c0d08a032220003c8a060001d01020b43e080c5a20400182070b00e10f440e40311 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 957703956 1250 957702706 957702737
    0x705090d03120e0105061e040f0908120708060d030305060d050a0302210306090c0c120d090c0e010f0608131704090e010917181005120a02130306020a0201020c0d 71
    0x1034210700c41c43c090007030002c0e003040d600045803074050088100300044800c01400041c6d40d980c2c401104000b0500040c00000640d040110b0f440d00005100880f42c4088400102c0081c03050f107000748140c0c001000301308016401d1301d080b4001c200090000ea000313204004c0c003c010440c20045410b8061084e802482402c0804016452801280c261070070782010500c06d005403580d030040304d15800b000d0340c0e00c05074550270120381841c9041000c0212080e030042c000307004c06200381d464001c080c80c503004240112503a80c0d54220001d40030824411240984a403003424443c082c8076041d07141c2c1100d1204a10702150740141c4035954210b091a08009500c40c0002e000c100030380b030b140290b000c9800300c2c000070040c240303d907103943c07213514070b201003000318140000b61a4280e0480e0002c0c01d0b10190024180f000d1104004901408580c891850441240503250026020009074000c80e0200d11f000c104c000380480c5543c2d1a240170f904048040801d5540a01444603a41d00801c10702d144000a6526403168094064 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 957705206 1250 957703956 957703961
    0x22140a15090f030806010c17040911030415110c07060519030b030a12030906050901091a091506130203070c02011101060b160204020f030901150e1e0705090d0312 71
    0xc061400c40d0510824002040544007219109501402c00311410fa0b00d0400403540994841402403001e010082d0120501c0c03c2c100252041c3e6801d15170800c4504603004010340d241c00308071030007400e201440708000c01e121015000344c1e09050200d0109800c4c0b0440c800600e040180c950804000140301180300090000e100c1540c01e13a080c16400c04000014140d000b00740c03034005d00703500600720030a501c0400807410700c01da00155480760001002c21803418a03294490103800018401e443d1541840f02e01c00c1101d140d13800340c50203600c40e08010041c44045200c14204048014007056020300200d13103414108031a400110301c104440d64400084017a540300141119040d030008050a1b0b01d809414041c03c0810b404071001040c0500a07100c40c0c1c451840041c019110340c3d61101c080d00e40110510401102c15007051039203031a402082001c050300c950076041c050b070302154030704120543c0c0000c68003080c1d15220456003100807454450f2a0050100114500705507401c2e00301d000868510720b0640b03005051 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 957706456 1250 957705206 957705233
    0xc07051807030b0a15030c180609260a062c06040c1a0405120a0501090c171203070f02010f0612020a08010c05091012050f15030a020922140a 62
    0x880d032007180e840c01c102045c000c0840541207038050603520000c14031030600802d05401d40075a000031200a69031540402407101c22035100300d066207500e08a10040403c1480c1040070b0703641c0c1240080130702c0070701a11080c1c0a4400c042c00d0500c180c2003d011203940e6111007070390300c039207502400007080c2608262614210102007940702001405034070709000340c03071003004040790203ca40843d150b400d01c0210703070155800e00525a50082c070a42c64200507404002d01100303048115400f1890409610413a03282c2d15449030103090b0603d018840c04c00004040c913010303454041036080d1600c00054a0b0041e05031260031908030f6044103ca8802d094410780c21440e06a51440140580a00910074290114806000c2c1d0040540861044005020000b4018440e400313502c041a042207060016042840c4994800300040d6850a085055000717280e00c24100050020099640907013040129612078a51321070a80441048065004100c0407000101302c4804004508145140140c108000139251044020292 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 957707706 1250 957706456 957706459
    0x1d1b0706051618090e03040b070c0501020d0306240e0d03020309210606010c02010c0602190306050d020d0605150406031109070f020c060a2706020607140706020c07051807030b 77
    0x4030703000c81104020a0f25904841300c9481c041040380c43c2d5404142140115000401c80c4007010981c02c040c44a5414024102c076002c1c0c0a0f103068425107036080742a24914040c044003081c40c1e1401d1090040321400700a2400803515088620451040003d405007038003503019001a4008107034207001d031506050350340072034a014240382041407407207610a0f00c07014024402c078180411800c1c18025640100c580008003580800215943d0500d136802c15a030034124090000001c0c500b8030003140b942049040c40c0f0709150010310420101656954071030203090005e2059416050b84e122281c81c1c1d0b210350080d43c001e144200700380105648441705008070b4100041c40603040040d19403802c8012900892890801082500d040b60758400a1070309a07420480d05100240640394940c0e0418404001901442540d00030360940e121601c41050403074404c9003004a14500341c00070406040090440e50041000842010590786c01e41e5541d8001100940001303419860540120300300811680c1c10320903030040c010b0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 957708956 1250 957707706 957707717
    0x207060c030f1a090a0212040b010311010809030313020604051c02040b040501060507060f0b180a0c09260c0301140103060f02031b0a03092f030102041d1b07060516 72
    0x40707604aa003c0b4940400e001801607007024007244e60180c480e0115081d60300c11030010411810700b8035244d41106030074071091b0b40c210541e200d410650362140070f41c01e0007414400021425074a8200c86682040340c1803034100d80c403400030040041c2a8841c4c40d8503a442925541c078044058403180140016a1600c010f020302ca64542401884010f402500f07403507010360000000103003c1420080100103100c3c442225920450004080c28000f4480581910036403564000380f0500e4080310058440d0105402101c203000c9075031500c0c0c4004010710182c0c0702e841990b141111600079804002c00d0031210b42030301b44400f965800006205100980c0240c001c1c0c012484801c614501c0d09152030540144051120b502404000030300c00300540c0300390007428400340c0110603800c40d00700c4103003000c01c4149980c0040f0801120103800301c1e0f03280340c10303c00d6600311010014038415004c03041d0220101c81c6c80c0180f5902c13203035848000d0101c43c20a0040940011803080c500000d150074030100b8150005140d2048104100 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 957710206 1250 957708956 957708971
    0x180e12070c06080c0d090602031f050121020f0c0d020d180909051f0510050f09010504020f0418060f230906040b13020a0f020d1e03020d0207060c030f 66
    0x2001c2440500c00c90b2100d28080e5030b503403030390fa0070900140700d10302c076107035000e0b04284548040c0304441d03006600400610640c841440340080c64031038600114404d00740451500002c04c8000a210242e0031001c40c1b0001d40107240c00c444520800b00c07074100f080036202c181d00a0f0f40003540140c041103055104042800c2061003810903010b0104100c001d4043c41007455207810783c4078100a420080c0c003181c42c008054140b45074070350148a40003000101e50600900c0005080020141020b0400102d0303000050f2080fa003036800c20342031002a5201c0e9150403480502000001880800e00389541007a17108a0404285a441c180c207802810701c11790084580060301c0d8940e10190780c0400841c0541c400141c40e1000507944010010700208000030340350303030000301140c0c023900c040d0300315402015060301c25115405026512403003203a5803a08000c101011820b40750501c4003000a51242002c0c05490345000351801103d80d222805903000502c003154502d4440300d1041d010364150040c84016117503948100640c0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 957711456 1250 957710206 957710213
    0xc1206030c031a0f220210021501090b060f0307180303120c051614160f05041a3a03170603030913051003230c0402070b06011107180e1207 61
    0x41c5029050010090017202d511141c0f0302138000c03815507039400601d0034002d5030200d40049d40311040310500729140012031001107803101c0c6900c6107943c400805400b440c01c00340081c600341c0882c1d1029044d40180900c0705082c0c480c8100e030b950060069882035807150803e014004141c4203649a0141c0305061000502c800c90a0b078500307841d541c4103550805101c07007c8000d460002400c0c984d880482080c610003140c00400d01c0185140100c048940075170f020004a803050440c044610070918889170f100da40160748200411a4000304462460205e540e04118481b0782081c5100105091045010421602c100c00300d413000e08030700c2980170600354042c502c0d29040c8800901e034078040e200d40e0004965208041007410781c0c42c140c8407003e568050403c14403c8e0289043d14800c112542100c01c2c2c80c46103520181c1f050406000f0b484031542d00161162041e1607030340041d2550780421050500502c25100300003500091a001d0300d05031070b00031000140c9201c06695a07400c0489910280750301034810032041000 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 957712706 1250 957711456 957711481
    0x20d050328060801150303180302220212310b1303030e16030254250908030307140705010f050a18050a0201030c1206030c031a 56
    0x800351400c1e8801c68403541c003040340000c01039030f00010015803810804407020002c4e21801816240240c8030aa10741c8031010b00d0428204460000a420064500b02103507544019200020240314040c000350800343c111030482c0100030202e5204481405201c0c0c4001480342244101c0d85180c1d09006681c0c400e182e6032903001d101100030b0103000d10764003680c0c4100c0074540f01e58400c3d40102408402c2e02d0703400f1030000792120850140c2c00164407403105c1840754800b502c201c00c82c1c5850307600e8668451801090410002c40010341d205507034080701c049050b20364500c0c0b50301d00102d885481c0708141d01502200465091300819092a03e200a01c294803106112855001081d0ba5104955280c14810600c920011305558010f0354002800e40d0300f040c0c03000d101d03891250803840c4101c0280a04200044a50046042403919100081c240c1c0e00149025009548a6000300c00d5518a80c1412011301001d03241440c121000b9034000d40762002848014401c1113034051900300022070083c16910541801f40746c6e43c00 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 957713956 1250 957712706 957712741
    0x30f05091509030409091101080c04080c06070c18090c0503010603081207020a0c030303050906280911060d0f06060509100c02010c0204110306040501080f030f1e0a0c03020d0503 78
    0x40351440c1c00000340780b0312410001c66024012480303040c0f00702401407811000d4804582185c60100e100900024007000d0940103440481d204140101644031008007408566480790b00c0c02e460443c190304001c03d140e000d10307184800d0307100d010100080c0501c25042130008402160825442030b410484100041600315040c0c1c0d803c01c400f41c1c0142c54a0b20340703030401e914280155030300510040811800100f810340641c04507201c1c441800598040f56100ca80b94002c404400d45a80006a4901c000169501241c5e10603450720340f10307041c000303620315040001510300e4000c810281581030315450016149052806428000d00c420b080060404050300005442e620780318800000b00402050720a00303581c899240410045d401810400416070f4000402e003aaa2003115410b004509040002917401c0b0001020b4041802d00c00c00f9501381410606040d180f54000400c90350100400b041d40081d00c80920010310340043d0540342c01200404910380030f03042030319103210941030003400e10421501e048032560709113 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 957715206 1250 957713956 957713983
    0x4170c0d08371d0a060f020d0c0c0c090b0a030b34030f05070e06030709090c080f09120d0b060c1b0108100e01050f0310150639020a170d030f0509 64
    0x419681c1e946c001e20090290791120000c00d8241a1f100c8041030300501e0300028203000302d4610302080d45800215080e81c4020500582200d4000c8080000c6407490041030307004560031050344204054075a82040c20b42c1d2111041c1c001e0b28040d5010150a03416108041d08100043d030f0510031450b10300f02c0034102d80d14122420780130b00e10000014108ac0d128140c050041c1400e940200425580f0031401805414116001d9108010100c0403e201c038000040c1c10714200e0120412914104c01040001d01030002881d5541d0442000c1c0003620600b40203101c02011013075290390517401c48404800040502e4005410082844880d10041c400c03040340307141c598103603281522503a0401c5604400b017450041c503411911101d602d81031080b900c4008140b4640300701e4042e80d50303414a601c11590703510903402c503002154003800c00201401c00304c180c42d404422601c3d8001030492941550326185084510007001c0713803800c076030095581e01e9200e94141c441c404980c1e120071000c0120b4503102035041e0707440c0c0441e81200c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 957716456 1250 957715206 957715211
    0xe0d061e1e090c0e1812090a0e13030c2409120518190b161703090c1c02041503031e0804020906010216090c08010b07030f0c020f03010c030504170c0d08371d0a06 71
    0x25024800b05001d440cdc10140542c1030b00d89140e030b00308a213400a0180d03403000c9034982d070752400513000c45101d0000d42d9042c841d040702075005e1851050401c0040485002d44400740d18143c900000d09005080c0038216103210414003022030101803800302c0b2511290802000d10440600034445543c50028003085211415100031801440d03105480c0c18400d11203030004d40c00360030311248000b903841d040102c4040f44e00c00d845404940c15110803002040c8015114200060100d100080c00341c038140d003005812240c180181e4070403c4030705104246001d90f0341c0102e0039840e1100300c03084840c2c0d40030a10900404581040c1820080b0a581c0108a2922008200c040091103145c1c082599196041c07400c030608000c000b04144030090002070040e09003150190f403101203a040c082d18034648c0000325043c94000c500501480c3e5990301080c1c620010141c004103603001c0300d901d400d2801c05014000c00200101c508100148920b100300d44082e501e03400134850104004100039405c4580004100350507a41c0003502 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 957717706 1250 957716456 957716477
    0x106051906051c060801090203121c051005030a03020a0b07090b0d0203090c0604150306050607080405090c0706050109060e06010f0e0d061e1e090c0e1812090a0e1303 73
    0xc1090100c00003483c81c1001d440c01c8800112400150b22050b8880e00c2035065544021400e2014021030290554501314540501691180c144255112992112203409c142e01c0e403e4a42021904e8488841400c901591180e810001032001c01c0502541c03102c070034500240d4080c01c083c51132116002c0c1c07e1011007415008004a00b4854040c000114801d002410300394171581e58000d858140c4004500d510007280c94440c0c01f107003900f850310849243c5508800c40e83d00d030610300717014484100c20050422604907410302174030002a110307003d031600030f00003500f0124026003404426070342c2a1000d00740c1414440301c05142081d0740d800405910358000210f40302050307509a801c100d006000590700071802524080913801000226500174a030300304405601041d141540388800c030894011031f4002c0c204040301041084000040e0903a140d2050304402560080c1d1003107108640340411842c045080b14001260344040d6040202201d00103100304100400a403c08200540645410100c060204481c5000 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 957718956 1250 957717706 957717727
    0xc0d0302010e1204090c0e0d0b1b040902091216030b0c0705100e010617031c0204150305041e02012f0304120c0b090906090a0f091103010605190605 65
    0x303160b0003503030001078a1041180c032a07060b980741c0c0140070740c0010902c0d00d0040b05995118003610041744002074a1b41000301d8130b80e1203503504510010b0001c010890780c41e1403541c4201005014100501c9400c401588401c20b500c2004800c407183c0b040f82041d0b0303000603011441000781046202c2101e070411041900c0751100d00490110f0b120b510307005400c910407409100f01c161065840000c40400341c1c1f00820a903500c800203054085076500407a16182d04c00d03c030780c013129000c401507025a000300c1a40103150650301d02c015001c1c04003805554010969800c1044280201d41402000600b03003920840005041580041d11a14080ac0100c11001020200e4040c14541e02110304070101e00a04032525281d4541c1082e82004a100003143c000c00c1180c00014030601c1c040546821040050100d136596450809001901c00300910086540303407a000710348400c035900c0c400e0f00000d0303005481c5204419100414582520400d6000c0ca000f04400140313036906074083c10145040e154545000c90f03807404102c1 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 957720206 1250 957718956 957718961
    0xe0c09091503030c0c040509030405031b0316080a1104020412060518010501030b04050d05180103021305090c13050324090f0105161808070501030b030703120503011e03050c0d030201 80
    0x1034490742c01d807100040c94803242c82c000030601d070114000c40d0180842e5179210045c1e038032806280f25483d0075901c40d07030380d06d816000301580806103214050100d4143c14844580c800c0091299885000c450b04188904800d1001c410461125100c1c1680d0661810f480c10b1050b00682e0b071a2a405070056540e107002c9201c41c3d48188003a080c0700900c0c8002c1c030003540c5a040220340d440702605e04844a104140680c00d01c40e010300160f0b80e0049003072019510400140d8010b4020b94003225848484908100380401c040d99080c0c1210302503d07141005940f150903c040e514100901e0ba000a4480d81c490042e030b00b03210b990f240b0303050305020b2188980200c0c0c1d2100d190701ea103000101c0c80000d80750b500b08001c01200c01d4041204039498581e950f02e0307149552100d1203448041c4c41d01e010786040381d000a45d041c0015400303908420749a01c17000c1e0813901d0842c1e403600d13082e26000f424400140003c01c000010880100c1c02c0184400380c00a5010002100f8507590b10950740314051b038050350003151034102d01c005250003035 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 957721456 1250 957720206 957720241
    0x180d120c0c060509030c06091606080c0c10020d0605040624050705010608010c080705090f28080105040201091a040e190e010506100f0507061104050d0302160e0c0909 73
    0x5001440581414004152070350482e1960201d0741c400ca400023400c020380026081d101000b0304043c4c6115134100b40e800c880c6960018030905a8403410845c1c403150003410040300c41c1c90f2442c2e0300f0040e11010400b40e8842510140d81c4007610840c100b80d802c0c0310030542001c4103081c0c6c1c00e00b042040d600b4200d0720810b6405014001010304135510b4010006505001904084a0340040741e8808075941e0300c80205035072a0240d000499008040784401c0403c40c244035012216801c01d14813030400030035807114003c08035040d6800c440500d0351a6428802196008031200c00942014061101c40c040303030140c0c0a50a000c0e500c28424600001e07404280031b085c1c60084100051074182003884089602d08207a40078243c2030320b6450045d007004001c401014420035141041d0819035031801e02d00300042c1c460001810000c0c2403030044e00300030000010039503036020841c078980707210750041c1000813641e081e00716100304250b0099074100b0000042001000c0c08000b01c41e007180d0b080303c000c0491b0b00e610718503050682c1e03c03 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 957722706 1250 957721456 957721463
    0x10f05010f052101060b0a0503040c05010c1e0201021f090212010621020105120901140105030c010909050a0b100f0f03020316030c030603061d0c0d11060d15060305180d120c0c 77
    0x48681039541c0c00230007903200d14042c88010a0035551071004407019006180060a5901030162550500e224010080b2002d4014812506495802c06511051140310146104502d1b0749070214011030409001c85401001d492000700044ca180c41803844030110146486130002c0404403110045a01800035940d4007244440802c4242c640b03059a40c0c02414840300b42d00c110188400001502e103800109240f04000603580c618005107040c3d100c034090f1201600c41c625590311502c440c803564550440071604188541d6900345042c0180340e029200300d4402d4860020180100b081103c103400c41c000fa450041050319000406401c01c08048006005a400040c0414100f0125000d40801c00003200484400c40d13081d55000840c41c07003040002c200c9200c0080041c20150580c00c024a04000a002d00006180d0041403950110030008018103441c0c0003040403030340c2d0f1014008082c86019032004030903c800001c1050314951500a400c1200c42c0c0c102c0000c240d142d00c4e1a11001d0303c11076885401c580d2 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 957723956 1250 957722706 957722729
    0x1050f21121c050a0b0609190503300c151806011401020d170a021312050604031b11040c0210110d0b030d050d0c090305030705010f05010f05210106 65
    0x21125040c82c40100d01401c4005410040460040300d1148540010078070010b00e100c0c0307841001401c1c018100444150344c0006035200c180050262000d11058000c800c17826241349004811546130750340d1125229000e840c0e80c03401d0000115881c40010b10310030001d8540b02c0840076a4607103188032101402c625074000c0c0c07402140000a03400780390b61a01e24980e0026002d6550a50b01d031001210807614030710006d41d41c03440f0000400d50b10801580100344040020304c42ea0005074440d41440c1207200b58036001c90b004e5000e4401c000070301d030b401968440d10315429600895004201d46800c0400240e8210440c421680d8000c141c8825008101c41495282e4071a807c0c003401d00d8034850300200790811100c0101132420b10601100b6850082045500841c40c1e03200c0e0348c188607540ca02e50b001082c08008003018000c0c041400f20120340208044d0805501c28000031401e1803100d9100d20a95106a021001550350320009110650712511600c88003001d9004401070501204201e9000d4010b81d40003a68940 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 957725206 1250 957723956 957723967
    0x11060315032512030905150c03040e07030f110a080c04171c1110020f131403010c0206090a0605040215040b070b1f0b090d1b050901050f2112 62
    0x4040501d6441150000d41d4001d82c0d5140c1143c079a80e24020b8005000494807042400340345004960f10001049100c4640e0415031401056840d690103504100b44000c0034a0812500030b9050090040e002c088001c1403040b461603588010040c0218030040c4107100074080098000c00d40d05054a00070008020543d04040341c0c08880c948441c00812482d103007020a1030709074a010b004485020f0030b208035000401240042120f81d000a401045400e8500700c4100700c1244e0343c0d9803000a410260039280114060070001700c042508503040c1000c142c0c11340d08140c0400182c542d000c01c200400c15009070000c2040da8031072000440007521000000800354000c00c02051a0241c54081c1c034401d03100d807003152103c1d02c403000145131500c0303410b00c00250f105121409001028052000e842c0700c0001404c50200007003e42d468a0307941068000c0c019100c2c0411070301300000c1c542207900c1801001c090b02c00c440c030701540001088180c40c1d164504101c0b0364503485001142a02046800ea00388840b0310f000303440c1d6 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 957726456 1250 957725206 957725233
    0x40b27090a0204210b010b1b010f0c20030315130e0607080109200c0c121c0302040e1308361804030807051e040602191106031503 57
    0x83d005401403a0306026502040f07000044d01c42d5000740d2103a008400240168604051030015a009055111040749513100502081c80c2c00d0050340c40b48402450003142c01d101e40c0e40300a200283d0240440d10580440070101003260020013100d0300300c1c0004d41e800c900c26378030402045206a1403140309050920b0120004001100419818000c80c0c0960300d40c1c0c0e0a0360307110700d00c10603a01c202c6541808010249120040c500e804001406030000070019149002804d000191201c060303844c1b210101d40240300b04290403890201d40c256011098101141024141110309050b404001c0c400c4002c08181c0117030b07030103012103a42995441814640281400704000c41a41404101c101c1441031541e2500300316403181c50030f0b0038100010b0000e071407005d03d16512500c048550708000780c0000309105007081114511201c1410340c100d02d18085002940c0d482c030341140240b810040c0341c00002001e2110501c4030001d00f515024a0000c01c0407581c0070f840e9254580f06098015401c911103a044c4140c2c005410b40 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 957727706 1250 957726456 957726461
    0x90c080303040c05030d090605070609060e160f0b030103020d050a02031e011b020c010c0c1d19020901051806090a03051609051905091002071406010803040b27090a 72
    0x6070f00c582030210f0841d07503600c00d00d40d6481a40c0b6102d00800d0a95109020203407051000c0c1c410240240e501160841240e00c40f8412500c00141003131068004044851605816101010050607061100311110385000c2c071000f89400180002480b9902c0a030b0b1100602c0001c01201c1c4001d50001e05941090b141800c1d60511011416011041542000c034030411143d1010480124030f00d46170085e04c9510201401100c00e01d0b4150001c44480611381000b203049903501c0d91441c400b050406804e102c0d401c00e0b1081255020400412014490041059500c1640e00400340d5031045e08800c08030b01101411000180b40d0300880e0701c15a004420814004240703d00083c000052210341501d41303e0b950380b215101820340300100c850003811a001d10305400c2c020000e03400140c0c854070b4101524008130044800b81c6c01da0307011007003d5480c8540280c0d03a40d8000c4091045038010406140107603c0c00e450404218907901460b0800b100c5000079035442c600b820004c1c1e070308482c84140144082c0a515200c02e48500 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 957728956 1250 957727706 957727711
    0xc0406110705010c141e030c0f0c0f0111010f023103170702041b050903060c03010305070605250803090c040612021c0803070e0906030d0801090f090c080303 69
    0x190002034208194640450040295801030756000345505003501d400419410185400600d4131a00400f07907008003030008080c0c0d00400c540e0103950744014225185d460172501044004441d0040300c0603c1d619902c1d0f0740709544500f005c2c20400540050041d032180180810440015010300000d0303c601c011000d1014281d002e5001c144030082e00002000110301300030f95000040c080712541d881c012609641d0409008003920090020410a40e5100e5131114210b0604803080403c1001c1402c028a00e0144981a03203c95503c1a40c1c2c107640c910307241e50342c0c0c8080511440e01800130004002180d0184540c0080e10b030440040d010142422038030700740840754004c951010a6000b0181005038520713284c081c01c3e0440346540401c0c070500038680c003005810800356000c6007814104000d0500000c04002c043d40c481c4c902a180e00008522030340c18401004801442c5500ca6081014559095034111220505550300c0b401c0020300d0344241d030102c2004145481000e400f80300b924000041c1d1510010040d0f1 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 957730206 1250 957728956 957728969
    0x24060c020109090b22060902040311040e03030c0313020a1d07080a06031110090e1609090209062a01020d0624080f13080c010b0306070e010f080a020c03030c04 70
    0x4145550381141e0b0708071008000d80c154400f25100c2c174210074102890700e5012040c800a00000c083c1c3c0d50b210910100c1e441070340100c1d41c03089d10304000c1d005441c1901c01c0008044071080514a5403600000c600110b00c001000c860b0601d0000c1c102c070007035403102648500500b80194000c070031210003030180c0204001c100c41060000381e5040c00503112013201e01842c02126401480d8030610b046250800100c0c841000b003540070040410000903003521030380785003402120f030689140700041050800411940e45900100c00880c01044414410349031002120b00c003440080880003800c4031074913412811910200c0c00c102035030000c54a00018221a03004004440419000c0c3c1d0180c0c5403944442030750f00b241c0354a140490300790030019a5014002c00601c0d8008240701d1600050a0b440e510b420071a0061130508105a41d6802e00301c413036040801c0b0046c0c00840302c4c01e00340030300c281c0070000034900404891084100030ba0440460f10103241501500c45240000d0252500d07813520809244541c4c000d8890345 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 957731456 1250 957730206 957730217
    0x15040501021801030c0504030b091c1106010e01050105040b07150e0f07050a0e01030b070e130c03050f22060e03070f050709050103031e0e122406030c0424060c0201 72
    0x25190360081c440c805c03141d491903c0c1c1d2410140785032625400c0090007045001180074405c0d500c04041c0e045958030708034901d036885810750300c904426882d18010050300301c0400c0c011554014003950380c0010030f403000c070b6106045103540c8030340d98505050103104003950313008210b003090340740e4658401c04581c124100c01a0780840302c68958400420104040d20701c580c08010101c20300520120304940ca4080d80161a8100003601e01042d05c0894030800030012402e0080f03543e00c114000c0035078503009054204200441c02d29680c00d010b18102d40c10002035481162003087d6640c4403040008903040740103000030200a60707849410f2410292500041d524085980f80030303110000c5410235052203124141d0f40c259480c008038003050a034041d811641b0050400c203119404030040380907981c1d054107451300d0342202e0180c011030042d00185000d1145025804021109450400045440c00500f403080900111004240809011002c5e580c500d1500720110407003460880103e0420340021245406e0707803003a03942 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 957732706 1250 957731456 957731497
    0x50c210d080421090b0d0501170c0f010e0a0b030405010b040b09040308060108041a0405010b1302210a0207050313050310020424120f0e0d0f09060c051504050102 71
    0x1c5035902401c442c010202942d124041d96411412031000191000a05169480a498101400f120303003180c01c0444004d911100140240300d811021145802c1405000b0704007000350318001000842d0b0300c080342e4104075403440e05089640e103004450000741035035941c0d1030741c2c0d09141c14418040c0041c2148540124140f1401ccd1500e410f1032641c0c244038179011f655502c00e0b41c560700d0046914440140064a030310a40310a14100d0841c2c4103610781c00382d44500300010310400c00c0400d1150382040c0e4001c00495510502002c5e4151715200b4100140380701c010041c1104e40e544540741c10090041c2c142c050b020f403001041c46100b090103030403240c0c190340040b41110489690809204181d20450141d42c0b03103032852045481081d075441d801e002c0a07900b141007400d44490004100007c03500080f03d4007117640e403590481c01d1102c00130700c03510995262903d03003541c60013101074001c1c00c1d01784644160700400c2940000701060000912098483e03031602815003909041a0a00c68041d4004ca04645428002000c4 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 957733812 1106 957732706 957732733
    0xb09120a0803160e370815091e06040c05041e0902010309080c1e01020414090c040306050406020406081e0703090204090b04050313080c03060c07050c21 67
    0x1c5c440b00101c402100449041003c91520086106000c0621000f0303000f18109080e460350740c4034480301c2d407291210103281c0444140750034040101205420707001000803d4050145021b03150080c2c3c3c5680b41c00c20401201c41903404020800441e4491052840054000f012018014140040e200d1100c0d190b42c10541d01152074107290b50840d0945040c3d515141c403070100d80034280f10085003843d0504005000b083c0404061a00c5802410009a0103026820031100a51340c400014407003810b140c03030603101a40041c003502c4003203003104000a0384030321b02d0921210b0508040300c008026485841003900109422002031b604151210a40b00204006908450180b4400d01c01951b90751000c00a8021103000350700805e4941e00300e40704511680d9800505640c124400b9081d00381d50382c80f40c1c40d00078680840844402d401c41e0f401c00c1d4810b0340c0294484065003200c0000250b402c1d0700d0f0f0011 = true := by decide +kernel

theorem cover : BRFrame.Cov 957553956 957733812 := by
  have h0 := BRFrame.cov_init 957553956
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957553956 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957553956 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957553956 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957553956 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957553956 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957553956 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957553956 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957553956 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957553956 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957553956 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957553956 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957553956 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957553956 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957553956 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957553956 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957553956 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957553956 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957553956 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957553956 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957553956 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957553956 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957553956 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957553956 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957553956 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957553956 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957553956 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957553956 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957553956 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957553956 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957553956 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957553956 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957553956 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957553956 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957553956 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957553956 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957553956 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957553956 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957553956 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957553956 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957553956 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957553956 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957553956 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957553956 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957553956 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957553956 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957553956 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957553956 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957553956 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957553956 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957553956 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957553956 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957553956 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957553956 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957553956 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957553956 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957553956 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957553956 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957553956 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957553956 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957553956 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957553956 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957553956 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957553956 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957553956 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957553956 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957553956 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957553956 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957553956 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957553956 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957553956 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957553956 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957553956 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957553956 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957553956 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957553956 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957553956 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957553956 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957553956 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957553956 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957553956 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957553956 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957553956 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957553956 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957553956 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957553956 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957553956 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957553956 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957553956 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957553956 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957553956 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957553956 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957553956 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957553956 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957553956 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957553956 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957553956 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957553956 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957553956 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957553956 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957553956 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957553956 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957553956 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957553956 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957553956 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957553956 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957553956 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957553956 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957553956 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957553956 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957553956 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957553956 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957553956 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957553956 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957553956 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957553956 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957553956 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957553956 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957553956 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957553956 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957553956 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957553956 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957553956 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957553956 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957553956 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957553956 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957553956 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957553956 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957553956 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957553956 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957553956 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957553956 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957553956 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957553956 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957553956 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957553956 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957553956 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957553956 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957553956 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957553956 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957553956 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957553956 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957553956 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957553956 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957553956 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 957553956 ≤ n) (h2 : n < 957733812) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
