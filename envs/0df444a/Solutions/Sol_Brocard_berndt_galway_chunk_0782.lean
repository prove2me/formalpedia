-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0782
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T22:45:10.628681+00:00
-- url     : https://prove2.me/submissions/59c55a62-0693-411d-808e-3666b70f6635

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 140467625 ≤ n < 140647482 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 140468875 1250 140467625 140467637
    0x60108010509070c0203070b0c15070c080d050402130e03040801140c04050108091c030b0f01020f071404060f12061503030f0c0c08030c1006050a0602120705150903030723070f03 78
    0x72048c4851142d04280022017043d4440e0800b040000d01c0281318540042c180e061080c0900c4c05904c1d421a51700c102001a00300540342d502240844d01d40122034100c1c240035500800c18001328100d0340e40c40748e1003445086065800c0441880c842e051900c441c500940280419501d03007840c1c9001500e1070000242044501e000d101540240032a180c6010501003070540d40000381a0005001c000c0c40780d003114030701303811544214403d00d4501c1001407840700381d681404810301c10f1103001c00018081d003c6034004107054181d40b0000140140401d44400401d40300c0c400500c403080c0212040c2002c46000e02c0003400203120383c00c0c0588282d02a80321307020898004c03051060300c0d0361102a000d2550744910094001980286032071051400d8600ca000047d0904490454000b41780440c003c0d075504034007000c2d00c01c000c0006242e90401504002012903044104185541c5151002185031680c04c1100c41102240d411045420a0460000d01e41030f18040c54810605240c02d86d141e03101c000804020880c28425 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 140470125 1250 140468875 140468879
    0x130b01031112010602060c1c0e0c03010e0f0613150207080d020c06040c0b0c03040506090d060603030f03050f07050343031506020606270705070506060108010509070c020307 76
    0x41100080261001195142e840ba502d03003400240382000080c058a1103107414071000b0103c100d400c1c42031030104824040419038401401150307003402c40c04c0c000660703d58648803010f108164041900c0c00071001c1c040c1501c0d480c1d43e40c0205c4c0340403200c03101001800f940b659007071104441d109074064190b00d03014003011030074841a000084102d80c001080c0d4806907001c503040200300480300400b0009412020010303800d00135540c015558a0145014551040e24082004030168481081d43d40000740c03c4042401010303903a08001d000c59010b00d0040c000a801c1400180e5401e110b01c81290040440390b0f1842e18560f9072003410481014003280e6107410000f0030301c0c0c004800501c0f251300b0528101c000f002d514030706501c40c006401c0381e03c95203100200c00448041003103091b8011075100c0d44548242c0d0706400c8007501228420980000c80080c1280e031003007406003c40300f45d2020140c10158440d0040700c60a850b0900192403402091150941c490290400144800e100e80100740d0301a202400304c54001d5 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 140471375 1250 140470125 140470151
    0x60c0a06090803010905090f0601090b0f04060e09060702010204030f030c020d02030d0306050310091a090f0607030f14190f020405030609060402030c15040608070e0d030c0506070509130b0103 84
    0x5078200c4030507a41100048018000050903101b016000f02c0f400000b08841800c1c9081c25403200340501c2204d070665542c030202102d0761200c5449190b40c00b80200208481511360b04020b68025044c2d943c869a44129000102c41d1401442141c00741d0b50001100c800c04422a42c048462041d0540d0890300314200a0303092005803000c11541001c40b0103510b001c2440c5040c07000303052910119282c1c0d4800c1c0d5040078000c0300031907603d096540554058070081645555a0300031070345800e560030005440ba120f4034003004082c0303a16a0110000540380c1c84e05202c2c0702c41203040481c41d207005951455002140040010a01d82030f580b0107150100c1c0d0745005400e243e5220700003030072308500300c0d00680d240d0400c200b00001c5140502000e030b8040c0044134150104001c0000d03604c0c20b806540905002d108040021a005c5800740e00300302041b50000b00000360080040c80c00419500300e21100721501d1081c039010030300150060042c0d43c0042405085000c0b080410b980c0140034000080e03105050655403540c920fa98 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 140472625 1250 140471375 140471381
    0x3061b3b0d080d06030506061801030f020303120405060105030706030624030e0d210204080d0c06060e070203120c04120f020d0501020301060903140c13050702070e070f09140609060c0a06 82
    0x1100810f00f0026039a0710f542086410880b00400a80c030844140d007042c0300d01031420300c0d1203042d290480d501c5005188a4408a451403050102064854504400300720030081b000588070305a680a80a0310809a52131400b40c003643c02d180929003140040c80c12030360209003141c2560b00000e62070700d070101d0444510f4440030b0800540000d0040000c603103a030751100c0d90f001d01401c500e144692040451600340b4240d80c450f02d4144040c0540c0030441c1ea41c44140a03c03078650000e40191545410202160a014101075035075884882e6080034051280005500b4031109000e403002c03580b0303441c050503100003c0e54446001ca40f00403001c0342d0204a804500d008150f003403003d140641065111144a18118100f207501c05a060000d907001703902c203004105180c0c4a000e401ca00305035442c00045000d071203020080e4100324880d0015a64400c3c5c1c9803c000c03910381e00034440142c420954440c05080ba4403290b1032050345420010880d0800c0341041030185904101000748183d10130903007a54220020b540e01c21040d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 140473875 1250 140472625 140472637
    0x70c03021c030c1e050702060a11030d0c0206060906031902040e010c031e020301061205060f030d080a060905041a10150203041701051b030604020403061b3b0d08 71
    0x1c1c0e941d100c48a94250012215002000c0610041101c010315803130061042c4210700000380908400701d001e01d0114050822400e9100070300c01a207403a040c4440400f0000c010741c0c1c552000500c07a12012420500340b60004601441e005005800e13050380ac4040c8441490744000100e070003d541320000c0d0708070030007885141c0030114603503008a0144e40c0304644100018010070f001062910410040100a0b080303651a4512012444c0100b402d644503800641e0b034218000c00660940036903010f004060380d20503140391140b00518010000301d9200c5042d0740845100f01e90040100b40703605a1204250b800305519903000d203880342c4034016140c5030050910717181c00000102d805a80041014030080a001c0d00c40341204201100802c11460004031b50014050000d48148001c0d00000214110f91103d4040340c02640d0000024422a200f002d8a00c0c04034803101c0c000c200190152005e07841c11010f0350445141d035520901541d4960700540508040b2019420351550f0000308400f03a071000400e0b160203000 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 140475125 1250 140473875 140473877
    0x110702030115080c0303190c150f0b040509010b03060a0b0303130e0702070b0307020604060c09091103010302030c0405061302032212030509030a02070603050606070b01030f05070617070c03021c 85
    0x40c240c6800c0b441850004e0100c01030b4403e4000303000001081c010200b03881110f4a803072810070301660f010b050022032162071460040a107402c101e03414003090b0340da4100f038000d003900340c40070071860b5074400c035050899100e6844541d050b000a4046907800d0b40a800090491200034180c07442c00454002d6106191a2980711031801c10400040000c825018071400008209121101d440c51606000081d100ca46c001d1005190710754400b89585102d1050100c038000d810a5141001210011400742e015074100344801ca00c24400c08542d8591400e090280c42e008410241c51101d82550200008029410042000c50346002d0207401e580301100400200c010540130306c10718402d40504280040c10b4603402820200981c1c4204041c448455000421400715600b9250010f8030351140e40005d92030703100c0c921001d410000000008820700041c40001102144144111031019030f030780c101907a0343c00c0200112607141c1c4140d030002da0180d001d49561a00c840c4a40305071445910881c000e800484040f4107448 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 140476375 1250 140475125 140475161
    0xb030604180507090c0f0f1110050702011e0b030a08030405030904060e040605100302060a050f12010915080c0108010509191a03160b0d0209060c070b070303060b13091107020301 78
    0x10882c0f800c0c4c843c220b100d44071850410810300250034064207000c402e91341f910801034400e1504900c41828485082c40040350603050226040018008ac081c2c05402d400300100400883d008070030300c000348954600864040c000d041c0c0400b40c0d844005048d04028401e403a24042008003881f03d40c0c6034410034000e0011540543c00b01d007414205041111401007003180041988401400035a4400069070200c210a2030308030b41d110445e114580c03035402400d0b200c480f0001814008142c0b22066000410044070307400030042c815648020140e6281400c0c072106001c140c000d40180064140337044910fa00c40100c1d0035008a8580e4915100c00711911003190000040c020380203020145403d0001200c8042c400308030400030390400c0c4000c0400d10542200c2e503400381d4009000740164030303148140d82a1101c81d40988003050ba0300e45800940b40e100c0e100071000640b41031b0f0040380001e82c400540b01c0310b84082200b41d0f40c15090190f040000d004165142c4101e44051000c3c5005940034001d500303400c07544040741 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 140477625 1250 140476375 140476379
    0x40309031401020702090408090604120c03050d0503010f090b0103110a0e040506060406020c06030a0914030408010b1c11062502090a0e0d0318020409050c1003150b030604180507 78
    0x100d80080100c0d03a001200b079004004c0c00000d6510f2040d0140c000e82c10205841e0394100c20710029420341b149600000380b04004802100c2880031030a403440c101c034010015200f06400f030407000c50b0a803200340900c1c41101011001031040d804194011088550113040014030041004420640c80d08803280d0103000827842036101600c1d05260042d00c2c0c00c82e405482d2503040504003000030352035100f100146400340c00c022000910701c030400e07001000c6003500303c03002042032110035001940f40d5119000c1c88101c1d6003000110010f03418003001481401c0b901c4407540000c409599540c0c20b40382d801084031903100340d00713003d5040703070289400c1100e0924141c0a8a81145900c2d40f05101d94000c000300040740c05880c0c060020110f008c081003409203400349140014501001540c075824484855a002c0e40007403905071400200300c2d002401030f00d001002ca0341c11110310101c102c2207060312201d041070700c1110b03090b02c010410aa04800a1340d0403501c000d002140d20100c2c0314151081d072101450541300d40d4403030141 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 140478875 1250 140477625 140477633
    0x306030708010b0a06180504060e0a050603061302130609020408030406081506092e26040804060f02010b150901140f090904030509040912091e09050903040e04030903 73
    0x3001000345800900400d02480006a6541c03000d208100a000440441c120f13540540e41620001c0c1c00014810880d19480350041002c514045400d030b20414508400708e103c40c900000c0240c0300340d550300780c0104100c6140c2e003404001c000c569100c590181d00c5500110700d2541074005400685405001142c41b14034001000301a2440a03004550420081b0340100690329094101c40441c501a9003420444521a40c0d11010f480416003009044038500112484d42e44c2c0145144a0201c1044660b10200a206200c0c40003003025580141000300070841000880c2c00307a40703e108030003400c0c00001005a42000400d03840302980d05641c10b54400003880d4006507030440040040c600e200c000742810f05104c5100c41c0b0a130321945c000f440c4a40d00b00d200003002c0502c16403c840000788054000d00a0030101c0c500802031a0681c2010f4000c10300502d404515038000c80301c1340c85169490000500c110340b600c0c28030002031101038250405400300304400f280c0f240d140740e20540030320f12076a1449802071035418 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 140480125 1250 140478875 140478883
    0xa0e0306070e030d03050f06010507020324180d020c210307080406170c12040c051908010609020a1707200313090902010c0b0709080706050c0606060304020307031203060e0c030603 79
    0x200c1300042c98030b003d0611990420000c0a9940100203003440e41d039820042c00000d1400b01c451614801d11484013000c1c4240d0558810300320300a9800f907900100081d5a82145502c1c1c010403011400103038070241d400480ea16101203602000c4d08118154403100038034020700f50a652001100f81d5200000040401000350b0010ba8622081041e841c420702600b01480c2c45001ca205d02c90203c1809000031000c2000d201c0c402030701800a100041800704d10081d41c200e00c01c01d160091151440e554a440b2000900307900c1e5008640703a01940399104110242c00101300c403240003000c1c0585042003403448042103480c0203000d6056441c00700000958403007003d041d44115011140c1c105001e5682048141c00040c1d80200c483d409150340161501c0072961128022a00d82035564020a01c92003003a400080d0190040006d110648024080d92400e0b510081840824402900c0080d0142d1085c401000410f0842805c41d00004d0039140c041481070381c03880100c3c0440c00580d56810300fa00300000340700261030100 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 140481375 1250 140480125 140480143
    0x1704020d110d23010b0604090c02010b0607030e120105070c0b0c0f070c0f3201030b0a0609030204050f01080a140a1b080f0109120e01021e0105041719050a0e0306070e03 74
    0x40003403103120a200046806e9004600c1208000c5807555640ca55050003900b0154052402800c0c1d9900d400300e41c1001000201c4440301d1034010308014802c840442010302496202d41107549580750320507001e9694880003100180803c102c88000d00107100c08440100051004501071003103409440d040000c54124606150b2107007614182c5100d1069860800c101140c6005028518182490040303400590150400c1e203191644080c001f90089066500503912806036030007984c0410a44e0799030ba0924440460a000f80c000365400305901c000040c007480c28400242424a00395a010801a6255200e903c1198003104c20158601802e1082c40c10402c9071103c10140c8a0091003203107543d880d070049450040c0804030030040625004402c590080000e14028805240b170841d40356206a1410300914040d074044846821260140803c2087c8400360303144070089403401d22400148500983d4664801c2900805200c0f01c2040c03c041641c06005261190030684c66184002001c0003c16080a5000c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 140482625 1250 140481375 140481443
    0x10e0907080a021507060b03070608011a03060303090607030507060905030304061a0d0209090a02121612080d0c0e042d060e19020f0c0703020f011704020d110d 70
    0x114014805030f0b13035900841d0040188507128541c1c0b0107113828104082d00d0008902c80d0507125028001421651000c20346048076030b02460301c0310305100382c101e4041030300c421b45581e94076078014001d0180b24075240c0001d00c502803003410068684580350781c1b50400d640c1440c100355600d0f040403040000b40b002500541d0114007001c0c0d021041c1400312030000d014102d0364003010780034540410025040344810000c6060081d001802d844541d444858142e65410398441c0c0007208559019002030400110541180110380c4031034001d0408441034404e10040c007541d4203d804205107080e500d06035454910404c20720448011321a040e0450504003562038800154001860307602e41a03081010495008950b40c105d288512003120b140303201404d0070042c2c0074200151b04c18250004000d11a100c0c0003411500304c91099800508185400c1c00555500f2000802c071080c5d00c00c07210000300145420604103110502c10b50703c4a107814115404542d0380001d041c003c492000320b4003c4d90318030480380800203592181d6 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 140483875 1250 140482625 140482633
    0x30c030e0a030f0b0606041a03060f0114030103060f061a0705011104051003050a0e0303070206090d0c030909021303080c0106050f040905150403051207051207030e07060e030f06010e090708 83
    0x340d540c48010f0501c100301c01604030309420002c224a9074517074086400030080c503000f0410400b070f0000700800369401542c040c2d12038610440e0360210b550261080b480c10000c050812030840e031940d198000038001110384070b5081c0b942ca0750b010070307400441c0c0010321846043c50380e42d07625444280740090071a807405490300d0140c041072200b00140e80d03580244540b4258646408503141d1958138200025002413030424030280000b00400080d581c0c0043c403144288030000440b141098003d03001d130b42e0104041805000641c0e075403804d02910000703800a005e0355084000152549940740ca0742d2109401c00003074a541d5944545003000315140c22000c00071036a80845003000000d070b903680c489554042c90382411a10b0056140040d0a15000d54180e8000020001d0140720f24502820014040e034000700c102d10041c1524804142a98401d00c100c08440301c40710020100f2134140310060b074030f0000d41c20209605115044e2441e45255040c42464020301c510703007503c0c0d02400c0ca6010681082100d402215003948 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 140485125 1250 140483875 140483879
    0x70e030a05030417070302131e11042c0a0c02010f11070b061305040b06010f03230a02041701020301050a050d03020d23161e080331030c030e0a 63
    0x800481150115050380307600e02c80d1070780000c4c1c155003450502c0d0b0020f50b00034440c050b440c030315241e56044030120603080d2840c295015800c0c41c942040b40c0f14002d80c40c01006082c03105000c2d86002004810215901c005d10025500071030070b040419903c04c0f01c00c002da95840361201006117809018000403240111800e02031840c181b5012001d1307009814020706016200d03004106241c403083c08c00c01004004035800d21031403409060041c502c4000b41d03903450000381100b00307419480d803182c031908049291100b0100031192109255a0f0300c02805456028001d034208400101036040c030740419802d00c8203900141c1c03250304d80410400c0c0c0b0080b590007030b0701481601000b0000260301298801203210242801c50710b41c51824203101d084800c4055400301c00d203000900908141e202c244040c210361080008a0902e06141c2040c04400c1844a00a04040003070009c2181e100c1071900500c0c201408200801100906601003c042d101070a016004503081000000038540d000007418100003054401c020154 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 140486375 1250 140485125 140485133
    0x918070b160b06040608030a230408210c011d070f0b19120e100b06090d021c0512040303080f130312060e071706030c03060f04060b060a08070e030a 65
    0xd0030110010300040040c0c0000f0341e2980d5551160f001b03440440c0840e130f11481d0541c4c024200040d541140051800014041d00c00d0480b100304907001d5840481c080e2100c0d1031500c0085000c1c201088001c411302c903040c425000150300901c1010004000825041d00e1040f002c0c044500f1301c03c036600400310340c8091031014400c0c850f0b0070044032a082449035000e00c2c05e0907000c0040703c00c08000c1c21000111030030800d04046280380040c3d4072041a13403410003000404840c0e01003142d03d02c100107601d03400c4803100701100003502d02030402e1a2000000c42036a54040c0d05551490700b400c80070100c42d07042d4500460f0500606030300495041d4084069142c1c1c5000b810b2247c4150f6108683c3e400007820041004030041462100d50001310050503540b0a0b04220706041c0d201422413200c0c1441d4103204031a22000660a01d40041e8040c40048050090215030715104a10701d0583c000410540e4550744031102490252a040010441c80703546a4030362020b4100340c11b00600103281d804d402d500c240c1c8958119004a = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 140487625 1250 140486375 140486407
    0x903031a010f0f09080a0605010603240918051c110601060e092706220c030201081b040b03070801050103090b01092706020702030c1c060f0b0918070b 66
    0x110a0600300303c1401c1000c4801107a5601031500300030f0080c007983e0310f507908014198104606032521601d00380222111020040303006e40c0c0714000300c40c104c0d004a000f0450034550380e000c00c00c07d441e1144c2e80455000303143c40e150701e002c071900458403e404503800c000d9102540005011361525400b00a04030300e51409100a101480042c940b0b8416a42c20b004640020008443e102410b480607010411000d06070710703456124032003110705094138a000c3c2d614507210f60203207070756500c00d561000d909484c103421038004441c0c2220043c05291605464065829040c2c12030001e4001408503584039907580c90065001050b604040c4d00c0300c0d040c1410410f081c40052130072048213054400c10440000d03a000a64090f611080f8146a10116010540800414800360b5001000601d0003a400c54000c18100014070504001d098000c2d90f001c003005810400052181d040985460070302800442d035101c2e030000080080701d046d10f06044801c140090042c1400050000400a2190786081401c104121403520341d8 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 140488875 1250 140487625 140487647
    0x15070605010608162006070c030e040905061311060409020d060e07020d0c0c170609060906070c06181a0610030203060105090405090f07060206010f12030f0f0c02060d0903031a01 78
    0x61105405c071242020032040320707407180e00c58900300f1913140d81030401c4043d200a480120030b80004d9641500e20105041c01d02821022580c080000d00f1107607100752440c1d581c0c1c0c1d5145011181100c0102c40d6000550340d5001800c050001008010303035402007590010708450542c1d104401030400b0500f00030441d0380200302c20000200c54241000520051314103421415403940040c1070700480401c001c0c50b661130000303055109202e2541150303099240d00c40c0c250b50700c4004840c59400a100c1c1140c1100044050b0091a03001c9440d03140741c910b18810740c5d9980070001c10300c01640d60302c0031325404018152a00100b0ba262082c12410304620798182000000d100341b00b1903103042d0003191181e001c0342c0850300c1000740604441310310050315201034407884001d48614080c480e1884000c0c0c110804140e0030342c54092500d03801d515449035150509964000d0f95502c0240e4044010320146800700805603c40a00501c0a000040310003d40c903030040c070303000d412107805650303032010000e42c03190925160b40c200f225404 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 140490125 1250 140488875 140488877
    0xf0d211b020607030e04050a06050103050c04150513031502180d02011407021804060c020708070e010603050405030d06060e030d0203030c120c0c010f06060e0306090601060f0203091507060501060816 87
    0x7507503030028102070b05c01d003400311882c03508246411308001e0000742a03807200c3c040d640d09036000e01c59901e618a2032103150050b400b4452405607184510f24a0710301400040c10150941c42d44603ca89a8a48924141c80201303100b040f426500081e03c00c0c045411008031a5140a0881d85101c0703401c643c2d0002010f0130888858156401c400280c06c00541d03440304002a1220f00c402280c1005180030716000018203075000503034015108140c0040390b000c9002c42e0420a8441a084400c081d03860807800320060b000203042278aa0340020004411f200c8454001c400103051140c4a503034800070782d42e0525103450020320300401103400034020300c0351070710b03016048074000c1d0f4441805800030303100d003003011742c551081000c009034035882c10407211400407403600700504444582d10341503c0032100c00700380340d00c59604880002003500400c2c0180300382801010814050290b07403044a05000004000c64541005008041c9140d14081141002c00c045800350328003401440c41c1180700ca01702414030f0389070000c04c42282c6e0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 140491375 1250 140490125 140490127
    0x4050105100e09100b1c1a0603071a0a0504050301090507060207080f0a080708120a0516030905030304030c0c0f0807080c0a0b07080c160e0f0601030c050a0e0f0d211b0206 75
    0x11480d07903103103496180e810600000907520b61210f40f81440300d824072070078405030b680c90b5200000d49509e0b01140990840784444802c10b070118989642c5481c0e035000340300060511000b400003023400d0714244036402280d44148000c00700d660a02e4806803a01e00aa406a491a804410b42036040000440c4402c0c880d544192019201c0d4814a817a056901620704240701e010402000c008144c00c258004030300589618901080300f54030403c007142640c1003c180a889540200049400603101d900380740011400380020114440c1ca6882c80607001c1e142e640151000e80c8040703011b000c805d07002d1240d4601b8203c12900c07070f400e0a1401c074141d8050702443e20081d0880b03401103054401c65000780b0021040741c00302440c10400701d0322011226401c40041e1040c000140040300080d440d03500910035403850035a0303030701c4030303803e215582000300c440a078a5003000350171000080804055484c0c210324181854800c4a1510400880320505000c80c0d14030034030a8200603125008100344504c07800312510761901506e02c5 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 140492625 1250 140491375 140491391
    0x306130507020c011b0b0903030411010203030106050405130608030d0b0f04091a0702010212010603091401060612020706090f03021e0d090b0307110a030e0a050103151512020304050105100e0910 85
    0x140716082080c40098100c106c85010854512400300003144035074841c58041c01250030303280c01265640424002d080c0800d001708001d001503d00010481a00c0300501d001140007a11040c0d030600b160000f0b116244055150010102645400d000d000c4403440c00b03460421440040ea1207401c0c0052220000e0700901900b06c0100351880d00c03c0d0100e52300c0c0450200400b4095a542e140200180f017201c50640e5840c0c2c0c1501001d0200c20306000e010212407140e030354400001029024103000f9444400700f01e92440d5a44172034400984020301001b00385010381c01805a013805a95000113055103e68000f14070b070855030466003c2504429403500751984d4101054480c3e8500c40182d0b03081400050300c0c0b40303e00ca4030302031318105a0b11104294501a0a641d0210303860707900c02c0190156014125a08540b0b190301c4014003400d88040fa003400018924500460806c404c884440201e0707000b56000c0c1d034940d4560003040324400c44a80b51000030080443d200d41c1a2034840c0c41e440d20b0b103100e4455105440c3d207502c08 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 140493875 1250 140492625 140492657
    0x908012c0715020a020a090c0804120504050901091b050304030507110d0b0a15050312090d1e050106150c0206220b0a08011403010e150c0706060b0306130507020c01 72
    0x24101c0a011428034000401207480c00195651800440c228404c160322140460607410074028040281120348448a858807107559800b88420810032035400c02ca024440054959200c08101d802032400c1d41e00059500d1800c08040c85200d2800f04820900c0000c005100000340d102c2e0031556403903000070301c5607891000c00c0d0021f01c01c11144a4040c2c4008011824025001242d078042800140c2601e000c004c4230f40e861040c0b580750010b85100c074142900c1400b0000040c20104500010244250f03800100d45542081c0c44004040c0000d05440d1690760f000c0920142c0e01080f00214850100c1c00d24104140721f80d400140107101c0c0d440103002494800340c072103541355134041c8400085c20f0300b404215201c80883d079008155043c00d01c00c44074038908200503804281018071a112196031424050180b080001c444040c15060241c10320145000c104224004941c080c41202c000d03024072402c007681d07401c001c8104440365801c126224005071801c000d002e2090703000a0a4445828207081c01030100e1001300c0d03 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 140495125 1250 140493875 140493883
    0x4080d11090a030302150601020c0a03020111030c010c050409060f030209180f010e0a03230f1308010c03051e2404020904140402150f0f0d02070c080303070908012c 72
    0x440250008050380c1d01100301900855000d910064500000010351f8a032401203a4540038900c0f000d8015031104014005544a219582644c100c650116440c0019140e680f03421a9003261220740001d0003c203080c440c240d46800760000a010305c80c8a00703075481c11600060f864581c0500044010228260300c103011400074822082c2c14103800d802000401c2c000c0030402d4907581100300c1240007445000c0355190000c00c00c0709022012103950380030303400c0c05028940c0705002da001034006610b00e10500c1c000203054100340600200304a00d681d000c12581803034164104151450754440219041d0a410440707590080e44614a44040e000290100b5001c10b20208000b0f1040703056070b98005085c215071089880944021501491003038410b001d041d1350700108590a40501524006484000c000004038648841e0184c000550031400040c58a18603985514681e011640503039001c2c2c01c04410450035540020002d401000110020b000070a00303010800c000a40d000314008200250361600000e400d4100 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 140496375 1250 140495125 140495137
    0x140d020111060c09131802010f0c080c011a03010c2a02060f070b0108030c0712030504180c020106090b090121050a14010c0e1c050f0115050f010804080d11 68
    0x4419920346081c4141c4200c0a41d104c0e9040e540104202000000e42010620905c03806100034250440d10000f9076004541310040d40030041d00b001a043c0c031a802051629008201d0300e817425000284600c01c019624803110b940c4c211051107640351080641d00a40c010b001648002c8403d0440000411510151112200e0300d10002e5048040400c0f074504c940c00c407070300030102d56001d06100c40c0c203a03a8440140e90707240f1900b5040342403500320003c01c00080441072100541d151080c00d00608050300c0f20f100d810f4081c0d90b01d40135050203803540c031449a030680a1080300080c0032840d6082c00710422003400b050080f81c06105102201e101c08a500100c5203416240e04681030f400429501088501d040418035080d41134544101940390007000350b413413030080300c0703103440907101030500c50b0945074641d01004900c0da200020f44850007041041d1a10074420700c00c8a454101d102c802d1012141004203105c0d030380c0d12140e10365050007407500510000c91403040554411480410380880d10310110200128076000d40 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 140497625 1250 140496375 140496407
    0x1080a02040f060c0c080c060f0c10050702031e03010f0e0c090d120f1b0320070602010c080c040f1206092111010504020603060112091709011404140d0201 68
    0x3407002203a0719a004e4800402d02c0c0c0120401c4c000280c80c0c203040c40d120440c1100380c17503004404000c0601c000c10800054052160030001381d40b42c0c001c00c480050141c0d03000720369800041e04005407410846c010707071085030000d0200c08900c5095604000c916064140613028110340549200c00044400c0e944102b00c603d00b11018040c0d04010740c0c90f1410038421020814002c0200382146483c1180074410781c0110b50050290740d40c900840100d071410b480155035080c120500580201d0b042d144071500300503e5005104642c00003034081b1050310010003921000d4040e0400200c100010071607590081100000e8800c0c08034031140c29050341c80d06030010500340c04000c003000c9510b10100307110302805402d00754000c0682c80c1e004241c0c00f0224018200d41007210003e5009000344081041540311385c0d103041c5d0302e880c1c0340c0b00000d0b004416194103554034050010004e508000003224190f550b845041855034103040a100da0800307003803425a611442607c07541900441d42c0f41408010340e0b2080c2c1c032752035a02000b = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 140498875 1250 140497625 140497649
    0xf091119180608060702010513030302070201021515030106080a0f020111030c010c03060e01090207120e0103110f0424020c0d2a17030c03040509092d0d0903020f01080a0204 76
    0x7144185070080c16161003103100300d00525000481c07550040c010341d80700e00070000b400c480702d10003035400f50000e410001059046104203070400c12402c070825041406020400101911034200404140c00d40308036810880e100e8001c031346440c00140d0f1708500c0b4203000c0d50908051404040b02c000b5181380d4002c1600540403503091a290600080d01540040107480000c0d00464060781c0364502c5405038401c00d14010089410415400b094a105070204801080b05140102d5820001c1100b0030040c1c0011600152040b4001020043c241c90b003604800c1c55020300c03082d00c40400700100003070344031000007000700c0c0141000c204010030481740e240105d030103021800b0395213081c00306055180c8500d4a6401516a00c002d220018507070f0510000603118002082001185800e0901c414000d80100c00b070700c100f0542c07050740c8810031844081c1e005002040c5c03824003c06905c20840c0c480519000091505a050203103121092025803918031000007a44801c0c00c040c5115141e4802c600020301c1590310034004280 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 140500125 1250 140498875 140498909
    0x20031308120106080c0304020102060403201015050f03030724140907090203010807120204060902030c0307080f040c121506080f100209010207300309090f091119 71
    0x80075800d058448640e034001e810b40d100000f40380f440c071042d20083c0c050f0b80510300040000c3d00c660709010903130310904a4202120005040b091410100c680980078031500c8100766005505450b08000c003c0400303d40403a6408906004a1303105d20604801034114035040001042e509501c51404484800f0094108050b00300b4034480351403d0b900b503d1103800c5010341100011040310300e0094078140c0c4c40441c058104649404000c0004000b00101242c001b40c4800e0001807800381807001c2c3d486403c03802c894603968509071900030011100140b00603c546030100a2102294005d10b86009440d0391054891158600e404d0426500425124283c100d40c1002400f2400705004101c002c0c5d145030440071101c61000c10310f4200300b6030180c0492180140d000d40340400885201d4004022460350861843c40c4070b5680500d46c41c1200c2e40b040c0b0a60109094090811900419100710030300082110320800c0512030329039850b0810038440c084540701d2000c078110501244c4401030750030000c10103c1d2005407003039 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 140501375 1250 140500125 140500147
    0x91701150906080c0d0b01150c050a0614090a0308060402070f0b0106020309040f0902090718031226060f01050d0f05010311040e0f07290313110420031308 68
    0xc0e4011403226009104d0301c810b950800c54480d00603e64402582d0300c10741c0c24400c04030069100c10051a040202814002c00460414084096124020b00c0007080050400f561340f035002001812181d140d131b002d00c90070008603a100c0c001940110381240c001d81c0c0c8006506000958225008001d043c5501880001410396000801000304050543d82030280c2c1511b103940c3c000300e4034040f601a4004020000043c1000d12820802882000d0030049110050b22503d0780448640061040c0010500071800c2c00d511202c032010f00d880c40c107442e901d0700c11640313040c002250041302c2e100b000505000c0c021a0554074883d4a80084064180e0040c04001540c0c6d03c2c18100c030100314500e0000e000700e1800e00e510311062004242440d000cbc0000c00280451480d241032a0949212003882078507440c00000c0d00300083c1036110046000703020705144103080c46007a051400001e12a061181d204901e0114160312520040717214129190fa129466612540c0e9803550121440010070003d120850000b0100025 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 140502625 1250 140501375 140501381
    0x30314040305100c2307140129010e0d050c090703110f0d05011202030d050306060d0504080c0f0705130e0118080705010609060b070b040309030510090b0a0203070917011509 76
    0x15400300d0390751001c0b140c02a10a08400c1920099101d1001e9081003a80003081c1f00c541c0044080784040000601103102c62503100001502c078521000140003040002d00540c3d000ca2204d21410040322031380c44e8010301e03903102c1b651040c40c10800c0340203090100019070024020340c401c040f90541c9054180d0381d8045070001c0e4107543e010141d0105020303c0c101c000f050301040700e0002120707640c1c080c0040200c088a13000903529900005c0045521080421980150340080d0058600440c41034a0003615281e850390340e203040c0b00c45141048160790101d002080950740f07602c1c61100140c84c5600016404211940440c0584584007080c003102d40c2d9400030314100860003009180c01400b40d002001070584600390310f0184c032014840d001480d00d0900403180070564118400b50046e210b400e010b94415602d81d101400c05045032107081c0030950b120190005d21102041c0c00d60b009512000441c6145401c013405402e50303159025900000050319416402040d09501810031580b100a55081c0260b5a011410207 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 140503875 1250 140502625 140502641
    0x12060409110405070926070605180604030308040203100506100c03020a05011a01170606040314030c011407020c0102060c0d0e07120c0501030b0f150901020723010801060207080703031404030510 85
    0xa02d900704504c3c0c0c00d042d00038101e90506c0c0741e94014000441c035188040b1402c1c3c01160603000c05001408d01c4555582d140e0004200941c401d4491014030315184c010107003008251004000058242002c124486d5a0100d002480c90103a04003014030740840d040480c5005105c0302e000b0999846c0101c3c07040f984404c24480e0003101300907610607040c1c211125000e40400e0040c2c403d9038020b98103200507c0007a40d13405039402c080c1816000c5a04200300c6a50040c20b4900d800c0589134520340781030038040035036814420b0f0a988d40080c001000a800d000c0c003610f20303500c40c10b8900d200c1c00c2d0365080f02c10308905040c0329200c02030808005515000c81a0f040c00c0325000442d10400c0c3c0480d10703021713215107181411100264060b80081c02c0e0041c1c40880c20070a005548508851340c1180950072012603450781c0b01125203d05c240010102c00c07101040c1c00003400088041c0c00003c250741c072503441004002d10005008041c1e039410320307105489000b0b50b900b5140e50b0045d600000c0650080304250805d0200590100007 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 140505125 1250 140503875 140503889
    0x10020c09090124030312110f161b08060609060a170705030615060901031113030606090501060903080f070303150b13090605033003130512120604091104050709 70
    0x203451001410b0758030f4000c03028400140031403605280103201071903a038081088138a180d206140b401c1500314405000d80d2001d80e91007103010741c01c0400f105100c1d0f2414801e07040c1580f02e80300d0790244d04142000d681da91000708803601c03c000c0040010310980311401640014407142100070003040c400c0d111706880b1035480c062079010f8811103000031600c03114484045480100904120b2500403020011000b61441c1e80010000c000304000114a010802d4240c0c0011070055100051a508000415081c1c0d107040c0c2c0520f080154a440074400f25100d1421180380c40070013422165141d005140550151184980c0750700511241000080c40350511001403120f03023003880000c1046522140c43c0e4040b105030740500c80d0164480c51481c1c0282c07151082501d94201c4003c071740c540380303002109607021551044030500400005c4400407401c02108001007036000002d20505400e010b24640441c0a50341c000b8040da00c80c94540d01040c0a001629840006c100009081400540f4100c0c3c2c0c090f0401c503903071261071 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 140506375 1250 140505125 140505161
    0x50a030e0117070c0c0315090312050c0406120f1a0102010e010905030d02070606150309020306160c0209150d030302031b0708071103030c03041e120f0210020c090901 73
    0x400150b00c1000201007070440c0044052154039801c800711000d83e01800111041d42c400035000c80442d000f25400040d20080060120b00006603140003029603c840c2d8a07450242d0400b400e0043ca140c01c80e080e90195941c0d842c02c07012000160340359070050480d01000303011482c03070040c4035015130288107600354030040286c00a1003400c120f003414600301c8880c1c0c8000703041c94109001d10f810550786500240741080c040e080100b21591a0520410701c62420907008000ca9070300d182103011800e060040d540d00205020341d04094400b14803024100014905000744116150000150812911418400e4400d40540424240426858058000c0d40291101494030303d0314003420525406a00c115505654000c40d041d0034114240d4444a40c4e10381e1803002c82d8540000c1c800b100b24501c0401c081e1000380352148841c40000d94003000104407001c0c80c0c22640484c00c0890070400440c403902c100c3c4419641c1580d0042d210801c41ca012428200c0d50b04c00389510810b0041400460b40054219805c605005c6004c1 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 140507625 1250 140506375 140506397
    0x2030420010c060203130605090c180c0a0f0302042102040b030309151305060c0d080a0515010e03210c010f05060a03120507020d080c0606060c0c0d060605060403050a03 74
    0x440148521030a1241c001494000780c0d000156081d00510382101e1101d02d200500d02c000e642d10b205956003184d0380000c542c840c42741d02d00325103080360314448000c9007201c1c071250b03d0400e010a04810b10440c140c4805000c03d41817120320a0303200381e0403507004041c20f00a418620f406000e00280c14100704109a00c00c0f810300017000030790318010080728540704005107070b032500d001c2c1044c2c02e0071190406c680d00d01340e0710000e03540082c1f1504c84000600608400380003074048800d10a42c041c01d0680045c00c0d013601c4500d0300c81003042c0c04900e165054039008090800300144500d0b0300000c1e252103d5002d014a00003c4c000b03940188001c02d801400c403880848000703125a1504600f04001c40c0c1046900d41c0e4003803001002080800c2006a01d24111b03000d600c1c0c0a0318005090f00030a03040c5030b10302001c40c0c00510010f820303031b8611800d01031726411143c102da485180960401840755211712400286216500003004141000300b50f170b0140d00148000b03840c55465550760306120344c950b055070b40f0640103d4401c04038 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 140508875 1250 140507625 140507663
    0x705210411011e1805040606020f06091f051024030501051806060d02040e0c19020f0d03020a05070204090b0603210f03061908240903030f0702120a03020304 69
    0x40310350310702a40c0000c40751894021000c8801a0f210202e110000350b48510104403031b141c0380600c0000d8001d58000b000f41c0034100110901d0100001c10412003904540701c8511043d0340003034010742180d009600171895454164a800641c0d49561090710085107540c0c800c3d00c2191100c69006071903c160310f00704890380c2c2c2c800500100f085482030b9030341080044000030704646020400782c000005500001401c0c65117464400c0d40c0e0910580c1c806150000100300b2034101400c0142c00150100644080c000a0440308006942c0799504041d013010b06401186002c0f80c01d100d00240e03001c07140c00034011f0119140f6400c1c141040902914080d01a004003080b002104c070b8440380e40080390510400fa03e01e05000c1d04c6840c0c4680d0406800c1690004450160441450a4644000107451000b01a05d0038a8420440e500d20040c052513040082c080e040410050010210980394407402c40c880400300c42e0354404d400ca0411b81202c0704485860004540b03030b42400c0c0e055024605c07552060f40100500104018 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 140510125 1250 140508875 140508887
    0x90d02070603020c030301120c180902101e03050a090f0b0a11030c070b0408041d16020a08041208041701020405031b09060d021201020a020114060d0308010b03070521041101 76
    0x4007441300d40e0080004000d086c5d161082000174600416011000e02e0721079088406042e0003903907202d1a40e40b101030075001d525180d42c204100c00c20500702003149052810840007000403e0a0203001d0540d26000a03c0055140e000081c00a074172104195898407240391005001005445942103d0725010a0ba08102502c0c012213000d20510003205e400c003d441d13691860003180081045880c49803d02c40016800280c034826914010205003002452800380c690b8544800401d94040840d4071480000011804510442e01035420914080041c0ca0142c10025503520440d4042641c078440045014010781c81903001c0c1c8103840c0101d0a4801d2100307001da007400c04034402442c00342c0c07020000000c0b07003a61a0507103559401034801f50024850748024485c40d800c9070081c444100151f5100e000ba5a107201d0001c6000ba0b00c800c04451800442203136440c02012407030305000e0310a01c0100080420158ce0095040d03400700104521610f100280146080e141082c096400702c80d0303880c0c0e001691001d58003c0c0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 140511375 1250 140510125 140510137
    0xc06011203050403080a1403010303020a03030506010302030106050d0906020c030a08010602010b01020a0c090e01090501020a090f05060f0f0a0c020303040909021305010602060a0b01050408060a060e1308090d0812090d0207060302 100
    0x1d03444600b02800c50700c8050890740302c1b80612003448a40954601980c1216001e140211300a80181006000c01c0c107001d030580d48001d2000381014410001400f9007600f03c02951210340c1440700014400300f80e0725210000780f0541c00020018400400c44c5d49200b9071104140c0c0c181d64450740284241500300005a80d22802640001c10f0000000070901444049600010b000e12004002103070b054000c0d00c85a0890b40314034403050015049001c14041162000c07200300007030070b0556100d8540401c4088030b803c0e80c020b10b48080a15400000c80038403980c460386034900440c0c0c00409807640d507035840500078010034604400b2801106c002c40b00011041071172045504803030450b0041d250b40c1e07450240800080a00700392003418030000703000100d00902c0070808140303d002079020000340181000103030090100020444a9074600d02d801000006d080324041d1010250141c6000d212605280360040d103070b004600d440440c00032044100031803d9000100e00908460540a072a40c2c29107034402102644104 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 140512625 1250 140511375 140511377
    0xe03060f091c1704020f0a0f1d131b0e13120503091b0a0306020706050a0b03071206020901031404230c09040f020102030712030203042030010906020c06011203 70
    0x221006603140a03c01c0380d00d40c0c05803008012540b210036400005040041d507401401e0108980d08042c00506a1104c2c41c5030f10400a4411501034503003906004404442c04000904041100072802d00b401045549003025100801401859103001204c4410f5940c841134240c1d5000c10107802d00e40c00c42d026400703c902840d5a0005000c1c01203101d80903008080b01079564541115814900001042140c0702411403544038641c04269410590401801e80d15000c0300c0c140b0940201204022a0b818041038003a0a175001c42c0142e250284540143e00401c079896800c1c401c1101c05d410002044006080130500d0a015000f12100515001e0515a42c10100181c650441c3c2130901003030120310042c4445942510500c100d915212642d95001b1444030a01403071008640c0110502c01085041c85d00104421400c1e90400748440160780060700e000b026100c00203c0003020384680107155400031a0704d60751100340303000703200c41c40039460300d9002036028000c01402d0340a00000412040545a000c004607501 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 140513875 1250 140512625 140512637
    0xa05011b1710090c050c0111160b0606160302030a020d0915080a150f0e0a0203070503010501030b130204270b01090e07030e0d1106091513030e03060f091c 68
    0x10071140041400380104036071070030840001074004120f0141641100c115a105034032501380c44906070941e114944182c80000c410701c40015208010680701f102143c01221441a98880401050f01441502403c01400806203e018181038001006004030f840c90b134210b855610b900c1301e08555401441c0109040449400c44c50b0880701d104040d03441d0842c902250024543c09044401408000980d1120003088a80b400420020f840d40741074aa10a0100070190702d035250a0740000d06520050140c18149592019440743ca900c400250710102000000c00310340d910784850382100402860810200c032042080c045c1c42007a066401220a4000181c482d00501e03420f090b20b00c80310303a600400b280b08140c0d4030344000c24041400c002c200500440d5440d000f07080380c050b250050030083d00170304018150b80709540d0810305080ea01d250070340c07000b1480a40003c2807110324084500341414401c150303041c402d140a2005032003840003080e02680b902011a41041000469505144983d246213400304031 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 140515125 1250 140513875 140513897
    0x50a0f0e0601050d0e07030f1104050919050123010806090c030c010f0216031103010b061e03070c050a030c174803090307060f1202091c1101110106030209010302040c11030c0a05011b 80
    0x1c4008941cdd001511031070000c903402101100c5a4034950480c003000c007011000c2401000350b498180541a08040302038003416140455501107a0f0f44d5400280c0181001500c102142005109018042054500040003149165030381492001580d000d5030907403195207404a104168504442100c2211080a1441c4074907000300001ca040c1ea00b00404c07407401e02032002007540000e030061100c4110036220303480b112900102070074070118541c804500c10a240c80108a00c1c007103041d00380c41d041c09401c0060b40c1401018a5039006603207a502d02000c075400c440d18a0690450483d0100240111090130380488455643d10301c0100e038580c031404100e00206211580c0711010140d00d0300100602c170406490522040c000320b400084030004602c0548103c0025801c00c0c109690200d0201c550340707000c1c3e000b0322103a41180c0005860190610001b4455a520442a5152405041451001502d000949449185441181e622003103900300881c0e841d40b8007a1040e00c00055a41d221224107041c2c0d07648000e202d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 140516375 1250 140515125 140515153
    0x60a030c02190c0b031b0f041809020f0907030b030a0b0402030f060f07030c05090a090c030e060907170a020a080f0706030c1d0406090c0306050a0f0e0601050d0e07030f11040509 78
    0x745c00076000700000d91684401080c40108a0700a180144034010116510740c9400148c4d50004807880031042c220b0f0038040d041025a841104210184404a4200b807a5072180d90b400e4000700100d9800e0f50305030154000440512130418201c1b48510300130303015505045508030710a5143e2400322901041c911302a008900624800c0c0d000c0490b650007824280d02d001d071640001034051103254030041d04a40c860b07a180140590600610b11026117410050402d4101021032603250092401684e440c000c1c4070042d20300c80d1604002c030b410081c2e00504116000d54950004544869422035002580d10a0480010b2003031320030f1040c0290301020341c1e645440308020003c2a540d1803115258a58055100c1e070010421400f5440780a144c1c2340c20307032400210146414144800d195495115400107002c40c1c008005800c242050641e11260918100cbe07a20801841d80c94010701c00c0f5100c0c03001a2041075808010000101c0b079140225001e1108160007442031800c02c41034075000ca981504075086000040150 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 140517625 1250 140516375 140516377
    0xc0b07080415090806010b19030c0509010c080d0207060204051008090706080601030f0e010b0a0803040513021e180a05091302040507020312130c0608040f0b06010509060a030c02190c0b 81
    0x181140c1d161948800d0f555407034141c0b1701802070f000031800c4100056030700b002d01c03001c01036640c0002a074101031001d4000008040c0850040690050602165441280400190208071010050382c1e0008540760829424070900030342281c007407680140e64a6510140140c043c2c5042407007242c40e01c009045007030500204030b0307141d1005808075060548880b404420000c460050150059854000298181ca413404104900b0718650103a40540c00801c414040b946072a1003109160b21605005a40c4002205001950542c482c12040c0060b1011818509000740e42c011507165050407540700c82d5107904d07a001c002c05e8840590b2101c101160000c01200141820b400040d40400340d40196401c190410f0001d0b607070355408554201c00140d68035020380401103030603111000b4000702c3c030b880c0007a80f03040d9031360440c00480700c50060400080000000d2a07a8840c2046a0315107001034180e5482d07000c2490090f0190022000b0200075010b4562403480b850102482902c0d12500b11000508003807070580840c0b49 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 140518875 1250 140517625 140517659
    0x10f1704030e040e0105042105040f0b0901050f0304080a1403060102030313110d030c0c1d220c090504050708010e0c0621010f080105160e09100905130c0b070804 71
    0x410345442c2c24410b081130a10407284070f6805003000c0e0f0f4803008005400400c12079050810400c0c001c0a100620040d0048000001076414039021190303a484001c0042c2d80740d01808000d6540f00000008210070800d40d00c2c09002650b004d0b0b1242e070ba10004500c81403415010840c1d903140103038004d0000508603046c05078000ca2850046403501d559515080102c0e51480c00f07a102500494410070801c42040703601e5403444010403210101d07180b1008400160b403110b1070040c118001c3e01a01d0100e0140500c0d0601640b015158007003843c2982039a1440c4280143c4800c40f020707181409038050004400c0010700516569041c4040580040072400e000c001140d080f081c500004d014001030801c0700c01001600650191041566940e005441c1c041540d00352400202003402e242c8440ea502e10807140c02c070b1780c0580c1020045545e80955a00e052002822a03102d90101903028102424840c0c6500c96481028107a4050441c8402a40d201e081060091040b0080140b160104000c00c006444582200d054 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 140520125 1250 140518875 140518879
    0xc090501050f0a140c0106060810080c010c030315090f140c04090e01060302060705030310080f06010b030403020c031b1810050402090303040b03040b01090614181b04090b010f1704030e 81
    0x1c01284d48046500b035500001c1c16010785030754408003800300c40e420100e03060b8400101480300940606181503d5250189151070074140000d07104c00104140c0079400004c50742240b841405010b640e00e0f031603100030300041107107408814648dc0b0081c10300c0c04d02c0c0a0b00740c410b4083e0542c0d6441c2501d881704500080100030340e01d5446540e42d8102000583d50308006181580c0140011034980c20a4203a0400703c4e880755122003c0d07036002d4001aa040070011443e181114a1100015182e41c2c803410141d0a11040054288c0e02d0b004034010340d50b8a10036501285c000142c10f4403582030b1078603801a011041d0000b900c6515103828a15000c101c01d15050700185101200501070300d05050303a4000c40007407500151402c030b540c2d00e80c800040c0100079552050000400c02003020084503014040400d0842c1c070120011f8602c0108840040c9821a00c0c10103440d40003410003500d90345039a00c01442c801000c0005050340050403500e00c29204510070502c01046036501e03560061035460359581504c149210041d02d42e = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 140521375 1250 140520125 140520137
    0x603090a15091103030301030c03020f130c12050a06050901050d051f0b031203160806040e0304060201090501060807051309030c021206090f060c040302010e030304030b0106050d0c090501050f0a 85
    0x110009000205480c00c0c41c0d50494085441461071414000c03406045181a000c1c0d8401d000400100c0d00481c580c03001ca0750142c48400008401c80003180d402d00162240c1421242868005007105910481141c945994140c080020703448080c0008140d561502c25560712100b4030005009a11b01050744030541e46c42030048403070300b41d202a8048000341e40c520130308941d5551911040100c0c14144658034100511942d420b255203401c131a964610144418034400700015800080c0f016151036200f6000902503408680d122a030710301c0c0090203802c200c40219515401c1450004680380700140b44010748000814926034031ba000b0300c45000400311036400f9000c00c8040c00140000d03844101a000ba68a8094003038a01e03441c0040c0e04501c0e05d840c1c9441d5450710380c800f000b040100e04400e0250344c107490b82460032148a001c2070700042e00e180141d40010317100c42ca45c0d80000905a401400600070640818400d100c604003a8000307a4000000c2d1081c40c0c049030080101e888240300c400004d145a4085091075 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 140522625 1250 140521375 140521393
    0x8070b0318071e090902060a030f1401090b1f0e130204150306060305130309120c051e01020f120d18060606081f141c060c0e01170f06060309 62
    0x14518295180d80403c2c642d49040c501c40c3d40b5100850104405003c580e6018000014941c0c0420458424692042c0815a80315414070315024035411850329071603030301c10b55155540c44018800007441e000649c0e038425334000d15010601c9151441c940031010254541c56210407001c4140003000c00d090754100070455081001040513003040070500582e01131550000342c0503003012805000ca07200501729075003140c449542c803000294803d94200035105000d00c2d1800309106403400c844ca44440d41c014903031014400c0103c61011001020301c0f0f401d680d09a08444802c0c015421840d10740000ea40c400342c803250104220281606942c20201910030301403070001c10b008035a2101000c031040d0741c0018000804980c240049482c111850340118841703ea154510b40740380c04040c40101e0b09884030580180e030122296400070401c0d246031642582c00190902218019141c0241030303044403840c003070204d040140042c0960a49022140c8190000401d50005072a0a4100059504024000c403a140b150301c840c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 140523875 1250 140522625 140522671
    0x3030705151b18060a03060e0f0a110307020c10110303070f081b041701090c0e04031b0b06041a03150906060d0302060f0a0204030c030b09010c020708070b03 69
    0x54000c500c1d400c801220203081c04200b00c0109100c80c411005070240c2884100045405405a06500c030780884140d40da8848240c0190040c04556000d80130b145403040c00c2044021780d0544840c4a82a00d1a042002c40000c44c541e2500740010380f410001640501d0280307445042c03089010f4008005424400c104030300c40401c003451584111080c0d0000780c1000820000a80c100c102240c200b560b1a01011344900c1d80d0075040441d0180d44900a100404414941142c43d400e500226009030070900142080e5201c10584840301c0054034100d0001e10146050780f0201440d5403889506a40a000c0461a031230744d0082201800c142c0e164148601012105548982e40421403500c828a070386a42c4101454107443d10313400c2c03910042c011070255500320011400244e022071115400507031030413a0315954545421070300080c020b98000500306503085030040280151541a036215094500080c0305d6102042400c030386030000d034458600b440d0301a01e4180a40b44044026607030298034070004000301104121 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 140525125 1250 140523875 140523883
    0x602130308071401111e09092d100506070201090503010c020a2607171c02040305061e061e03060114150408030d050a02120a0c0e0301090c0303030b03030705 69
    0x2108554148000880508101a0f88a40c02900742c00400800030380840d030045d05024400e443c01c0102d105011b09054a441c2100e074103444803540701500c442d040380381c40540042e441503003416511441c00088045540020594040d0384643c00d52200034590501d44028008207401001c4200d0601007102d4021030152003d1003592004c8400c3d90040408615a00b04074110156034210002080001c000d9000d03601c051008031980558020106007201d038290110052501070411484032808801d00c904465054940240064034060420340b803190701c503220107000920303040000f00802001003001030a10302d040d8030751a00317020080c150454910400c10000b400c01409070000140c440d41d03010200954140030310000c05682c2441c0d0210318040c1880074142d42c1c1c0c0616101516000c0d12400050203540568041d20004a08004100e05074102030100b40080c10449040d107000514410904c01c0301e2405001c0c100540e0340211031680e2050642c1ca0880203000540d1405416210412a040010b00204 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 140526375 1250 140525125 140525129
    0x9030e0910060c02010c1505040b100b070b2d070c030801210b1911181509040c120c0f02011a06070b04030e030f01020a0e0406081b130609020403120503010b030f04060213 75
    0x1900380c41d00340c90607032f400c01c840b5503d940022444181c01d05c07107480054800c00442d50490401050380c0c02c09603d10820328600e00040c01034100c5192140c091140107034010416000003031003919400490303038a0351035580660007200c617140d02003140c840511000c28002c1c61419040140710200100f81c1c045d014440d03060321400301e00d240e803441c03001408070748520a5424070307aa614800c40710396104105064481075180107440180b407145640d10b80850f40d80e80102e610700004d80e010750040c404480800c0d80a0004000904484059401c0107888011020164820002900d005202c1800c00ca231503115803442c144000e00480c00c4c041640d80301c031703d165000c0045c0381c0d4204100001507502c100441d001044090007a01c0346015505050007401220404554115a003030035206640346241d6207000644203170304c007039002403241d40351080200b541c007032540081040d40d020b1403c100e521002080115903900c024403a202d9200c0003800400c2c5a4034500411740c0d0018002e02d000350400d800d08008100b034010075 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 140527625 1250 140526375 140526383
    0x71401110c100606210f0f0507030f060b04060c030806190f08010c08150603190e07050108010e01030b070c1412030601030b4009030e0910060c02010c150504 69
    0x30440c503040340c2c0382405500080c011a240204c1075400d4082a8441d20410300030002140303458001c044e600303c4041e404070461050501080c001800c141304080e005044080c103581c1260700304000440c00000300c400300c6044422a513111070407400306850482d041040a030890358080064129103580840c8107060794064020140b04511035480c20008a007101c2854a2803418051004c1c104103a80c901da0502128200042e80d003190b0b00c0d40c980741030300e0f080c540c41c00804050519048400200960003c6c012040d520280c07608035940c0d0f00c54400302405002480001c04030040080016041482240c0c1c00780914800c0103180e0800ca48582800d0414215858010190340f000c01000119070740f5000325003c07040c040c1c1d864412079652103070b40c2c8500c0e41061080038012882c01502001c03040c1018141141800d01242040700c1d0071645002003150740751580d5036106801c050f001c941214143c2000008983c1c664480080148141e401503540c904c40c45c100340e41c03840011110004131812805140d05c40d43c41 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 140528875 1250 140527625 140527633
    0x10905090d080405070608041b080303011403011107110312070503191e050f07060e0601090e06091b04090501020d05011a090a09050603030702030a05010f0506090705071401110c 78
    0x20000409182040c16601c0d041003000d541d003400003048001c5804403d8400a1800035400d039503600b000584c08603403c0710183d000f10210340004800d003000c00954161058812007241c2e216a143c00c05090301d0070040d0701580c00a04100c1080061100c0581d441d941d44060140c803840c008218890000380c0190a00f644c2603000000c0038110100032052200c654003c0b42080d1142e02207115000d040f050340079418006000340010490303500c40603c070036180c0702c55101d0f00a00c105c0b02c2c0b8000298940d0320a1240000c2d00341041c4207400c1001c1c000c981c80e4800d2504000a00102a49410b50810790301c00c1e076807450b0015510080b14021071401c1c0010303d40d1195005c0d002c5502d524210031800084904440b00c103a508052045000c1941c030354041f20308503802001c01003601c1d2030b8071001030b0a5101c0c14000070f50510413000010204181034210807811a07503000c0411543d600d0300d0a00000f54000c5803014005001000307800d0000d20b120b200301c940448050300028100b41c2c2094a000e545d480710038120203680c0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 140530125 1250 140528875 140528881
    0x1e091323010c0c0b2404020f070b060a03150f0f1406101e030e010b100804110904020f010507110a08100e010624020a05061509060f0609040c17010905 66
    0x3000d005602403144a403524204524203519005601c0c030001e0904104056800c0b01c03070080781c4140050212000c0000c1c421592207103540c0686c90103500103e0121400d85440c400100c00d46070001e00c01085940108803500c5640407070202c40020022180b0301c480d116914100300c0c2801c1c0e00c0344250701009a16039421545404d002c0304000c1030b40141056941041100ca6400c0b02c0120100d251400c035010701d0802150704c040034265240541000603c494000e00001107880d649a40149018000c90140c96a0002540030100348404100700300c034080c0d08a0302e00ca050000ba54802c3c1c004101441c0248801c580c074800090010b80305084540c0b0604050348040c000c44060100c0e481303002d41205d00100200b20303103458222422205034801603110389041550611042d014001c1c4a903c010300d90010688429103081820113a00008030704046006000c2000015410709212626144212006146a0503d9640b4040201070030764181f80a0401c003170181c002c0e11084101030602d0113010002000301e1245 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 140531375 1250 140530125 140530193
    0x10908160218092d1b010801060302070203120f1603030e0d180b1308120315011704060b12010203010e040b0f070c02060d11070309050f1e0913 63
    0x90300e4024040400e08140188454000001001d0540c0141c8044c0703000b800901040d103000540c02500005a10300601034950802010304440c01c60b0784400b625602480d0740c031007030110228041e03c140290158000002611040c50501c0504054903807045001d01d081174015040f0581090340104501098940e0303c96010010b091101070b105154600d840450312400c0d00d000c0100503414851404103483c0007480c03401c02d070302c14840301025100e42002c40d211164030921500942d40101c17282c56551546810703075045176124036041c411401c6802c2a205240e112030711200014032109125950103100800203a0a010f400c3c0051402080c038040c250b056403600d41011940b646000700000c920b0310750b40e42000090364104200b00c03041a01552840e07125086284100000d01480d41807074041900030681030100350784207060f6026030b03a040e18541042040300c0b0038890001986401402c01032540f400003101e42c2424041c0c2540a1034107250000c2c844071986841482e00d010000c800c0c44100a009920707818 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 140532625 1250 140531375 140531389
    0x6190b1002060601120b030327060703080105011b0803160201020d090807060509030901020d03050603010b040603050c010f080c0405040b03011401060903050d09050108060f041e060303090b040b040e090109081602 93
    0x201d0034410051043c00c6c000701c0040d0b06c910959440030003000201e410780700041c0c072504a07140720400180a20740d8841e03d07410302400620b401d20580d400030f024900a407440344100e00714050050713400300913942541c03a00c0807100e00951110103c1e008665003413002c10300003040d40c0100c0c1d903014050a40159141d0050034003809890000784005043e40c010404000140d80c009600d5061003c0c80c5400616904c442c0b00003405404208038103903005007801c0b00030003800004a40c510f88000241ca400d0020a2506000e665601007154070825031141440204200d00300380c0c01241e0a00381c01000004c94000342642c2602c9890b081e00103400043c5401d030284100700302040300514400842c1010703d01580f070423000a04500004100c42d0085202c0c803c044116156174004d08080e01212012442803503140000800074099403200742d0001e40094800071740058081b04640640301014a0141781a003011010084910080c141240640d03880030b007140800e031610098002c18400c04110305081e10700e40100044 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 140533875 1250 140532625 140532647
    0x917180310020f1e040801050a0b0f0d0b221b050307080a020a0b0d1b0e0102160302060306151c020d0c170402040c02010e0307050c09090a0506190b1002060601 70
    0x61807040241c4543e405103079090b6007002e0348843d051041d92003015000d000718092584002030a40c01c0205001c40c1e42d08507000241804020380340a241d8002c22020007682440c107440c003900d12100540070413811543c1d80d41d81d10034510300403101c06646000755502040801200c078071032204032540d841407040f031131b0078080b103030007800503400131301003002c1d182c0001c1c2d0a0180c0d8400c0c0c0e90442c800081d10303000c0c0740c04c03500440140024008482c4100b8140700d405403000d0004000580140900c54140303446262000002042c0c0341c01505284c2559246d106201a0440940100b2600001884070910390129410100a25040600c01588450001c0c068806403007601c1030080510001c034500c6103a6040035072106070b00c01c1c1c04541c0400c501ca414001a801042061145030a6000008050080c0a80000d4404a0036026030b05601c95980d00c030b02c660340b079010041004001c1d400a03004228044906c00c0d186495001c05240000d500701c5000000f54402c0311070101d0405130300300008000780f540e001004102 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 140535125 1250 140533875 140533903
    0x40f0507080f070504020a0c080d1a030f120c151306051b03130809060d1a0603040f03030e010b1002010c030c08060a0513020f03010e0405070801180609171803 70
    0x5109581002c20391158914001d0302d0080303a0100308403445c544074020310300740c003034202c00c001c0d90f2165100e104002420311011040754025510540f01c10350309000418051107600700740a40b00a24100504880c954007071100c0d102140b0400c20030000046841203414020800111220700201061030a102034590092600c040e0720030300040c008100c1c140d1022240d10001c2c020840702848050320300550b01e80241c01c02d4a81211300821045002030596102c00c0c0006070203403648a140220a08008680c03000311001802d0700504a2040002030207600480c4001400400100c5c42c004900045600b90f086c0245000c01030303448014003035026800d4410014140010300e401003080c030305413022400041403849558080c840c1c015a10b4a010309540c1980c10402d441e0a82c2540c81d40e4a0501e840040819101550036004c0e1800000d0701440521807260803601d1103074002440d1229403101c02c01010044415071314000c10507001440810400d00070007040c5412070000544c05214010300d454604d24000b078031 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 140536375 1250 140535125 140535133
    0x30a0f06030b040803061504080f01060b07020d17160b160207060503060d0c0506040f080f060f0402090a020d0906050106140c060a020a11030d02180f0a0504050618040f050708 77
    0x44041000126103a600c960004001c45c0c1d0b035141c00c1d0104290003507036445280201d10105000c41c0c1284041400561500400024440140c0750841c240340d80c4200e15000750b120035100c880c40000741074508006138803110020014106490246040c1e942c01014108031002d080200c00c02c00c1040c43c1c2c00d15100301210500c01071101e1410311601401911014014a11480c50011408200700102d140b01c0003400b80689043d840d1565558000b1884406000f2001d45000d00714070000e41090008802e8440d4000300c04c14159601c0d035400b8000c4605e005806940e4041d02041038011103501406281d0851b42f05450000f100c2d032420f40700078404044c14403045004081044240c501c210001080d50f00000c00090043e070f1203107288019103400719400396400c40e6000100d03400940c080e8a40c0075080c9058440b980400070043d1104005070b131a001103090764007100d16501485030382040d0740315660204025240c10320f1003140040504c0b606404135000c0380d844012004600070031006008500050082c3c800030 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 140537625 1250 140536375 140536379
    0x90604020114120a0b030a05070e010e0903030903040605160501150e1605180f0a06030f05010603062402120c0f0705010e0607120c120201240501020a08030604021905030a0f06 77
    0x2c2c0f84040070180031001d102d40c460006540695050104040c0c5542c000101e442503a83d944025006240c00d01c0351041c0c0030309001c00510000d1020040301d1003048014041d518003820708006583c180c21640686540d8032a619a00c8001282482668200807150f0f91044c4a1751601c9801c9903090742c000d200c10780603400c41c5000c420103500301c0180d800d031800d41c0840e14188020071010414803409018040ea100e60702c0c542c00145030350158450700400031403000c180400e1381c0b10759054096408230301c10129030317000c00030540111200e200d010213a41005803055070b103484008101225039801c04490041180c1000e0043d4215003001c116240040c642800c6c14140d0900d0301c40010380f1409100304c0034150300ca0500c00030340110300c1001000384d00766101c8044044424032041c02030080901c5a41d07000f603022542c0745005200030205502003103a1059005000004083c2e07590780440e00081c140f01c2d00036801388001040506040a100841095603a13103c4e02c07460460980d0055803102010fa86105141070f5003 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 140538875 1250 140537625 140537647
    0x17010515010306060c060f090512030907090b06030408072a0e0609010e1f1d07030506010e0307140a0f12151811060c0a140d110c040c17090604020114 66
    0xc00701d54560054000901100d01c401f6600180001c400d0040c140e004482c6a00c04122401c005035008800003c01c41382c03803e480710a06022105040e0314203900071810700006d00010301180041420b28485c6102250381d542800842c0c00c03c1d501c400310800000100f4006002140c1401d0307030f140c1d03c090110b4150380036515025802802d0080900340902c0469a06005400c42503440c405000402e5210300e000071402941c0306806509009031201d000090611010407020362203580101c080200c0100641000361074a0910b0340d11011880034180c001c0340307041001455030000410070006100440e003101039600c09181041c1c40d4090511164840b903c2c0001c40d41d030094552928a0305198894a5920124140c0000a10724001c41542118600c1031000340c5080160010b18510040058000c903511861a5034003138400d00030003580803007650b1110603000c040d03240c503400946101c0c6d118280b42024003224007207480461003c0740c0300401c0398005400d000855034011018613003001a1007040d41010300c0502 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 140540125 1250 140538875 140538887
    0x50a030318030f0c1d06030c06090103060305121b03040b09090a240311031b0d030903020607030e01020c0618040c03020d2a02060f04080a091701051501030606 70
    0x8050100904907800400320840c049500015603080f00800048100c00d10b80242c030207620b4010721500c0700d86005281030a00706058050f01600008020340300b248000000c0c010b0603000842402d04258588000101056050003205011440c0104030355a860415241d00045250341008040940c01080104407503900001501c5110000b100e40e42041c0d100c81d010b040151642240362440800021640700e004801004610100ca1246100c46c200e00121020991509000c0140c00803210711001c01c02c40a140140059840d00c0c442c1c20014801030300c0350041005604403220440108203d0103507603501e50780401c0401e4200d00c084680d1450400e240081402036855000303024060341c0c0b5100802011341c0690156102800044410401040042c42c4104c2c0441c0801c00d1040b0070010240c098846c81c408940c140c0301e400b1003200f41e06141c550350b8441a565029100785002c1008200c008110344e50305194001c1000a0080080b80d00c1c10800e50782114240844580b5061600c2c0100c10003126401070 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 140541375 1250 140540125 140540129
    0x506090d080c072316050a0b091c080a08040c050607080a0807270e060d0b0106080405120a03090209090a0b16020106031a040c0e040b13020d020406060801081501050a 73
    0x80303668031039a162402100a81081d88003540c800d540c4d80d07009800c00c00004070012a1718801c181c101c4891b507039400340400d00d20035000704185482c040201a00504010035034201c2d07200c285140703141881c1c15803a81c1d8044d0700050f418000103800752051109002c00c08070450041d1608948181c6030001c0c5da03691a9291107846c03600c20501c41300c1000569414015102590440350884510f1400900344400c03c03030006403030089038003480c24040071034261b00380443d0b0003209540c8540e19080d135074244001902e21304002401118140710399500707072024076044400307810050b829880c080b4a80303d60740304000758101c00500b2201d15500c4449500c0129540006082d003221550071941c0006090710b100302e0152080e034101800d10244004e42006445050328100d03c254020344841405549407030048480c008280c401a04903060400804d2045600705080882c9604c0100325440f24000d0360b020809480003644554003003854000104482c01091001c00b181c1000c280580403198108400204a01c400d8 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 140542625 1250 140541375 140541391
    0xa35070605032e09020309120403050c040902031e0c0a05041503030807050706020c0309011107060c03050a030b0d06050609070f02120d020c070905241e06130605070506090d08 77
    0x700d0510f07043c10035507549460100c2045880c5a000741d84900801001e580151000b480358412120f82011501c480c1d02658241c90b40b01014001c109049401c000c06031400110507a494010517a1022420b10003291404000782c01d070001c2c124036a0003000f08180402c0036481a4080c5041080a6840c8502e0111075030aa0b60716041503019a00c0340032040702c5500850000421461000a10040c2c000d0f002014000c1a5400d030307141c03448031415200094032010184145030216003003151001c00240504042d08240e05c02d0315001500d030601348005440081420005c2c3c403140c0e990342c14000541071605001da40103800d82881d10320229284402540e589c0d90b081440e0f42c6003401b141c13033703112030103160126860b00c100003080b100e0203603c6100020040c0800c1e41e10720780170000044000e00e5040d00e030051030a40d4a00034282c40c50303a401c034854105001080499590300c290100508424060321000a00203000e0030303a1040d40b290018134040b490844090a6002d45900c00d080980c40154400900340d4005a0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 140543875 1250 140542625 140542651
    0x2a080706050c090607030c12170a0506060702060406121103160507140f0d080f041709010c080c030406030609020306030606060a02010f09030f08150f010c020a3507060503 75
    0x19418084429004018000307500c25130004032001850f0340071483c80c520314001c03d8141d011240c00d507416981074a48080c001c1581d85a9000611a02c4031070380b20301d0707100001418862400340c0f10f500080c180c0c2d1042e008400440c280303c3c0100480203840c4602c02d14503c400072482d1171403c0244640f001d489a8000881c10084002560020455038010b0317140c032910324208641188a100002640ba42c803c0c60451000615031030001c5c65090b206001d847c081c0360440c80c500c561814100100020744d10083d05141403261030ba2405000408600c0107140401c9040041c54850b42419070007400e40c1c0445d03014610f494014800e02110f0350300400e40d650030200c1180d01c155580c41c0040103902500030f404450703004624240c404030515810280300e400034020307a612001169141d446000c0c800321072a0301140c001a42100d05031055004054403100a03000a0504044658403100c0014807801800070300a82d20980c0d0f410200c02041210010f0000c1c154805000c8440c2084001045804002e00184040301c2c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 140545125 1250 140543875 140543881
    0x130221010b0d230a0b01032a03110f0607172209061401020d14161b060e030f0d0e060d0207051e0c030c060c0102040e072a08070605 58
    0x10940c040c0d81c892502070091040b140e1982415254a10950300300000201d800781412040c04001c10049480c95001d05a03180a90954403202400d221045004d06040d0700c9036000c0304030b01c00503240341006510540100000c00400d01c1840400d003441e03108180a00414000040010340e185400c6041603c1f0300e16903030300c981010000e030a00a111040d141c8880c41000008940f40115411420607541d50051403e81d01804900490391040000404400241c000031a9044c954480c0b000300000796800c20712100d010301302d0704c95200d07540036824150700401e070740002003081c0da07040136070700ad14071008a002e003514a1a800d070050b22940c071012881c08003c1448010003403569000140d030140c6103094021074031042c4d541390050341c400040a00c11401311030101886246c0d07a001035000359080000d0050049001d00c0c0303090003c039030008543c00d02107540074400885d40d4003250880c6c5200307414540e5241021000381c4e42c0d985140041340c44140c3d140b00800240c90100c0c07841320031600d42c60742c0000c0000303040e6 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 140546375 1250 140545125 140545189
    0x10e120604150b0d0605040c170604030c0305090a06200102040806010e0604060902030411040f061401030e0a0b040f030906050406050708090d020910051e090c0d0b031c02061302 78
    0x4200c1c104242d2092600210b44d0520026900c00c40c0700c0c40c41294011415030302c44c0d61a45080700021941402c0b9405000060000b921a032001c00b0203e01c6400d0460600761000009900c8100641081d0002141c001001c0301480b00c42600d180c40300713a480000c5141c035041c00c0d100b0361944014050602140704020228006868591000000700000368045480e8101440c100c4074801500391807600c56801c000c001003444030644074130300440b11045c00704d54846080d000107501800f1600b03010801d600603460f1000200340701c02e000d24820340c4100c022004542c3d040c42c0150400c591504014101b00c400d2000784095508030046503d40e9400c42089516019410b00041c00c1c031003609070094002c01c400f0140036809410030f0152007690030484494401088c3c2d40d05180702c100e842d451041d400140000072520303c0d1300d5035004140b132484500010501c45c0d40d4801192038200100040b910100a0100c044003056052004980000504818442d6440160000cd4a8258010403c91404075104240c8120 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 140547625 1250 140546375 140546381
    0x3120507060903030209101110090f020301090501091e0203060c090d05122a07050d020307030606080312150a1a13090209010216031a18011a010e12060415 68
    0x41548041c05000200c074500c0c1c018044d4012649050003441c6004d072109202d0b002d10030110b90f480421000b051400d420781c003100b0180c01c00041c1602c148504680100c056102802041c0b80c0c1402003002290140d0586440404409002510020b4034482140880141c6c1c2c0440c0e000d40140801e01d440e03498100f403100003480f080c05840014485c0c0700341ca400c12441202403015001880d003030303000b40002189010701c0704c00ca110b26a02450030350b00522030510151402a54001d2103600242c100c9004540381c0d5100b00481340c5030b4110303410a41c00498114614010300e1189540f10801008004004d0103c01c04189c84c81c0082c0600342c409407200c0b1032004040242c0050354804880314a001c26210303034a0303151600a510040041c0d005015114204030702c03010741005039049039808070f0005402c0e40280d10000402501034a0555601e883d111a030120340824040d100e0703012005001da01303507240702400141090340124842801101b8551117092901000300e0138945c000c3c0c11004211440342c024540b0401 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 140548875 1250 140547625 140547637
    0x5030c040b030a0b061902070503031e0d140c0409061d06010305040203010219080105040e07061d01180306051801060b09041a090108060f07020c0a06030f150902070b0c13031205 78
    0x4c0706011a03406058101e5030450700c6d464803540c080e40c0031140c4a2040c075449106c0e1940543e00b242900071610308014192b0000c048940d912500001c0c2c406551100700e1042c030040c0d840381860234000c50244045240c501c100801001302141240410142d251200340c2c0010040c03e01d41819500d400003000c1d0345083d01112208403d4030a90301912400c0d4030060b0442d2803c1c020076000e00d00d0086456903804001803114151000da03100c0c80400701c0059000c24003407240460302c5041203034890141103c1204040000041c6220315000b099500d000c507280c141e0705480004051850381030803c1082081503c0080783c69140c400d0b13601041003d8100440310401d01d03100c1180350841c642c40c0000903000c4011a9007801845c10724540300341a1103500c0101d83c2c444130482204e42c00028210104200b41c0603611190380004603400c0490411060350841ca94451140c0c0301e075030655000a1150200095a03600707a83c040c445260302400c100501500c0c3c11031541e6400001c000713005000751040402e002c1c10130b0341d42d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 140550125 1250 140548875 140548879
    0x1008100503010c050403060e010606170901090506011203120902060f130e07050a0206010909030824040e0304050f01051602040b0d060c02010903030506030609060403030506010e060c0d0f05030c040b030a0b 90
    0x300078043d010004140d80e01902c0141c9400745420200d081555041c00303104112229079548140407164540e101500b0840581b000300c2541d0380d203440d0400079a042c44986d008140e074503a6910300c0145810040c24912584400103201c81c981210500144d41700b4081e039030311004c1c1002c4152513880160248054a07229000b003e0300904076003c2080c80ca500000604850513181d0030744503981d81e951f980307070b040d1456100010007089401e0006502c2d1848454201000f0000720020320b1510f03150350120f411582c2e41c54841c1002e0b000020140100e083c1104204151102860070a150405907407942d8010204100000e01c030300c0e1901070408443c1c0e204440d0310010b580051040001c44031152020b8000c20541e08201d020900f0280010f04620700450400d2150708004060105139403070b96400c50042000a02e400d0500441032401603103522082c01030300742404400c0080c007030640ca400000c2c0a20381d02e0450041000030810800500040310b100b46c0e01110007802045499071190030010024203041c1500d95 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 140551375 1250 140550125 140550131
    0x22701180b15130f080d050307030f050906070807020c0607120201020c0d26040b15011b0605010f090203041e1e0602030f0912090f0609032a030a02100810050301 71
    0x14003100c411a0040041031250103c10014694a980e0786111641a2203a400320360004694120254000c40040d0f5015000b4071300011900301004501d8121802600c401959910143c10454003a03080300d00300b43c201c007090005040f80329541300000d14030322030884000c04407030f0605000b02126000f501070b607030000e0303040060b44e6006210813401070400c003c82d400740060401a809452110240801031401607030401c0300f011460f039540c1c0e03200da00080113221442c1045035500b580840d010310030450b0000b10b07104070383c089503551502003141030f140405c0d000004a01c1c4104180301c00a00150f803641200032407100020020030983c1040c220000003460380f0712100c050b002103d401c000c113690045200300d01350f0400f000d01d031708c0d180071840c0da480304940c204040410400000341da516041000d10117809000b00103524010302100420300300340100d68014500c41401e01441d2070401201c2040300b6640c0140d0040c102c3c1050303900000d14522848a581003841055804545139115500011029260247c024 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 140552625 1250 140551375 140551399
    0x1505070507080f060a0b041e0213030b071805040e0703140102040b0a17091605060d090203011817031006030c0e040c02070801230114061204060504022701180b 70
    0x2c54840500f101d013200f41c103183c01c0f806d841518192060342400c0b0806400e40200180c6020200001c3d44242c02d00034240d0740302400000051010781d8001e02c9405285e496103ea442421403e0301c44510a0700080e12641c104a4002d21140d40020310f5011a03402c05442000c1c88009032a0500903c615000080d540c48001401c07060543c001d8030b0301149000001c2e8a0301c1a0ba100021161503a000c3c40d5905c0343c103504081c1c20041031901e000a0f180e40d0740b0a10300084c00041e2030740000c0c2121440320ba400415072810300c40d2000e0280400d42c2032680042e05c9041480c41c42d01d0034690078a2000d6000e103030145503a400301c8100c50380c407641d00070b0b5522201420030000d400000740c01941d0354010b4032580e401903090204441c010380155039105140181340341562245c0e420203002031255040081103903000102801644541d1754200c00783c83c003a5014403000215070500380140002054913012050318060408030b14548010108202411030b030119115155000e400010304024040710745070250301003104d1b084 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 140553875 1250 140552625 140552653
    0xf0c0806040516081b010f030e01090b06090606070b040f030e030f0115050109120f0204110f1e0313022101140609060406121203140421020601150507050708 69
    0x200d40030b6104810942d40c902d581d12840d0990382c00380581d0717020a0040328001020207502a00c5440c14141d182e00380400c1400c403a0701c489007101c501480c03e440303250707006040c0500d0f42418200d8681284040d5a80d92801b03181d61500c1c0c00090307001d8401406e0356004d40c801030525210b64250301d40100000d00380d9041400c1d1250385406415200140800da0031990000941076025203c404c3c00c071604a800320706030a580d52644110307101e0480c010b0b600503807150020004580c01800400081d02c580c4c0c2d0880c0c449500c81c8401c40c403105814081e1003442030406c18820307800048203602403a10b50482c1d00010140c00d201030800e080d030100c1d03060701c02c030743c20070a070404045105041944203102c2690076141c6a541c01040005440442c4143c100d28003521450344003141c19a00200d070030420a04001ca01901d02c0d420801e1204811a01552480d440e114204072025204c02110000d40300e91004203500d50402e00000045000d809581051040008411003008800e2003000000d043e0501503070580001c8100d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 140555125 1250 140553875 140553883
    0x6080303070206070e030a0204020d02161506080102091807020f0615030c030a030c200d0803010305010b0d050c011215060207150201150e1503010f0f060f080303040f0c08060405 78
    0x80c581e026001d80000103d200c0e124021944113070703030010001c0c80150080d400b03010017035002c40258001d1030b40800900b0122402210f4108a15106000b42c5014900e00c501403400c40b5080d42040d4800c2e4010480d40e01c5030350303071000390f12185102200c0c41070301038036000002c0c0d1406c480340d5483c1c1014040c001c00c000d841811242042e83c5e40c102981512080c08a1000301031b21a07c40740001404101050f2000700803810f0000b00c0f481c0c15070118000c0c0742c104442800280410b8031200201c40d4801e0000050080203001e000f103080c9e180058501e2101e50041e503540b25103500b21441d005042101e8251042d01c10000b0303412030741090302d0050900c0d003040d4441d84000c1d240c441c00d000700503602c48400b10051100f48144075455620080307248600843c4c2c00c02c210a402404003912040e03113146c1000454140750b0302031161803c0404100000520303c0108040041510036651022405400c030301420842c0100210459030b110ba800502c40521010a00d8900080d0705550408032452144070f0412042040c00a = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 140556375 1250 140555125 140555131
    0x50a0204080f012003070207030503030901050a1d0a020405090304030b040b1501021903031505060d0509070b040302090115180303050a140a0c030c020301061815090504050706050c03040906080303 86
    0x8415268090b00e21482d441c01d03103036800c51440d0840314150703440c168070054501860704901c081c03040da41c49564988800b49075820948408190b41d5642d020322030341c000c9d01d00c682c003000c401080580100303800340e250503500c41d0301185010b800f658070f80c400903059210a000700c0c1e020b164814100c0e102030410781083c1c6080402260320401511240844090030f6000046890800c2d4104410f002d4100b40c82c0c1c1c04170060b01e008030601c070750074044040104090b900c203400343c11099040c0703e00042c06e01d0858034541c0380c01920b82c070001d500d40c0104421300150312118065815140c4a10a144002070b04840c212062a0ba58114a842040202d40881015030080007491044440e5803207418030b0003500d0301000188610b51640300070920100d15280001c0c045c0c507901c51880d000034000690260342d03041503104841c00c803011144403580d80302c0141c202c20410402c1c0020780840d01c420407031840d0a6407803031b68440c014090031060150100d500003512100b0411540a8112130005005030303940c4501c0d40d5600c1d0429 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 140557625 1250 140556375 140556389
    0x4060b0c06010504050c160c122906101103070501060303021b0402040509060103050402030f07080109020a08060705040b0f070206041d06030c13090204090506090303072d140706050a0204 82
    0x2080000540d481c01c0c1c02094028894411020b103071681a41e2001140d10081c00c1c12110001102c0000400300208041d040100e070090485598480782c18600040a2b003901d074000724242c24100c240000d68613041c4500d0b0301d483c00c80c1000088002103203c5280b0714040c000004003290309180c804003c040e808900564201c03503011548081e4140d280400050303004501440d40c02c840494001201341d0710a4010300c0c1c0050002e41a642890824003416003411002d40011400d80c0d147d642c05011414581000e0004040702009040a070a11a900400c039202d1803207010f04220001c10200840c0b5000021a80e00b6030780103022607681d41d42c80380700103648102c40d4031000f607410040700012200d04010594142c10340c40100200c18200c01c80407820001c2090358426600301e6920036090000820800c85603008800400c004d585900c0c0c1031600409584410040780c103804122510700b17a140c0240600800200600e080895007008031600400320b500460802400140c145000d20007131003401da004000307940c00 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 140558875 1250 140557625 140557633
    0xf09050d200604030c080a0c0213060503190b041b0b07050c130209010801180f050c0306091e0610210e1e06040b090a02120c130c0807110c04060b0c 65
    0x20141d00c00303440740002c4a0240120b05441c4911000460800081012040c681055808012030b0780100d49100700303c1040000c5550707039010174443c0d490100080d406c8c1c2c0e490101c2110140a03a81d48001c3c468002600041905000802100124078844142c00240c00307100c404d0758a0307001302d0230495038541984543c240108c082c0e0540c00c0c0c041e1554000c5621100043e1034051450f4a0140340d245030301450700c24450350a50303908882460101d24001e09000d0800300d04815100d0a0201c100b2070718410280030340003242e602048419202c501000f541d80e000700e00b11550800a544440c043c1c3e01e40341d4101e200181c04919544655820803558800100301c03144074122038010b80c1c0c0f01144028456964035800c902c0d0301c440c000a0014289100f481d03132081e40c810a54100f220705070301048030501c1c15000c9124982004a420407d8100072286044912030404140058040c0744800741036100040c00c02000c0002040d0202c20107942007003200300303440014000f044000d0343d544c041c034855040380a00350300e6401 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 140560125 1250 140558875 140558927
    0x16140f010b090121150b100e18090a030c0302120409090b09160509060a030203010c0504061116033207081501080606010c06090b01060c02030c041406040f09050d 71
    0x203042101d00f01c41a91041a0440100c11a25131340360178090313043c000a0554607042c018100e0b1b110620300f102c002d40309481d03a04030000f1b20402c11a0325040802250b000450500800c00c1100c000030300c400043c0e4050030805940724160404a040044190115107400400600024108d01517803103440060b0084550404548401000c0e03a15681f5980310341e010500b02010030b02851500c426800c0c1c1007070005040303610607a66039006c0703402e454584664001042c4086810090207802c4204814101d445002808030b07885000220121848240000b428840500020805103840410071440c8200401e0b21001455048450b4550b106203d002e003405600929810035501406201424103a5001c003000d4030455803078030011161959038000c240d8140781c49640300e0380866850810716010b07100c5940c49400051150040c5850860341418a50041d860014030307442089000824603000341d070842d030209906480d80480c2e006042c0c0c40c107000d01640030f5074040d6030340640c00090740e021400c0020310b0800980 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 140561375 1250 140560125 140560139
    0x170321010e0f04020f1e0901080c0108010f030b040f02120a060204090b0102150610020a08160c060c0209040213060b0409050601030606020a0b060d031e03060806010506040b16140f010b0901 83
    0x102641d0094008445038610b641078a0404040c4120200c010102d4481031b01d50320003e65081020781c0500966017140c030100b0f02c0703564400c0108d0702400e00303410703900d0105244d80e4a95201c00e10040000c1c014403503400e000011951140101c1c0990002d69044546404250419000030760003880344500b4507140c090407140a50022440e136400120488404c68030360f5a000c188581a03461201a60460140c400f1940003d40741e40050021441c108158401ca50500d1910404448041e04801d00388103010303514100581c0c0d07104034107501980c141d0304c40c480d00d1003420400003d0010b91300044070b882e101140c041028151984840c0c4160826071701131000994849081c0e1f210760161070702416031034045d800500c280c1040d9903840c03506846403601e40c54400c00b6030700c3c1c2d0541c41c025100d00720000740c640100f080f411704100305507070242c07600303d0346940340a00c1d00c11640414030418880355011500410700005118094031000343d021408015100e01080e2504014006c0140b036503080c2c07198100b40c001086038 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 140562625 1250 140561375 140561401
    0x8010f05091302010c050706030c080a06080d0f05040f030308150906060706051302120a0210090602030703030b03030706021201080d090e072709021c0203060109170321010e 76
    0x100c40240c0500c61503111142c1e50b844024001206134140101451445c001607170820200006151559000031072544c4e1007402400c0c044084c108102182c14a24107100d802000f01d04000f2003140b5041c821400c100352401560135028a80c001d43d042c0400400000901d038000701c00750b22a10891840141040c501d0782045007640040d00d080c1e821410a0000341c000802030b600994200000d02c2d04540e0221440c3d000424140e03c44030b800310b40750800c0d00c04d60b0440c1040c0340c05100e207140a080c404020b5041140081d0381303004d500000b500301525203d000383d468074180100c45200350800e0003503554561f280700c154860300f801c0c40780d0451841825a0800594450105441500d011031055001c5031a041d0f4100c03030340b90300ca66194101840000c060b803003400c130040100c40145850000541c8038092a034400215244c0c5a5465043d40c1c010000c10601341e03032000316882500c0c41640001d1180485000440c82c6009031282010410103540d60168080c4890210b10704860290101081541c6d64490b41188 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 140563875 1250 140562625 140562629
    0x63302070612060e10090e150c0d110f130803041203030f0b030a150605011b030809070819060507030207210e061215010c0302120901051c0b0108010f 66
    0x5030844503081c00304034410561511906081d600204849480b80001200c14405541d126030300302d40034070108000307903080c0150207800a0140240920905826151003410001812643c81700c0f800034540140610a9001c2e40d44448c0803c0010340b02d01c510100340350a54819200407000d0034480d0070004505000004407800e8494035062000201c0f0682c1c7d0a801030040240b080141940b51025141c5540f010040380301c03903e01401c0b1000c41d101808029030111000d81c1c11882c1081400c003c07a02c000c04507290744c1031a15074140341448165171141d00003418210250400c042074001c246003024106e060300c2c05180c880b03008010402094407010003d41c12445107820041c0b400d800245038080d020201e10310f403604026a8200040c500b280000014110f500c00039540c8104421107052182c40c2c0e00e440b12a014118080c20a0000050740340c40181d540d140700706058800441c009100d00d26644140c05a840c89484404022510364168017400e002d056400e801500049040000140500c810740724001 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 140565125 1250 140563875 140563877
    0x2e06020304140f040f06050103050c091f2003030a0c0908100b04021e0304060b090103030210021e0403050616051602060c03040512160e060609040c0908010633 70
    0x46031516150480e5042d1001190311076100030550910320703081e00d560140f15500308000100190042c201000034003250b02c060301803424440b0600c41e55005031150402400011241402c1484026400e80c040340d0001c0c0c0000c00340e49683e581c519140807980000095400fa5450107024032070412100e00840b886803592041480039440803110700c84072a8507a116540b0740301d011340094035142e41440e070312448240b020480b00c0003c40001c00c200a10245220b1050800310844080c40254036541b0000c0d0758007014000c024425600140c0840c0d04c502011201c00045100b50405449075520305010362202001c4070b95102e210340300010302940c580319508070741515404400c460b107844929000e1088641160b10800304a100070040460982c1c1d6005604002d200c980e0020444810007007045d401410880e849004209603540610410ba5160303019140b0540c070554000926007980c24088910000035400000c29501c0c214002c40c103600c0040303a01000a039a684100c020240e05004400090a0010114 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 140566375 1250 140565125 140565127
    0x20a1508090c0355050f010b0942180103080a110c0a080309030d0e0f0405061f030e01110f0a05030910180c120c09050a020f032e060203 60
    0x410741aa00c1a20130703c040c2c02000d02c8124503034400300103032001c4c04420f40b188400900c401c15002001010400100c065180500138005005010f01048038a0130190039800c0d204600c2c4c5140600701900e20030701c0815251040c1038841c0c4100000c030020301580d00080316000d071000998114484080f5029141200d910400041c513100350700e041241d00f25109100b40d14540030350513412800c0d81e2803000c00030185c19402b004e103030780b0940c010802d4541040703542d900050240c0200528002d54901410340e003240f206440206441d0f0700c0394006070140709041e1048840c41803c50540841562580c8040f4014100800801468280c6080d848c1240500d1243c1040d0b46020040304410b46c4c0b084000e15003120414084421448041d0310700d80c10b0b03840c204e000c41d0309070200c040c150341480f0b1b0400640e03008289145121420191540344c000900b41c050041c0c0d15009d4035040410340754082c55040311030514207041581e0310f90408090300c41000844c50001c0044a40400300f8003040c92210016908032880d6800031 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 140567625 1250 140566375 140566423
    0xb071e0302100f090212071d16031505040507090315060b0306040209120303070c110901060507140c1e0f0102030313030323010b0307030507050901120504020a1508090c03 75
    0x2d10241c043c400074105050340b640312850041c0c88a9142665540c9000301034400c0c01d0501c85606d9a83c14a1112a464200c0b00002e025655242103266501c0c00a00c0c44c2c04140380d80c0443c18000e8440055002940203468202001803480e40260020140d03849100d2200c0e0107120840031400340d4640f40a0a04100020004189180b40650003002c0551000e0001e04284240c05441810340d00115140c1d8003190449603888108100302d643c1001380941203130b100f4580d50411070020f00c4c9000742d0000812041c00101c1c8038240c46070400010440350001402180d0b85502c00c01d87c00504010300342081e00408035685001265070000c400d40f031050201c00804000d90016842c100d000d40625100e01800d132030060241d034040e4150f00c0b2154040d01c03023910a076a030ba0914010042c21500000d105104101080c000302801d0703079004041c50000350210001040c240c44500004255485940c000b6000611040800510340c0d081900f039032107005202c0c2914205072008007490744031034000140e044501411460 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 140568875 1250 140567625 140567653
    0x905010905061315080a050a050c030402040911040614011107050d0b04031716020c0102060403210e071e0611031b031303140d021b0409080d060b071e0302 68
    0x10f054408103212030755074100c2da00d00302403e03080c1012078650300040c038000802c0703100b038075902a85400c40c406800401c402d01d040d05c0700120b070340030240000388616100c02c45c041c28000c0c40030a044404800030300400c40f0b9540c4404118140c4010811070f404034488244d4445903180100c0e01d08200c8a0150240392881c00d20342d148070394060014400c42c188080a092459440c1c80000318503c2031000000022240b0328400c4060301d41003900c0305007411588580700308000030358844400c0564444400a0b1610b88a0501e49400541003a114a400d10701c20364000040e103e01c00c400400e80440600f030b42c80700340c50300c03584107c1d4000445100200186d0040041c00f144007540070300310798450b5012040d00e082c01030920300b4480c40f50b4160300582d40042c0c6041c0302c00026905205030504c1030301900041109000309403201c0d480030542600180703e940d80b0124001408507500840d40d84501c0311100f040900d865122490391900100415203801ca0000c540320f8006684050704258641c05030020107580282e862 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 140570125 1250 140568875 140568877
    0x30307030c02011809060509010b210a090b0c030106090f0f1802070213090b060102011e09050a02030f0d0e01091413020904060b270a17120a03020304020a06090501090506 75
    0x40228104020310f84c001c0d450554011107600500511400400d10600e0241045840c02c81a0000c42000b0010420038480ca03030749400707542444002d07640503815581c880302440b0041500c0031001d40911074500c10040150050f100946c16070b44a6242c180c07145854ad01000740d80c0d600b5018a10f044030584e042400310100c00c400000a1890fa440050710f04100340e40410720085040000851140e02c034038001080000401078590302000a20003003020030032511075643e43d00c01640c500c2c3c401c259260003510030711000340801c2d11165000750407507002216800600360364201184000c00020a1110000120341c81107054104640d413480c00000d49400a03010000a005407500c5021242c1d42007001801549845c007500c0c0041c000b190001d501c4030700990825064103103001d200c02544001044001065130b4040e1a8070503070780301010300e074145915405c0d500e2500007031980440418402003080070b14542e054004500c2113100750780781441a66219029241810540189804212035400501c02030a10070 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 140571375 1250 140570125 140570147
    0x5071209060605130b010305010e15040b03011407050a020106320307080d0f03060f030203070605030408070203061311040c02030415050f0a02070518070909020a02010b09070807020f0c03030703 85
    0x1d000045841ea501c0c0060103480c9150740e00c44106442d01c050b00f14a6030144070701401400d002010051510740864081e900850042200344a56560078401c00700351001d60043c09c0c0e20695020b80d108c0c0b8144072402404070780081d1107040041d800c1800202d00001d20f420f0b18403060f143c0070602c500126005c48034643d00040400095007502ca500d10000d030f100c01c1000b401186072031307d480d0f040070b04c040420001c05a8070705402400720b2403114071007000141c40000742c51084551a280031a281c1e202d52410100c103114800c0040d5262080000b030159050549185201c0144075181c0414502c12020500c1b068400e024126009a08140010881c203084a1000f000b0480390f441c2ca02d2810000c2e01012034660000310300580161710000b428031103070415104c1c0b100022250400e0084619120100903c04040c902807041c40c0341e00410000c8601d07000350000c82c010103000380740320542d2504201c02401c1540450311680184201405000070040208468200110140146103400025201928400d50030 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 140572625 1250 140571375 140571383
    0x11070308061c0f0605061807030203100501020109021003020705120f03010f0e0403021b0a09050405060906100f0b09010e180613060303020a0b100b1306140910030f0605030a0f060c0305071209 84
    0x100724011f401c01e032840e20548031501c0058403800c040040035600700c002e42080d4103583c5400018405650380100b10120a1507528000d651000301c0d01c0c0190504080940910010314046500b00e080c680341006541a18400d9610f46007055075008201401c0300141e40240150700541800c4580d4420384a0a00c103018014104610301d9903541010700880c2d900b01c0b000c0d940f0340c200e01d0034030404442c01d21120350454250101c0c10740c61801c007000781c00040b01900c10225007480000305581141d018071120364440000403c010440003100c50346c911000c01c1220003178842c1801d0303049042c01507010700c030b003600744c82d01940200804040c56aa14102c030a01800454107011301d6200003a0703841e012801400d8180850a94044c1140b408c0006001d00c44c2c1d14541840d0003070141b04401081e142c182c200c1c40400c9082c50041038490f8001c011000602181e0055078050180e401d40e0000e001e802458003005501c112001c001c03240500604134201d51058074080000385180d87c0300c1081c103460342c010301541c80c06 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 140573875 1250 140572625 140572639
    0x30609090c21010b010e06040618050411090301141905060f03010603050a030e0a0b1215040f090308092b05090301060e071706101211070308061c0f060506 68
    0x1c02400104001c00080491a5014000c1000300d42d421083c051119124003c0c2466180078440e000001c0070340c0184e008120801c01480b0184a00010150011000f0b0201030020801311198032501d40c026030103405000e01a40c24000211160314620100ca0b228803c0074180160880300100890080d02c0c1c050103190703000b0241c4d080c150042d0350038801d030342c001c5103d2070090890080074503000d03081c0403480781d01600c40c034801801001001103450032252121a640044061030f070701d143c900c1c8034094100004580080c0340074000c40300c130380099000301c0003680203403142c04031a5180480207070354480301894030a03201481c68003405d00303200d141003d90035140c090409c80d041800c00b00110b82119651351141d1401180981804420ba400c9584040391000700b440400e80d5181c0034000c42d00342c09000030000c0070000c190b010354590950070742c40108a40754581120741e4503800341c1001420080140c0301d243c4240d10415044d0480c200002d02d120030380e5440750500071314088540b624402848000c02c0940c00c00a = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 140575125 1250 140573875 140573893
    0x15011103041d010611010908030412020a0c0306050a061e060309030909110703030b01020a03171b0c03030406061211010c0c080a06092306010e1e0403020c01020613030503060909 78
    0x14800702c42864500d0142c11a00c41d626041c80207180107034408500c000d5924100070800420f031400d0403654826001174104004262070301080340f43c010590409021088980004010030691303801c200c1c014000070703e00348032954403003001406180300c0f168880210f1000300001c2244074001c2d0443d05800380682032100849998040040079900c0080c0100710342800011901c0070181c00d849000445c0d0710070300c0140740700806a90040d100c16031500b5642007140e0038000044444100401d845451a07800340c11030303240c11300056278598a0700251030032942c03a4248400480d580720210030002d00b5580080c4942da104c1111001580c02003c1584240c070040d10001c4041255030007008107001c824444d1400150b0b03040710307085c264080701c5013403444c0806420410410f1401c440004001e810b6527500c07110070350300b0f85a0808416641c84d1171048420a40340050420041c181c0114035400610400c1e0280c843c0da545440c0400f038150807004c07009011902c20320105074981082000303a070340070440800b1500105 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 140576375 1250 140575125 140575139
    0x6080415180803010f0b0705032b1406030705030d021506030a0605010311090a0612030818010903020d02070608010b0301140102012702040b1e0d030306030210030509010b091501110304 81
    0x1c0401041a00d01800c00401080618407000341c150092038120f8401d424144d46590305a00e034424103203000c035110106903504d10381010b242c01107114249422400c00580b891415400e5401c0002c0750303050300c47d0249000001d05800c01044125003009664050403190500e00a50420007a01401d52509442403d80003070010302c0da489880d01030340c001c8108140d4401e001c0700708200200c0c0203162121903820185d0400c4081d91025000002c140d041c28512520343d00c03500304600d030b50408007a158a40d030a00c810101030540108080d00c0c90f6441c1d80c03c0e0b070642d036240c00d400d942c091000e100d14207400e070080004020000711a10410319014051001183c18401081c4440d000304a08542e003921607a05402a000c518207445070741c1c01c1e4007003070711990020100504c4031145100301e802d0301800752507504a41030030948291300590103558001c00c0b11031111452400100181012208078032136602c5e101e1000303002d24050a45a2244200783e0000d8103202540004484024103880c10501d00c0c401407102003102c0d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 140577625 1250 140576375 140576411
    0xa170405070e0403110c031b0d060b04050708040b1f0509250e03070806010e060103111e07031d0d0201120605030304080102070b060a1d07090306050a0506031606080415 74
    0x4030f001e90385589171885219011810001ea00310800e01c04d0307011110070b0380d05890504c0c0019818504644022580b842030800034044c08c2c0f000140b0b030303100c2d01c2c1000300081c10340c0201f20176009070b000365070034507880d519400c4101c66105104002000110091010001403500304540303980a0301c0303000110203000398015484103e0f00314410402c00701d070030180c034001c89040400104000f018180001e110b2945407011409200c0c0c1c003d404a41019110301c0c01d0740303c14111404640740c6242d11048298144982c0e000115181c02c9942d00301e000072000c178114051080c0820f90b40e004c0a0005007128501c43c080e5005540048811200d480400d84600707000031544c2c1c040c03003c0c02c0100034540015a0301c05051401580074403004000500c980e0708110284001c0070500680e800c080e0300310403136071203d854001c01500e2980a50384020a000d08000400c225444590045030090a0503000c45003201800c02445216000394000d5000099040001401107040b1812082c0011680c10001501c41001000c600c80 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 140578875 1250 140577625 140577631
    0xf0313080a031a010f170a0902030a0c03020a090516030c020c0a0f0906090213061805131505120309040504060b0d030203031b04030f12090905160e060a170405070e 72
    0x21940e42c071242520501c4403981c5400e500401d01c5d25504010225030003801c4505120500f00351120f40d240052112007080d84401c441c15002811a02c3d0301c041ca1400640c40c0c042c0f80812805807054034400550030001f4020301c0c1c080c07141c408182031070302010342d0304400404010010700118450400a6109a100e07200074a010300f2582c44044a142e081c00082002e50f842a841089082e104200071001a90b031900b080d01602d0f45031500e00c0c030303604541d0150b86180410b81c124980c060305000343c081000c05075501c03024030561643d2440021940d079034104035600b030506040f9030303450304200103030f810500e01640000e9116101300c50019000b4040c40215500e485080340440240c6d20010502600301400204420200e000c1210580390608603079031030800c007a10708001400c00d001104a000400e0003840180040d02e581002044585000f20100f240c105050b0400404580f6030708036180716082400c1125845442d40d1101c0f4494540410042040c40004005562a024200c80810b0340004030441e280 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 140580125 1250 140578875 140578877
    0x5090c0403020f0306010302010e06031e0a050702010e0a030203030109150306020304061410180c30060b040b07080a1709151e010b0a09091404050606090c0f0313080a 73
    0x2031114214814011464070096080303100340d105900410050b03a01c0025400f10020980b4903036100c1d00c8034255800c48401150806850a00c4081000b00d400d049078080340c8101030350340c001d2051000a0040b1900c0f0346040720064010b80003000184981d186940100340078070f0400e41d0400005640f81c5803842260429541141c0540c2c491440000b040c2c01411855000101c400c3c20405aa00e001e0b6900303684003410400c0032003103480c1c10388805a07900901d55071503642e49406000d41800700b01c580c01a214080d07020803da00615141021940e85450010781c0d0541d0030074030086c0d2400c0c02c9030b2600d3341039410210001c41041804080310605900c035506650141d0803450040441c0880030b19203480b070f00700050006007801207078000c1c06800c02e100c0c05024115464080e150382d892100f01021207031442242c204001e541e0030308a0304208003d84840291084e401b60003035070015200d41c0104290860142c0d4000702c0f04070244009803810100c14000c2d42c103e0703c080c00500560010b83ea811440d80c01c8110350780 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 140581375 1250 140580125 140580127
    0x70e01050f0d2307051218190209010b1303150e030406050702090604020a1e020106080304080304030b0702031e0a02150a05090c0306071b050a0206042601060f030209040c05090c 78
    0xc09640d00780f0f81c0d8030a001c45034900d40d10f04d14014000134420b00908804442d03071003111000ca02006116a00070351514512419038140c0c03860704007501c980003100c1d001203005528000002801040c40301c140c91600c581c00c50818061031440d1100442d0303400302c0d424a40b0140e545c41501141c10301c104024002021291078050712072001d40100702c014100108a60301440c0100010304400e607014001101c0c4044036000d02c0e00c42e01c0748540803401000039410000765488001000305403048000098022244154800d510031390741d090040380c0b00d00a040c6100603c0d090740e1002800108140d0160852003501d1040300d00000c0401e1170034050703150540781000c1c659503600900000c010107020070251001d054004140c00d003401040185803500c0d04403000c109002d0b00e4a4581080f07014080c4d40344854004056580740c03602e444a0403503e100d841001e060442076034044102c4510103005100c200c0303080403022801c1c2483c40c0c0034428000e0b4010b10840d292800d1100100b007540d00d4880b4180900c00c004070803 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 140582625 1250 140581375 140581391
    0xf02030106120b06090114031503010e011e110a1215030f120206060603060f0411030a02040f0807180e010b0a17160503060601030c0c0f031d04090b070e01050f0d 71
    0x4a02110498003183e0b0040d503042003883e1140e6000303034000c40c04601c0801d01c07035541da841501d51201100c0218080340d040d400d10032880c00240d015082944845890221003a00008454810701258904e50940e945042c0030f01000c08000c0c01140451100e011009005c00e15941d841e442e5074011039142c0040300c583c3c0c140c0c0442820b0010312062100304041d41e000500c3d007414207800040d00b502004121620416901c2d0318180c15469030782061601c00b5140c401c0b280c4a041102c0600b029401a003d98401c5c4800201c1c00620701c0c0f0700003800d204443c9140740c042c10118507072410001a20b42c1d010010303229900c0d040241d280b42c0755140501c0080810514607001c1401c03c114140c10700c084d14a20134030b14025070400740141d40d0046070f4540c1141d8242800501c03800035000942d040700317001c1c00c007801010000b0421401c0c15009420401e0580c042d8901503220f1a05e00c0410046909203a1b000c4d00c0c0c0728980e8005840c0d00d002c1c800300c080c55841410070b68206400107440341701d140d20410024180940721307500 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 140583875 1250 140582625 140582657
    0x807030c050a0903120c050a08030a0b09040b04030503060f060307021f0c05040b0a14070503070b06040e1015171605060c1b010306030c080606090a2304060f02030106 73
    0x1503000c009020300e030003480d10ba440c100003858042c83e400041d000f0103d403c45407660501032402a00c55036880410b50f0820302c040d0502c1403aa800c1203a03c100481d0924502201c90716000c007000e4802d075400010b0304441d07101d549044455402c01001282c00c05030108203640319a40f02d1b40514825551a801400400c642c4000c16042c001098213421690317041c005410702064005007030b01d0907920301881c030503100c000580040314840012030414080c50030000e105400d210000c001010f5041c010b81c401c03d2140c45200502c0225140a01c1112960f04549142c2d140088070f5003280c0e010280b000c035240b41c40c2e03842d10310900288568480c4003140b944606044058810389100840003800200e03141401c1102c841c40b5562109a0720000c0740b01e02c144040c0286c0c1c0c0368040d500407005907810280304411182c039105440d076100002e60341c4c5482604d11100080058409019024541850446d880510740030b800104e100098090000c941c0552201e14034800c4110900c0658020445992001401144084 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 140585125 1250 140583875 140583881
    0x4110d020a11010501080d0c110d05030a090803030f040b09010b09090a03091a07120908190318080c0103110904020307021c050315060d0b030106142b030302031003060c080703 77
    0x6040b403a4180b40041107100004550303903005100310b00703002d40210308514007400da9041c0b0b000101d030301444c060908028814004081c0507812919110f002500f0303140c044035640c90108850300c404081c0314400040c000343e011804950407031030100011881c03401d980e000030740e8070608903100402c55001759840414990b0118188004280702c420305e04884111241c450142d00c1641d1020b00301c0c281a90542c826140300704015402801c80c4016503180d030704007541c807002120060405a00003404440440341800010141d0f8040314101d5008050300e144d00c2005501812400c400443e5080b020b010300d4000f41c8803070001310700c54015503020305100300404061000580c002c07401001006424070803c2520002e080c0020014141150f4681c0c0b600c85a44100c400b400741c000c070103501741d4244000011060054501c0e40b400810880b06000082d0820040f5844100c0c14003480405030124280300c00070074000c0d03004580001c3d2000f1000b03160f5842e9110a026685600030540008500e04100028540c2c144 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 140586375 1250 140585125 140585147
    0x2030d05090a0b0c0d0c1a07050a41220302010f0c0302030a030915020c0c04060501020307020114030601050702031b0910030b0615040f0807150c050307060b04110d020a 74
    0x810f0541020a050340c483e07542e4141d044d580052207030b1b81081c403007480034080c9241c401080c07842d04801c00345000c207401040c0d038010050f0800131030445500c130b02142c0700380b40d8005200c00c1c80084242c00c3c0440008807941f0b80c1030b00701c601c0c801c0300c0c000c000140c0c2900300d64030395800d40700300710002c0c3d00780c0c520718800104902c2c001d20f00c0c00e0409c40440605070010354003008488510000d490003054049060822640d0110940c0980c11064030006500d4885200446d19005460701100d040150030341da83c005985174850340d98028001606200c42032140344801002c0c42d009003041c036040b0f0a003803181d0701080c6043c1d00c100200501416a4200fa803083c80c0010440e540402040019505070f4619a14020100b1001e00350a2055178407580c0894400652810356000340512000b0211007592414925182c1084d8080c50304040d507401003104030b01c0d000b41156840143c0c010019850038230143c66541c010403032400002d51150701d50540c80b0b200e0003100003030000c40604580040e030350200041e01501d10f030992 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 140587625 1250 140586375 140586389
    0xc0503030703090306020a030204150804140304260f0a080c06150604030b060d061503020102070503070e010b0f0d11180d11060a030204030f0803010f0e0919080702030d05090a 77
    0x40285100080d03002200c1800c99500c85c40258035150840000d038041d000310b400c4034020b41c80070040304080560100456002d28000c07010318540802c0310b0645038a1344640c1c043d0710400000c5d00c1c0c40409064555907111681f08a40d0240d0b1f0701400c0150f98a4107040c200442901c0701c900c0420404c41c920002d00c4001d410801010104508a4800000c50180c1c040c48c0300292201d69500700007015034827000655080d8a43c000d20130007074004840b00401c1407a1146c0030a034014800d03001c012905040010f030100c1540c0b903c095540d00c5a19104990007280d02007850481100b009129900080c0c40138010f401801160380c6059480d064658581100340c0f40c0ca015461080f07155070143c1002c80c1101c01010100407040e80e01507525118001d050307020384110340c0010711506840c0340307a00034041e04001031416200e090201e840c416076120009111040b06850741c0b407145d0071062008140b03074240600c0c90f000e14803811541d82000001e40009040106c02004100070400000302105139180c0301e120b10700034080c1 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 140588875 1250 140587625 140587627
    0x5030d090b1609030b27060a06060203070816050307120306170d1d01030204050a03120e010507030912150c0e0f03010612060f020f0c1b090708060108070311070f0c050303 75
    0x482c0c100240209154031024000c00030501c0801c18180121040c850030608954541c503203140e01c051a56601d800c211603182010b407400300e000c02c81c00e01c04011280740d0380d0001411070500852150390080400c1040f000c480307d20041010f1400580744420310310040304540c4001a0240c0750071001c070001114400001026040300a440340800d4010410000351031280741c00c82016881c0c1001a4024030440c0c00903540702c40a500000100704900d142d081000200340d4401e0501c401da00012b58140c02103030001404181c2c02201484502945c1080900503806002d4086e064220402c103503080751008030f0428001044009108418140108881c0401c003040d4020040c261806041c084091042e800040ac5203403501001c11800509070155600c271002e20b01900d41e209854011283c3d00c0c8200b43d035102049106115001d030030f01d004002103200340c04d16201c40e00f42c2e40d6200300441d607a01c0010840414145e442ca103162440c01c4500207011f4040c49154052100302040c240000c0e500341d01e03400740b4483e82c0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 140590125 1250 140588875 140588911
    0x510050708062808031309060b03041703190603050604020f032113030506070804060e0d0e040f0f0e0706091a1b0102041a070210031b1b05030d090b 65
    0x180c1d0064801d0055100c0107140011800c85a40c000188a83d84501300764071004c522040d045c80032082e83c50031a0014041041000c0da200d40140003400700b141c01801e4109010500790080d202c40c002542d000c811120300920355441004003034101d680c150070a4540c2c3d405042007101b1401d15003c0d80303484050403001450002411403000341c0200e44040c4009014101203400361240a0391030080c006158040b013552400e14140500030900c0c00100c8013030b9421400c04d0720703804e401d078000701e020304a5200d107565815403c00058140405404400d001c42c68650740c0da0200a04e0445511845500e080c00348090842c40c0e24003a4000e00044460300582c802d61021000a00d04407140400c480310301104207115407a10241182c82402400340354408090342e075000705840d881110f514007c00c84140700301c2d81e41090700c0d9090300031001c43c0c001031f001160400041041c40308243c02004061914694030343e070381c52522016030750582950003018400f01d00c107403107491311010846001901944031410b0380c450401a5 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 140591375 1250 140590125 140590129
    0x22170114090601150c0f0302010c021011030a02091c080405010e0603090a1e120203040512010b010801050915130906180305040902030c040e0732040302100905030a051005070806 78
    0x910b041c8209407090340d2444c140c03540075020f1100300041d950403c000030140b503801c0c107020340a09903041c441e80040c000c00301045601e8400c3d2140201c50101c44600da8150740d0f03880d0200d8004d501c001e8490f0341c0840211409504e0800900302d05071424070500945407182d1500001610861030f0250720f0384650401c1c000c0000401e80014030b00c007100e8000880c1c90700280c1d600c0c3e018518000805000d48800014043c032421260000020021100f0030384800e88002d100125090803030300050181030000300600700401c21403800c0d07100541c2209050401502020350080000e0b4920000c3e0056000c2c6a2940044c00030702c0510b128002c6401030080844144411079500284284a00c5c003566607031560100201d0b03801c1001070300380c60140081070010201e44c209040e02801484504400b042090302613494201c0e840904c20304516026034031141c407030509055034200104071401180c004104042d1144c0056265010031000e1140c0340540003801c0e115000d070001905480d002080403040c4a15041800810317 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 140592625 1250 140591375 140591383
    0x7060c110a2a140402090609061201060e0409030503070804080412030801090e030f0301150e04050c0d0615120209030307050304030c03060b01020615010302030a090506010b0a020c242217011409 85
    0xf04030444005070b461994000190f550300980407000d40003c000319055841003000c0d20407506803511078840c0707008550800d0401064030a080402000500c003440804d4a0601850900e6007080c440c4181d9400c01c0c0d243c807410241c6010b02402a4005442c4000421100400b48200200c03947c0203009945040030104000d20544818422010801c003d07550313116142d07204010107100380000400078051420a041c1100031904170902d010142440c00038009068200c3c000509aa44140d80700c20390700700000c0402c40f000b5000340880310f4041c0070401c440c500060017400144042d5225900b191034660950500c6001c6564031310f1541d040d54410703401c1c05009402020b010341154001d19025035a075480201c0c2c003018251085006140d881003000100395400340c4005800c1e00880d1350700710b5800b400c01404201403d0110510703d281d00c00001d0081c0f10101002d0020654a01003030800302c1046514000c40702040195804110382c100c0b00b800d0707000401c40078058101609482e004468490600300341080e29 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 140593875 1250 140592625 140592659
    0xf201e0f060403080709050604170c040c0e0f040f06091b03020a0512041415160e0d080f0f03010605070201111605120c0916080903030403020307060c110a2a 69
    0x24008a1380005050751712901070a00a00300142c1120f441c0c3d59078040d0010000301c0801c990619020b5501e048159040a200d0030310052081e07601da00300c0c00d40b220140909110b10744a41500180c5401c0c243e846201a8000c90004040380403000900341d85074144690781c100248582d03004c0600400045016a61150540710041e84179610074066807620b213804e031443ca407160001c2c2410b0148484103d03800c0207241c0c41e14070071810311031040c1500125003022101c4d59806080590300c074a040080d4004500305038050410031000c03010b140e03d400d42c1c03012510b0441e0400d0f40070100280340001c801085583c44184034590bc1206c500030320191072010101910040b141c01a40c6c011120300012009140c03040150400d268000b0340401d015080c6802c00e4214004200f104001184680c004a03004013000012203114580540c01346041030456a58034003d400084c90000c00c0100031a251100d280c000d10082c0740c1c81c0e1040d860b031081c0b001089107680034410b440c80c1c4d4120040c0403500401500019040480b1 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 140595125 1250 140593875 140593877
    0x1030b0c0310050603180d0905120c030a08030c07020d1104060b090904030e01030b0607030c0501140103030206040803060a05090f0a0b03010c14070503120c0406110a020a060f201e0f060403 83
    0x9220f50b14403956625508600041506c10300c01c005141281c00d0700210000b0566605480b101030305801501c80c65512640c40c1c4059030141c2c032050344100482c02306c001079038200c44109285443c5c84100d400040d01000303a04c00950f1070401500c1c142e10076103071900c500c1c4004c2c5102c000043c202503901e00020951400140007a081c800320641040640e0712907441000004401070070b054546d03800b803d00502007100e990003203609600e800049045141100c0d1824105c81c1e040d0b004010940e21581d0740e00d502c0c0c001414494009581c1301000c22aa52000d0030140b05040c02e00c6000b8040c40d0111820060310894821180a41d1400c180b42d081c1c1ca9201e01c030700c00d01d1466003415540c2c40d0060302d0003618521400b13a2030205014078005108400344100700520440d83d29690b246500c0901d07034442600c40310301420003036000942c41d4040082c40d0149080c11301c0700320941010640070000d155901c0188120f01075101403500004082941000029144591252507400820104d1031206c100f82da075110141001d0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 140596375 1250 140595125 140595127
    0xa02011b030201060902040b04090b0a0803030103030507060e15040b060108090706140906031314030f0301050d050307061e200a140c0a320c0907121401030b0c03100506 74
    0x200c2858000d4210710020482c09004559581d0b4510100b402c0b41c2160003890040c0d41041340c0da8161f80f5020091105507020380f070141d89180d00e10f60341a00d0584c030503c000c43d04180c0311114207400c02d0040c0440a40180042c05a484501d0310b480c2c40900d1940040600c0e050049000510040b10340000d40e0006071161400c00d0b03540c0200b0000c00c006a4000d01a100d544250008204001c203c0c1210b0f805000e04e109034031901c2c07408940c200c140e403a8020351000b10380c40c510501c010001490400e10303144075603018034146c1e4a40320040d00c616040e141000ca07266510b410000d10030720aa500341c40344407540001d260b980b44c00c1442e01c08080d0030707134401d0041a10070055441c4c0707010b00e81d00300c41c001c0301c608000480841e2640039003460443d64280503285221074a0007011712141c5100100514a03903058483c00c0038025500000003080503942014155804103c0924504103c240140c4a00d070400802190505c8141d80745103008141c010006010400e4070700c00b0303c1800b19595802c0345920540e50308403081b03 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 140597625 1250 140596375 140596427
    0x3080105060721020f0106080a14060f1513020a1e0f0c08031005131401090e030a111009050105060a0504020f04121a0a0f0608030418020706021207020709050601020a0201 75
    0x105d00e4035584120a840f9540b902d4000100008000b170344444841c410908850102200130f505030b196501141d0506c1c980042c0381c00242c03030f000c244500726042d40f0024080d81e0850480c680490881e00211711074404940d01c94001c400d0038610000090b503e1449151240c0c4101305460020301c160709003900204401c0021021800100c1050081009494083c0a45652003003031030f06d00c0b000d0000291080160100700001043d01c070350602400340e400002000640c540310004804448100c003000d548000d42c0542c00c035512844400c1d006860880340144004a080e0070000c0c10801b00e680c0c00d500071803082e84104640c00000c480c203416601100d036800c00e9040340170918280044141d080443c1c10684050503010840010740381d80c4501c1d104c101192040000944941c1d0290703481c4120300030702540344141c84801c04050314030f40041144a22803500941040118030018a403c90281e56035000368003e0002400700410313a1059070703481301091000b01b80983c01c0e5000a007c486c0c00c10315480ca805026508 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 140598875 1250 140597625 140597627
    0x3010e19110d2d03090501051305060a030204050103061203090308031b070b0a0e060601080a02090102010e03040909050d050f0d0b010c02030601090507121b0302030405070b040305070303080105060721 88
    0x409030075a00c0140114a00b0500c0b40303000651406a414052190301809500c0005100e08001e00c0c1c0100d03900da21142110360500d801910282c00c0003500071210301144a0100b081e88421001e030154070459200903032200d090a0025059850030340003040b8541109100501017a440b040c49002c60303412014031562511a203150303200e1242c8008581c050040001a00020086911121441000ca0040030011081240b14070f5460b19000d0342c40c03a00007013040c07000c600c0d418500c2d801880d005405000001d10109501806411900141d012000d00c80d61070ba007890901c80180521740d05803005281c2249000040180030b00c00e07000d098030841c00160340d0f1040455a90241d014480c5980d0000c0c2251040c2d03070740d000d03004c0241104840e440c0c0050b600301d42c0c0545010a40c018016000081a4403001406c155207045009400080080c0c0f29441104000243d0007100c60051001e14092001b500b102d034218140909085010f80c406402990708018900c08912850040c1d41090306043c1e000103801c5d00031030 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 140600125 1250 140598875 140598893
    0x60610180e1608040201021213080f0a140a0c06050702010302040504051003050c030307020108010e0403050405100302190e030303060d0c0b0c0c030c0a0602070315060f12020f03010e19 81
    0xc038600c811110540490403a42001d4500e102e6014840704003010040740204030362078007003900c00074003680c480300c041c1c801210300c000900707104e40f010396907885c1c09955440036038500506803142d0300789a041808a03400740484d1002c0d44107541003100090035684101d9480f00f0301182130384219820001c001c614074003160710075012600240710062051185c3d0030000d403040e030060340900c0b04541c248900384841c1c1203400c0100a85011540507100c2c01c031103038a081124564140001e0084003003000800011405684100100405a40039580181c9929408204c0c1d0b0392006005965070521800c800c1c11040d542e000400c603640101c2c19a0740c180002c00a2605420040950708110707442c00001c11030f0052603100081c00906504106d040740c1020002500f4801e4080f182d00503100140c211441c24408210483c2c6100c0b0003110b2100e0010304103a54040c0c80e14500020b411611040780d0200400f400d500d00b01d043c00309031603812002000050012140140e40d04810700307014001c0c080b4545001d040c01000c103 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 140601375 1250 140600125 140600147
    0x801060c111017100605040e13050d0f1803020607120c0602040b1c02130308070f020303030a0b030d020f0601260d031e06080604150f0c050307090801020c060610 71
    0x9054071080e40034210002e0640c6140a070f01c080005524400202d4030341240e00020b04646441e15001d103400d0419a40405481c1e004200802c0303500350461006c0011810045050079600603a61551100846500204907000e81104c48520811468042c00907903111412203c01a80c4aa6103850144d84104180c4141e0320400010b0042032001c10002212520341c00107004810401041041807888200c8090480c0070f102002201400418418070000701a039006200d0a4091a03420340d0480b0643d0000f4555031040701c50300d4401d511545048050b0408020403801840380b4006010109614142155107160507c14800030000c83c03650780c218800744442c6600300a84403003d4696943c20180d010300900302d201e03110391721081c40d450b03920340000b0140305005c103882e4040301a280c0d5448a84a2030300d1065000e080c410526038600240c0744000b01845244400a03550701c8050b100e103080d1002800301ca4940c0c0c401080d590042000001c07680e0f0100d42c85511203003c40b03c1440c1031a800078120b9440343e02c4 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 140602625 1250 140601375 140601379
    0x210f0601170402010315030b1006020307050a1101090f0f0e0c03130320070306020a0906020a03020a06270f02040f090b0c0309030c0f1c09030317090c030d051801030501060801060c11 80
    0x2900010041c015511000c074450406078080c0c827841540c1e140c00300d075240301d00c400180183e0045a00351000800c006060514a00140350280c02d154580500e031550f44441c3e0310125210710301c20001c0158401800d510780d884102d80c0340250451034114004d0b04140c803210002020000031244000341c2407008010068201c006808823544a40c403840c084e8020350103034008001160141c10000707083c07032000502028242d4140c2c003611841c4080e58509028001da56060000800c0c2c0440b512580c03d040354012184c00d0060180c030741c0c604482c0c0144021240c0100000410505042d03141010580c0e034219036402013035030304280760703641c3c5c0d228134550440c01a0b640d2480c1500401d482808aa5800159028581a401a082ca540318990016101c2d40181d12009012070600144030b512034004140d6554440c407103d064031070710000f800010b800c081c00b00c3d03c800046040031074030000b00f201c1d81c9503107100040d0a083c20441541045005442c0c040c05202d88030404c101d09090104001552016103200c101c0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 140603875 1250 140602625 140602661
    0x7122703020c0f09070207150504090c020d0905120c0906031006080706090509011a0904111909090c02070e0406060e0c09030d030506060417030f210f06011704020103 73
    0xe140080d100c000145802c0c0c8a0203480c00c01c42e6092400612290040c0d81c903070010601c0528205000710750300c44143c03804003405018040010300c40040d0044620800a03540035150345112800042c00d8035241c0d0300300300c1c018004218140101c40000030b18030180d00049480c006559900d600192500382d20500240016042990001d0182c2c400600349040d6840d503128141802d490310f0a100100300700344200071452200780e0308980c1a06060b00107040c1030f400039101283c0c407000d15500c1100e681c010038007843c2401219800e5001190f200d811940a0030700710b4010f10681c0b021000083d40c8103094050009540c2340c00020501b004202e90140c00100610b40540c035942c5427484c0c403000c0c0c1d0742100103020700a018005500c0306240c0700e88540d030311544008022a05241c1044400401609990102e6043c0e1204205520382141900301500400401c01c0e05c203c2200200014641401000707460711640440070382c14000140e800c9824071103041c1000502410903030b52400100d020385039540321a002018 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 140605125 1250 140603875 140603951
    0x41107060e0307031b020604090908070b0702030a0e0102010b03100c05070b010f1409060a030308060d050102030109060f0e0412030f0209040515030d140403021003110301170601060302030712 84
    0x80043d0003814040c0e2201140f0a00c241401c0c22001092100203510078803c100904c08011554020f540480c011069582071036490754690920160a0b281c040142c2c1c004103403603195603400f6450010b001801c0c8006c0c040004824003199a0310403104900046984500a0000342d5101c0c2099440c03c580000c100d40065a5490007500090744600a0504061241041c1d00389030074940aa2401280c015080408072440c50300c04407443c5901070540c0d0790203054105042c001c21001d00245000c1d2101900001c1d1507441c100981d10031034050f03400001d8080185040001203051101031440c000f020b8100421200d09806c9044001c0c840c001c09264024645002d00c0405080342c000301c1e140f14401e030111a1007602a10065030003010404240130000c40401062005060036000a41100c102d400c7c04554242606050f0700640c00980252002400500c942046e0b1101000f00741e0040100d41802c5141d810718400040001d50880c1c50f0050b540c0c1c80b030360f4490f1a0b03240c04810000c1c0b01160002021000707 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 140606375 1250 140605125 140605151
    0x3150607030c030306090501080a0f03030b1003050609061203040b0304020a0905040b0a05101503090203031e030405011505150a0e0307320105190306080706030203070210061404110706 81
    0x10b00c1610107400092801c60013007500c007207a205540c1aa01c007200101081c00c400c0d0b640d43c543c2d0100351012020151100d040009545035018904103510b550740f40491b05160000c07d2007844e8070010050fa110b500c2c005401d01104c003000c41140c0990b59542061681c0390b50b1070000c99446035443c0e10181101d80390404110074095803802c9140155081d072000c5c00b081e111408a0301030303000c3c1400f92040400c4013140d2000e64030302a034001000341d44007030180e0b8144041c0007141d800138400d540710082003030030000801040000038030825854003014040b0003801410200450295140503a000c07580c2040052201c40703030f50180200c010300b154020200c42c1d080387c035800c0c42c0f003403410b949a0000c0c40a001009403070000360700b42c000032000141a0343d00360801030741100100360904070403508801e050342c0340710116145c101804030602520842e1000359403130410810003071030694241e41c1100c1051400500707104003003923118005140d100c200c902062403283c018840d4250b100b44d074001080310323107403081d000030035 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 140607625 1250 140606375 140606387
    0xf0f05210a020d020c03070b1305120d11070e06010c030c0b190b0901120605060a030b040b07090602010b0f10020304180c09060203040f030f0f0b07080117030c03040b0315060703 78
    0x4001d142c1d09079912118034a00680c3d80c3c0c1c0310141819495003150509020420a1601402c0d2005104016500781e40c6e8030300c040f501034001c0801025854002c906041c5d9500d8200304021010316068000b0440e69107803d48007603240c80b01900c805c6c1003100901c916414140b107240e685071020303008012a801402e201c42e120901100511019002c070742001e440190504c1c0c2121400e040300e502d030b0f00450400419a890900601c0024a5903510280890011011801d4400810312803881414500014180004041c10b01c00b000d83c8113104580c100144100c0d65280c0d042030384c0c0300f203105442446016040c200c05034114050b50300516490000400700d4141d1400340e4001074010003194030f17403071481e07a182c400890305ea2049009040800281d80c0c000c10004002d00710b10b021050182d45c2883c0013400903940c045440005503031000c0052601c00060001e0000c451401a1403030340c040c02140740ca1000c1250070388034029071082c04007080000c000583c000c0ca444901c0c1e42030440007044503540750058030700a0b181e = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 140608875 1250 140607625 140607637
    0x30c08070602181f0e040c17010e0f1005030c0111010f0e10050702010c08041113020301031109101d091207080d0516090506030a060b04080705010210090f0f0521 71
    0x1080d00c1c54000c2100f0b101c00d2901c3c1300303400c8034150350f0722070150200700c2804064031040c2d4031032003003082141c0844000c01100314840d020f44001c2080039158100f000424070800f0000e4109201c600c8404420001c9640c00606100a0b080030b00b80001404440800f030b500508100c900700c0441404e0220303040711364001107582031114285220412031500c070300d1001c13401c07a02a20030b14404581070401040104000030b080ca01c0c40c840045c049a0740d118003956240590b0400c0c0d0046031090040100c91740701d894070007801a40b1058503032050f05124075242d03014900c82070b000d000711001e183c500049601210240041142c0b41030241c20703603507a60302d189048603040d072000c40681c00d0580b8080c04180c4000c4180c6401c12241e02e0b543d40c04c41e0300380c149010801c085c1d10252004d030f00c840ea6400001a490300c6180039100402402000d404041d10740700000e800c0c03031000410404d107285044d4040b000902300202d40c10150760400d0f90040d668200d80760941c54001d900c803450720310500d0f20341d0304001d0b00c14240042c58 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 140610125 1250 140608875 140608879
    0x13030e03100f36060603080412030f080f011e050918100e030409050702010f0606231c02031803190906020303060a0603110d02041202030c09040807030c0807060218 72
    0x20b4440061843c40382143c48040e02628526401d100c803106400e0a201c01025809100c000800d281c0d687c1d11b40f0804e90007940001c00142c1c0040e080010726801c039504160ba00303520f00708280c50749420b070042001d000d014059a00d2004100c01c5103002400f107180c04001403c80542800c0d05410078400d80302c1407110102003030303685201d040341c42d603c0344226006803007210010900a42c1080d08260901c40507000041c05001190350360f24070b000b01d1065900500c00100300756107500b07094400305801d9104000300c90485c5028100b00704641121b4980300342c886401c5c4404107800503200d843ea0107000200c1070150761226128440403e1422070682c0003102c1a505244503151002815944c0350203a860303010440d001e035031200b485070381044100d000f5008440302807800902c880c50441d110808000700c0e001f030b401890004021076058011420108051041d0322002c4620495600d00b6035901d954512410320010104140321105108120909050350b042d00d5000c00c0a40d00c034060062504118062905894 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 140611375 1250 140610125 140610131
    0xf0c0c04150b03070f0c02030a0308044b0f0b0910050402030303061003061a031e0402030a030302090409150c08010506190311040509070504090501091413030e03100f 73
    0x448800c07024604241100c007000360700c2e41141e850441c15918690342c0101e01082c05906562840140d5061080101c3c851080d1904413150905080c00d00840c1c2046c801d041c0e4100244908030217441140ca040400061a917a4007503503404e04c2540203c0940d000d6100803362800600030104209441901d24440c2111030104c50803542c0d00307105034042c0c803c1a180650160010401704140f81172480d50600560201c0c10b0101e4416502c0d02e0701c110000c0100e00c112007000d0080240440c940e814151602d0f440801c10b4455580d007015000242c40e0540c090005041c95400943d10349141c807613400c0f21f14041e0304a9181c00c06c0008820340031000e030040c1c0d0031082c00510300000205e614a401c0d02526001c1030705180480703514048440035001410a0320401c901090113210006642c0d403200032442c49a007095482d0b5445a00d0074030030005031031040e0081d600c100e0030030031505191020707059015440103285200007280d05a5081c25209520081061600740c003484001d810081c21070381100158082c200010 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 140612625 1250 140611375 140611391
    0x210a0516031b050906060c07030c06020307050708060c030705132417070504180f0e01090b01120201021c120e06061315060320070c031a040b06040e030f0c0c04 70
    0x10301d40b0006580143c5600c03064403030220b07615007000c0c03004e0720614000c1812a0845030b00c80d00c4d40d04207040b10b0761222006a1000030b500701008410b02c0642c0003003403000300910141c01c1c054403201d81408010720850401402060601e9260081c000c1c81c4020403246242552280c07180d0b51011442d0008107034440030403000b0080c10140700358011442d01c500801c1c0c0d90642003505048a95030440e5800d038103580c41c0742e1078440d03215849045104105000d80288000580d0b2001e0b03150110020345e0582c00700f0059000c08045d4409030b60045004080d003200840c6443d940603c4040aa07141d0541c0750ba2250981c0c544121072101440000f005c0340280c000301d62541e0700d140c0e50b5002c50242d0740450721400390340c1d41090007004902c3c002d41203141c2c41094111020000038008174901d999130001413007a2200c1c03902c03c2d0700300107006100480c9161221205411600c5241c152640d003018900500f00da030140b50340e00c0040040b00818415240781c00c130b0021a0f5582c0380071024005584488216090f440b41d03181400d2 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 140613875 1250 140612625 140612663
    0x90c12050705120115020705040c020a0803130b0105032107140a03020d0e19030b040305070f120e04020901020a032001060b040513270809040c02010c1d210a051603 72
    0x3160a0780343c9031b50041282a0800c1d052101400c44511001e0035481801c0c1c64a0026030100055071141d00c07111210172503444d2034100099041c0301030f8052400b90300030440d4407210510b082c1c1d0000c200003107503034095031720890307840c6c941010301d0480c00c081d055028511841041540c0822b4040107031200d03a0b10826032240304400c006004510f20740700010042c140e14100001982505035507445402400c0c01410002291035504600d10045401c40e1890765400c501460680c01200c0e0202c4064191011420001e185c00040e5071000511405003c0c894201490841c2d030304104800041c05202d00006c2c840c45641c1c61030b140040e045400765520481240c0ca00404180ca68400c003402940760b030079440040d040c1000802680c0d211128241e030b00b6041003114140c02d4686014003038082c0d24a600014841d200c1c000700810380070000c5802c20001104204040c10399849417411a010080070070840c01617030328403404030326244800100a00a000316900c1c02e501e0030503120002c044034002c4807890074003c010030b9 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 140615125 1250 140613875 140613899
    0x60103051306091a1602060f060108150a05060c0d0201140702071505040815070f090b251406061f050d0902030c030a11040f05040804090c120507051201 67
    0x16415814980e90281c1801080103030300094003003030081d031041002441c10340c41c411000d581201c2914507450b4041c2c4036205d260f03040003040d030b000c81e810752003089906005000030000c0380042c00300c90800780c20203801d0140340c2e20095040002c11000700502d40da11a0480c000d03480c0e4240701d2a4102551070a10b083d0b0b03004940b88200c80c07040f009a40589199070a215815485030920380300e2404001c801d00011402c500d04000a010540d00c03200c0040700c038070b443e86004160a14108200007001444602003107010000c1040d15594907008000509504003203a104071121301c005d001806610402c14071b142c54503004510280189030580e180c14014010701100c103412b100308120a00001c00c10402c1500e2131203258407241d1410320040540d0b02880349000040d01d82485a0010b6440c1c003401c03184034549207130511412680e070f80c085609103c545000e80316000e82d40681d01c00e100e90fa646401042041a00c103480d905020760400760100301380d00702641d00508942200f40e11030741d43c08000b0004210034103142 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 140616375 1250 140615125 140615131
    0x6050a14090402121203010605030a050c2115040612060501051c0201031104170708100b03030409020906041502030d0b0f09060f0a0b120411040b011b110904110906010305 75
    0x90200007180d10381e075083c400b0142005107076030721500500300440c500b190184021802407140d503440319100e042501100c01183c4014104103544c200030040000c07100f034944002e1000c408481203c3e200c6548070409410080c41112040d540300d8a00040480d0000415194100d1240100c204101076a2240705001d4030415104189160b0316095030031800541c4613820509481c10350b6821241481d80d90420b082c800c00711074013405040e420005c41800fa84c2c1080048190050440f40203000e02c04200022a40300c3c89035000e91115260002505200d0362035010485005103000607580c008120038000003920380d04501d9581045900301001d000e05464610602038020500510512280d00ca40c4100040e00e6803140000340c201c02111000601c40346104041d0030b07017030140e1100b0141440c06282c0202c00c07803900020705108030f14000003450180d03802001c0c448840300c0360460088000107800c1011034040034000322a48103585c001040204101512840e000390b2051f54030400c1900d8060055060707482c21 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 140617625 1250 140616375 140616379
    0xc0923070315090905010f05070c030806030c0d030806040204031b03030f0903021c11120a0b010905071b050f060a060314010902030c1302130b0301080709020301180e0312010906050a14 81
    0x2e241e00780301c1c03009a03030700100300c4c01e224800028140b4103298158040d52000c41ea038602164030408003509041d0404000796020b5404c4019200341951a000140740c1942100e01500704440c40000401d10303241d41e81124080e540000281d9011405045c18244404d07140c003046000510800e85140e590340034903000000c1e681d000300060040c10082101c0300030f08104030429101101c800f02c4d00300035038407803944500141d01c0300d0015003d0504c03036044c03441c0d07a014107134400350107645814100005141d11031002002d0300701881240408000c2401c00510344504010244858040c4005100005400da8400ea048034030900951420080b2441928201c82072078030060b405030060441e01d412880e21041080010800903c01801c01c01005520b040c81c00c82600001000d802c000014048800304101d000300030711600405516641c102402403000c0d640100ea10b00c00300783c841c0c0e108903140b0b109006445035101044003d40b001c0da52000000003403c0e41d48a0380e0b001d4940e45801081820048030185001140 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 140618875 1250 140617625 140617661
    0x10914030a0f02070602070504050a020d060e09011103131416060e0406081603230604050c0306090a030c1704090c020a060f0c05040506130f0b030403031a01080604090c09230703 78
    0x8d00b00c00c3c407014180083c07503070803660383c00c00a8210201e5244200c6001d0311060038504164544031029600f1205c0d0001000f4170346d0b005004001c410074842651513402d95001d51543d141111042e40c0528105071750184554004c03894002242043c0c0c008500f08124000b198144a4203554803030494030384002c1544960f200345003d0302440401c100c0051100c001c0d0150f075000506c80040b000e12800c1010030398003201e143c0c200c0402c421007450104400e94000d480c0f5000781a44007090b80d0054035102c05c1c907400030280050324083c2c001854150098500400a007141030040880c241c00080d180c101c3c044044a07400d240985810341c5a420344546408080075444480c9080d04003000c108150b0082a20801c020107010408100f2444440303c010044c0306845405449007082c0c40d028056441528691000c1200f1184121050303074003000850b0007890a03140014034000a04201e016195181c11041d5002d04140c4c050b02c48240c20303100551151468101c0403080c0c0c03142c101c11001d455a18203202c1c00891 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 140620125 1250 140618875 140618879
    0xa0f03081918092310030b0603030d0612031404150c05070801090b15030607091e05030105011214030408030307181a1206120d050c010914030a0f0207060207 69
    0x54400c0d1001400741d42401c014040e034121480c81010740030103820001000b40c44003a80010011800c0d024400d8244880c0344e82c00c0d40c0751410316030400030140d00c0054000030b4030a02081441d14280304071404001821010f00c1090749500f00c150b10248108002c800089a0944180d2068240e00a850541e904011340035010000000708032401d0f40e503504141c6050040440c001511402403048c800f602d881007010014034542034200640c0844184071003030094110604201c2d080d07a01880d00c0702610740080b444418855a0a180d81e8010041d402c600d805611f81800881e42010280f5440c04951045903c00b252503406e4662507128050751141c00f413a40e00901c041440070303000320f8a82000ea566134118010585e951080c070110b40301c030340b400b4115403980025000b01141c07020704826400388041d5054149101c81109069980c1b403003ca410080110110390400c64000a4003d079141036002003012172240002d010f410749070b0748840c03140380224940c0700f10f00c2d02c1c1d140003245800840c1c0c4aa0013424040b8 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 140621375 1250 140620125 140620147
    0x2010b0105090f01110f010518010b010e06210907170c0f21030d15081b1201021303111215010b030403030e0f010f0c1706040c0201180b04020a0f0308 66
    0x140c14410140c0c14045c3c0c010441c80c04900c20001d48040c0d10000002160904065820008201c01100e4415103641401000a50b0380d0f048000c42e99032620039540b10b40e60781a080340c244600d40f0101d041300111071707480381400f11000c4005011010b803440b190482d00d00400580300160b942d6509404240c03c00058495030f92240b40680c4920801c002c0d80d084005000f08507454107096034040c1600c030f01410754410703c000781006280d024101801c9540002c2c81d400724100c81300035980300c0b0b02078500d10890030750244d541e42e9103081d0107481141e402d5100513140942c9038034100a644d0801c0514501424440c0350845405000281c443c8590001c003205254503403c0400d0000150b10040090701807688074845105071050030401e00000e0049240001086101c0e00e481c041a94401d40a01041001220200000d0042d005070390350002d0045400041001031391400380e01420210b4140d501840460103490180012030540611641c030880d58000410f40b12540109680c5903400050b1440c141400104101 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 140622625 1250 140621375 140621389
    0xb07020a140103090b010906060219050303160504080304030b010e0c1e070c150806100503060307140a05100c1707110f011106010f0602010615020c1e0a1403060702010b010509 77
    0x41d01041c98003260407401d684690f0a4044282c3c03007000499901c5004201e51681408042e0801d5198440056002d400d0341715150380c1d000240c84007508081c11782d020342c5280e00500480700200f5125007680c0e02c565403400c000a00080911986202100c0c020018982c29000c10440701e0901d1b12010b800840c8803481102645070f04206400c070307100302c1074000220703507882c4902c028007180034150384881061030200180440d290318000c001080c81004e0040c0903d6170f60106032201030782e040d4041a030f02203080c0c40c001586e503031141e480301c3c0c0c10041811f501c0c4415a804a000c051950091b01200352500c01d19080d03084a11070703510080c1406140144404091808082644502e1814076080d407040301c180b080c00e800c02800307038444140309021507401c2000c941c081c0114130007009120f04450b0340a40801001e91100c0d048070701144209984c400d00f10418a032a20480c40449015080b103080d19291410100440b66460281d48641302d11000580701c0e034414050322203440810f9443d90300b00040c180c240500 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 140623875 1250 140622625 140622659
    0x60801060b0c0a080a120203040609150b0a0524030109020301031202070e040f05010207050f0d180b0405060c190c06080a150302061b1501051906090317040302060c0114010b07020a 79
    0x800c81d124680d20601b0079a80080c5000754002e402c000303200c4103245440d0300b0501000d00140c0065040090529007643c13154081c004403402a24040384845603101d048980c41c00009100c11202004400880d440690307502950689210750290600e40381c01c1d42050366110031074400d13860000c44e00000180003c07051121088800c2c8500300241c01c1c0071f01079030307980d04000c501c49119410b03510072242c101c0100d90100c03004800e40c900c50f412140e80360415400b0a0103200300d0055038010075000031828450481042503440d403d0718601c900701c0c070403418074042c0c268203041e02c200700c00104400c001c102e03071150324451ba2407003042e45030b0003c4036203141d030b802c0c0541d40c1c11100503900010482c01d030b0740c0d14458003030004081002c185556001d540d8107050820074a07241d003200160030003030142028040c40340c00c16150002c2c0d98102c2209030b01e001c4140c54024140c0301715007000707400103000f2400c1082078105400a1109016038502850546c0e25100045c0c0c2e00c6c069480c01075481045000104181d0030700000e2604 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 140625125 1250 140623875 140623877
    0xc0112020405091609141e0607021210050c0a08180c060f03041209030203060420060a02030a03060501030b0607060509010b0904080d0501080114010303110703021003060801060b0c0a080a 82
    0x810540ea0744001100d00c2c0c0101c407501ca05452062601381015444549a80904000c000035410100d2000115000000c0c1803026900b0809100c035400d140c0d6106004d03118496802007403225403d4000c503c903900c0c0d54185403072181c1c460378080815080d400c0c80c0b0980b4508003103541c605100d692080007480e0082c0c1c40c0e040014040c09007884040c101d85528004290242c1c00044030f42e52401d091502c00760000202641c2c0040055404043c40107075800b0480d5600141c121803d00194201084100f040d04402c6603259400070b00090300a24154010001d0808880681c404006190382ca400560a890683e0007860b0300817400c01001c400107260b548029003007981500005140403550010030400d0406442c2902c4a00b4040740c00e207104196400340c1405031950800078030111100c601d007200034042c103000040038441d041d90842c6a09500708044801140c00501080d200162281c000d00100698004d0000325400c0c1440402c2d0f50402d142101c22050f08040181000480c03601c503402d82d82c00c0a050f100c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 140626375 1250 140625125 140625127
    0x10c020a171606020c0318040204080309060d02130909050c0102120405010f05090a080106030c1a030c070f060f0609240e061c060507030b1c1205090909010c02070b04080c011202 78
    0x202c04110310f80702600400c10310300c0042d41e40754564070307088101d828840d01c824030641c010030051080000c04001d8551820b000d03109146c5403013003034408034040e000700c5016541500b10030500103a031003015007040885038042c4003030341c05e5520752000483c3c941c0c420412014944000300320802c030a5110726084811743e846440c10f0b1742050390960010701069880d60040203070340e4407680c040c400d10002120340303c0102034241c103e11014a05031000c010301d01004188054101000c00d0304400d100b0750444103100070740c2c41502009540300c0c5c10f804500070150350184d81d81940c5001480180c00404510b503088049204400c411130602d80004030b4850140106080e8106228101070910401110044102a842140c000c40c1c28903003181c1c001c0480c2e4200c2a0103105944500c10911190364a0000a4605030084101909034090b8001541c140c41a0b000c0250495499000c2186400c01940000002e1a02d9401d03500e5450b40c8007848000d500842c000e03440c1c2c981220006102c1ca40c02040e0345504c15a00d40c2c1e000d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 140627625 1250 140626375 140626417
    0x706171b03070c0c0f090c020615040b04020706090605090f030405180711030c0601060318030c0b070212040b03060307091e090c0306090b0f0703020c0c010e0d170c010c020a17 77
    0xa2001c460040c3e0108400c0180a6014019200031f0b004603406048181700402441c6818500241300e0044515641d001d0f80d1380350000d0103e80c40315011100d815410000074410340103e40f0b070000040004a46104640c010b212035507201035008030403a01160002400384080e507501e040c04000510002d07125030144552003201084d0100c0c280f018001d0341c0c490001425182d072600c40040c00391080c2d0180c2d041d00c000404900c0000036002454242015040500455207584aa0702640341040c80020034844010128001840f500b81d80300640c8203a000340c080e600c1155071000d0000c1503811442c50b01d42c40013004035004605814540c03001c1c0106014440c0140b5860340c0341c96040c2283c10541d400d0b106c080b50031040008a00f21041a590003500b113140862030402c44056154840f0300510500341080700458041c00e1035a00c80500340d56407508108544000004010407100660040d00c0016a6500b08400102d90360b00114076004e4440d0040015a00d451064100038482c0c0d0000e07844480311041c44401d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 140628875 1250 140627625 140627633
    0x1140a05010318150b03121b0a030f03050406060803030c040f050301050c030c16080f04050909070e15010210020a02030c06011a070b0a090b0a0608070b0f09060306010c060e0706171b03070c 83
    0x103100008900500040e40d200300e0422099100c0c110240558009da001f810b1700c60010358041040301c43c442d41481c1c00145a103c80c5000390161031694050f842c0d41c800801404207240310080144211981050309100c140e42e100e05150036a0403c46001030342c2c540034030014085041500040104080300d000900085407141c2c1c0c0d01016402025245600b003101003028801c1d828030850803038224401d000242011362812a41282204c0000d0152142c0705019408113166402008850388022642c2c1c0b00390f48403000400c00030756a41001d403604842e072150b1000003507005d51803010184000b80c0744010928004603500e440000407805400801c0301c1396601c100c00037081c14a124140141403000b000b03d0300b01e00d0403032214035000302174000e074403050820442545007050001c1120b4940d40306507040e035226510500145c801e10361410003c1c01486c20a10303806801c00c000301d10907003600c5468481c2c40800418602043c00b460044540784d4401540c9103410001c1c4050381c0203154000224a04896084100d6032 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 140630125 1250 140628875 140628883
    0x1140105041e050c07111e0618060f03091e070b0a120e010b0109080d02150405151513060b0a120b0402070303050612010b15160b01140a05010318150b03 67
    0x40c48003480d0308081030040401c00c000c0051b16401004451803030228603d11b8413543c401c072100d8990b5104100000c0c5054502c41007001d890f24102c0c0003041140c446100d0742084c4002d41c801c460600e0075001c1e1a04030b030355541210260346065000100144403071402c0c516140a10341c068604175007800140c2a0310740f00c020b25401940702c181010000801c910003210b0015200c4607840e00000709a4110310246c103250713030b400206040104a800843c44950f1500c1c1040b0b8144804d0040c529078003440241005080c11900c6039400ca0141d003a14054206003200195a00715051070080c0e400458041103841141403084166900760b04250800095144261000500302e1340607a000700c002c82c0c1c40b2420018207190001c034031030900c06144000d01890442800003800704c1d0b21901c40c103070f2105001c12180044103545040107500c0e50301010300301c102c5d6110034a4054140c02c08043e54401d580c5100701158a520a00070039005140e51581c00c001d92041380ea8165040306104400c0c005956102040d1a0303d5400b04 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 140631375 1250 140630125 140630131
    0x2010b0d030e03010b0405072703050d0c110f0105030103060507020f0d090303031a030309060f0d02041d070914041a09010605040e0903090a060305061c030807020f01140105041e05 79
    0xb40b00c0103551080305050500351103824207000d110714907080c05c12801c02e4001f00616107101914842001c0e0104410520010201d180c2026001d4441e824600c180507030004c450150a500900d1446100d801910401c103460160989813400910700b03000400000300340c3d8005941208403801503038400320f503110703482e840c10300c03201c404074002900170700208145500743c0b11701d02c80321189584045100d1104e901003a500c0c400c00c84602e0007144001028503810b40d60006481e04804500c50640d038456403005094041000303c40c040303c210100e80b000c254480e0140030340900315120440c082035401482e00420000700458079803c0e118220000c0c4012595503102c0041e4042c0c40c2ca6207a49403150300304050395002100c004c058441c03a030300c00c010410041e0303070700140f40701151a07511700800c20303a55400104440400c1840c1e10060032403c084008100340d0024010707441107406500301ca10a2918000840c2a55843c0d90054448420301005000d14141600041481d4000241038080e24410450103c00c4400c11 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 140632625 1250 140631375 140631377
    0x2150c0a0f1b0807080c0d1a0901050a06050301090b0f090a0611031005010908061303051c0605040507030207110f0303070506090604060f110d0f0b04140f28050702010b0d03 76
    0x40141451034410b8610164007401c0c0007002807007181d040a10701641d82c804014507500c200541d40542041001614844d40076600d030040107086030401080480c040c007001d0300c2a01c072044c200000408c0600f4148150f44c003481e00b041503260300e5118191a20185180036001c8042401802c031000701064403405880b0403004e010702003540e6485c104100c00d601e40096040641040b000420400c1140c800160b1240c004000a5201c0203490461a0503520707072182501e220040d0b040c010304c80c1c04a05507984540101e46043c2d07800c0c007060307803240c138203e04911800000030040f88481e12091a5424070b141d600c0c4d0b1900e03001d81101d140c5007094683d24034044003100ca901c010b41c8604100420040c8078000c80c2c60910300350700c040c0440001c2280c2e40d4000d003c0e01030b00c503c07900d0750741c01d00e80344032101904082c04420024004001d440441901406900310407904408900e02100114504c26240200714140b0700607084a103840c101c0d20750b8840050107018088808564841980352082d40e07070640ca002483d071107 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 140633875 1250 140632625 140632643
    0x170606041d011a0f030f06030c12010902010807030b2101090c03050609070b120106081b03010f06170f011221050c010c09050906010e04020f070620040302150c0a0f 72
    0x15040994000c10f0480380c0710200c0c04024060300c11520200015250424030110740065680d0300c0c80003181c50041e010a1241d0b000614003544542940103500885065000b0b076a224196035a4000c16819190b0340210203400050b02e40704190041c03d20311390036110700e4030744d000402d01032659102d80d00040c0040d0029a0545c000380240862070004001200040c1842d4210b41d041010140408200c4a41441100180b0810900043c03070201040080e5120044500b0100e45035615000060000e0a003406a00c020402741d00c58200505540b0517040c1c49114141a0b5510030307820501c842400c100754450803120455880309020300020340b400c65021030003041d030b1101e40707402071110010b00355910718030000140108010140415100c490344941d20501c00c0c2840b5844485000104d0020722504441c0381e02c945000c60020100071980e04090788104640d00c12000181c0f04948800c124890361000941c09401030300022074115103a406090114150025522200c000b80c458283d8004044000c81300e0802e = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 140635125 1250 140633875 140633879
    0x307120c0e19030b0c370c1506030c1503020903060a09020621060f040902030a031b17040609270506061207020c0306010f03030804080f0f04060c0b06040903170606041d01 75
    0x30492211030008070146c00d6a80e402c2e160702c06565066070304014070410001700c00d000206204c0c3c80341220541c3c0d0000c23041005055541d040c15080301200b8080c000e0142251051540003610900030b48440250050107003d40342c89440c503c600500f0803010484c1c10100130f00031290000356214001c00001085c00b04881c42d403410400700a003c0c3d40d480c5026120350320b020444070242e00c2c005880042150705080001002204005020280b001500000c0c01902806607440360031401130003030400c80310140c9a455542d0380b01c441803c00c1c82d19942481d00d4255042c0d1a1040c81d00403600000c0d0000405405240340c0f44000c2c070060b160700c1045070b0000150b400300e80c5110042c02c0810415005144075a00d01c01514203584d401044181c0c043d201801c1541c01060340c82d420584003088500c8414800c040325900c540c1d45c8400350149403c5e90082e1410b2845c0400100d003403e02c0d0190240940e490b580e054480410200c0d00c242181d070203000c0381d401002c140804290340d100c58541040102e075008a5440d07030342c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 140636375 1250 140635125 140635147
    0x160c150209010201062c19020a031b0305041e0c050901030308040c0509010b040e220c1a041401030c0210020409021b03070807030f021606050307120c0e19030b0c 71
    0x54841d40c09020100d000d00f0006c407035140303150b08400d0600c01e00181058151500d411503500b2210400032600c00380d10001d0b41700001a0981d201314513005022160f040e810071200350540071100d0445010308609500c0008510040d401303080703a15601e101d49109281d00340c692021584901b001d800071001b20707440034188410b00c000c42c032020b0b00801c000c0761b10200b158144000d4034000c1c01075124803801c4503188000320380e00f803a1245030724500c5088002e81e046442c1260800200c1c0000610600c5090600382510341d96030b0f1400d004840584c3c2114142c0c403804014200110002c040424942c000c5001d9a400f0b0303000c1703142500050005200101015854080560401c0103004101410000c40d6208001000004104e070003038890450f09030132f00c3c00103880c0b01c0d58144c6c1030441c503100850041c00c0070b480110f496078200000e580244090790f114803085645a500c80115419500c0010100300c0c0103101c10f415240402c3c2040000b011050381070302c810b540e59600d89103c6002d48192041399404078480c0c0c220 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 140637625 1250 140636375 140636381
    0xf0c07060603140f01062403061d07120207030804080903030c06090102040501020c03010e060106030e0304090204080d0809010b0d0b0901020d05040f03080f010e16030e060405070509010b12160c150209010201 91
    0x44c491180204200d5180400700d00030702e06890012001080c0b80358500180d50f009900500050400000003600c45008550031001c0c51411200c0310b021984007448000c03000c0c80742c0b0a5031135141d0305072582c0720141c669032155852904403030401e503818032080180c00b4400109020950103000c1034400980c55a0401c400681840c0d40d2004441c001ea140810714001d05100080c10350450b007d60800080007215501c0c0c1c2411823003190080c0e564503000040c0007886500018000038010f8190b902c0391081d88801020500384d030650040d15600c80741d11881c03400850103042859400c070303041e080014500f030300c1c15458805030b07602220150f40c02c4803462040401d041d0000403065000100e803010b44c501c2d6050404070310100750701800c0d002c400c0c1001051085054005e41c4500080b170b5801c406c0f01c00d507180c189810360381c4809030b01505010b0a0010000902c0f07280c1d04d400c0d42c0001042080c0c4c8042a80d07000c64003a41e103511682d1410403c2621003808000c40c01c26094000203c0b800344003d84d990b41614001390039 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 140638875 1250 140637625 140637643
    0x30b0c091f020a05120f0904050601030b100e011b020306041202010e01060b04090509070e0703091a1302031c0f030e1203010b1206010203090a0e10050901080c091302090f0c0706060314 81
    0xd1503041141c00110080c006c211035626100711380000d426164000100c00a054810109800c41e1541c00554080364026009800c0485d09a858142140441c20b11220b0074000341360094141d84030101144c002101751404610b070014038400002d0f000203240c0f100f03003520790380c0d4003000555900060510140c2028003a40307500004020091904a142c031811424022004214008241e607590701c01d8100510210380641001490051005034209034015010f04040150200d10901c18062241107008290300803491000c11900c030601c07039485185d010340150034000078a03011801400e61465091000c0405103018080ea0429a42c68412042c0e030048901d8020342a00d041d980144962502591066020301c1a5040710210640d00d4450141d05e809030101c40e0403c0e54040001d5002090810b000a9100f4034100100c0b451105034951051203141e003201c2c98030117500f00a486001840050b404c1040e00c0e08407000d0303c2d4440c504080c0b43c59840c00c45905800846241c621100042c044200030020741c1c032 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 140640125 1250 140638875 140638903
    0x50904200d0f0903080103080a02030c0709061d150616050102030a090203061302062a0708010e070527090f0105041b0b12070e0406180209011404030b0c091f020a05 72
    0x102c0320f48241c030058000601440010001030740003842c550483d1082c030544044c2e003c03031021180b00603100c1070004007403c0c843c0201640e031034850030501400c0d500601c207640034400002103c054040313070703005000b555070001c66080082d010080c00c010000c0c4091008520400726a40009040121071041600b0035502410b5103003000b40d42c0900d1000344c1d40d05002c4900b401c00c0c07110060210a05800851302d070742864040380390340b4020500000381081064009118600890003911801d50322071040000d51007a00c0e81080b400d12007000720082d100c0114013000c0d004001c5100f210740d0690491052408e60303c1c2240c0880d006118400c040032402e802a03141800380131f09144a50820f00c1c811070001002034000d00d240c04106021080e81c40e181c40d10b50250004c0c080c1d0500083d0942d18641e00900a5404030305414001110746001010040002c0103031800d6a9110500324a5030f1500c40c40c80b0001c0c0c02c0207600907403045203801c2c14861185403440052401e070068000e44640301c01400c2c040d0400403a045040 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 140641375 1250 140640125 140640131
    0x90906010e010501080a0b1206061216050607020609031002120708040b0f150d03030623030307080f0906070f030906031802042a08010e010f06050307050904200d0f 72
    0x12040c0041110303001c2c1500c0003840d1030031032541c034081c000d0064801c140390240c021005001001000001143e070503c02c00c01a5000a000c40e502003d6a5480c0d442068003054001682d9080c400d501d840c000401585000500a1713003803541c81c00000b820081d906011082855000481c00800004030310031a034009000d080100080c5080e455121b010b071401045038403201d00107000a9000c0216812208005a01814601d400e005518ac0940181303540c0c011200b014801d142c8034948056001c0c014015900040c02075401c1c808140c1c1e80c2c0ca480c0c0c01520740b1129407181413100c000c490311560080c0590a0003882d80210200c1e59007400713820004150018010103084c0300c2035108030801641900c000c00d9058400054a038820050b41000c1d224222030089160501a00560100e612420442c180ca421030400b86803643c1e2502003d0715400396105d04008a003083c400100d0450055001d483c01d1200a070000c10008040c4010405c1a41007202c0d0030000c1c500803820f01c1d030504561248418000d4900070030 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 140642625 1250 140641375 140641379
    0x61404030c1217030a020a08010510051b030c030708040e090705240405040c0c020307140108010902030c0c0d08090d080f01050405130803010e0609071809020a0512040b0609090601 79
    0x1d40300240d800d014840d410005590014200b00502d030039251480d1505250b1a140d007019401c82011b54889020785000918500003c0740038a003419074000358802030f8030713060314202d64205080900601e079180e81001d80401e01c080d0204d610305000074060281b180b034007030f43da4900340444490303d20005404040c155000141c2484a504c81400c00340c2500b0841414034007140100342011114031480e04040d030081d0400440c103c0264000b58044400b62080b415100e6290f140c103000f21110426224240c00541c44000400010417281c0c000d680000101c20054a028240c1e0005850161101c4402d030004800d8802c124140d00140045580001070b850100300302c1c10440f59403402002c040c06a83d1040396174602054204091401c1049a19444030b9299225a0b5604120349885012070340c550041c0d005a000036603c80c0318101a807109500c254460b40000e0412903030800a402400c0e050701400010810b12190001001003030f840303144034140c04045464140e041c01511040a00101415031080d401 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 140643875 1250 140642625 140642633
    0xc090f0905072a0f0b151002060f07140703080a1109060f03130213020304120516060b0f0d050f1603120f09030f0308040201110309180405010e01020c03030106140403 73
    0x500031078040d080f0884995164804200a0003c094074802021010b00c000c2e0a001c000059220901c510051340c0d207091010402030078028160005607038240141c02440000392076240d5520749641013840ca10700100700390001050010070303621026082e0041035a0307100300104084203014143d1903003000c108160801281c0f00c003080380350061950100505001000007404081c1c16100c00c07100360340062401484c4004411000c00940c0b081d5010764140748004034001380b06002d03600711001103099007910760744000709480701401032000b01402d03544841f0050802e050340d0b5803103528268007801200503044076101200c4461500c0001d01d10311404070b00c581010804102c1c010361580a44005041c000d00344508200c0c116898a159007004040e005070001c5501410b41c403603039851040d80f00380c80b2440440d601d180b626980340941070074135a2042400440608040a445186422a22440002ca00e80c52006019826600000c0414070b0741e074000710040143d08e52040085c040342032042c000303908d02815034032 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 140645125 1250 140643875 140643887
    0x80f06030f0c0108150d0f03031b0c02040513050d0e04060e1003080c01060506040b0711040509030f0c0309031504021801030308060906061209030d0b03190b060111010c090f090507 79
    0x301c518144540b210000b408100b000c02c031082d17111401012440300168a00d010242c8003c07940b8190006850f010340b8485180e21075a00d20f020305519143d00c00071400b80e0f820440a418010b2100c0034840740130204000107002001521500c0140f0303107400d000e1070003507410300c4100e60030303680420101c010080078400c96055004104c4240c1e900041c42d5a55082042c49581c09050180d021070b41020b030004000400301c0e503a2014084c0180701d100c0c007071801c46103102040299441600c4150040c0c10400200062070652402000c5100d03508003038904102c070039030020f400c00030a224860300c0c1b140c19000708000c501e441e0580b02003151040c0702e10400e07541161001080e407140284600c2c00b904242003c20865510101940c0003156810103c0d0503078604140555200d4005407024a0340301c1c01c02d034402d030051401007514074081c014058001900e10154a4011180720023400007030600103001c0050701d10000a01403150000d400703071075006245145c0001200f1001d41c42d84941c0c0381920700300506c48000e074002 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 140646375 1250 140645125 140645143
    0x11b05090310140c0a170405060103060f05150103020c070e0109021b030a0804030315030501020304150c020a050a020904060b06030a090201181d060427120c080a140f0a080f06030f 79
    0x41d40749605c0d040d103c20244e0b110100081e020743c140880034108410000002400e038180d030f02c210030500054102c0084102030b01c00c10303108841180c07001501c10100354860340c041e0100c04602811074168030360300c3c40c1c0140c26820a03000041c4440d00060150020019401985035000b1900010f516046120000030f10569010304001c1c10151558100c4550007001026000659040002155030713041918241d2141020b0540741040d45080a8000038540c3c0049080c8540703941100103003002c0b0006508202c4a020000c0c4200c82132030341d501c3c00c005692210800f9620850040320006030764066800050207c0200459000c417a0303400403800e00c01a00700c10840c519426201351124807580b1088009030180c04c0f90401c403580c04041c03800100c500d00c0b1209220b407001d40141500a04404542c80403143c03803104220240111000300222540c041c810b041c049080e0180e070305880d0521984001da8146680b11402d6040018081d209002c0e0044880440f0b0f0b40115088000b04450301d002d60503151180c2900d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 140647482 1107 140646375 140646391
    0x15090a0c06090515030a090816061116060504050a021e0a0b030108060621010513030e0904020102120d0204031b06140301060e0d05011b0509031014 65
    0xa10340c400c081e140c0107000f990115a20302c0c00c488650740042c00c800300b01651550500086507683c0081d00700704e00c01c42d00308032011270300d810250b050364140c450141c00884c080104011304008040060800c66001c24041103e694508100341014011007000c4e401c00c0c000040b40802d00c0d1040840048410102c618542a03504c541c44045280401d01800010303502001c00b184040c5850250341c007200c501d4000140704500076124041c01d440c81a10340003508000a5100c4080607000b003c4132010b50010f5a03842507520780f640000307580340c4950010000760400084d0104074902503804980280d80c21078484041e4010000788074103804207610038900004d000200c0c0c9031001100760203c1e0304a03081d603900d1324504c1c02c00004020030300388200800c858941d40d0301c6000c0d1141e0040303855520304891688556440e070202c0700502d8200b40b800c4008882d03480ca440c0d0100141c041d441a40b07038110402c = true := by decide +kernel

theorem cover : BRFrame.Cov 140467625 140647482 := by
  have h0 := BRFrame.cov_init 140467625
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140467625 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140467625 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140467625 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140467625 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140467625 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140467625 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140467625 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140467625 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140467625 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140467625 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140467625 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140467625 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140467625 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140467625 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140467625 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140467625 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140467625 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140467625 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140467625 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140467625 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140467625 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140467625 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140467625 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140467625 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140467625 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140467625 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140467625 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140467625 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140467625 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140467625 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140467625 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140467625 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140467625 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140467625 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140467625 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140467625 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140467625 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140467625 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140467625 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140467625 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140467625 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140467625 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140467625 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140467625 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140467625 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140467625 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140467625 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140467625 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140467625 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140467625 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140467625 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140467625 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140467625 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140467625 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140467625 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140467625 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140467625 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140467625 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140467625 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140467625 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140467625 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140467625 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140467625 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140467625 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140467625 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140467625 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140467625 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140467625 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140467625 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140467625 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140467625 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140467625 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140467625 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140467625 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140467625 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140467625 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140467625 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140467625 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140467625 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140467625 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140467625 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140467625 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140467625 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140467625 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140467625 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140467625 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140467625 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140467625 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140467625 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140467625 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140467625 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140467625 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140467625 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140467625 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140467625 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140467625 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140467625 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140467625 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140467625 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140467625 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140467625 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140467625 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140467625 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140467625 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140467625 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140467625 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140467625 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140467625 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140467625 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140467625 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140467625 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140467625 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140467625 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140467625 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140467625 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140467625 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140467625 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140467625 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140467625 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140467625 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140467625 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140467625 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140467625 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140467625 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140467625 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140467625 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140467625 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140467625 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140467625 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140467625 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140467625 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140467625 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140467625 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140467625 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140467625 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140467625 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140467625 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140467625 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140467625 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140467625 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140467625 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140467625 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140467625 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140467625 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 140467625 ≤ n) (h2 : n < 140647482) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
