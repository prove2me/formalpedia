-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3913
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:02:51.479058+00:00
-- url     : https://prove2.me/submissions/edbdda78-4741-426d-8ac6-77c85fa46964

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 703597122 ≤ n < 703776978 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 703598372 1250 703597122 703597127
    0x6070501060806040501020a110606010c080c03190504140307030b0f091002040e070f180e07171e1806010e06060403061a010809073f030203040609240f 67
    0x5040d0300501c06801024248800c02006400400d540c420300e81d0727200a1b20704407d10042e01e0340030550f14140850780f40f01e00140011f40c000e025205012080c015a410b1818000d50300801c20210501070000400c0040d060100e0300550310300300ba098000b81d009140e03ca046076120b4604070720260081041407000000125240410000c3c4181151040010740d12195640d501c030031040025204500415000d4114540d05403040c0300c0c0d024076600a140c5141d1052410405081c40c030405005c5100b008100e049030700440400031001806003100700c0d280b0700c0c960805103400c0c0e145400507000c00c0908911036003000322008c001400605581c01404848800e4452200140b25849141e1004064604040760099503604602001205a500383c03550f80702542d80444060701d07011580a40030318120036007003a0481d00c690030300300354800c1500c0003408100382001c481d1525418100710300718010b030b20004052207a00d0b48aa1450020704140c0c40f041848000c1a000000c101159840c001c1000210040c407520f161 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 703599622 1250 703598372 703598381
    0xf0902031f0b06040315180f06200408100e060408031f0504050702010b0f0402090d06151707090c0302030105010801031202011104080f24010e09010603051219020d050906070501 78
    0x180003c0c4090b42e5541e50b40741050701c0001541002d46d000b46000140010301040804545110750701001e59041d000c265901c4200074007541148601c1410520180b0800b00340c100010405015180018a00c0d0303040b039440d0000f03941c082c0d01c0302802600600d0038480024441000e89400c4620381e1401c0003840c4400c05060710070146603101c560f200b400d007014010b20a4041d400f1056441007541c9044207112044203000a070701c50240e80b690041c900c000c080000c0390301035101e0501c41407000e15000482d0303030380c0500b40001d180ba200c4410780c980080c031042204000c0c600c5610040c100070304065003558900300c00680303011414031001c2c0501c4011001e4002443c403e512101000da142c101d600c0d02c0315160910300b6030301c02e0b10750540c03203152007001d00c000890300401c1c0319800b4003440d448039010280c1c01c0425110103030901820341031a640d00c805001c800944103011800d07040494401c210389605285401c5000c0000c08c1c070100056402c0f070002c803040c07103034084200c0d51804410741300240c1c2c0b0601c901d491030050 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 703600872 1250 703599622 703599641
    0x30204052d250f260117010204081e070e0c0a0503071116080f01050c09060901090806191406091609170309030d080c09130b060a0801090f0902031f 65
    0x10810001d0440030960400c2503d10100b01903958143e1440d0515030301460b500842d002002280c1154004001c1050040591400e42c50010000b41c200b0751780d601075a281035000401c640390100d0b440000d5503000020400743c0c1c010010926100681d06105040090a11444c0c0788101000700001c00104601e01899a030344003001c20104507092420520140d6514a8080c0200c82080c055240110304040b03050107098091500c600482d4540100c2104004551380860303001814442e0303000c00001e04507020305c84a4440c100711130300300e228040c1d484040e05c101c0759400d0106440c10889400e00a45407900d610a560005004c1540b103074444040c40d00b030301d40340380580c0b01d98030f81314194107841b41c0d9a0b0301001600900c4c1c07003038044480d000354908041d03070034200031120411603c01c1440b003840c4920b0f003030300f030301e810380740184800208500b00c4004910a40d015400c0c6802081c2c00c44010001c1548a2003014183c000101041084200303941c0000e8403203116102c9a83c51a0012400740304c4c2800e03560280107403 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 703602122 1250 703600872 703600921
    0x90402040b07301e0e090f06150a08043003021c05040b0c220e101502030901030e03090d05060f0a0612020112060e0709030204052d 58
    0x480d022850869121000c000540280c4000c04400f40c0c0780018116204140d543c183d200c403250b14000d05140c000356504403070b001e010040d036098041d10030b407101200c00e0300600080e00805250b2400d50240007a22481d83c4003454925400c108078950145e120f442c5503040755001407000340750181003204910480401e111071480c0c081d075000140c40c5e5a0150f00402040c101c20b06806001400d80c02400c1c2207620403217014202c0c10303008000441c2000da48000340300242c80c903083c580091800c4c103410080c000c42a0400c01c000c8840c00d0900580048030001d50001b0b1500403a1b249041d2860305000392640107000c3d80714141600c80310b9144003004180140c4421400240540c400c03c40c0e03500304690303150405d03105240c1030030a170400304114900d0307409004143d030b6205140d02c070071000f02d900444120b0300100440007416602d100201e140e010403c6102c0c015003556076154038582c11401000205c030406850800c2c001e1f0030701d01d01d4082103030301c0f800a840b150001e106c14000d507072010564902480300390707040da0300f = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 703603372 1250 703602122 703602127
    0x7030c2304021804060f1a07050f0a0c050f2202400905060a0e060409021f03150509150a090501031a09190b1b0c06011721090402040b 59
    0x5050318640383c4940074044030f081c40003d50303586010203400303094010101e40c0b9401c0011105610303c880000c0803a24400d904944407402a40d4080e23081442000c0129140109000104107034942707802920102d00040320358800b40b1031a40c4c14070b491503140c0c840c0c3c03090b1a83c01103032010020b080b00112110179907401c50521101c3c0004007500b25000c2002100c3c401411740000c0200e402c00301132040c40c0c402c40018041082480c03c0030141841d01078001c1215512070703158812940180c0b1240030003003411742c0400740502c03866585a006015150008a40c0209110031642084160340f007150980e0019641d00d0b5007140c803403014010400141c001c1d04031503411811b000000040200c0c03082c0d000b40e2803ca5491244003174076000807080c0c030b510040343c9041040001415240104101340300f80398200003c0120588010300c40f080e188025004030700c02c01416040200100200c08290a80e080140c00c1c400c0581007102002c40000c1c96213904c540404035580d400b0443e80d045858550489001c0c0ca6202c62054 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 703604622 1250 703603372 703603387
    0xc0c330e0708070f030201050325030515010e010e1003090b07230301030525080d0503100e06010203030c070618140f0304060905060706060e07120605010207030c230402 74
    0x38040640882826104030580002c55441c003045500c16a8a002400303014203280d60011030342c0b50000791403107030070740c443c1201145100505880040d91500548000c0303080e140c02c8480f40e4220103143c00182c10320100e44040005a07900c4910104045011030b2081c50307904901a00714014480300074000c042c40c400009100c0180d030080205c200031807d0580758960001d045025458034002840028040d80c08400721000b01074a00d5036100710341e0a015101580b445da50761049240140502d10040440c00000c140105a95601c5c3c1d114080c000030810600c0c217081c00b0000031364071f2200078207035034181401094500411041e41c2000703210305e00c216500e508000c0741d4240903008009001803040c162162015991160308048165011643d103034841032081840d140500040da8000b8008641640e40d88130080340d55401d520349640180107a45d20130b2041210b4015580131103c80d07030812815540701407400c10000d988010400d017940c1503280d540350083d1443d00d0b90361800290034145c5902500104144 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 703605872 1250 703604622 703604723
    0xe010902101707020313050907030b130f050a02040302060f13050315010501020f0c0f12100501090b131406060a021f2327150901050105040507030c0c 66
    0x80c01a00c0c03070341040200390f1605801aa5a03100301d4801e0071804030802030400503460100140c0da404001800d010441030004c07000140030b80f2100003110302c0780b80e80b0701d20b560300e819442c85416400040107004515150441e00040d005000d00551100d00b1100084e10107850b2030481c15070401440b01400300c03800310101e482560280082401001e0040c071609144101c032070000500324004000290540c454600464280320300920007141c480f07c18410840640d004e1183c2e403043d54000c04880000282c2c0c016070408100326030a81020b0303407100900344242d40555542c500102600010211121a5110b64150041c1d00384044d000e60b40d2608036001000d071412222a400001b600c644000c00042c0029080144568400c03081d603100c0200f80710072100004040444940d408410489011142803000200c00c03800d90b40d1085421045994484c401040340341403d01585400c903c07141003c0c40034098414001f09503118004002e040145001d22401401c01002000c041c064040032038940411381c0c14115 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 703607122 1250 703605872 703605887
    0x301030b01150201090b06100521060406230f121f05100e0a0905070e0106050d050a0528110c0109020a06080424180f2a03060e01090210 60
    0x4455201c1c80e80d080e104a40c0f031041c400c40070425405100c480f21901d0b5981403210b084080700a40042c071004110113260a440014180f826580440e000740311450400e00b0702050710030f5076000700214542500e203100400310348001c08610395400d84040c84c0017103030303140028007050382c1703c0e00e0224500031051542c090207844901007200303d0140b141804180c403040905c140c9100301c0d05c2440d40801d0440b0124071507442c05c2d0840043c440c040e0084984840c0c45d2103d07002c4242c02a40000d01181000483ca06004590b0007142c0d030120310010100440d02d014407038002040d0301100c00e20f003226854001d551210304903920603101c507030800041da07440d2030720044128000e00341c803a000e0b44a0403010600040c140d110f100d0300c52040703601c12034810450b1403c00000c02d1500c1c0c1d0100f0a83c0391510748032054a40b04c0d0010002081c0380c010380d40ba00008042d070500800d080e800c0030139002594145010340e00c5d88600da0744404201d03503004000081d6002d950080301d005083c10380000f03501800c607414284150340e0000a = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 703608372 1250 703607122 703607129
    0x50409051b090114010e0a0e070f03150501090510181707150203121012061410060e0607051002040b03090618060121060501030321020f0f0702060c030301030b01 71
    0x3104101d6940c6030801644500904c40d103820382246540d038207200d51060b0b213107501a0f0801351400c15003a0329074041c450021400c46ea0140010303a41460045069418000d5800d0700c82240340300658217082c400000c08001d0240078071800340803071031400c8240c41e2042030740211041103044941812600c4032845080b41c80920b051a842d44100403001ca1050240409004441480c2d0021841c0910b000f5140b04070f800000c00461304030440740800900111100c2a88885a203d50000528940160040028035002402c00601d652640409110b00c1d07070030030841403450b40d04680c3c490321140946031007440c0040700c510806546002040005049803442d01039801041583d050300c0c025580c10641403051003002c2c55001c25544860b00411140c100001c0701e0791102a2500d40380d0a000140c0c80300c6041c2d40083e03008a00041c0c0f001540c40324100d02900c00301100003e54010f51410781c03410200a60707400752000c40c0c400024000303512002c641d5140100e031050a54030b425207880703680d6400c001040c00024031 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 703609622 1250 703608372 703608403
    0x80307231306020102041206091407060309060e010c301b02010c0c080708031806100305070609050117060102010b030a03020705010e06030402060a120b04020409051506070b07051305040905 83
    0x820210b0558018001da030207407812108a43d00024240d00c0da0030203400c01c02026aa03070781130f030325150450355414070403034014029686011460320640c0c641002102e0502400000700c2c3d24006402d0800c992280402c00803a0101e458600d200d0788010305181440176600340804000c2c505254140c02a44806c1d01d425040f01d00d40003000600013401c0c4c20f4541c0401e11a001b00b03450010480d44001032004405103801040b804001da5a000022065525160041d0360719200e11100000400801004001c0300001e801c0f140f8000c00805d24100010707242030b007140030030000c1400030000250503074800d5104c6151500d00500300c510a490a09000e500c480d4a8002e0030300180750007001d00719904149080701e004603070103010b031032601c0b40703d200403140c01c14014095441940c94410080c0c041d502d0380007070800340824080004407070500030344100d840607405180e18002c040a00c64035001c2628055441c1e80080d45003081c4e9603039103900e108180b0540e00c5800059000e4a0000c1c40740a02c0340000d5118694030090 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 703610872 1250 703609622 703609657
    0x50301090f14030319021e1614010209180a1b0f020d05070f030f18080312010e1003030c0c030501020a110613020f1c020907020307031b050a08030723 66
    0x10303403900e8683c40102c3d00018802801742001d081d01c0c54a82c002c00c400381040005c3d40340212685403001003a8072260309907215059a80400c2e007804034180d4919900c403200002185060004004a00f103c02c07800300c032102c3c02c003882e000109001c0803a041380070925441c1c004200a41c07c42c50002c1e001e04103107001600140309041201c407841d40038000715503085411444564003e2110f503012111811010040d00403c08103d0101441854030b0314528042d200b004007458a034003c80e4589080c54805030302c10000112090300b03100c95015010b1040050740c0c0c16142030341030700e8002d007007541001d080c952008049620001d00c0d901234981c001c10005080d002c207001d4030350585aa14160030640200321002e50300ca500002c882040b4506a88000b607440b00c40d070903549102c02b10344c00107070440b0802ca51150250304005144400c05503c18804144010404403504140d241c58507240e655041d4954010507586000010925207070088840d02d0320441e00803c5800c285110000f411141d800c83c0c0c0c15014481d091 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 703612122 1250 703610872 703610903
    0x1b1401020c06040b070f020604080a18062601030b0a0213150206010501030e0c03152a03011508130f030c0f050c13200d181b0b070b0718050301090f 65
    0x1c0c0341e601b21015483c4d0080c4401c0d11252201d0000d0741c4050f02c2c0e00103011403500d08000d40d141e0640031000600c40c5d51202d01100a24040d90f0414103207400c444d0710032000b0303c3c00510000300401001a04100e229500613203802240140605400498200030158812851002502c5a001031020306079402a41e0901010340e19100c2665200305801030340c0d80c9504180e8405001a201c07a1002e40d1041a0305401c00824080b43c4c00010000c10300d084c0b0030600341d03000006000c40036082504100f144080e2600ea980e0b0318005882060200640b64018041c600c03d01a403c18584116188440e070fa070801d180352180880c1e407a055568038100280e80e80030300450a100d504a02042c400d841166084010301607004001c0c2511000c907501c41c110003e1003d1b0750751000041c0d80c0799100c1c4404454401e4103016511190245c2d24a19031810364802c4005070803c00c2070400003004454007540040e81414100c006120a080710302030040580c0080d03805620f001c49032401c0c400401c2c0f0741c4a20728040c54840380d00d6540f = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 703613372 1250 703612122 703612127
    0xa05120910030e0c040b0a050d1b05191806031a0a1a03100513051e0606030706092c0a2003060108190e01050f1509071b1401020c06040b07 61
    0x16144000c103044d030081da0700000c2609064200042e5118020540c011140d01e440024256800014055501c0e18400b07401d00b6030050390003003d001400c401c84141c0f1340c0d40408058000621824040c1c14040464540401c00000c00c60b00704101455100d080e40240c44220110403901100481c0c49142c50b07410a40320032440c2c9080300d0318507103450000c0c0c003820450b18001c4141c4081c040c00340045200c90f141c01d1400000c504240710f0118009000345c07804807080f54800b0018a051000303003000c0d2090b00030100800955030040054011034030908002410f404404007180c0c9049606042c1c04904c0258804010280310395078018045440d03180c150708440d500070192042d40d804110b0703401d03001c02e503450041540003060754610400d18500300c001050680020444da030a4900507982c10b680c0c220f12000303000c040282c00c2c902249500d81520100400e00c2c0004c0b0003003030541c01ca0074941c1d03100c10101004040c818020800380b48070b02d00310b000b956940001400541d45201c121003d460f071114100104a1052 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 703614622 1250 703613372 703613381
    0x290d2c0d090f12030207051305071103040e0411041b05130b0c0309120f0a240c0806040c0c08181c03120c0c052508010b0303030412020a0512091003 65
    0x1000e11440d01250740c200b800084010a103c00305034103620070480300054940c2ca164032000da01d0381742e0742c001c1000e052800c40a4480d010400f54040d40360814007003808128141c40c0c1c0701d644240c0040d01058491050000b08005003142207c4030b19440107520000a225040030003031615142e608048009142e80340b081e219a4001c0d03982c038614035001000046010316003070000450340f0740c1401c20f880b40108002c0e495442c060445404807068000d440007450031061140e6100c5113088503540030b00c040031008000910040380185030398880d139a03500b001d0040c0da108004540050740e00070482681c0b00c50104240b203440e1402588240300e444c1c3c00c10304680c8801c1d00b0501103140d03981612281c842c41104100003014110102d4030b80d04001020500d0b1010130010426041900c0c150241b031000001d03c40510301d01e60300c0541002505a040401c428030507240041143d50081d0054256502003c00700000c0381445840c3c04054294032030300d03000341c6040c14aa0002c0801d004129040f030a0446c2081040e015079 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 703615872 1250 703614622 703614629
    0x1a010503070b0417032106031005041e03110d09050306090102092b1205120a0b030c01051c020c07060207061404030201120f020a03090c290d2c0d09 65
    0x2c0b0600c01005040b40c030380880c0c012458504183ca0034002140a03115031078400341400e4008044070070134004141014800c40c81c854551900900c000d25040c1c481000e03081121304036050160040d100c4000741489510390107510015a01500d20411800800410040480c000c1c180300740210307400304655100c144215440c40d1000b5080190441400803807000ca50701c25510700f410168400119000103000088610041e031458407903a481d0150f1203240d1500340c9008105014140c0b4000c9a8038950398005001c03000c5c11401d00c1c050303940b41c6290f203030406214040140c2802c101d0000c030325010340c400042030030030a482c5681e08070b030030ac659241d00032250045942e00b00021b48c64108018009544035841d501c0101c426080080303241134041c0c400104a0344203201880010399521042010403002180302001496002c400e41c02d08403c80310203d400c000c800c0c038020007444001442c0c10301034482d504969510074282010024405001c2c0d41e0030541d84a40008907004d004042403072004a0080d02c009094 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 703617122 1250 703615872 703615889
    0x20c07031a0108060f09010e1009050105280e01020702100e100305010b1207031b0f09081501330503040c09020a091e05130e06280c110a1a01050307 65
    0x36403503030b805e1040c40510240a845881d520b501001489050811601e0b0248440e05800200401e090610303908440b400f600350300c01c2c00044181d000445100c4001001c1100312840000350380b0782002c0c0513074028802c84000030341003592002ca45008581028014a42c0c0d501542c03481400ca40320202201250360902403007107c86003e0003005014a48000c01561144050500082d82410904038205940c00011001e00091045520015459001c022400203204010040464442106e400e2441403414002c004102500310000c501e03080181c2001030302c031800003803080c42c0b4601c8020014107130349c4215000d646c40d100d44140003e131000c0a108951441c200ca40c0c600d80d43d00c1c00c1480d003503000f0729428130401000e410b00782d020913281c1d034a20021443d02c004040c00600138032300945543c00e140009142003141000007007102c8054120008500c15011210b000207501d044605090710200780c503542d030035030601c60f00c840d100401001940a01412407146520f141c01d030b07a00ca04043d5103034105d0240416 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 703618372 1250 703617122 703617133
    0x12050118030f0e060c0615031002040303020303012d080d18051f03150b09040e0106030302060a0e01060e01030b090618030d0f020c0f15070e06090d060906020c07031a0108 75
    0x18003a101d00c1c0140f00000004200f186404e50040143d4034001003919000990310302c280025880746030810408401c1a050709007581091b103581c078080c0d120302051140d0140c01f4041545840f0403803080c003c408ac540011405900d0441c0ca4039052a41c0300045d801c41d9010035022800109080c103001d0040048500052082205042081d2016818610805650f0038140c03544180442d404078013030301c00040d0175120400307504ca60082c402c0005a8401c85460600c50b494028140003095000c07440aa02143c0402c01142040400749202d004241980c000b005600040d00080108680421118084d103c3c1c402226655110031519148060305010035042c10340c010059030b081015190072404042d100a480141004952042a410300020031000d14454101810112020701c485c02d00c0d68105415180030b000b02d903078082c046078040c4a800346051080140540503410000e107500003010341e40d8040410f54076550024000340e03031000c6d6404107d5800c1052020303032104007205040d446c12204c03900300504 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 703619622 1250 703618372 703618397
    0x3120f0e0d02011d0405011401180b0f0703020c060d0506041b021b0315010303021f1e1802040f1d011109210f1c020a030f050c01151205011803 63
    0x124040740141c0703611150340b040c1e0000031392683c8a1043d0340c02494010b40000707110303140d0400101810100300034140d0308030302d4140910515294400751780c481e0f201d11078111350714225400c00f80d181140380041154441c8001030000740b103c21681225000d40700588052203a00034170640c03242c1e903090907940e010040c0d0141d2840301441f08203002e045980c0310b01805132589507020241c0d40d40074807800d820540140c0e100081c06da1404e8030401442c2c0603ca1221020001c401c0d2404442030102404422000d00e1621201001600c2112040801c507207903004100700481280916035001501ca00711003c0c9008414031a80c001500d0107000b030564240c0034800f45442e0075490710400152803928540b48480c1410500780408069041100002c2ca9101400814840c03111420170804105c04c281c255003107401490382e05000941006420020349224201182c07181481441d00340180101d48886c1d6154034003200020740125a00c001e07003001c9001d81e009001c00c001105202c0d03050500264010005007200d80c180 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 703620872 1250 703619622 703619627
    0x18030705011d0a24060e2505070515190f060305160503030d0203130b0c0903071a070b04030e33030601090b03040206070b04030e030f0d1706060f0403120f0e0d0201 72
    0x360940c640713064001031803900c41800030524002203607050071070501d0144605182401a0500c00c0c15501c914002e440e03c0082e560395602e42000e440150f91405144000c00c0d40a0341007a0306064520302032404010018030300d80d0031401303001c180c8000d0b00c440c094908c1c8000010001029201606c40182c0210701e01920214204000e50000b00b40c5242d00302e00d0014400060444880c2900480500300c2d05a19006030408040c00e0212a47c00701021980f0b01c190510342000f40fa090700c000e10303003100c1500240e036514202520849410507406910441c1c0c07400240005040042d0101c140900001c11100380003499811415480160f8134240401c00d0090104091b0b11860004c40d40584050140c60400a15075101000e00350161011004aa4002d004140d20b0a041021140405088000742540c0050f4074002d0014089100c011031104945800190f16449030002c9440c044a10301200755101ea40c5d081c42a41c0032070754201c00740000c1e2104814100a0721800312600384d050b00402000682c2c6003507005 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 703622122 1250 703620872 703620923
    0xc03091a0a050702030f030301061809020324040902041b0311040b03061c0c0311090609010315090c08151006020c03030d0207030e04090803060112050903090918030705011d0a 77
    0x1245c0c1440307201c110450303504007400910f000b002d0340c0d02c800c0300c190050020100c51030800d4110220107481481040303000b84440a068140c07c86448141c20206085004a0041e04090350080d41040c2001e403045589a00e0440501a00b001c2d50f904100e510034080140310903108510031078044400c00e001140d410b190803440354a4903028240c01c4e2441d14000d5442120280341c03a030055440d100e01108041d01d41c00d144c0503c0744d01c180c2c21101261590304590b01d1580e50001484503103d0700303699584880030405454007000141c61040d0480b10160000e00690303196800840d600d107044220304200085050001426403094640200618140940c2d010503600941110400f6004c101007540740354032039100e91280641c3d06015401d141d507603203041e4001400807080500c14850407440c12080004640c808010740d028131404a510404a8589480710220f40c00e070132083c05500e000024110007003220542c44080c185e0009602c503801c2d290b6600b5499210b41021001074424400e2445d4070600001c1c8120 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 703623372 1250 703622122 703622137
    0x1e0306030313080a0c08210c0f0a050d1b08040504052503200708030f060d021306080606100815130e01020909061f110114070c03091a0a05 61
    0x200e90500d414203080c801c500b4483d500806264004001d16000d001c0400c0102c0054440900105941046003821615044041144402a55002c108810f40c280d00384500501521400101e0b0440c011a003000340d21a000d0036004004a109034261540e0743c1c81100c43d5030f0700b2640000c001030a0900d040b051201900e00205580302490441121600f0582c041401c0c00e00905560b0700000d10301007410031056001e0f88480308008605092003d1000038203c60100c0f82e10102c41202c00b41a038a0702030126014401000000754842d141c8105412507140991158040700c0b1958100c90342074030750b0810b0040d80c00e0012501b00001e40c130140000c8202010390290058410302038480310b15501d29400c100e045845036031440d06540d400064068580c038104a100c2d0b001402201c145a402c00383d0b42c00000100c0b400c0c0726010034481460000300c8940001e41c800e02042e806151030220b20304c0e103c41c008021020284088010071f00d5240c01086030900e444480c844800380c01941c903d00020301e2001e0300d45d82c10404 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 703624622 1250 703623372 703623379
    0x60906030c1c0501090605040b0709080f0c0f0301020c1f060f0509060d03090b030709030b0a020c070501140708030408040305060f190b060702060d05102123120a141e0306 75
    0x18205c000040e0035128480c4103d0064400400c1410540d038024141d8405c1e42c0031480c2c0e9440580300c4e0303681e1003011941c01022402110551058012200440d01a00440303400d49071500030042c131a009030105840c00c09043c000035504101c51a01c3d40c240420021041c013031507801c0fa07000c00c00141c0394144002c47c00c0d0410300908094403200d94a0030b501010b580301b00c0d4a4000076000b408100208030340c00f40055040a49800c0030b5041904041407541d0700c1c0001d00c0340c2e0f030400c5900181d054101805a007200e0805070400a820303564902400c1c5140242d00c94402194284140790001e01009040032089005500540c0100482045040110003400c6103444103940800104003880042e51400001d10704810460004030311071030608000b061029240d4010421402e0303c000096081100e00142181c1d580c1c0a005140a0718070f080b040d040075007082031122424410f113507050484d40032450160040842030f0b610000021440310b10f42515001c0e41d0504929103403440f81100703140421802469106002a = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 703625872 1250 703624622 703624631
    0x11010e0304090f09050a060b0f090903090103050c0c030d1413150f0b04021206040e06131e080a03140106090b0304170c100b030d050a0f0f050f0a0206060906030c1c0501 74
    0x507205c0505040c1d003007038100c400d00d940760b01001c0d8070700340028003024583e41124131300400c2c90a001039035141d12840b070507141090f650340c0c00030302c035682054142c0307209071410700440342c80c1c907030300350100004200308040056a1200c031000250903131090b80000320a5039003c40b88642261030f00d00480042c1030010302c0514210f8440d2040300c0161240d2000e4111050020441c54a03030404100b0301044a02d2038010b0607050304603c0820500c00c114006465080398051003200140501c99088909103800c0c4c10b00502d030000c0003814007909a41500051024030220036010b00990ba901015603054045100e03000d0428010b200003400300758a550049041c0451401c014070304dc4030702c00860f04150002c2d581c81c60455480540c0d541509041042d0942064581407480c5040c000c1c400103455103111480c01400c205904034000c0c0031611810507140c1240d0b000d445143c07690303440b6070b01944a1f00100c480c14041c03202400010034a280005142d00181009043c2020740410079100b0600d28444c42e0041c1c40d07a6494 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 703627122 1250 703625872 703625891
    0x319060b03160e010602120a0f09050a08012c0d080c220e1302060d0c111b030c060f03010302010f0c170301031a0103030905010c0c0b0a09030311010e0304090f 70
    0x82c4107511a054100003111011800c1000d000d01a800c103170000d5086500c080103000c0711642c51400c41e40544020706045a0484004030b003207074405110341020340c0041d024032001400940540003070004004101d03090445a20519441d5100e021400390f40c150f0b50302401210441da401a100356801c007103a84506490003045021808007400c0c991424038120703403159000c0281c0840c40e0603c50f009003801035402602040c0303400066860149070020034100342d448008901e1a1f0240d0390340030a000e106019100710000c418200c664040107620042d0207402039404500c030718500081155500c400d55a1882d0a5900b550011030310319412410030030030300c16110740c0140403030240160215038100d83d0000035640e606624101d91042c0500d22000e041a120400610020350000d4031070050791801e06c0c041c9016080350030030040200780c5038000010304900103001d130101a0300145640030f507401ba45850408000c13010400d0300b00c45c0220032082494105100920900c1000c6c1c21083c1803500c0a60045601c088 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 703628372 1250 703627122 703627129
    0xa02030d060621060e0a020a031e0b1c0807060c090306062714150112090c14091b0a0302090405070e04050907080a060b0604031406010602070e060319060b 68
    0x75940008000c280071840100154810b160421081181c0c0701c02481103c3c03400b4011400a000603102c1000ea940200c4c0020305240701c0d83c0118422411410115211500d4072001030092805801c01801410840381880c121080ba100d9034500741d5201d50041d207040c1464464400034000840fa040401454010003c04031304940610f20161035030504140000d824a80e03c400ca960310410100600343c03c00c0c0710380402050140032a40d2000c101009800c0c0a0049401254a1040c082d04101031925100c1204c09000401480c9420398200000e5500c800c03480e00d080011011003110503070248640c1108100303045c85600040d144e26820b90501605024083c00081c0c02d64504035460000501c0700102c2d4520303440e15029254105100102800e0b44604084a50341c07610f50a0902802c0548c0b5000c008000d078881c8411200190380084801030310203007106025440e83c000b0b20520005102e210750210340a800c40c0d90031406180c0043c024070b1184c0d10101c40b18000c00c000320007511190394440304411580c4 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 703629622 1250 703628372 703628381
    0x3181203090303150409080702040c210501080609010b102303010303050903010b011826070611281203090503042d03031407060204150c050f1c050a02030d 68
    0x51010003079070300c3c0e18081c0c40040b0007a428000c20351203182050090404107407138008a403051501170310042124518084180e5070850903441e0351050181c0c0c075038100484071144d40710328180c80c590000c0d20001d032129a42d2500b82c46600030700b079502c000701c1100c80c10b02c540103654011102c6003012082100079101448824035810980c002c0d000304d240022448800e140a04c6540340050003401e00c0271842c0a181d21001050403540a08815060b41011082d01c10850050382d9009607410411200b01d00c2e21601d005283e10c2d020351401201e07104800030003240f01100111040945500c0600c1900900c003511448200b40300c1c1e0b4030034003d055417a911500440e00a00080025041c0344a810081c2260321030001440b107a0001319840f144c001407020700029034061111000607180b08501d0781c5443d0503050280085c41243d01800f4406125280142c405400601205c4594020000d135001041421051600e50400485600508175a0b2243c480304074010300152800350090f10480b82841205c80d12102202c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 703630872 1250 703629622 703629631
    0xa0b03030703091511060a020a0e0a0b19031a06070809040e0d2712021f020703030e090609010302010503180712050f07140f010c020904030309060c0507030503181203 73
    0x90a0f40b01c044c00300790000c12518031260032500d07103c088000126030441e01c40324090301681e00107400242c1c00d181184140d48491004030000e10807446141c0d540c0d650380d840c5e408261500f00d003100701e5201c10003450003803142d441459685504411039801c42c0c010003215502154046611640c00c0c001a82e440d00c462085140001c0401c005040d4902c403101d015040c0001030039072101f4452042010014032590452100898082c2050842042154030014101642c903140100c04081990000c50210f40d0000b6044202c034002d4880c0c2080f589808248030b01003904450041d008000130b03004200552040e0002c690002c04908a040c0e407503520440642441c0203a80302501121068103504140b0505003e40c4504020420041103282d240c00c110704403c0d141140ca65118140c01c09010080764002e428030758480c0d6005180b90f0980c501032034041d00401c1c11003c155045032807c0404e100441c003030003c81d100140c25454540c1103580301030740c041c00f10f040f0982940417401034a0130f070020342403528084e6005 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 703632122 1250 703630872 703630877
    0x114040510031a0603013605030708070b010e010b0909150103060906090f050903030603071401030f0c050a0f02010623030a050f06070e150f0c01060f080304090b030d08010b030a0b03030703 83
    0x69003130500815080d0340f140342055589400b110b440300c0c401c0c000049500b1903ca03101c6502510014a4100301d030440c045c3e0407000c1e02c0d58000089072010022001140ca040e110b08600b2603001e640c0302d0040d40228020301c000b01e034005001401007102c620780c1c221b1865068a0526011805030748400406040d6030455120780365043d210090f11504031440e0088a6003e000314009604604e01040025907404082c452410b007a0b081001c1d03180140d101e504048074118081c10240829810b91100402e20347c0407500c8140065003030b4151801d03182c41030041000b1a03000741005242d042c222004501c1c8110301fa141583d1510910006800149043c0955a10070701e03d1000341909150841002d0100c7e81c00c00860740c0b041c10642daa9440c0c43d1103904c19165441d6192828503201e07000c107280c60340100b5554200803941000824001803984001006005944890300d091240380c46207418035a40c0c0c1c1082c6440400310340510300600025410801542c0e001c0c510550110300200031001290841d0b0011006500 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 703633372 1250 703632122 703632173
    0x1003050f030702030c04050408070b0a0209100906020d03111e040e01120209090c0d060507030902121c03060503030301060f140d020316020f0d2f010f0c08011404051003 74
    0x154a024007220300e0180c810b8a0502032403410f681c80101e81d10403c0ae0080480403458041b465020003036059a22540d0003400389001c010122401504d03e5a0610030303140103100e881030000406100b40100f903200e82d09060781c3c03070074816000f80509000c826038080c0010501c05120001b8000e64089013103000300f2440e14a10a00003c41c014000e8444000f050091641d0204416010644407854074480943d00710100142d961500f00c41217000d03024405001e5480a01d000f0010324440d40421142401c0e240d880e0345141030f0710856401e40c291280c5100300c07070341904203100400074180100c8813150342485925051124900e03480c180182170704070405000c003007a4044100710000080c4141c4d030403001d407240000c2c82440f00300c0440c9542c90392019042410000140c4182844803d016403524210650402c0340c012059003505c2e00c0d0080900c1800b186e000b80c205000c889845008040e2181603a0b0300880e80c0d45030580b0342042c031001c0c017405044080051041e8400101240c3c42095044064451078024038 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 703634622 1250 703633372 703633387
    0x1020a0204060b041418160905030d02010b011209020108010b280903020310051303112e0606211a090705130905010b040e0a110c0f0706020a0c0e1003050f03 69
    0x2485c030400c040180303000303640242c10242c0103000070310031950102503081101d84070301c404507040f60b08031020760103203800d4411615403403181a0190040e4580f26801e076103000900c0c80c2141d811003595001000a070102d2000c50041c0700200a0000a112001c26150401e80b046e900390303000001102d022040c0700001c0c0311420b003071003146010300840400484582c0d041c4004e00300480c01032101e80c0c0c00800201030103541c24084154050600643d00c503851206214006050f100002c1041c2151701104e01c081e00b03180c00808154075001d01107400c40308000c07614040d40d100b003d54040c4002c1080f41c414403001f01b004040140c640c1c0d0707113056241c4580155651142c4901ca803103840001d80c04103802020602d82441c00600c40441c001c1c058a08948540040600d151030704c1d94040c0081203104041100014002403140b80201c00041c90b81141c440f0000301d548040d0f80703540c100c0e210243c41400421207004447c00300072001030741007100c0d0850426000da41103e81d581d078030785142c07090301c00c10410180c0000c1070340d2 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 703635872 1250 703634622 703634639
    0x206070e03060408031603060302130b1314011502030c0a21030615030b1503010f170a020f28150905030613060504150f0b040e030c0601050f01020a0204060b04 70
    0x86110003000c0e40142043d0406607149080c43c00000c00782d650301103c280040c1d418621a0304000c1c000e6070007030460058000c4034460400940b1801146602800ca81800348007001c80610540000010050100505900b40400c80d4035510403441c5000031480140324819460f04240400358645100700201d00b0032104a85802c000a10601511818503140500410240d041c82e24000f5800401e07160005085440780c0014552011049461a01032004000803540e5542d51043c04141c401502b102003000700740b00744d2180d5802484500035007055135024800401d00701444004d00e41c89585004902c40282940030300d183c0c403460380c00090600c0410068509071500810703140c010380400d40180c08207142c031a0031210001a889001000c4560b264001024403200d030180d0b035501d0b4007081e010b001c0a40300e4810b003c0039007102d002051080d443c11125400204000003110b001c007c41802401468cc41d1108201010504030a505d056014120034400103946520a0f03101034108540b407561103d0601044 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 703637122 1250 703635872 703635887
    0x1503080f0307140c0d0f120f0501091b020c040b13050a050a0c02070e0c1b1e1605010804060506030c12030414060c0703110103110a120f060b090f0d12020607 69
    0xf04804402000b0060440307002248955500e6141d00b41b1642035000944e088680205820901a4091030040c00980940305a00643e049499116091010307881c040e60a03549007000b881c1613005030303002e102c480b540350901c1d03003000c85003040003000103042200c06a8440141e070b5040701c0c42501c46580740104841e18a140c0304543e00329110f8030050407014144614890300c02c0001c1c1404141c44404181030106408407601c5641603030440059030014642c010b078004014840b080008114010b135110030301c4c0010010100012a01d0580d2082d09684560311200018040908542e0705030140781c01d148295110034489191a040620055586918240c1518542650f48601d01e1094400304188000e618002400c2c2d420b51350060403070b00156040d4001a401003440c5840e4801a40000c240c05100b6a0008801c140300c920400c001e02c00744000c3d0220300104d400d1406149035030003051281c030600d814410520741c041c150140030003403030b402030341c90740b00404905000710001a4000b6040121340d0781d00400 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 703638372 1250 703637122 703637147
    0x305040605010f0b0702010e0d0204060f0e0906070503011e031b0306050a0e15220303021b010b060a11011e0902181e270705040e07030f03031503080f0307 68
    0x407142030281407004a820505c101d401c00b90401c105800001c4c1030360341d048442c1c0c1c142e541c010010002c1581c1e450300303100d40000511400b030f00385034100c00080a103c03000c0b80f01442090385503076041c6541c3c20071101132042c424065016a120307a60340000700c0040e1544200302c509001e03031110905800c2ca5450644140c2c2d030002c20a401e51070030040720484040000800729400c20100307030504840c0d681c04a020107070241003951190703416010b11501c824141c0590060140c5240291a41d00422810740140c2c00d85100f490b42d11f800241c2007040c240820300c51240d81c581c9804003400490b4030400303c000c540040000c641d00880b001d0b40c80100c10210b1800c040c1402d61000301040c0b158103444c005c1c0650141c4070710100110005581c080c0091900e400c01d140d126018002007080c006405060a0023507035400060248900440c904180781e650b903140041d180013140e6000400e1585416155402c030301030100384010312507a03a00c2600c088005000030000d01345059080c1010b07a140d28010b60002d10a104850 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 703639622 1250 703638372 703638389
    0x612010e060402060702032107020406090504020307030b0c0d1d010b0901030305221706100b0f2a07032d020d03110f030d140a0204060210090c0e07030504060501 71
    0x102648596034000c200640d1240d01200d900e41c90b104a0700100307007400000c01c50658803040d42d4035061040d114410203071243d2402610100030786c44e124110310040303174015079019601d0341c401c10003040040e1010113210340c8a4180240e160421400358281000c0e2000c180302c18202c1c00c6060b1b980404540240300c0d815a44a0072035280c1041d51445e280507004d44500701c0700d034060480b45c0184010541d000c10400e40108040444120b901c000d03584241d4035010b040e140000030401d984400100c815110007500c0400c55010b01d046d10306180c50741c10746409120500848090000d1082580140509000e0b86c4000c601910008900300314040c44080300d0440da0b0780002e4030610440f00e40340561212060326032955418149440140b080310b0307240e4505040c00450380c00b58030000615840700001c6800404001d4440982d1449985176640306030241c0c0158041e07400103901c1400a00403103903582c4c01c1644454001c2e0b584424203622403007459050030084403e480440e0b111010700003005494440c680c0103000c1c44 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 703640872 1250 703639622 703639631
    0x3050702031b010903080d09120305040212030c0c09090c030f1c23160c0f0303020c120a0209070903050d03020a121a060a091e0317120c03131505061201 67
    0x40002e13180e01811300000d840c221000c0344610b01180710354048001540c00c81003480a83c9111031000b805003204450880c09041200420340c04d44800009946146000c0e070702804107104c40c0400d0181030500140b240000f0310402e0040452900c0c04c2c8000315244c0822070151103240c01c445e91182c5134150340c400d440e04100550408803105440c501d01000206595115507546411607484030920101504002d4160346846000090b405403907007002c030480344a50203032201c4803190301c20002c0341100041c045189400c45030384c0100510303060003842d600c041c880c101194515126101c0a02d49242d600200380803030360018480307180356080244080c8002c1014400c0c080c107401d5109d54800000e43c0b0fa0020301808000c00d03511002ca0003201c0308000b405848652a030202e02e00a08146084094881600c1040c0144c1c6140b803945011011658203400440a1211903188d920a240c0740d640300600d88111780343ca006071030b0700281c07281111942d8070440d8100803039107050180030085120000014100c40f41c0c9032 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 703642122 1250 703640872 703640923
    0x115170f0a05090f1204090e01090809101b0309030311061303110705190303090e0c12061201050708010e01080d2c1207140625050c0d0305070203 64
    0x10141240c1c0c0701c1c1031444041490780390500032a150211a0016105074019400031240d0002a04080d008503080440c061200c40b1400c505107089680100019080080c200200181401d01002a136500c48207072414940001540c0c0c9a461001c0340a102280050351803101002416842a9110180038164000d4046030a094508440440e01010003c0c1801440d0750b45c1400b0110900010004080140c03500842880d503403c646001265408114041905210041820001040001d200700b1044907060b1409005103040f8011901c010202e95202880400c1090100700038014507020f160b10303840e04c07045c95040030180c030710114058000b45c000e6486044241d1880e6031014010344001075103100c0c44a0504900081e001007114018556040358101030303a071043e240000b031041d0031a0f6070b80e01c079252a404a03504000861003128400d003084010710182ca440c1090b070442466409104504a548400001c004100c0081c195802640483c0021400d0010750805010400090311400e1594080548 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 703643372 1250 703642122 703642141
    0xb1605030118051f090204081e0d0c1115092103090d0c0f0303020609070f030b0a2414090a02120c0c010212161b24020f03011517 57
    0x280c0341c84100794030fa101c1e00030811002078584048980d000000c0c1e803018843d1111030100203035000740f15005452007014600821101d0540010340c00c200108090030000001060480b8048001c4009940e000e02c051400e02059503003442c03060b0640d031410348140d107504030002003146a503440038002c03182652030025814003002c00b2044441070740c02120450b2950340030b818161a25801a0440e080c4406c404e04003100345500001d015200d0058002118003c6403560290420015a0312004003028040004078094504542004000c101942c4426003400700c7c08004a07003031817240d4030002507a111140c107505981000700510346d1040501800f9460a1030070b1404401c0d0003030040c010360401e400030401010b41301c02074040305c00c00c00c0c2010207510309040c07a4106004501d56001c102d808541241d0340c3c01401002c0c010340c00c500300e401c2941003000d0380c0c00041e05038041c9407002c018000341741d00704010100d008254020798013070540e0f00006c58007040c0034180549903014807201455018240e0b001c1241000 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 703644622 1250 703643372 703643399
    0x120f02070e0105060a0309150204081b0108180a0204092108100b03091f0c0e010f0e06160f051509031303080a09080f0d021006061407030903020d0b16050301 69
    0x3c2d01620480da5030303c150903003103004142d0004020422540aa040e4002d40ca6039006002540c200c0301c1941c9800131200131200000110001090108102d0000500d002c500f0006180b00380032680103840750000c05a001904a4213440002c0f60f0f480300d00808000010303402609129200c0c96414600941e0a2403490000a02d00620605440310030000014441c10310074031850f010401c1c0c420001e04824000512400a002d40c00001c0e0006480c40c0000090ba40c81141c0030200402a41c950503032080b0807000b44500c035030000403420786504002c491440041c0714846a031401c1c40c00703075010f000daa90303c0080c40ea041507009042c2c086a82d10078001060310162174201041140c0c1d10420540c4e540c04001401e40c0e580398203034040c44142c05420502c404203500800c00e202d01d40700750303030035641500154420502120f1590080c9030014400020345c030003a000e008010104039010781448800c850752640091810300d10030100315125070b880400d01982c601d5a0400358180d044a091840c11581009035061807030 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 703645872 1250 703644622 703644629
    0xf150c09090903140309100b0117042010020610080c15071a01091b0f0c030806030a210207060219020613050307092301060507080309100504120f02070e01 68
    0x140d52a0b03034110405004850304205407403c05041e40e2a490141d50301915500c0403100d081410341800c0140f00706610507610944254148480130702ea43d111600c0f0226407141c3c10b2550303070842da19461094029544d07248150b680408580c000e01842c41d01d191000d0308440300b5409100503902c0b0450a0b4010347c0c1d8618081d65030507903594103d0f1561200c0c00c0004400040891061040d11150004200c006441e00720f095800580e04503414101302d94402100c030b44c04c203458030100007010781c20310704002031103500c0c0113030020300040407240720f014035480d03581c54801a502c4a0040c08404048041d80640500c20340e0010a1180058100346405580c658480d104420000b0302c2214002034000701c41408400480180c0805002c958027640c0f1461440c0040c61101d1841103141c3d04400000d1041c1440040c00d07050728034641c1c405040400503642c80601c0e800203400c042d0b19000d0070140352900f618501c0f03407610448c01014200b04206140b103010b030101d11b100a100085400c00001484203044403281541107 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 703647122 1250 703645872 703645889
    0x50706050a120207030c0b060d0506011206020f031f060f051209010e070b03221109060619121b0e01140408070e0103050f0304060f05070c0e040f150c09 67
    0x688494840860310710610781030041c0d8103840030030131206150344203484a0340584a1152000c1c0c42c2c03200c10821030900174200005104c0e40c8a9001402185100c0311184038030744c41224050b0034020344102e003d400d03800c2100c450380081030841c4000701c8a807400440c140103100906005104425030b0000520768030904011140c03207041400481e128050035030180012003841019600100c0c1c40c1c2408000b1079105407001c0796a43c1c40040301c80348041c4060460b080c029401061034454000c40f400784180c03985d0090005038007501c18003c601c0714071582c00705114002455500c00c03049050130b244401c103c8003c04110f213604042d01c0003085513690000099203080909003804075000701c1e40652000c21307101d03035000f1103201c2c09a0440011031851103045036040e41c0c407500030b45075120000d240680d5203005a2258400040020981a0300640607030001d12505000782d881e09002c0d902d41c004070303007109401d840031901010906500c8062007840740d40009510002c0c4810b00c89641d00203801001d840d447e00070540c0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 703648372 1250 703647122 703647127
    0x3020c0d1101030b060408010921091d13050f010609050a0b011b0819051327020f04030f08090316050a0e10050a03080403050601080c09010306020a0908100b03160305070605 76
    0x280c91790b422069a006181c480000c0c4a484418500007100400c1d0424201211108009922069000b60752200565044002c2019541d41104c1002e03c0071102414030010306610340b66840c0032032001c0c809040c5510b1035000102da6140780403d00e40132900300901561060740f80c032020800c1a80d00141c1116612100c0504000c2c0009170306285005104000318080720000c00d4008080701130700040980301c24043c2070141c04400d9a01d01002da000750458901502101c92000c000700300c0c502680c003620340c003800310000c03d00302a100c1d40c83c00180d001c501c1701661000c01c00b040c01e61007407030108132480c0007021158151100d540703020007040d400d103014002c04100d040c4c03480025401c00b1010b0804002020018802808591340e41044061648a804299014000c2c0d03000420103942c00603500d50303078181c041c00c0148980e285448440080d009112030008000e902800003070328200801c694001c07030342650000245001e41004140c98a0310080c0c46050107002000e042000c54804201700307007250000d050665 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 703649622 1250 703648372 703648391
    0x180402040504060b060d1a0d110607060e070b070b060d12120216080c0d030e0d11150106030b0a0f050d030305060d21080a02070c0b0906040b03040f03020c0d110103 72
    0x280502050b120582c2c0140000c00c02c00340b041b00f0790700701b0303450581409039800d06004020305000082c40301c1800506404400c81c20550542000001000c00314000e1100041c1060040c61203410500d640c6d014940303107180420f80e1800c6c0845a48003030b0304100112408070500c01076a403261005100c0081100c140f00440200e400d200e46180c048802c5d80070b15110b0108544071500e04461181c01a0b0307040c1c503003481003c0c041e1001e140241700d2203d40050f100c2c001c0403e01010a0100c5101494003000030550007a8030307401000070a00300b0003034040c140985020400041100600164402d01d80c0280b94480000700100320544509240103a1a0b03054500415240e4603140424580300d2a50801020341408000000d50b070706090407411100c0540341e40c2c51a9580351506400c06a000324100640030b5403043c2c40800c070380d40c41200101010b06016020504096079990110396a03001240c0a807a4200590f40722010194180003244400a088486203400002e030380311000031844c03c41d80b8a061655130398404 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 703650872 1250 703649622 703649633
    0x9180b1504020d02030f070f02070324110c07051c0305040519030f080310060807270b070302030c07091401090b0a0b03070f030b030c012a060c020d0806180402040504 73
    0x2600d0040c483c45003550b990400d01c0d049003206104941003c001a03a29840d0b0321840d06c0030a0b01c00489402843c032200d1120041079100d00c050001203014040c48daa0200840154a410081c1c007900c44050098000a0300d80350170700c0206240c126043c0c0d040a413003210320000a800009480540300150380310b0007074480c1452246c910b43c1031500050320300440c035144c8a0400c410403000358491500480305c2540143e4a000907101860b0694901000c146a0f40c109000110707414000366440401c01501180280e5410b8900a144d005810a03001600009440207699004010107002032040843c01c010b8280d55100000010506010b0088510b84800c0c1149aa54a211211018160708207845a8a0900f0308002d440a1250301c0e1000c0441c2c281540542c1d140740120300b42e500305006840380c281c800b6000c940c062620419801d50100440304d00d0350390340460a54881c0740c40d07662040e0024280700d042490003500404005003000d1140c022020a08042c007510071841e60040c2d4141c8012030241c03141d1400c3d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 703652122 1250 703650872 703650877
    0x6050a021b13090b1014061902101104050312280329031c080c0d091e03080c270d020d121205101a040b040602030409180b150402 57
    0x341d038402d604010855060001c1484460b01038000800840e207656503a100034071a4056514980c0e920900c14462000e1011500741d100c5d1441d90030b44159171400b410780b2918030031281d4400080300341d003401180c140700b14102049561496000704195906248181c0b42d00c440d82c411811a8140ba00c00c40e0b800d114003207000b9080408030482c60700a1058401140024102e1248040140c2d44a407080030400303448419520b444003080c1070f090391440015690b408400305a81d02240c1c0c0d541c0c07010394410703000000c80c400d202c0da101c585c802c80d15580c21200840c203008044100180c0340c0003030580100400d00c00b00c0b03000300f00035403801c41c0f46078601c2103c80c0788800580507201e04140650001524150201001410116020001d0a640f60a507104143c04949001c85008650039405602e104105000400610891280081d0307001c2510b40340a45499094a00e904598410b002580c000700341444089201c0c01041107e0740c92203c0b44200c5041c540394000714030405800b45402a214915040240e100c0307804 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 703653372 1250 703652122 703652149
    0x3060c171b070c0b0a05090406051206070e0a03020607050a120809031c0b030105070215070216090e2d0c090c1b010e03042d0515220e1006050a021b 65
    0xb0880c0c9900705c1400c0a000b40c2c5c00010810703c00c40c60200041414508444410340d003510490091056944d190350070340781500881c180751751100c10a0070000060b030707900e070007815078501c180c1c054620a8114501940c2030000d400f100801e2242c00c80402c000088000b00380d920154410580c111041810f00034440140301400185405500f002d0400590340d4001800c420108903010310341c0010b81d107075a01243c84e05021410301d002816100303030420180804d03030081803d070315000d415110300d0400b44c2c00b00492140e802c117144114078140d0340c140024030001e00c04201c0c0060191140c455038548803400076494401c0006050b2030b06407007103105588180075400303a80d08840d003504503030f501d40d2201803014044c81920010000d18605c64440f8540415502003031003164030150803120048003011429019030003020000300c40b82008042c890b0511020402c10000b03281003d40c086042c20511202541020325800001c1440f00400c500103140307500252202c020051000600254844a030024154240e90607 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 703654622 1250 703653372 703653389
    0x316110a170607031a01111603031710060503180c1201140a06050607152a12112b050a0b010908010e07030807060b090103060c171b070c 60
    0x10402440d41c01030041c200480000302d800d1651400402c8068a80c00c240240a82031410075200265025081d5541400d20803825124585410a800b9050301404d52050f4002160100c0c090120076600802c03c1d04580d03418551961103082c020094054800070309616258000100c51701031000707007400078812120008040030b42280750950018041d149104600007001013032404100c071031100d840341d8821140c01030580350811546458401c01035030399420701c01c10284c84840340380c0400c035022100c0d115002d40180c4c40700d940c403003c3c1005041c0d00c100c1c503401c01c5d5185410302052010301c1e280300f50742c0c07414082541c501a09001403085600c1c04c80c0c401e4000d001c00d05000134488406443d8001018166007a640c00325616540c1c10314500307039007801005200d1600040070501c0030a20b620010310340c0501800001c00c0507802480400c9504009a1041e0380303080d9504108940b450b40510311036400703040710303e01c3d04a50814000018141c0c482c0032540301c010b4400620a4100151202c00b04014803480 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 703655872 1250 703654622 703654639
    0x60103030e0f01020604050712083106020d0c060b040b1c050c0306190c050705150703110f0405040c181e050915090c0408162105031611 60
    0x3440c01400c003503611115280b045848100c080c0c09544001466449150400c0003405440d16180803003601c0c2210341d1003a10301c22000c10805146841d0304500c181c0014040e0b0300480000542c3c84920101202508030a0440d001207808a00c0c0b1544010120b115a400c01400526506050002070003046400c804070303008411540c1007040101c448040001d054081e405444440d100076003019180c4004070b458030b000c00885580e40750070403423590000100404504040d4542400c540f80c051803c04070001c000d01514494003005100d42c0d2500515450a071504840c81c10b140030000b226800c0c0c01240130b130601465440004208a070320172041d540006007071002045c0382d50b0b00d4852541188400c49515034030103450107000120390600d0b41c05240310368003401d6401c100b09017640c10031510010260002021100c00c0c4008900c2000a001d40ca140240303010600e07210790b107001d404501039401020ba075140d0b64501c11a60001c1400401111160414919008001540c9180401441d4100c078a0b807500110b44 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 703657122 1250 703655872 703655879
    0x90d060906060801061a0a0207030f0807140f100b040603060e07030308130807020f03070504061502060c040602190c030b0403050d1a0f10030906020d02091f2f0601 72
    0x140da21126006000707240c20300c0b101d070b2070702185801d035007a6104010200c02c24843c981007038020b0b9005001002180d02c191202e07241d50707031210341c01910b4019041d1400007001034000104500d40d0748803118600248098040b44116040306911740030400002846503440e03a00400c1c4036034035075000c9800744d80c0c4120300300042e40c005c5072001e95038000c074042100400d6070000446c0104104001181c1c1a603881002c06107003070b4007035083c13004182c50003c190b0741505c2403541c003103002d0743c1e50702030741d400f406174189602800a40620020303d03000c0050800c0d83c8803032007004284500d5602080768544c064518901505250440c545158104140d500180107080140300b44000c042c0e01000a00c1e41010a6078217200036802a0003000d0418907104a00b98058000c80006000f400e201100e243c600178542070001340d07403c0c192500000c0e03030701c15801010a107500007030f02c124600e0081d00110580050341c1c82500c01c00e52280029000c2c0c024180026401000d208260143d41c803403000c1003d201030001c05403200395070b4 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 703658372 1250 703657122 703657133
    0xe0f01050106050a230301091e050426070503031506160302011406041401030210020102071a0105100908030a1d0d0b01091a220b1807120e0a1502090d 66
    0x12443c50980024528000b1801e210178210b500b40385200c124801c50b01c0d503468107030030100500401481407440d42808100154114003441030030700ca00c2c0110079a00c0f004126444241110b02e4500081c00c42071014040400440c0c0c002052b6513000104902c60b188042c03244000403070034024001190802c80d43c0341222020980e06411000d084442548084010b440d244204000c2e07848058040c0010705403134004001610b44039a0030729038090a4000107140c444035460303002241c00f1700d0100113080c101010040202d03080000000320b20341068585140782d00d003040d0b4255100d22aa940e41403c000d898921241c00c4200ca038908844076400814800c500c05a41c0782480481e4024860700d0b0350700c1d280482d02409000810062090b581d00100b4803100030b240c004181000c460a62900c42c506680d510b01803500e43c07188006404a0940c2e421f080c4c804e454142d9005000150850115440b6400c0000a03d11000001440390b000743d400400080b050911500280090040307000700d42e4802d900c59414800e210 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 703659622 1250 703658372 703658377
    0x70f06020d02060705030105030a0b100f03060902030f0d0813150207060b011103090604030215040f06020a170a080103030c020d0b13020a090203060f0d060207060f0c0318150e0f0105010605 83
    0x1c1c0e503003d64221341d80c0d4003c20b071400d020034400e254158002e403844100080007040f01980c800300001075600099110f07601c031a11441650002c07074420f5510a520b4080d8601008984802100540101108000e414009068040241034042001c0d100385844c810006a59140682e429000c1170854841c04181071035030140a8040310300f400305404011404c041500070080b640944005802e0603c7c161441e801d118603c030710381840c204208400e210101f4030716907200d0600001c1c01154024011192a4200301c82d1132501c035000080c140c8400c2012594054001185078112a09410904100085ca0000c260250342280300100149008810480d016074880520034556009540e0010460b80b02d03101e082c2248000d68500b5444690404107450a140250301038840303074841d0f0405420804030f69514425907603078413207002e0304a4440618503401581032241c41c060210950907044180c40c2600c4100c44100164040b05509469046104542c07008111a00c91198048000c00182d1707543c110040194 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 703660872 1250 703659622 703659643
    0xc030402211f06092d0204030b0a0e0a0204060f06090501020307080d0c02070b07080d0f02190e0321040608071403070309060f18170f09060903070f0602 67
    0x90040202040306122040840c08001422200404061080d0103151000c00300740c00548200e292a002c01080406480c0a41700f00868400541d00c0d404c800c07200e04950f1156019503031400d5902c1804100045001b0301e2919400c40349081001900b42010303164982041034036807020b500039060480c001002600100c01500301d425039980ca402e050703155401241c0345d120b2444003420541c03040c84603803828a03095110301e10203d218011a038607030341c2d55502500613400049081d5071a030741c0800c1104442c20030b40102a440c0c00518000c62034a032012550500143c40401c40c03e00b00301c0c0e0502486081e0f1010005a409613000140d0444070085581d0540740701e52060240c10005920400480c0545008900b50300711003800030b004504640e103d80040f4014521104103039400ca8030382c0001d054038281d40c481c607280f41041c0b294400d8030b100d0702d050500d81401404100d60002c2000c0014140c00b51170001035a14003801200c1d1903070341c4d00041d0000380c40c142540d08210082d80d009000001c21a40014011503003 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 703662122 1250 703660872 703660879
    0xc0f110f010f0903140c030f030c161203080406021b0303040210052d12090a0c0e1509060d0b01120515060d060e150c04060801080115120c0e0c030402 66
    0x80a0480c0111802c10000e800300c004241402001c0c000165200c520001c00320220013190b051014201c00a482c01c4c441004442007608006140c117000728062040e40c08480c04881159252894400008103903401080c4c068208107050b00072404000580e01101ca160804207491079017a2454080d241e07c03588155000c80c8900c40a0300d285101d140202e007501d00c07090441010071196151610322908210040c2c0a80ca0000c40411243e05070100039013841d801150f4800041c076046030603261440100040ba0018200d0300d0940007008250050301d01a50b101c1a0b064a07910b00b01c0d180e01d40071440c040058040100004220030011803580c42d6030000c1082e40340100110b0311140e004401c00880403406440c45a00308216011880102d01907800034081356210741e040340d41b58042c0c09180c00460f101a10510412400080e08004882c3c0c003087d10303805001c060008125000e80c44042022564035032145d1105829001c01880030311081200004c01003074038201d9510a40b41050410003aa0310446081b2720 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 703663372 1250 703662122 703662139
    0xe0a1a0901030617070b160204050a09050c150301120302030405060d090213140708040807020901060906030606090803160203030c060a051b1e0d2705070806070e0402030402010c0f11 80
    0x81c01144828035080914004015210382d81c2804040f00c4254400c03049403a540c2c091030011f4005032100c1c82494441d0040e0100000c001801d49003480c1010b40f1514514030540c0d501c04c0010182c000a405c603411580c3c2c2c8450908514428a001d81c10350242d94000c680c02000132603110107150443d0000e502c0f60b13100304d42138200c80103441034441c122a14000b42500300c0300c0f06c100140f0542d005940c41070b0400d00032a4060f05101d0707968001103102c2001d812000014128510403c20140c060040e540584803030306000d0607990030442c526503a0f00943c500d03d003050340c0ca5811001951010300c00c80d28460110420340359586810701c15100030b4441510b6111a004951342031a243c41b00002c06e80300f5251141e02e80d80e03407041c84601c1c010115003000d0300c203100c0d80e541e850038000207081c036113415421f064040c0900c5025280b0b44c20110b0400d03509511400c4281c0003001040b01165004c40c08a0b0707282021100141c0302c1c0c03aa400100c0320314045010040c01c0c0309190213100c09000c1c0900c9a20030b9858112600c44 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 703664622 1250 703663372 703663379
    0x6160f09030c0e1e0702011b0c050a0206070303090b0f0103050c0a0b032404091103011a21100e1c0e13091401150e0601020a0c060e0a1a09010306 64
    0x44446496101c050201c41d45020140074036045600c9458200c030810010680d01d85810340c41841994098607080d000d40c1d5034541c8031511101ca80c036602e12040301824040642a040c0e180c080d154801c10320028440c034400030708002054000e40c00480020b403c03c40b15001407410b81c003201224a002c0c00240c6003440b506a04580c0c0389040b9124a09131000c0003d91802d54484030035085441c0c440c05808d05007180c0c0c51500704040c2d11030f88542d5103114050820340d01c5501002050601311800e040c11441c4108509001c003074140c880d80c0401000c40c0d01a10400c5a11000900b0141001c01407201141464103001c00355007a014000790041140b264120350a40b401c242030004d8501c10144540e160300030442c001aa103140110f91b00004a0600400f0390030f43c25200196464211b1740085407402044610280030b1044005039100107500036420300082070b01510b60b442d50368645e41c0f588500f004010034540035003010348907070703040d88010035003011802e403c0007a040003000b41c0d8000390422400a8a4080d001 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 703665872 1250 703664622 703664627
    0xf050a050f0607050a1d03030a0201020702011803172206051911070603090f0803100e16120e190302031c090818011701181107020117070e0306160f 65
    0xe40a0f0b00c090700e8035850151901c000340c5041c00386c0f140c21406945101010711158030240018003140005a0006035168020306c000b40000486880c2804280f0405005000241895258002240041c0700d90b54460607003030001c2d000c441025481901d42c000d080c000147c1e82d0f400401600010040c1c0050b410813040c2c9120031241076503000004025070344048002c106250081d1300403c0614020401a001143c507034860018a50050b1881c0310020500c01082001814562032a03400140910a00716400e140101c014005001e250391303d4402070341e4841814040700c0800032003c4501195000b50f00300d0005080194480d00040307100315501401c2c151200e1110058852a00d40650114801f418095104000102c084500440b10306210140780001900c01c00b001c001c40c02014840803d14200800000d0707a82a035010786040900100240f02c0707940140e0700111200e40d0008145d080340180d035074882d01103407445040401c868050103681c0600c024103c800c520146800c2440d00c54480081c9858001c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 703667122 1250 703665872 703665883
    0xb0f070c060801060e06030601021b03210d060b16030513050306181e030301030b090f0304080a02152110120f0605060607081801031b110d080105180402030a0f050a050f 74
    0x243e0041c0c01020342d00250f400084075040742094033400f100e414428040700c1981400d0074401c04070781c065002c00c3d00740075070030b2500404003d854038201260a0020116506141c480d4030b82005042c800003180700c5402c1c040800404000702002070803502941400700c2c2c14454513419a024091500482e14200113408401003c0c80d18118038038000c5156030701c0e42e20f96569036038020b00060b04500445151aa11480400145c4090b0141e14050042c1c0a2148104081c072542d012000702d0101081c0718a1400611402142030386641c02c8511130034581d42c03941c486600e21400e4218203103240c43c0f102c2d1403050103014400c05146078400d880401068a484042206c070707000d0a14010a44c0c2410000c21100e100c3d842184c420149040c1404103002c4050100f030790b080840001d298000410030800440628002c1050b002c0009403820150748650402c004600d1100800102110510840010038115142048030390503146d00314401d040707400f81525256072942464407050741c0d184200b100411084001080 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 703668372 1250 703667122 703667131
    0xd0c1d0906030d050702060408070f090c020c0d0816020301050705090a12020d021320190905010509040e0a0f0809030709050906060405060303090405040b06040e12040b0f070c060801060e0603 84
    0x83c60358400320708080700c0b1503025841c01c80e08490148400034000ba4100441c6000c0c0c05100490142e440c1004940c000701e62040e09a84119402b0301402c04550300c7c0e01a11460058001c80c5943d943d910b80100880001d240da280290190b18023010000c26641c0312010b0b000c204821504488842c0d070790704064281008c4100040d50000d110304241e40186070645440c4080ea0340e0100c00700302c0c450485410040b00800d00c91030001c01074001004940c2d0440e0304900300300c4008500f02a5503030790420f00001c0c564010030305424040c076580d2040340341f1054100202014294820740c1d032000010303649030444507070f08408942070003807103503a001142c0d01c1454082c00d0310030b40c408002000309598502c1004090080900226090b000800206580b5103541c080e0318465030180c81d040c11300d41049030910045401d0440c603d0301e950007100e190450040d0600440d01220a03e9410585680c07080b1401c44981c4209240180326070b19000700020103e030002e05890403130b07100d0b803500280400e246007807129900c003c44 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 703669622 1250 703668372 703668379
    0xd02161503140925030515091903050702011101230c090a08100b0126041a07030504031119151b02060a0609092111031602030c0102071d0405030d0c1d0906 68
    0x2c402254503031f815480d481d444200e01c412118100c254004500412003644415000240c002802100791350300b0503e8605155a04030003041400790098031200380004518141d286181e40c840442d811107842c80a0b5803c9030402001008816640c202c100c0d9030790008a20025054140089848558066101000c01241d0000358035031601003c0381c8d468500a0042c0200d6405240da00c0c0801240f112041f0703c1d20512030b5440018141c1000c3c100504099603007036050b142540509058040300b07607a120700305282030303021416241c03400c0d4445840d8040c140e11060b081c0b010396282c2c09240960b42c0091518015040d480e01080b0058990166000f0354560600160400c06542441800400340d002d0740ca80145091610302460718240300c5032030465001d071070080360801d42c00070140c0070b51078280214441280240000d0200a20f0400024100c0c0c4040e10001c0c1242d1201000805010040c0202ca100d1070100b40100043d40d80c02c600070b00007200031929554400b5002e000795004d401c20700205409014002e = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 703670872 1250 703669622 703669633
    0x150108011206090804170f010216031b022d010c080906070c0e16080a05130308070c05070f2103020304210210110d021615031409250305 60
    0x1490307295441450078411a44903507111101c001103204c40e0044c10240c00075944128201800c100400d103002a4a020884507910401c484400c00900c80040d10701c1c1135060910030070080844c18907403c1824201e50203504504103004140c15960103128540344004600d4090ba1020ad025004454a03101140010104a82005042150315250b030240004e40c6c07144800400c00c64030341000004c580000d960101c0c44411001e02c0078241900304000c03940c4101040c00c100220f1500001009244050040c0070b0b05001c10940031030705161182e500b0129441e0081d04603005690b69491f0b1440f500e80c244114981881c102d0340d00d98402800c1410402880e415a001358282414100e1166060380140d0030441400c0c2610911001602c0300c02e5059900026522003c080d690b0883d034040c104071a01c6018411034000140c001113030031121400300240c40d03010f8408038100b00004030990007000c1c15142603181c2141d4a00304061001d0001d00c01509000795589031100300c83e0741d4000212140140401000368000 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 703672122 1250 703670872 703670879
    0x3070e10090207150e1c08041a0c042409060203091f02010b0a080312010b030907030b1810050603070f060909020c0304120305130b04060203071401060f1d15010801 72
    0x71500a45042070140441c00808540725a4041c22514881c0c0d14007029040340700c140602c1285d040c01107404404604102c00790380703041d0350340da6445110400b05a03241e9210b08041516420881e080e0340c09002c00400075038480c4485a800484d6000c00082000050a800030106000e4404030903183c03041da010306a09a408070054112a03802034604000c0c0841d9a204040b0255580d0302c102c12008011040c09581d8448103a001403508150580080794135540810602901150000300c050449800c01c181c800d0507141c8a040c20071200011000750ba4a2103403403403411050307590f9071085001d00c41c210708895402c2d980e0401858901418420800810034016040142004030340050240c049100143ca03c1c2139162070001a1540e103041041e0300045001c2031581501320011448406000d40389806810640b600c04000c0d0f603441801f44c001d2031040980d6115081903000d402ca400034000d1002c03041c4a413615a42c42908403202c10102c40d080c00d001c00080345509513004012100d104040c1c0d119001a0308 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 703673372 1250 703672122 703672139
    0x816050307170c240d0212060916050a1701150905041a0d05160b04080607090b0f1c0c170a0c230d05010b0a0e121e0106031205070203070e10 62
    0x269856440442c1e130134050304a00410000041054404aa10050b190f410280d56103204000040440d4010b520340c2d01841302415002070130307000c100003d1802c1c130355501c0c1c55601142c4c3c20300303c1700e203500f100149800085503002d404051445080764955030020003076a200100001e8901d10400032400d071810740990b00c00c504100d541820558042c0c41180c01c1040503001c0e02c08125010f0348404884803000c1424081e500003400050b40140140ca0300090140c104034017008140b103241090424a0f50000e200c0b801e091003210803100200b9040800c002c1c1106808000d4284109211048a250030407000a01c038040644604010498142c1c1c0d805106225142c5c0300b414004030b80b1054410078002d02c400805100e0500403a030180c44810300d20f82e102c0c41c1110001e024210318076407407071180c500c11840e00807003000065a44059201d405c0303800c5014411520745401440280c1010701480d2031440c94140444e0040010710105d4401c1c0c0880c2c08450fa00e0a0364514074506035007038401c070300424400300107460303 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 703674622 1250 703673372 703673389
    0x906041707020312070b0609071107061b02040e01020d0b01030207120c0305071209050901082103130f050106050a0e0c0403200d0b0118020f040b130816050307170c 72
    0x2c0c80501121030400841e00f0340302c0c10780c0007200304075a61050710b81048254140823400d070303800c14400e05010620003640c0c0d241ca0384800d804d0156108206030b20042040c0ba603400c051106100707402800400c040140d0343c807110302075404036504049140c101000c1e00c0465102c0d2007215a0300d0740110304403000c2d032102c484c03c807842c5921a9068040110502c0303054003041500628074803229054595032102d500c0c000038046941da059100e2504c41c0c000c0c0d001c6a2a07040d9416648200c0a03c614849541c0e50302d5864401400200300c00241c4030703a00151465040050551205007650804c07100907100d0b9649100a400300c40c4200c0e1012075148061004100180450340c804420030031181394180200402400318000401c84601592194850300040143d403002010382501e04401000030342c07800c82d81c0c2041c500c1c1d920440c030500300c031400001040486610400c03c0b520180c8091030950b40f03c40c0004d41c00701d20503600d80c065103200e405030000008441c81014222100d0704401401303004001c610600f04403456 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 703675872 1250 703674622 703674637
    0x60501210f090804080703051b2112070c090513020a0612020403061112070306050102070e0907210516030308190e010608010c02010f050402060316090902030103080a030509060417 79
    0x207602c88180600190f0385502500180070240c2c000d18105245040c124070f8003a009042111007240011138508a440b01c8504c924104020220003c1398405031500501d020481e118541001e1f00100340141005211580c90701112104a018400780d101d51000300034042c200e51000303520264030402003043c5409454640c0e01f00b07410b041d0050805030781e52a14010b1b0b030800e040d19907000c01c00040038007440c0c0341882c0d1513030005e01ea480c003040010700b0304e00084d5490a060080d880888100b00000d002d02030104400c138041c040c4441e8100101c802c00c06140612043e0754003c980b18090088498141900023104004498159070344e55942e894807035090b0040e6440f03503150804243c5034074041c01805024085c0748000c10009000194291179150002c0c01c4500955660006c2414002070001580d5280e040d2a080b0401c07140402c04610840350954101000c0c3d03109503a00b5002000010900c40c0c0c100203041102201d0710140403540e40c8504590321100100d070020300c61200441100000f64100d070240140 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 703677122 1250 703675872 703675901
    0x150304031110020f03060418110111011d0c090708040c0504020307020f01052403010605090109110c0d05030106170702060a0b220204141503070507060b130f06050121 73
    0x2e81aa44aa0030140d81c40000740d40342c103c4c00001881100d0a00748103040c200d64402600144007a40b5a0700c1039412050304000a0400c100f40c00710b61f040d030744203501c50a0b49100340c0c400300425440600c0e10586840c81d140b540d5204084610000c4e00c514042c0715140e218a503c0540000c29504190800000750000740440c0114450031050006024091141c07501520651140008480a20700340302031610742001214000c0c0d0618008100544480c45070a040d654407a6010454850030301e4841014092a001d0003018810000b580c1d421680040045060b20190780c6c80c4043c1d0150441d8140c440303407040d00c02c8001a401980000c80c15000c1e5400201089002800d0300e40700f101c0c41410707014000751191700c461950350006d003c00ca039600d290000d41806806031810100700c090300380e080a543c080244910b040c44000203032842000f42c21703813052040440c02404140c06682d6000b03080c008044811010860341d26080c4e000c2002c0d07003d54442c400203468403400c180d00301040441803000e08414603d94a1 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 703678372 1250 703677122 703677133
    0x50301051011060403170c3c030f040b0c03090a0f0501021b01150503010603030203030106032c0102090a061b0219050a120b0705040b040b031302030d020106050a051503040311 77
    0x20481418400d2a004038006e9880c40406c0901030741c81d80c02c4c008042c20009082c031003000680c400000c1090441a0480240001e41c010301c8040030003201e281d10b07445098100500003042200d001d407004000c900070350080321000c2d41c0c2d5481e000c1c2d1021500c01035603803405039401070081c1c900040c05060440340352445000007500b480c0358070000b10044a1036041c0003031144d440f10400000908015800d40007050120002e01c0958038586000c0d40341d200c1800b86204054403010040c14403403000c20710804943e44059a040303a0104e044920b8001e4100064040c400c5140035000519148918001a5101c402e09068043d010b8540c2c20041a800716603111180d40780c1c0c8040004441c2d845092600083c1022204054817564504d48140404002088003091010521040c001c0c017050341305882c252007202d10325035074230307101e07040000700350022404001e525215524100700925819040101205ea00f910325008503034850302000001115403041034003180d410710004003c02c0c4102e0160001e80040c07000c0d2074 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 703679622 1250 703678372 703678397
    0x3010b030402211e010903320a09140a06081303200a05070e0106050412141f0c08060907081e010305030a0f02030a12020307051201090b040b030d0503010510 69
    0x111001a0300f4200c0c1c19600030403800b1024400e241080d11910040000800154005d0355010b07240171001c48104140035641031320b008406540802480319221091811502c0d840b610380d00034070040180c090f80b02c514450041034407107800c0c6070541c94290b40c01600c0341c0000355681501801d490300c0200c4290208030040112018000407005e8102c000b05011001d80030114480c2001d43c6059000d501c14039400004900400000307a0002c151401c1d0340b0184000f0702c0f52050317818072011303008200c17940300c6c180d010350b5541c010001c0c0b1481d8900c4400e400b900e8107211003900351106541442040328503039002042c036400503074600c0c41b0381149a03000b03207940500010380c400907000b070805450980045540303500000c1c11008480d0429000e1007070721481d10086107410f0090310010a00103581030460350f800c1d000320109a240e8010700a40e0155003502c81803409540c1e6915420010b01841e5000601480c50882e50014600340890801d5581c040d540740c41e03146902c4d0a05001d9542c2d101c9030148100704101d21000e = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 703680872 1250 703679622 703679659
    0xf0601050f04171513080d0f021204050d05210a020c060103080a020c120d080901021c0605190506071e02060d0b0406050913030e131515090b03010b030402 68
    0x8001400e101450f50711842e02d080d400b5440c180c403116020407101403ca0400c214580301c05100d0024680c00b845094031803569201d81c10241c036421441d40400f50000c5501100056402c0d0458421801081243d00d00d02d442902aa043d209945544004650b042e01c540442d00088015a0b00103600360001450034001c202c03001d080c0107003a04101c83c5070310000340c100300a0f036040100c0340819030100c43d0030032244c074104411079440031000d032650300b40040100014000310013981a10b200c59100b40300ea104095000500c04018129801054801c0c070a410a1800741c103444e108480980f01c000d4101850002d068071452513034070004c100c0d00704001e002142100181caa0402810003905c01d14804a59242d20004100a80d1a550003190080319404100904000100c13941100a81c050a0003801d50710b000c00440c01940100540c01c10301f1382041200c491660790000c0900c200d4400e002c5021920300480c00071100c1d00c00611038010624401d000500481162900030b5030400e00c010040c070503600402101 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 703682122 1250 703680872 703680877
    0x9140f18071d0906010e01120f06080a020a090e03091315091e0506060306061e03070801080d05030103051b01120e03091309150b03030403080408010c030c170f0601050f 74
    0x284000805401106508110030902c03007003801012100c4401e10319103200001c005400400402d410480c011143c0303410354100e0f51000c040c40c4d0038000c041c001240c450040580e00c00c101c2030124010705000d0f41c0080c2ca55190310508a503000b10201462812880d0310411900700c00140b10040b5030342e42d45020350311030764040e070f4044018100718170301140c0305c3e00042d5110000b1001425681d4002d00703202c20098a640c0307a804603507020201701c1d0079036113400c0d203c40080650754840e126100c196400100344107050313802c00d164a048aa07154116a00034a811408a07031601080c0300040030307503101c4e2204241804690401065000c01072409440c00c0380320b18014800d5030048180c0540720307003001510325150b0604003280071030700107051010700918642d40d90f40103020141000c1c9038413056030b1340c941e040740d03039000c0c401c079030046411000540e101ca40700c0300c41034000c4c41c0701d08028021038038282626104c03e02460801881e030300c02400c4242d40b580c810142e424141c900404141c100101041582d2440407204007 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 703683372 1250 703682122 703682131
    0x7150c03050a0c0302031b03090c120f07050d030c120314070306210309140a05130f1803050a0f0908010e0c03012f07030c0218070206060109140f18 65
    0x4021a075410109406030888071820380c0401014010000c0040e0b90060020741d40c5140403980b500c41c0d40c2c5e50b030410868140b00e080528243c3c003201d4900102c0e8810320020302c4c0718440c3d000c0800e40d407440d580c1d0b90410400545c040390040100382140c0702c100116865180c0c1c400243c07000d00340802c508140c4295010800000c84040c030220f613544506000d502320940780c0084129144105161442c100d4a0240c400600380c420640b0001400600d038519480304c07600500202805400010341c416040302103c050b01e0514203001c1c01601d40005c61150348440082e01c14004d070151a12460246101030456500c2ca90304500302c04d105000c7e000064071402445810040c0c500d0f20042d1510b40c000c081010300f510b0748001c1400007040104a842c402c8007480601510030004082c0036a9501100d10b410344603c07840d00c50103544240007103a24400d0200c40d11005101c4d80d41c03a801d44003c0c2da41e00d0015507581e4198024020260701d0340d658011581804a034800c4d0800d4018036441641480c80701409400300c0c2181c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 703684622 1250 703683372 703683377
    0x20c040e0d02010c0306050102100e0102090307120b0c070f121106010906030312020408030f0a02010b061201060f08070f1b211d0d021c060c020c030c010801030b0c07150c 75
    0x548102201d98284904040200b640c41e06111440c03170030700003e40d50396183ca01c1042c1103554031141510785009504543c0d15034401390981e18000e81d18208419005001c02040d41c100e65001c000606108048040f9910030350b1020443c0300a0f04541c4440e8025500106580d0a000b11034070740c45461001000102e009051400000c59198103601c0c00038001d00d08045001c00c0c0300d006003c00c0c0945003022059582c401031640340d883d25100c1c0c1c00c038224050040c41c0b005c1c3d5000800022540c28510890b900755040c0c4005842e9507840000072002112050400c42e0340324005100c0e41d0044e50f22034864140018041444d502c0c05000c980e154a03082501480b40c503502e00d030204010360081c4c9581c6c100848a02c141501d030f07102c20361422004080381d4240107900c0000c4c89013010700d18484440309420302061079950400400c0182c0d1141d960040e603109001511940b080c4038824003040d203507103d0000241030303980c8040901c1e05600e400c52541250341140d032007141d2200c0c1c1401c00254401881c8100384070503070985d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 703685872 1250 703684622 703684633
    0x1c0e030109060e16052b150507020a0c05030a0209180a0203120712020f15060103020d020c07030c05040911120102070812150409030203030f0c041e1707180c020c040e 73
    0x500c1424450060790b04c010301881d0b41b0300e515000303411071445440c500710010302c840700c08051500d0a40f83c1a8000400380c0412840c150520402c19800155181882d01c5860111034041d00c4204050365507543d2580254481c00743c100207001c0c5281140005070780218041198144409a0300103820701d400c452040c0d0750b5020100c0c0c041c0c01c0c8400214801c02106072400030309106660012510349490f51844200c010941c80d0000c00d4090b403190f811036079200d04541c011922480104459521648607200c142c0d01d1003400100032441c1d1402d40324004007a9409200c2d945001d44a900f80031018050390010501958280b205102044441008000c17440500406c200e8900e01080c00c013071264062460180183e01d841903400c0000e40010072660005001c41280c0240e5480e0701c803454003485181c020b408100c481c00404103801113220020070aa6031541f030103c0305444100135050b40c90f807841c4100705801d15080412000c2c8081c5500c1001144081e2068a021084040c0410159411482302c0111039012 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 703687122 1250 703685872 703685893
    0x21923030c030a0303020909100e04031119240203090304140a0f150206011a0409050921090108061905011d091302130c0f0e030f0607021e1c0e030109060e 68
    0xd10220390b0701270600340b80511500d05204803140b840c48014001401d10441403581004070358100a40016010b842500120800080c5450480c1c0c1c41600301c4144059060402114040f10a0099030300c9003404c0b100940c1040e1520094042c0610f003011030b1500500880004507446c00e008400130040c00040380b030142c11448a00000b4902072059000003483c40d0042d1420415400c1e000840b811541d021780d0208132034890b0500f00c1d00308812006010402005040c03a0941c81500c0c102400c00e5403002d8036140303859500d0038280f04400c08444009800d024030f80d0f4050005600819040e40700040080c241219541200c010036a07981e815100183d40308a80101c803011442d14056010040e18410300c18080390200c444094902040044284188600e880e00640707161820071807031114081d54000c0ba41181014000039480d181d000556804d4082c006034480803102e400a41c20f04d40040603100c1d280e003003452a104490400150318450b42c55500c618a00c004100240104c618025020020349482c900 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 703688372 1250 703687122 703687129
    0x3b041e260a020f03031005100203091e0307060e03060403080709170619090b0115030f060f0303080f400507052115040206120f04021923030c030a03030209 68
    0x243c401c0d2404594020000c0000c2011b41e048071008841c800d40c0c000411341c401c100268150300600c01200e400a0454202d0540c400395204042900c40c0140c050b0741700140c4615044034070064800542d90154814804180064451400c442c1c1c4500d642c40c1414006855024110381c00611010342130036507102000740601100e84a1040d4240380c90040e0801c6091420b683d5005213807014446c40d22142c05810b203103d9154060f4111020040454108000c110b441d000c10620007081d901040c0c000032416000243d0182c820303081c0074080d403000b0011684000724410350002001c21091422500e0141c0c42c4070022030040505400b41540c4998042c0074298241014040240c4403201d010700d9000001c19460120354011130047e09030006c45e00c0510b050340c3c80c3d0020420501c900094036020390010400c2016803407019401600440c4216040c10443c02010100c4590905500502045c402035102c0b8500c03417504400300844003007018081d50b01d0391400800190802009120640101c0c0e000200c0c12094503 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 703689622 1250 703688372 703688383
    0x6010b0a030c050a020a0308100b040e0405190b0a1a060f19021b01050d020702150c010c0207230a1a070c09050108070614043b041e260a02 61
    0xb200c901e0080d04165407100025a00c80542801030705003c400e00118004041c0ca80700c0b030001d05055048940c2d07030b665541240031200012a030035640781c00384a24421004070381100c0b11103004e8202d01c44220b113031202c0740018001c0a81540d44a920049200b80245a8880801070000c185048020030b44400c401e0381248103e00c101e40c5810304540000a034446002a101e0f1100050314080c601f6989804102d44840c0080c45041c002961050b60b00410b40c5126040f64014040c540c590002400201400802640e031052580600a0704803481a1840c00200800010f220120300c010150b1584640c2d031080c0c0859044020310034591010005008418080039484404c000d10020104100f0385d80b4200409456655500411040100c0d0041e03014194020000340c90240803141301c034034a0108207211243c5c6420f070048000c0c1503490b64841e602c3c0200d12040d01c00e0b10480c0c114050500b001c40c01000c100c1c0d1080b15030011100d41c00c00441718041c2d10b0350043c26034110b04560b007400d0307912100c0410180c0b030034 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 703690872 1250 703689622 703689641
    0x9170c0d0803010602152406090415031505010806040204050601020a152f030109020723060609090c010c0303020c070815180607020a030c06020d15050f120309091806010b0a03 77
    0xa1554101f80000205e04821110382c002d00745c00140f9500c1c203200700091751881194801c3d0b40c4182014910801c0524000d202f500301c80c8503040004c048032148900e034098403030174070405045400000010f005410030360002e035880f060500c180c40801d0b11582d80c4403411441c81d001c00084959425240b000403458410702c00b90000c284017242030030414511200c3d09840140100015560003203410401c0101e02c00810310007000c0c0400580005c1410480c1607902e0320201c0c0d5403403203485003c005c14a12000070443c44040401039588011090070780e24103501a51004002080500c81d403000000d0042060103103030100d0204034030101150805040600c0c2007012011040c0058100704140070f07000d600013032043c0d8419810b04001d180003200741007002c02402910f005410503800d00c8a400300d003c05921502d410703183c0803240a01180062000e000c1c2207241d0049241043d0f00c20040c8a48515200b40e0841e0301055005081140a00c000b000c07a0409a0a0703104040c044004140c00040940502030074000307 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 703692122 1250 703690872 703690903
    0x30c0e030307060b1c030e100507020306070c0312020c0f0f01140411010203040b0c0105060a06030c092105011b0905040912030c0207050910090e060709170c0d0803010602 75
    0x1204002001946910480c2001400c80d640c035103010700343d40c84522492001c400440030250304848103080180c0807090041e8080d21988200c0518030710030b4050420b45c0c01c0f41d0b0f00900101039641c0c514205544245551100758148034500c5803c101600780c41c001040244e4034070b13018201050310f911005140150468414900340d050241d5980e001d480305858580c81070f00150b80302815415200181d003180704a8004030380c0d04400184a8a5010301500000d008880075980b50780a6a40e03010228100c6400080203030000d51141400c10800c945d85020102200d1440c81c00f802d0341500b940e6190031100303510058102078000c120b2a0740c00c41d80050041000b031006607400e1240c403505607034008844401c024414241540c1d0700380c20b40e855200304030035406880003902d50030a03400c0060300e11400c1c24051013002100d600708404c0d5007101c1c902144840c0540d01644130b00c0442c50a0400f22150304022501e101001e124525008980d0368910304050b00050144807461340c2c070f50400d00c0090802c4c070f0341c1000c00003 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 703693372 1250 703692122 703692137
    0x121f060b03071211030a05070809010917090a09141f030c151b03080a0e070b0d110d02070f02100f0c02060310030c0b030a05010501090807031502041e0303030c 70
    0xd04100504407035120300a403406045030b00864488100420000c458446840008030030800004c00d15884940660b4141d1203007926503031008071140c240c42d03649100500742100720000050103040075018260410300108003081642d140e0502e1011107110b03074101490302d80c1c020148802d480c8054600c1180d410070803000e80f1114150f8542c05402045071007650070901c080118114014840e010740035464498046080e511600d03403c0041115409451401c1c2003883d0035110031388401d0000e810b004541d042e0083c40d0402c884404040c0081c004c0e0260003800000c100b00803030754800a0310007020407501c11001c006048942e401408140003c85110138244907080c134807a10515003101113071408507412101d165482e0f4821800d10b510b400c05510080c40b4600d841c00104201c8000d601a510500820108000c980c6c0e84200456039000f80e486846080d0b081585c3c103101003900c81070164800d4440d5407015181a503104803085e6041402004945d0001c01c9a405104140e414080c0050320800c51030041f6 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 703694622 1250 703693372 703693379
    0x711090907230d051c02011104030c14041b120c09060806120f2d010b0109030b1f060507020a2c09010e010513030f08070c030f0e121f06 60
    0x103400400c0301114101c80344450b0b4070032140b540c0740c1c100b03880c18590020a81704000030341c60100100704640d1103060095400c10340c0c100403058044c010350b8201e90b00030700800b800c94584403480b601d0f40c041c07982032a08691079516904840940b40160070742506542d5a0720440c800b0710700b8002c125104442c0b480100100c40100700710040d44035903c1c5800550803a2180075001150340013030f1400c0034406848242e07005544442814502030480c181c450080b0314980b03400d0030720040c50305003250307400400d29002c0307000c4420034800b0030621001c0603446000700d00c100c0051a0729250604903036040d540610002034000410341c0444c1880880700c07000781401155800700d03506044540c1c0a078802401907101c1c5001c0c0d100001d0300340500350481c0750b030815444020000750909002d2000e544440100030ba000c2016500c103d103c40d0303c158900e41c82110a030703590a54950269a049441c121042e10741c804102d07005015044c695038102403d0f560310000c0004091410a18500c00c108441c50514010128900003042 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 703695872 1250 703694622 703694639
    0x1050406080a021308120a081506250218061206100b0a020120070530030402010c05071e050607020a05040b1804060b040e0109020d121101020711090907 67
    0x40c1e410110007a400360300d41c0c0d0f046811964408481d481711596104550042491124100c01001403014507a0b640203141d45154000c50200f0883c181c1382d400c40c908001c06c55200b200054012180c003d181070036902002903800042d1034881407448070b52120940402c1c8496481d00c900ca50444a0ba10405805145001d4299080d8031019120b00c1045403070024a8240e40c034400e46c4034048101f40403203e0b1014000f02d14100e92590400081280e4603c02c40f01700c3e009161225019032882002c9041d5581d01141460381000c0030781001d807040f410301c1004c504c0c28000900c00d004c91409081c00c421511803540300003c2a0600203940d5002034001d590070400d180258445c0959002a17500a40b404248041d082d804200c614010f0550b82d0040c41d019010300c010881c81e90883c040c3c07610211000d02203240404006801c940c09450000c3d030016890000b00001403da06141100061504107020f08501e40100c0340e003a60700204003120944418004c228040c90711f9071500e83c0041c07000004001e05802d02402 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 703697122 1250 703695872 703695887
    0x20f070506070923010806280b0915071106070807150b03060112050c09090708030a030c020607030b0612040305041d16090e01230607080706060902031308030a0e15011401050406 78
    0x1814006c128900200da4000381113220b5421602494400c003038489d90303601d1803001c6604040341a41c8112000752003409402c03019000c3c2d814964000c08142c0321241510b041020590014100b00caa001080c843da5001c1940c100b0010300e0040d1054000c140e02954004040c03c10300d050b000f05c80301d401c0148012010420005031903000c50000c1d41d000245481c0d5040441ca421070560003c1c420344000101020f0440d0b01d500036005908140c1c013111507c0d00c07001c40580945502001303d81c0c02490910141c0100740302c26a005401c20701174102140f50030303202c4d0301b0000c0e4403101901041d1f074403d9440c1840040105141545004007141c038101d4002030030866504681803061041740001030300746032840741454000c0741c2c071001503100501040e0382e100305180028290308124030503641d030340c5410b40c001074045141c0201c91003080b0740907003030080f580c9950352001340346c20203008418a1555042c0d550340d81d001c20442d0308003104501c031004000750316102418020386228100281040700510007044a103411130701 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 703698372 1250 703697122 703697131
    0xb15010e10020d0c051c0c0c240309140601060e1305010e0c030406060803070f03030e0d0e300a120f0e04050c1e03010f060c0503070303020f0705060709230108 70
    0x2090665101903040062414402001c0c02e001b4030b040044c01da03c40c5800c02003500c40030f071140b04c1d031007411a47d030750780d8014240d18402005416005280d448082c0c0c1c0c800c2d404007501500c40c07540b4120b900048010146818001d070800300201b803000030200f80d1032500000952916050780001d000c50740c140500c1707032400b0101401c1808441c1c0040085010442980c020307030080c101c080104c0740c0360040c500f0240000d8410100980c0131074a841100030780e90101107854200d0301080d807503c480801001041c4403032034405284500b1019441c6886105d20040080c41d20340d4110300340000c007524081401d0a000c480035442d992001d01080410a0451036000502c030000e209084500040c03554405030818402c2c0715542c1305143c4081500b900c0304034480050003031416034045211407002281c6595081e6602031404601420b035078014428100002e20980080c01080020300110382000a55652246019001d85041c0d0109864039030a000303820791300b00da009203071440c000056079172081d0400180c1220001b51 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 703699622 1250 703698372 703698377
    0xc0a05030c0d0221030d0b10020715020f03030a0f06081501230409030309050c180117010e0d050a021209100c020f03030703080115140a08040f0b15010e10020d 70
    0x10600b5095550744c101010b0900003001030807072161039050882d0740301d50206010081051620300c510541d410484441d00d10032510380c000f0301840b401e00b8002400840c00b54501c004600c240a06030b041c24105001560040502201c0401c3c2c100301c2d0500042910a03a802103517180d800b4010b82e50540e03814040003411150052244508480304e00407843c2d40c0c904800f070003508503040c91042001c15515070b120081030f600400540c1c80301c41c4a4010450301e0f00d0003070300c1c0341d00c036480c07440040c00740c1e210240c1e650302034481010000500034824000d0341d04050700c049958002c20300204400c0c40c80350701800440f40b07428036000c00c0381c641b0b90600300164060070000414801c00036011001c40454484c1c00b140d00f08044020704880d2101c1c41854014040c0c1c0003406981802a0400d05400c0224080d0344c2da91243c51155150a00704114807400721030a0b50002c6c0107076241030f20085244007181d410810680652a40031954001c041d4550000d80f4900b000700300c09005d040c0b651030140840354041408800c042e03c91 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 703700872 1250 703699622 703699639
    0x60509040906110705061b07030e0a080d020709180c0b0c010b04020310060219030206130f0803190b12070b090f04020d0504150203040515270309030c0a05030c 70
    0x40208004045a2200900b01403400c44507442003100700010b44041840340d03044a00c1d9070307545d034202041203081000c4e00002c28818050400002d001d0000f0a10441006d080113100381e80d100300b5280b50140d13440b010409a00f10000c00c1c0440546806803401558030720003d00c0c0340c4802c40d5a410007201e01403280c9040001c02061045010760203401c410962280108295281d06103440c201004c02510b20640c405031040318540180c0f140240781e6103a04c240c05402404c0580e498102d010940700d0303045400c44040b00381c1000800060103030301c0030b18040d07142806014044c10540c03500034200e52001d8a4207210303a5101c10a01080800080c81406540d038051042e516007400c500400c511042011030a6803081c0081002c1c42400c41c698841440341380036540c3c401003a081c80c00d5550492005071806030064100700016502088100030b01303a002512080452804400100810700006010640c84040e17040011201040e140c10080c0381c104010403a021161246802d0010f6542c40c084807800d030082041 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 703702122 1250 703700872 703700887
    0x9030e04051807090e0708060c09040506030708010908040906050108060a090b03160308090a0b03040b06060a050c0f010504050c06040b030f06030a021003020d05130302030a0305090115081617070605 87
    0x411582204261110201ca203c02d4484000c500981881da625018910440384001140c500c0090030501030f264510325075141c8542d0505100203800001d0801da003621035000700090050091042c40d8980380034542e11900d4504002d408070503140141d000314100f28041050103001c0d5038400040c41180d01c80c502c001280c00c20351010905144180e107080e1600c0503c0d45000045c045014010b1104603421250102040e840316071000d6240800c1d1406000840c1e00e800089d0300382031038001400e00e6007183c10114102840d001419203040030386000680340707175180c00c00e000c10080c003001841c280105c101c0380b09082c01d00f0001036500d10f000c000c5c042a40020800086903041d1018000d001c00c4540180c0380c21601843e05c400074001c2c3d8840000c82200c0c5140c40e0000c3d101e80ba8030324103000c109600d0303800b8520749034070040c0c118040d00c005408004155a20342d05949002d007840c04040062808a01078040d43c0c20f400112a201201c69000442521100d0f18031b150248010483c04180c505a0400b107441d90403 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 703703372 1250 703702122 703702141
    0xc0f0f0c211206050a03080d0e0c04091a0603030a020a02010c02150307020607020712020604030615051207170102030402150c03040e0c19031b03111201090e06090109030e0405 77
    0xc8000d00d08108031036074400700d030400c0e444108240400240d9505020302e90340c8009001c18039002d8400502075540501105168462603001501c3c200c141d01c0845140e2440600020704644482504948990003c3c0c5101d881e0300c10780d40c203d540074604078040c2d802d21307050001c040d485205201d03000f8100030300c5041c2c400840d90350b421013103481c2410a00784c83d22413801078800381d9144030540e4890054810b030707080003441651018880c0c24031030f8040c03c454201031850395142c01900c40c410603c4039208030b100c00421aa1101c0d010038000e2080ea000406404c7e00c0d1504034a100525040e8128007079004004200140e100c40f045110070118241d08191348003c0050464110b0045400003a651111181071003002010b40001d0a003000c031441c8031458404180e0010380c211404070040000d144407030b81d0039800c045c2c001d5004170104651143e00321320f860000005088038042c00d811110096545481d80400d0321780400c41c40d40e100800100800901e401c60b18040c1c2281121a80305101d6a15240015001c06 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 703704622 1250 703703372 703703393
    0x201050105060d0b130906060302031b01050f16210f14070b1b03070c021315060806010e041509060b070804050f040608060412260c070303020915030a0c0f0f0c 70
    0xc5c2050000c020740071103803904101034500c601c000c0c1d10912a0030194400004c401006043e4250161a1103141284040b043c5c6c0c05a00300b49010204140d40317038490b40c0441d000940c0030346096510946a0042e010008000d000206420a0314080110340d8600700c5c0c240729010221030fa001e80048400202707035140015100c911403448480412a000801440003203a0000d001c2d400061088400c0c00544100301c2400b02152021075240400d50b8260004002950003441d03910b40058040c5402d090703502c2c1c00c50104040d01c080c3c20806c441015000c00c01c021403000d600ca86000b170b01c3c80c211401d180044946440505014030b0080c20711845180d114141c50b66100e911510091800c00e05884891034241030814610383c800f120440881d00b00215501c4205090003440241200c0d054107151545604000440c01d8201180031014540d0820507400c440c0d0342c0030490800792000c00c1900b942c0c1d1400e08841c5096802d800070480c01d22048100045079070b81c00a00d10030070814185406100c0013841c2c1001c90040 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 703705872 1250 703704622 703704649
    0x1d061b37330c05070209040201082215061a040608100f090504021008060a1710060e190603080d090c030618050f0609030f220902040509070201050105060d0b 69
    0x180d000c1051884540701540c407031026000a420400854580090a44603445441d000a40c4400c444d0000780040d070142700d0ba07540240703071080c1d15010300000d00784c02c0c1545070101500b544c4c21070303d007038107450f0041c014042c4c04003400082d05620083c1414411096190040d4020310091001c0c60000030102c8211041c00d00050407080c00e070880c417581d200406001408180e40a90082400000da241042c0c000d92a15001c0c40c00680040907081c641a9015222103100011046c58000c0c4402c0c0002602c0500a0b840508800c1010200702c0c10303d503c81140300781181781100a02e90601c5003c101042641003036485003110803802060a0881e86080350341b107600740d007008103004d01e410000c54038185061034041c0401d204d8400c44415000c6004225030322542117501049a40c0100015405402588041e00d590000d8186020032665901807000400030550800c0280071303400301d8100300a2038801e100c65046901c1c2c0c002004203504141c0800e415114058030900701c00d0710341346810207940300c0e201214183c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 703707122 1250 703705872 703705913
    0x8070308030103080a0513170115080705011d03010606080106091d070e040f15091116020f0307091b140903101107021809160e06011d061b37 62
    0x21f10344a2003040310710315800501c419150b1911070600406100c90300c0c02d2060301c041500604005180c040119500da4a500c0b002e1b1368119070070ba00b802c80e51800d0085a010b4003864881e5140c56040210080404400340d0045000264100c196100c1500c12003110340c0010702480e04121508405010901130301c0650112043c1901c1c11001c0144a051861204240d4400c90070a02401280448000203800744a20b02030f442011031801400500e8840703900b1203409005400c1c1c50b00d040d139410030f480031903207034002003030f1041100d01c1480d80542d07101c14119106200d501050b401d1000ca040801e640c0d810340d1581004e2143d4541203c031201d0b0620054402842e0300400208250304c14007440c0c241942c0544007019a803141d2200300030260046604078003900c07803001507503241eaa43c0300011201aa04080308910079142d80711200d5450301c951006211554090505040d0650f00e030f030046103054495042d10100000d203209049180010700d0b20360080d0320018110300c100203503604090407214105051680c9 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 703708372 1250 703707122 703707157
    0x40e0906070201050718090b0a0b0a050c0c06041203080601020708160503070f050310020306060f0a080411010315050603040c171c03140126060a0b090108070308030103080a05 77
    0x20001000200184500380d00e07070092090362075100301030300c40603030303007900d40349545445401031050398440d81c070426000c44010080c0c200c5607a20008085240d00501e0450005a000640c201c1c40a004005034101494195403851610749019001d1008441d81c0b203006040160740404554568801c000c0c8101901c40c010075200c940e2441e00c240d00054060b8400d4602900800500003144400798400c4000c5031000b4020b805600b441d101000020751008011a500031810b0000d00300701c200101c0508100c10041d220780071030741094100355880710204101c04e0704142c14428003061680111a0003021a07000788c07134030384e1a40c95504c0c11040442d901d4004020900ca40180710141a00000e18150b04d084038601488840d98101011015110b443c0c07840f0402c102480010009158034100c0b4500501c0d9044c050346841101045140c1400401c2c6c402100d001c0d21608010751a14040e43c100f8010600c000007490b00c50f2940c2c0d2103104e60b0205200c0a8120913022942140550090085a228000f070044000 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 703709622 1250 703708372 703708381
    0x31b030b010e19291f050c12210a1109270f0718050f06071b0303050309010b0d0b072303010905040b0603010b0a140114120103020103050f19090206040e 67
    0x506000f11344649400c503044000d806003e81c02c25820b801140011500c8a42045204d44002e5400e0791000100d9009407152103440b02c0d01c000d84401034015045480700300018041c0d4416960078110015000d81c04552401100168050400044500c2c0000541e4041c0c0d9007403080d00304101c008808501944502c440c502000001000c1c2a43c4038452110354480d00c0c40003210f00c4001410302898003c8642080f0144a5030000c1e00d8000090641184a03680c1c41c01c2203419400c10000700c02d11980101c000c0707503020007803000c0501d0a02a056500f10b0684004a00d00b9458850003a071600c007410070780610010700d852000120b180f05110b40001d0324546511383d0303565150b90000062900310ba003950039406510110b641c40c80c06003e203c0d1351038001040702c00c61500340342081704541030105d0041c0c1484503642d030194020700f020303014060150041c048010650f01d54000074040d20001414500000400e5040060742d10380c8103100c555140240313400181d01c52007440454494851900a520f0310385504003000b = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 703710872 1250 703709622 703709651
    0xf011205040f0303050708040302150604020c0f010e100c090506030c070807051b010c0b2e0902070b01080d3e030304030f082a190207031b030b010e19 66
    0x502d12078400d0b42c08110698804608036665101660b000740140c109130315214030004005403d80c1c00c8100100018a04402100e40302c0c50002140d0020340301365120702c90402d20b08410b001a032003415041d0720074404540b140000501200c0580030b0740303200d40b0010010858440700a800d0b204050f901011055440f0054100f80c0d54a110120303841404410500c0148030551003089002c3c2c09591000d00704016480300c0c0005082416400b0104404101b1910100303180011500c03548010254000300680d40c080318189894400416002421181d00000c2c03a10768407680400e403d02d00300c0e0b00301c801c2c4000100c00e9044e588a0484220582c01c0c26594003070242240d40003000940c0601d1182e143c42c2c201010115055610f28011105810981183e4a0520003040d403680d201007050401e44e1310314038000002e00c0740003070442c0301240080160300506040c802c104030243c000c5162912155091483e40c61561456070000c0c0501030030900072a040c01003841401c40e0003c441e00041ca024050001050300c401c0c1 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 703712122 1250 703710872 703710893
    0xf0f03040c0b120105061c0c09091406090c2d03150a05030c0f03010e030a09080f16060c030507150f231b040e010602100f1a0f01120504 60
    0x1900c484080c80070000700c0c003280404881c043c03010110008040da182c4820401c840d0803801c1c1406181428a2500b501010746102d01c038007040f259103800d44160708210301c000440300200c2103a01420b442d14140200381d03492000710f907480304404010507034400495482d10200e05200c05081e03618001c0b820410784008904019500c520075100885030401062010002c20dd07100d88519601900f0a00350303480203007000b580701085404003600101d85c0b40304144409103154400d01200300021000042400148024002c0c01078a10503100240f08a2007240084004010f030f911584041c42031103582541014064070907984c4c1207400080c002581c0035203881c4140075110b00046441460710705103c550301c40300000010403010007841d03884102940c07a00d12442c580380400c00020f50300c0b42d05020010b07000041c244024042c011a60240c007942c5401c1134024250b40d051003503611002d00f0000720b4101c80e400d0030b4000410484c111111003a5078002401030703591801116100e418241070030200014051034080 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 703713372 1250 703712122 703712131
    0x907051c1a09130201270801151a030c13170a0b061c080a0903200f06030c07060b0406050d141603050706030207030203121f1a0f0c030f0f03 62
    0x90350040c1511080070410008402c41d0010700c90070a280b080400340d4410017200103240c0301d1704004003c94034050900f07091b06010b41d20143c02c0fa03440d407404a41500b1014010f40080444011034080107100040301c1c074280c0401880d04069443c082940c407501c500500070400105805034400c20703c504064006515804240380036140560300c1404102d6904001407030207030302e8031002ca4030b551402d65a9512603c691080d120401089050b400100c00300b0680741c1c1d00720080004010700c01c86825185d0901844a5088503054803811060040022006810045910346035018800080010000c80054020829074000030340000c61300c1d88140c10032010300124507018062030101c0f00700d2040180b00303260820341400300a111785c1181c04c0410566009070054401144a030065a00b400302601071180c0e41e0b0000c8940750142c0421420b2541c40e002c0101c2411301070b03c0c2064002400c19545406010944111410029004c1c0300182004200f441841a11110011404407070340c0c9044a040a11b0309030000c3d038 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 703714622 1250 703713372 703713401
    0xa080a06030b04120f081003110f210607170a051f060201020c0f06012115050c0307080609071b02030f010609021321030c020607050607030c200c0907051c 68
    0x1000325000768050701b60544180c0c04402c0ca41394541c21969402d01009e1051750307180d040228030140c800c1c0c0350b0b100c1800f4510384c10019030314658144111702240ca80038018010b5014403020071007102184034810355203031b8840e40c0e1030b101103616103400c40c59101c80c1410104001e01c41b41e0002001c0380c0e641d4190020200c40001e401103401200070894815121030702841a00742c1154200a603081a603d05816480080c0c004c00c486203520039040d20007010b0b40c42c11a465041c5810000c20003094542081529402a90941e480d03d002d1500420242001012985003c99013921038003650865604002000e02012610024804c2d5652051984040e401c050008110940d0200d8003180b030840c840b6031044003441612000c524060707951002c0d0707000d15482806980000d410481072010401c20404640203681c1a6400110025949402003107074006000405100400034443c0200180000d10000180000ca540310f40c60b4a4510301680d15100380021203504a95085011a00b18515480351400300d4401 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 703715872 1250 703714622 703714637
    0xe0d02041a0d0b090c0a12060c1b0c0e010905240628020c190b09040908070b01030219240c200102070e09060a09080f0c0109170f0a080a06030b0412 65
    0x45c1c00c00010170040d01500d50f0034990403440102003503150b0000d80681019003086d04a41000c2601d81010082d01c101c1950500e480480c01c1140100b0449001d00400982008110b80e04080e0703003080280c96140710500c0d1022400110401990701c1504132040c0071040c01102010f2400301001851200c1e02060f0f00b40580506034400c0042d0824008203840b251501042124403801c000ea0402d69410291a4a400035030b90f980c0070000821030401801200d0040c00b0041043d85184100300504a814680c0225181c000108105981e107660740a0078016400340c83c1d620351400d0742001c0321120109240900040650781e024412941444c1d007c9030038090a90075101c2c0661141c1c2c007401c0030181510a1090756016100094400104e544035000e040c0c4203203003d901d4003144030b01102d07042d0001215844a6596540d040f420040c1040e0002d003502551100e003824001c841404901501650812a081c02040c50000d845201d01d540004041c40d4400d00701005820281000580030302e1a01d402408101d16 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 703717122 1250 703715872 703715893
    0x1c110c16090c03110706090639020f031b030906030c040801050f07171003021207090e0f2109030601090623100c0c08010e030a0f0e0d02041a0d0b09 65
    0x290154110800142c0c0c1c03298580481c43e031b1510000d00e100c5606036042a6030f0f004541390540100000c0c2c41c4040d500c1e2040f40b420458940c90141d01940c1e010300425540000854402c121022090394286c036021083c4800715000b6444035421403040d00a941d078412000020000f850308024042c0094405420003009940e0b40e00500c40c03480d04c01640c850000c900c400d07584050482c1c0d4046c0c66540b0000c140080068a0358130390126088204802c00122142c0102000b48200c09891042240000d0302600a1140c5201a05034544400341c40302401400385d11115908503100300d0b5021144031070409001c441c215a03548490000a2a0714003491802c81c45480d180440c0c4407003030410012115004042c840108914201680c17080741d0694111200310a019000030340c481c00307104150b0040000005543d40341c2a40300b0081c00c02486801c03035810f110141c0038056285d00c5803418451015410744002030941c01c07110030448501c04240d201540582d00b000d003c001c011400f210079000711a01c00882c0c102c10740 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 703718372 1250 703717122 703717127
    0x14010f0302090115020c0909061e010e04120216030f030929091309050d0905010212040e04170a090515070206030c030c070215030105151c110c16090c 66
    0x81a100181d0320001140042c40440f1100c507042c65480c00ba40120b401c02d4a0000c0400c0c0c00110440302485513400640404c03885103504081c85100c000e03c004181d80c04e60402c00c0c207500048001c1e20250011307070a04a01e0203454000c1294032401d0071502038500b80703203680f445c11b241c0790b02850310124006006000d000480c0e0a4000d421041d12070180100d9685080500c03544400c1e800580348a680000c0810801d4200c074a148640158140680d01610018082c0742c0b01411a0200745d000c14110b40c0240085001c00d100f000544040c1c0d00200750b8100181ca850401e0151031045900030b90480c070700002e480c800c1d00d030050b54a108940f42920700644c101000c03a44091140903001d406900068100005180c01281200840c0c0c01454161002d00300344083e00415000040a0304d0000c2c0000000b0050049260a600b15040d01c1c0c00c1322546031038841c09030480e1403000010141c841550340c540c2f99a070b1054000c80c0a80c2c2c1214040c8040719103000b2015121501480d89109481c40c0c140f500e00201c01756803 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 703719622 1250 703718372 703718399
    0x1030c050901060e04092a0905090c10030506062a070602120d090f0b07051e0a0c1410050c1b030f0901080c040b070f050d0314070c241401 61
    0x90320f58903007880403040001480003501e85620304850250349021098443d2181e21203000401100b142d0455450b030911540724102c80c4c010340380e11081c0d446250503189546d01e003002218072041501c0d01181c00c3d21044c0c0071629030f0091140001c070507020306895403004952854901c41c5da810500c03c4400207595010140d89070710550110358002103040183e002c80c200300c0e0b00240540c41c8035184190426070562202e11030718105a41c810f001074000103502132107045041c8902510400d1070b20107445c0c038142d4000030b0315a80500700d004260090090401100e03070300610009000d4544410700703000d03600e466607032102103920800150f00c0384103400da19000100030000035030f400c086403208414508280d020040d500d140e030082c8407049a2030300708404220a0131510160456034850b4000300300214151403c1420f0003040c0f080d0302c0401d482c104203c031454046140d402d030007440f6410503d02c141c500381804489840e01c48418880e2a00701446034859200719408428050001c202a00d4280d0300c5020208800 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 703720872 1250 703719622 703719629
    0x706050a0c18150f05070624140d0308060120011b0309050613050a061b03061512050603160e04030f0f0c021c050a0605040219030f0807230601030c050901 68
    0x2500160300f11801600403184440c0320465400d0081c200b00496980c03030199148602030b010f845002200c40c0441c1c440d0850000040c10218030303500c80d00303005400410010301003a0070103410031a0101c046a4240d005440e43d060801d880394075845600f0080745d00700c0c00ba190450b900e0b490b10620030540c0034070a2103807081c456141c0e031140290880b5100c407038040b0700030013601405840c81d00940c0c1c40407000940c40c3c032684440348540907070608030201c1c0707050103000c03950303d54000104900b144c03903070048090380b1030340000310a000c0d41c90001e5191590000320703103095419600300c01d07d0849090040751441490f0b030351600c41e0b4400d1344c2e004c00d41c2d0702c0054211142c08070381820601040700d00c2d201d100185003021005042c0312101c82c4c55840c3c06542c6d1900361400d10003500030340c0d8565660050000354100205004080480c00051280c40c81c51030340c0b100d6100100d11005088404c0c041080e80402c4442401c245c0c1d01142c040840700b2003140c2c03041030754aa4000703210450791020301170000105810407440180c101c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 703722122 1250 703720872 703720889
    0x180f0a0201081515040602011a01030207031b0c050406060e281401021606050a1d0a092003090f07060305160c060608031602040b0a0b091002030706050a0c18 69
    0x190303c0f40441010902c00014555900c40240c40000c051220701c000a8402460258008100451441c140000329010020400d0407d0300410a0310040790700042114441c2d541c4144010304000d85051016003a48139400465200e0704000740080c40d41d0b409420804500421100f042275408040b5181c42011030145469160340c0c1016010072000d8a071080c041c1e0456818010f0320764040945a440d0310010b216000740c00032880100744610010381c4401000e8500c102211000400580070001404012613403003021205502d406403020391401031291600050000c04a0503101d0621107131a548030850094924441d01c281c00f070020b4214828004d8a00032003490915001c49840c40e00c040316004d41012003510281d84580c400945a40208010084e015010600080c10407070381c4104403da460b0a00c0d83c91050410080612100807072004458082404a88102c4184000b180503800c5009000c00544010301d480201308a070940d0b82c004294030301540c0d88038042c15000c0c03010300d02c0c150094002d0488 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 703723372 1250 703722122 703722137
    0x1308040f09050a0204050f060f0d0204030c03051507080c0a050c0d0906080a090c030201030b0f0d0c17160501030213030507120b0a180305031b0304050124080d080a14180f0a0201 78
    0x7c150034507070028949030043d405079038a004c80ca002490207a17809a40211003400c1c6108007007003400030a200c0c3c1d01203405203090345801ca003081c850040c503210001d400b50701840c000003080c51a0318002c20841d180000014181c8000c0c640d050b05c064800c1c2c800744a50320201c0d020200150354280140b040b05d0388183d12841c10041c01d4150340045001740001d0002c00e400c021003104030f048540d180025103110a100d0062020000d0800ea0841c1d080101034082030041d5001d440054151542041c000d01507032420b00c0c0040c0c50302c0085440c651101c95552014046002d054030100c2c5a900864618a030640254600d004984422510008403100f002003244494a220004400680324400840d04400c0d02c4400c44504001c001c00c03640b50740e0083d10101c034203a541d6203203000b0b0b00c0044212000c0c801441480000c410346040348192b25004203038070342d80402411000103801c1d00226071050181001050001c0c09603d045150b00c200441560450010b80c419030030400e6425000040d089200d030b41c1a0744410 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 703724622 1250 703723372 703723399
    0x4200604030f150207020910061d030c0d02061b01050108012304030c1401020c030d0605181914070513050a050d060f090b04030903030e100c08031308040f09050a020405 74
    0x5120f85146914450b45401300300c5440943e44d07100700640034410805550040619004001d000b03844074011410071951941c0c182111541d01145000307103058180c1709010713800ca0f07601c0040d419201e580c0070010001c400b0724140b0075010055210324142d480000007041369101c2e400b40c000b8030014600c050382d0340020143c00100000c1c460110359400500c01e046d5420503c542d460854260303007100c60313000581c1c0d10120310803014034014000d0400030300c0183c410a00324040342c003003440040320080050b0315170707014140b00000c000c13491352200043c205a04601c4502e800c0c040f0006100d80d0041d161009001c1d0106000b095505e04800e554045903401042800c40e80001e6595002600e51420b0502a1580d03450b80b10000c11294108148994440c1d9200c540301403c0d460b01506400d02da0305128021240241a804221741107040441015000030907561643c1c0c4400d101d0b000c00c0e1131081c0040c407c0f6004603002a131041020420020368014130030a00c4941e4032a070012040307004074840c6d168400308006800 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 703725872 1250 703724622 703724633
    0x3110415180908030702031c05010305030a08090c03010903050904050a05060306061306031b260a03050d0b030d0f030605030f0325210906080906010509180604200604030f 75
    0x70300580c248007001c40c81c0400d40c0c41d085450303002161031001682000840348242c81d020029040d021b2140c00e010040c0394116112582d49001d101d192a09000d501004103140100800090080030300040c000d11410400b403800810759000200d002e03010380e05100101e05a8801e60140b14406c0d0006801010150b03201e00070402468219081c40060f10750314400803000c07074a01082c502404490215562403940742411030600d807c00042124403040b81034950120900340802c091490f00e0b05407418517201c2c001c9403070007001020030700101ca0381441004032002c2001e03002110f0350400201d41e24104042540c40c0b09042d101c1ea501c960050280d0400c10004c416a50440840e0105101480341d00c1c940314001e9440d00541c0f000c100c90207110140c10702040018941c00451540913041903d041d949a043c814000e42d6554010f0156a214084010000344a10518191200b180c1c8055085a1080c1003030308200100490100b00044070210b410040c8041e41040c0301150704503540565100007d0880b9200c2 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 703727122 1250 703725872 703725899
    0x309150b1f0c08030109020406090f030312150503030c0c030d0c020f10110607030b3a03021011030402120304030515070e0d051c08010f06050306131503110415 70
    0x51003844941c00300d00700403e5405000d18083c2130b800000580e40c0b420070a0282c00920107920480c03804422a4082c000a075001244600340411007001081020380e00070844611880ca40003150140b0010a1400000034005501c110034003065040e03038807402c00d940007240d2080f803007803010703400c070401e640d9000c96402c12000b042210303001c4d4a0b000040c804842e110707908050341903810300e000a0302c9480d0800d80c1e2a101d039005080b40743e070b03050030710ba0090b0070060045010071441e107544d41c107009103d10406060003071080c0e071140c9410303903010001e900c00c200d07240180d80c1003600c042c1c0c01101212103440d52120000b044030140ca4100008102c0020000418400030700001c05030420410316075000206615102003c0aa4500c15000340c110500010400303c0710030070145860003044071840c010403910841482140c240c40442c64815030704e0360782c0c0c1c0c00705014501e06101c071030240d468135050400100c00c0c1ea07903400c249c0b841101d030398074450380500800040d604100551168040e2140041201c108110712 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 703728372 1250 703727122 703727179
    0x20a021207110925021504060c030b040216061401270908030f041203050c0a030e03040b190f0206271c02070503010b2205040f0b070309150b 62
    0x212000b181040004112035400a4a060b0902240d0340d0b8440c1095001c0900641a02c1451000713020945008411001003003014101524030303035984400300002d80c801d4000b54181c8030050002e665070032134500c0d925104284040203654be42d00e050036604c4980e44000c4602d04072242100502c641c9108248450181000030703100401e07080d60b8100320b00000d50900042c5110b54612410043c140c60300c0c0c103003000f401e0001034404e41014544000c2040d01c02c5c42c04207903540d21400345000203142d5200318800c0d1440c0b0864100c2000303e00003090344108000300d0702c004229100c040d5510300e000907200b28180ea481c0c83c01d0b121400322028004e900c2c0201160030b40c0c0e000010180340102c03480e52442c15244910001020000001078208500030301032404d0900501072640c5e001e0795501c00c03024030f625600100d0300034561106110781d00e032004a8140940b145115009a4001a041041d030900030000340007816101806c5448820550400524254510480050440c0078203081a004096044040031260803038 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 703729622 1250 703728372 703728383
    0x31305040509190809011e140a1404080f280605040201030603021009090c090b0f0306031204080715081e04140f0606090c04030c0e1302060a0309060f020a021207 71
    0x6180d284403000200343e1011030007101c81075a10103445000400c9464040b998103900c0e503130344103028541036000c0b1491f0040d1100d04003940d26544126402c80700c8408003150800c40311004100450b07851004100604e045030f03e00107c410070f00c103401400c82d83ca0408840c2c07980c0c222040c5460408070b9082e400072a4080d03c145000184140c4039400918800784510882001528040c07040c4030300c4805201c0d0b6484601d803420724000307107440d124100c0c032541700f0725003000406e0034080f01140b410748080011001c440e5405205c2034495803030b042c1a581c1c0320400e120341c503001094902030400160249083c140600150b260f107860350100c0e40044454200e0251085030304a4450004046a880a00c81407000000d1600902a581400420004088805070014011210070402080040d0800f40b40034210740c4c1842022040356200703510040c10304081d02000c0d411140011300c1c080c0b0b065140c0d21203890b4500c9200204411030b1120004000c0380600903040c00580e00c20048c14603c5840000a051440e02c0394 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 703730872 1250 703729622 703729633
    0xe030c0607110a081b0d141e01050f0c090f0a0e010b040305010501141809031e0d0e0d0e0409150606110609010c020714060d0501080f0f031305040509 66
    0x81000c2441a4000e040a40b180c0202954080039407400c240c0200c01031244500621032200e035a4a48003400760102c503014801d02d1045110000c00000418206411030701c03400780c520408042c419007a1201c040c00c4418855480d1500042e070b080000c1c1101c40c0168460f80305c50b030802c0600000e10940001600d01107500c500c9002c0700052100140c0d804502810b900030040c0d031614510704e001402d4410682064840f40d80301c5000c08080d450343c0500040c210b00b88580d11380161540310f85581140708501c00d040810018156110030400c0d41c1c001407001c0040c410040001e40403800b013554032694000141000501c015031000b24074540b641141680c1c602440d600c03a00c6030010102d9104480b00307130340510040384619941090364135050101581c03001c0018020f00c141d00c0d00d020000e441c5d8025000b80810054075100e000025106d2809440208980b800c00300a1540c45122283c0d580802010b0012144681c0c1c004540b0400003005032103540d02d000380b4280030b0a0420301000083c01e0010700401003445034 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 703732122 1250 703730872 703730893
    0x7030b040c020309040c0314060d0f06051311060c0a0303050601050d02070c06200606060714011401080709060303021f0207050a080307080f13030f02070f0b040509010816060e03 78
    0x16403041d803004400319001156509035990030b0200b0382d000d0134100b0041c14a0311400c00224201001f52a0340040101c1ea40060392600e481c041c203003041c2c03000001e0612454201003000d0412240b10f40b00b0128040e40c0a8041400824200020f03032047c0010b85415401ca8004900001e000c0e4012a03008001410300c50300380100c2200c00c90490704106015078880c16014802c010054100c404d001e4455040b07005d4422000d41c0c040070641e00d900107446075000300c0e00010f02e5400e0008030500b0b22001c0281000900011171820700c04c2002e43c100b801060001e004107980000c04140a100741c60480307034140c01601050301c5680e240101201208540c032002902000041d00003001440310a0205214002880d164204203400610094000340181000d240b8a010f0254084840032031b0180c86034907242090100749013071422400e00e000d0b80c0c0070322194000410040703481c44d800c41c0a4010743e10f00b518440381030b84c0d9400341030340d46040002c54409000c0c1080300a22a140c8112000918094042c0844199800 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 703733372 1250 703732122 703732129
    0x31c051308161e080418050402063f04050606012c0d06020417070812090d0201170703020c12090d03050a0201020418050a1406010806130b0402070525060206010b0307030b 75
    0x1201c1208540d41c19000400b4050340c030011202c0043e06d42089001c202c203180660100c6c109114800144148a54580c80020103c0000081200b0007000480081c0305410305e2850b0f07a402181034904803024043c1c103000800951240c00003200905914200081003511030310700da50301002d500005a00807008860520225409000401c0141561990450010256441a814001148c1042405802c5040c040300380100000507110915000c80700e50f00782d40c2180c0b0040e14152039580c00d40f00e20208078410000c01c160180e029242040a13a0b099a19000d40340000203140d00c1502e5a03907500003c02e40e41d14020030b00c140007400a0030070a0000614140c0c40c0e48403400308510340c0744005140791716407040280c00350240c002c401d000a10103a10400c282480e5001902c1c0c880024500e0340108140a4060344103051500b1011a80201520855443c25523003800c035202c0030b2910300c015090201004100e580f03002c0807090380840f40741340d0150040d6403e101d03a801050f807010746840704054480713408503000d64 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 703734622 1250 703733372 703733423
    0x20607030c020907020309030601060e0103021b0d0f0c02101b210f2c0f0a0815060a0807032031020a08010312020f031c05130816 57
    0x90003616100c000803002d104101d64000010a0202190014004065140c0b000079915065a1950410140c1d0030381043c0100c000340540051400c0c007071015902c100f00d445012a112409905560311424061000340003030340d010b126210000d410035540c04000c20100e105400c411440182401031540303140c6251510320910000703a2020b1200c0b68a140c0901185030003001c00c102d40d4045e42092100e5264403003402026085c0d008400c640260f407440d0055181d84c0d003000a41d801400101108082600c40101a60b1849012242448008107001181c810b1400301260402c8503850b030300030a0301e1401c580d1504000100d140c50301c2031401c008d0704400250340d07030144881880c1100d03640500074030100702e9078030b40400d10300140504400c0c4104412071026610440042c103590300585200031031035048600300d02c1d010311403840c41018000400c0c44c8100849299150000c41d48006050141c1d803a14001c020115000300c00080c6040c80400101c0079400001e140b0848440c020061041d5100405036802d000c103 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 703735872 1250 703734622 703734637
    0x607050c09161d01050304060b1c0309090b010c05061609260c0a051507150213140109060504090e0c03060c2104050c010c05010b1302040e070309080301120602070206 73
    0x3160300d1103030742480d43c84110a0040884a10301000462404001810303030f100250024114544030189138078240c8030a451504484a207940400c0030320624140241081d4107402103d44940c20052184429031140d403079401e070190404042c292640b64070500e00f12088503010307140b091125881000429568500c0d100584d803042c0d005d2416501c6580101c24107080151041902c100d01c40001070080f601c82c2c1a1a841c04c1c0c800611040e55034603203003070610b42c110440070002c0c410b40c00010030030180007110203180200c440844041203040d00040054820180c00c3c0100000680c0a200c2048a0340c2d40c3d800c5542641f0b40039040d110094040302c00309007004001c4a030800c040e0300000e00358070b184004164004148101040b420703410f0916580311900d51254041241c10064078900020500c04203500100c04420006d2010340201400242d402c0a500284916001d003510038000402d8140240100000f82d23501641c1285541e0034107d00641e0044105015503480d6802d01401005032940300050801 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 703737122 1250 703735872 703735891
    0x40e1617240109050a2a0c120e10031b0e18010e15030106124e0806030a120302041206021210081b1203030a050a0c030b01020a020607050c09 62
    0x4541c18403c40e101a18005030070320703050a28103000e0484040320000002604600f018440e01b414100c0201110408001140600b541b1205051104095080108503410309000c1c0d42c031000349031000c082642207030000d14001c40080d00094044c50050320aa65500c00d200c002802c00407100c00500386408a030781c2c240c0149105441800c1800b02520324149262a00c400840083c090142042071825030f200310260003c1803100d00003c01198070801c2a1116046403030452005006140c00940c00c0081e140c45515401007441c00c951038010798480d504080c45907a0203001000010910f41da007041001000005400701a4240800b2815110441c4c540c00b40c02e000e142c0142e101d94000c95a1a03250201600b0001c19000c0e602c0b00b04003084001c680200e000c070304242005016103c0c00041003030944041807042c2c0d41d01000003001004165640b0281c010f501c65070b03041000c65403c6a0903030441e1070308803505025900024900f00140380c59030080c03628a109000f5a02228040c2000c038000420130f4035903020 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 703738372 1250 703737122 703737193
    0x1140705060a051311062529131b0b0c011a120d05030a090c2403050712050a0e01060602150705090109030b1b03090309040e1617 57
    0xc0b000b0031070003a280c12200c001861007008180e0350b02d544640c004051821b002d0b00c0f0101d544c4241212205640c4030000301c0514009441030303207103009900300c0c00100c410aa00310b01c501c04051220502801300b0302c1030208486805040c00c882d00d4440048204101e002440c044403200402c07110701110181400c0820007001103a00342c441c0360301c18814041401110302a0350f43d148609001d00b40003503042d60400342810029aa07454809000010701100711015080d0b401c1c4410024090005100b135014150401c0b009031242403100d042101030f07450958440c000111040b0407860011401e61005030801084080010392034010500e071420b4a4031a480080035170490b03242c003008620122084c5502020341c2ca4105d01c1c0102c80750000e000c80002e4000503013a0007003100020300c2d948281d0074146582d0358081e01c807600c9103070001c4900e80c0c9502c0002c80d980613a040200c2d1b05000d000005560100e00c101c000005001c6040ca26000b102c6400c0d038462903030703d00c1502058903a8802c810541d602e1011009038144 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 703739622 1250 703738372 703738381
    0xc05190e03101a01171b13090c05270927060f091615030c050d1a031b030606042301080a110105031003060b0109031a0703050f04080412020114070506 66
    0x425030100140595480c0d00c0400400808043c03020241242c6c0c03100445403920380b0b410b20341d80c030a03030031841d00043c01c200e02d03280c1104250398108015242c00b010034602c1910b58401c828441000c3c041810340319400c008100c0202d002c140104d0741c081c010346e03440c0140c000c4c20030241405910700001500c54680d16901e0009001542600b444487c0c00d241201fa112000d00d450100c10342c120b128181c0e10b400800da500d8403541e50b200d114030100d503039004130204184501c4214004407404400c02425441c480d12490401032030340d03040306d800b400042e40001c010b08071503564501880080c150807401c030702c002400d5403602854201d407802c8250107031044000511660015190920100484200d424148034081c4200100821a8684001569402140410070b0000080184c5051620340c00091860f106003000441c44007254414506c94002544e007408140c48007039440060800644001d00107000801c4240705150035143c2030b803a1350b44185820024212981c0c010046c40c0c02402c01100c0c6500b1060901 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 703740872 1250 703739622 703739627
    0xb18010f06080c071208040f12080108010e120904051f03060903030c0305090c041109040c03090c060c0f1103101a0f010f02100e010b060c030304060c05190e03101a01 73
    0xb60700030f40e2042c515103000321545802c0401c0010840c0c034020490403c2c005001c00c0510903903480c08681c070400b0091800103110014242080c240a0400726618119600004070030000f9074079450901d29028a1802880c40d050001074070f401084940b4001c9101004400001d40b014250001d50044d903000074102e000d490010181e4801c0200d000c10036040c10280003520f2400700301440a0340c011280000c099a40341c03140d6216000e8004402d5005240100c80d13040c10b40c150700031603c110720943d00c210a040c0c44071000e0358807044020000e40250f28401c040000549508185013078018010200c0325454001c0c45c901c000c0c0c0300c0f015944658162807800304107450520407214100e0606c242450100e043e040c03000256a140e101500724a80703900c800035400c103000c080d40301d0904000e01602c0290f070b4000401610383d40f07034401d0ba0100da10724584069881414070450a0b5034414004030020f22481190040460340302011101c6181d1500400405483c4035031300e88240b900500e81d050380380c1e01d010b0505001 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 703742122 1250 703740872 703740887
    0x30712060e01020f09011206090e0705090912072009010b0c0c01091809020d050d0903200d0f2f01020d020c0a090903021c0e0913030e01030b18010f06 66
    0xc21102c0c2e0061180081131007101003a03400c500790070b01c0c099461010403003171007010300304030b6101d402d00600c0c04031504071a40b8049640c01c155001550340314010b4032000ca85503035404d806401c0943c101001e010040000d5044449082000120140294594104400104d801c0c0f0280d000e07041d101c000045c0d50400d404140040e034040c0c0401d080203c3c0d210301c1e0249200003011720260000f0825510fa455400719030745c003000c40014903000000c03214040c01e84940500088000c2c0400c0d280d84004403500e44401464107000564900c000c0d0601c140740700c9136a598100001540303c200d8000ca000030351581c0002101003851111b030600d41760005035080180000e402d00c01501969821900981d03c03803880c035107407200307040210b40012000046803241c1d070034201d05121016000b030032030340b2244400000d1aa84810700c15104842143c9100d01d640b0f440042c090580142c0c440200410380c4c80e44245510360087e840001c2c0e180c0040c0c490036800c0e03298100c060650600f43c018203010a40b2100078000701d98416031 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 703743372 1250 703742122 703742141
    0x10090e150d2f0d03080106080a18060f140106021c11030a0c020a09090305030c2b05040618051c12110415050301081005090109081602120d050a0e06070203071206 71
    0x140e640f41880b994500410070070050050409100141c408900c81e581d0755071124010074211400178a407480189003920181c03800d41621542181481007450388240c0c1d040105041b21100d40060141c54205000108210220326600c01801a402450700d510b000c140010000039046981d0304031890170b6441003001d4094103400c1005928035120420000a800c901140e800122480031680c841c06103c1301d640c1010321090340c01e0485e900e484020030805801e604007a020310300c01c080500c071113801c00c2c43c041224005100c0252040d80700140e80501da140b103070040130007000b8910380548400390808800b019909051910b8820000004d02044030702d00002c0c0c02c8517008454039044c0d185524114800b6a00c46603c0b2181038419034071030114510031800d50001402c01c3d4009145611503200750301e104005502e010003a40034036040103491400f07541c080b555030002c038000c0d04c985013480481c0000f10360701c06c00d0040903030b0031010811110002d40d5013005001d00820304841c0342c03001a6030514108080d64112030 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 703744622 1250 703743372 703743379
    0x206040606060f09330c1106090609060c0106030c060c060506090408091509041e1d06131104021803070603020901050702040209060706090b010510090e150d2f 70
    0xc0d001000c40d0b01021542c103d41d620002c41d18208103528040d02000b4034000400d042d0040480d0490110b07400034104a00d890040104170f1076003c07c0c90a00000348074140b42c2d070354807034810000040385243c80c0b0090f1612080c683e00024082d52240c3d503140600200b03821000200d454660719004100c10b80c059183d10a105503691446801d190361341000714066040550320036144880070000c000200b40640740c0743c04004100b4403c1c00d00740b03400030545a01c60b6a81920f21824410300b901c0484900740c000010000c076100030a015607a109180c80d400b200c000080340e10074070049201c2083e40d40c50014055207549264081d03800f08025082518049a951182003807500603c1001c50b00d03a006002d0340c6181c4c0c0c040e00c015a0301c0c0a442c0008185101d031103001400c551a04003001d00380310031907031024103031740c001d4812803c0c004006078295034942e82845000096081d440001d40c0c0148030700c10350820a5005404000c54500d69502c154000030f240da0070b0301811080c0d068950541842c40125902004240d = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 703745872 1250 703744622 703744637
    0x803160306080307080f0c070b0703080108060609041101032301060e03060c032a0c070806060604050d3f02060a05090303180705040f0203040c05040c021c021903020604060606 77
    0x41c940b161a070103407400c0036080c207401066070718005000c00c003282c41c4580035400fa40c480c0c6403100440991601b02141c141c1c0003e402c1800800c25000000f902401303424010305503426a40d85a5400416100042da420704060720390032551002d036091551106012040b00b649a800e41c18103074002c0000682020b28ee2190b070290051050814078002141d80041050703900340c85007502c44081c00781140d44954010500a0009844030050001007094400c0d6104c60099860302c0d01c862007008001d004900607142c1c070a03028003007500021007030920451040082421a400c00d01c1005845442c194040d4890b038248907030407141e04099506000c2e0aa100700b25070010001401c0c90f802541e0740380001070403400e114404d03c1c0e450b02e91001c100550001060020414000345031541c0c120000b0b908192000c651902804102207040d00e000c1c050050000310b182e00030000f071424080d10740304900c004c01c00031055003e0301407050208a0390502510790503000343c00801040c100351400070126400e9078030420400142 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 703747122 1250 703745872 703745879
    0x50f0c09070e0a030209040b0a051b0901030b0f0a0803031b0a1d01090b0301090b0406120f12030e03040905070e03010b0108160519020f0709110702060c010f0501030803160306 77
    0x202500250001514070386100d020b0145000b0407000451030304003075404035605040104100094641900c00d5400c110b041c403040d03d5000309c02c40c2008a49030b81351481c080a02809200b94440d81c0403052801f002040c400440c2d04243c0815131840c6680c000402d00e4000208210326a140d5640c10403c03440381080d803030f10b8031261000c01000d459413100c0c101d091a90307002a092540e889044810058107910b442c0c141e9a5a5403040b400003405030584050040d0b081c108001501c0c0f0094440c180e0b141e401080441c1842240d503100c1d0320f01c030700c10764108040c569100445441d14500300050b04c041c0144150000300342c20504405403070b05034403031140c611036814052000103c0e40d00140294211070350100c0400036030700024080d0b541d8000d20000101c00302c1c02d03514100c007e680c0020001040545034003070f1814503032903641800980c1c1c000d08852900300c404015280040c101000140000e0088200004224441800f6141500c1081e0b03c2134513a41e40200610281064000ba01640e540c89400c1c20000c5034034 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 703748372 1250 703747122 703747129
    0xd050a1704052d0c0f0306040303020a0c12031a0415211b050118030302121b06040c0302040b03010b010215060402070f0311100e0a2d0b04050f0c 64
    0x44800400d080105100124007000030400105100e0f0764440568922101a880000c005440b50b0011028038441c0f0750940c603407800c2a558500b121040600505441d40e2161026806944001805000c100c04904035001044240c424108111700c40d81d40880c07688032180c55201c24000400407070f41f145250500c1c400c880d035248900e81007181d03400e005201010641e01d100e10705114a04034080c3c9071105d80da0450610f0000d07844a5020745209890309035a5080418003800d88a103503000040261b407040c1c20700101040801d02408640745041d202c881e0300712001d01e0141c282101a142215152005841441189094014084c2d1001c040c1d00130000c0b00c05410000303644040400309103640b02c00201c080384c40380d04c40e501220f0002c0d1f00009001c000814074940240301d0030001c24050301038000c0301c0700c0900e04000c50184105500042d001421011142c0e2036082c2c080c1030800903107414801d00d50208841502e112020407640e401049801c0341032401c1e04280303040c40f080710000e20f42908800850013150740c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 703749622 1250 703748372 703748387
    0x10501062c010e06160c2418030c0816140f0f0612091e0109020d02061c06061808061b072909010c020c0a0501031a040516020d050a 58
    0x1801e80000c9921401d00c1d00103030380d544402c0100301d810000010303c201c40b1004131301c1c10414803481000c00b40300d500c0c0d503070780204000041400d990000281c5c1501c04484548505a100803070700c01285440802d555036500c04089100d81c1e40900c00c0750301300c0003595001020b02d0444c800144100000200a155a500001c0c07108008140c090f109000c41000d200322611403800313407403600c0b00314000c00b4410b0074458030480d5580703a4009400b4070001c1c2009444501d51043c01401c1c0b850303901404020691401c5d908001080e00840c00585040c0c80d40700e00340340f08128a00400700100025100d2032442044010140c0c0c28580a82140c525940004244105940c04004881151070414402500d811081ca040550103074083c90740c0301c4030313010200c064581c0e900c0348130030341e01560205d002048100b500d0340069880f40c01c250320f6039600024814003000654000d42040044445091600900c2085040020b04a40d00ac1c0ea0909502100e100302c580e02e582c041100001c2e4442d00d0a04030700384608120002c2540 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 703750872 1250 703749622 703749677
    0x1b08030c0a0203040803040b070b0a11030a1e0507030605101806032f0909090a05070b1605011416140301120201030920030706031e05090a050a1401050106 68
    0x1c150820798420f00a440107445e154050700e9980fa500c54601c04242c02111090f120200c00102140b8510818410211900844400f00d03085545207602d100042c0315207500700c0000742c1145d6541d10359001d140b0a140c81200b8644000400e281004140004c2612481c82c03030050203007401d00c8604003503500c1080750440749240f07008140c1c403524180000081a0301004400b2100400704210780d41150000030344548181a90325a031140e076544030386603550079581000750103038001c6030341408201c2080008050300b0340074064000c1000041d94441303003102d240f4001142595160380034082500038944015005030042d02e0607603031840741400e40721110700c410301c0740c000d440d0755458052085900907000b186000ea000084d940340f003110640402511200c003c01076100c0d0056140126000f406440f542801c0448250b040b40e9a04d081c2c008031000b05800380104a0500c607050314003000450800c110a03905100e0300d85e1040c02c191a1441ca801e446040c0c00000506c03140d4560655a050b0b0615480d002 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 703752122 1250 703750872 703750891
    0x5060618040b0109030206370c0b060a150905150702150307140a231c0902060d0903020d0207060903110103150521060a0c350f04031b0803 61
    0x45440140c44c02041c80d800250000300c08211181c0312600712000c00c0c0c419412304201000c16425501d0030400c910300d00d4103003011841540454012650fa0124564440342c0904601203007519940c03081012004100b81c04002000d0280500c201d0a04d2510858200400c583d0a070800105500003426040200145400c00700040b00250009100b1003070403049402452140b5a2900021001000036030050420a11206000303040c00c40603070b01d1001ca54900c40c1e0404c1c4c914406150840e12000381003800400d80c0e014038280581c1920803a1803007045283c91083d001800da2444264000c3d00b0090310340e104130180b040000040020400059015409000900c0e00084680f42030700940d04816864100070342100b8800811305003e1800d0700102c0010301030000321030140da941682c0074155506031a2a2001031040610007101c87e1190008449800726001c00194450700c90b4242004c0020480d4039120401104061005040d006006a0301a075420222115191160385a8103610b00c00034000551 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 703753372 1250 703752122 703752131
    0x7090f1a18070c0b01060807181802071a0c0a08010906030b04170d0c0203040603150f2601090320013308030304141c0c0f030302040b030f01090506061804 68
    0x440c6480f805141800070341c40f030720101c0d0550312040000c0144004889070000f044000f90360302d901e10952a403940c11038484400c031615441c0200e04c910003a400c0000200d81d910483c0321500022452034691074030901200301c4060b21450340401c024210001071f0310840d800b40c60801c1c00c1c4007282074401c1d034560294005400a030741c100401d0074810035214245048044501c1c20300030b04460b03a4040000d0046410ba940d0510008c030200c261035204003120303c40c69a001d00c0d0703c00b0402c481c07a4900195604815080440c650100c02c14800310f094a0410500f02c001561070001c0c5124005031400d03a6034102c11000003000318152a00d40a806805440c4c0c03030380c00e0b005100c41c005000410032030390480a0131548007500d882e41028030b441c0f40703407038041500e50074603018407013200390405003c00c044000c14140385e40300d0060000b140c48a848403c1000c5043e410160204004601d4000c1e241c025030013280c0c012107a29a640c905048481107a00140c00c0a1044400b084540880c05605041c044071000403500060b = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 703754622 1250 703753372 703753381
    0x1503220c0902130b03040c03060c09050109051216090213090905030d0e0304050307080c04050f070f030905030f0a050a080a11092106040f0302060f060604030b1807090f1a18 76
    0x290f503210380d409000f01100010811040204a60103032003103a1080e0424441c0d00c443c0300c0155980c10660048500140107444100800e2600920480c00b9000d0b45043d81d41100410451040c59140ca4110001c2c094000811000b2807050460700c2c0c0003020b071644c040051403e0350f0703100e984a1040c103008c034041545510b0031120102f020300842b00100030042c22561000d41d107500e001d0311400202c0030307103104500d0800054215005040d0092103003c499440840c00d403001101135006000050007a122444248101c5e15054800001031a600f862500c0712502c800c400e100041c88407100a0900035010305011500030107001c00d209468081c1c02c100c810028080e44d0529040c0c2e012000600703500c00f4030401d002d010074002d905050300f03031442c080d50075075170269104074000c41041002d65449403c0b190401040010540c49030080f50803110552840f40701020301d481152030400b50340c2105100d030713a407010141b207083c40740d1043d0010310000e901d41c03000c0c20030072100207200300c0050802c007024608201c0008 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 703755872 1250 703754622 703754647
    0x2a03020f2e0c0201270618080702091003050a081b120d0f15030b010e16020607121e0c121107030f0909091209051e1e1503220c0902 58
    0x2428010800c244207110317409070385188015100650401e45005d40740500c0f034211203640e060140308103604152000c0c41c100c6103900f480b901c3c2c04002c0103c07801b40182940840020400d1060700c18090252188070f4482041c02182c0101028131401e60000f548000490b0344103203030150a54241100503280000e08101e64400c1101520030b410719002241c00c07008001c07040050f016010307416205005c817022110754601f441100c0f107081c0b0803c010056401240010051886a0052400d00401802c0810700c00404802c1c40007451580d105004010f4440c041d04409607440740c1580b5914107044410711540080400202240c400e50f04003504100070209069090307070184441740d0041006040030441442c15050480c521602c103184540001d040e00d00015aa2070700010702d544419225658a604034010001c0151200c09a141543c004003a48009d5a080d0f440341c130044030500c48546400c0d50b9140c501900d101d85040d060103120b03100342c82e402c500b004c42d10101f4084107480000c9401130390344c281603c11 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 703757122 1250 703755872 703755881
    0x60114060c06010b0409060501020d080a0f02250209092103041b03052401141003110c0703050f030a020d080c040312050a02061b0702012a03020f2e0c0201 68
    0x208071284507400c00002c8a150300d200800c1107442c1030508201c280d484100483c3c841070b2851380040065008404076035056041c0e440910051184200145024200f40300000b0302411218000c0100003a040340c00f06504016030225806007680303000d0400ca044130007142038220389402501c0c0b0000e101000140400080303049020424070744000e14036030182d42e450401d40c1d94074150852641850b0784204440c40403a10040c0a040e034800c041562001d9400005000001d001889540c04050321905500116900f400040c000400440007074100c01c0c0c1076007409450940c03980306192840d401042510241070340414503070300030300042c0b502c50318a4440b488000c8450049400243c800d200c828803152007940c010000b031010141c0340e0262011561403100e04040d004000030200c00b0751400b0008000190300c224281c41300180344c092240e0100e00f100ba0740d00c4040f82000030450141c0c1c419841000444006c101c0e080250408055484243c0d6600c080090003040c0035401e41c107007075200d09014000034000c4d0013 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 703758372 1250 703757122 703757137
    0x90b2e1101021e07080d05040f261803011e09060e07060c080c010608030d1a010305061c050102121008070e040503250f0c1e0e060907090f0b0306130e06011406 70
    0x409010354101810009c0c10f03007007800011202035181d203c1c5e0101030104000b07203400403e807c00e107660804001c009203d00821111416503815542e42c982000c5501560400030b0020088040010fa03d040911748001240c0141c041800300f903200c0001004131300d503c00d13000752000340e10540b02c41d1105101595035025002e42d41043e0139502000c640039140021544c403030400b01e0b20a015104462003802c0054088401c20746004e070304090b4200a010308070711001c0c40365412501c5000018507240400865250a0700c003614079181d5002030000401144074200680070203010fa00d2003c00c3c09040c2551195500d1181030410322001060010318070014211820700341c08241c02c00a010403d80ca94580f56054200c240501d00036040381c0c0ba115081d506000392044281c40f1101200642501c5100410405030002400407041109030040440d8246c04e8440000080281e06905500e9061500c00c001c03211640100d120181c9180a110001d00f040000d807050456010602e0a00140920700216141c0d200e1081c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 703759622 1250 703758372 703758397
    0x7080f03090d080f09120c030412150b19090506060421030f1107140a080709021822110910091805070801090b2e1101021e0708 56
    0x41001449800400d41003118034440d560b11070a80c1e00c881120904043c1914104916804140c1c1d02e06d000407001c1c01001c028075040c0440b4103145d560955208c08180c0d00408440c0442c08003031094480395540541e200c0604119408900040501d0402d0104505849080190742d00c41000c02c105480756421035014000f01d0119481c2403190780d410000f4005c130300f4001c81c000780040504a0001e8450503111030359082c0b4001410760140340030038900c0940f036400c441950011601c40000345004040121500a100ac40704c0561107800d40c003400c1204130700242c04103006041c10710151000d14541a5a9a003035880341e400060900c0d0042540b03140c80c09140e841c10f4210010180d06c080240c0c00038424002c42d542c00801c110460559400d4006981050354001c0106004800501801040d60804114581c0c0a0000c0f080c0000300c500c500c0303800001800d001079041c0300c1b41643d550700b913005204510060800c0300030f61418401c00c1c0312840e5090703601d1200c0740010b004104401040707004021500c440d4040d1 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 703760872 1250 703759622 703759627
    0xc1b030c06020f090f030123101d0108010e070308040506030a0b0406080f06090102070f02090c070203010501031208070c020303090609010c051c020d0305090c0904060f0507020c01171303030207080f 87
    0x2c14240d030968044c0b41024491000f000c1d081159141c14040e001c0604070165000c0180d401c001000c23146920098111031800c0b00030080464002e0808114078004651480b80c1d0895500d0300d0003c80c01c403640003207100d5498001000c1440441c4031001110100e035030598045950b62740ba80c8005000f044120b41007036015044c140006807003440060b400c0d8034803510400340d071443e40ba1040c58900300c0c07240740d40003041c0e40800c660301400351920000c0140e118040700f415070b02c0c0c450180e000900310f0741709030001c03130f25000303c414203c48142e401215035a10540d54240900070806070f40000b5030b02e00407140a648600320001e85c414045e48100400e54085070302500703c0344203103d4122072007040d03680307110040014862104c80d04402440781c040c26000e1075443d000380552880d000d041c0010910300610940e80c01e52100540d07104900341e4440c00344520710329800b81c541181080d000409400b00050040b44140c180010304c102c0b0041c0303481d601390003030307050600503070300e0186144c0860f00e070081316007001181202 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 703762122 1250 703760872 703760887
    0x90a140f090c0d150b04020301030c0b1315090e0f040308010b0f0412120315230d0b092d03090d0609020d06050a18050d0c0606050a14130c1b030c0602 66
    0x2406548590130100c44c42030280384090024803080303000922000e4071208010404210111550005107035248841c0c0e000300e0381c0c40d03d49043c0406002d10a0102c4c00050368004c042012211701d4800c144c10103c68080c20310281010b460080555206015592454200140d12008000170500f114020a05541040d40c946080e0038031069403504090700d40003090500b240d40013000122482071003034541244502c04041c0354484525800022103104540040856015101107003450b0b4866119a512200030f090004d900724420380041650f10304824411078005034130b44490f10100650380d41c2d810690701425094258200f07800681060310000e508400c02c42c16020500105400c071a01c07641c0700080921440d070b030b6440c1310a000060084090216041040f40a0600340300c2c1d00c1c034420302805650041030342e9449800045a00070b003541300c41c040c655010b422820390304003c4003401c0e004442c2c86040103200461a0064110420340b0b44001880c0d255590510825000b0141e14059a0b00721400b15125a0b4 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 703763372 1250 703762122 703762133
    0x3160306050d0b010906080105090d050903011107060219030e030a1404030c08060a063015150806090c0109030305030c1c0b030f0a20060f0f0306090a140f090c0d 71
    0x3420b00644100740c0c21b200012800407014000c650281c4465002130100a051440c101da9540041044561554031016106001c0344c281018100c2c19008440041c0c0d140f01c02910003410480e203003903e44c1854240381c40e6a800c030b103010094a41000c0241008050350350040f5000c2d60b04c2c8201e40004000726564000401c0090780022040d2144840d03590410045844003200000703450742043c03c000b241c036100caa150700c444c2c3c08550754000c18461180f200e0b01070502442c800540d140801c91030150018000100404c0600308611f54200d5200ca0141c005001e81354002841030304240409010321000001013048103544c0c4c000c4440640c0403201200c0d075a442da0741c507100a00b0190401078460b20074110381c15500c100218a45181c150300a10000c800c09401541e82819220540c04560205003400742d00000f030040700041180081610b00c2c00d5407480c0080802407124030103040c00c5140d510746242414050000118613410142c0021240942e6444008aa2401481042c0300d42c204000f85840020440c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 703764622 1250 703763372 703763393
    0x17130e070306081501050d03050901020a06090b16030b0f091803040e04113a0215030a1b1706040609090c0e150603060f0d0804061119020603160306050d 67
    0x10303244425624a4018601c4e49100e41e04203000b6a42d00080800d60080040c0c065030040c800088180151030081da800d4407814221108290300b13490f00b40000d41044a00e00f1007110f40c0c802003016003070030004502503402240316070441800c480d00400c491400b1604603c3d20300540c05000c08a10100e0f59902d032500d209140b1200c0a440840b140e21403403481c80340e1842d00c08403081441100800708114004c1c000c00020003c00c01c2d02c03c0c911041e41000d2500056190032800d030900c031080f0750700315542e030802c04442e008640601194036120f8502d0400489403561284400c4800c4101b640300d00c1e02070b190b080c001001094507602420946140109260410481c04c550740f0850b42415883c0c9540d40e41c4e0360301603502ea40000c07412036002d20200b001401c02c0c03a010008054041019005401e0300703055540308005684983c000c003011620030090580806e80c10040448008100b01c2c40e94142ca4850340402d527a404064107202020301c1d110320540543c3e1080c2d201c40c00400c0010310314003070110345080425045 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 703765872 1250 703764622 703764629
    0xa15090213150c030c020a090e01020c06070207030312091a01081e01050105010c1502131e0f0506090f0409080301090212090c0f010f020c190806060d17130e070306 72
    0x9240320300000980300078030b1829041030300554840903d41c510325070341240c0c01d00510300103d03801350014601043c45003003803080000ca002d420000603a580c0e101104c40d032038510014910804c6502c82c000503c0001c2e440168403c40c009100c00c0450541c01074904050800a01c1201d10407543c1100000209900005031140505054070702c074190f0034010124031400d030383c000d000d0301e404181452600d01c00900c8007a55182c0f25002940700504204031000c101e003500f02c05a100103503010105d0001c040070150360780080020700012820040e014501008075501d03000e981c8d4200e104000c0140c13070720307501d0704d84c1e4110301a00b1303a000110583c2d03036840e50b151000075089628500ca81c00c4a400014202020020780c64001c1c040c018a10003200069100446074440707009900d00843c007400840340180e0706d0740480d480541c03a801217421156030a1000561509000600d800d100e0781120300340b80301181c20010b001040c8100c140b0015910004190a901010102d9002c11184071340030f420017000d29896406801034 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 703767122 1250 703765872 703765897
    0xb03010f061e2103020c0904050a05070b03010e0c0c010e0106030c14030c13020a17071707030c0905060f1e0702030c0d170703171807120312050a150902 67
    0x8000c16500b0111800d0308500038880c1e082e40301250000c0d01c004046501180500c00e204a03900360758a140414104101603804950036030000c203483c1c04101050004101601e451103a003411076240183d0112224000340c80015801070010321104c0806080d006240e015140d900240031907696490075052042c40352150180101800d0300780c164a1401003910701e07091030b0003003034402011a0604410000c0d070000d0340010a000074403590400b5074046084aa00c2210580c540304404c1c00340100e125212070000340180308141c509126184040d8000001000384c62055070059120904c01038929910310030000901c500b140b64840140c2c01c0b1a00304020039095209500f51030b161400101031001d0b00008580042c40180320494040314a80b00da00a070038400c0c0245455031074803820510038100b082040d500140301c1201410105100f28040006030000d0a4901c0c0c0e0244404440d10b00800000701c02c0740046032240c445005c15681c00860b00000800200c10b21040da1203552040780d40c00035403108186122 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 703768372 1250 703767122 703767149
    0x706020c100506040c020c101b080406080f0103021806030708070806150102010203070203031914090604110a051c051507210b0108060405071112090103110415050d0b03010f06 77
    0x1c43e410300b40149901c1403002c1d00100700d10b0840320204131007000020112400c10201d541c4043c15081c1c003ca288403054014080c4030b6070703581040002000c0700c00041801902102c440010401600d07000d00c00405800d4041a20810f526141c00207414122544d00c4809148200000880c0039280860035074020200906440444052003005a00340c0c04100c0d48139015810900008840003810300509560044281000492101c5007510703c1d1107a4050b503500070903a20442c1003104014500a40039040d240444211184d1032030100007817144805a0000071b48441020206820810200b2410384179010000b8440b140780f03001c0100508446008003507815544840c030780b41a03410620301c1514550075041e9900d007000c1da25401480050b20010300031008102c94103981c55540c1f03c051003000a0528507099950f600c1d540040018182d9014515256002404010422481a1100300880d100c400c3d03080c65515000013501003401003030000301154065081c0b4072400103402c8658080b40644a40800d40d54 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 703769622 1250 703768372 703768381
    0xd0614070e190e19020c03070b010303080906060616050102040f1202010906180303140c01060e0105040e01050f0a051b0316090803070515062803380c0706020c1005 72
    0x1034210b920721850141c41c0c0c10740c1c04181c481102200e0340801130a101005458104c44025591035a800284159114002c8100500805a00c10072260b0001460b100918440c10b040b0000f969520800d000c0203240b10003030100038200301302901501c0052501d1080f015006654490314103044585840890001d6151000802d0403402841e66112480808441390159400c640d400d40e20481000341c4504812014880803c4965007405004050012543c0f4800194542000d01c4299100640895450303410b2004112000704000989070b44a0b88403500404c064580d80681c000711682030345400c1e03600500108018100d1140c120340344000000d030761902d00c05030b9948210b5480380540d210051081c0c0107a00b9148441c1551052540c0180c0e000b4180780508800d4040002400a820071150000c11158010001d1014192800c4c0001c0070350412070a40700b080d032010a500320101c803c60443c24000101082500d0240401d980c051580060b0442d030701d850900e0025034940c9400b03001c60700e8904100000307 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 703770872 1250 703769622 703769659
    0xe031b0109320315070c080c0d02010c0905040e0c13090206070b040203100b090424020d0f2d050a1b020a050d051e0c010209040615090902070c050d0614070e 69
    0x284680b50118511400e50344035030b68101c6c0c00612900c2d003528422400e001c0c824000c4014014490f60740034a4000281002d014000540352550f103511207480b0314504140203000d19404540c500e2800c20882c0c40426048a2106140041601c014007942040b4049032050400100c0002580a03e00072403c84040d046080043e400ba110038140b0720b504221414049000a080c40c58200900c807030b44841d03514580c01030038171a004c0b60043c0c2d515644c619101c48041c5690f42140c41400030100c140100a00c0900704107190741d8072842d800c0c2c48804482da88000181d51781c02da9a0000303055002422a43c46003a008813402592131810100a07245801440c0412120b28051421130f074442034406180b5142c410031807401c044540085580080070354003000000c1441e652489458007600da1f03109100b01251000c5c0b4001d014101d01c0d0011030205104005501c04142d0b002c4018045600c11500c0718102c1c030032841d001001d000d10341000b62542203000d05012965401003000c54003a82e00ba02c50501c0ac400b0b1f040ca5 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 703772122 1250 703770872 703770883
    0xf0d050304030e0a180f0f0e03130e4006020d1a011e0306030830040507090209010e12010204171b2407030906030c0e031b01093203 58
    0x1020700c0c4148240c41440b00038030740e800c2440503c406800c00608807080a01b8001a42c007070003238502d899000001c1800c0d605004214503405055a001c42105034604904e000701c2d80c81c02c800d500742d105040c8a5001000404141765044906045018003032665058030b03100c4040d400c11401ca05507103081c03590301d50799603c01104000103000160745490b21480c0140d441103c1c07051040010041645511001c004a06100028641800d45a14155070b402007000301c001118610b4042000d034108980034400032610024250054800c12800140d0303810309400141c1c1c01c10000714040790456001c4500c640c1d09a0194050011038141076115032040d50b0350443c060321442e2906044580302c802804084d403e0402427171f4040b1400d21850000000d00100481109a400c1504124001000071609100566040c0a1859402c1180c10007200c01d10300600080c0d01c907a4403500d0007081031802d2000302103076803050107210028402102e005989035564000214203105604c4030b40460b00ea408500744050600007074 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 703773372 1250 703772122 703772129
    0x6090b031005040e0f0303011203020706110a3f02010605030a0812270607030c08010b0304141c03020c0607110d140d140711011e0e0f0d050304030e0a 66
    0x1820008074240020400180b401900400892040e00c51700c08002404000450117000c9400c42c603541d142c080d141c02031406009400c09400c100c240105880003140021f1400d2120794400d102c185142c140d40240f0340e2480100c40080e2882c1800581d22131300c1a24410034140d11030095000384403140d1160103042c0e456000c503800a1031202c041080d41c880880807a09280c01c201a13441c900d03940d4000214507117a407441100c001d20103800c00420300c00415010310510100c940d05060110301903150881303500103800b00030400f420501420703c2154500c0070034400007401541d141c0c00101c10502c1c443d00100250072a04001c2014402c900200780000d00950040c2c00d0341c400c8000414043c0f9082208a80a621403d4517107900074042c03190751100e00c0c0e1750050034000c0000c298402064a04044020001c0546031840d2105034500700b00365081c0400102200c40b04090b40c60040703040320a081c011407401c0c070041048011401403070800585564031100840c080ca0080c0d0307600340781074600820050200e031032b4071 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 703774622 1250 703773372 703773391
    0xb0703021c090204020c03120a060905040b0c0a0e060408070e010b090307060f0203070b16123b060106030b0a0f05060d1112070207080d0806030d0c052506090b03 71
    0x3041d030003aa0120380c202c4240e4501c0584003606082c110602c0c646035030080301d4402050500c80c0c0800c4182c030010322441c0014a000c11082c4402e0400d5121070903504005480126444000036207180b43c01c2c061208000380c0d20b0098121655503030343c0c54000d03407500d82c80d0040c4a01420355400005865002d581503d140020007005803040c1c601d0f01c081a90794854415142081d40000d001550201e05108811403065055010005502203184001000c42c184080e803d01413a00c1c0001c0c0101d6a06800c3d0150007184841d0712812801070500140d039400c0602130110103442c0314090010410551541000c3e12400090320300c58a01515580c480403d80510f01030640c0080b014400407000c4030454122003d9440c07070a56013807810016090141401004132003010143c1d21040b0b041001c520100300b10f8010101a29120310380307050450000740c55a20000c00c0401b040469003038401801014008401801d0b04110b600b4921815a200c41615072858402e100110b0004d620005600c080101120720500c0e90382c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 703775872 1250 703774622 703774657
    0xd181506051806012f01020405090112170306150310030b0708010e0a0506040605030102070302010b03071715090f03071110050721090b1201051c170a0203091c0b070302 74
    0x30001100d1201945162400702c80403805d904040e9254401c0302c1019254150000d659541881e06000e01e8000c180e1082e550001e203010a1030205010000c00c505421419003010b81d603444000000d62058007400185460b1003002003840412074048201d4011603100b0f0013034221964134030900b507458403c2481000c81c08004040010180ca1082d400380b68041401040000d0080d110400f2a08a8200882c1100542e40d51050b44541d40b40410040000302425418a25001c40712072a00792140c60340030000441c2481300010a4403843c05209580070b4806403801c9903210810f80c1001c940c1c41a1030120342d8080c0d80005195410f0381d2141c02103981294020a589100c02c0d078401003081c0b01e0906086c0f1108010030580c0220720075004100070800034600118401081d414041040030020310342d499000071030318a120f041300095643c031049a182c0000b2006030745411036600241e04502c00c2411040e8464581400103960080c0020244c1081e802035220791030540e82c040d01513089124610000038054611f = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 703776978 1106 703775872 703775881
    0x4150e071d031207060609180b0c0a091202010c0b2a09010f0f050c0a03080106020c040614150712111b0f04020d1815060518 55
    0x7070981d180000c20010300060b580310300d030b26203009981d030002c82c81405010030707503000c903005045d07404041c44062398002c03000b40c00419100d412200000d00b0030100d08800c2c0001c05881d686a101d03214181242e052044001918040380000ca040114440f1a4070005000d450b509000301001090118217561050000704208040f0752045d42c1d0701001d01c0f4080403070b079101c501c44140801609001300000d43d0a001107415210320050b020b1079201d8801d50404160f0b0004d1118100c4655600b90341c41c1e4060f0781c04210035551a44a4202c00e000340c1d04589544d4900704000c149a41d60445480c1c1c60001385070346400c4a8015030100701c0c00320b00f0102e00068101340501000a440c02083d9030b04c000c0d030030390b500016004c0801400c2c4500a0b6400300f80225215600d510000c0d030102e028034121000e560910784014a40315812000c1d9500c1d00380a00000d07a030516481e80241428280d1401c9159500c = true := by decide +kernel

theorem cover : BRFrame.Cov 703597122 703776978 := by
  have h0 := BRFrame.cov_init 703597122
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703597122 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703597122 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703597122 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703597122 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703597122 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703597122 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703597122 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703597122 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703597122 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703597122 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703597122 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703597122 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703597122 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703597122 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703597122 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703597122 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703597122 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703597122 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703597122 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703597122 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703597122 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703597122 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703597122 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703597122 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703597122 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703597122 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703597122 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703597122 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703597122 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703597122 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703597122 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703597122 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703597122 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703597122 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703597122 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703597122 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703597122 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703597122 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703597122 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703597122 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703597122 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703597122 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703597122 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703597122 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703597122 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703597122 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703597122 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703597122 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703597122 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703597122 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703597122 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703597122 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703597122 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703597122 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703597122 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703597122 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703597122 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703597122 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703597122 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703597122 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703597122 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703597122 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703597122 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703597122 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703597122 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703597122 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703597122 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703597122 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703597122 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703597122 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703597122 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703597122 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703597122 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703597122 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703597122 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703597122 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703597122 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703597122 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703597122 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703597122 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703597122 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703597122 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703597122 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703597122 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703597122 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703597122 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703597122 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703597122 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703597122 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703597122 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703597122 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703597122 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703597122 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703597122 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703597122 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703597122 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703597122 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703597122 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703597122 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703597122 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703597122 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703597122 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703597122 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703597122 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703597122 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703597122 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703597122 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703597122 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703597122 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703597122 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703597122 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703597122 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703597122 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703597122 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703597122 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703597122 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703597122 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703597122 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703597122 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703597122 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703597122 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703597122 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703597122 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703597122 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703597122 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703597122 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703597122 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703597122 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703597122 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703597122 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703597122 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703597122 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703597122 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703597122 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703597122 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703597122 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703597122 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703597122 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703597122 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703597122 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703597122 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703597122 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703597122 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703597122 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 703597122 ≤ n) (h2 : n < 703776978) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
