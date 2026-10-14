-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0786
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T22:47:00.829249+00:00
-- url     : https://prove2.me/submissions/ee1f6647-3bfc-4707-9da6-9ea0ad7ab975

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 141187050 ≤ n < 141366906 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 141188300 1250 141187050 141187069
    0x506090108180f070e01090c0522030b04050105100503121209030d11071716031d062a070323030d050f040201180e010b1b0a121205160f0c02 62
    0x101c04090524a1710b000220f401150f410b0700400c40d901d01d030859405c3c2c03498122040b111340c0e0700d10200748106000e4103140c10707803c2400303075201501d401181c60801013081410341c1b1451260f40350034031801d1019218020b04d076079401203540c88980020304001080305440300c0300d01c66901400003011203140c2080180800250362013002100419400400e10a08100b07020101c0c201ca510380d905060f0920502403880c000617084048082d083c802043c0b0300a0000107000768000c8404006030500790340780070111601200002c4100c081024001e003442d00c81a41d04041100e6046a40121200805506403611003110132401c2007030822511040100204a40e10b50041510403110611811058501350001602c18050080c411110b40003001041c0a0b981180751500e0640e00e91007000b40e00c030091548417440c105514041240e40384076019045041004403809489080955a129220101040300c0c030400c0e03490aa440c00c007001903c0c9108920704d803050007075400110203460480345021807a0045100b004 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 141189550 1250 141188300 141188323
    0x507170f071401051506030604091a070e010e0a0509090709090b1801020703080c090a0302090a09060e0303040f120306091401030c080d02100902150c0a060f0501050609010818 77
    0x800072441409002841c54034090101d4804000d0040f0301d02203810542d121100c0a1991080c0d6000c80070881c035480d02d9222a0025500c90740c80f103200360f4000d10540041c0c0c02202c0400004440207032450300c55205107589002c1c10b00184c4542c4034a42410208038011078002c0c814842d03440748500c0003c0410860041100c000d00031440c4141130700740741c6240d1201402c0c90014980a80c010007888e00026444949070354408106450b654a5078210000a0b584c94110b80c406540152910b00340242c910303a541c06560705c1489000100301d50740d01c20f510310f900c9020071180a00742c40c2140020f034021036004c03825101112000c1c3380020b142511042450125000308c40300408801181005004211008a400b4040c045d20307001049110000003000303503550318002c0d0544145441e00118000c54985480c24580e14a189102c5521188203120507a03076000400c3c0103640650605d5412000b041b600d10401d4141c55001d0101c52410303a1030001561010b1020b050012603050100c42024550402c1c0720828050 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 141190800 1250 141189550 141189577
    0x1806020a1407030206070e0f13021206190308160b0a0b0f0303040b0a050c0709050c070309051503010510110105070e1302030720010902030102030c0301081b10050717 73
    0x491218000410241402070301e0344070150200030b004040394000a900f41e0106d0146401130031001e0b20b00208008031107005200341c0024058030300f240b05c0003c5401030510040ba003014452607035510800c01405495016080e170000410032070901c0403500c3e031002010b6540c80e448100e4040701856880c0084844215100c003100303580c40301580802e182c207000c502c0021408800030b5003050708285132180079100c1d40600d94144000002d0310f0345004014001d01c0002c0a060001b0001c81c83c04a02d6000680c0c0000720403000600003010128003450011192503c04200541c82e80c2180e081009100004040c2c01032030050000c05500340c207005100740112031141e4066070320141c003030030144140034421848980c5d6400d0b041c01032041101d62580301401c5514000460951200e0080c1000c10a0041201c0a4003940550000080140c4069006d00640c1220000c2d0300f110314000c1d0051402042c8182c0102d0540d100c940d8980c45006180302c1c8000c0c100c41400380341100d948091984940129a10020140020 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 141192050 1250 141190800 141190807
    0x90f0605061c0b0105100c120201020a08010b16080d090506070f020c09060f0f060d02030c0405151603031a03031204020f030601030b0106230c0c040509070302180703180602 76
    0x281c140042d01000b4440b214501040d500219500c558105105001d154000c80058440c1c107600d07841681900100754112014808055103250024040d600100003d030102d03591100000390304003100c0c104c1e0506004901c4811103010a0f559402c001d9100000041d240c0da00c9038580c0c00070078801d0108030f004240b10781b00c040151001490190a01000c040514403400c8507001b04405c54849070b1a0004042007143c401d82c44d00400f60000302d050003200700c40501d240c0f0100402600c1c408540090064801c206c0d81480f486d032811400c01254072400b56541e4010040070456400680aa008010702c011802c46440b80c94036a0400310349550401d40d400b2419403400d02c240303c00d5041410761000c00500550240c5125815501c3c1d280d0300340d006100b03860422201d9000d1064940001d21003144401681013480d6560400e44080d5664a2818540714410703450070340403403600500080c20808603035026080d46d00d07040305040142c809900091680e810b058803590704200c00c07407000400b400f540380301c0d0000586 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 141193300 1250 141192050 141192061
    0x3100b0a031506050c120c010e0a110102070906180c0e0607030201020d0e07030b1602031e030f160c02040f020403050601240801051f03090206030108150901020702100c06090f0605 79
    0x2c1e42c4415034000e1061080412800211401c081510341c840c0c210340480c2d640d200c44a0000900400507056a500da901900491008002070300300e400b209020300742e00321050719840c1c2850b00115141d07803080441c050100c041c050700c100c100d81c00408007403035207050100c0042d900c0720108405034000c01040300180d50001da8150100c4592040c074a5109510008240160031561184009003000d0041e540166065072600b41c4103108104949200c10040011425094050410070b00b03900b040d1569030080d100000014000d10f025000a20007440e80c1d991046400810f400740401003044600300340415408101c08030124100700700b020300808509010701004080482c0e180c42d0030b02248030000802040400400245eaa0280c0c8201c5a8100141150360f0303084480d03040d402080a030800135088a408800020520008500b640c0c10408104a000081d60f41810343c500300d2043c0c0c40004c8d80291a034044c06c61491090f0001c0f8042c9119100000e51544140c903200f00907507000310221180d540380c104014 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 141194550 1250 141193300 141193331
    0x405060c03073011040f1a0406050f0706020406030e0f0a031d0a030507060903030f02030903060a02030606070c0e0a0c14070303051e040609020f090f01170109080c07030203060f07080c03100b0a03 86
    0xc01000940c4000c0c2e80e001c2015159030140c45203210360b27403c229020410607041d0141c1c800b21500c1a42c0250308640e55641e5141c0a00681807120980356240140035198820f002c020900682966150f03440200354001000d002107040c01701c9203040c0d08085400c1e80440012001c211401c050070a5440d0894080d10350715005082c40c0c40322201104640080c403140d200c90314002810360300304140100160716559000c010400034001c01c40c02602c40059801c000600c0d1211400c00b40c01646c090609101940b41007006492098001e1001d83d1800c10404c0b418001c030b0711030b0344070940003a0340b05d0b048201790310504145200ca48042da0f0648803544d40720084021440c3c803180f400b402e4102600e41115520741281e8041c40000b0511401c0e00d03407210300104540e00e460a60001c0e5280c0d50010201d0388075100c0c049960340da07040382e0004a009214007004204116822200c070f6100300300b26980e0008031f990b90355280740180c101034000011808025404104405107078040c000001950342d0001c0c0406801c0b900c403 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 141195800 1250 141194550 141194579
    0x10f09051204030309051324030213060b040e0711070b0909070305090a0314040b12090f0303040210230a030218010f0e1e04060e0405060c0307301104 66
    0x101032801d0108800c10000e5000344007002190300c1210040006417005070844090181d0b421002c680408090302c480d408800c5105e014103a900039540e072000800c0702408201103900901030514520340511042050100d54003403140d0000440c90043c1d0701c90510b41000e40703405110740081600703003004039004030a808c251041d41e602c0305052505101e40e0603e10b500c81c0d152000684098104041c0c104c9000d41041c0c10421100241103071000c45503141ccc070709205004000803d880700806402040d0720303200e200c2d100200707981c05190010300445c0c18140d0881c1c1620480041d042c014100c1c15681038014203038540f1030103801800d840351005070b80c43c1e488000c8d0750700100e18001454180811030014a4490341e21100110001d4001e0720103090303c0c64003d0b0015500c06031002140e501c6030034628007141080755110035030b00961041c011600c990311071031003040f9a40400ca070b400000400005401c6010512100004910712240e007140c1c0700411118104003e9881c0c00d1074009502a0000e02044001c20310b1119 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 141197050 1250 141195800 141195823
    0xb010914060a1203140d1d060c160c0f03210f0207121112070f0614160f051605120a0203064c0e1302061803010f0905 52
    0x2611180c5841000115000c1060080742e0310f6501d03592004007010f0003100c00d400c949410910b003a445906407110680582203c0c102c1c000002c254000c0084400d8000542502441d0541e60290400c80d0148000303ca90401510070307100d81082240025410003403540301009940155100f42c107280d01d00101c40c0154507a620410304120980a405031000d030302040c5581503c4000305003030a800c1c0c007400c081d0481300c0a66101d83c0d00600c0650501000701e0001800411200c1c00c100b00404103698420a4881c441d0301401480388a00800c8602d000910300f80a0302c8000740300c2c00a16110703107015110b042c40e1040904002120031940007040c8807902d00a01c0303002070401180003d003e106034980c042525200050020b8281204030a41000c46290501250721114568444c040c104156407203c0c40e01404007070601c1c2030354001101e0120341d0400c03207124944100d902c0b4415070000d00e09542407001d01e601602281c0065001003c0003141540e00b802003c442c1152004045100b40250a24900b000c218004 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 141198300 1250 141197050 141197081
    0x31b0a110f010c02040c050d11070b010f0b09041805100917360904060507080601051908042a08010c03092001020a0c0e070906021b0f06040e01030b0109 67
    0x30541507981e0301c4107604101a5061718041007820440301c00380e545000c0e1001072450b4504080208030f284940402921b000e034000c10300900d042e40e071a000002050024058410940c0c1d08100040003403c080c1c0050701d080b2605041c0002c683c00680f20281042508502041201d0f07c512441c42032003003001406000900c141d01039403809500d0911900300c0d403540c0801e400e001003101103442041101c1d144640d44100b019050b41528035052500100914045402e41d0202d1080008540f40c0d5106405480c0c522000207014440e540c0c28040a0722402d03c003c100722100313070940400c42000910110355000c04c944a00c1a66a03047c1801400381c20f6400008441e010189803080f208080348007074400c0111078002c108070103901002c2e0f00040f82890301c0c602e805000410301e2480050300e1204820400d104502e10399484000c0d54407003c00f240c41300e95840c144861400816400b6100d4580605510142400101014540b9a640300380c03a200d14806d90082c0c0e060751302c0200410180f0300a0142d200402e04045 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 141199550 1250 141198300 141198319
    0xa030f050601020c0d11030601060203030f0a060e13060608030d0603020307090207020f060309120307170708010e0c180a090501030c0608160c14160807060804080a0f02031b0a11 78
    0x1d44c1d03501800304180c4946003001c1d1403004d01084e0403050035003520103410382c2c1080d82c40303d4003cac2d07481d0300664000c0207a051040c00580916400c2c03090400b07032916003600f004941c803144c40309440540842c8042d40c0c20360b520031001a544d8001c01c02031800c0116241c0203d09585180105030a00754658000da0700e55004101040044e07032041c00e80c00c42c902d000c8404503100c2c0c480c51240741c542207850a141104a0000092007210b58015a45065258840655050030354030303000216804107080c400c41c2d81408034000850012030960010f0310011a10325001c44010440b034000a040f02e006034884a040356551700140107101800c18806c002d44801e0030f1200442c00d010301d400747c03a140400320070380800c01911040c0081108058500c0c10446201040364510b03080810581020401845014a140315699000030003e001e003404500c1f076500100b80078140036141406445d494548a10001140810070541540f9101c1c0010040603400c0140108848100ca00e07055008401c0e0303104092240e03840070f = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 141200800 1250 141199550 141199561
    0x11100c18080c0f041e020a050717070209040b1803040902030a050106140a0e130207050c0102060105030a02090a050402060705070e07140702060d1a060a110d080403080708090304030b09030a030f05 86
    0x1003c500e0318218141d50000703002d0580e2a00304a1034503940c44140b9161300000700094406d60140180407414060848142a80c0140384c54100742d10500400a4110700700d440000e0100c0c0800c2500c030360001607814000c01e40051144070604503030040c0c00244041e580801402400d400758820b00303001d842e07030f03041400c2c01484462801149005101e86101004002c000c00503141e11040421581f402c0b0390a010b5413902e40c28501191a2848a10078034018402c3c05c0c000605481e0000c2c0e039000598001d04a0381c2251078000f100c60180c48000c00582e0880000c0015400258080055a00819a01c9081611801e028074018400010054110901d490511a140c0542d590a0032150000044840003c041c0419422103058941d84401e00e80c0c4108041f801080c1307150064080948010881c0239682c042c0441981038030a08000e980c080c00103001c2200180200e400703000340f242c000d0603000071039043c1623490351520b203401000c44061225800215103261005d8060113000038120f00c0b280c081c460307031404 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 141202050 1250 141200800 141200809
    0x13120624030b0405030f0f0702030f03030709090209040b060313030201140708070302090d1205070b0a0501030803130f0204060609080607090324060b0f120a0903090611100c18080c 79
    0x480c0070141031800d005000c107042040400451700102d0b03068120940350b9400407021480c07600588070580c00381c010030134600d00c2c41c0008012248507540c0c41d103c5090a5080607c0507000b500141202504155168680030050341c810029620400c4052040c882c400228507000f420768518080b00f40c1d036a0342c0b20040c003210541041c1403d6101005240040c2c03142d480200007058822015030103450800d0740e100d40e052495000c401004034600401c40e511041d2940003809089860900c4043c0101500f80007050b021b419800c04008924021910500c1300c1c03c2d81e800050890351030713510000c040b45d55141e0402061200740f200c6a445101070070b03d440c5091658880560103694030401e0b01e08010042180e0036043e0140d0702140150044080e07464580c8452100107d465107c2d2098540172032026000a0420070140030710b2407466490380d61000494030303240c3d0a441103c0856103056582c09105142e00c1d24110a20458800c81200d82e665403400c0003103034054034001c0180c0c010a2140e002030350740d20220b886 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 141203300 1250 141202050 141202121
    0x1030201050313030201180516080703151e0219030b010c020306070e030a0b04121b081603050c06090709050604181b030506010905010603110309190503131206 70
    0x3d03010010107181501d00d422801819908074056a862810b0401e1040c003030002400c4128004100a8241c8584c80741901d5640300c070588002807050b0040b254003c00c1c00101e0300101c00a14120400c80700c10b0750704403c4070081e038024900000010103a5403a1040050b418054103950031000c2c285840f090740c450300400e4a44000510450034000510162001a103081114125103038011501007218203181c030304020314948a6855000080102d12035544400084403940300b907540c8101400d20342030b90300c1241640007441e000d0503400e00000340306d0701401801c02d101c410b00c10340c00f407405020114180750304e14040b642d025000f2805a80360103661709801c2c01e100c83c151003d5400c41c81030340c1300e60710b00100c64048480c80c2d04001c1c51402080c00004603001c9a4100714165103403602c007400403022014140403079003c00c41d9818140c1d8084498044190341c000d2040c0d01706d43c0120281d915084a201d41c1701041501680424400c4660011070340a128191280d04001701c2c6c107104c0c04020b0311021226000d10b11 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 141204550 1250 141203300 141203311
    0x6070b0f06120115050315090303070e0307031509020307230609060702040603050f061303050406050c0106080303150f12121602031b040e0105060307120f020406030b041703010302010503 82
    0x30010001c100180d0700c400442d4420741810000740414411030342c400059030b82c280318482c020303c07031501c4c1c0303400c4103000d0200340d84140c100400550030750361030450440ba40100103403081d415005441c400320116410800540c1030000d65040416a40328900c1810b00d094440d81c409092030f0040022281d80031100030041d40020006c4550648884140001441032710034441c0081d4460705d89100081000f4010451800e0594040103030b612079550300e150f0352407000220300d00400140c8204814000640030381c0c050540e181581d1b00004000d519648020324503402610203009211080003d203080d8544100e101814080540d0340c0f0b06880502c05100d13036544100040b0302d030b404c003021407180c551090400705002030700e8000303040700d100445500d810100300d043e0300f6000340164245540303480c5010050040501504002c3c00801c10b01d0f203010700c2443c0102c406601200d0707181c100005a40940d4480c015000170303501402000a040c1014544900341d000d01e00606207002ca414130040002d40c0c0c005d000e03a90b021 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 141205800 1250 141204550 141204571
    0x1109061c031418150903070302040e03130f17031206040b3609031306050d0906020f040f05090709030b04020a0e07020f16270204050a0909050c06070b 66
    0x440c2618054610702541c0546107019400455075000515075080d200301c10b0501075483d042e84441c4080124001d21034001411781542c0030000070001424564070002c503070800e12040c0c9007040c1e5400c0d8403000b0490740e0340c0b103145120210b001c180143c2485940900c06041040c004610705548074411104c40710b0700504091060b5560300f11008552582440700700701d2060b10310340001c441d580e414400280c52013002c0021140c0201e0000400d1038000000711620343c03c40000d8998074038030f020300c22030b200d81c019803841856580790034034a40001d01c1400540310100d4120051512039080c8010300c00d0031001035004a110b24404014010a6034004007058192504880705043c00d0b52203001058442403d0340c0901c03040b100260030400695808a0381c41e203245e90441c1030700c100da80049d05000402c030003801200c03002c2948460b40c040d442c280788a10720080c00200b002505080e074440004070001700c503502c84600e20380c4079880380c000c0000c180416224100204c5900c0d04040c120344908001110040c4000e241 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 141207050 1250 141205800 141205849
    0x6060c0c1503020918070f031a040b040b040603050601050f09160f050417061803180405190509100c09140d030c020604090905010b06091813021903110906 68
    0x84a00c41d404941d44c406014001660048201101d1812468210784003030000300c0c03601804035032038440c0c040c11031904803140040d0a040d44030301c2084005e1115460b81c9a20030355a0204540c0754660b030180800a50260002e00b07107075071400081c80a04003002d40410b01ca150388008000806821504461502c4c500785001c11049004400c150340510403a0031004410a00503160750440d031000808600c50404480e14012583c08003880654902840e017203480c0ca02c174007404404050420742d00265025001c40303440764408968178504000c40750305590703880540d00320118a00070080030740a0b010208000d464010021498107400f26041da014140c40380c4140030044c1100b061610924454100036002040030380d84030354608140700144001c2c44212801e500b00a80c4408526101d0107962681801405001c005103e0111a81c1c0304a0010040d2403014140e510704405625040400042400d1000c0480005400d40c2007211114030140c030400d01c2102a0030170400507031a1880041c0354541e9440b03404c2030 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 141208300 1250 141207050 141207089
    0x2060f04020303121e0411011e050405040f1503030c020315010f06050306061b06010f0603050c03040f02120f010b04180c180b040513020f010c08270607110406060c0c 73
    0x205c0d8800d4140000c00a004030511043c0400000b008403150002d03294119a09010210704810454044844000c981d06010030440743c04d080c7c200090451030200006980402100b210201340c1c81078005400080a41d0340942c21403d00300601c40b002d8640b52a1401c103580340000112103241c0d41d001d0312040002c0030002c11150f0700c03410184d403a0800c02c100407108030180900742564600d424403c140119110210001c1c80300e006c0c0c41000d008100e0500102e1540e582c0d502c50880080e0b0040041703811100881107211002d5060002424400c43c1c440003040000915040000341e032841c1e61401900305041d0401400603030780e0190ba07022140341e103400301c503444183c050340801420303030314403041d0428104400c1000340101e4000c080c030124801c031a001441c1520000440d22030507803510060001a0401c516005002c3d41c048444a0300d0340d0845451509108038080740042d004a1002c1b24a4005004000064078042c020035001e090301d844c0c804203544894481202c005903500c981d0080d07210741c080b18075 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 141209550 1250 141208300 141208321
    0xf080f04060b0427050601091116030903020d08030f01090204080a030f050c0106030b010e0108030a023007080c0601140d02010c0c0f0303080708011203050702011d13060602060f0402030312 83
    0x8012180c100c0304d0342140b112080a401c12183c2d142004c6926008900c0081400811482000c0100300782e905d1003802c04140c03000399001c90607a0394040c2c06005080900200581e40c100035096024030900d04240c40382003031104c440003c04180c1111200c42d0050209212600b4002030382e01c01181c0502d080c4110050255050312240b060003050b800550a108020080c41404070080c1d0407118000c2c9898402ea80c4c6a228544070b000b06a50312005801c019420002900c15140003c0800c4046551440c80345401020249503440120211407290740401c0c0301078034440c180180d5006128038650020b803015500006212540c0541c00203052000440c443c00901144a81c034001404807003100a131401e441c0e0401922009040b07c20f94001303401240040381c40c040b00c1d0313208903440358551074083c140b040d141e005445c0f01041b21416081c00c045015410119558042c07140c0c140444050009800c40c00c28000030b0909a004041d1103220700803000340001a1070000440e584e0200414442004e900c0706407010 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 141210800 1250 141209550 141209561
    0xc050d15030c06020c0102120a0f20030414120c0112020c01090203012c01060501020a020d1401060f0602070e0606030f0402010908030307030204050a1d0f09070504020d020a0f080f04060b04 83
    0xb40105400a50104182e60002004241e800090702180c6e100701d494220b00d40c072071040d9889400010f0f00a141c0c820003034000e40c010302010801484084096100d07061552031074026078001c0c0e0207a00b00300444412030070700e0f84014182c010305a01800c0d40018840019000c408a16210104a1790000f00c00c1c04604c401e6004101e8a50300400034020740da07000100508a0000c0c1071000d41ca41d0440b5004c00100c80c0506c00c0700c08641e0180c020300001c000036020000b25155050b0262200103240b803054090040030303c10a00a0481d0074100b17100070342018002841c0051a0300714455001d80b103800e00c070842da22a419a40e0040400c0e20703664040e42d4078401200c0036803e5138880784051102100344403889416801520607103005503515154584d42d00c0c407000d581948a110040c01580f00c01c08507591140317100f80b09d9800b207120421501d445560301e01013000c0381c0c020803641c11300c035a0104070b40364015484a03100e60031016514003841d840c20071501d1105c0c54000504010701480c3e0724407080305a611b544c0c101 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 141212050 1250 141210800 141210803
    0x5280203060405011a031f0203040f020d141605032d0706030204230603040605041b060302130603020307090902070c03020603010306020d05010e0c0405090907090e031c0c050d1503 79
    0x15142503042c1440c00d43e018201866151245c80048005c01043d03040002c4c0361030b0a01d9004000f000d051180070340060007544064401c0e0341a5a15034030320400750700c1d9504d4041e000c0c2d10a0020341d000314800404c180c145601d44000789444480040c04220710364000070b40000e80114800b0301d00d054448001c0002458650b00020400750107940c2c400500c0b47d405d0b0380135100302e80001102901140e4401e0000e000070103040b005641c030130f0040c008034000c507040754031007580940309890640b0411100d1607400a14a142e60000c400645c00180c86100580d030300003d10000e040c2410f080d400c41c01c02c150083c18500c0280201003180c0e5020407644c0c280510803815000a60700034120b90769a507143c2c00c2480182d07000d0941c1c400c46c1410540005401150407803058880c1f50041e04981c18107042c84c08000354202d010740442c007584074134a00407420440b54460000b4414440c2c00551740c4070a0318002503130542d0003074a0440701c14070b06641342080d290484202d58401c1980304002552100050000b031996605400 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 141213300 1250 141212050 141212053
    0x230a021b0714100807050d06180e1509070b07030203041203050406021501050109051005040b03090303071b1205032a0307030f06030f0816150614040905280203 70
    0x301100600c00200e40d01d81500c0c4120444081c200404007484441881107560400162001000521251048026040702c140e121008103030341d80e460041807082c000715038041007007030703982c08456220040820418650740340a0316414140d00c0c1030384295450b4155440344146c0800300040d0784041500c28401c540240c990f24502405000a504000344140c01c075006500152003600241c002d520396001c00d0504031181603591010b82400d01703041c0000407003003504030000c3c84070a000100d4205021009907100e0000103001315124038001100420710a1100ca107000341007010415140450000c0030b24543c0c2c41d9603414031a036a07446610000440c80380814601180b40d40c0c40720101700b0007484c0c0f402180207404e00c3d50144559504900c1660841d1654032004010209103180400004c41d16005816817a4115982c409655004d845803840c610500c00d15904c0c0f6a620380c1c052020756400208400b0f00a0207903810401d40c10303a07035903541e55140551808001c200c0c0b0b980c120f2000310b1002a01c8144a58046d0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 141214550 1250 141213300 141213337
    0x40209041b120209010602010519020901050d050f160914190803030f01080c030708030711010e09100f1d07031a030f0105100603090209010909170f03070f03230a02 72
    0x40e0b03102d85800c009030200d200d041c890000149081c414007075680a2129105c0b04011a0400f6400303500030744c4500c1441c2d050080504c00c00d012107045102c2e47c0d1240008100840c0d0070714105450700c001d9541c4c080746030180001030005100d104e140c19000c03a8415001c0c1e9401024154280e03035a03005d0f04141c1d2281055100c000b0410a482c0b24003001c5034101c0f030f031003002c454100e50b1080c00c1640f215524012084280d00c00d20005000c1104000f021807400c0d03060520104024800340441d401c4182110000c034400c0005108114400804200200a0429040c6040c01503102c0c0c4080b01d03018400b40410040540750080e80a0341c0405141c20408080e0050856080700c0311804600c1c040c0000311203028a0300b44172940081e4050190040d000007680c020142400c076030070804409c0051002210980c0e002050f001064400850340c4004e11040c21649215a101d01e480c4000070003068140400e10109418240542100c00780c01c035000c00460088c500914207640e401a041009001d0800c0d031103202014036 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 141215800 1250 141214550 141214559
    0x9021c03021e0619150503010510030308070203040f0e0a110a031401050d02030618030c10090209070c0209070f0e0901120b0a0e1e03160b01090e010e06040209041b 72
    0xe080301800a0b0050a480c0001401da100c1e868400c11a4802203124901d44410001211544400d0343e040509060050f00c075100d10100e821243d0480320f10b00301c002151014000d043c6c10101c0280c3c0b00b21284011458a800c12214009440080c46580c804080e003401003110400981c011140c1c2010300c0956584030f0b038804034000e0107860807030300700c1410015a000109031400c20020078003540b44c0203001003181c0d445440c442c1c0400d401c8425401260301051204501409062080040c00501c401c40498070900900401c40844806849e080030310000da112440141c551081d91750f84450907041034000240300e0101a117051185102080c0d01c000000c00118141405c040881030090080008003410764809a82c0300407118042d06101d00c50b4003130542d041e00491000c004200c805c5504c01940d0520813004c5160307010050490044035540b074400c0050001d1802c40c0f01e106100844240241301d00b0000032010364685002410282c0148a001d0000c0c042c0044411401000112141c0f01c031f104075510f = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 141217050 1250 141215800 141215803
    0xc25110409200a031703182d010e0d030c050f04030c090e0f0303040b06010905030a0303060905100f0b0306010513080318060a0206130516060518030a031209021c0302 73
    0xc0b02c2122036040c041c1d0a00c802e0b0070440401c800f42c0b584458400880400c0e0030070503001d60402007018920402c00401d014094a051040c41c0e111030046480006901e0141032031b040070134030044141c1039a0b140c15a204114100094074030503540c0541000100c032a01c0b03190440d0781e4810014241c010900005000040019400c1c542c0101c8104820030000161010f08540c0c440c2c0d070502500603a0303403044c40840c0210b410348901d9038210105040904219039180086030500c121150309501103542c0314000c1100d00214000c80f87e1044800c009100f21a042c0041c410490100d4080c00c042c1690100005145901960444005042100385000290740d103401c91a42e0360310a0f900800d08034003190300e450342c40c02c00000341c5407020704a8000e0300b026615192141d034202d040c2241a95107119800550051040104864020305400e50300c060396030700072141e6100300d8085034800e14000d07808049000086684035000c01a0a207030f1500108007400580001031001ca1040701000c60704065181d80d4040580 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 141218300 1250 141217050 141217073
    0xc090503010c210203240d0609141b150904020d09050a05240106031a040216030e0a080c01120204080102181306030201140a02010905011b080c25110409 67
    0x1050a01e106101c10030b031103c0400e0b400140c60f407a40e0207044916103c3c0c001c0c00c402c26031145500240802c081505251070705015500700100a035420340790b0320003101480c0c60900c17501444990703140c0e60200c2c40c4a5103001c02c64003840090101c112520200701c1c1c1d2490741d5284c040311124242000288020340e26030030181c0c2c40305503901c400c550074814460103c0c0401c01c01c2440308a6030004c9000902a60b10b007400942c01340840702c1d088900205454091011070b030f07a903c00390480f925205520f8045000c1d5240150040701e40048651140d0030603c81044400400201c1d03031100307076080c41c110070b026810400300d20103130041d90030a1016500101d4803100b520708050305000d14010403283d150300242088202000c1300c010340000f0340016803039018407080280a2004085814491000194000c1c1585405007142c007990340b0300301132140e40b540308410a44d0080c911b5822514414240c0d1802061100d90028424002054a012070f0b40e042202c05002400c1071142c0c6a0101500600c09000c0340d182c000103891 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 141219550 1250 141218300 141218327
    0xd121802130e15060f130b0d080315031912022a4617030703261501050403060c0903030f0306030f14120403030e040b04110901030c090503010c 63
    0x854442c060740e12500080e01680216000383c5140c41720014042404090142200360180c6a0303140d0444c160507448401102c00050b00030400151607080080c0e00884140f04801c0d00d41c8254032038500002c94441100090074100e41c030040d5021401c00071441a8140003545503440c05c1d020403003008625106120000d0401940100d4171103d100c4416075070135180c54120060461154080781800a503002c0e4000ba0641001301041901d451070f40e01d49000e0300ca00c401849240040d000401d141041642083e1523000c24078042c61600302c80ca680300c20590100030010855080b4a415176204a00f40c0d00400c201c8014503000403041c0140d0320748000190036400c00344000c07800102001c00c440013940c820b114600540780e01c072014001d104841d4882d0700b11200c824100c015079005254484200b489142c008000841c441c0e203a5558510032031040104481c1800310386400b4a041180f1020040003900403107078440401d003400541c000449404489a0403a034100580542c0f8141546440d544c125020fa81c1c0c48 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 141220800 1250 141219550 141219553
    0x702060105060a08180f1212010501140d050a09140109050d0503270111040f090515060d15050a1d0121080a03110304061d0d121802130e 60
    0x1660380c0e00c18030400c2d01c1500030f140c00041250010400c413401203a10500ca000500003101e41c13414809180390305290403100c4411007080b00041520784070000004240c010303c001d0924495100b02540c17000349600c102c00c142c0d20103030342d19400541146020381c40743c01c0d0741d0b0f00115800805083e20040d180200701c0c0400c25603c40c480c2402d0f007009113104104a921400841882c40000640d0b218486d030070008603031000340c1e10754990042c90602c5980e84040c000074484d48103030b114400c0c5400e0004003103440141001020031200310781c542041d103402045030720070a00564000b03200411080314101841c4a60402c1e0391083d0170b40000558440244011a1000c0305642c2000c00da0b61380340091525135070b204646d5900100045021000708080d200641100703815410003150260350a00c03000590340c4104c40c100d500503030364a40c0700d01400313918000c10f04294070f242c01004120300c2c00402401d40e0107003e450603c2e980c0c44038500c034141c0c2c0440c009030103203e03406070940312000410103108000d4899005c50a215 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 141222050 1250 141220800 141220813
    0x10308030919030219020604081507120c0804020f041407030e150405060103020d020a090e07140306090601180b0301091a0709030f0201030504031103030a0f050106020a020109120c0503030c060702 86
    0x5800c2c003030008400142c1c10b4000b030201d11294076010710700c3d4140d050140d0740040148000101c0120621108502c40e840140c2090145040318000c1c0082d82c1500c0d050b145c1c107203480c0100201e160001031311a005901110703401d8048005000140c0070344004e05400c0d2400070080c06110f0403039056041041c2026074002a86d03190b2070001703500300484d0802c0710090610340c0003000400c09030030301084006280f0b001825481340380351500e101800341e403044042800303181c0c0405010010717001001a2940711050071005072200d41410010155202c40602412629803461414400302c0380856203e03c0b8100300140c001c1c4803050013410560f01c00d404501ca025124012400083c00462103140640c0a5035132203035038901c00c080035400440c02010f000f40210184900a9500102948100043c61003a401c40d500410407160403c065002d9a406911090655225100000050780c1284154060796550240c140204400d4200200b04080c2c40d0302854041c080001c107204d4130440401d0340c1c1c3c840e85294084404 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 141223300 1250 141222050 141222073
    0xc03331506110604060e15070c1703010b09040b030f070906090b040e0a080304080904090807050d030615050c07031209080c010c020607060f1e0c1209030f05031e0103080309 76
    0x402c20010881862290000400240000c805034850103492007164200da070381c0340d00c0d540d2520442106030340e0300000c951000c0e00e400c01c004000140e08000c4006100c00750030b5500d8607002504030300401900e1403150340c86040e26102624104154000380030b034a0b0884074419607030821030300101031700d00810031018108008a885401d140c09142e41e0401d20030020012000c0d03a445000c01a000640101d490b66000c005908143d50381c2e000b0210801d00481c2065510740407864002d1401402280c3c200515050a008002107100c0348400c91100c05541000e80d076131045200c49908000b0707a40c000401203459006104242c5034081148801e9650781c00841742c03400c020300d0044d180c94003482c0d030082d4010810801c1c2000201140c120208000c0708810200d14501c0c0700c00505a02c144101d0000000e942c0e03030b840140701c954000190244c0f584500020000d003031143d01c006060b08480040c101c180840080861100d100390342111100c06503050038024196100d140000070744e0310564040b400d5102e00da070041c0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 141224550 1250 141223300 141223307
    0xc060f27030c130e01050f18010e0606010c02040207050f032706030126120903010c17010303050f1201060905281a22060f0207030c03331506 62
    0x900c401401802889030000d00b40410140700a00100c1c1c101d030588448800086181c240921400341c0705c110040c0450b03141c080001c090380b072984c00c1400026030521800502903c40031850380e40000d002c2c0b80c41003050f04a40041400b034400e2800090080c031520021034001c2d180070014024400d070b200203040d0005003e000f810000b003081448168004070400041000144030b024456520321018032180c1107140340a03089090601000304126040340005800b00c0c2403401b807007050694041824a480400d004218904408030140001402d0000000384003080c030600300b0640340c1801100d03000d00965030710380300001c00910840c82070718091680c0c20f140c0400c09108400322240241c501c2d90100b1001d00d4080791038410601500e946103451010041011500780e001c802c404820b521081150f0354514100000b40700c1c0004a0003103045404c024000d00c0010030b1002d5200c100c0381c00066602c0c00b1059082e0710650301040c510440d0403042035240c02040c8103000d81010743c1000d031400584481c01d5030340c001030707 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 141225800 1250 141224550 141224617
    0x60d0c030b070e150a05031902070501060306060f0e01090203040804030f08090901140d0f060f1a030609070e0a0b04060b04060c06060e0105010203040915031e0519080a030b030c060f 80
    0x20b04d842c602440f0311100c43d40b20f0000386502014040400500007a018040002c9034442c020640d06039441e0441031080c0811030040f0b00040600c95500e0200703d103001e2500c601010180100e00c5290740000105c1c0600c00141c086e20007541c0c120104403420303c641e05c0e00703e03020740c084071000340501c145000000e90403200c0319010400000c05041c0d0a011815984d5041c03d1841210702180c42a07901c00059113135290f1b621501c140400c9101c000d682a8070b401e030805140c0032000303010f802c140d03014030001d0251020001909800034001d1401103282c0d0000c00010f4040c09044c1c1141d024548003181c001622036020003544203407070150b10104000c07034407100080401e0400340941e0780035030300410003001050702d15441101a5040ca54095090a46030303500e10f003101030f00c1c1800303015003000c03105c82000f446818070179940c2ca100c20745a07400440019503251a00d070b00655880d14181a91544408110349050100305000c00d0001c203019950a040ca020440b1170700104450b0104036044000044000c0314410507 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 141227050 1250 141225800 141225829
    0x6080a1506050304120e0f010e1305090f010e0c031513060f020a1e08011a0c01020708040f211e05010c020f1203101707030c030501020a081f0509060d0c030b070e 71
    0x72543c0d1f00c984400540340c98080c40c03030940d009840c203804d030780f08000d0500c1000d0045c420440a0154101c081c900b00782501c1600c5101e0005402045084040c2d90740003940f2468550300000491700c07541c40100754005068003031405030145042544080c0306240a5004010030040b0740c651050110314081440400140d011004012030328031001489001019210010130781c2483c038015240c258080e11540c00da0300b044104603803010010405100d0b661281a150b0080d0441c08200210341410001c4101110ba4500e0060a0384000440c1c45080328249814440020741106c028004060200d100950761005a4096181030081c810584d003105420011203024030807210030b0a504d42c0c11303c079008404e411107141306100e45c80740502c004005078024601400441c0200d0005803a8403000001604000d80144400c000030098243d5110404082c0042e4081d40c00c26940d040c1d40c0d80d610300108240740103920001d44954030840d0008108030b041b1070114412302c49a91105000b4419070305006945140002 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 141228300 1250 141227050 141227059
    0x50702060f0f061e06091f08091204050f0a050319061b12050a0632010302030103020d0f02150d0605040e030c07060c08070209040506070305090f0706080a1506050304120e 75
    0x4135403a540002040d4a558202c0100314918203015031000400e0220460705c01c6161480014401e540039070070802d0180e000c94110040c0c140300440001c841c0f4640300d54010284642c55030b1401000035150003a442000c1c01000c0d0840e152015600190414401d217940100c0b089402d08050400b101c00040b0710020402c2c090b10342124840302044050054400200050724071540c41b100002d001c003028140980381d2005551742840000060b03448500300c4880382400c1d040c0b50041004000603115082024011904116104207802c40c0d4400622035040c4002c20441c410008510901800702d141e004400f2200c0485040002c04550b10301c0e1a202c1c0550014401c00ea04042d00411119020b0b02c05010014403a00f0050b1034241c8a9000402041c01078405035401e074031100810980b5501440b40a400c50480e4006044e501c0240107103998030500c40c0140d10810041e00c0201d928448207802012801e441142181800303529550020b0650700300700c506440346421154400b0905005841001c074942c4083c0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 141229550 1250 141228300 141228319
    0x100f12020603060d0804030f110f06040302040f060b0f180415051207030813090509060f0106110a0f030c0b0a02130909020117090609150f0604090c0801050702060f0f06 74
    0x8080054070740000f001c1a41048210813407600045050000344081c0d0310910302c41c180c001c07041c104400050100034040b801180c6280000005548005c25141120703412580840e001c015548400050107141d484081260301c00300d8881313103903030182e00030703140c85a001e11807005007941d00e0042000f82e9501c1c48552640440b00e44040c005414041c0700782d00301c0310031101143c080f140d44c1d94aa84030380c0d221201c07100280c2a105030070b00a05519026080d0001001e4004000a040c002102d804526041c41074034140a442154405083ea0138895405482d42240320313502c004850b030030041c12128140d0400c0b646060100001403c001c8548281c6040301d5000740ad056040b41481c07105001000229810303810300040302410442c2c600b1255407039100d00c2c50350703002c1d14860030310b940b00030310f00b04401410301140303003581040014104848011981c00030b130889002c100754009040403d8a1030345034100304115401c1400700120381e500000e0050103448108108200d6554108203841c1841050360000d60200c00e51 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 141230800 1250 141229550 141229553
    0x1506060910091508060405070203071106030703140f0a05010f06021b0d0204020705010b01110d0503130f05070b03010807060903120e01050d1401030212010c0c30020105100f12 77
    0x40c04084400506050001c50f8860311012420102007400c540050701c10801c0100d1070415004407138002d00180015400c02826075111142d484071100c0040c004c19000c400100c17001e210390000c103103030414041640c1c0d06051500c00498880022038010340c04904000002a409001071031610850707510341e02900440d030074254031800b40808110096400400300e022400569984c0c4001c1c03900604c903900000e0300060150014181100e1540e210103d50480902c0d00c1425070024104c80e8802140c6d05001010a503a00d00f0207120a9444800360580c40742c01808580d14070000c2c000d505071000700b0110b1329415030300c1004a4a410341808014103c3c00b8512102041c54080c6103903004060050414904040c070414145046074002e08088000403e08030041007582440742c82404414800300c000c6c0251220140302030507400c07584100404010042085c91b00c8010406031440c40440700d6106062076030818180240606000c5e640c021540c02c80400000c2c030000ca900b0201c00715030031008a45000083d5 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 141232050 1250 141230800 141230809
    0x50f03030d020f1201060c020414061503060a090905070f12080d0b040608030a0c1a0603030412050102070605041a0a0501081c140403030f080c0f0f09012f15060609 72
    0x2090f5403451540c0203116502140d40c001e030040f4040c2c412940c074100c183d44140108400d5400c035805244401035043e0034400180c03114440d501d1103205100c102030780ca4031800c010900e1010944e0040002a20300304070f0310108040417517850300312210000c860340a117480d41d0312104811150303c00200500c40801000741d00761b036207400152105000900000c0ca840c2e03290101400c40d4481242140007403e111212410000302900383c8001c09480040c951562904102003030303582c8100c4c001c0f4200c02449a00040c1000001d4044070b1805900c11400c0c421801e0170f290001c0040e03036080c00040d00c500c4120010b1285001c40c0300300c0d0b040740e00c03100041000464602c02d03481143c4407080110108103040100030342103a0180020002144640d0b100410341c544494001c00441018100e1002030f40308101c040f00300140c440c140c0700380c4040c10550543c0c603280d07003005803080600b54161007640d00004c480c01040c2d000c00d03010100204060015904541c000343c10400301400c00301e4040707610035001c0c00300d840d080c00d1 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 141233300 1250 141232050 141232057
    0x215010608040b090312040b090c0d03050a020706030b0d241404120206060d030f090b1b010516020709020904180b0a0c0509030a080306010c05030309011b050c10110d020f070c050f03030d02 83
    0x1645001d41d00703460344810208200d84034103002074000c58dc0c0020825070581d410000c84d802081180b804011980c2500e000417100024a00060303c42420841c84900c03860180300e80030500710340340c28100442003a800099040681c00c88041d01c0350142211020141800454000d00c144801085100030070495942a103000915480d10410406042d00125403030241708024031100c94086204140350301c0104c000760070341720010100001080c80805c4444030a4000800c20b040d145003c0b4056203451107036010800a050300a81111a004500c2c02e130300a0041420041307000300f0446100740011240c200f03055030144030702c103c0c45030554020340c070a10100704014042c60300000c0514141c0a0003815841e00c628640040c0d40907201c6966070303607503d8125005100f082c2007540c1a401c1030740c02c00c540d40e50015114034100400b4428940c6424180003110600e004980d00d040c1342a4003192194420151101035803c049000c07100f0640128002c034417841d10b40307441c0a41c01c0300100110b14000c0f00c0c090302d002940 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 141234550 1250 141233300 141233311
    0xc0f0617070504050303160209010b070812130218070e010e030309040209040e010203040506150a03030f0e010e040c020d0e090c070f1509030804030201141501030207030215010608040b090312040b 86
    0x180408184e070355081c030040c00a10741010801601003110300411034010300c180d12175a01008100809030014058000769004051901d10030f180b030751358000c130000b4051a0f400c4006c0d4401500104006195510403159008002d2030f07a03002c6003812440300540e140a00c3e0f610f6150f0543c8288158840d51600b81c00a140b9120007400c003048400f1007004d49800c0e40c00940d022201e03500710348100100c01c40040507400080004458003540c841c5547c40180c1002e08084c0d4020410a10000c441040d9004450213440300342d0240080044004084000f9100d80b102c4917000000703440d04080200350320300100554003030010f60300854901102035842010810b08003504445180151204541040e00e40c070503004018000d45070301c5010f01c0c05241c0203003152121700524000070011800c3c41108000c2904400703000b0400c0c00c0050341c420709070806034580020b8600b20407030005808004140340340e02c40103d034020307031142d010900e698071007200190300c078069401d1240b10a10f4110005020844095403e034210 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 141235800 1250 141234550 141234557
    0x90d020f041104030512030708071b0b01180e030c0c01031e2c06070206040212010608031308120f03060405060f030303090a02010909110304121b030306030c0f061707 73
    0xc4802000c101a650711641d100d20000d00883e04005000c0c00f8045000300c9607013211500e1540c030b8505005054401d01401c003d040150212981c5a2440c1c40d44034030502c1904612a0182d56030344014109091005603460170340d80c0c2c20701c1900750308048008191162042c600c0083c200252000d4011401080c0c400034120300900483c000102e040c0203481543d000801244a540401034230840105038040f548400c00101d920050811965507030100700c460b089a41140d19280e0048540c0125015045c1508030041c0e0307010005040c00c803034030840411002c03641d030f06007642c074815004a29109a03002c0c8140007000711804000140e080e103410b900583d0721000c000d04417226820f091002c01c0c84c542040300c2a01042d8010790020066603041aa1140240100c400a000003004201c58078007500001d04028940d0902c0540044ea05004500c00850255160001d8100489078100100903010501c404d41c0d0b48084a1800b20301001103005100503070750192200440b400b00717401c00400d00b010050802040 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 141237050 1250 141235800 141235819
    0x7021212040809060415050304030e010c021e031f0501080c1f0f14040e061f0e1306050d03051c0209011e0201091b0807080c01020c060a0207050d03051809010605090d02 74
    0x4203098040060046d0299440c0f42d01d078070f402d00e4043d00c5100c4202c58141800070314040100165194000ca001c0c000380200346519038042000480e281c0394410007110042d84c64003550361751440581c0c3c0301c0b1b4100c4d25a64212040781c44c0b004280642e442042405502651004032010f8185e8011044440c481d1058070b841c2c0c0c966003407198400403903045900081054030003070042c8083e80c42c2007504c80911044150240c2c1d2003a59a840c05420a406800424004c446218940000d022581e009800802001c0c200044e0701465142c010001c2d408404148070003c0394003d4030740710150610960304c0441e010b13103808000d0354849001103121084510300c00704540d01c0f512640f00080036112491811a50b650340743c1141410216900c2c2015003035080400c2e15441f80d00500501c1e80d00207050300e070a0000303807a4160760381a1600e080b8140030050b00950340049642c20048101a0f110004004102c4283d030704040304d0b1312070010006020030a02c40c1303030005402071003064043d241c44808510138a1000780011403 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 141238300 1250 141237050 141237059
    0x31e060204140108100506030a09020109150207060807020a03020712021314160201021e0717181f0c06020c0f0a0c050306060a0608040b070903020d0506070212120408090604 76
    0x5a900c1900800b07110006000a2091541c018182a8016520202c12030004e814040401d0f85808000d01d683c0347c19881d48844415039002d10001d40142c1241543c0d44031004480a010790303200300310701c80d00001408140004900d541b0204410b00e941d03174076601420495240c602407240088403420103903401a80b10750023104150a41c460941004404a030070400d0b40340108402d110501d11004403021342e40100842110b00040054540d13449030712152403500c2e00ea0301d06002241c0d0950200a4040c0c0d500064818083c03250940401760300e41c8100c07134032103019403802003008251110b14900008501e00c501340743c00050b440d801a210450742d03c3d084441e140001540580381480082050b905a441240d041c41142004d010042c0c0c46102941d8807007180d46130140040014000420107450b800c00c2c8070100710443c2c85010714070015500103000c415184002d0801d2a110101139440c1d00151068944c0602c02c0b400d8002900e40c00c0c003200d01101956521911082d841d9800b402d103c1d548180308100205 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 141239550 1250 141238300 141238313
    0x61107030201090309150e0d03030b101206050f01051903020c0717060a0e0a03140403020405010b0d0f05061309050a0803010b03010306050a290a17280c031e 69
    0x48040d00a034000b041e00501c2c2d05000c4c0c00d81e6103a030450410164000743c0c80c0282070708015040400503055490319855006400e0442c01002c1840116501004599a200c040c5074407050b000011216400e08220081c0d58038100001103046031401030104205200c2e02080c8190542c000d50f000980c0d040c0945402d20100e000ca0411410340c0040c14030280300b0043d1440e6035401c0102580c000d900e030500b080b103039000c0c6002c0c0ea0344403624040103040041e24074205295217080c4080c1c40095a000c0d000b405103586507900075885410490f03c0365183c44c81c200780c0b1020314449000341809003001900b05c3c2200400207840034040e095010050360f0f20301c503510900c0006071109004600034030702c015040f5241d5040d4685501600c201400d01a1032a0401e146040c000c29141003104519904c01c01070319580d03c0c5000030501400040d881007008102e50141001416008912042c801c40070b600688210809002c8684402c0e02c050b00c0a44400304c101d005100241480c0c0044051003100c20b40c890740054140d0352103 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 141240800 1250 141239550 141239557
    0x150903030c14010612140a0f1b0918060e06040b1308070803070e0307080c090105012f0708070812090d02121b040b090f041b0f0f0509010f0f120611 65
    0x80c20b0340794104001380305004074006c005d00700390300d46005002c0081040d142c4481c20742c140100503042107044203984481d00a0030b01c0c090010404c1c2c0c03806204481c0120b005044002c4211410b41e902c0f0304120030080340510115401d8419a400500715110351a58640c440c81c102c0740910864081c5000c000c10404500040c0c003844c0f052a07240e03960741200707003c50140340c00e00303010361701900c003d0b8007111400d01f040cbd0b5000c5605054070f1080c42d051203102000c5804080411059444054480d0621000b4480c20000314448094500e030f0000c641c0203c3c3d030303030b010555201c1480500076001c4901340042c0103185018001a100540000c04d1036950a14111a207070030807640c0e05070070311710a04441c15400c2c01d09144c003401791070140c03c6403010900d01e8112042252a00020402003400c0c056504410b082c1303000c6441400503104c0e1065401c00b054171021a48118800307402940c0c41501c000000007442880058442c0540d01c3c40e00f001404a4546180d40306600070320301003254941e840d405041580071515019 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 141242050 1250 141240800 141240809
    0x318050115081b19050d0f05160608011202010e030d0309020418030c03030e1212040510020a1409130e010209040509062412011d0106150903030c140106 67
    0x496821615103007040c000140d1041c070030b07600061140300c00d0b4001d941c82500070740420303920201d00200d0f07200c1c04480c074403068108650003840220504180300c500760200c0c04052182d8100c4480769042c1061b04802c03041482054001100100188070046040800d105002e1040c10401d50510100d40041e0400d41c146c05584002613503001d0401c2586010b000d510711002e011010160b040c9102d890082c801084240c0c00b03410302d0f4888015198803d001c00807160351092850940d52140100300d0004890101902e0503030b010b103d80e901d1510050f03ca4400c9920030040d035240d05150b04940009600c568104102266000381e108a1510500095000e108440006a00010fa82d150362008000440b480179014000380d6003c00204140c0d8030a01c8140e154201d00c0c0b100c0f040001c0d00b0100010121016010421215424030003401e003040313a00003013001071031a103800034425907440e00e0302401b10b4000540002c00184865034104046402244140040b6004200f420383d64030085803100d0035a061b0340d00 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 141243300 1250 141242050 141242053
    0x14160e0301021308100c08060609010c0f210801050405010e1603060510030204060216141905100816021218010c0c0326070f0809010c060509010603030f030207030207090507031805 79
    0x217002103140040c460129401403a00f000c070b030365082c01e001041c480c0c01a80e070b07628180f1100540305005c1c0700c0303409880e511040c3d018041000c100d030700200b085c1c20604100c44e0325000c11001400481c0310314113030040038165420611090390941c0e44550b01d01c00d80c0c81858100040c540e8480300401c1a0715007030140010f66011b40c601507580c03440c00c00028500706021212a00d207050681040c00100038a814200d0380500882d101e42200c1c0c40d1001c56950713500158000f6a210340000311b40d510031900031020070f02c07a240d0210301208180540d00140d0f00c82002c0e40d19100600400c12003c40c0301e00006c9001c0d01110740600d09200f803010203680d40030b01200715800030b5400074200110381c00d0b41ca0302c0309030030403550804002ca43d09019076690b46805040014100a000981c0071401c494243d03c03402d084542550003800904c114100100114000c1140b404103800284044002c0004c59000b0700803a000254103500404166280400c0c0c44014900905004100f503203035500c2c800c1c8034003101441006a80100b0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 141244550 1250 141243300 141243313
    0x303111e0406080c03070f0f030b040f0608150c03061e030a0b0f0c040317070602070b0a090c090c050d0e030d0e06090c0f090c09060714010b030114160e0301021308 72
    0xb6000d450060001c200d1200c2e15801c00821280c2c0758003c0281e45044118140a03180012040d070a601818405040a030000c0c507260045c240c000d01504100111001f007415269180c0c07200d4548602070100702c031214020070041000c2021400d0038000321802d10300d041c00520480c044a0006400c1080c4140d099038800022030510200400880e115078008503039000e2546040d2456440108a1202c8880610708000c04075030441030100c15011140d190b07602c0000300b520742c54618141c40c001c047c01e040603140c524a400c0f000c03801c02d007540b00308515050709031560350404e082e0810340c80c050f22500d8030110107400305000912000049014100e00d1140714006480245001f188640c50045a03041e03d0b4410030b56801030700060749514a0450b0071406070805070740e0700c03450700300811244e1140620040200350301c010412800342040d40215020320f012002403180e40740ca40401882010300380d41d090464214024842c003c54000d1842c26111180a4005400c08031004000741e031410701030f0300c0880e16401c0b40 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 141245800 1250 141244550 141244559
    0xc031b0314061006030b0d0f060b030a03050403060b0a0308040302120703060507050912070e040b0919060e0606090603060105040207021c1202070e0106020709051806070306062a0303111e04 83
    0x40f0b400034003890300d0100809052403000501c91030162a0203014202030904000034081a6080206254005411141c2d00219407400502c40e6010b407106581144c642400460146001264002140d07007184a1608080c115000c121b40c0c01c1c1400350140d550b20445600200054041c094140702e120709444140d05d941700c0d0018012059441070800c000d541010768244401d8442902607500560002141c90b01a5100302d01245010394441c082e8890003ea00031100401c886600010714980d0f540c000c0e2611921040300303004c2ca4080c1907e105525412400c01882a81071a03409024500c0c0000d000030a0407050000040341e00c03000c43c0058410f0b01662991480c1140c0412001004103502003484410b9850118025125040c0c2d005900c41da43c1c640c000320b070b1003001c0d00c0036480b540c00520003a500c050401e01d0025005160078411000811031406c4128480c100101c40c0c80c201242010402142d410180e03404c4008000f1401550403000c0f040c0300802c1955030044444603030b100702800c09540c46040 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 141247050 1250 141245800 141245821
    0x20f0a080913050408220807180f05061e010c0b09031201080d090e150907110d0203040803090907030608030703020f0114041a0603030f12011406070c031b031406 71
    0x1d0b4001030301e8641002c040c0000259035004840e40d13500c9601b6210b510b03902401c801a9101402e62012a403449002070120700310f500c07401d007541c0500c282c04040020101c400b02440c140c0310202c1d0031680c840d07151513082e201000490301000009805140049400c1c07629582c00d0030141c000c0e51590040d074000314101140ca40d40000315400340c10204010080c00060201c02006581d03203010f24090f020700d01780070905202090300740b10350800c001404201149000c82c4000c002010020700402d680c414605100702d042d00100823a07041d54110b0014628040301c900034007543c400098641000c160f6a00d0000035410000c2c0094130f041c512a81c05803000e154560f90075820744114103090f02c8200340342c200340000141010184c0407000505500422250740d030b40002800c43c05982c4202e000308170002403510480c1d501c0e955681c1a216410140c0010040040034031429016510004100c510420303414000704041d15030300b00d485024002c1c401c03450b68880e910340c48540c1400c1c1051180b030380b15400303101000300d2 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 141248300 1250 141247050 141247069
    0x40201050d110903190c0609030f0602070618050102030a0b0a060f14040302030703080304050d03020f190216060201060608090706090501110a0f06060311030109030f0e0117010608040308010e06090103080a020f0a0809 95
    0x7e041c07820f2141d050840d00c81c0201f40c41c0b012802000c4070303400200c007000c1180301c0d0407144101400e0031142d48280f280e41842c034040d6000700c88048000c0c2c50244181c038075180034a915001c0d20015500c11a45016018044c0c4840c80454818480035a040c48004010723a000c1003502d020714800d0080a07103030301306803030014a0900c1c052030b82802c4c580144a10549500342e001a900c810300708004640b0801c110250503410059001c1440d12461100b00e00410a6074054000c50100c80280d9165416035407526140350702d40405e8003c02c07000503402c51081049602c1080120300c106a644180d41903400315036201c4180400d4900d08882c042e89840080042c0000840c0400c0400002d5009003c1c4141e1681e00030701c5000d0040494040c040e40d486650050391040c1c10384c1d4490000484d0315500ca58440601170070203a000c07a411400514500700106510b9160399071140214800390441e0100c1e400c1d561070300380542003c5000011407199840b0016800320400540011038000c8445513035544601040c00352104 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 141249550 1250 141248300 141248309
    0xa0503071a1504110d060e01080c0103020f03150102030f0706060611240a020c0102030a06080c100f050702062503090801090309050f0a0e010b09030601050405040201050d110903190c 80
    0x11104010041551034007103503071010302c108680020b480010300b1545842c0d03010340780f0b4901d08185002e1000c651421440d80c428140d41c1e40300225910b46d0f40b01d000440592141507400c6001d400b0034004106c2c0301141440f00e290740f40050042d07070305002c1447c1140220790800030080d10507d480b100d04000c00d0b80c001c20410b140d1010000a000640d0340b8003205280300b44181d03007031200310400400080c036000181e8151042440204000d40d6203061989021018204a003d154603a02901c01c040209180081c0c050000401c1500e5580020b4000750042d01c26402051050342c02c090100702504120b8072649807000d210787c800011303104000e15410000c103048903e80110300c241c0e15107920100840d810100050480d00100c43c282d000901c0d007404a0741d20300c05980624100a0608000b045034000d403c003800c4001d034143c08503801680c1e00c2c4204015580141c502a01040c0d04004240c480541500680000c143c0110814500310200c40403900e09a40f040b86c0e0312103031000d4814482000000d03100748000b403 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 141250800 1250 141249550 141249593
    0xb060c0d0c0b061c120909150302030d0504030515061909140f071709010e06012c060f06090d0c060207230303030c16060c0903050d2309010903050a050307 68
    0x40700030031020840d8001120000c0c00714005d032600300c40c02602c00c8a4200252804001c14400c2d203c0c03840d440051a482400202e00c40c0c0500c92001040500c80c0702507404594000000302480300348120107410821020304855001040b83c0c0d030a000440007220302d10000c01c20440002855211f10100c5002c2c0032019026100c404000d40500600710b50040f128241e20340c0030a281d9200d5225038808034010219004185074600610000150405246481d1900c46164000b500103080a801c144080d100040b240c2540c0a046413240302980d0512101512100d0030203000d0b4200c884058841c210b40d800710b603000d44010b80c003007007081c0030084000303054083c0a4141012040000038080000c0c0e103a0100800d000c0700d440307021444040400b070100342c080010b80c1011040100e080d000d80b00610719005400141d5882c0720f800f040c2c1124600c9080142842400e03007045440d080c42032054808680d2118480f1030400c20b5110005c070203e007050091080b044d01c20341c02181d413049180b0302010f100c0708104103180e01 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 141252050 1250 141250800 141250819
    0x90b0405010e0109030207061110050702030909090a02090c0d02090414070e040614060304050307080a020109060e2d0307020411030601030b19030201080408040e0a0606180f05040b060c0d0c0b06 85
    0x1b600001c50307006440450614102c005900c200c00c07450043c0520080c0c1d210340c10101801000b503004030080c8011101612690810340d1510038840d03031007038803000c000d4100142e0783c0064480b00310350b400b401d2200600701001d85030509600029082c3e070101c4203420f51400300c5130103020905401103503e40440b002070700d0074040c3c82c1c0740c0b0a112600c3d20542088078021440000000c080200034401c0302c210503404110341344c507002e003168000e000305410300d0200d801e5803420110006045001541c000c421a42841850141485a54031400071098824a640314170041c0040c00040e625402242d29840820381d2540e00c91401100040c2a980c06032040707030182c2d0603445400030402000420006494080c00c040445440d9450414564480c917070284200260b0341e02444412a81e5400140840e0340c00d588120401911540784103488006100c0c0c2c0c296403d102104100074180350308111000240140b2850600011114280c1000709451110f400102000c0c08074007009401840340360013110a9038030600c0c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 141253300 1250 141252050 141252053
    0x501020c060712060308160f1401060e0601050c0c040b01032003040b01050a0e040303051015050904110301051e030102120c0d0509011103040f02042406110309030304030b090a06090b0405010e0109 86
    0x907485180f00c02d204001c000d21a540500c840c120041e078260307a00c0012749a8196585885c03600801081c09800d20860350350022407d035620a03000c0d91071b546001c101a01007a0305400801c0010090402210b040c15114405071000381043d041e080c08140c0c007856496542e142c1440c003042244416004507104402e2241c0510031111504222540a949800c0000d603a44520f550a845039209901c44400200851903141e0041e034000c0c0602041c0d0015182401020141255012540424003c468001260038001214403000c00d201865204010300014540f07143c40500700907080e0110b4a031a080030b00020010394440d0107208040e44090100700030004890381d144010111300c80a04082c00010f51080030030255510307079029070307001601c4629509060f1441c81c0e10f01c10310382c601d2180308081014800b981081c0e40010088886600d4000d0245180030b0450303503240c041540190000301c1c00c0c880c140442000900c64414020050701600340300300c0c10301e4a850110309403002c0c82c108840903414a0203650 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 141254550 1250 141253300 141253313
    0x2703080702090a1413050d08060135070207051009050105090f0f0d030f02011a03030304020d0302120403050309040c170a0b0d200406051023070501020c0607120603 72
    0x2500298100c401000907141d41c40402e02a00c030050544008071000400d01117105082c5210307402c403d100303030151050306e0100302d8140d907640d40444085010031100c2541c80302c440b100f280b0010403080b1468000000051707000c0c1c0301c10002412a2001c01582c8841d00900c0940f800d110301e100e15042910f000b891250a040009240d1300403804200d00a030b0700c84828a0481c0c1d1080340004000c00c010b8400136909601c0d013001803e02014000201c0036501e0700307160468241c0f00780704000c01040007400452558483c0e909004004030000c4080e1b08602801c1e0034011280c08400040004502500040d07446211003c00c000c1121424201c040c14000b8411905004046640046030300c400480400102d5171481d40110320b00c42c108500c010107070000c0da04040c0440c00f007125138030025070041d10104002900c40c4140080c6c02c07280580348012a4107000240c0f0764052a86d0040c0203100060416805d04400395a01070030390b08580c0c5110103a4014108010407907900c0b10700542e04080c103031003c1c0450b51070340d01e819 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 141255800 1250 141254550 141254557
    0x3090b030403140a0c051501030b010519050d2307081605010206160201241703030403050708030703060f0b0304060510140609060702150301030b09011103060103050411040507270308 80
    0x110045400030131107221081c0205180903003160000251680011550b98a8268010900080b0344080e0408004101400c000c10410000c000d10348840f11090b0030035007040307900282c1402c115102000e5500303800d02e03000700f0480349210b0910003009040c0541040041c0d401c2c4507980305450088140d0440801c403582c1d00040b1071340c000b0341200c1a8003410010f104101d014001c40034100038400002412071a80400b45040c40045600e85a2101880110350349119200d00c420b90340038000640900c50b001c0030038a03d07001560000c14908000400503503d888110301c00701c19a0114018060100800c000e00c179846c01802d600c80e045e803400b44501802c00c0105001e0b0303080855128051000824594400c0e15080c04417151103400505651303510109100e0360010754024001250051005404a85400c2050141501c00031241000c942980e036210011030080c00700074020f55800ac110018075940d5191482114001c074443c2d40e601b1002d201c840702440d5904071a0042d03c040c4182000c0400100d60071000b40d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 141257050 1250 141255800 141255827
    0x8010e150105120f01061403070906060215150915040b04090c06050d0f0e0d0f0305040807110d150204170a0206030103032304140906040b10030b011b0501050403090b030403 76
    0x1e80003451001d100f850302c0d012a4002d121519864441c01191509003148086541407003201121025500d810035581650034610425026901c494094006c03c0c10210031030f80d000c0c03001005032468241500008035016419a07104168030a0713810100360504241c003540c01611400d403009d1045407880da41e581400c6005100301e0741040404198045401404d0300a6404482e5001c4184040003132041001c0c1c0300c201c0350580358082038501544040107030184c002e651050b500503003202c0c02c1510540b41c51241070744a0388111762020820401c000000c4004911045000d00c90314010f0f1990f007030000324a41035407850700002e8070b588107070b0103000160b8621003102d041d02e6251801441c002450184104458922000e287d100e4030301090125071201000790448003042c0884a0201c1a02d5100a20084a104501450300074002c0744c00101864040e0300040200d50061400000ea5224900d0313541e1821b00141080707655944603002d00090540c81240c41d8050460004428510b09080e40c0280042e070300841c3d03 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 141258300 1250 141257050 141257059
    0x201050309070f0e060910060c0323131e0503060408070c0f0602061609080309010c1104091a15030d0e0109170d020706020c131d010204030c08010e150105 68
    0x501d90020a01618000b480302c2e40844140a4990b600b12100340c0045600b9801980e03030000182c0340a0711010488100c0b0a1511204a21002c1d41c82c12030300325510f10032001000503ca0941c900300d188074001481d402e1014500c0c8103680b410f000c6403110402d42070030f44201420480c10140001c3d0b8020584540140e80003501c40da4460031481c00c4060b03c06c541c0d0120030303060985500000c0e00f81c0c0100d1001d20030f0040584800c0d500110700c030f041d10f22121a001c1d210196105105207440c0b94012000840964010b64408501c01319480003c0c05948220703004031142d8400a40442003020034150f15500b01d245042a0043d01c402080400e41e20f1022a545d034007002b5840c2c00d0042180d00038000f000140080443d940884d02605094503079808801c0b41c504d0042c8524030b40052424030200300e1a201c001e005007601d10b0940e07080a40400f030700001c5c100900303080c2100c590802400091004200440c418a515070581d864030090908503400000d92100580203003102603160618803088905460701105d = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 141259550 1250 141258300 141258307
    0x30102040b0a03180803130c06020a030507060e011103010906090516140708160b01140d020a06030c050c0f01140a090b0f07020a1a060f0102011506050708070501050c0d140402030703020105 83
    0x205004c0c440010000c0c0508008000401d102d100c041007604c03480d0050040440702d680360380c1c0c0c080c200c0c0d40b100380910240004405101c0b01001442c560004011040f82c6000401c01d505025030032000b0394003c0e03021b080407564031501003040740310758003138994090694480c0c102003210041028141c02883d50401e505004009030b400d0800c54950207880305500b55800300d00d00808240b500b4204400f0a00480399607602d04109c1120904d06107044800d440d5002d0b01d500c1e8050718100b0b043e00a020620544400e00c1750600403002090010402510b09121400011500c004d0f03041008107584130191404c0c403054113140c1d85101107104403e5244d0042005016404a513440c454100e0400309007001c0242103224401c0600300c0d8514520b00c65000300e0041f0340b0009540040c000580c2214583c4840c40c80c0703070301c030b200c0104001809100500041406032040524140c825680c0c6421076400321002030f00d0100204025030b0120385e9201b40c0b0a42d0b41016034054003400d02d500080d50b50189407000904100000 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 141260800 1250 141259550 141259571
    0x4060b0c0715050c070f0f12020f19050913030908030a020d080703060506030f04030f02030a2007031b140f03030d0f0e1b030105070203041d0702070f060e0a05030102040b0a03 77
    0x34021200c0c212030031001e44170b156032904480340300b94006104422034011801c101141250071a00c5c000d40c41903004003854202c0d44014140315804102e1500c040108001c2d1b00d000a040d211102614429145c0c0f02c80328124039a00d18015010140e59002101e85e64018008042e100c0c0e0002149016590a810701000310740d01c1c0e01c001c8018001e945c2000b0340207000801800340241501762500c0c040e61003038a90009260310174000b260380e40108144540010b0384c4c0c41200e40400201d4040c3c4101480b843d007600c1c4d88076140d8075150382c1c0840a003014501c20300c1e50074080140000c0810b54004140040b0f920980380464900080d660380280203004d04400d0759110604c030b0f190450b60000d88001186400e4070006070041035214140c5413030b144058041d50030140000c00c443e00c0407040b00d0955403800d050b60024410540c40c160031441c0142000c066101c0c0c0640800d0100e4000d0080008018030381d02c00f09050018004c0c02004415a0f02081c000e0b80140b0082c00004480c00039101e60b040640384c0012200210b = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 141262050 1250 141260800 141260807
    0x60305041a0c0f0708040f0602010c030506033f0a0c0c0602031603181502030403050601090501030b01150219140c040e2104050d030302030708010b03040506040807050a0203061504060b0c0715 84
    0x5947c080040441000300019810b901034002211500060300d00f0807c43e030b41e007002c0c1601d4000794041d441900c0d80b041c42289105038030b4120104607400c50420054002d040100b07003413840c0d01c00492a03010400c06140b40701000f812102e008081c05030792014600300603050342e50300d00c507015a0308006c2c1888558049104805050758a031b100609070100411002c000c207030b001075140d5000740026180b41c064a0004070b4440098040d0718104c3e58042d50819003a881c0c001119141d08040002108500170700a41a084c0119505640c41050092030040a0000d400d127040380b41184650030103004900301101d20200c2c250207d14151403107040311045c18098141300c03c241540c811034001540c0322a00c40c441703030305040d850340c040d6103d041c26842e45405ca036214810f110081c0011600100194000800100000c10402c00b5021192107a0b048480b1f012140d030000303040c0708007243d091001e0000902100301502d454003c2c440200b4001004900d0210070120840d1154502c0c0101c450324549000a075219921 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 141263300 1250 141262050 141262057
    0x30702040b1804080d0b01030501080316030203040314162408070203091801140114090411040b0307082203080f04031e020307021518040b04060807060305041a0c0f0708 74
    0xa10a072032141d5141500d000981c40c5c208603002c2148a1034412050000e50180c41198183c1c2c0b220320003981400300d1005114444601070504400f1400140800000111042d0700354004d200703004064800000460b45408000300d560344080c0040084640c1281542401803110a201020b4505420240c0e00c0c628242d103144200403103280c110b0603020045a164611781c060f541654400c0d146c101e00300070074000445010310070440380105100104100d036a02d162076480ba1420540d001034240c10569100e0b40c8031059002220003e000c61840010001e04c0c041d4034183c0848001450325000701307410300d924010311000005110031b201c0703070b90b6101080515004503035042050a11600201c19014003010094481e0072418040303020381c0061880d04070700460082529400c10f40a928039915400c11020032000d0020418141d402c1603540d4404944014180908806040b4585000c1458100b51400306c0b040f680012034800008850f4051000c0c00d9001402c4511000465200320b84911841c28441031038072 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 141264550 1250 141263300 141263329
    0x501050712020106080307060b040e03070b160903080a0f0909020c030406080c0f0301080a0b010503011109060304030320071703060a0b0703030e0712120905010f03090c080124080a05030702040b 85
    0x40301050f010100b002e25040279400701d10a813028404800c0c2d0411055032801404ea0040100c2400b000281d0006100303003003a51030020903c0c00c4182e80d580d0b0703140e481050f4000c5618400290004c09a0821150400105002420a1441180385c146031502094490040380036050420001c5c1010404a184040030340710910b0111540a5a80d42d44220320781c1d541c0e0101c20200c900b1884040006814907040c881c0030081c07540c0410085c0f4004410040040b00d078001070044041c55610310000000b06da020031544c442c85029141903a4928160601251002c107010f00100e0740e00040007081680d0320744109520484840100d240d4848000d49415800b9190302c12003117101d4480c4007400100d400420084205c2a8098181d50349014412101151b828129000d200d001c50010075404010920a82c04070f2030060144503482c0040352151350305429140604081c40c851011100410b000c09140074090b401411400c00808602c01240d84a60b00d070700078900040d01c86d598999155003140c44030f40c01c0150f030740c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 141265800 1250 141264550 141264553
    0x180a0501121a0a09090203100203070903121101050705091507020d0303050613020313060f1a090c0c1501080d110a060b060903010f0e01060906030201080c03071808101401050105071202010608 84
    0x5488821100007441500e50a0b4408e128013803843e50800c01520880b4010301c82c603170390400302c50b041d9122856031008101c2c1b0f000030002300c00086e80c000d103030a02c1140e010301c4180e0f172056039620307940003003100d00215921041d140241c10012035006a4900303517010714480d411b040126035030761604001141158181c2d10b002900780004100081280d040a004030a0752040d00100072061060150000300ca04018207480301d810805403081c064541018603e07449000310208030315102c815404503090404a110140001c2c003258014003c81100740700e40c02102c0d80d5841d14a0480c1000310b80103a640da24440060892035841000c021161a4071088a1511002600904ca418102e55449009000210b08075086510b0003d0205021344d082c09100210f80c2c0582d41c100ea9a15005905019984050251018030181e44004540c1d001c69039581c2c0014a1000c014000a82c6008191300a46859440c40d1070141591001407000340c0e0030030165451581c0101c0c0c084400700c000c9200360b00401d0782e40c110352020f = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 141267050 1250 141265800 141265819
    0x11110050921040503060714070f0501270b06090c0d02130b04141201021602130204050405190509030306010c0312111c0b1e120c060708180a0501121a 66
    0xb407004100040044400a80032184242d4641000315a0070920400d0403501007010041c002c085400b240c0300d068110f005100010743c5251404c0f814100404040c01c00c20020300c2804403606100c03542400a03400300b0107880c4003509240c580c070f41010340c1c0f1841880140340341d804100f400d95110b10200f0038011b0103808045507956526441c403603d1106046124034458400b40c00030b5480d0070b206000f903455401c1c2d00c0c08164092812942002250b20410036441e04c1698203010003c0c0310b580b18004c82d40150840c400e02c00703400da20301c1501c000f83d850041c540d905c1c640c4204140242664402e003003440b03603030b05442d114440401165106014080110107804000390100e005803040a120000f402000e40b45030003000000350707a0080c40100718000b140f120400d0341e000304040c41c608244c8010905000440143e90741e40d10f1080002d4481e41204034240c079401d5002c10305191b441d4000301c030810a90021517902c24071030300d8800000d00030040140032000041d00c1d12240e0315880700c0d03001c0b00c0005480c01042d5549 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 141268300 1250 141267050 141267103
    0x303050105031c050f0a030e060406270506130602120910060503060103020a050111030f190e220221010305010f0c0801060903120c050d0801060e0111100509 69
    0x6010203006040c0701c0d001d068165244450035000680118a1a88410b8244140003107000000d41082c007584041c03545800d0104100e040038800c440c0328910486c1d0020704c00700010b41513407281601010313840d00303103141800802c042040080c85542c000d04181035500ca01300a07140c880040c0c041c903580b401005180f9810300282c50740208a2518003075200b642002030555420415648080038170002e90005941c040c1484036500c201d4406804c21038140881e4544030700e01011044940c000c83c0701d607610040321004d81124544c040d2011002200031a940d032190004008011103411600006400c4940e00040c0000c8005100c11b03038004074006d403100000d03650707982d05083d400303410000340348649549000402d051090180401c18141c40c420766586440c1410342c0c1d2611004c0c000c00c000c0106002660792400c001075010410060402d01c103a40702221075140c084090640821401c80b00e0501a0030790a98540010002c0c0000e146a490000420aa2100c0d49404d040c015181c01c55000c282c140c003800c54 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 141269550 1250 141268300 141268307
    0x512071520010c0210060b1213050304030f0606121e020102070f0e01081e060109020c010207020a0b090f120d03200a080108100c1d04060506210a050402010207030b150603010303 78
    0x4243c022150242ca544181070741ea007000311103c034014800340e540305004c1e0104000119142d20360100d00c0110001150503d901c03420303e960069817089422400b0b0901c500100301403401a5401404940001400340320603541d41450f10380c01e02c61001c030074000b01c10780d2415607108104580c0104080c0784903001c40364440c200080000b40c00d014a2075544680035600c1e50089903014103825400b856009040c00340d003130090345d1000c0c0d4800302d12101959000c7c8070140169848216900003440703810200c1e907544c0d86c988180101c500417100031911480c81401850000003010514a4903d4800e280010700450f030342140454007581c40c2041109240041181c5c8000764100e16034030305071822002180c00038140c6a0381c01040d98141c0c07000100051601103500c00215a400d440d2120450007800461900e4a074000b00d02d01c1d0300300780d1400c4821102e051080fa00384a054119540103140b840003401946031640000c0e544100d9403200500d81c107901d40c0020041080c0304460041b951000f40707160340c0c0f56500e00300103 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 141270800 1250 141269550 141269561
    0xe10090611240a09170316080c0a1407050a060e06090f1e010b1e01030c05130e04051903080a060b0306030d0f020f0109050d020106051207152001 64
    0xe0100e00da010081010041c0002c0c0c0218265650311800003840c0070340d40041c540c180c040d180840240c2c880c01100c0001d0002101000000c0d03000880c181c99181981c69003da404014210209200011051203000100300c41110354906090920300300040780202c04002e0b510800201604030301640303140a0811005410002445501c0d000326071442c0c549107400e0b80c60314a001402c1c051076202810039004041c44040c5890002000000000c84400380c1d4045080c88150840300b54004140c414640c01c69038061043c07111440c4180313041d0f410b00d03101c1070394549440d22501a404104144e04005400c002e820040c00c6074540e0401d05c50461100c0611b40982821800e90f800c2d410380742004008103500d0b100d4001d49108100080081246400c0050140d0303100111341c071011b003107024980301103c41100034056010f400d4411b5004086030400000d00031308480441c1c1000c0c0c480d4804188a100d03e500c00101c000c20b0781e0714285100c10780c0d80340200980d0440c000070124142805940440880441e040d03222 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 141272050 1250 141270800 141270809
    0x306060905010b0a080604090804150e03100606050403020f030c0a0b031b0319050a0e030a120608030304020a0e070c06090b040b060609010f14040308030c030106030b0301140a09030e1009 82
    0x1d101c1d59032a01c1e0808000c0c014003405800007910000000c1c0149010780210344014066440c051525484400c0c801980c1400c0071303040d02003034400c2c07030640c00c50804122460f500900321104200382403c210001b0120310030380c40068030510f1039001200e00d036a410700868001c080004c1860b100103545c1c0342041038039003088480710003003401490b03d0500b040080044034440c00b414080c5451611132046843c0080030040c0c0b41c48060307503071801d45c0d041c00c000420081150007e16120000408002216607003507403416000517505070020300610005840750742e0400255080b104039641103907241d00d02155040380e200c00103402c241c00e00c0c150006102021510034010ba0003000d10245566490f014806a846808600350014600700c0c0100e0f00c4034415151000c001c000201614503142c1d880d110b48440b0740041c0c2c1c2c614450311000004004158041c4a42103081c84140d000340501049040712450100008203000351194507184003008261017404204424200203105078078481d4050001002c0040c036004 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 141273300 1250 141272050 141272069
    0x2040f08010c0c1707050f1f0b0a030c0e07030f02130311040510210524090a080a030b0f040608070501020118081801140a0c020901120b0a02090d020406030606 70
    0x300d546880c401c3c0041031080e6003154038400c03400021484805503902c81c0800340d4403400f03040031240301940d09111510020b82d174465440d41a00012503028100c0345151040781c400e101c98941080002c0070018080c088901c503000b1a500c40da161003094018105400440e00514030000c0d140c1e0f00101d0440007281034074012142c0f012006090000d0000301c4030155440c21002c49985400c0060112401c000c2e0003243c400340328040c000c102a96418036013144e88400810014000c403540000101c800c0461768000b201034010724503400c00351244c1009211381c500860416427030362a10802920b07448806005000701030420003c0c203907a82503c60710b8101900402c0d005509005003200e02041442012a20300c2e00310624510741050f0204900c0300d6040f06540c1814002d0107103650100f1421078010300004000368a0b005072811141c4104000308505030858018118403501d690302081401c403145a004050010059487c510800000d116014161307000354850300b8060f0100410a40307400100c04c4805201 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 141274550 1250 141273300 141273311
    0x7060314090a11060c01110309010513120e0109080307060501060f030225050a020607050a0302061e04030f0e031605040b0f2d0d031e0503100302090c0d02040f0801 72
    0x158180c0e4001040d10625038560003a038050011540301c0789045a0f0040c001d26007403600f004d801c0c00c0c40c02e49003c0b05034021011804810005698400e015050344035050170003054100a159440e000b0684086034602c040141200c40302d81164018400d882c0030300300900c101c90b10745a0b90310701440035050902a890008280d02d4181503103a0083c020740d80b0000d03000b0b58440107071024250040c0c4500b2000000d035020321440501401680302c51009103180c03400361019010707225540c2806460450b01500900f008240140486804841c91801c1ba80107603041c41d00c82100917281ca000c80308500c003104019494042c2410070030a41051182c1c0000300e880030749040c4011041c0d0b82c00c0101ea905050403403a004944a480c0804140100e41c501480e220490700b8101d4100552000c43c800c5800808100c012440640da600d00c1004000c42a00302c0c1215440c0452841c07821404411310307188103101c028001e00179840811034034040710082d50040c02d00b1040c11034613980d0f43c440b02c1c060000f8910075200c09500c2c24 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 141275800 1250 141274550 141274571
    0xf02030601180b0706090c090524180402040213030b0c0903070b0705060f13080406030b091005060d0908090d050c130204031205070807020a060818010b0d06020901180305070603 78
    0xb90320a40c211096418110304008903070711244003038a0030358011118408450000700340481c8070700c6000d0041d001c01642e00e03540700c0c84c12041040c50550713100d814800c04100751480e4800007081d0741150700c294186d40260f1102501c8481d500d80d220541c100400900d0a241000480b507480d0000d06240b0b14110200c5100341d541d182e08006900c90f44070003515a80244000500004411000c560485600740c0400c1401010b0703221442e0301d400c00e8100c1400079031501e906883c24609880f440d508a0701c4540e000c8651468000094117500c0781e0710404065a80383c040322421300c8070324016900480720203000071140400e81d140c120340360900001c1e400d21480d008800300000407414800e6405403540070081e0310610700310700c8069455030003600003111b9240c0e04000341d0340140c4dc2c5202a10003400f60713444031541824160784100550010103a5002c2076031500244100760743d81e0854000110760000390043c0e1314412800107d501001140040404031000100081044030014000c41110b000b0344d41005143d501 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 141277050 1250 141275800 141275837
    0x306040b060301180203040311070e0f1f06261305070b070c03030c02061b0f010606030917070206090a0b0703031415090a15091506030c020303071407060f02030601 72
    0x84c0545843d90b0380d00390300c10300c0301050b80d4019a0000c2c06800c2c0505c04810038003100746441003070b4000e002003544050500078903803e00195a07400005104400d01490716545070b8480b002e2031032194a04226060300c0e407106107003281042c451004454083c1012501c2d24100030b1f0818500e40d001180d181c0304081c80080c0641d0040e0541e20703900d0b40042003800d00c6185440440e0600d200d0b58041ea400a03003000740d05c0c0581202c100f01000080540040c1140c880c41c1e80c41542103500369804082803500308100d00e0001030745204001d841c10721555445440300c540e0b0021490354001d0300e10880e001f4000d0380008c200d6000070006040424440d075000d1003803045001902c00700c1c0314245c42440311740b0080011400240360091031194060510800002c5007040350f094000012100da11444145549030000d00401c1c011150b044007070134a900341401900302c0d17510000d43d40e11000349004100111031000c2d00b440d0540c0b0b4200c400b01508007000b40001030f5010500b4000394800e440c1c0342d0102c2d000b90010780e2203a04 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 141278300 1250 141277050 141277057
    0x31d010504180b0102070b070605160503130303020f0f04060908010b010c120c05010b190609050301140c070f08030403030609050f0106090603020a05071209030c090b0a0b0a120906020306040b06 85
    0x8414903140084010711400b5002e0030351200c486055001d0550049507180c3c2050151601602a403800b117414107110547c0d00c00c10183c0e030281030070071004008000f1002440341d91b0001031545880c0069468050014082e11030250405500fa8014001800660194001c08880c251114075008003d400c101c800151204440041c00900c11881c9442d048244d50041890800309405040041602e1950707400050b1020940b001002c80c0c084894018450142d00805120103010254000c0040c0e000041c80260b049074000c24141d80f070340000030303075038108400d0420411313903594030406564482c100f61502030f000c2d000a024031580249040c002843c40122009003034100c80007a03c41c0e000d100d013402d178103c0181d48007110303080c00d2000801a02c0c0010781070300071230386000c0c02c9546d80441c668110303e480c9070200c0f45984071a81090030051000800c1d13840700c400c80700302d4030302e100d045540780c56142c0140c8909465040000c5404e2070024648140450b0760029480b40000311000c008220001b402c20020b0300 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 141279550 1250 141278300 141278309
    0x4140d0909050a150b0a020d030e03030f040201141215010c0f030305070507050708010509060702060f010501050d062402100608060a02090f1002010c0f0f1b060605060403031d010504 80
    0x84049a0030419514079502964004403005408255980c5105402e1446501c0303078404240300300000741c6003d203194144080204403803289010302428120880055807800090030700b02c3c101c540403002c2821607008007960001d8026000075a91075031810b9504e05000e0204840e102c00c2c1d24910b0085505641c0300c0c2722200049030b40b080100c00060f1554801320b0042c0401011807050040402c45000800e90810800f001458210300115881c03400340491f40c10241c0140030142554020b03400e0003e0640c1403003070981510001e10740551540445c588800180000c2d6108201010b00d80e02030500c01e0f42c4082c61000f40342c5068003240e22000710300e2414001c54803217104203503103074100d14086091480590001c00c520000100310403200b00ca01400901c202c420035204c040075030354039141130110720742244000000300e0039820522082c0c442e040d00949441c6201f20002c56140400800004100c150303400350000e440c1c050319076600c03552249400742202019500058010307203e0582001690b2041d0115016a0b = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 141280800 1250 141279550 141279557
    0x180108071a0d0506030c0a0e0103151b051c0906090b0705190507260a090801020901050414011808030a080a020a1413050301051311010801061b050a0b01060804140d 72
    0x714070240c0c282c0c02081c0c060042941405000c4216a0030382d581032611002e054031240c0e101640d4503624090b2140c0032a9040d08042c181060b0b82c002c81d0904903510b1990008280c10a03035a5040440401004080008011a40d061030301180b1018014264401034174503200c0e400f1089030380c4400400b90740f01d00a9a4412105146c007800c4200a544102c01420680c0d01c03c149003a09810b1500c0000900440300320ba0620144000c034603001ca01e680200313184010300c034000086190100410000302944554001c5510b10411885008001d92141c08225625407041d00345a00054840a070a902c0b6840000b180002800c8000440e076140401d108603070070815103444a0140b0b6500d0340202449401901c402c605403003030044005010f071002e0050501c2040401d0492040102a2624181801e00110082d04101e1000c005101e00c03604042c0040391030008580060240780c0391725081e0700c0d280113540c00400b03d5084100004400b6040800140031754894443e00380b103003200000719965050302c2d40141001 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 141282050 1250 141280800 141280807
    0x21002010b0303030a0c090509070f02070b090303030408030612010f0506040b03010204050a050f12031c1b0806090910020c060411240304030e03011a01110102090a170705180108071a 80
    0x5038611b034000760200c00070303051620aa680c1da000160014100300e0302d000100d0100c00c0301d1040c6030b5052041100ad40721104590b800c00d00a0004a0740e07038000144018604200040420302d541c3d11400f00081c91030141c00207021810244060300c0c05042c2c1030381d44501440c140102d0210f03918060090700d040c0c1e40050300040300544bc100c20010315070201020181c00182c005044458084180010031865111414000309611420200c4084544008900c040d2030340000110240d25445549030303401c1802158010b2640c0c036800c02250038201d20704a20a80035200162404241d0404101e49114a0003480d142c1d03800300c032000c2404490314400d1036803982032290320f00009044110710040c607001402483d20000380e6a002001c642141da40d0b1003021560004801d18075002c1d07a00481c440507001e0400000c1d42058881130110f10750004078000d0080076000700d884c407000120104212002403900818482c0701000001c5c051400200038010000f190081c841e02282e030070602e84143c0c05415900d080a440d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 141283300 1250 141282050 141282061
    0x91502071a0406020f070c0302010e120d1119050606120708060a02070503041a070203160503100906110301061106090d08040803070c0c09020d050901050c192a021002010b030303 78
    0x201403005008841c5568241700c0e01c00c2c000f244202a000a40c416600b051a450031800054002c142c0d07130b0360552050307500550b002d588400104821009103040c0c03e121180015003003085003086041d1500030400a0403040764002d020f800546503006003015580f01c1c1d452261202d015407038044d180950a4a0f92000c0d01103103219001d9070080101c03500a1050702e040a8449104072004203061a10f0402c00754040391880a41c502404154120071703140c21031881c11441e150101340c0304e64188030540941603451594509111950b006541d440b0100b28101e507496854050140c500c02003d000702c1498422100001e03400c5034000740c119050003494440702d2a40d51a5901d07030005920040581040010110035500011640ca6918014150054025031070b000700610890480d2001414944668102014007030702c05041000c0ba8642e00d900f803824070300e41d050a1000c0e2590f404110b808074140450b070f40000d4540c0c1e5400314034502c1e14800c076103050812052000480c00d82d181c06814991681042000c140c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 141284550 1250 141283300 141283343
    0x1050319060803040914160e060d0608060f090f0c0a0b250605090d020a15050702160602011a030c01080f0601020127020a0f03080a0e0607021309150207 67
    0x31411400302030041501511a1111411a04260304c45140c1c2900c8900c02082ea2020091080e440070500800844a0b24401c6000b0f00c1850b26401c80e80c001c850010b900303240e11069030000c4020340241802c4540314184078200c58100203048036104503500401a0400c80c3e04004104c00c8080c0c41c00521628080c0d05007122400a58000210446002c031050103440c0030348400f07041c801e5018000c6400207407915008061504241c0d5003d208402c6410580841000a0030f005400158409840e00050704d507885c8001640752030040e504070003003550050070000d0001c2d8150016004c1d0700180301440c03410400703c2e041c03640d40c50b01d43c01c03813a010800f1400043d00e120300d80c0e141550f0100c4148008140c02c6236644501105410341160802522030400e111011f50070141c41403401011354026a1300098038646a001c07141c0182e107a00420466034144c111520b07550641900c41c0309800030003680844941e015040000d08032503800310b40c403440c00e100f43e24900d0814800e850640b0382000540b103510800d0380000 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 141285800 1250 141284550 141284581
    0x5070e090c0f040f050720030c15090c03060c03041b08031902011503080702040507090b1801140415080a06050f1207030618051504210e060c0304051905010503 70
    0x660b0856540c43e24207100c400d680c040c2c44c2c0581c81c6d5031114010451b08654071320841400c8042a011540100726111100380001041c048190203103008005d907440f4146214100381e6160041c03a850711426040c059002500c0c4c0066008034031030300299245c91000d048140030300e0031520400115030424807010610b85440079440c41c01200382d200008811040c56804542401e0507042a115500b0104400046080c1446007076000038171401e006814626002c107a03445c610402c00600d2001030480344101e05e6900036100002d41c41c0265020315180ca8403403251403065103001c100da00004e6034203400300740199424440e0b40107941c0c000d0109140010090107000c83c1d08a071b02c0c00d032100d070300c201e040000116803035110b445030018404120b40c40045c91400d1030b600d0076000000b40c9803240700303240034000040e4500f900c008140e90740a1032120040c18440d416196005c4681f20250040c030006420a410000072000340299542103491180d400503002d681c10b0f80f0541c601038540070417003c0021403202c55016620 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 141287050 1250 141285800 141285829
    0x100b0306070f0804140f010f0b0f03060103170403080301061205101a1e0301090e0601060f05090909010902120601051e0a031b03080703020705150306090402091305060f0405070e090c 80
    0x30203140d1917040401c0c9000542d074038911459559480000d02803001d4041c1e500142e108950716046540c0580c0001e84891061000500d419841c002d1074040c030b207100303090310019600b02c45800d03125070b56108054000d9240240c10410b403442c00000810358203428800302c042c0e070b00c1c00e01f1803c8011014000c2001d40e500a01c04403001c141c001407840303070014065000354003810b010040403c00c044185c056034640341c3c040e000801803101a01151817502c0d41309042d03030b0752644111980c0c1c01c6916196101030040c54500000fa400c00604c040843c010500002c19038100c0381c050b42c80c0608030103201445c005000300202d03055800048680100301040510b0650740100c3d903180000445280d50ba6514401d560021780100c0c0560020b4030f0400403441d040c081603000710211005145146005070016100c1c0d5002403000b40306508120110380800314048004c06841d512004586003820143d184802c480400c84044401c1d20441c0c0000c280118903a0f0510300610740d0100401201d92484100001400707241e05 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 141288300 1250 141287050 141287063
    0x315210105010312031413060b01050c060406050609060f0f060c010612031119080a0804050c0a030606030c06020d0903060905121b01050a0c0504030f23100b0306070f0804 75
    0x4214012020310a00d8000d500c100b03d8554008105040a4141c07001009910050882c10301041140504001a80318896001d071000559020003001039505000b900d0b00c0101078410841000204502984040d00468003107030f0948996949070204010780c02c0030401550009584069a80582000c038040c00c80d650201e000881d21380d40718800a2485580c00d02c0690019080c003128109245061121001c294400d42c404207050070b103038035601078600c10f41101c0300400134020002401d211b002d200041504000600001c0c01d20303a681425800b80c00b65002c19125000d01c007000003101400003030003130121582615482c8615207980c462600610350107400381c8144c000e0030071420049941c2801030104844800410368494240ca6081d070031148010326540f14207181050341c0244503042019201160351100000d0f07285403840c070344168648500030040c40320720810a07841d9540c07600480c0c01e0140103841c00c001c101e81c460070000c16941c1c0400f0313110100803410300394885030a0703403051071401d5200340200f4 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 141289550 1250 141288300 141288349
    0x111b01020318040b1512070306030305040b13090e03070309050405011d09031e0307020f06071202090a03080f091003060f14030a02090106021f051015021504030206010315020315 78
    0x240802da00c0c0c07008401d9034010744c07030004144c0511a019034081f0341001c80c1d468108413071411a50050700707611903801403000010700483d02074000500000c420000d0203a140303040c4144440c3c1d5110302d540b9000051300314082200c490020800741001e00c41c845c12500101a00f40080c110388965820000000d4594001030008001400c070030322440311312480701d0b030501000306c0c0c2da8980040300900b00980001a40e10310b40100061042c0c00360300000c00b5070091000540180c1c1d50111000107240c105c51680002d0800c4004130341000910306c000050b00003420f00b0b031220b14500a0401045040381c0301d5004012550004400520440400314000701c450000502120040303400c2d6000180940303805d038442d90050340403d920400f00e030070031010040080c407501e000f80128100207840060700805400b81c4007202c00790f00fa0081c1c507103208001c1c1c482004200d000f041207904290a000f07403194424001520718880385c10310840c0b80310451084034402e02a8504030303900c004192082040a90041100d10030000d903e0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 141290800 1250 141289550 141289571
    0x1050d0f0f0c421101140a050601020a030206060f030703021c03020c0307030c0e10030605100311060703050706151e0e16020606010c06110a0305150117040807050102070b07111b0102031804 83
    0xd02c0b80ea80942c6e0f240c80b0007102c500e007616520040d180014180c1d4115041005030000003900018503d8001c181268003014a02244001c00d00d490b00650003c0d62007203004190b10202d080c0c189141c0312442c029408e1703d0a15074a9400d06036211490b00c4000c2c422403030010704019203208484002e410002c1400e11004880e920344070725041d1601a100004203a900c0c2d102041000ba0080140001030342c299403903401c119160b10081d103036024600300900110340702e210240748d07500d030300b07000101800c107a98074810100400300a445d4203642c039000740184960f844e00460700b00c20800b0300440d80c0110950040c07015913503a4004565600c40c6c45412a0402c0d1280c02c9040c542c41214b01070b100c2100c00790340001c0c151803c80b405050726141c4090706414005107003510551400c02200c143c0d03100d034001002c0c41e5079924a1802078020700c01c111004d00044595824401e10030ba0280c00b11851a014034121030300014010300921195072002d1020b8090380c070803c00c201c51b031ba00445c03902c146e510b0020f200240d0400c15 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 141292050 1250 141290800 141290803
    0x203090603150108100f090f02040509070c20060d0e0106050a1d06060903030304020d050c040c030b03150903040621020408070e0f010e01050d0f0f0c4211 68
    0x1514810800030440da0901d002d96030220302c0580c4501c02c140300841d41441d004481d04c0d00119400b0300d0720b20f607840e410ba101561010341c044900421000c1c0140c400b5107402c0600038502c5038078020480f100c541d003100160013804100b101002c3d5240c02800c7c0c5141804400c26071004015040c03850009540f03500f40010a5903425400200400000e4403100c10003803a1442c0c1c400070400200b0440c0300341c3e418015040c0303d803030000a1b02d0740321f83d050300c41c2d04110070182011894101c2402005a001c0d00745000600101da0640141007044810380c110381c8620006400d955012000320b9203814194418841002203500c241c100700e44454803422808008811010104182e0b44141c0200c00c1640c0304813800c000b03851512001d568005601071048082c5e506040425408134418401d0740d20030b681200d25041400304107500394071400c0e407007140103d204c10380d403900501f185581c2c03189129040c3e01000c105144200e035a141c3d211035442550400000740741450f81001c0314044c0c2c00c2e56040040136811600080e00 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 141293300 1250 141292050 141292057
    0xd0e030109050601030b1f030f0b0907181b0309030206150a050315061002070305210d02070b0108010b0607020f0d0c0f0b04091d031e0d0f1d0109050d0c0302030906 72
    0x1b440034003544d103030000c01c0ea000041140c601c0042100e06441c01c0020a034482c003101d10b2564803c4007025a81c84450019180c180a6002034520309000889a804100e540d44000c06034544400f81d0202010381c0c00065085800c840800b50158102d1000203403074202e0f80040b8655800c0c003c1c4010303804e9484002107841d00310746c220081214450300051014515041d601d0a20722441c606c001c202441c10b50740d80c16100d03d0030751084240c403003d846061088030300d00000d652042161000441d110182d60601c1c3c400c00380203210b50a2203500c0d05007076880e18282031003142c96a540282006e46000104021f0101105014174103841003002104086115140c49003514001c00c68601944d445a04187c0d10030f08642105404031000f4404000d28200c03283c01005a5000e5071101d0407040001c06500c1903c90240308200d102144180743c5403d02ea6810301691103200400750803600e01c01598001c49003142220076100c000b60036039000c6080301d40350910900702d41d07403214400e00c19a41413440b020082001e940 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 141294550 1250 141293300 141293303
    0x31608070203060f010b0a110106181b03050c070305091201060e09060901020414040207060b04020307171501020c15210105130c08130f0503070804030b01060306080d0e03010905060103 81
    0x480010080c05510b410000e031a00600d90b80f40d00016035240c0604883c0d24031810074084244140c4480e4221640000c1d88840000c3c004100514a002007120445005284104c540c0182c00d142c0140c401020388039104840c8078085040e81c8515003032075500e050321580c000c140481d50190700319108020441d8203000758401801c1800a0843c0d40c00c0c0300180504000c0002c12a240513841440f0410540d43c40c1c00418025610035180107030341c1d030b00d1802c00e0000746c900c1c0c0b4405a0407600000900c400301d90320040320521022680c00f0242c140e103440c8401c6198082e1054003d006a10400c504150b910703050101d00d142012a85500e450070040400340642e41046040c48090640080300411550410b041c000005034148401044001c00d84a0301a15992014200501c0822071800311401c0280075003200d11480d41010840b80c484666103001c401d264042c1c0800c8420746400700001881da4040d0040606446c2d410001d00080c40101c0d100325045155544a591305648407482c0002090013400303014043c6 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 141295800 1250 141294550 141294563
    0x1407060e01150e0403120b1206090303071101020705070b1303050d05180306102c2d070804020105030406110304032012070b0c090901120606062c01020316 68
    0x80c02c0b845090071500d6140d5010203c00c4a41e0020400025849100e9081c4180350050000c0c51750058070200750640034201b078400c81440f40c2030034030295142c0000a5881a51903a0f140781c00c001111110074245d026924008200e60704c40c0f8001d01c10000d00c0d01c09024500700d00108a5481913494130b8040c5000400c030040030214000091011010f10100999460baa2060780244601e00740881c0081880300d052048041c00546071070b0400200f00c200d4211040c000e00c600780c0f400c0904101d90450720b254150108440302c43caa48003c1200300324021080d07071040041d40c0300e403032042d901d640041da6682d10062040354001e81e00d03855031503540c4003600a5400381d8000d5940e6010030386151f0314003500254291a50013a03611244403000c5841000c030449031001e52088000c1529200c0040b85541405420f802e60760100740c02002180280c0c00c0104407500c0b600884040c460749646001c16903150a14001c13903a9480b002030305072198441c090f500d1000f24041031049038a012202d8039003444104c010070301120314 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 141297050 1250 141295800 141295811
    0x7030f120201020c0a0602210112121e030e0706110316031b030503040b100f090207020f040606080703061a04051e061c0e030412021c021f081003121407060e01 70
    0x4842360100501c400381e00c0c80202c54600d5041c0006a40703841c0c0c1c0004014440c0660301d03165200b0764400c6c20380d0304420348035903040404a0b1a00c10050060a40c064891040384101800015080d204111200b0340030a59000b0310315101d00c40401c00307500a1a02c070207030b0a221004105c005031000200031840c07003a00966a0544a0401d442c10801040b005001003100d0403103400d00b40810b0b00c11380106411501c0c517050069458243d131005c1850b03080c0340b60403180d00500d020310010300c158212880324415941c41d0780c04c1100c2d50322400304901c44250085c542008140c244000e210604000c084046503603415030031449004090700000e0003076480420119200c0c0340102005a42004600401c2e8803414030402450620303051050703000303105c03441140181c858144844d00040300742120040040842e0082c0000d80803402e0000001072601d00440c8241c00101c008000401c0c02c0d4800803080256640405076616240a040044440b21300e018070600450720100308801c0002c205100d44280500b01c0000441c4 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 141298300 1250 141297050 141297067
    0x111070e0109062103090506160605040b0f0f15010c0501020c250b070503071704090905010c0e01030b010c0201030f2406090b12040611070803041a0907030f120201020c0a0602 77
    0x111200300401802c10500c540d40c4e03070000380c1156200040c1c8006407072850b220020b91070f036110f00c400c5141000d4a11460702062005002d4842c01031489079100c1404c1c1d070303c19200c1c51164500098101c0c1c0005840d03242a5a82040b98400c4840030700d030360b0140d4005424491203288047c00d203482c2d00c91079603101c1030749071000b0a0450401c0c4051700520754005c3d8641460100c0d100c19071607214560005051a00368500400072805c0b007015100944040c003000c1001c60650b25100d402400082e54130f1b00460005490ba040d41e42c071a01480f040f5500c10380d80d049402541d54019000f500d450038498507020f44844401811303a00304840282c03410f194040071604545400c0307000c1c0591105410042e00354204002c1101550701c2034445a4205910000006088628441000550142c080014510403000081c40188028400e241c0c805980c0a21447c545031a001d114550b40c130035601c40203201e083c802c800000400c0244400f2490104540009884e140000c1e1b55a42000c4491500311000c1d40d0220301c810 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 141299550 1250 141298300 141298319
    0x203130201080603030c12070f050607050a08060a05060702040f02190c060f06080304120c03020604030f0204060b160b04050109050304170c0405041e05010b060316020606041503020111070e010906 86
    0x41d0400f90a07400f0f98036141e42c0340185620f07110030f40440e0420712800a0380d101000700d9041075040042e0070506070350f0380742400c500040941c2e00040c0303410002040100407d1341e501d01080400111100100011b2410511758240000340c00c01c414900c585982c240020011101000768110420b8900d64a210700e250041ca02002211404244803220b185015000d01109000104990a445072000c06070680740c12440c00600c43e49940d000250001000305001003000021366821880d10f10880d018042140c4810005010340281241220207001c890007600118000001c100e8005010308004949100c01d925903d203107a1081d40140700922415400c40d80d0481d0610070f89003048800c44080c40a400c00340c8403003400b050700e030b411103001d0050703280d007041001025844141c40400160241d0740700d1a200340501005c05400d071041000d4000c020005601c1c0c80d0502c2400340c480c840090a00740c443c1980c00445d203c41448521a0031072140843c04100d4440000440380201496800400d81c14140f60100 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 141300800 1250 141299550 141299567
    0x30603050f0601060206130f080a030e150603060105010c08160506060307090504030207030206030a0f060816062316050f0a020f0d05150903091507020a1d060d0201030f0203130201 79
    0x1d9035034000c07100610045901203011608400301a131420302c0540a41060108082c1e03100d001407d8010000c1e07540b101c04e4140d0070034515084d000041c2c9075900c03100d8044510308001140e40a5041d0803050040c403030340d80602d8000c035200e801660402d040c480e9004070030110701e66144041e0f50942c400300421030680307401c10202018144d1940d05000c1070600d540d010b96280710a00009210700e1022000800d0042306a12504020a41140502081c0c2d0368102450b250318225075140f800f100c803a4401315459014605404444880c485881d2014020900d1038007950024050b40a900140030011741c0402c00410103c1452001d06003d407080c9a003910402240d1400b60490078068000482c080012134800318a050054081c003021003c5607491300f03400c90441c442c940d00107601041c0700c000800541000e0000c0d00213148240c600d440401d0311001500340d1001110b48900640300080e000030603904210300f5000020b4410b0401060a800d040303032030300598204440d580c050030400c00d0024150f691003102c1 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 141302050 1250 141300800 141300823
    0x60c0f030d05060906100f050a050c06070c060e03120a020901020a1205040906050a1d040c08100510050607050d03020a020a20010206240405041e0c090605040c092d0603060305 77
    0x8481e24010700a4003415003031f50000b40d4410b02402103440354443c0c1c024400c40710050000710595000d031410020113401034404002c25201e07507141c0415051450000012102900c0100c030300d0007115075541c0c0d8000302941c010504581180904220400041d84c010864412080d113521001c4d02c950925501000b10b902d075910062107202d61a600300204076803e0b8030410f40008914040d0000c1d6140e0402c41a2101283d00c0281c0c64443c40c0c61082042034542d20450103148540501c004180d84d450811566020704400a0640c2d0010401e070030116009074014441140a03005031482e40360f03942c03641542080c44401c15420020f01c1542c048540d80d040c002e41d98030090f07103422001001c03401d08075202c00f45148420180169a6080400d046c00301c1860381110501482d08200368402181c501410081818032800d0070890508402003140c2c42e00d4080e840300e99449683e000c454a14141d0500079000c851006506880000e400050035084c1c01c00302e40c0007178611034038045001c618501c0c2c01460120b90400 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 141303300 1250 141302050 141302059
    0x9030a0e0d030f030b040e060903070c1401020606120705090a0c030e0105040819020a12170f0405030a0e01030902040603080c070506030906040b090f060a0b090703050411060c0f030d05060906 84
    0x50340e0019030841441e4080b800f407031900090320060000800c00402440007103031154802d44d8100803103400004003c140d81441811003600c46562102d903501801c0c10407410307a01680151001680900f0001040e1480d4050b0a04031024a0303942c1010902c02942070b2200203900da10740702d680b4190b5825018044000c1e040400070059490140c43d5410b040c003811440c501079079442c807078401100d4801c00c1240e64542d005808000d0032111104050031200030003402c1c201034580f00d0700240c281d000700314080344941c4e0044095403a00501d0714080343ca00d41003607003141c1415526140000541c6980c4500b0014520920216130340d10f1a04090364644880d5502c80b9214140070400c0012290004c03a060b41c2255002503114226100c6a60890509905440c200300c0c0e886641c0410816460940012241501c00e846402d01504e58481c110151201160090f01426441500f9100703400d1a00081581e0a801020b0b0340615110301403050960f4084c42c0c04078262030325882030014914150100640100086071b = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 141304550 1250 141303300 141303319
    0x3030406240311060c01140f070c050a02040203060d080703020a0b1807030602090a0b070b0a0501060c08090118050a0305010b0a052704110d0b07020c0301060602210706020309030a0e 80
    0xc0030762407442440c2c0001000140002c0d16000710f07884150a44003000d61042c0203000d070044040480340d00481c111190820350070400003164140e8040d517440410240c010001d486004180d03004e0101961010307009907007107004820400c01103100907018001040c401c3c0c1c050001c000c1c40b4100118110303c00f500c185509140c1020700086a00c00142002c1220b034000c8001d81c5a4400d8000508418a40d42c003503400003000042e038108101521441c140b1035240e0400c1000b0f243d0300e030750049520345040d540080406c2c004001942c8190700944604059001c542142e0202c581c50700007041d900c80c10790340304451a80d10703001d004055142c440d41d81405440261006e084000e00d1260104d8019044000d44034640c0707568000ca018046424480d001030b450160000c904407200c1d151040000d44115043d10040c0112001c02e400d514043c0142003c0340c15550003046400d0b14001040d000f500803200300c52044400b081074070001166030001d107110b0f1500001030740c0c0f58201fa100c042d01d0104201d07a00340c030400018 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 141305800 1250 141304550 141304601
    0x3080714090904080409110d11090d0b04150213051f0207061209050304030b07030506040510090b060c0708010b1003020a02151305161a04080613150501060203030406 73
    0xc1500d442501c1152000035035100e40c20f00b5407003449944c0100340000c0c241940280440d5907100249008400f002040183c0c007038007040c9500398005d090034240d000c00702c0310400d804a921700040c55001070164088240c0c0d1504c21904a049a000320034140300341403146030400181c94420303090141280881000203a100d2518002903c44c1482c3c0101c0c000c1c450391100440c644900c0d5400742030150780c060b080703030340c0d450304c81c00c0041880c0c2040b1400b00000b800e0000190321420140103a600a4081c03070b00c1842c2003802c1c4000c12010300461692160088014403000d204554101302e0b8070010001074000054080d50382092111010700996440181801000320210003036000071091010380e80700c0c0c09003410741c03100002201c41141030180030b08140700303090308417504450550824007100c072405078500d071007071080700180080d01591181d64210381003c000a00b010304004581c540043c820580c8080c3e40d5544449801158000e030170100043e44007004100c01c04c03403248a41044140000d1400e40d600896 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 141307050 1250 141305800 141305837
    0x10201060510030207051e070f050105091e01030f0f0207020906033418060f050109030c030b0604090503030901021903020910200f0a021503090703080906090a12030807 74
    0x442d0b6411040603070005100d010322400340007030720504001d0303062401c0c582c1d20000f03181d964035028001c3c40040302c4407040001740d0758080c01c02c680c2c4d140400742681d0204030303040080840041521161906040d02c81c00c95100b2800603203c4c441071403a0300030300103807141c281c0e0050081944004005da4040d038450303044140f11480c00b8a01400c07415035010050022044040c0c924070302000340c0d10807060002d401914020f400e0f0941c102a050340d00c5920344c07880c541c1d540d000440d007000c0a480040c09c80c42d403000d0305001080c903400b50b40c0e030310000242003c9015204c50b0354052641d8011030345583c080e58085107010070341645d403e445400e08230514003507007002c3c3d113031000610350400400b80030142728000802c02c40240c41d00e0000040020500182c1d8180c80ca44185940c4030114450100e10649102040c0028860406d0580b8002c500d50b00040071001c2c215640c00b1180c0d413004400c2e991007142805031803201d6680e054200d0160440101300d820350491850042e2402101800e20002d0009120841085041 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 141308300 1250 141307050 141307069
    0x10314010b0f07080a0c0605150d14010e0a0503040312031e02180301061403071a091003060306020f040509090106080d0518040e0d0807050f161110030501050406050102010605 77
    0x145820300d03916040400c02091500c20200010020071340840d89510b80c80d044540044030300c0c0202c409002907601e041882c060000c2510751607034421728090003440420302c041d402c600d401001400005403180d030f40049924047d00010212029440020103108000880c20788920807402d80c1401e200c0c0140d240400074101c075a002c4200c1d03205502155080c2c5040130098000c40c01d2401070000c100003500e90b103814071048202d101c028068410f14400081086207400c4002c880c001014000b0300304503408080002c07010950810381c04168540401001240300e520003001307180c451400441e0703107a14000501005240041c814661071f40340c00001c106100700490445d04546491606550b2001c100c5c804207001260704004d15080344c540350705095001000240f5081d94405502d802070f81e50340f403000840e0700d4404d003010520011003d01c41603409144003031684001c5441207845901e030742204400301c0c071044605202580007a03100c1004014508041c450030014010a20007402118144404502c4512 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 141309550 1250 141308300 141308309
    0xa090c0806011707060f020d2a06060f0b03060a0302010c030c0501021908010803070302100b01111f0e030421060e011404030e06070201090e04021f0804030e09010321050c0d030e010b01031401 84
    0x1200c0300041c074012903951403419626001c4109c244d0101d4517003840340081046001e08283c4403140c00c000b040415840c0103491040000034100c0d99000d06681c011100c460441d0701c00c805008100d024075001440130b0029080400c3d020810701d040c01e40c1002c0c0140301d1f000690140701c140e0810848500480c0d400316001000c2c0451b0300000c6070700c18071040100c51480040e21256031170b0107140d002d10207511944001e03820901d8141014400000140081ca44910807441003405070510705a40482031004c0d40c50030061923009410000701191804032071425501c03001d0b901d00140c6400d000b00300405070008954001200b00b950007500701241640007030011000d0b070182d61048103c40001504565409071035601c21000540c218082820650b0041c1c64040c00307540440105581000f0405a41005801181200e0300170049202d4422010300c46006040d034000e0b100c040000403c018803840b0720030041c1080020301960f0000307210034240315441c215102034640c00c0c10141022440c0089452a449030360640c1c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 141310800 1250 141309550 141309557
    0x30812060f030712050c2b05120a23041401050d020d021611040209010f05090414071101050c030f1807330c020303030a090c0806011707060f020d 64
    0x1a12144000340000846020706a40341c420060301180503058180030440c2d05214104840100368500d0420040d41e1203280e4081c55048031500e0b403502d001c48000c01c8080e07280035000790380b0b103040200003c000780e500400c00580840e01030411a01c0007a007400960003001810500c050409003041400104444000d40d210b0401001082444c80c04110f85d04a8900c1032031184219031307684040b002c001d145030041d03005039540c280c1011580b80608040c003c0360030581d030595910ba440490788a0aa805800080340b25801076a01c2454a01050010903447c1c0148490703290300c03801c6c1e18001d60007400d4034001848100140b07010b20901c0b080040f400300654204202c007030740c1140e10102c01d6860340303000002c1d80484042c09500e0a411182c7c44812140d1801d03202d400c0d00d0a0801806080c11381d045c03203050000035016881003001845038100c41d444800c0c140d01c1030605401d410341d6124254504642038101a0108a003000e034070494600407c42c2b07000038140c07424628106441c464000e074071181c0c02d24041d402d1 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 141312050 1250 141310800 141310837
    0x105040503300411090a0606080109230a050910060f030809030307050709051e040201140c01090204021b160b0d0c11030c070906090902060412050f06070804021005040308 75
    0x52403841d24454403000c1c2c2520b1441d02c40c502410a00c40d8a050f00310528002d40007540807401e111524001c0700180c400d581c540402591030064114014803503d03d4403121000700e1440c5c0512a040b612919008a440034800f1820381002845d003403c106034420020201403a1a50410112500709090003c03660402d014a40710700000010078210301c07807550018a01c0c002d413a00445c40d0b2082e9403200c0c1c01140d4144040b18801d5940340010452002503070041d000ca0b440380e424a0080d0642002812028186400031650300540d40c045070a0360054420701d601814035031900001d0140c208521011140c1b0303141041000392400700c60100d10f1042c014103131600c0340c9507520001c070f00b4002e081041c03001d0005030480381c0d150f400d000c007a40c80d02c1d83c6008000301c40d03040680008503820540540119250014000ca103480d240110340005010f503420120754034041c1c00030800b503c00081c0009489008a038503500d01600e010f20400c038201039007400440902c5070030f12050008c211454103890031083e40315100c504 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 141313300 1250 141312050 141312097
    0x5180a060b030319020a050d0908060a050406060b04080c090a020a08010b03070215010b0a080a02090307060302070c0f061d0306150d05011103161202070809090a06120605090f0105040503 82
    0x30f500c44d1244114111240c2481018090b9000420400c040e01940944a01c015548001c6034a00e40714815045c0d9540210045185141c03c2d5008581092203050001803040d03890140d492642c00540c442d59135500003458505142c2803001041354040c402e64011841c0075000c40b006042c180c2d06004011502102000080089000b001203500703900e440d44000d0b6a560b0740d0b1011400580c420069480041c0b2400040b406419460080e504002c8009010b010024180002203000303400869013a1441c038940640043c0d03075800e102c4003001070200343c1e5400702251300005001c03070004903000300540a0340c040c0f020445000b1042c00c1200e04140d040342c8801c202c041506040f80034028505201940b08400824045800407141ea9004801400d440355181d802280c2c6404e0120b0148801c06810000c04000000c2d45151440d1a154861000c0200280094980038203148503003000c0001c80d1040e5450081c82911070007040b840030203011040007400380d41740c203960f0315807640915030384211940c060740710a1b807 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 141314550 1250 141313300 141313303
    0x6040f030c08040b0c01180b1902040306050108010b10020309060d0e0c0a0611010b0a1404270606030b280b0a09111e03010b191214010905180a060b03 66
    0x120307003a0400d90058840361601d099150135405981c4861040d03103041c1c14202e0005240c1401421103421403160030907a5217825109084108a40c066541c1e241d08000110002d501482424060911140006100b0000700c05024001e4003c00200096600510942c1000d0b46c07200200c0310810000740c004159046000e0000f8601401ca41d400d90f03100500f800042005503100c00c0212a59002c00028031204004900b441a13680480c041c0b141c01010b1408104490304103a0031881103107455440019050541803440c0404a030400300480d03000740c5844d001c01c14004c10600854114200001088000c1407441142040c0c0c04038400c0603801d50b49900410341c150f994404641c000b041c1c500810b01c8541d4408004030469030124500081e00c15107002c944501070460b20640341030344d1102008030315000c0c0d100d41300d0b2843e00340007009038108403a1001120880000b4019078031004415854005c82d075050681e0442a1100104100500d046028031039080200014450903030030b412100001c0d80c01d011b140400d = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 141315800 1250 141314550 141314567
    0x6010f1d06063006010e0a0e0a0b0a03051207050d03020f03151504030602090a09020c0618011509140f06010504031403090a080f06010e04020901060f021c020106090501080a030206040f03 82
    0x40002140d076000481810f501d208269220b60400da0341e015024442a04200c81515940150494142c481001036000c00b01913005041c0d04100501d900001641c3e40d840c40d1504000d628050341c848400301d559010050100009104032589080660900d00d0341035049140c0d0000800943c99001a02401c01e800d0725521400851034060b090030580e11742c0c0303900b0000085d6104142150048051000c0024800400d1007650907880002000e015240c07075468001140e02c484892108103550380e59843c3d68596008080c040081c06010008a106040a0803050406400510100d040300340c64040088507a40710003101d0580303500020f00c0d40c00c02013090650785540281040160800146a004106840009041030711844520300320303109aa2a0310314640b0903482914000d4022513207100520100d8003819a07001100c8003481158001c200f07030a80341c2c071a4500c0d000e4040c0941d5442c1818417003218a0f0081902600204004201c0403005940003903548400a0000d8a10700031a0410020140b203584035 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 141317050 1250 141315800 141315847
    0xf04060e010c20150d0b0102070b03040c06050d0b0406120201080601140d1112040c0807140a03081b06150102190c1406040b0a260907060e01030906020301030506010f1d0606 76
    0xd5160001d5000c0b61700241034004074540984589400025040c1005003203a100f594019901568103160080c240c0d550313005811901c240c1901c0e024440c1c059100c510401000700880507000c031201c52035000140000c00098201810003901d030440c2104484e00c61308a58000c206049d0009804009140070180e1380100d107428004140b82805010a004a4161100940d0f04490680d203000355585081450b00303600c5000c0c0d070303008184050300f04045820400505441d051611401844004403001e460800b803089484190046038000c0001d00355078100840000815001c0d01c40343c1c040010349170f0b44030b02d507981e00c03480c600b0a140a0003040f0a44a42090301d000f440c00484d0f480d02c40000b2600039021100d0083d1034211800d4884400c0748881c40080b5050040700c80d4006420310908021040b2001d444c1010100c0c181615800c00900185440c4000e600840c040c2014000550409070040c0b200c03900c582c8440ba140300108068190048244181d0340c015804490860703450ba0400c2085a00f40f00c0340c42d4 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 141318300 1250 141317050 141317089
    0x1c05060408040e07020d2a0b040b090c010201090f020609011e02060901110306180702070b040e010302040c05190305060a1805070801090c020c04090807080f04060e010c20 75
    0x510007001404000750060780c41030f0040214075501c0d00012650340ba114100c64000a640e0b0110700c0400b107448191400800c140c8080e103400014685600410400640d01110503100c0442080300e03007d810b10103001101c07400d1009110402c01922406114922400084d10820000402c0d01c1280c0c0965940120348440c0c1c4480c0c1c1240e2030f800806512480101c90103a60b550a20580324a0315102074122441100010445088500184101655200b000b41400250b100b45400804c5c0700340c8004c050002000c8108800744158107610500c070a4900c0420305800740314040c420001030042c8081e46203050015407400140700d64813000003a00848044d40310480315070380c1e0840824a400c15401c05440f070a141c0d02c890101c0d0f40c1c0e518928044801d68000000160002040301d0040d15150300b140400c41c2c0510781640c1008507e85540781c0369407282c0c40079080080300150811038103801c1009018000d60900341601c0e0503e940e00d448405071503580410070000400f880c00005903550b0003003000c01026044 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 141319550 1250 141318300 141318313
    0x303050c0312010605130f030803010303080414030d020405030c090f0424050412080f09070612020405131b0c0506010306020a11060a05062412040f060c0806090112030e1c05 76
    0x202404503408951004420106d0100100711840c0c448905002c40350320450051071070786191011540804041d004580140c5e903214a806114030400280c016500c1c24200140d51368030f0203042624000c0c001d5011401205a0400c000c030400d0b80340d06060380076801424005040750490f01060740070101d0300c0b00c040714074501010301091101080d40b0208076061504c8075000c1da01e4492104400710030445600d86190b000300001c0c06100c0c400d244045841c0c95101c80542416261800152402c11051b0615002c541d10307400c0c51269407205000c1510007030716041030911404140c99883d12030b0414040030b44001d4001039000007131489020224220940c54058501c80d040218000b0040c2100f580ca042c403400103800a80340e4204007658145040014008951410442c0805840400780c000c0c826106100000010000f0414034000d018040d0709696507071f42e81c2e14003a801c102d61510181c101c2210390308415440c8000a800038a6007800d510b048580c28407400d40100c081c4420410000c0c0144540501d4 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 141320800 1250 141319550 141319559
    0x3050703090b1c05150907200f060f0105090c070201030207080d180c14011e0e0904060b04110901020a1128030506090c0117250c03180f0303050c031201 67
    0x60140800310f001e40d40c401d1146031510380c041c0000c60520130100341c4c0f00c1c0c51180428403840c050007540100c00c8400c06d0820619100540d010300345000540c3c5089a07420550070418010041035640c0d01400040300c4400c918101907220750fa540c09800402414954005154002e03c10703500c06548446600302c10038000301d80040752074201c960000074212400c0c50300c0007012078140f0410540c0060b415040e5180c0c982011130b070890070070b82c6841031600820301c0005a00c009060700e410b00c649126034003880c008140840c100c0c2c00d0000b1205008030070055500d06001c0c0b04241c1e0390102da588c0c401c42e0032400e95829000402d00040c40c182d0062103e82c4506400340e00c084110400c000a801141e00603819a00c0e41c0e82c54403811601d40a0300d2241600091841902183c1110001c0c10184c00c2500c4031078400203100300d00180703035507860001c881c00c3c0071401d211081010141c1c0b0820028501040240d4a500c0b18980500340b40c8500060000805002c00440d40703040031740c802c0013600c43c1c1c4d80b807988003c015540e5a = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 141322050 1250 141320800 141320827
    0x61418090a0f0c08070e0607110d030203031e04020108010311010e041a030c04060f030b0714161217010b07081303080a08100b070204090501020903150a0e0f0a03050703090b 76
    0x40d500040003580c145405180f4190142c20854421401d0381c8a0700707201007180b8100a0076621a003000c440b21000040314501075101c1144441d00c052298005596906000309140409241c00c551304003c038035400e0070400140da00c108610304413580040000c5010784d51100590750304000352040d603006071801b03030090b4184140380130080c0085000d8050314580c0342000207000940307020740135261200d28900020000650300d00003a80d84242c1a02d0107101a45120b1400d6a0542c8006000e181c5d01c2c5112000000340400074651446004a90808c142410b1024800500c00c2505128440002c1d0010170144240255030b0100c45604030104004000340c0c2c2c0300c0c81c0c0070b02290484802c100000b4030510003c4c00007403182d186c02c01680e100d001802d04242035682000b000d01030b03002c0125210b54003802400041d440801c40c081d4219940d00002c0e2440c50f02804e410120361114000d626590300501a90306000c80100da491410ba4152800d1961a100360600b51140107407035010b00e080b0040000c15a41d5040f4 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 141323300 1250 141322050 141322061
    0x30702010327052103130f1a01120201030e011515050f0c060f0c07080409090309030212060403020d020c010806060906040b0c060405071205031b0f030d1a0109061418090a 75
    0x2904030700e134480614840c0030103260108031a00c0075900d000c03041a6010801c00e951494801d4820b07440f95040d80c0119243e480c0c0c0103020b80c0710391080c1040410031821580c01d406504d101070703401c1008001c02021455001d0b004141da204070a440b80c2001c580c0b114580c402c0007100d0b034400e030302d40016a403070502c00807250756044100c1707241045d01c440d40049a00c208103207040380c9055400881482c14a401c2640e003200a0405c500114140705d0035070f40000068a484440390034400303512002c4c044501e080c4c18040d08203c1103028090031504180340d044c9050703811000c40c3c0e0b080341c03064a041e0303143d0b804070340410064800c607081543d100b400071611b40c8003c840003d030039205511a101741c4d0344041e9224211040c0c01518000105030307800c00d10103400c6203132500c11056030940c0d6000c12101400c032a071501906680c4010a4070b80700da80c88290b00c240180e0112030600d6400401c1c84c00109180c5015002030480d0701d60389002620550015010150f03189460ba0352164141c001c1c11040c040c1022500701000f0b00 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 141324550 1250 141323300 141323323
    0x1902071104050108030c0604060e0106150503160806031b060c01052521050907090e0a030305010506040503070b0c0f0714031b010504060c05070b030a05060307080a020303070201032705 81
    0x6042c0800814501c00120a950b8200d0300300e00102400c0e02c42d940d4200c00f078442c907020703018207640c0d64100141c1500100e21801d2044401d848059890401d25440410044004032200c10304c808502030091341e445c0010b83d0154440c2003603410800b04444400908a40b054a41c40d03401036007000280000c044400200071590520041c01d100001c0e2148402c1d50601c610302144452021030580303078180100319030841c5a02c007180c1419200c1441d103132500581198810228007070142d00094607007080541610549015150407100c0a08140c540782c0060780d15030440c010094641e4000ca65080d002900300312a9000c0308240e42501c81c0683c41d420081c00217101c1c240c00034480e00c1490a075a8800b0380142000031621010703940c0758901400d01b007050310710405c0c4400403902413052034030000d00310395800040c43c02118064004116030400404140c03400c8a00d8100e10f146d50004400000103a40000071100d07216420300300410b904a503520180c090146481c14603208080041c50752003000b0b80400d4003103125 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 141325800 1250 141324550 141324559
    0x1e0409090b07110606030601090504020117040303020415050f03041101090e0702010b011403060f0910080601180606080709030b0a0b041d010c020a0b0a090516030c03020103050f0601051219020711 86
    0x405400103d03580ea1441541c41c1340d0503401c45001480394150303d40105503c240181404110011485102d0300805000c581c1940000d078042014400e400d030a0f1840c80700f00312503203004c17820111460706c5800503100c00303403006000303a00720b9840d054240d0040c01140d0042007007096412061170801d2010307010b000700301445400100e0345151200c040c43d00d403080c3c074010ba03001742080d8640400441840480c03c8040d01680080700b0f800800920036200b0000c07140603100b00580b1003400b514440d030b88026144650440030500c81704000f00407c090f40070407104101c0790031910401850701c0383c0c09090024541401d03107a81050400c44110500320181100b41101e2261000802000b940d2000c01ca880780070300b510003000d4921490102e4103e2005802000a240c02003094802d2012801492a8030030701c5031340308a810880b840010029584c051003007580c404217002070fa42582c6001000244544220001d03403181b00786510108030900c3c0c81c1540c3c5000801d0307090003156a440c1d00d00303050556001080c0c8407840b4 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 141327050 1250 141325800 141325817
    0x303030b0103180f02101404030303060302030607020f150a0b040c020309122e1b0909150b04060c21050c0c0d03020309090a0b0a0e041e081e0409090b07 67
    0x58a01c0c0403140383d402034004007484c04c014a141d00700011a80d46007402c000300501e00d07400c3c40e400c49031000104021440b94400180c1d0382d1035407050504041c401000c44c000d43d0441c06061901450112b02c12400503240700c212030160b40d9880c4c060000b0802d0504c5a03402c14940642101050780000007040c048000319180000680c4c01440150b40d03040808403183d440000883d11601200f0860902c00060b00d950030104100600384161000072110b180c91800245030034804101e5030b10180303e0744075151004507440c8040b5051111554070f602c82d9118030410414074000f00e10074008800c59100544440c402642413845c0342880040140d0001407281e0300d14011810709a28515028101240065040e00510308140b844010000c62410003018118071580358a1400e0075a5540400100036260b070b140c0c2d103042414541010380340780e50b1411420f084614000b40038408150028140c5114400040790a49514290b084000f181e014590002031210b05180f100f00c00c002580c003c05210344c1c0d9580d6032050 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 141328300 1250 141327050 141327071
    0x230316120b0f060a030204030501020c0102071703070c12020f060a020301081603021311070b0c030f0708060a03021003020c010608030a020f1203190b090709090501050609031005060f0a0303030b0103 87
    0xc4480d4016540d62054861010302e0140c10540054140a13005050060400c0d0741c0b6140d444c2a80d1080c1040542c1e654001201c00400c941030394542c0d04c450100d20403605625100c5d0000d0300720344403080080c00d01188224120711141c42004200d4016a0140594620703080010a0034041d40080c0103040c82402940020101d184e00d101034201100d400400c042c00c04240480440c008008020324051b45601c204005004501c002035030900135800d1448481e500d140c070701c076055a000c401400d071100708900d4005229190b84c0c5c120f10b8005994044401d00070041754520150001c3c8517526002410354200480022650300c0400940148242d580941c0e40c186050420b07507443e09081420340e03028941c00d0012a903412060015480d40c40e01c001800103410400100042c00540c0c215001c80000d990b8043c24030078000d00e0700810f03004100c00d5a400703042029110009456004045a03501e0682c0e6400000d00182d80c0d40c2040703075000d00c003e016000740d02d8507402c0040203408606005030200b424130000300d4 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 141329550 1250 141328300 141328337
    0xf230705010201140f2509030b0121112701090c05040605030c0a02011e05181902010e0a030803010608090105060f0a0e1e1005010e090c0901230316 65
    0x40040038180343d150f007942d442120184154010703195003d44040322001181c4101b50703c01e0086d844a864486000355441c1d07107040341248a0503000306000f05a80031041d0081c50200705400d07030050348100c826003000d004201103817039454184255401e05d00b000d0781c41070b1180a03226259041e0303064034000703024100d03011005036085e100e140f00d420002203007003000445000718080034010304d0b043ca200119403002c455202400c420032114010011a5607201806104503071182c00d020501c0c50b4001030300c0d0096035111280b14408002e10080d041c0404080310216950340c00e5811400b0f5a48104001c1c0c603541c480c5c82c0104292012a1034403031640c40c200100f0301d0761034000d9840845a10003888485a00d0a1442201e03c01d000904110f00329804000008403403400c00e2030381485000031042c3c1c8003000345000001003408903031542040c0168020000e01084503d400115025410203003080088242c000384004e080700f4501203807284140003c420300400c1c040301d241d0840b0008040d5280c800100b080b00612 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 141330800 1250 141329550 141329561
    0x40609030201080f0402180c040b040b0307120b010f0c0c0f120201090e16300e010f02090d140a06091101030b031f0c0513121a0c04030201030203040f230705010201 72
    0x41d40c801000c1c403041e40605401c171541f5611602c2c1600c0b880c20141d171005c1880342c941043d0414560110003100300030302198880036406040307070840001d1144911080000e04180b040f001c58400704001090904140007050b002a0000d108076215134002c65038425140c43d01c00b40c0d4913022030015104210000d001040030149a000341d41460310030040d061030034401ea1f901880980b04140c9510010305002507007003008601a0200f180c644007080c81842044a41c2c00c480b41d1082e10010580306004c4480c2980340d40381c00c0542154450a412021803002c80079a190006d5900c006064074200b000701401c200e180341c0c4a0465200a0301c052141541c0041056120465814000325020700c000c0701707000b200390541020001203540d0602038600a0580c4c0a500368407055042940104046110381e401c101100505900d020f80340c0d0034015540c03e02110010f540d102d2480040d04147d004030102c1e00780200c1e4917120380540d82c4540110152403d00242d003e4454001031320310042d010345040000c0550060148 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 141332050 1250 141330800 141330803
    0x110a0305040504020d0b09041401050115050d0f06030b010b0d05070503040305220b0a020604050d0903020a140402091c0203101a0904080702040507020312060301021204060c030908040609030201080f04 88
    0x4035401d041c2001c082c00300a400c03a800402c00580c64028101c401d46410011502450180052011500303007620f00c64251101a0301c40c0c002c840c2c1400e20481f00507072060a0f55800300154002181034071a001d02e000292019800c0545200b5400c1d00000da4a00d0607001400c03910034000c0e040c0106c2d90780d100151040d020444024021500c10070803100241c5074500148402c0d40170750885034185032101e5140c1040d8004a2405000d07901c00d909100501c101040036040e046020f20382284114156401f00380c0000d07403072250340d41510342122050700381c0d5a1a01038800b1254040d14401c0c52200c0751500f101e21a80c0d103401640280a10340311040010790f28001e103105c2a541e9030120403010302c104280041e07410010400c1e6407030802806a00c00680d030302d0103441e001e000b640c1e0042d82c4404500440c07480607100540a03900c6a0700c10005101d01003a02c1c102264090b4211030005800c1d22584001d1300502605440106103017800540420444d0f00b010301c000c02d6034003c0e41c80b0300301641c0b412030411801780d003500c0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 141333300 1250 141332050 141332057
    0x20010804030e03010f110901031803020c060c07080d0906080603060106140c0f030a05030609010b0705100506120706050a02070b0c0c0d0201110106081b030a0c05210a05010903110a03 80
    0x10301090040b40c1d50100030703201400000f40f4000c0246240100c5122410801a221340000c429000350703898060140c50804181d00300c1110f58466802964410b5000070303081c050440071070702c0300f2240024810b8038000c0c84070354160740c0c0500070680c000306203050501038000800d0501003c41c0e0303141000a01c0301d040e50196290602c020100141c1000c841d00039026441080c410140b09100c1001c00f8409082c4429558541135107a0402d036040164180f03058010980241c000e101d06030119100055050654940442c0010f0355140c04010800351461401e22040a1280300ca0000700ca96111000b854103036000ea0958010030340351802c68440e441007404a5500e54084003107aa228900b01c0c1400554910504040c02415500c11a65095a200c0d92001e10150410701e0441c01108001c50784030b0414008074060000c420980e61039403409003950150700c0c010070343c41c41e4a2900c40e003a600b1101c588038100e01122204409450524040d102d9601c3c2140021303100160303e10810300006140c0303542c681c07644 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 141334550 1250 141333300 141333317
    0x80601020a08091504030c0f05060307050f031503160305061602100c1808070302010201140906070305090f0f1e0304050d060b010509060403060902030f03030106090b030910050903072001 82
    0x1110000643c1102c020941c0c803040c81d00c0d1200c0381c610310a0060008521440b0301002991805c2e90b942e00c49481d40c0d010301c0c0529400c00400602035404403c80e107070781946c0320f00645c0300d403550403031040e02c1c1c1c0f044181c10703400d0b2081e0810030300305001c521404002c1701d104008903070517951207032100429122840344000140c2e0100d50410101d14454000710b0410580d45460032070465000c0c0c000b00040010340c0001c603580c0100b40c06009559080c0116280c8d240100b021100c00d04041080716a9108000e180504040c1d071000030560401c0b0a011540b0350b40390010403902d00c014039035400d036120f05550105407801e00083c48034841d041000f2080c3c90840fa0018810b0f41112441e0710b5a20191808881980c10000c1c1009241995034405002d04065030180000080504d101d105041c6407411002e01e000060744207000400155030301c18104400e403010070f41c46c141c1300e442d801d010703602e01640301c0910701e001801c2404210810f080000075008860042c00424000446081c0d40d441860000030128001909407 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 141335800 1250 141334550 141334553
    0x30c120504110409080a0f081005060a0201060b031006172a0702040603111903080405040c031401060215010b1c111207050a09050406181d0609030d0c080601020a 71
    0x540c0a140d00c41e001d5a1801001508100007508580e0010411170700c00802080f81c186059002c8000d490041c42410003106030705169080d084642c00610405106200000303104907414800c1d04098028101810616181c1c18182d604500d0b90340c1900900000440c404681070010007060b000600449074030f4072004a411540f40c15503c02e00c038000450048070303c10003401c0d0050b1954420580118050035400760354100342010400f80c40d1f0804425906c0388105038084c07010822500848089940440700010300040409042d005440c41400f0a405d403a000400058425004107506100e210100f01001d100da889010075030300342c003c1008194500081507100d68005086a00c482e01c05a8840411814880c1030103038001051002c03a1610006580401c0e852011908190b5203000303450100c5080c48503d04212810400c0940705450f00409501d560b0010307400e10107501032400a541f210140c80031840c141005a0381c0b64001c3e00c5103404146031503410346195114510b000c1c015807059002e00301e0180d09 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 141337050 1250 141335800 141335837
    0xa02251a042607030f060501090e01020a020c1201060315050921040905070c05031b0601090614060f0c191101050a0206041b080f0106150f0f120b040f0f050601030c 72
    0x1c2c00715607110340c0c903001c0b000c503030304c030341c48800881c0304c1d01011403203604044621054901150b100d064a07030041c000c00001c01e030080350710342040d4800d41d141020918001d00d40e502400c0507501c05040b80c21070703100f202c4480e04030341c000074404c40080302210074000c0082141580d03404200f02e14008090240003d0010f181d15801503030b0800c0c0c0a1801000c07110083d207a450030345d804007000301070fa0481590205004441800628010300c03c0038000c0008915142c4903021423115003462034414040001e1034012002ca038010750f521083e144085440c482c0c003044054030790013440b8009a48400c410841c0b160390350300c502c0807248030030340d107030f002d407440b5115642d4040d0a0340f83c08009c084401104580030a0f1902c04000d0502054078030380001c200249441000d202c00100c4102003070170040140d1a1451158100c107443e05540024a0506448a0106410001003500480c41c0340d02c1030500402c100744210581220400290411003042962074860054081311080045034002c0b03144818010f1b800c061 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 141338300 1250 141337050 141337109
    0xb0c030402010c12020a0b0c030603150c0c1603030e060313120c0510150b0301061e050d050c09011706030d0e0d05010e1516140a02251a04 61
    0x70605242c42000f0181d90360303600e10300c00906030740d005078407190112061141209640d40c00c03001206180e0b185081050110303444800c5c0d0b011540364502c003034000c50800c41401c400c45842e1080c00c81654100780e81c00030f0f244408001c9100a900140011054114518140086900601889145038100c9010b60b07240c655984585504000b40580702220b80c0c04120b091110951525503807000283c400002d961209500109402400c40103d06000500c0580d0304101980045144020100d110364160300080361140304aa480415403410041407000c8155640d02900441c2000d0700d47e500d0b500303403142000c00c0c4075208958582d491343c44803d603114258041c801d4041c40001c098422240e41c0c801b501c031542525043c254131861030b8450305e07600d02c110348900c03007d50b0810401c10b5040c1071100340d40b0004112104a5110040784840040c8820f4018000c0100140010201501303003000e500030048241101d002d8400c40a800d0301050b081c540da00d0007441101c00b80c0d8021940c0c0d25040c600601400c20005 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 141339550 1250 141338300 141338303
    0x60901270201021e010b011106100e10090e0304090b04020a0207062703050d030b01050a080613090b0a0b040f06081020041509060305090604060c030f020f04030506010608040b0c0304 80
    0x900360f1100b001c480d0a80c0c45152030884d4100110f000c000c182c000500003902241c0103250750b0030072400d1103420308409184000301d4414404100964507016004880040140c1c0512225485c142a50f100350b0fa0210282c021502d000341c003007058a030440d0038401640f041250031001601700810620010780100805115040104040008640c086000d00d28006a6410030f455903030007281916545d0b44c0c180200e40c4031101c286031080c140304000d10090304650f00a010340c3d206840300d0303c03410011030b52644581603080d080307030300c4550720709020395203030010810a100d840c0a5030a2110f0314a440c001801203c04480c8044001e1030f22804103580c26000300500050750300c0c601c0403143c0018105070b50300050b201034040344851603510606100302411070761055100c0424141004108802c8480208000e0744c41a00074101150540e8040c00482c010040719010381036075440031880c1400412030601030801d407807241045031520b036203818042e03408580488004100c800104001101403109802030760b00607 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 141340800 1250 141339550 141339553
    0x30f06050c040906060806090a09080703030c050702090a240b09060903010f05160905030d05030c0a030905010c02070314070506090d15050a02032409070309110a03120206090127020102 81
    0x140d118903420f01a600c0a91104001031900b10074050203260811170b5a0f0408010401006000c845030744404890241c0d0b01c001e014141d42d085c040c541c090045044039003143c0e00030b1040030b0034030303085070100000d01c41e10100441e9006413003200002040300c04e0804017507038000064141003514190810403281d000341081501552100071000c401c03031083c05124000c00c0070b10801c0e014040382010040c0300301c5056011620a911082284030070340d8000007165040600d030441c181e5548101d400c01d0740a000888030060440d8030349070512002c00c0c3e0101d80c4c00192840380d100e02600c2503403951410f680e94440e005150303000000300403401c0f25150840c104141103110f8070481f840030300c4280c1008201c44045504c000819000420041c40c964104204085441503a82140c282604080410955400244a102807507510801a4180a2201c07805690244014003900700c2903224030b4203006010500c0721107000f40c400c840c08118411018040c82104c44405220b02d280c041d200c83c4c08100030041c0260a030b056 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 141342050 1250 141340800 141340807
    0x50702040203040b070f0c1a0a0207020910141f050304050f0f0604060c050c070302040203060d0203010516030507080702031606060918290a020d111b070f030f06050c 73
    0x1a00d490000d14441c500580c200c007000d18050360054a006c210003180010403011088400004c1d004807548924003da008201c180303992140c0700f1500030b00c01d07258060740c0220480304000c1d0b00003203101f805065845044195403150407910a100c5900801c51481e110030525403440d44103948140080c1d80d019024400722001d030080310308410300b009100300150400742c0224082106100440c05000141c61803860880e29103038010314250348484042c000248030710340010101d8425916000d45030070180c0c0042c020012420509032411101203150f00760b10101e0304100014035068002c0860320301c80d5020b40c02840c606030700c1e1810314084c1c15180c0001c88403076541b080c0102d44500300348608651a42c002103e013103c400f460914091082107000e05c2d03083d12804d0000e030f201079458190003030781044502d140542c503110758820b12400751640780c1540300b0704130b0086100c9003001c80b000418001d2004a20079642c55603210400c83e4800340320303404041c011940420244001400c6607100580c8030749424806800e = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 141343300 1250 141342050 141342053
    0x121c1103040e040f1514070503011d15030d0513090501030b0f0a18050307060f060b0405010c0c0e0f040b01060e0d0b060d0b0a020a03050105032d07030b0a0207050f0d09150507 77
    0x184000380020a1741036943d6081d4148015422041680041f000d0800d02e056603d4840001249100e03880081e46d0f1505105c0401c030005401c0c807110202c040c00900342d58105c00d139090010700c980c11041e040c0f922400300e40390000300110b03180310722410703640c1201102540d580c554a04000340200606081c25482d510340c03030740c41d04098001c1c1070b1008a01c0340020b56980c0131142000750541c2d60b0319200081e064078140d0b0801900306602c08581c1204c40070b013025803104485081c01c0402c1c50b855401414010402c60400c03a0790400c040c45588070721700c00c2080320a00c0e6240c000848041e01d5032140c030760700712a000c190200401c0c1c3d0509600d510600003443c1040d40c5685a4402e41d80e8071081c2da0101e90389401089040d11282c16014160160400360004c100c00d20b05141410006c0800891b1104220748808007113442180600250340074540141c03002150b41060f028100083d1b00c00003055a160080e003040c00700c54040418284000c100030f55a03400300b01d040c984041c0b04000c4e942d01039021302608010200 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 141344550 1250 141343300 141343313
    0xb0708070c12090e0609070e0f2d031203040c05010302031801090b0a2a0320041404051608180a0f0605070f09060f031a121c1103040e040f 61
    0xd210b1426a41c0b51103951038810030f0000c408026190034400d030361038001c00c03083d01e43c0080c5103448428101d950300e103a141085d0100380580d1076034420001107900040455500701001002c0441d030203041e001c440c002180071b0344c0100b041c0010342c2d0081041e8100c500801566100c1c2d00a56002160402d690f808006840d5105e03003154a030304411a6040d50389001c01200c08010301c034581c0d604204c5c02c003840b600c0049020105240d003c4104400034556600ca080c2c09000c4d20f1480100700b800442081e41e80e45441c0c2c0b030425120b0b5403c442161056091a0004089c0c0f56048060301d0240710944909004d81c50344000c090b0f0241655494400c180b080002c3d107070124440c0c0c0700100a050180c040000d44d42803070701d4020300014180e40c0c020244107030150108501a401030f2003200d008094600050000407014585074201d0020440076072220b50800d59500070480400c00f9070100c0c0c080581d102a2a04070074040d80d00036615500000f076600103100810110070074554965000b03210f100400c5894178603503504c0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 141345800 1250 141344550 141344573
    0x5091e22050907030305160804051801150504050303030601111f020706050a020903060408070309032406051e060903030906070b090c0105070c090b0315190b0a030b0708070c 76
    0x10140c89054100000d02003918450207400c0080d00010f8492503056031005030440c4106110b10108140880c0203d06102410003a40c0103440014400d20100b03050180e0011007180038000c1a000c0cbc010140c102070a0350083c012141180e401501641c2144d58040040d03e8404028105c000300703015203071050540c03c00c038020881100500440050f110003603030600f2011660b000740700d0307001039204005640a5507000a030055210350301c0300c0b0a658500b5030349001c40381a5580d500050060141c6800ca0540d045442c001e401c0002002000b08041030b514002c0260a000c24144a4464000790030103c0050074060002c220701c0d05c1c0039080b0b9107031182c1440455615400500140d070701c19101824800e00c3c40090050394100e107000d203443c90070812b9070380395000c08802ca40300d1000c3c0d1654070301182c11551003c0c00f05182e8511600c010741124905040040418029100500041c5140860201140c03605074141320030307070307401c810280043d0f42d40b9001a6140710700540000b0510418004960029800c4601d0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 141347050 1250 141345800 141345829
    0xc03020403060b0a030b060603090703080304030f030f06210501110d0903181409060103090611040510081e07110313031e021e06070203030310050f030a0305091e 71
    0x580e00e500c1d60808004640c50205004c0c41051501ca082000c43e018584140e0401c1003120301c2c980c2e036191301c60310b64034000307490340300528410001c000c02003815040781200c00d42126030b48060240080d0703200d00c0c0c0304913440c42c000c0321103121217140014181401003110582c071511034800050031018400002205402030301c0880c10403511000410101a440900010120316841841052504044c006403d129018141c0c502615640001400c1a84a50818600c1640044d020404880d60707200c100c460764014010a4083d00c45221015102841000003601c241c0895800111040c1c5554203014421009400e5104014102c042622251070900051510200841d100c2101600d503282000e950490900aa589102d00c0755072240540c459503600381c8272140b501d90009002071890005441c1d0300643c00b01942612000c010003011005410010b010b844d408c99001e1313450360b41d404c00c0542c1e0f00019400200022024428651750341030840d68480400a07241103680810441e401080304001c04410 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 141348300 1250 141347050 141347057
    0x2011401120501140709150302090d1a090d120b03120d0c02191511040f080a06050606090105160f06020a021b01030b0a050621070207080d0206040209011202010309060c 74
    0x22075040110074410290000c03451080004140b60510700a0841021407041d8601131111000e40a1014840d60444600d01c40007000788040080c1400c040005441d00388180d180c00c404c103400300f0008000014102001c50f41c1d59220648007000381c10810241c16420075594040c072a070f480f551082034402b0042d00c0b0301503818a00041e4800a100002d25103400500c038102c80c207010012100114104042c01c003403a40540c0404219100480c50300300ca54459580158116609800081024000880c461340124019007090200352a0304080009510850b0025030100d0010412035181200c0d044001301c882e0302510200955a13204c0d1a01020382c2d0110f1005401a0444040c00c6072080c000742c24170402480030b20b4104860150301c1e02240d0090441d000f098800c0b05d0104400d0a4155125030414410440a101140c0c50400000296a40f000783c003e4003070a0040c1c811840010340b000403114883e0390018116002ea034130b81700385d1103400541d002c0c00b03030704150304c4542d20000308110340079009803003c1559 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 141349550 1250 141348300 141348329
    0x415080610090b0f060705100203091005220f060207050613050f060f0109020c0a020a060203090330031807060f1101020327070807060c06050c1c020a02011401 70
    0x1112034002080c90b0031202d2524644501c00540761551116120b810f24259500c60b941c8600d0304040e80f4000144139a182524000020404000008560001040c20811061004ae00d8014503da45202d55007a901c00b0842100c40081c08100d90075201c00c80940a050010b140145a0720703802d0400c4000c0718080c00802485004100304602000b1081c0c9482c000c80261035542081d400340c6400302c1040c481c40308078540100c3d1107543c81405200d00100c40780e00030014540d0030303514500a0f441e50010301480344680659a50803104d1090300c0c4003103d06030a12121020030000c0000701004c1908041c0c0500651200345050202e81c04040000c1c2000d06680c0e1036014418948005c0200080d40030101400740c0c0c1d005209124400b40452200c0100f808040505410f0f035a4002019140c0041680043c0c001e1041c1c5d580080c503d0382100301c002c0303050b0140708140200d43e16072a40c0240c0348030b0f81030118840101503c050101c0125940506802000d520012603100030700c1c1e40c103448468003038001e00d40c10f00603003 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 141350800 1250 141349550 141349561
    0x1d0c04230718081902061b060118050601110309060a0504030b090606030d020d170417030a0f0f0c050d05060f030d08011d090607050a0201060b0a11162304150806 71
    0x614410009200d0074004021035a58030301c1204c52101c20301c01c001d0240390b01003040c42041e41003c2403540030000c524210340c00c40d0303980c42000c0108d490442c541041c0074a09808a1001c3d4480c0c500f0140c01e12142004520303120701c0c513041c0202ca90000108004220040c40044000384407001014000c210060040c40030341040000c040c103104040c2c00ea04250351000b201500100e800500d03520030300569406800083d0b03600d0030601a40c1816189100040c580002040690f00040e8014200354030300074800c100c5140d2aa08000072250640c3c449030101e4018000e82c484008250130891780310700d018050007001c2010201092034a90801000750218100100602561512281650100c40044640100c90600c480c3c0103440b150b018294038100306000034212640350007500214014034005080300d5403071007481001004100200b507402054018a403941c43c904102407038060a84d4800c1c0340d035110499008042092000c80545500d800c0b5440300040f40e0010048003491004100c100c000c1e002d540f408 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 141352050 1250 141350800 141350837
    0x7050304031206050a120507300204020c0f07030303060605040f09020a033c0b060301030b13020303070b04020f040501060203090103090c03050105090c1203030702030702151201181d0c042307 84
    0x280c10040c482c2610100349c4004640041c0f44841d8880c012029940081d280c1c00450003906c13844a49a0052040384240b100c0c4000002d03030507085a010360740800c0116141d4500f101c451045101c3e440e410240030b042485041950b60003070050070300b42e04001500c1240904d44190742a260290200c1c091192100030403076203100c1e00c1405400001c440100450b048a8000884c10300040c000900074940c03c0d8000781d88444520402081d458004081703940ba0006403074460a000340865040340a0190b2001c160344d541402d000ea02d05894480d00a94142200340d001140100020300c002d0721091b03070b4105c0000c0890420311400703004a503040040c003a68003005007400076191900400003255401001001405940030095460b4203030b0482c2c005c061401c4500f01c0c0d20300c602030312004840c58507915000266000d10b40310b4640c040245003005110031440f8007034034076104d015141c41e8440e68005041004044c030746680701c000a595806490110303030401c14996401201e04440c1719021811075410041b00031130 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 141353300 1250 141352050 141352063
    0x19030c171015030b13200f041d2707050a0b04061806080a09140105070c0b1005150901171005031501060219020301020c030c0c041407050304031206050a1205 69
    0x18504060000f001c04d50045540070f42d140300008006070341e510b08507200715051556080c4200d0740301c0b400b03611b9008001d1017440301d5009200d400e2504e1100750341520122040c1c223002d84250700784d0400b0b01031003501700c21103003a12084000003c541d003d00c01000c2826910440000c024208038074140741c07a6803d090001e00b90b82d1140004150035100726204101890780b11101c070341e101c07950200120308101c0c0345c90f000d141d5900031402c11703507107500300300804c01041c0e84040c0098440d80251200c0c115071312401d000c00c00981d800c8c060503400c81c0345403030300e500d005100308018211890103241c420502151906928444031042e19021595240d82d40208414601085005500c0c11380e900d02c05025450040069580c4100d0030030207180c0743d1600048002c1d95000c1d07059803010385488003540e81e030341c5070114241e07155059035440d648628544440c44c003910003c0c000c9140302e52159228240707141c0721920300741c0e50710f40851600d02145850344c80c04100b64030f032014000010400c0000342180c403600340c640344c2d08046 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 141354550 1250 141353300 141353339
    0x9040b01020a0f080d09120201050601090f0b07140f03040e0103150c0f030c021006090f0e0c0607140a050a29090303010b160501021206030d02010219030c1710 70
    0x10701ca074103654085503c9030241c0e22200c3c2d00c69103041e03640c4503d10b402c1020f441802805421100d680c909983e1903601900214460030090b071721307940c0081c2c80312180780101082e070280c0c00e070f040c1c07040c01b0b41d100089001c0000070448400008a070044400c602d1090700d55480f41c0c011035480b00d0b4000040040241558660b0b1142c180910113002148402030300500042c80c0300b1288041540ba40191078109000384000c0e040d61031005d0060040984031070700000504132180c4034996603881c00030014050b48020462a1900e2001861f0034038105543e1181301c1c014040310340302d2903540160900100081c90402c090b002c0c0603c0f440c10b202c444648404103000109072028500c18118081040101c2645c0c08003c4034152006403a501751143d1200300a1f41d4001280d40005003030f0342c4001a0300d0400c508115865200d00000c4044600725496008103d0a034050030043c040c080da224020079520500940104c1000c20740380c03808240361b000300276800005030403d48122194580b060400d01208115040022001 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 141355800 1250 141354550 141354553
    0x1606150b07030f0c1407140109050307050d02090c040f12031b0203060103020108090102070606090b04060f030c050d11031f180b010506180d03051206010903020d060b030705040c0509040b0102 84
    0x7590700e450103080844000080810407811000c020200051180340c3c040951003001200c08860b11151000c145c1c100282c81c040c003280307448800250301d00d4005a60707401e40e400545901403c403450341c00d00c8090072015143c8044d6400501c07003c52100c204540c0f80c6c0c01010219401103070352140d805e0281c24030500c420046115070304550b0450141c0c8000404a04580e420720340a82907503a4a03000c18028064490010162800c04d40c0000f03564505411103891840e040b5000c02c406541c4900407481101c4900c07005015802c2d01e80f0410083c030b480060a05d40501811b0395500e88108040024103054031800c1d052a581643e021910b0901c00c144135140c15000420700d0b083e210f00030342c1c0361071008440512a007489014009460040e44c505505240d03042c030070181c50110310095929000e0059048903074101e00c80090080003668a40c420321031602100e070050417512480c126034452101034000500000d800d0311810100007016111803080c44407203203c5076a40c83e116001c4508110680b1400055141107 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 141357050 1250 141355800 141355807
    0x2040f140609151011070f031e020f13091505010602100b060d051305010e010b0105073908010b0402091005160c09020c0d020f0706050a051606150b 65
    0x1040644440e980c0c108904482d488040e99800e001c002041c103c288a0301d40080b1100209501541c0001c000352950710000240d6081c0c1d0346416030550f94003510700c00980160742c43c2540d000c7e00441c400300c8401150019042e540c40c0d600250115080040000000301515038600011007444010f2a0341406c07100d4518013484030f5490101c009660b000981c0392100c3d01c40d62410308202e9590707003800b195910842044c0038001c40c5002c80700d501c0003e04500069406500340201040424070600c154000564161142e0382440066110198000d001e41c41c0410010001002104150043d854054203000000e50203058941042113032800c0d109040075081c01640180b280c1030540d56003640c0c169207651540b400c030703498106440c600c516241c00000060725a0104510101d043c41803130300188240c1c00e016044030000c0c1d41c038000c200e03600c0a5810002499400c100028807600348074000500e4207101c1858118100b0302c4060000006506c640740846416941c3d0703203240000280801e000c00108903a80c5078608 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 141358300 1250 141357050 141357071
    0x103090503090f0f040e010207050f03070c1802070c090605100806060706020306150703030516080702060103080f0409021306020d05031003020f010306090507120b0d02130c0c050a0b010302040f 85
    0x1660b0052460072881920101240d82803a100e00341c000c01e40702402001440710900108409000b980450019101c50044040c1804464000811103d40c3d60b44400800141850003482c2e0302540110040c081c1c1e0a03408001d02400700c2c1103c01000054a46a4000604d051510041100344074001001d041801005c10801500355034607425145856000340700540c0d41e5440d080012078492007006402c0d80c0b20300104000c0e060541c540d01491250040f60702c44045900c2c07410055030001c0040350654016405580180b0000311240c0180100131010390750142440e032200803107403c1c0c0c0c000100348080d141707510b5410494543d041050001e41151410704500c2c40c2404240c00106c0800c600010b80900516140c2d150281d1081d80a080101100352041056080094004000c20301c0e04005585841c2000080c1900c1d1a114080c1d0611943c001c0c10141850004c40d07c0b6009080c1034070750700d020301c0814004800850810300c1452030b031600c80c1007503003015811441000110340040829004180ca844007200 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 141359550 1250 141358300 141358303
    0x60f0306090c03210301150e060d0b010806121b120703080d05160f21020a080a110a0c0b0405010b0303030108030a17010b09010e04060f09060f090504080a110c100509040b01030905 79
    0x1b030641e00b11680844503460020001e035046905080c4103500a2000a001d2940070803d6016800d451400d80c2c600d0640d0703e908080080c0f500700015443e84941010206d503084541d58001464030000140c40c400c1581802c05a0500300365903540240c0d0003010028103010000d620f4441c55602000c0f02c818842d0110440100400500080c040b02d800d000003004002040842c0c0d031041d080c5034100da00d06540da2500705600500045090310440e140c1424079103909000c080f003c0a0300c0744d0b03402c03a40e50300200e51441d4481c15007030040988140c50341e540e5401c160f429070b227007480118040c00307040b80256641c0c4402c6400070400d01c0c0c84501584850454001840302081384812105501c07000d2074200070f01107028000500402e0380750300c10300b40e030071a0903000103041040e0f42004c8112000d030340703040c1c4156a42708058420b4a0b002ca8000700341402c100130a0040c0c6000d00b80d140d191006040072140c070a6143c0340400c600004066800340070070000300c2c25030b002e440e242c018103000302000e10702031010f4651035440307a = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 141360800 1250 141359550 141359557
    0x2060f0103031e0908060703020405010315051309080408011d06250f02030909040c05010e01021603082a012c100c050922050606120a0203060f0306090c0321 69
    0x110001044110441480c85413400b88080c046141c152001d07418072a40c090b0003503115105c1c0f1400300b8103001c0c1c03e000884410340c4080440c0c0000d000c007500c2008500b04400103200c001d20441d201c1c0814000840c2070320b003d00c10b00c210400d0f1040c07111030540410b01c80707500e40000200030420401584204000000c00f08139000700c024254107000c00507140380802a801c50141e0400c2c103400142840c2040244000895050200c4e50207813120306030040d26100490321003403e0088016240100a0100006880100101079079114402000f0200c1044503804001120240c40910503079150994001703403420303007114a03032031910091400000742c4043d1101a11000c1154013083d40d13540d41d1008441e07290080c41210711f4103034010800c9416201c806604610b16800c2c0085020040c41c00d0006112810410b044841d40c6451310b201c000da958400305504040e604c000d04280c5c020480001508858070100022801182e020000e801c601102100345032030032025815480c0a42c6001a110200ea501e10044 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 141362050 1250 141360800 141360827
    0xa140f1e130f080a0201031503120e120c0108010b091507060501030c060903030206160201200403050c0307080304090203070903020d061a01050a051e13240302040b04050d03030608031902060f010303 87
    0x200b044240d11a41081d4003016030b00140864482b425018070311a07208202203001c104c201d036411300c11071078901e40e5984e40102c00b01c000d0101f42c4000051001c1c0600c50b01030223002c4c00050517208401180e012000054000440417145c880d1038400500400100001410181030940790106a65156840080d507c000180450441074000391407180380c640b0039002544581450000c0803010a00d400030700f142a4454803054450703000b9034081d26031914011500d0002c0f0b42c0d110300158203250520000c00001d5102804100500624410000068942205440119018001c005518814034a0303610705149030040080c100041002100103243c6c001096400080780d1a0184000045011103100540f0802d0f600c5068030600340f500181280d0180100e810b0780c0001e46100c602185580b000b54181d004600035000650800d0100380100d0a00b003034007150705402443d0120b00180d0310320002d4110307400480c04000d6811000e002060240d01081105e41000c00b007484a05650314640300101411340b038582 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 141363300 1250 141362050 141362057
    0x1306020613081b01020a120501080111040e070203091306031a071e0c0203120405010f0e10080a1506051306090302030a0201081906140112020a140f1e130f080a0201 72
    0x2160307005800403800c0100c0840f2850002c643c1c8503010717000549000307801c014618156007400c0011070000018001d0400b20009000f40e54201405c1014030212051300828046c21844180030200160703407041241c038605140e9030b40000d81c1509504107504c083c900c444d4502c0400b28500b0910003140d074001441c1074100d404040c044102052140210340032910190b01039030501c01e08000c2c20400f0139000c02403007110400d032100f91b52585e20130800d0315524003e441c900e81c0f142010318903a0032a03004207000307580040c98080c002401c1401100c602c50880064014000007000410300030003003070a080c5104003900b01420000311091455000a98070030700060000d0402c040c11021658107841920740d19160725003003a09004103a198602d40c0040710024000034001240d0781000e21403150706200f140e04641c03d5565041810380d115485013041e5100e0b50303202c4000082000744d008002180d9040c400384190744000c0700c0d44d0303001403034548040280540000420001c1150100300e0504002000820180d080c00c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 141364550 1250 141363300 141363307
    0x81503060403050a2606031903050304021912030206100b180d030c170304020901060305060907110c12100608030c030a030902040906140711010209010c0308100305010c0203130602061308 82
    0x8078112510001d12545240c140459030f0030a82c1198405c00c034a02c00d0310140d045807540484600c1032655a610f510740580880d60400104016042106100e400d4003050038088165550340d00d00c01c3c0031101d0034401500140c02100c1070011501c1c50001510081884103002401c1100e0181c2c21480c401031007081d54491030350b562400d810140240d41070318505070032403004250b9540109030100d00c0d074000c94080303100d1503004001168150080c41020702608015200603110b9076408826180d00103201d4003c1d44520071041c0504056035554002030303070031900c280513103031000007061500d0581c1d4654100500715002408200c1800c0000401d403029a041c2e4500829290f03907074000700c0d00511180c3c1000d0310850424003030020301e41c4046030950140026640e942911394606074640e00701d003d282c07003603400143d48400c0080404d1003884510f8101240410349020f10703507660b50300c40c00c40b91183e0700c0b000542c00110700900c0c2c01e50140764203001401c41d40081c04662501d81340b1047c01c0812100d00500140010 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 141365800 1250 141364550 141364567
    0x6040b10050105161e0c0602060105090714070f060f090614070804350301080606010908060a0b060d02040608010303090e071e020a0c030302070f170d0509011107031208150306040305 80
    0x40d240c1104c0580f507031700440301c4001281800184600710f40030345c070b01604c603c0b0000074403410004140d40c1f150403650345400c420927034400783d42141e80c010301d001d81d10000140c0301480812010310941350301c4404880002003206403490310605684414071035a404900b041c04010f540c0d600300003480ea10691022541c884100c100034404000034601507c208604c4600c0092620030381c0140056042c2e61203481125042c1d900c000045840038024005c401180d000b1501081001015410078414200c00804c1030f41800800c0c0725103c200d8010b580b2240005292714010824950000e2100d0301805588120b01082d15000308083e2500c803e0f03690381e411100850350100c1c0003510a101c54034203d42c0c40034540340c48544e681002076540c96107000b80215142d40c002d00064006100d02da40b0356032044000680b0780e0070713540381d41a9030307540000c05490705000325074505040046050088001941c444c03601001c220400305401020f10400500d50504040c0e81c900400d099540014a2a845580b610300141d441606 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 141366906 1106 141365800 141365813
    0x31005030a1703132001030605182a0a0e01030c02010c0206040803071403010905041506060e10090b0f0403110306060a0e09030f0c06040b1005010516 66
    0x2010020414409002d000c0c1d03600180203941010034103072540310b034102105451240400380c405600e113000e1541c0c040c132800000d0481a02c2c00040181002006841400c001d048415202c840713010800b22044005aa021032404000d0650740703414141d140a04034a590007241404203080040c02c00c90b0601c140325155040181340d00174101d0342c95940320412180d00c081e00e034008001d06801106513021513480294002c0460300301c0010240341a04001c1000c1d498604a0074155041000c10810140d02032036410046500f204e40741c00c000c00c29603090303441801c240d1209940b064003298034032250b01e684000e841100d00440490444070900c50030951501c104450b1250301014100c010b01c24900d0801603194021326800c01c49144c18114203003035665070460a02c0709010351140703080000f040110f048064105902c101003500080c1020000b0741580118070b0f8060744141c01c0322514052060307 = true := by decide +kernel

theorem cover : BRFrame.Cov 141187050 141366906 := by
  have h0 := BRFrame.cov_init 141187050
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141187050 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141187050 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141187050 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141187050 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141187050 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141187050 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141187050 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141187050 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141187050 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141187050 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141187050 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141187050 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141187050 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141187050 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141187050 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141187050 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141187050 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141187050 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141187050 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141187050 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141187050 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141187050 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141187050 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141187050 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141187050 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141187050 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141187050 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141187050 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141187050 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141187050 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141187050 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141187050 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141187050 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141187050 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141187050 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141187050 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141187050 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141187050 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141187050 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141187050 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141187050 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141187050 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141187050 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141187050 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141187050 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141187050 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141187050 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141187050 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141187050 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141187050 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141187050 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141187050 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141187050 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141187050 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141187050 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141187050 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141187050 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141187050 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141187050 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141187050 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141187050 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141187050 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141187050 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141187050 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141187050 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141187050 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141187050 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141187050 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141187050 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141187050 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141187050 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141187050 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141187050 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141187050 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141187050 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141187050 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141187050 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141187050 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141187050 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141187050 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141187050 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141187050 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141187050 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141187050 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141187050 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141187050 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141187050 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141187050 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141187050 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141187050 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141187050 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141187050 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141187050 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141187050 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141187050 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141187050 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141187050 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141187050 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141187050 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141187050 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141187050 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141187050 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141187050 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141187050 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141187050 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141187050 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141187050 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141187050 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141187050 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141187050 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141187050 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141187050 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141187050 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141187050 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141187050 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141187050 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141187050 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141187050 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141187050 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141187050 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141187050 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141187050 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141187050 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141187050 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141187050 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141187050 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141187050 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141187050 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141187050 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141187050 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141187050 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141187050 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141187050 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141187050 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141187050 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141187050 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141187050 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141187050 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141187050 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141187050 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141187050 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141187050 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141187050 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141187050 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 141187050 ≤ n) (h2 : n < 141366906) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
