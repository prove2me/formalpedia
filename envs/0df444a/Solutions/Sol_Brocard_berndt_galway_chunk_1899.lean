-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1899
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:04:51.161451+00:00
-- url     : https://prove2.me/submissions/e16b65b2-65a0-44ce-8ff7-098d6bb292c5

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 341366906 ≤ n < 341546762 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 341368156 1250 341366906 341366911
    0x2d0509390d05040308100b04090b0a030c0b0c06060114070807020d0c091e05042f040c050405040515101404030516030c09140103020d050f0a0305041508040209 70
    0xa03000c1203044000480541004006064661440d0305854140c0718800030000e20044900b1400300302c4001c00b00e11080c0b008407002c022540140451450b05003000124806001460f207415080131034803e01000041081e020503024140350f03001c0580311448402d01e00d1800001505c10703414031800296042120382d00c042180c21440e0001d4144d9030720780c1c00c1e10200b1010400000007074640145158041203500c100d4001101d4524888041301c2c002d900d101c400c004640044c2c0340180a12994403018501c1404105421061403000e811009803500d56000705054420008015000070f030001418451841c00b403198a4100c0d40b03480c04801a4807c4a001c07500c0c41d008c0900d240184081100303403410a02c0c01c0340484001d1540722081d240801c0d0101076011049000e03010032103034000400408558403400f442000020b41c100c284d200c400ba441e41d020b02c40401c1c14800c050383c446c029241494480501001244e05aa03c41d03035856954078582807280900d900018064000c00080302c3c28800543d0301c04503280e4 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 341369406 1250 341368156 341368201
    0xa0212011b030603050d051c050c0c010c08090a170403240f0212070e0f03030c01200a1d01030e150108190206040e090c0a1203020607080103150f062d0509 68
    0x9076149441e17110409000480124234014078100030400c4240484034001c2d20010b10360800030321080754917500940c1d00c00c504468080d0181c1c081c2c200da002082e02e070318106804804204001d071030680c803510707403618030342c005008210240940c1d00c0d44811908c2070300c54507190f40201c2c5130031428016130a44812205c0070240c0f4040800074108101d81040d83c846e0440c50300500000c084030b588000f214011806403540380040d140c4176001c0100d0440380100c080440c0c1d0302113410341d518041e101c8290030604425043d81d12803410183e5960301052410f20411055810380036030189110203616107104d2501e401c4141d62910038000807030382c00740010b8950f201900e040e07035183c88103080155140b2a045203081055010a680491802d4000900c00200d280401482c0d00950a0b1549030b9a4454290b40c440c0d0300b0300c8000e1201d48090512564440d095200b10128056004086005581c4a004000100300c0d600d58220740900c1109118008003d190244d00415059400344150310b485810030800750050044103 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 341370656 1250 341369406 341369417
    0x6011203050a0e01120e0703021e0307090906090210020618032106040b090705030708100b03041b1505040f150801061b0615090b0a0e07050c0a0212011b030603050d 72
    0x183e8580e01800c02c3c28400040c807482000002030112030b50303179901c00702e00c016030040100e03810000320051101244009601c01800414001d03103000c448500805504200741e9201c0e98541c0d880c40180d44400d540d940d0392905900902d55420910010810124500f21001c2030f503004010b40f2214910031640a02c6011100c0943c100b00e54544000c100503050000f26a0351280010f02000301c40c5170084041c500a101c1552008407554410081c2c0d02100c0d014020305604401c1400000e0018800c8003032403121954034080340f4030507642c0d500e80540c81d002004e03050010400100f401d0101c600701588072002000d00fa0204d03840603d070544090050031042c0161420400700c01e40c0c402a0b41c5424405546141e48070108019007a103038101c0b018184864000e5503040d6040a124030120314210700c02009807901403a5042c556168200269001d9001c0080350074035028007518031001d66139082c2141d440200000000c10100c50003000d80c441d030449242c1d00400c1c1458001c040c00440d100080b9540b814181d030900 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 341371906 1250 341370656 341370677
    0xc0e010309141615090e01030f08220501110307020a0302090402031c0509040605030a051b03101404140f030702130609020304050106080106060c080304060c14160506011203050a 78
    0xb07080ea0311880955a0600c01c0c419080d40c05400c0d0503110f412200113043c4e1044582104c40c00320351481c01c0d4811400d03040c5143c2c0050001c6000422030000780c03031044017803600d01001011980e5145041465000c503100c18003200b042a540c01c070140043c0c0c07662040180d40b600541d6800039100741e40600000c0e003d017000500150440d10100182aa071601c0405082c03100141ca020051403a4000810140078900f00075000a40c0d040001300003074071f10b51113405811210381f0b480407084030440102c0c9a0341c0c10301c0349080c031074401c00c00e91250805182e41400c959000f45014100403840f502180b8030b02c881035201c9000210303800004800d072051542c3c1290303440030381e14036115010041c0c82c80350030854034588000140400c1202c15884013044030080c400900c030640d41d4500686501510318405040b4010800000e40050f07110341c0402686603c0b418074200b9071040118200068100701800c08826500000341c2003844030411019005091102c2c070000c180d829681c0003016400f48080074020320a000d80f1 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 341373156 1250 341371906 341371913
    0xd080601030f0b13020d0b121b010906021b15160b0c07030c03030b060405040c0c1703060a03110d0b070c060506091b2107020a03030e010c0e010804030e19030b07030c0e010309 77
    0xc11f420800400b1f000d51200c01c5007145844e0070045045c040410b07800001c1d0303003c55004408940841d28990040c1041c0c900100040c084a507120040c1e581c4148002c0c68440c00400d0031000c2d00900f07642e101c14003001203207460302c00000780010b08112100d40b001e000200c0000d500554001e03c45616180c045400300104e00858500e020326004694000c2c1858020840d4070390280c0c041010030f002d0b480c080910410b4641c1c0c04080d10064404503008080d00605001058007040d0444800002401400c00040d030780c0c94403802d0034804e41d641070004440094000c03e0003010b014142e0048801c40340010641440c002180c010001500c80d03031010300d40410f40d5401c9601c1c00e52a641e0f54910000c034142c141c07030f040350002d448042d00c41007240802d28110001410090502c5405052629a11100e410300700100042d5580c0b0401441142007005002561007252590000808114104000404403500310b20302440d80f501c0042c805000c0501c0d010b90500f580741e01186280b0071003c01c0c200002c03002c44504 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 341374406 1250 341373156 341373161
    0x60f05033705060403050702011805010806060a021f0e1005060607030305040f02041a0a060e06121b07050c10020606090c03180303091612080a0518030d080601030f0b13020d 76
    0x80c07018215010b01e07070801040c190008028411203100343e0341c000703000711074080544d00468640a0b031400501048002122810401c00402031840705004441d1002040c00b00d203065090420060f03003605032964240000d0080401c100c1ca00b44c040d04005000900c0c10741d01151181c06051400340805172104041000c0c0009a0603c5070072580252091102e002c1d03451001c005802c90703a407124051200e8a4001925078440c03606c640840f9001422140b4120002d0141d0840700006051104291a41820480d481e09200002d00c9007600c5030300941082060035041040c008010018070b815074001d0800c111240d9100840280d20000b03603002c140e126164640c840381c400d50f040c08183c032648400400d00c011007800103440e4000701031696480c9051911341e8000e4141c0407200780300070a10b02080c00010a42400b41019003105600c0e040074080420729040080d1900d0840d85019010800b040240b00c41d40d641030081004000c007100040c4508110740c40800d140350640c0b040480f800b5400f081d049088100764 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 341375656 1250 341374406 341374513
    0x12030316050f0720030109110d05030918010602060c031303030c021c05041802070b072d080708010504020a020d0315030b0c04061b0b0103031b15060f0503 68
    0x10442203444a08034900f410130b070b418032940d030304049603c941c082c2082e2605015180d00e40d940007070810744100510092200e03405001000702d50500043c002004280c5540c0d5034040748440602120b03120b03500d4000c2c06400c00c8405010242d4030f02d41041008851503941d820354251a034140b600040001c40c0e10070407402c0124a0780044444a0030000940d50142d0000103001500c0d040c0e28096090b140001d403000880c80f40e1200100941000f03000982e610f4000c42016101013100f64082d4520351201c000010051828052000440c1211040c4604640d00420341d60140a05403070441ca00350038148080d42ea034042d81e04c130608042d16803459100b880c00d030303c1e071410042d68010b14000c4503003850340c003c0c40c054019000e92400203000c3c5482e500150005507000d41c282d6001010215030b6400e40e1402c880d42c00c2c114041e40f41c1c50201d50700c002d0000c0c41c045064507420a2001000a01c282040d0501400d403900390301907071213a4032454401600f4582d440804014201510030140b0800040c1004803251000 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 341376906 1250 341375656 341375677
    0x11061b030c030711040506181308160b0f01050102030405060d0204090513120c0c03150902030f07060e0a08070608070207030501020c01020a14130b031806090d0e1203031605 76
    0x71489142100000002e410140d2288040b44000a802c3c0107100485404642c4030743c1c403e0550110b40950307254194203503041a0700314030001000301c1e43e444200320750340f00481c60400303104402c0ca031106001801f4070702c03900056683d000d100f15524000c0001e5580c045c82c000c0910078207000031380c1c0d0032005180c2d0444000704041c2c6800c1c001460009007082051440c46400d40341401c0c3d45007850f2081f48034013200000254482c8100140c1421070306c50000d04441002440907076a074900401000d643d0130442a41c0e815290300c01889101d040540083c50407000311071860083d02d0041c01400140c0780410307060162500c2e85803807200743c1c0c3e4a0008900d01562540090015440012202c3d00101d040d0018614290b00f40ca070f9064481e03003280005170303620030107204119401e550034040c00400c4020f401544c21850a400c0898a4104800f01e81d05040080d1292150782d07200c90780100717085800071100d02900c4011240782d1545850326800d15144c1c80000c06501d000b103c2c1800c0c108940303000b1400d6400e500c80 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 341378156 1250 341376906 341376913
    0x30e011e1d0d1704030c080706050a0e0a03050a0c030c1a03060d02040b0a0306060306060f03030f030e012301150302030c160201090306050705090103060f0501170a060b07150b01030911061b 83
    0x401024202c81c644c03090000740e5064110f000045200500003c0300710440d801030343c4145c43c0480d1000110740034840c100589510150562000011030f0302004810358040c090b007518100186076290864510700141d021850007400c2240645030251120252980804281c4403408107108504c00200100b03c0745132400d0748441705480100c20700100703a2080c82540d110310003c02c0882c1d100c01e01c11040c41c90700d1000800040303a0b040400301080c8684c0108818140080000c11101200603940c0900110790703185440329070400004000c445014003440800082c54141141b6500342503000700307510710a001c0c0702054141d1015600d0300310391140d4400e000031904140b0400c840e0500ca60000c05650244070800e00090078030001080f00b1546075102021510b05031200c400f035a08881038049000402403500c10b00d2a981c05000482814090090100c284a400c150040f0740b4940001c0c0c0031906800303803a40c101440c003074022002440b50100b03003621a0084036040c0d2a1009c00c00860382d90180d6043c0c6980500 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 341379406 1250 341378156 341378183
    0xb1305060a08150f060414010605070302070f06030243141b0108280b0402090d1202100216080c03160c170a05060601140c0703030e011e1d0d 62
    0xd1000c050f40b4010311400750780c91120340700c8034100010341e0403030b02406903401c10303200040045ca4098402043c9061090044d150881d03518020301e07024101c40d45c86000481c0d000507804100344590381503006540c034030b0fa850034418807000016841c031202135030070626500311810301c05040c018064030600340c40900c481180c3d00c04d150b0001a48040b0308441a040c007051484021841c07030151094640140600d000d0342d000e02451189051340509100030010790003507400c000c0c01603030ba101c64155030005070040c2e40c51045032504407002460a81040f1030032064a1040c0905060113140d815408402074100c8100d0f510b030382d0543c140500314801c400d01742540c1e01c110b51051040090540b604811642d9020303451702d104c80780121150b110304146000400f140c001e00006500366001f484000f188404e141402401d140c4a60a014503000c5160820380c04a1403035903000b056580c0c410b00640c0a0004038855a00d205031f030301d070058201e48180c1c0d82601c00313802c04882c5150640f40d00010319442600f1105c1c516000 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 341380656 1250 341379406 341379433
    0x6060201020c070902160827040519051003170304050f0715050d020405060705071401050a0c0f170c01020d050a0911010e01110d0c1203020405330a02010c0f030b1305060a08 76
    0x42400c8d8110a000384030340300c0d18003982d02d07051180c00d101d244a0001c0c90341010007440701c140242802041c0d104410449500400416040301e0300c1d24000c882203a01c10b65a0030203041c410310300722015039001902c2e070101d00240100188101007111025680c14001d49075003100b808440a40201d8001355004280401e02009005002803070304101c42040c416542040e2803140111800e10503e401e0700045218000402e0010f0b0100306020140c0340203001c101241403002d82300c024030ba8084558054903a402003401d520100885c82081d8100380048002c00005d1030b90b0b5150003581d00e28100c0c01e410b000e402107142c0480e9000d0f40c218210001001c05071401c84c402640064140301005c2801e03240f54129440180388203020384201d805440b4010107188001031010303000003240c48041904200b14201e03800c1c203a6560541806032100400303039000803030541036248000300100802071500080600340540c289150b16200e40307240075100c8440000c22140c0c0c42c4408280540415803002950703105081101c0b441 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 341381906 1250 341380656 341380687
    0x9090406092d0b040611031003110f0a170a080c0106061b050c0607050f030a0c11040501030b0711010209060703050a142701031d060a06060201020c0709021608 70
    0x1454826008001400e20b024152500c80d554031070070103080304080398110081120b10040d150f1040c0720300c8021404500c8409144015082510707880d03c400f03203482c0140100b01e960f18945e4200d4400742ea86947e20404040010070b10301c07081c42202c4103009520502080548184402182a6080000241c0d102d52044100d8001c080d0b40c895000020420103c0b8400c440e0316103c280c490a40110060007241241c00400c2010b42c0007076400c5446100e250700301c00c103054090014110300e030400d495660b05c41c60241818150149903081d014170aa141200610004038911821504000c540c6048211495251001802480341d4810300340e1151300400d04404141e4024000c019000c0c43d0764941d11210044510410039005e1403060154810701060400d007000c014241d8064080d00500d40406c40050300d4144010071003c1201340300068010601300000502c680c040e50005010f144000c6240c8440384031410f071516154080c1c1095a070700001c004c00704050700400300180f550030020a540ea131400c058000c10 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 341383156 1250 341381906 341381921
    0x10030902031b130e0c10230c1c17090604060b01020f06041214030411030f1c0309060204050d050601030605090c09060906061c021c0606050d0f020c01061e050901030c030803090309090406 82
    0x50701c1f103410003629450440f0f0700c10358021000340350040488030082d01e0309a1040c45d020040408220840c45c80d410b0402e44120110301851941d009031400342030908111040d1152516800d055602c01000c80380e00200010f00d035a407060704400f00302a81a1040f00c2203842e80000e903241040d115001c814007082c0607440f038540c00c0d01d0504904603070600284101d101e8580307403031510081d40c0002c0e0030b0a01e40e40078080e1708036681852086c10018501515170000440071580d4500540301680100010300070030100c1c0c41400e40020381d042c02800e08851420004801d4003005040c00e000b1407184020030a40d1f20b8801c01d0b50480d11017122141ea02042050103140290001c0c44041d041700c1c486508002440410311031402a41c205544840c50080045c03d0b440150100ca40b80d12981c541c00c00102001100a228070b0340900761950a007038884154209910940105802044c8101072070030040001810501c01081205e0344420542d48a0391030540c4203096000f03084403e030b00100e05404000c10081c1030f910908 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 341384406 1250 341383156 341383187
    0x51209120a1e0f0914040204090f1a0603060f061e1209070f03080909101a040509150303040312090504110c060a06060f1b0210030902031b130e0c10 65
    0x10010000300e0215410480c40c90f6034008105440d0040c0084101018044041d83c000b50000d8a85036481c2ea40808644e00c03c4186144107070b4420308070760246000301c060703018040221621415170800e100018440c11030b15500a00c607000c0081c180d0480800c08048504944800c4081030312032032400c404580c01001240c0480040c09014400304584181c0c900d0002a80e42000c956410480b569090211030301003d44486034644000d100040c12000d140c3d844a40a5101c0c0c0c1c0940e261880d100034070059600c00781c011100e4198424403031310642c6001046d10100c07900211000300c130a03401001540c03031210540200c4c3c0c20908290000040d01d402c1c1e802003060080f0102102d000b640c80c0f07441001118402c2c004c2d500002d141c1008103100b1803149500145101c481e8604a04e2400541c0c00a4000f990100300080800d8581012409501c0e0034400315000f0f10902407150501030300e01c0d0004010720b03400b82801d0111503403100d4001c103110041000490150000e0441c0804008000300030381418030308a1180c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 341385656 1250 341384406 341384447
    0x1b0c0e0712020309060105010c051603031d04090206070615031202010c0f020a0b04110301231012030c02190b0a030f15050a030210030b0901092901051209120a 70
    0x1441d80450602c2280d104034040320141c032032a4244401101c0343e5004800907a250300c144e4880c0070a21181002d41790046200ea12020101d2000d860400c48120b00340c40c2d040d201d5071900c3d0301c40c00540c407107504a84010340e02c071800060f43c850002c00344804940030740010b02421110300350006055015844070514103081e845e040503030200340c2400c1380d5a1498403001011400800301040008201080d0344604a10090010400313060400082000e40352038110100403220781d205010b182c00907112804040c1c58118102110120b236501e0103880119040300080c06007008040c800c1201501c454610040c21044c2c1c003055482041940050103041914040d5510510b009041400c045000c41b0700012150003511000c840e0745035408100208200755a441c09254945003003d0b00e59079804812800b0300088580060b0040702e0858105001e52007080001d000307031200391522416170b040350648403040c02c0c50001c540d41d82d44503e040c0c0d05010380350035090440c000200c1c28520442d0065040d1101c2806001079 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 341386906 1250 341385656 341385677
    0xd030903031a062b020d092a120320150105031b090a1506080a0c08061309060e01050703090209090c09070503041403030406020d050a06030809011b0c0e07 68
    0x403010641d000c00100c0d64084010030014944c1442101c001c103041d285500030b069003038a604182002e82c1d1109501c42c900958940441007006090607c80781d480521880b210104072031070010240c40d0540380910a134032542d4407508010988038129828102c05802d030301e0500850070841041d86e03501c42c030a0700081c141c83d030b900101e11800d00249140c58800036080349002c05420409211140c2c801030310007500681c42e040516500011440c0340340c001c6c0381d180e0310a1103510304400064101c8403003c54910402c8450740500c1821750f81e484103180303001094140024a00428a420802000040b5400c9002d50800e030412401e81d4141d401500310034020345442d070055a0b000645910b5480e080380d42ca9008c0e03007035404a45064401e8005d598070910036142800160b0b00340040f28619081140d00f2114503400003299107684000e07014041d040029040e0501c43c65085503561106405036149040c10003074000c80e010388030300581a80c580318036002000ca0f4040d58548400b10110380080704d9003000700300213440 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 341388156 1250 341386906 341386931
    0x9160b0c011a030d0e0a0302030a0503090114030709140112052a04050a170a080f030a0e0a02030628050a140108030a081f03021c0302010e0309030a1101020106080d03090303 76
    0x3030005606001001341c40ca20f000e1410039103104001210450f04060320001c00703c0140c60810481304604e00480080d510786d0059000100300724011407601d03048203401d0092010541c1c00ca4920004c0d12011038403a1092111500101c0c0e62400300c0c00c8a0103c2c3d8100402d100700391003031000b1031240c0c125080c2560101d000491003020f0a07c0745128a54002d810404100205100c13030b01e1404c2120018010b6035400d208a03120b07020150810202c56101e00d1000050014112071445101c61550541d8060480304041e0b800081c0c4806000385002400000e244400210404009280c058500c0b087c0c010070150421007190001003901c1c0a250403203d4144002281c4c59034000181d407800e060b907a6902246a86100450506042c00c1c09009001c040501d00480140c0d40c6201c0e041140104c940d06c980d045a0505000b804e54219180340b4440742c03c1081480050f45000c04c2005c0381c0d681100f01c000d028056240101c2c01040d00b0341c080c00d058055042003030205503143c0c1000030071138001c1c0e9062214589526 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 341389406 1250 341388156 341388191
    0x801080a080301090506030102070203070e010e0a09051005040206130b09030f2107080702130f0506010e1008270d081501050a0c020409140f070e060102070e09160b0c01 74
    0x2005401080d042c00100032003141d5421641d800980a03001508060032540440d14025407900311100d65900100140030045101d403010380c0c00b01c554203091100001503200c1540341d005003204080d500340c4810000c5c040d519034a040f02c3c0c00106146030540c5480e41e0700509610f80d007000605902c40c0c0141600c01040c0b1100246a00301c06216480d401c807140c10b1307501d2824050f40650401c4401e0b0409101e842c000d0380e80c0310a401414a038910000c10101d00908505084900042c1154107201004101818a450704521071040d44101d00307001c1580d40b5881001c0b96120100d8241d41003127444102481d80030440403581080000050700c80b5001307500ea1000905401e03601003252800100c083c010b08454511442017441858006403001601d410745807244044600324a074444802c1c0d1140b94003529103402080800e0040040307203c01c581c2402c100000079156130f003e01c00d00000014040101e04881c0040c00f1042e81c22942c00007184003e695209000310a40104c0c910011551801050035100b85409 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 341390656 1250 341389406 341389423
    0x40605100221071a04030311030a06090f0e06150414010308070c1a07030f03021303060b0117040f3c02010f0804151109041406090705120a05040f02090f0106080108 72
    0xb04c91003034200c0351240300345003d10000304203504058503060190505e00701440110300800808a02140203405d207001203003603a10002c144c00ba0646003210030741a0243c0424041d4219100302100362040c203521001401803d4500b038801da00031102800082007003054401007614610a41040101c555180604171071610000007401030f481d803c0240c68000382c45032141060809417803d0050a264540c0c107217180844064004640050340c034a660300a96800c2400350340382203211603502000703140030303a52500040b450750170041c1011507800754111a11400c909070341d00656000604e0022900c1c0b007a10026012180f0b406034081a80c0394502e0020030320a00506201b039800030714079252030028880b100000d207020f80e02c030308003044140605000d03640d580c0203120108940440d0328015041400401c12517590152940040c484100720b0002c3c40c0400300000c41d404010010009a166a103040030007240e8507043c2e00035031151014041003c0708500400c4079050741d42c1603450107500c0c1c0c0c030340f80056a1103c07070 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 341391906 1250 341390656 341390663
    0x10306051806041506090504030207050102010f060f1401110a0b060f0111060415231b071703070210020309030a080a0506010c060e0309031c0809010c050403020f04060510022107 78
    0x400c2c001804180c40304a11803409442c6607000600070307a18282c400441e102550704400503003044400308660b40c0d090042403004036032000304000040c81c020300745142d0b4800b417007203402410102120451981c0203880c4001c00c03034000c0060358602909460b10700a405011210188214460606010254803500d00480c0500c944001085a0348507626480505251002183c0101d5181d55091101d0680781c0080090346030302224228035800c02c101c50f001080d9000c3d11954404d9010f00900020812510b944024080407045d00c0c3e0340d988511404034148030380f0500542e140303400007061024100c070000040020120030b9490400030744410900c0c030306a880a54403240080c401f01c031040d0108209a002d010141aa6001c80c0d113064544c1000c242017030030300b80311003c1000c005a201214243c0140c1d034143d00a5006c002049003500c0740030058400e00032804040e000d11807000c040032894031942d001c50003500004151a00c0558030300d000030355403108402c00445903e1441052040ba0300310b00180c0302c0c401c2e403 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 341393156 1250 341391906 341391913
    0x30c0e0a140411030702060405071d0c09220906060504150b0a0e0307180b0108240307120b1e0708070302030a02160c06030b1203040308031909030c0212150a150314060103060518 78
    0x20303081017400c1c9640125041a0f4009172000398500c079193b1f80180c0701100200c0c2d00c40482d04480a0a000c411501650f104600072418050081c1035400070101500a07501002100741d120f140408045030b00fa0800380803190184202c41020910101140481a100420368024051442e0450046440060643d41103c0c20b83c4605200e003840100d0102284054001508849050b075550580b60718032a40280180c5112031080d040c022042d61451003c00101c121265129060074100c50092049030010001420554044042190240c05070100d070041c07221499031441110041c1048203111585104032000f0a00d000d91807901420302c80359003102c403410304000d107040070f10b10380f03079003c49900060075204001134186030103121444c180310b451011030007683c400f10198014414040d80320204003046145074080d00784c00c4401032042e49195805a511230380407581002050b00648219202e0704000c2c012a00034484e1420300c100040e041c0c0c100e80c01040d00344032540b00d107515400c94401800b205621a003 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 341394406 1250 341393156 341393161
    0xc3303020901030207151401120b0703091403070b0108070609080a0206030603010902090109090308010b03090318150a0206060a061e080411091501030c0e0a140411030702060405071d 80
    0x1402640076040020040c180585492940c2c0d803011800301c206040c40c5000c55803120301041c0114031242c187e0241400305a00d9a0710301041c0c45003c403840c8028804000c15480b1803a500400010180c400980918241207036120034907450300142000c0c0174040c4440b180300b0400c3c0080c840c0d01c40c0c8285821250b845001d011009000e80912925600080040b5007544d203070300101c0011380364812064002e08070304400042402e240c8c40c0040c8519810390044500f61010f00500160aa01001700c4207a8904001c6940760121103101203001c0008250030410300348801308500e91200c1e00032030030b030f881030f44103c800c1c2d100e480c1c0b00c21080d2011001c0d4a03070a00104560852007084c075000c1c030409900640038807a1011b450b850400018032402c000c0b5000d07007000700c5507180080c41c2d507054040c542ca030170b12a050014408442c0000314031281054418280b20b2010200e0003121034650b544200703807004000c0316043d903071b2601d072002075030b200002e0b141221584284030700000c01e03014610b494000d60114030502c0301c0c5074 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 341395656 1250 341394406 341394509
    0x306050112051b0f0c01180209010e0a06050303130801060f1518081b0102060f0103172109070f2309071101060305072105030304031b0c030c 62
    0x1404000d083d51019074000e1414095104000007031300521084502c401d54035889600f913642512060005038100042c42401c00e40107946021800d81503c0c0c030040b4243c0207a03a10b10140000c1c0c83c0350342c03149030980030016801030a4a0745035140815604248000d214842d0b0354254603502211a12030401c04807032002030b04116a1088160412040c4140803c5202039111407507641042a00d4000080f040c0803401c0c011850358060000700d5019025103650030b915850758076401c0c080c5003405451169000006196000c5400c460705408141903c11808083c0346804c600752a600c20480c0150740100e007184100203190004d072494410792012004416035809205030501017802000790080e070521030f4007000f0200d84403091003420000c600500c000d00c0003910301703150301c0044000c00e041b00d00c8034000c5d070411901180c0c00104aa4006030b1510303003402920000010005600e50241c0000c1543e507c401d0300000740942d0310000c5080c0d800c2940c003043e0300001d00d002402228900346040b60070285002e1000f809 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 341396906 1250 341395656 341395661
    0xe1b07050a08130f0e0103060605030c010c030e06160c0305061f05010f0507080a020607091208030408131e0302040f0203070e1915020102041503020a050f030a02070609210306050112 80
    0x20080710200c0c01c6003642d104e0110040400c22600002c800c01c016400400034003c140c01914000d1030b0176006460000390040001388050302e4004042c050181005205a050700d8450440b24030460580b018070140c00180707000104030940348400d86007441004041807948820303100225181e82940c49034880c49291100640e4080a6010301905102d02441048003186009005007010003055000e40b40500d080b55001e01a00ba440d04030081d0908910400310018840c40200c0380c0040c1c11219103034855030140070f2030508030420703009031403140e411040b038603540010303890402d080d84d100302d4013807000c0b0040806840403800b0440d003c00000d4003d0724000c80c51f042444520f0000c001390102000e900d84c942d220050320800d80481340c001070b94001000c1104400319802034130442d01d1854154600f80301b1000080560045060400120b0800004682c416040303034111110b480cad1010051211080c9030074260a03291a625850902000c408842030b5800c2c40b1344281016240e0503100c219285241c90601c400 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 341398156 1250 341396906 341396917
    0x105120405030417030307090f08030a050c0a14100605010e060a0c11060a020a02010e09090c060c0f0613060e010b03071505041e0510170604020a0201090605010e1b07050a08 76
    0x1194001000f02107030f4114000c018614400c4500700030b580e603041080d03000b046251a6840a22446c000c86000e2010b0400401114192203091405580702c0410101b1075044c1240d0f404000c1c00140d001c50582004407002c101802e0b5070110b5401080440d550350015951300e00382c01c0c54181e00ac607041041c0d2950501541040f02e000c0c1c01341d441d00005002e40004210035504c1100210050392142c9500811036a0044880403030301d2060f41e148809092405c9543d41d60184400c801d4410308001c034202c4081c00c4200070241040001d102240e515003001245c542c0d200700040700030344032181010035004002905000f580001100500248145440e10070702c901f00032082c4403454200f1070204000201c02a007a00c0707107446203640300300c0d81d07090910340700402c046e440c030703440b036003024440120740703d081c00d0285038031031031b403100c0d0070f2300d000d6520b10a040d4201d0042c030040343c0c000e080c00c0c130340000403900941070b42c0c1c107134824182255244a0601d2500c6441102d00a6160040c502c0e84801c160000040c00c1c0c5003c4c15 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 341399406 1250 341398156 341398163
    0x1605040c020a0609060219021207170d0203010306020306090c12060f280503061608010506070201030f020a08061306141e06030a050a0f0c020d111e0a0b011401051204 73
    0x2082da0516035600070560f001600305403943c50300421503010303501000c1800180d81c8014001041e50300b9004079020007a015001c0b010f0202400349960390480d000030022039140c1545964110b503250303182d14084000b03400545030540a14104070004a0703007490041160700030398510800010350360f0f4810803c01040b0b03181ca403440d000b0088404038001610004218070915101d80854500745040c01c0603d898074200400c1001d81c412030608100300d0036040440c440c156503080d00d4850baa0451800103902034192526a40001031000507000003a55003d8203503030207081c0440740c40c10a01d19841c803080c1600d25034000d002c60310740d0911261140b4034022414204500300d030907990503401d107030000203460382d00100c405a1070350f0340340c40c10448000803e124001100d4081c5400300301046480c03030001d41d50703000600d03084140b200720100d41c4c0e030610301002101600c034003030a100c02c11044079069141e19503100c0031085914003c10800415099495105289001410f9441d50b0402c83c01005900d80007001030400d4 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 341400656 1250 341399406 341399413
    0x2d030204090f0504053c0c0901030b0f09030c0d050903121c0b040203010f05091003120905010201050c0309030a0f0909150e10030b0c0c190606060807021605040c02 72
    0x61440014050300b03220b100034180000d490b1409080c50744c10188600c00410342e005e08940010301041d9211010302c116000d0100140340f03c182212080d00c0c080090400070340c45003440700000100304c1d009800f075210b40300044a0361400e80310003004507500d0045015040054100c0b0050039055403045000d4a52107400508a401c0c0420889408016901007030511003205041d075201e5060b042c450041103504c0b0307030940382186151703d01a00501d1418043c040c480c404d003d078030049450311b40b9501c155005940c00444200300c070360a680002e40b02a00300d21609015500b4040001c0a0303003402c0c401d80e4072402c1c4050140d4a0607004483c200c6030b100703c1d9510351080c002036050200c0c9895030b07842a6014500131f61401441c19050031a00e0384070365401848440466400c940510009004415503500100c81d903410f20b031600480322149081c0144680d20203c11982c0281100500c001500094100c3d1101c4d115a440c60b110b26204a840314078908000028140380f140412003800e06030b015119482c02403065 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 341401906 1250 341400656 341400659
    0x90f0204060303090e0c0406050a0804030c1a0a0b0f03071203050c0706030603060605041503020906030a170d0c09030f0b1b0c010b01080726040807050a05011b2d030204 74
    0x180440307105800a03000540302040c28070561a03250542c2d0b40200400e440681011325040006020348a0303401c2d01d5081204c00f4004c20201801114000c0c075495008280d0800700d03132200c03e81d0f90703040811039456800300d081c04c100600358145001e2842e4401e1000d409010200e0800d40d1040103511013070803c50800004201e520000398052050201a000c03541e008a0000e1440c01d0213019102642c0001d0322a524041003110410038011803030088960603204d0012940c0d031000046e08140c40d040002c0c029600080b5902401d4001034010600946007000820580d1440c8404803085550741c00000c1242d03031303904440401f01b0030705000039030300441c55034032400418101000142990000b003541c50302c40c0e44500f040383c650341c0c000194950001d2640b03000070042107501540700c5050750490008850035440e07004030707043c0142c00f030440e881035401c0380484202080e0340c50724600a00b0030764054910b01b0182840c48140c41d104013118811000d1180508070301901615400001c01a640171210078154201300 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 341403156 1250 341401906 341401909
    0x1401050a0b0a0e220b010305070b0426010e010222080f030a03051f0303050304050709180609020402040503032212210309150e070b0a09030f08040906090b01020c01030b0a0603090f02 80
    0x542c4e0740e070750344520810502540b5504d0168030f400c1c0b95401415407070409001c10b01407403540306401d0b503c1000d901c0045d00621114070600380141140350b000000381d400050b000d040b13900030031480d40078032202540b010202039030f4207916500d4034039202d12286e940d0000c0200c0064517119401c0180c001c0e07282c45d150680000d144003686a640d0040c5d2007180414008001c1206010301401010700500ca82c800500480e410080c14a03000c511440700100300310754400c6480306540380c6138151805400080c04480e0344424507035508100d035a681501040e02c8034503800c0441d8664941c80307003401055200c4230441d26400441810308940310b03c41d0301032003003503030320307002d0b0b4012820306c480c007440c80b07a8040b400007100d8034130f07034109420035410360003600810000300210443c040d4130081040440341c002c211110160b1441c40d00c111103110f9a44008034060416030042120500d540c841c500551007602201c408001090042d01900c482400c05548054030460400c1014020f80048808a10a66030817071030014590 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 341404406 1250 341403156 341403211
    0x1203121503030f0318121b05100204030210020d090308090f100513050f030606090405120406050a030524061b0318040b01050309060103030e0a03020301091401050a0b0a0e 75
    0x41c000da00090341e5019166a4035014400c61180c8a10420050082180c5849550406480310744410800c0300250b00c42c6486280c0300e220454880d440802c0d00c2c0c10011800c12080650800e00061740300d4122448580292400040d0841c101501e07603c0d4003d180b40345031504e09154228106040c1c00c000d80038101c41d0556074140c05c10094620580f00d480d110103c86075080008441c1c1d4002d50301840314074070f0441c0750743e500027038075980550304480402140c4d8403450700c2d074103080c102e030074038109003001140105070250000041d10341c01d90a03940400a03550380ca60806050a4192540c40c84014140f68080080c10b0440080400c01c3c52400c5424240400300c000300d02c1c42e40300701280c8250550b04000383e03080c0d2500d4051805100340c00d18005045003011800b0030b449900c1840014244005d80170381411644030f18081900854008000304001291800c10250001503100b004445518010010314080c10302c3c800c105d0840300142107015601c1c01d001700700c0100440905260440400c1e049880000d00000313 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 341405656 1250 341404406 341404409
    0x14071d0f1324060b0a021203180a0521090d0f020402040513060302120604170a0e10080411091003140111030c0d060911072003071502060c0412031215 66
    0x4001d4032072031a100d01ca4041202d0858000151312501001045815680003d65842002403c510281d690b00c44107003429507490310480100440c000d0050440500001040020003048910408031004211100c014080c1c82140d01007580100028100d01c0400c5100100c2410184090401490300c0d4035840000c210f555400030840c15551038940910440c10424000041410510002d141c98207055403070b44800c0c4000403100800d00320124240c59118890385e40c01c5500c0101a11442e404514058014071158080b20240c654200d0300241d038400781440c45a940c030400e50b91800206941c250b80d609407030307003d910200b10407542d01c0e140c00c1c2d241030000c18000c0d40030749034020413141e442c00400e030f101c01039540e00d511502c480c500c0c01032208662005a0200e54409a01422a981004903602c9401d8070000401740e0380d41501c9484004200d00c1e4440951085140d0b01740c003140e4045c1c0d113061540c2120301c501c1c066601d80e410051020000030740504006242c81407610b1001c211262146038500314003115 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 341406906 1250 341405656 341405693
    0x3080c21010803070201140307080103030c08070206030a090203061015050d110c0c03060907030305190c0501050703020d150f03120c0f1b090b1806040902090414071d0f13 75
    0x142c120843d030308002c1016400c7e81030120031b420741c9044100034014080505c40501402004950402046581e208031601150300806042e207030308010340524001c1c0b449020490191141d03201240c01c01044a03007450031188a0070f240c07401152031820469007070704184404110796444802440361038030800c01074070030241810010010380600350100b41c58040064002a030641280d0418004281c0c0f203030413111002c00100d4151400f80004204850b9030041c0b1001400f65480e0405010301d50768150004c0a034551000c20901900300501d60002505d070079407090700006000d2000410024031017240010714041d560422405081107038591103d044030144045484442819030a07822510601070540034103038487d810402440d05c44089040600588000e11400c3c038407800103002c1e0380e91078001c0c001e46540a041d81490b810685003080804501500b164401d0080301c001160800b4404a01c420502c15071003802c006484080e6030002d9070201a24480c8441d81520040340440d4a520225000707000 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 341408156 1250 341406906 341406913
    0x1c08220210030621030906090f03060b0109050303130905070509030a020d0c0308030c070b010b0f161118010f12151808030f100b0412110d020307150206100303080c210108 75
    0x1013a20700200041a29045201440010081400900b081000403c2503c1c0c0c84200001c2000780b14006a17005106035101a50521000640c080310220540c00304017120083c550070b0103583c03501030003035582c0d02908540e9509a4040000700c0c01518190030304030216030240182c0c04080c1d440c0c0d1504402644100ea1040d1110300c001003907800c10148900250045c003002c40e82d1410891241c1e000c607424410010311248a007031207800c110601001980d070501203440140b030000c00c410f10410010040030244110b481425a00341c0005007807244260454125034400c003010f11003144c2404d83c03001000d0b01c0c44140e80c44200b40185000060202000314080c0c0510900305c1810314000800001140d141e8001c401001002e102c00c000d80014025031111040c0e019405005840300d10f00880c080c40c6440074003950600c41c2c00c030001760605400c0c4d040c003505440c40e401d0f1203569440c00380d40c10030300210344002400101c1c550700084c5000c00705000383c0b107542e045034500301e0007000d1210300304c859010a80101200d41c0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 341409406 1250 341408156 341408219
    0x8070507060305040c0b2b0c03150515130509070e1c05031c09050a0605040c06030204080307110f032e09080306010e060c1c082202100306 61
    0x120800c1028024074291900780610700e865034800350308010b03034801d84019802c041400980009928080d0400c1125003801314280140810a070b80504001020f41020900c0d01d008041e02040606800c016500c000d0042d042c1d034820301440036001e80c41542c078080d01c840c4280300490b842e070700c5036800e038003460080d0368440c5442103000402008540c1d030316140304079290b1001100001800842590044240302c1503170b03980c0c01501c40d030510150010003030003401402003046801c00c12803151710503405a4040d8108141c102e0700e5103c2541248030b0740c016100954000e1001400107450407000014010024012900003012180841e24115041c00c80503158451807120000544111612200302c003070f80c800c14045e8202c591030300001741c40f011b40210304101502490401036180d08003201c0381100c07000b0484003007a1039030313a890030607215000c21080003c2c000780c0410101102e0218081c2c1140141c0401c0b42c01c4005070b0308011060107010041c4050607110140003c1605107640d0185881155a20211040 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 341410656 1250 341409406 341409413
    0x1031e050114040b0f15120a0b010f0312110c0409060b12060601030e030901090911040e0c0306034c11041a0c0616020102070804181406030a0326040807 67
    0x80e0080c08020085c852404000c2904460107a0003100d00e4203907110071070800c0107643c650074455401030281032100000000520380c04100c1c1440c00300c0740190416806040105006c4560750501c805d05903040c0d0222403604064a0950701c503d07035261081d0000604240804042400b2114403110645250418001c0200950b014003400111680880245113000c04100010b410080d0501800550070390302c0c00c90f10800034200045030068400c10b681e942613032600c00100c1e20300b9031044406501902a0354207546120507103003420716a100754400c121140a0030b22090000f030500e41c5882d0440ca446241180d02d40f901300303210700303005640c22000e8030b40d07100c0c24000c4010180105c0c0c0082d088990b010444602610b9000c90b4143d003101c003a0703001c4844410f5402c0c0490190146850181000000003400102400030720b1010101c0107030b140d028003c2c2e00c007420301d041c074024007103540340c0e099000650800c00280c0308440035140d003003820116007a1200180105040c00204450031104034400140007401d2 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 341411906 1250 341410656 341410673
    0x90503070203060f06150c0a06050c0a0e09010609090b04090206041502071e03032105240102060910091e0317090601030302071a120408030123060301031e05011404 72
    0x1300101c81d1003001d250800e100801c0f01042e0060031828031444c0800d60720080c1006101032072003aa0020014042402d001c3d1000c0c0d0702e07a000081820115801814090040c00c004001d0750480b0015111100c3d070fa0700e0540321401400640c03512030387c450342d5082e014005a803024040c0c0080e00008400d00000202240064070f841000d070401001780d07000c1002e00742800c00c0300380144150f03585803501c0014202503d0710107480c08041c030210303102c0504101c1081545900445221035180021802000a41c0080d0041e0388800042d40c1580960300038440210000150b03401c8044420321400e03813006052072510444000e2500000c0403400500200c140b1441e16107413a51990b0010480d6000e0502949181d4002c1c0d80c0300700503c1a1065030a090340050318842c46001698003040100005820034603081c038003006a0f038824041e0741c403e01183c03038142c0c05828080c24048119800034003490315690860b1580700c6000440c030180c03500041c2100885000a90a000d5004010003030003070b50302d0714241440d1074043c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 341413156 1250 341411906 341411911
    0xf030c070806040f020f03100e03070218040c1401050405040204080304140a151d100206180c0904020f0607140a0c05010f120e010f02040806090d020d0f080a06050409050307020306 79
    0x101d0782e020209201c003281076003082509503541111607182c414642800300b42031428200688a0b182e10f007100109030b4000210040c05914400c948009411946900c880d03400c0da419900a400020304550074054070342928030040039542d050410318206036032080014280d074041d4006407050f07000810100000c0003c0d51b844001404101c40c440d00c020b09140002c1e071801c0c02c00c140241000001c90103030203c0c01100d0142c180001e000341c1103820000e40741002944e14103080d2008804c0300301204a0b00401600461030902d8440000c2040000d81c81e5502009840489580c0d0070b07078032040800c000d000061100801d2242f25541a0181200c41507a003006d101118030783c2d0225060101c94092612040c2c2d014240c04030100d05800300140d41036a41402e540103044a1018800840c8006004140303014001071041c843c0706180106c034042c40182d4400c0f40c0301d103520340d074120204d0817003903600f05207900551800e43e00882ea00b200090f03482c3d60384001802c3e508a81001c3e03076980c00020300700055090500c04145d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 341414406 1250 341413156 341413169
    0xd08160c051906080a150909062f04030308040203030903070e07120c09050405040609060f0f0501051e0907110d0801051807020d0c050c1009150912020409060e0f030c07 74
    0x180418a00f942c0541440001410708503210342da45a91042c030301010b034002c0040c0c030b1101410403442c04149820030080003283c806106c5901e4094029030400d041810fa40566902d2440c4141042d145541c00c0c4e41072480a0400c0740c0c580010702000c1903688080100c48000e0052a40400303003401d1001000d441e030003864130480780c3c1e182480603184069810041d004211001914009a01e03030b59402e02d88000c00d00d001008012605002000008940d80d4000485041c41c01c0303800c0202d03998034420071031218405039a5130060003551b14091010310f8240c817410360007400703414142c0040071340e44542d505007042d1040785404604010014012402e202c0750144000c015001000268148480081d40e2450b021070024100503180c400c682c2040018050181c1d1084e0260107508005003002014041003414040c1e885507441100349822640e208daa00c3d03804072521003101d01c460b10740580902c8042e0242d00380c2580c00340d0702c90603032100742c000c00c00075a001180254007442d2224840380c021820104681d02c50b0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 341415656 1250 341414406 341414449
    0xf011d04060317130618050d031b0503041401030207050c01030207080c0102030a06060e0f0a0312020a0804121421091503070305090f0d020c0d06060803040306020c120301030f020d08160c05 83
    0x18034070b0b01c292a07224015200c0454242c5c8e564142c41c0340446050002c40300c019100041440e050040140000241c4141c0386d882c07200445141100c00110220700490301d000e810381d40b08000c1d200840d40280c1c02441d441d80944c0d884c5203420078142200342a0791080d00c0c601c05513540c0d8142041a0b644c42440300d800c030a0101d40151049400310005411010140405440c101103640e18520280c000c014456000e0361002c9029202ca60714180030700512a00300f0309680c80b9202480001280c10080755100c0c0f115404810100c4030500b540c2e005085401c55001d407600008000e001d650880170f51000307184120000e82c0d000c00c652805062850030156030f040001d01e90b61080412002064011641e02c0741c554040d40c42c0c904030502414030101400c0d40703a1005ca144e000c00a0088288642c91b0010181150007000712110705200e05c1094850344000d00c0040c050380031a201e0403006150201c2d052054074028083c0702c2c148101c0c043d400103e0300020f8812a40c0220f000002c01141c240b0880400d82e5010510b5070 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 341416906 1250 341415656 341415677
    0x1060b040b040e010b0f1902030d0911360901150306052505070219030f052104140123030c0c100501050f12150a02040608060f011d040603171306 64
    0x6d111607400745010707807814811002805115144200306480030b0039071035001840340804a041840c60b0369408807da6010340101c07068005100540c22944440c4205412840b020316805021202240b0001d03194068a54132041d07403140b0103481c803044c0f0340034500482000602d42450154020401380c1c8000203c60100203503420140141c201051360590b13134040d20071460408a201500c1c00642940d0801003024406000e0301d1b0a104002070a502c0c00554040c0c6d51003400404a0381c0c0c4800d008030b218030070f40c000c4108071002c5554480d030510043d1010100b11303940f22002c0c02100f8803080c0c004a840b0524128003140700040c1800c100720440f40b800ba0080e04011035410000818031441108640c42e0107402840702868186504011030801e404002e101131801e414030000d500301950061103800b001904240c0803514038a41910038840c0f410050712502c101c0500104040100c5040850060b4000c3c1e03940c41c004081101d00070040310828940d10fa440d0780d050f4400b6064042c18644d01b1000c108804100c2 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 341418156 1250 341416906 341416927
    0x50127060e01021c091809020406090504021903020904171e0c3702120d0e01081806010326030901020703090b040b03040206160501020a090501021905120c01060b040b040e010b 77
    0x405c130541e181c02007000c22800d5640c111002900e00703840020340140c5481c00c00504a5400d5001a0089100322080282103100342c4101c044601d00b40406580800000080380c0010303034450320004c1240c901017526090a80b800090b0003c542060b00d40001ca00d4002030100c401c0b5400d115540d02e01080d002c944d41030741200c0b1b900c031005c0841c92500909280a18480c1025540c460400511a0080f0000c80d4401e01d00e41000812038240380080e00d002c2841e90300810075001d030642604455048031001809aa841d40d2141d8104070b550302c42449180b0712030814145942c150300019482803094600159595455140040804040303900080c04c1c3d4a060205009802c0d84608032504181c04440e5962a816908512441c0d01442c1400500a40c400240d80c0f98494020b9500c03411640240c0960b048180070f038688071a90710180d0401022608140300c05544004800c018049014461000041e034a03107841c00c04c3c9940d07000f508018107002d00030804004184000c0030340c07805070030492401801e0400080 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 341419406 1250 341418156 341418167
    0x2703010603210203070c09020d0b0603010312030506210a05100b060703030b06040e190f020307020a061a060406110d050a0e01081911070c120507050127060e01021c 72
    0xd030303141c40d4842c2c4642c005840d18030070400e450505400c900450500d59403150510025032048524994540c103003040501e035403400c00c0c1642d040300c2c0c009450f0121042c2c0c255044004080c001c22050307200000c504a40220b901c8820042c103140030741c4005040e041da107070601d585020ba1030303c0c020400b40d00700440c502c8203445080541d1540d42c2e041c200840d810703a0810000e0458040c030f40114400404000401107034400768038203800381a0800c2c04c1001070591002c60342090b44411a07029025a20a05480380021019800603080800c85440500c541c18070740c0003c1e49a0307210703902900000e0382004402c500c0c0b00341800044142c1c181030404a18048480c80d024101e44038500640d4188400361001404040300c6075568001c640c80071400f00040303880240c0d10076013900804016282c410700700501140c0c0c020b2612050b008150440000c1035032078034000044401d0204042c40d44002c00ca040604000395128400c14805844107494485021101d0b000092030f0075011143c072487d40d00d0500d01d2044098201 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 341420656 1250 341419406 341419433
    0x609180b010f0807090806191a0a140406050604030302011b020c030d050304110a0b0c0708030f030103060207021c08190804030909020a020a080f030a050f010b0d05130501022703010603 81
    0x1810114903a130745441e42600c0c0506036030310503440760040c503082041100d0703030008100c601d055106082014501083c0c00c07031205107070400d1180d00070a00344424002c2000500b0914280100140b02256440e1110045696a0019031040700942c6d100d4089603e0341400304c0c4000c49007034803403000381940c5401e10000b80c2c0d10301c0d924200009004000012070180110700c16030f884d180601508242a90b81d40d034024060590040107644031600036284003280d0310324040125410b12071850a15401e46c2d007146c40f000c000f50300c28007040ba4071152903007082d03605c0303c8007a4640003800c0c0100605600d41025102c00d031059041c1102050410000c6003c210009420059031002c0c0e5420910050310349444000c01e03031420ba15042c01400d50710b00410f07410850b450840003540325815074007060000e619002c04040e000c076002c1c02000500e110600c030010340300c00150320155108100c02103003403c910f015180c40b0300f2a0700c140420000035a01440340c8485407030440d200000b005044d8002c014540c42d548a01001e8000d1 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 341421906 1250 341420656 341420687
    0xf03120a0507080c010507020f010c05091e120a030e1f0f0f09080f01020c0106090207080a050a120e0309090609060d0b060a0b19020c18060f011106010609180b01 71
    0x480d0342820f215228064510041c5904020403a609240300081e6440c0c002c104400f03540d60074a002285d40520603000c1d15250000603109018a203082c014074284641062180d94112060240c40c0f8032036a07007004010540e90080c0c903020f00c000c1000040c802800d0300025001c20400c000f59100c0070b0030707504c03910400050340c10307243c0075100c8064140f003154800600d03400103240303101d0303858410310001c01940104400b0000307034000c106141d562014101603009450001d841c9100601c10480c0382c900a0340181244041480c00c1c1c8500c0112a0200c41102c0e00d201c01c005082c0d0000c03c2100c081e003040d1641540000c41254110114034003800051990211a98002c5c52014a00c0100f00a42c48a02c0854040c0519021403034031102d4a00682c480c030a60b001c2158010306c220380e482c0302e083c106090700f19006000303516416540c0d91440180b00608400c41120360400c40c41d007280400101e020310415002e0491035440c00040e074034107030095080782507415112858070301e0031840c81c0c030344d0707030018040c2e04058070 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 341423156 1250 341421906 341421917
    0xa0501151d13061e02030a021c0b0603060d0606050a120302010e0c0f0f010e03060903091e060d0b01020a0203070305250503030301060e0303121303080a050f1b0d090f020f03120a 78
    0x12010310b51400b11380c10f1141102ca03d002005010710445540c018058404a008503c0354a036202c2c40c44100352040343d00d030719803c0b100c04c0000c181c0e141080c603202ca0280c2c0c02107002003519a50784005ca030b4003140c660300100d0600c401c55500420540e0a009102a401d50740c1c00070460202d0800000f0180c40d07204044500c180100084030100343d00803100510030100040c20f940c141e25011103103076142e901c58201c15220b0303865080d2201139500c2000940f0701d1171030081e00440c00c0c0428010044010400c0102c118154880c09081100590b000c1202001443c80b880181402004039601e1902556081b50822401c1030000c500340569103002082d00d0455155107800f5508500101c0440d0640c480d0b03c04c2a420704020500300f211342669100e2524000307100c1c1ea68103001e42c2d035a2040000f00c82c426595600d148102d0004101c0d144640c40c2c42c00140704860a22510700030784024202c08481c91008100c0b465000b40c1c1c2c4140651400300300600801d0f02c00e80140c40840d01c003090b800794034401e1502400c103000e03 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 341424406 1250 341423156 341423171
    0x312020c33090a090510080601060903050309090622061a04080a060f0605060c01020a08070f0806010e01200f0105100302010206010b0307031506050d0b01020309010e120a0501151d1306 81
    0xd8030800944000d144202040010341800e0001c0d0306c5414040c082c0c2a054841c1d03000004282d4452242d00302180c1d08000950f08062800080000c3d108010b041c1036800b0b0703500300500340407070b00c030050240042c0d00e410000680580f4000c141a90940c1c0c81c104103042c40340074001003206210120306814025804000001c001600020a000034512500710301c4e0002c0012800e451900d10540c0208005075464560810581c0d0303103041111840b03801c050040c001543c04022440d42d50241c00008203900c01410206104042c0d95204401500c0020881c1c4540d4898100b03068042d40070722455030080d81031032203000585d086030000307076a442c010300c100d981d04c13440080002c0c550340c4203031300600b005103414007400010380ea11640140140c1003d51946811460f04017074100b03941c0004121101401c040c1c4070900c0382e1080c1020006641d11548103a0542d0055014441c00a4003c0c400c0d518200080320006102504000400440101004601d20f1000401090011000028a50010040e4480307804038561 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 341425656 1250 341424406 341424409
    0x120f050403033c09080d090b031e0907050f0d021005030702010207060f050f060a140f011209030c03021509150405031902010618060302060a0809070312020c3309 71
    0x381e40001400c040d4982c2c9084143c40503004040c503244200326944030840161107540783e0b07858003540409800440c83c150020030001c014607000d168002c0d22003e03068a000c4c8100702010000d80101d400f0003954000c80742c00d0109103407110001070780076002e403100c0c4280c1030540d0200e0200110404205c0c01d10401200045600d07100350119160b0b103900003002e01c00c505800340d0000150509403006910307007000c0000140242401039a08003141c10070b00d0420500280300c02484000305400320610304005007902c44c0461031585008221b030380741c80782d80c032011500f21504009041041261008403412140000d04c00462400601aa001c1500d1440000742d0340380d80c61714501d10312906488022806c0c13600010901d5030b8065000342c0c100c50702e042c5011b01c0949100a04000c40d20070b400000c3d030051080c0018402c0741d104003c040e070b10a40310b2040700c11107602c0f500c440106001105603480164481c08040060341411124a201a0203494164070181c40d4085240070b01c0012180c00000144c01141c5400207 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 341426906 1250 341425656 341425697
    0x6060d0c080d180b031e06151602100807090501030b1210050a050a090b1b0c0a050a0302010c05070b06100216060504050f030309011b020f1c120f05040303 68
    0x1e0031404200e41640e6084032025114074444412680c3c0007a1002d400580030201e030b01101d105603c140100010107417501200c0b14140000740001c1d8001c3c018440761440ca607010300040072080311a0144001488082c81000031b08014860304204004c3d46005200c1e015402c821075209030380007420085140c1c94400c0210f020302c01c854020101502ca0001102848504e550009004400140040c0003603500d00d40c41c2c0b01501c0c2c125a00a145456080008000e03100000314440c08241080c155803400d445030003102d1401d43c6005060341c2a03005815003004054091061010701e00b66414014182802a21031410002005003060b01030b900380c18214404500c00e201074005c120041051802e03e9444070070017405508103004041c0a1124034000d10820f10780041981d02016050f0b540d54074138500c5800120303407803500880c221b811038200e42008030507948508005008400d03802101d0002490303810a00201e01250001405100441ca6030360030880d8408105d40c2a0381e01030038440510005040700001 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 341428156 1250 341426906 341426909
    0xe0910020d020901031a1005090a030f0305120601030b0d230102180306060a081c05040f03060507180305120a020a0b150307171b011101060b03090f01060806060d0c 72
    0x821500c002000255030310346a003e001250402ea030200a80000305030103c0c2c0c5892104000b0b940040381c501149080c9110754020120b140b40076000c0d00071240d480e628811841201c020880119201003990501c0c9120004443c0e44080c0034682071186000c40000700e0f201401044002d0b1803184440c06184407050040f000c3c3d0148500040215910003a501c0760840c84e04243c1401c030300c0f03402000081965071504030700440070b64400301c02402c02100a4011400c0014103c1b0300b81092100511000079074603c00540e0700c00541c000d1401281914007044010001422030b000c030b1100803490703042030000c038100241c403e000000e12070340980d5401c24035030241d01e050071820000f880003d0350004c0000c0710180012145146905604440c80c5640307a144003501c40f030500304414a558000c232203604100c104051052044541030407e120030042ea81503860940e107094128a013181000021b000c0351800420124040e00c43c2034000b00990f609001c01241c9500c00a07100d0b0748038012a07031411b010300c410921001d0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 341429406 1250 341428156 341428183
    0x40306050c07020a030b06011101020c06060d0201111f1d0a060c12050405010c030b0307081b130e010504150b0a090203061c05150703180201110c030a0606080607020a0308010e09 78
    0x7204c0554034608808803000440e0480e001440450000398158014001d0707a482031035260190070301c0d0359094240544408212010f90402010000c1504807100c1840040c01e04185814200540c090745a000c1064036041e90070f506454200280d00d2010440c041250311210342d010b00c0105420705c01c001e00700e036001d4030305040a0043e8688800d01081182c1580800f8114003503840a004516200080545a100c00d20405645030812114141048103d101f10300002d40c0007442000000ea00c2441c0c0c000704c5500071410b5060f41c0d0b6a006110510049400b800100c0d42e4802c002d01121980801140050400c0d1080100c16900400440c0c0159100b035024041d003941010301c484055100d040440d070720450040c4000703120300000d011030074070361007130240350741c01041d045043d000f07805d160b0700444008001c5550001c0c80d01905a40d9052641c0c1841032002607070041c5404580107040209240c00c098010f400d0390199030120308408006038120b5090741c110b51181940d01b505680f50782445060440b02078401 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 341430656 1250 341429406 341429419
    0x60a1505100801031a0c030a0906180b07080105100e060d060e090318090606040b13050405070203040e09010212011a0403080d0207150603080d0b0d12051b12040306050c0702 76
    0x1610766900c06101030489020740c402c1ca2507421540741c503440d02070056421034403e56081000800c2450305030000350503e0f221b1040061590b01d002542c0d03685165401c811a10b0700d502000380101c80d076120080e9400f4110880e44406202101c01d406041c1b0342901c3c0780c1070300406000c10b004140d1042544004024010301041200d03034075214000c10384a0380840e80c0b060506005400100070b901301190072500c10140584400d141ca8201202030242d0340007481408591441c02001041c00c2c0c503140503040c003403403441e0002c40d00e5070f088c4802e10000385001403900d4007580c414012203040184542c1d1281c112250040a0070884084100c107049034400d58001070000d08001078500707000c240070380c000e2600d07038000c00384984101d8441418105032802840060320381c0c2c40a1004140321481139022424140005000741071101d0755a84200440c2045c403403c1c008100003140d030001c0c0c030b08400210240d94104401400d840c41c9150701280c114011404090031041c0d4401c0021240307c030703403412108100c2d0004e028 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 341431906 1250 341430656 341430679
    0xd0905040e15091c030c05070f2108061002010e3a020714120c0402030606040e04060209100809030d15050603162604080703021203040605070e010f02060a1505 70
    0x1160344c0d95450242c141130b103c90a15245405500c80d210740807080300310341d83d542d151100c143c40751040e2001c4500d058964031414400f15103881c02e014034110b241511900c400384145840c508010040500c450840c041d641450459a1040c8010030303d02d4042d0340c030705030b265002160326041000c40d10420000b4244510074180035005a03400140c03441c01c488481c0b8081c50041c1108042c8401551002016112070b44410804483c41c0f44c2900078640c0503c0283c01c5908007070741d81c2c14080914200742c4060341c80039400118003a150415958034030550070720f420660814240507210315503034400d03040301801e0300faa5219004046d4000c0c00641006200081800c1d4490900c01c5610200710700000340304003c02d1101150381d014207102440803002524038890515655916151041154089002141107024521607c100d00c002400658000c41c0038010006480ca808007010b40207090b103000480c188549140d04000d0950300041407548140c0403c00461110f034116038400700d010307540d00404c0d80000c2005a = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 341433156 1250 341431906 341431921
    0x90a150906030506060a0806071202090d06060e09010510030b090102070b0114030106080d090b0d0608031b010b030c0d080d110d020711060307090b070f02060f030402040b01020d0905040e15 83
    0x41e5050342e028006665094850f072040003401e181522543d0f9081d0001400503004d00e0060104a01070032840c00d0161030300030340e2800644260300c007410481700c141d40c501081c480c102d0380080c5550300201e954020000303406c003090b958200ba01c041c4401000034070100e00060040c482901900c6640780e0000c5950102d503103500c01864030788aa440178034081c1d841c0c000001200203002490303220741c0c0001d0315011070507400c04070400c0c140d40c4504142c0e10f030070351602000615420100014880b20f507109801818245101c2d5560382507510f00c0c031010b8441ea0245441000651354070010540459100c548a55220011400c0d0400380140230700014240c000031400401e0072000e600148450303440f43c580307064484046020460180029210040091501c660901c070f0b410320003000740801805141c00034204d0b2581d078002620780d071000c441d403041d52402106020841c1014011000c0c0d040d001d0026000341c481c0705000401d421003506c1194031903500c40c0603050406800744400b404a1965041d0580c9030300e8070b00c0f07 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 341434406 1250 341433156 341433161
    0x1527090605060108060d1e0606030b0f16030c12230403050a02100618110d0e0c040c0f1e030b04020c0102130803120a0c0306210302010c030b030606090a1509 69
    0x1103480e40880d180c2d0000950311b207000d10440c0c030f205500500483c030307204601d01e4084400314080021a91540d5440c0c0110204441c012120303c60b1164a071601850b20b804211007003103900506c401c50500d0700306040340480c01c0c1c000e24106200310b45990b0004d00011841030f90800042c01c0e4124840394008142440305042d44500204000c420716000ca82c8c03803032007100380981221901e1180304001f0101810420301e8026030b400560744640300c0c80d11141800045401d072411100c1d00080095154402c1e621920f00d810035002d030841c4111241000c00a001d50500040e00704c074003550007c61440021040b0640442c000c1c0c0c030904020a001e0011500c030f07a24415424001c0d405541d010403504103a01001440f0400042110b6034031100c40b11091181e201c85000f40050030704a00028145615160082407600c25110560700350501e0304e50218110005060183c210b8640000c07250825040100c2c000c141c0e00d0020b071082d042402550014031302c1d503900403444024100b0056003401190104030004125010382c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 341435656 1250 341434406 341434411
    0x109120b01060e0303070c0306020c0c1008010602100612020f06160f050601090c1709150a05040b0603010515010c0c0914090d0e090103020f011e0f121527090605 71
    0x780c80e01c440321078010f4105540d0303000d01d0000404800303100c40f090000a1a030b0300905503180405d0b0860300324140f40400038028102c0e081112002511550040040981c1009210404115860104140c90130802218a04151030350040d004000c10116002d207511580c08441460041e40c0030030014528078a00a1507841c2c5134031040d940da2080d200085008592481141c8020640d91100f03040906c5400e488000341400400088190243c801904c20344402041c0c0036119140d88900080c1c0c40c5020314000755121005009a07020380c0c5040c3c1006405113a404110151030400d08240040c00c080e40342482960003a6004200350700c0c100b64180604442c5144014055410f0405607980742d5418041110181400b21005511101440040001d1305104204019501041c581803611595280f00c0c0e003001400c00030210009803014100000c5654002040781d170b584880074003403181c90041d013001c80e00c0c11814000d4100308203010001c800c413404c070004400011075240d001030201089900300f100003880308 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 341436906 1250 341435656 341435669
    0xf08040218090709150f060c06020c0627010b0139030c140a0f12030b0d0308090708070f0611030c0106030605060f220c0e030a0f2109050f0109120b01 66
    0x40000c1501c0c1c5c2d020b00388006003a1000080ba5100c400e04c0c0c000b0484041440400940d00b02c0e500304200125280c00344421440380b0001040d0407408040341d84540c04044d409003042d83c071640f400f840101107a07403003190601d060195056009a440341c07440f40c6c0d04250384070040f6091030700d82c4d800310900f0582c0040024080c640103842640d085a800f600c00b60701c9010404000b0080200b030824480040d401d504007654046041c9400550261460003040b8070501205068000c03c50314410480803007020080c08000e00701d0b80c8042c0c1945c030b00d88280409605420300a80003445200d00600d02d0300300d8200183c2e4509151103000348241540da040c10401802d0541d80c4e1805000854101e20301420004580440d56004034408000d0b00100d1489200070708a03054007004015001412000030f6800300040c1c001140038103da24026511403802e45003034650761502403c0c0520300b07114994020380150140c41243c40c150b400980c0f0302c4400d030040fa0800002c0d0800310b0b008004155443c140300014480234140c650b07 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 341438156 1250 341436906 341436911
    0x21e0108070302030a0b22150608060d06140a090c080307030804080304060908040b0a120c020c0d030e0d051006151209080417030307031d0a0312020d02030108060a0b09070f08040218090709 83
    0x140f0b048c120a640381d6034040c55010a40707250114499007000500d070441c036405450002254015030506403254001a24402011501c2d004040244101410800000c1078901c4c0110314000e81c40d60083e160200040000d05040c50220004003440b9841d0011511240c0c0303c00256a51034860a440d0710941000c48101c00144501c01c509201400b0b07403082c6038416000390010255042038504010031a40004011410410105080320458460302c01400c9260f1040d0058a2104001200c40e011501c01d42e0105500c8242ca60002e5006038024400f00182a298040070501165504061320203105990009541c1d43c40b603907441c074002c040440a14003609460780c0c14040180e400071907100000d010034001a454121403414000a40145c03100c18030b40c04490805400c142c04403060400300e81013603000da041380d0000810480d940f80c0c58450300700e881200b2500700e140d6051400000344004401820f81c0300344884240400e055584003d40d80c2c1c070410b62404620030074038000007015201c8000e4850065002e0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 341439406 1250 341438156 341438171
    0x1507061d0708060402010c08130902040603090506060402042904030b0c07020906090106050f0c010f1404030219110609011710051008010e0c070c090e060103021e0108070302030a0b22 80
    0x1c0380403d5050286405a542410248082d201c0307507410fa000c101c0c00803082d016003000186001c1c2e01e0001e84003d04171510b00050744141070502030304041004108522075403040100303201c05100440594245000341d941903c020303000d181c60381e002d40b042e41c0010303050002120401044510050041a2440c42541c1d03200d03d0383c13a02410b000c81040e00703019450100d03209100080b14850080090b1100b6a4100c0003c43c03e445101103610071108284034002e03a40c240300c01008141a01042100020f072008a0701e900d0518490316103050740c5580c100e5080c4900000181c0880c0c030380c450142045500c0c9801401e4009050001c81e01424007200d10419000d2140c54860f840d1150260080714101e036095008a07070203550703807940104940d0240a0480c1d9039070001d040850318424500c240098981008000c001d1541580100042545011851140144007040703000040e64464a6290081c2590402588176180c01f98034001900d148007034a40c10a03480f10380c0780041034484038041e5035140e20035002c22800 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 341440656 1250 341439406 341439419
    0x708071a0c041d131b1212020c01020a0c060804060906180302010501080c030a0f080c07080708010b1f0806010905041107060b010c020d03080405101404030201060501050a020a021507061d07 83
    0x85400300c0c1c0d444c0b00f80c200150b8800c0412911001a500051001105001e0170303200c0b440850b12501d01d82c410707120540d03c020340c0c03440b00e42c042201800061090000700b01021440d65202e418400038001c3d0002c01c810744010404104261300301071300c0c680c2d1000061007400c1601c55580410071114500764010340c01c200001034041000308140c25500d1002c0c020340700b561059100c1c00c40340810181c003280c6031a07003040111701c080c0050001d0000b40003403002070300c1e03a940b4108945083d0f40200d183e042c07041c0d0054040844c050f0a26190500740c0b160313030a00807003a50352800162081d10b4070364440c80d0018106002c000c0061600c80c000d0003640d1040408002224104004440492071280c00a401082440e0b440000c00d0041445075406407041084a501d1581c6c0658402614002710980000e00031f20070905c001c054080c02840007405003031901500303041d90090000e556045013600a802101c0d02c01c10340c02c510303000c00d044840041d00b00340c05020301aa1514141d80806a00240c1070b03940c0640074021905 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 341441906 1250 341440656 341440709
    0x3011d0105010e0a050402031312020d090e0609040b151012110403050304051c0807120e01080c0318030d0c080402012c090c09040603050718110708071a0c04 69
    0x3560b0020b80104004c03400c01062000950000c2e01d2030704c0300d016031922078000450404915030b840a0980c050040c0c01140d1002500d0400c03150000b04000355102c0401c501910341079940d5a01580100310310000e80c680c0790b200125100c1e90000b03550001c02c0080c00a0041e90005009400c0c0144100300700b10004d031007903040f03005000f10b000080041c2c004110402c03e030b1810404441183d00711184940003098155030b890f10a03400404101da40f500d24100030b140d203981143d440c488420003820110034601e0a084400075a11000b00550312008505081c3c0ca0f40060801c1a100218a1702074100954040300c40081e110810807601240002c403d040030180b600e882e5a03019100290b146414048211038000f0000800030090030641422803d001d154800d035100d000d07590080d4018000f4040d41402c02940c51445400d81d2000302d00f55050020504007040e0080c00c070740d441a0001c502c0d98481d1316900e0b200c030650140c080e80c0454848503400380704004840740d00501c100c402000c000e074243c4031552500d018 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 341443156 1250 341441906 341441927
    0xb030108072c07050d0e01060e01050609090a0e100e01150b07080702010309031218060c0201060501080f060a0323011d0309012106091a030606221103011d010501 71
    0x204466001140000b0001c45030040c0c100030f041c10000d0030071a101041a0440c0c10180c40035444d82e441d03040030400f200c64041c03028050a07080c0c8440e032520b0001c1c00480c05840000c1c0c1424411603450325240d0159209010001c8080403100c801d1180034640c0006901a2140c500c0507440684003400000312014084119a812075218403400d00b880e5858005500070040240300b40c050000c045400120320b0340521600e140c6513821501140d9100c240c2c144601100c46103d880819680f4102d002c1c0241d80c0c0100c0400ea02200e0b00101c080c044d0755010100f5003801080c0d000074443c01c403810351000c202c0000761015520300c1503c03000b00103c449110901e2082807007a02c0c0d62001d904100403a1210b944113800c2c030001007400b440710311510034109100d0002c42d8000d62012045542e13a40c50403020104400000604006c101c0041c680e509001000030080000c10044a221451151421185403030316009500d901d2006940582c40c2e6139101c0c2ea50800d14030070139400103116020000400c1302d41c081c40b000003 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 341444406 1250 341443156 341443199
    0x80f071d04020108041e0c06030e0c06040b16320d170606090a03050f0a11240a02011b0f08181002131a04051516020f01030b03070b03010807 62
    0x10303400e842d5500c41800404030103e01e440117001c00d5400c00302041c110301f40d140040400e42d9001846c0100102c6003800c044510104600c290010001007001d1215141918031043c401090220241100e20300300902c5202002c41c8030b49403030300250900c0100001c140c0031807502100d03400d44101c01480a0106d841810740c03075901121022110100b410b6050404c090710301440042c121442c00342c1c49071101840d048050194103001d501031754100c4100094400d0980c40c0280650b48601e040c030010b0803003d00700500035030100c0710010105180c0e03099031007500818604c1c0030441070201c140401941c000e0000c0c072000340b060080751110002ca44200c03600400b516248a955026110110744050384a02030f520810301c03170044808854010440364045034080b100b40e2026220290b545207000107001c21000c40c0c501402e0820700c01d0004800d10740794000490348035030381210428100040c1800590003000a10040c1c2c0d0148540131000c107a01d2200c90003103040c1c1c2c03480c800b141c182c0c039540c2c0b0148440c90001c90001 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 341445656 1250 341444406 341444417
    0xf030501090519050a12021f0501090f060305030d02030c0403150204090e1902012709091103070605070f0c120506040c081b090405011b02100606030b01051801020106080f071d040201 80
    0x140211b40c0d0b060000f4440000382c410740700009100014001a100040c60088159640300010080b2104034030036041c0701410400c1c00d0194a1441e03d501d07071240517654010703d07880d40000c0000c01004407501114003840d8401401d20540800c011400001c0d0802d0044080c1c5d240341100940260034001415208030084e80c9242c021601994011920204840d1460f0742d41d4495940200b901000d42c40d40a02030040200000703460320031404d10000411000400301e020fa04211024050b0650080c03c4815640e0020007202c0300094610b05401a02243c5d400051138101c0d211040080010110398036018070b0046180c0b0318842d403944111601d4000322089001d460f100c0c6100844a410540c1040b64824040d00c00007820140d010381c50f4220100910075500141c000f561340749099120b6114640241180d4a0104011462640042e000d0b2007000313070840c1c0c20803030b02c0c0070780720141e100350088000b0300400d10580300c07034401c048200390303a40400e40149650f008036050001b07243c40147c650144269016500d1 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 341446906 1250 341445656 341445673
    0xf03050c0d020105090303071a16090b090609090f0f0a02180f04020409090b0a05010b0f09010c0c0305100b0306131106131e06021006150302090303040f03050109051905 74
    0x1040800c0714580001c9050010174005001c481c1d800748040c05d10036000f01048860360201462004150360010f00b400d44e100350400000c801c0945c4204800c00b540c8208501301e03507400c44500040c245004110f815903000500e002004040c80440501500074000181032907104d8580000b400103038005e0420703080c40031483d03400048a903c1c041a00410318240a080145001d40b10b10300941910000b00060f11410000d009001c202045846501c0c0100b04003c5128101801d0a591540074840c1d52010b070304000f96030090720140291001460300455010046614082400442d0f001400052807007038420f00403034000940b40b040400c41040d1035a4041c051003800f89481080000940008041c040c119110b80800f01d0b5102c01000c0c030119454016481211491402c1d0000303182100c4c0d42c052581c420704049040110030004c8181081c005c00c1402c002d078444602c1400f092460186604c03030010468000030000912070103502000055004405503420200c50100349031031200d0703010000b00594011b001 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 341448156 1250 341446906 341446909
    0x3180c191e0302090c0a050405030709090320061503150702010f110c070504051911071221110d06090c030c02150a0c09032f0d0c0b2d090a0f03050c 65
    0x1010315940c6c50405034240f6031140e001c40c2c035050658012a1125586a10110031715401a4031200980c5e4214810b1031a003042043d25500c50b50064a150140c204210325000c00b40c5d401c0c000c001d41d408104400c2c030110301c1c044400902800c030181c2c009061f2071901070001005c035a0780781107420041e80388000b0309060345081d00b0b10004150040c140035010303180b181d11100c0720b2a40d0290084025150440319101c26040c14400c402c1c51100004c1c105001002400084100304801440c0054040f0200001c3c003188400b40002c0174811040f038100760700e19003207010565500070ba11080480d24256810040500000000d82c4e0307031581400340800d100e1400300012004d41d103c0e000b40b44601014501007010558950355044144100005003201503444650b8001d14592146c440e040344004075840328241c1f035281c40da007905c2c000502480c80c0441c00020200003400482c500c1c2d0040d202040300c5803032259002c122401640e04104074844c81100b8400000408501006c2d0901c00c0ea42c01070003501300c40c6ca0050 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 341449406 1250 341448156 341448181
    0x303070503041e0e07050a091202030d030509010615170f0615090409061e0c08160e04090b07120506010c021503070e21010e011103180c191e030209 65
    0x1000320b2244200d220046107561200710194005c5c840341d20340c3e5442e0010884050309220302900148000038081c410070026035000a2010140000b5050025550716071101250242545400901c0300c110001040365007154015030006007105500030803404ea494145803620040070590300b17070740d0100d00502c0542a40720f214008090b0000000d00000700803026940b80000e83d80d20000c81d5181c2948010f08203d800c81e2401900810400307450701c01e40914005221096041040750948208801401c6011090720f070780e404582680d821250406481c07820200083c490003c11405042442c2001c001c1130055010b6a84061401c1d4018031030454000144003901c0c140d0170003000c1d441001425140e150080d11400720320000d080b40170600c42c42c80100001c155003501c0e1b01481240042c0e1406031102802012081035036000f50101e1072003100c0e416050600303031800f8400c40070550f01117030070310040e228000700d0040740741111140c809900082c0c20410340e0204402c118800079400c0000070b00000c80004912 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 341450656 1250 341449406 341449439
    0x11061e07030603050706050408100603050d0c14030c010e0f07050307060305090c0a031b05030303010308032a0d05060f09040b040b06030a0c1d18070501140d05040c0f05030307050304 80
    0x1d207000242540d40b500ea25180098960100020602c00034040c400d150052001504541810000b407101910711758613142d984008203610400c000d0304181c020700304601180781e5610341c0e00440031282c0f9001c00d100014000c1030202c5004030248642c0000060300203010480c10708451004003c0d001b05850b100b030a8002d0705001308400c004d4000c08540001d1652100580800745015036110740c0188401036080e10410f40e1908079500c40d80c030a000410004029000700d0381e00140c00184184c150f40300c0340c2040464240c1880310f4802c40d10110b000070305c1140560010740300c0d900c12254800c5c1100349a00340a42c410040d900079126001c0b06000034003080819104a400010203411a0703c40b20540c2c032003c1c2c0d040311a80100d42468030420b034048604552808064010704c81220856042d81031500c07207a40c4410921456046c886800e040d0b0422075080015591445007200052109152a18280070507052602460b401d00f9440c0300080b9050030000300390341e0401d500800035413820341056809545207045 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 341451906 1250 341450656 341450671
    0x6100f0f0b1803010507020a17090d290c0d050a050601080a1a0303040b040f0506210606040e130201080708190b0d0204020408100e0102090a0b21010f0611061e 70
    0x40d002d15105032824401d05200740300c41d078060a607200440c5403000500800611040c0c503c1000d01c0600c40c0d9036654080c2c009030661110b0300307404030010360301c054041c408401400342410951804002c4c1c161100c0c4020302e031428000804020036078401003148102c03881561541c1c00a51104002031014042d6448000c045480e0000c55001181000002c1d256a005421018451401143c104202280c140443c030280408940680c00c01504d001340c02d800d680c07030094080d01c90300d0300d0300401c1454442404481c00344c42601840c16039840c0c43d01d04000c017030f00100c2c001c82c009180d010000324402e114001c01030040e0413200641e1318095052a244011d08500004990310864203080180107035103030b20040c002010780001402c00200303c842032004403000080014640e900403c05210b5554640e141c40d019a402a550701342c8a5031341606900001200c1e0328003020120600001140d03100010041d901166915903034002c617088a40d500c240c44600a450b0004100481112152852021000550301144 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 341453156 1250 341451906 341451937
    0x9040605040e01090309050d02090714041212120510050f030102040e1326040b0d0213030302010f18051207021503130308071110020a0c02030f06100f0f0b 68
    0x480344009000c8a800601c85485607542c0c401e001c0c02c164004412100411080f260401e0b0340a140e000b140c1205c60082200d0304110704a51010b11550040701602c014200540d41d540c10007885203400c481c24800401180081841a240052066020b004062060700320300c1107016090320f0103050003400f00080c0030a940c10f540a12000c42d10a0b10305051a2103440c7c010483c1124904034182065020328061100440c0c3c0804005440d00034100801c0f10210f40c10307250902d6560ba0003030072440c0280101980385005000580c00001030550542145614070051801000300e07001c0115010b29100d0515802042c9400003119081c151070105c01030710001d40064509145602c900300312200f9603204541d2002d0500b411000c000c2807542c800c200507031050280c20481ca00000090440d556503c0350441e007100280c00089000e10580b10346103000f4900e9000d002c40e031008800f10f51994a6034000c440300c18400d45c850000246000c445d83c0c4000c2200c40240c000718000e070034100e50881d90391050003050035024 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 341454406 1250 341453156 341453159
    0xb0d02090904061b020d0219020a18140a0204060e0405040602040b03040c0e0c03061c111302040e09010c12052508041104020307140721020a030e0d0c030206090406 72
    0xc0340d101c0705511951081e100062503400480704a0119540a0618021544542041d200042c1c0024a0440d010105c1c41e903812448500e10000b024014140c100204c5802548085203181a980d001078141d18100d841040d904e59a900521040f4082e9100e81000030341d0810300c011150400d40d200303a800c05e004000c09403405440300d80d0100140e02c10740c3e045412202038502001040d8000341e00d5508500500e280320b1450511400141c1a040c0302c00703510345002c4160801504112600c074444400c040040e00440403038403002c85c140000d40280c80bd10000e0f4102500040c004032041c0b28684114a842c6c03600c81d045055804100c0007442c0c005e1014000c100300030b09280800c440d00c8192403040540d90b403548068501171400300441505115254000d074010700c28441c400380c0140d041506282c04c0c2030400c2d124121030416004905002c07240d84120400c50440c4c0740000c0d8041050620f42d0b000c2d8a90b03201d4500e034402803000d440020a00a060081c1e00e400a2005140132001400440c43c014030220708035 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 341455656 1250 341454406 341454409
    0x6040519080a200d081207030615050901090803071a09010f0906050105100c17070222090311030c0601060f0e10030c0306090209030304211e030809160b0d0209 70
    0x15501c0b24162988400114841e40340d684142a83d0781c0c1c83c10555a560108403181d440507817900400080b01d0008400c0000609001e209902c0340000b041c20300100c030704000d5405400b03042c0d903005c405140d000032261000414090400000c440c44039a0100000c04003000d8482083c1840c08017629524031552162807e0340108402e0050b0400c05020f5040001c895140c20100310340d2185ca0000760080c4081035131110003150400f2a03000050040d2019665511036900c0090701c00078000b078078605000c075103d0b0040501c403030300d034010184607100307498540b918815200c0e4070703a80c0e000c0c00e014005198003500040c026070348182c198820720200c5051200207412810002050a0014804e00000039610b0b00c035070352a280d041c010b00005000c2c0c20000c40c136141e00720010940701d200e50702810156100c4000700f0b80e00c414007420314940c6d00360080c004d80b0a499981222510358040300e44281e00103043c00c0040b0f40c4507500801c0306032a4488842000000600d482440b104c190071a4042c074030143c0c2c0c2400070b400c99 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 341456906 1250 341455656 341455663
    0x2090414010e071115040602180111070b030907050d080403050c030a0c03030e0a0b0c0c030d0e06030f060a030c060302030a05060a06080f0403110d1806230c12071202060f060604051908 81
    0x6d6226000258a409403080e110002140c20803905041045000c070707406030380340040b48640540b411820f010740d0340c0d0f4880c1c1d10329140c10400d0780016008070a000c040810320030403901620541b4400c400780c0d40080381d81410503545240392040540b1501d406201040040d004103000e41401202030b01c5108040c0d911400c40707070140c0010421035907503088460510b80302e240c00c1c003010b4091816401c080c0403001425003c600203000040c0003100100550002c02c0c2c1980d00c01140c0070082d035004010000040c0c079250010082d4005540000e1302c1c5080c48049100c1746044411041502d0746547d9a0b030580c0d6981803403461000c0c0140040c2e0510048140c289081c038424800340c080401d058494503d9000e02c0c00741a50900c02c039900100c1001303a00c0402c100c556540d03030b826000c1c403940c5554542d00c56045039040380c03e2082008805055236000035001040001282489648240517003d542c45980c642c44007941c2d4080c1122801d501c01000c00c030034080362074017100c0a8150340184000c00009a00c5a642625 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 341458156 1250 341456906 341456911
    0x112021e0333070f0504030602090303070203030a0216050616030324060e0307170c0112020906031e0f060906362d04080706150902090414010e071115 66
    0x1c0040c10b0398180091100c0d034460540c000646107460080c03000b00e018002d16900460000800440c2c001490040031fa40070001d444c0500d4004007941c1d40c500840070b005e50f03501070301e805408141c2440d100001c0c103440c000c02666007079201500c09040020550b5811401000902d403140b00070780b000d6900c4c0e0201e080c010b9042014000307984490b4189034013001090316050700c0c2c0d800004119142c40c0c800c50300400c0801c1c1401710900a080045942440080080c042c0c021441107940000700401008100054504805c4c80c0c0324842c0b45820031600c0f03803581c0480d00d48d4202c40c60740d0041a80c0300444c4c0142062006a01d0800b005090310800c0380e401d0b22102590161907950401e078001a00c00d018204401d030380440311812000e0301c2072380d41208441c8540c101000050028020100c082204410300c003958004c1c0c10159000d824170603005071603c118a000790800101d5500961500300003140c0524152665416035641f0030000100d0b079103d0f0800c44401409410081c43c6014020340c940c0d110195100450 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 341459406 1250 341458156 341458213
    0x22101020a110a0203070e0c04030b0a060923011505040e0f04060b0303041202010e04020c1015080f0c1302070212030304051005130615080f03120112021e03 69
    0x60303640440c0100140a9055030144100e03030380004001c0f00059400040300821a640810078005a68503011341b4039040c01290720246c03212034481c1c20000aa09a64048000e480c0b9250b41040560740400d0980d182030b810580b520b003006080c00c010b01c070716a480002c0d00242c030101c1ca400f602d400c0d1100c4010a581c0c1041c0d6071050072040e03010a00040001a0090700350a020070740045040c00d06d84920f46848424100c0043e05015040d8407082d2141c031a03030119005696880e003264003500d008100e203801414603640e03c50b042e0a100c8004540b5050200e10900c2a0300003400402c003176004d81e001c012640620b05200d00006030300b00161401612a4000803001c0c1000030041d64a0f49828109141000c54035a03844920510704001c0240f401000500362042d076802038000a040302d54088415036016150f00000c1081c811715000702d03102a800001000c44080b170301201c600c00c0c1d0340c0b548502122031038484020352214194400004006100e04913031182c000c020b0444580841d40081040020114600c50 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 341460656 1250 341459406 341459411
    0x20d020406110105060105210c12010e061201060803041e090905030703090b09010c060507031d0c0a0f060f05130e0708010302040b010e0303030604020a0201140702060708011719022101 81
    0x14a580b980a102d1030f503104100b802e1107460700402c2d01c45006181c000e44112050031407840c010405021414043d120900c0c0305091103134403561240b08040c03415070116200c0d4410313401c1042a250a16060207020100c0b0104c9004501305814040d8080d65180c41580c0c44152009003900001c09501c28015260b00e2402030004d03550f9880641002040341ca01900841d00900040181a500da40d2020305076070305c240c008070002066115131404401829480d95100290000c60160390130354000841c00103c84c50701218000403041d034508490001c00594415400403418140b41807107600e0061700140030314030750240743c048038603140d082c182d0600809850940c0050004801070045081910814451040908000852160075000240e80740b000400c401d008680100b41914224000d40100542c4001010315059525006800030350741e407022100400001d10704400001d803000c1650030180c04d4442d04004d08140b000802201400c4201e43e04100e030040f811690a641a001c04450100c14140b9078001 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 341461906 1250 341460656 341460677
    0xd06090c08060c040e01030204050a1401082406030715180f060e0906101b02030703211b060207150c020a030f17040b04020409021309170f07110301020d020406 70
    0x40e01d26140008041c10010101000244545c584110752103044a90440300030074140d1711a07050708003401000c40342c174400c40350140000c60b0186002c1038080e04011140911846020800b00f00c205844082c1c07451601034010850078000c0c01c440c25107441d140ba446c1d05050b03403041c0349012070b40740d40c08180d48030f200654050761003805203590142c805022881c2c1110740d078040d400d0100001d220b403501000b005081c4400440d10700d41c030074240d440e4150060340003402d88240954a050004039620400c120120380c6501c65402c0b03550728010a10b03155203c4041511031290000d030399841d030003540101c0c001d0711030708000c4500c0840c1807401d01401d007000701c60341d0107003c201c00300303140140c08170301001200c0060013030b0340d01080c02d08507010304c10a0b4443d40090320100b440e2250b0000c100103090b0988082e41090405c0e03841c41070b02005e90040300c807080c4681401c02088102000070380305805922142440c0d81010003d000200d03564a540d50640f503001800140342c1284221814220b0344241c2c0440c000c03070400d809 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 341463156 1250 341461906 341461919
    0xd0605011e050a0e0a0807030305031005060403051c0e0a170f010c0f120b03120c060726100b03091b03010912260c03040b150603070e0d06090c 63
    0xd000745007010394200d120501c40c40710000b030014010719408800300070324138019040036038500100400400002040e120111340340c0c100140235600c1181c4003020380604150020301402e01100325002c0300d4000d405492903000101c00d8501c02c0100f500c0703845c2006029004442e84e59a401d40340ba00414292440f50310714003050000034248280c000501c203041e407604010000c0b9641050a1035a0504c861400804694198004800503d428980180c1621a0340005130f103070402000181444070b11101140c140c1d56450070308566841e0000501000c80d114241d1054200c81e10710f00940d003145c4005a901c00c100d0b241d99025120350411100501690701070104d081c858030415629015040c81a4003d2140d5815038a45681250b01303190518204400cc01c01c510f0070120b200c0c62048100800340c0c00a5113400c5c40640509946c00c01d4400342c0764502e1840100e001410181790441da03210010b000e140c2141d40b9201c094800c000d022241c2504a0000041140010200d00c02e003500c1c07510a00e1081d403241e08084 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 341464406 1250 341463156 341463167
    0x70306080f0604020f21031603092c04021329040e300a0905010806040c08060402090301060306090c170a200f0310050114010302041a030702120d060501 67
    0x3403112407142c02c00024440544c13500000301c20054401d8541100d01c0c0a0b008a41d076860f07140c1d0700302d141e09020203d200c103040b801c9403c007210b005010740d444080c01a00d844542001140c400113018824100020a0100c90090048903502600042400f402c00c0d00500c0002d05881070031004244d0100e0344220310036a05d494005c24200c04c141a6410881442000c00da40d5682040741e002107010240c0540d01d4454402c0c0183d6000d180240900e12910b90380c83d188050050f54981c058140400d14a90006801e41024802d400c00300e1780342d41d50140300e5150b031010f1000030341c061036845815540b555004400328143e4000d841e4800c2c860340300303841501d14218103207000c603c15140d00d10564104a007000302003000380b0030602c1e003030641614000c580786043c40000c03040031000c10101d80501901003100090b000540c002412240610410788100440341c004504a11560246c500c1041d550700481003500b203040051640145c140c0100c40e0000c2d800b0400210b0b0b50462100011943d403110001d0003c2d580c0728 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 341465656 1250 341464406 341464423
    0xa0b0306040f063507050a2102030f0606040c0516021302041224050108030a082502100501050f01050f0d0f05010308070309060c23070509090106080601080d0e011b050607030608 78
    0x14090b04e102ea00380746c00111105040d00c00c1240f0388642c440380320380001d14142c0c03012100380e00408071885242120806130301e544040715285e00c242c0c070700f800c0301e0500c5e0301500480d036102078100420a1540c190390700f008090110008401c03076042d0709210100302c0300310210a1800b95801518548241c10380c2c0510042d2a000381c1100d2100c13941042d00400c03619100000ba50004440c83c10414015074602c480c5102d00e0381c9041d4500d000a130300c20050441c05801044140c4c21070902c10003402113a032107405000701d008000b240b440c00920200240071545226501070305e40072440c0a008500086180e03401801c3c0c410030303001030390480b200185420405420258460080c191820f00003404180c49d2180c0300450600b0000b032000000369a8800c0b000744081c008000a842d0007420541241043c2000358000c08290180007120301c15100041542c0d9800189405840829680c0d041c85541202c0116036992209481c0141c01c518140c031400050002d0148a100300c00e180c0c2c1c0010701a00d0900320703074a000d0f0740c0c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 341466906 1250 341465656 341465759
    0xc030115030201080c070512041409070305040c05101407080903280f030e030f010c180302030303013f020405061807080601050f030112110a0b0306040f06 68
    0x4003101040180d81105041750f100c0d5502c601c06488081d14205142030140d038507400c11a5160001d40800d40b50b2600056810001040d280b04c245641c5441003074080702d1041d46c002c3c003d244075000402051819185000d4000c0e0315141c104180301d0a0340e4081c600d0740010008990840c008206203083c2e0400f04a100d0040381100f1081041c61140a080c048a100085000d031803000d0f4411140300349801041c103914520300140c111540e0714070119115008007000340d45500054501e10805054412140021043c1c0e60001c024510b10391a010440309181301001c0400f015a40301d0101440c498040c00e14a920682148810324100509104000460740002c0440d072041400001d5038045085586041d81e000d40380341030084030b07a02d07401c0041e60640a28900b0008514001002280ca0041c818191000ca4440c203201055030100c40108868114140982c0e04440c00901c000781079458260000760b035030004c01400040042e1a040001c82e1540c0700740f00004400d01c0d510041c10030901f100750031520b83c0038 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 341468156 1250 341466906 341466941
    0x60a050c040f0302061605060a0902030f01021c0c0c1a07030c050304051504020105040f08071a0304080d15030807060b280303033b0f0c151b010507020c0301 69
    0x40c03122480720b0b400c15000183c00786001140c107140c82000246a0a5003070f4110040314540c0ca45845080054a00100d080740640038034501400510414001d948407103506030348400c00351111a025800800381401203008000301d400300900822940402c032000802000c03000c0915190907030000d0103460800054804010b020010440410804500a2540c0b600350034540d1068480c1c0c0012502402250030800040c54007100025041e50300080880440380e420b214000c0101c2c0c030f440c5900030b0780400c80e4080c001e40c508112004802450fa4802c03044400115002018583c032a00c03802e1441c0c10140040354459034460400c03116103002589048000d040b524049160581484a102150824800207052585454400300d68100341d21a505528200d1405c002142051101ca88401000100780f107089005440f40b50140b42000f29110004440140208812290000ca414440c3e0300501301c1c1e607a4401d214170040450789007806200d020b854075034010324254520704101400c541c81c00c480300013a180d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 341469406 1250 341468156 341468159
    0x23070912120c03110709060f08060f0103020d03020708030a1d09250903020607030c022b030f02190b01142707050706021201091803170604020d0e060a050c04 69
    0x5020100c81103408001d864000903000492070140c480c18103031550714081d4041c00310302203441d4900303500c00812035140040c01e0810640c0c0b0541c90f5168901600c0709100c2e05412401800582040c0249000d1540705c1c0c0304030b81c0c0317442e0394107a90341c150b401c15540302001030002500101c440d0984080c500940400305d0b03802c11541410b401c100740075003443c00d0610088510b601c144030000d010300035400003190080c090384d40d200154640244110920700040b48105403544d4015100140202c03144241004070300d40001c0c3c1080340d202603400c21407651f120380451003040c10442c2c041d40d0282c682c1c09028031447c0f0304036584d410f01c5403d00102003140300450050340904140c0c0040c5e54901041e0b0000e04900c1e200244d87d40300c580084805104001028000c0e60000421110346142c03520f00031704071082d00c4000c103e030307404810051100d8100c041018002446980c024181030236003d14803500074074000c00040c500022059140c040e0f40e83c1401c118010341200040050b501c02c6806032943c45041801c8681c6040e = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 341470656 1250 341469406 341469413
    0x7020901051e010e01090e0f250e0d0221060f01090e0312071719060504020901080417041502010203040210030207030f050d061703130f08190623070912 67
    0x2454105550f04000754138800030301d141d00501c50300340034289a002402d40341c0340610a03941a40401e0710800300f06808201c11009850260001ca20640f03010390f50550749090010402204240041782a6031003400a10344038180700098059401c3c2245860141810380382103003100b550703030300c0c160300c96440d00e800c00c2080600340d01d001c001c45140c0070245810050b03588603105c0480707011000300302d48418040700e034040c031141d02080c4c105105c85107210389041c007055482c0c0081c842a40105240740780824a20390101e0009400034201a031440568200759041039a5040e0000b244013000300780c000944d41c00400d000070750510b850315041005d1107090552a00c2000d0b500105680c46145000080040c080b40c0700a607800c0a4101c28001d00b9002c640e0781482401415035503c0f5030021a81050322682e5403800901c81429494100445098402501c0314461280c001d0103c0005508200c900e42c1d619141310800d0709209550045104006e1712107603081c90030311b802500040c1540c10200c0341450000d21000007 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 341471906 1250 341470656 341470699
    0x14010c0e06040506130902070302060906010b120a05061201110901171e040602130e010627050d08040e0709061803020d11130905100f0608062a0409020702090105 71
    0x3c40314181c030100c0d90707102094140300c0c0c0da5803950004d03143c450000842e1001d15500203102400350041c5820740d00c0d5640e079034111200a1003a260100030030100d100c001008220700303900560340050044c2c0266400700c07240000d6030842d045c400030b49254040101d5513540da941d0100180c500d060303101c20b000d25a4108003079141c41d80c040020108249141d40400281002030980649002123494009022155100d4100a40c0464240500e60025102e8204510390b80000c0850602c0340314514840070106092000713001003500c07135a40580d5109001c000005403100e047c3d03da58401c9481d59690320f1090304240340103240054210312410f030043c00b207a0600159556126669155502080c400900740044011a0600c200241050840d510b03111101c028040c01040042c0108440c030800c100d0040306400ca0307801c403000b6005201c9107a0180c800101a00b40c082d10381e031140e2903240c100f5503000f180c803200d00002e036100b90885594550085800360450030300100c000d001d000c0880764050010020740340c1000 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 341473156 1250 341471906 341471909
    0x150a0e042a020a0803011212020a020d11180109050f0108030711090a090506040c0317040321030608100c0e01050405060703030f150306050906011a031f0905010314010c0e0604 77
    0x707040d280c0e410503903554003c00c0307120322003540300300290f0300c942c1d40741e103000d00301d003e900700175183c203200081044400d504c08940e001c0c0c035a60041c00e0501120f05501e038450b440203c0c0b040035800184c00b000e400e895505100115000b0003c004ac081910f14226001e0f0200c84011791068286500500c1040b00042c101d1641151a14068a424039036076910741010018058403c0c0107002401050144401d0007880b0203400c2c2030380e0040c15005041c2e00c0781c2c00f012013a8811481b0190041c00345032402122400c1d051040c00070b0b0852864041000d5440f81c440a0804e8100c1d4945000c181e910240b00c00c0c01c41c0c10074610318860300c09003003590510340b0f0000451181e1040800090415a071510b942c28041c009a01081642d80d9120031500400c0d00da20b811001482d095810044600c40d25000244950210302c41200e00104420700c0e90650300c401511041d01d00d00f2415219481d0014180440e20315030500c00c0b075001f140101c20104140740c1e01d054481c2141c005035580400c01604005410700358a03058120b40 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 341474406 1250 341473156 341473211
    0x5090f07030308041202010f020c0604121d09060d060e0a0c050901060f0806041b021f020906040e040c080d0c29011211030102030c040f080609060a020711150a0e04 72
    0x45c0041c4040404134010180d40d0b420302074052010803280481980003034914800d52042000042c00b0883c85020780b4410a84144003900050300c220030249400c128240c41c0d0000c2e00503100210500c844d95030b50301074403c40c001e4045694080245041403203000c0e110b1200504040c0c2fa02101941030a00040503014004600010711002c4d030f02207600c7d52a19840a0103d8061241d0411002c4007080300039102c141c0031400316131820005d91400d106180d580f084a4401000810451415140070004601c0081c020303c20b0346c80041c0e1541c001038800d002d02c40100c0d18400c99803104401c04942c50803e0202070648a030b002c0c8110b08210460390391a812104e40c0c1924195030110703103500550318000c15160840b101150300355001005002c10000f00f10040c109881150102d94041a160445255506821170b00e44a1039848a0013144038a07050380e00400744140a103000c00422000c1300042a503030074101c00d00c600702e10400030f2460a1543e100034100101c0700304607014403d86100d50070000c5000b04105518 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 341475656 1250 341474406 341474423
    0x1106060d0206070501112d120612030d05011a030405060402090603010f0f05010f0b120106050f04030204090b06040f060803190e120d14030402010c0605220605090f0703030804 77
    0x50199990001074a41d015131003802401403541410521406c2d8110581084050a0510003d0000a003c0d03225000019910000d82d0905d14003a0901321020740c0501095000102d41d4450402035100b440100010222100089800d51601d4900301d0101e0080c41403403590002482031100107a400728806800c19012075200b0329680700d6a00081c01080c40300103001105d448c2140d5020702104a4102d5412140171018070b4142d1a65022003251510130028032003050320282c40180089805180178014403880d03d50214106510f03640424102d55100a055819013031034010012030385441d000300c801201e0400014840d0a1410804070703506d000340c20b0548600c4420000c84d8400500c90425604184c5005009a540181c9445001c0d2100d9130307a00d0400020b40c10f0941d0461618800080300e004070f40c180d60380307a11800381d6141c132401000c004c1e20502c0340b140001540721801d83d00c013402001942c0038410000345030401c10002d85ca024003e00c450000c54000100400c086a00700e807900e40d0160f080b0400 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 341476906 1250 341475656 341475679
    0x40209070f03020d1416111e0703060603050c0f060a0c03030b060705150703140601080105040b040f110c0606090f0c0c070509040f120905031f1107110a06110606 71
    0xba40070303004081c81d406000d03140c025100d00c1e0740700700e0102e6401801909107041c28002010011204032040000b40c4442e548110040040607100481d0b140d4201e0940064a254030389940e1000252200ca074410380d040e500080020701d2034a0700b1190540303001001c40d0200d02e000340c40c40e40038082c100c0e258006401c0c50350701d1400d15040d8459104662680e40d0100c150703003000b06521441201c00009035540c2000911304400c001c0903045400855006580585071642940c0c60001000040c0007070324001034205403100e000803c1e40c8240d009468230310844481040c0c031111306c111680d00c4d291000304554031074000201809402107403014060340100c281c6600c44d03910300c490402030346013400550000360011481c000700401d00841001c01d01015200364258201000182022a44950b4501655a240d0401d00f1950310541000b81c420007a180c4582c40031641c1c01d030440f4042d40b01e802a1505480803004941200000c0c6080010310f0042d00d403504001c095004161520380c0c2e2000000c26250080c2c030003d69 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 341478156 1250 341476906 341476937
    0xe040911040c0302070510090b160302070506010906140a05090a0e0a151a040c021f0e011515020703030503040f0f050303070f08090312040b060a0503100b0a0e04020907 74
    0x90000ca20003500501080c4004a0028020751080605441e40c1c0070303400111121100310700a40006c50313005032442d55140c07a48801c41c0c065418210001c018164200b01450000e0030a20600b8000e10300c0320800a105071400048020f015030310b080042c42141c80c0c000c2401281c0c0e410020307640000c0d8240d00010302d181039030412072800907054409030400540d080c0490425103160850302d03c070303030300c1c5550075031117071034142c1848280e9070740424040241e0030070f042d2107011302c41c0f0968500b12182908004920442d0a0500307508407003a110300c03c02600380c03241042c40098268031070027a00001030320041041078995200203169010251004100b2040c0210318814000c2c151105045a5001410760b552410301c8000900080f200000302408555050b000503810180401601d40c0c069410728210016952540c503078205980060059a100440d00b80100e62610104584c02042008920006080d59603104001e6180c442e94814070080300040c1c100001a200d0002c61600806103080c0002059032050303 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 341479406 1250 341478156 341478173
    0x30204241b060f060504290109050d0f05010c0525020109050406093c23070c110303090612060406030213090204050a18030c050a0501090b06040b0409030e0409 70
    0x46200900c40100840c0d41c0501541c2d5102034401ea583d40010400142e548040c40b00b9940e1004c0704000c1007612003c040c0840c021f00e200380e082d8240501d0301e01e0485482d00001103062070459410b491060424000400f001424440c1d0184580241001c1d0b05007100f0000c1e0000b072581c561310610001c0c0030141325070704590090800d6400340c400180203220700c6458800c604001c1c00903c40f00071001100e40381520054030203031200000d511207013520094000015000c1406010422132050340006078811201056002a00480c0143c0c0d0781c0d911030400541c80d04080314605008011240310313402c100544002075682c07104460180c80d141d59202602ea944000190007000ea5500180d005950981c218000301c2655102c500140d00c01c0324200003c0c0c0740e90030240100d40f04c034031042c405440030f41d10700c4002c2401920901c1e00584510201c0300049010340c1c4c1d007030a40701c00785011036aaa8000051094034541030196905042c015501044070307500700d481c006e100020540307029008550b503000310001d011060 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 341480656 1250 341479406 341479427
    0xd06060305012a030905030a1404081e0f060c07020909010f090623010f05040209030307170301170c030d0f03090204020f0c0c220b0607140d020d03020424 68
    0x70000c100c1c00015008100e8a00401e20046010f90204030451101da40a403080d1521150400001c44c1807101154054855501c4040a00020001440001401881003010b256440601509100c22010006d405131400400c003c01e004680c024a04002d44885410203655840c4d070112951091031320740c4401036005002d2041c0360400f050601400c40144015500b105904240d1302c01d200c03502404d5044500740d209800e00841883c3c1d8182e40013080185040d8020f007000140003410f483c500000c13955a0031403103100c00117503010707403102000401c150483c80b45071400b600540ca02038054540c2940c0065150042414003c0c14000e54220011a40303119a0008140640c003400031590340c400c168a12030642c014684003040e0384103804001c1d4090030302d200b0414207144070031485051803058030002c6000c0c02d4004041034100780d041c4511808036207184984c0354810b030755070041d0000c1240c44034003d0820910500c180c0a240c010002000b003132669010000c07082da8071b40c1c03442031144c1c0d0140c422542800c15 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 341481906 1250 341480656 341480663
    0x307030e0405060d0f030e0907030b011d030312010321050a12050a110c0a1202010903020d08040302030906070b0a060506030c0405010806060705070602150702010603030806061317030717030907050d060603 90
    0x944250826410587d411301c1c2840c110382206c00341c0c0d0380d400d0172401e881043c0ca020f070010340f94602490758000c1031031400052600041c192810305403240344200f8200f209070b00c10340300842003842001d5400c01e0141740001184003458054a042c6014401030507070f454060a0034030711a80d50317002400342340f203c0c0d0224401245a90385a80c3e207400d400c80d516629203501200b42d681801c0d01d1b241c03011050051144a643d5035141d0007810100001d42c800342d420940080c404d50940c0400c10207030030aa9a484024090304d40700da0310045807411b01890180481d886a001076004040400600c92030700001400d03201240c00901e444d0710300b035440201041c550700075038100401328800d11b2004202c0e26000704041c503c072050980825220350700e1078030480c281c4410b0300c40580419440d401058081c18564001e0407441e4085840720409551009442400502045085880e80011030310508004550328481820705080c0d090381e0840c28040d83c0c00d030700c0e00d503940f09992180e10b100030b8110421101d07030411401140c2 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 341483156 1250 341481906 341481923
    0x30809070f060e0307050a0602060c0c1c030c1d062a0102030411091303210209030706050a0906050304120f0212030901060f05040c090603020a030b0d060902120307030e0405060d 78
    0x70349800c083c10410040c60340910a0180c0c1901041a0801442080c210703512580180030306d485001c52140e040e4400400003400307010b1007410080e8083c207104003403a124034907540090000c05065004100f18034644c0c0341080c6c4a009080c07012150360b840195060070122581481280114805070030180100410018075540044201710901c00035001041c00c4860545071484e031541c5200c1c900d41200b02541d0000d010618181420714074004202414590000103c801840c004460300000d103000d91a0f8004000684001401394809900c0b000110061502d400e00c14203500b86070345c07003002048294002d80204800394038000c500b00c0c404c000f00758100c6038880c5807503902e0031b0507a00c4502910842c0264120607544400010b41c80c00e1034810f1000d04405680d4022a042c00c080c0c003100a035014802c0841050f0b1943d10307081c443e9441c9002d60614a2169000240c03070b02581c414408805c02d403000080c150341041c1315060120340c1041c08d00120850445c0c00041541c1c40000041d1403101959020b0714024 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 341484406 1250 341483156 341483159
    0x2090d140a0605041a071403160c0206160c050f031002030a090b090703062904051005030f060f100501090902070804030b01150e0301150e04050a080a052101030b04030809070f 77
    0x3640c41c0c1542040d2803545105c581d03510440c040d2039a00d480c1400d840c456504100049160307050001080e400035641c9022090040c0a80004015401078446072001646402d900800c019400ba0b0240003080706441101c51403100d080001c1d110f1107500541418140c002000515000e000e80c0326022891340714501c10941c0c200801341caa42e6000d58001100e450303103040301c11448000f08054a52900c1401c50414104104020501000d0500035104800d90031001c07d0208039a601400b0b074680c961106070007451a81340000e4842200c181c00340003641d02d01e525420601003640c2c0f0101c40c000b9150040300141c0d45102314a07100003d445036603c0642050601000030480b09062601c458001310039580d0440a034250b801050f08a80039100d0541c00150100300c100308451109007802c2d4850702940903a00c500d052901e03540d0365544035400300c0000460014003080341085004840101d1010038003241c50b258116594075000d10b101400142c244a00000003960707001c000c110000c041e0a090030f0807804603 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 341485656 1250 341484406 341484413
    0x405071e080601060801030c05040914120a0311040b1e0708070c06180b0418090606060f0f0801080619180501050a061707030b0702030d05150a06020102090d140a060504 74
    0x24000360080040a018003400050b40030f10508070181030300d800c05080c0c00440c0ca00800c00004040a072011102001d03080030030307070308441c09211408181c5218810a030740c0f440d007150f00800b01ea12000300b840b00100103200501414041d042650324002d902c0c64035009400c03407404101018002c00380300500342500098941c08000f80c40c9031450480726280c0312040010110030200d003003944140668441060103120401100744008990078150445490000c0e220305543c54140a0350019004280454081f0454016141d0300a155003a0084a4500f055455040c031200c2511080040c00f40842401c1320103ca501c908100d5101d0728000c3c0e4503100c15400c102581c9421400b0300000c86180041e1494404009586009050300e41290040f8002030b1510030f08650b141d010b4204098203050440c4418404070420101d03078442c3c41d0203022000c0c0a010000a07903020019810b401c3d40084c01164014045031229803075100c20402082d9100074030b42ca1310100510342900c1c000c00d00384060070340e41c182000d01051 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 341486906 1250 341485656 341485709
    0x403021005010b0c0c31020c0c06190e060c0d08011503090c0308030a0207020603010914070f0e12031908060307050306010510050f1b01020a081f030308040507 70
    0x14100304920501c01ca81c0d070341c24140800d028209128a65420401c03551711145000e11501500c10f000c40310451040e00012803040d002a0341002440303245500098481200108010300c2c40550403c50305035150070039182e000c00300c5026801004061040990713041010303075105425990b041207458225584805200b2009020036401e1140c00d0540204580070454244a80240074045d90400c0c94070b030150346165944180e5500060520786e81650a001030401a681c0c403009600910f6890001b0800000343d00c220101c480000d4501c10900107000034a0324282e4000c05c4c0e03454500801c0b1100140d81501c80001811803165501f5002d521210314038418003140c0203003041c0d01540064080340c40983d152130030b06030b03208020301596520014200100e00000c1c4078000038815018603100d440d080c07852221103520203403020301e680c02681e500490350416060b4410b26196100c81060080310186650440240014085000140800a014000806100c0200012001061140f0b211400030055800d083c88 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 341488156 1250 341486906 341486923
    0x61409010210111905190813080c031e03060d12110118030210200705032701120603150c091703041503060e061002010902132309060a0b18040302 64
    0x61150054150307101c0c0512440c00e981c90003601700640410b20741e2005042d941e00e8401440c4c0342d41c0300d0120f00c0308c1e000254400080d0498828410045880b50a01480501704195507610107030301c80c00520800c00d460f6640c07002c001c0c0303180d00100300031214066940103c9100c00362070140c80e0951b091200c0348421101054400031094029404d840c800784038038640e0420f40f8100350010002c18882a500d15010100034010004d2610030401c8030300e0681d150b920b1814900181c440311201d03406210480e880c550304000c5801e492003181a08101050855452070fa40f5109132040101b12542d81c4089040e46003d10442400762805140c182d1090000c1c0075816980d5010740240703a4190707040001c00075024020b00501c0c1c103403400300ba04071080c2e555100512060382c100b05c28100442d900c420348100562154089503202d00020ba601103019501401003942c40b10380c51004890001c6420100700034044045117042c0c200342002c80204110410780b0000e24040d1180a4907003e0810400500c410142c00103034220 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 341489406 1250 341488156 341488177
    0xc030a1721100914060103150f0608070825030b0a030519050c010804050606010e0402040e15010e03030403050a110301020c1b0a12030203090907091701141006140901021011 76
    0x269500d40184000344d900307000f8042030f4041c54802041d0158086d4004140320440d407404101c06566850113a44c101c801c9a0040d80401c10142c140140e0030780c0809680e500c082c0700d142e001c040704001c0e1000d1075207004101c4440205a515078400030290707a11000c12000f1500300d800c840b4818454044041d02c000301110071a22403044421954055008910552095401801a0410341d5036a0010b6030710352200d40700c01e54042d908000203e500045588085d00861401100c031031410303030100014005540f5107214910940c0140302c100f00203440003800c174201651010248800c0d04000b004640a402440813500607030003041c001c00102e24100e0300180c040f06c000c40705002c180fa680e481c0e12100c5030500d0405401600200120409820582d1240c0c3c0c0081c40c500d04211030594840016080e54416081c030384bc01e035100c0154102001301c0c540072980000c10303240d10202d041d02e030240180174008845074520802c0d20104520b110b503802807002c0000d0621101042c85540600804120107502140244 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 341490656 1250 341489406 341489431
    0x7110f0a0b0310060318060507030f0504030c0c0602010e12090d020301050118061a0d091a090f06010b031005010c0302030d0204030804240f0c110d031e020c030a1721 73
    0x113a9148240160300109030010517044985c12140c1b182c03009032030010044014541c892107000c45100580c421144500c1c0660303103403000c000103841d0000030f22215602080c00c580c1003604181008002282c007800101c07550045513600d0310018045509002034140c040e51552034440009031201040509110052003001c1c1000203503283e40204480e1100740d08004074010040c480d2902d10b040e940d104020446c0601d103101e280854101c84d5440052045035a404c0941007401000e000c01c00410005001d03100340e90070320b421458000f245450318491440b8080c104105100200145802801100c4d02c3c80351191003555601d841c1c3c1010200c980c401e125106007d58007104500369000c0c0c0c1d0400c2e02d2403c07119a1920000c0d401c1000494041e11032401c07e80e50920344840c3c070740c41a80c8020300e080401e0300c43c3d01e03507a800d101d40d038017130600b514401c0c0d01207400c1d500581412800d6079004101800c44030360001c00c1e49214540905078101038000c40d1308080d489503031200307500c010b03504020006228031404050b1 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 341491906 1250 341490656 341490659
    0x50919151a0402131a0f0418141519031a10150f090509101806050d0b150109030c05240a09050f010302091f0e0316050118050607110f0a0b0310 63
    0xe02e803031b481390340300c1c0b508080c405000030300540300260301c04460700c5801c0c0c0002c201c4030999028450001825511200c0d2200c0d0021840514103140c40c43c0f08a50384154400078000d8610b0b1a0303000da0800d031044241c10000391900088a49200805074400760840429180160141c9840a05002403004000c00803c41c41000041c0b1441c1040041e4859007804005c1c04d002880c080f40c603200001e061040c41a03c540399100458540c541e840c440f4804d6000b812541a0340c108001c400007600c240c0c40400f410040d000005001140300e420403001101e03c2500c5012412801e51204042d012042d00ea0010010000491208031503000c510442501c0301181c0803800740503c13000640880c40b4200409420003512580e17030100c0a07080314810b800c082c542c206440c40c5291071001034207000a280036140e098100c1c4005004a5038090340f141101007140c00c0ca0703243d0314205030004500f80500782c002400000404407440740d03601d03000071711451580094102120b2a481d40c0c101903d07a00201c440b0720100fa041e440 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 341493156 1250 341491906 341491949
    0x90705160c0509061e010c03020f100510080d050a12020702150c010e070f0b090d0203070e09010c0c030e040b031c020a0b06150405010f17010306050919151a040213 72
    0x145e1103c41c010300e01c8031401ca0241c1c2e0040d2032041840f902a01940183e01400100c607406000d103c09014500c0c00006240c501004030030b881c6509901700403803d51008903598140740c1c00074210740d01d1344454100304051003c05240c070350280c0318110009400c0b04211580c00c081100d00c0000c0e100b890240c0c80240034031000045815035809040c852103c1001ca0008200000d03118803008101c9a5070140a03680b10075903a0700424503020f41a8000c9840d036201c5020044003034400e01c00d080001c1030038581032001200c5a10001d000f11400b000c01f03880b5a0b80d8202c000181c0ea01041440506030f085e402c00c1240b15601c440183d01d44000e680182e0f0320f080070000242461600110240701c584520f103100b401d013418a00111900442c03003451800f07001c1c106045010103000a100035009500c50700c00411185017840c0c8050514004c180ea002d5400080e504000c0020807200c55004114140d420004103511803100c100750607503071001c210350814400610b18002c0380c51100100d050b104000b0300da092600f034256 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 341494406 1250 341493156 341493169
    0x220e0717060108071b051606090f260a02040f0b011205010f032402030c07140c010903080d020f03100504180c0e06040e1603120e0f090705160c050906 66
    0x707039081d0001c0c2a000000e0a454020460403035003900c058032180081003a80d42d81840c0407004c440380d0010701103151041050300d500840700c001400b01d5401d4203128038134001030340600201400d05404200d0702008050408201041702d41d0401340c0003001400018803a566040c0145118044940024251118820240043d0203440c0c101e640c20801c41e40700d2840d41d1500c10b0f400d0002d031303001e61041c3c940452202080840f800a0740c010040c000d4030a40e00c0d0301c1864040c2047c01003550404517030701b001141550326a044030300c02c42100e800c40540e036654002503064400902c220020201d2290010040c0400040c0da14031440540b00d007580e007040040004c401c020414031030824020903c0c01d07007620078001c0b10700d07040b85203400020240012800240d02c4c010581028403540c607281010445110410900004802e407010700f035141e04042d86a400c5c220081060106441d9800303014213800704c0419055032107903040354031440d4030703800080c8c60080c0b0f40741100030351707081d031081718800c28038100410b5071440c044 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 341495656 1250 341494406 341494411
    0x90907140a17160801090509070f030305090a151b150207061407030b03061807050a09090303050a1e02071a1305010e0d1b030216060504080601090e12220e0717 70
    0x40e298621030b17078a00b40d1b9103c060304008125049138001c40c0c20004100c10b440001c0ca01943c42902c400d40c980110009020380c60381c50b980041c2004114580214140d42c01240080c0103000030665031101d24614103000382c140c642400300351a0075100003000d100b80015079010003150700301484240501d0b11081c00850546401054240e4180c01c07400105200406640741740302110440c01c10750701c00c2540e03040005d0105140e54046600e00e0f440304201c00800d9414840d080c3d00c500c0340740040000d450851000d400c10510021501543d030b50028030f00091000e4909080006c0c01030030484001c07407404405013510314144040440e0150309200702404145800b0840c090324641a41d00c00781d01181086460f82c081d07103100c0041d000d60141c00c0c41d100c584444020048043c111a468403030707540d40713016816494204140e200712449890a042d55164160200e000b0a400740b10380b08090325202002c560312505024592010707490346218200041c171741d4810845611468490703c50003005540c0c2d8202c5044007504 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 341496906 1250 341495656 341495701
    0x5010b0901080901060506030f040203010e0d0f0c060e06040f05060c180418061508150f16110d0906031103090a06020f090d06050103110114090907140a17 68
    0x380103400080d4410b0307011660202c1070500114220399910302040b4207600968522a482d03107150104001c9d030600740908402000620f0041c0841c540a039001089020352004040030001203110607010301000c0e82184a5804045050f260a410b151904030446100080c00320349501034900000c03001d00303500c401d03100940f0030000700c854121041800c02008080c484e9845a06203100100100840d0441c401d01d480b40040100600ca070300d0504618616109080031681c0040749481e00b003200003208840e40c59002620b4403003402d5441b0368000300303071100d251501941106205040400c041290311544040880394240c9040000a4007211004a030b84011501c40c011548085840c00006d80c4a0b0300500c240381900d501241401a420006070201000086c1912810345a2006006020b110781898a4001c02400e100b400711840702c642902e24001c0e1360b42c0e140b00d8800400051035043c01101c001004958000c80959141d80514016200c0144006060411340c0184009001d425008c038840002035a07 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 341498156 1250 341496906 341496929
    0x70f020c01030f02070b04060504260d020703020705370506090f032118030303041e02030313080d090618031b050d0302060103290f0a060305100c120501 67
    0x15140054001d005180f18510002d0703401c000f1600400d0b41c5441841c0a28070601010510781802c0c2403000d0b080c6405042e07641400e80c203103946510300b00c0d80004c48980700480100540c80d00d00380d040c03d074103209940c0d10164201d0400b5510180d240b401900c620b1081000b1640f1040c000001d280089182a01e4055990004420046e40030b543c80c022084064800c00102100d091802c9019240e01480701908054203602e0040344a01c00701c608000c0c0801901c10030b8000b50304610302526032400d2450b40900b06802e0600c241707440301c1503440a0040b00c41074110802d4003d007043d524000ca42e0354420301d01750340d800070350401c0380821010320611540004810512400100f2405c40d1140d64050300580d070429400b82d903108000890b5261544503400460083d0003900c400e601d1400c04080c14100a101112000031030b0072800c1040d17030740d88400d581103002400c2800b902e45c1e402210000400058101034420b10030201d0844406002c0e800c8100c40070340030f9807006038000480010005440c003c0c02102103102 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 341499406 1250 341498156 341498173
    0x1b070501050d0f060801020d0e06091902062104031707090e0c09010509040c1809110a0f02011508010507020c03010510150c06020703121415011101060503010501150206070f02 77
    0x807030300078200f400322002d000a003d40d80c49202608a81c03017405e469030b046889080007174218a05101c2254000c041030040c180c90b070604046101d4209010200078030a1001007a403111901110004072003442d5451446041c03802c0c0b070700780a09401086403078024105000e1002030f0505219410704001c40719000c9a082082e25004c010703980c250041d105850401a050000d80055511030040440380e0540340c8803042c200d02250030920b8004025080030108038102000c80c03001038029012212040240c1c503045815020721031080380508100c0e800c4050000f031030400415900419400f007802001160211400100c05134189800c4c0e641c102c902554000c1d0009040212100d40e07c090142c1130303594901444030b44500d9803070030300300c0c1c01102c0300b50001680701214080040c1c7c14410803002c0040b450f80708a4915200504582040300038000b0ba0402c40c403480b010b14445402d41010340580750050007804690b860703511002d407500e1010041801881a00045041903000e0402000004034a5000d4440c11 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 341500656 1250 341499406 341499427
    0x4030b01030b06062a0c0a0b03010e010503030f070206030709051306060f020c0f0906030c090403020105070e060f03060d020103110d090213060e0c0306130e0a02150307091710060602031b07050105 86
    0x1400b9400e0110702030146001401d00e1f1340d04d40480001500c500001f0300c1d160750401d00ea103154110140c0042c0d02a90003046114144403070310b02600d01403503044503015500e645030703501154642e00c1079004c59080f40e000c011091410800b5044101540d51030b641e4101022100481203035692460000550000c0000040040c24100783e070600e0752284001d011203c500305444049807000008071410f40060359a0010b00592582c0240a1640c54508545143c00e280c0031400520107440050190b5101d6071999001030110f900a8105241040c40c00b41d502e503c600854500c81c01800402c44100d206003045008141d9116071842031400b504c0e02c0d8042610159500090f03206e00340e00c00791a00d03901c0500020200103001060003105142c4003007801821102e0100d2041c0030a00c60306030454940c031042070040080607079128901604441e60801403100c1075040b642641c1c1012900c8a0002107a0704056021900700c0d000001001c681449083c003800b031907a05000661202618040e590000743c0800c48407800 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 341501906 1250 341500656 341500717
    0x213142805061303050d08010e07020601151b05030d06051309112107120b0601020706020309041d0f03030f01080604052e0e161d0a0903050f04030b01030b0606 70
    0x803a1090b1640c0b4032101e859440b914582411b03c00030340c0024002000601101085100080e0007030f51a0000701030b00d50400e40034100c0240400c081208000348543c0102c2c0d042d4407405280d03109908042660780d5400c03100e009001a280c03a001c0c0e180104110450000c0421840c0320300c198850304003861481d00000e440c204100c05040a00182e884102d2001c010160a030601943c1c00a02c0311540750b000007000362822040c0a08003c01803410354000e810204003c940100c103c2d401d12108850000302c203c0348407055800c1d840b5180700508144980101d0000b0041d00000850040d040c03c02c40a58507a40c50304c86640c1c4560485008040d50030048034800540c44a0145560041031314030f0f103004040b840c4c20344104880c20a009545181c0c41003090070140951842c04c0f00c09060f8009003561a050010045400c41c80094068140d20b03a071200954149807241d001d44540c951400d01450b580c550300d0520941103a02800180e40a0344c0103c0072030300c6807078070030122440c5110880c81c2c0e50f00d240c1143c00c8150f0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 341503156 1250 341501906 341501917
    0x13050919051003020103060512210f0d0507020717070302060703030b030a030201050f13021c03091a091504050d0209040519050102030a0609140a050a021314280506 72
    0x510040c0034a404408205402200c0c4140c80190703903000c0091a6000040980e0b41a80c4628041e241c000ca685001c0c0001044e00290319294000d17410070540c5921a0070139038403d801c00d00f0110713240440e46454080315600100e008890700e50032666010f0301c0b1a074807101c020701d17a03e074940140e00c1101c0400c0141485000750240d1806810001640e01000010078100750101d10101c005035561400c0000801020440075048000030020075100409980820404032000080013104043c1d0040c006c00c0602c0fa50b40000680b0b5200304101084403803041007021070300200e840030b00c16244000040183d000e0300c015242140d400514010382081d00f0f40038040c0201001c1c00c1a03400c0d000f49007003013545400a0340075410185c8120001640c92074030038070520444220342c21000742d0b2400d240c1e075064400d90f0f046e10b99421051400c4000350b9501c821402e03078024410614100d09000315001c0019030360f08e41e003000d041881401d85040203103961200900c2c12500607940340b00080301e00302c041801541040c001500c07 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 341504406 1250 341503156 341503171
    0xa0318050a03050a021e030307020402030a0902042c0d0906050a120c0207330f0e0d03050c0123010b09011101021204051501061e0c0c0b0a020c06130509 67
    0x1010240c485011424054254006503042d6105446060443c18a0303140042c250541c3c201d1900c9003040007001a0f1240308030400a4410350300440480c4030101e5a030712514200358000c104214683e04803000d030b81d00c4005064902d45d004008101c5078500c060103d0441003400c0d6a64413003881c58200402a202078000300f111808012000c18207514180d02c0d88640014003869400900300c5500c3c20143c6412210a4201c8031300c2c6071809541c00309048000e102903203601c0743c40e0920b42074152407403008440c1700e4080500c3c2c0d44c0c460302d032002c100145034000c00240b00450110b002401101078401e142120403600700d8101c0807404c0144010040f41041201400e6904014505130307040c50100100642a03801148111a0212041060008011040000425036909150f00600035850201c028051985000400c4c00c0500303502400c4061a00c124480c0c501158090008a807a945800419803190040003662000d4030403c280210301d440c0440644869112a08501c84010f081030140401c0c00006450103 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 341505656 1250 341504406 341504447
    0x902070c23090711010606050403021c08130e070815030c12070b03010902040611070f0b0706060b03091606090b0d0f0b22060605030f15030f010e031305030f0a03 71
    0x8080c03655a445494043d400650302e4400900b07005603844e00b110110350000c0240310b420041040180c0b00d0030b19000c151080f4440c04400040d550814000340e1180a40b00f10311100407000225040480301c84c0c46000d0580780d540d403a601c0d514044100340748564654450fa05500c011100b103101d18003070002d003858100d8102a0351a031665240c03121095082030300800704194000c101030040c19400b0300352403840d202c907200611b102c078a800c0814000304440d0044099580380000e240d000d00410303400000041444000c0f4694030f00e0600c0066844050101e5441c0011044440c000342c00361240644a0a85408403a07070b600c2c01d40c0c0c01d800c1900811007802400c03002034503800c2c0328000d40e4503502d2903d59000c0c080b03600780300b510803489248204e6030f9641204c803d200e000d1060191584031181159801003900d943d540880c01c901c0006840c00303800895004140d801d00214245e42c10020010349428040c16520aa5454440301090749811001d03440300107603400031403460b01103445410030211114644201 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 341506906 1250 341505656 341505719
    0xe0a1b0f0e0f190606111005010b03010909080405090a15080d05090105090a0e04030c0c060212190c0203190506150315041b06030c12060b0910020106051c03090902070c 74
    0xc0b0020307115150711900101c6e0f112a6a0b41c050071083c00344001c078412041c4108090b43c11300c3d2a50016000c10300640b441d07203075641d981f0340030000500e044038080d0200602c81150b900d40301e0701c2c00000c1c00c985001c00540110480340040d540100044000440f082900d07a039040ca04a4801191150801d07004680d1201213080300141203a5603454040c040c1c0d000750380300c81d04045a420315808151940d4462401c550001072404540880101551681d03c0800d514882603d4040001c0b034041400b040060f61500641c80f2440886801c0c00e0305500140c4240240e994950311440c41c1e01c80c8c1900791141740d0305a0040d03082ca0380b10015004109074458412030607030290740385c12401500c144450741c0100010903902d048060040e90130241d1a825800c680c64180a03403030800348004c45600076510400e009407086016840c03030134000e400c1200a0240948203001c11807407008040b4500085a0003540400c03181503000c11141a2402140c112541020448502c589860101e079410074001a540810300c255604 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 341508156 1250 341506906 341506951
    0x90d0605070306080d05130b03040303021b01060f05041103070c05070e0f040209060f010f18091a1207290d020703030b0301050c0913020a030e0a1b0f0e0f 68
    0x4050150781e25650001e802410604202d2030807401d0003014050020034444a82e06c480b000001c1825110401c4802d91640c40da031030254040d000d521012150070814030200c03007920b14154442411109000c012060380c6503203030103110032500740645c50200e8039400c1000555003405082001c90961160382200c514035510000d44010044c166606200d04118000303100951038490340f6560040002c407012421f0051400002e000b60700103001b0030062240c20701d40c1008c95079003810200010601d143d42400440c030b07080e40d024111810301041d00c2c4140802010440c04c1c0b10005110429154018102580d0b1411300310060400c0394880c3c101e03c4900c0040280502030304003400a030011a01c20b407070200d500d001c00e00815096440041040f801d8400a020710413003a03031080c134043c0341c4030100360300182d07201c5019200303d001e031030b40204215091107410500010801c140c4183c1d500782021101c200c009603120440e0354403c14407441584483e103020030120324002c290350300003604a02c1c000542e01d5280c44001d0b = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 341509406 1250 341508156 341508161
    0x120f0206041d01051c120306150509040e1c11030403082206020d0509010302031e0f04060e01061202010e0307030b011706060d0c0e07020a05062502010b0303030c090d06 74
    0x704140c84008000d9003950382e03100c088140a0140c1000c5840040002e00c5003002880604040e1014204042c1428041c1e0484e01a1344420041c00324003101000d40006100d010348282d00c51582140180d02e4211610303070300c51001c103071030850154420a1040040d140c007801c5500e0401000f42d00c0c858042004004005071041009060060140d82d05040402403012221140c41c59580084195008100d16168181c0e01904a0705124400d080c01030716610384400c070b101103881c1da20240842c00c00040a000602d1550090503200710311134441881a112036000050070b80b6100d119985034000f002c80010b0041d070080010280301c240240489400e259640c4072080480002c0c0d02801c51001d50030f05444001c1024402a540a6015109031050a00540d11a0079604192040500c0c08000e9030200f2a11f81c400d0180041240e00482142c1e09403d0030511100144c030391219001e81d0420301207440d5403050060060603030700b0b1f40040103581150344400e980103469008041d500d03801041d09000600161062 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 341510656 1250 341509406 341509409
    0x20d170c07060309061b0203030730090b07020106050109050103050408120c09120a080f09010c060c050a2d050c0a080c03031b040b0304060b060d0f0c0216080304120f020604 76
    0x80e40c02082c0d400050170440c0c21501c071298041c0084110200322410b2640010440e0b8004130180350040d800c0b4050041d509820004076a15044e8018000c420b61018040b5040b044c0b045018003d150a41c0e00d8082041c1c0c229080380c85418080780a8910801c007560080e8441984503000700300d030500c1c00c031202103040824a0122100e2840490103d8804890f003059170040041b074000d00000d125403071182c0c4402c0c2c028003e1001c0c1038000d1f00000740e00b288030f91143c1000d181103940302e0341c00e0004115800c4064402e8001201c0600003c0061618013030700f550b40441032804c6414404c01102c42548601c00310f41d80e500c0b4030a0b00010b8450b0049190000d080f14006016294141010b1616410034820318070503a1845510000074880030300c000c1c4000504041100c0d00158440b0001681041c80c101091550244019100039107242c41c0221605454903000311900b00302c0d03a402d0300e0820b20007038200780a034082401504916401031206008111141d900070604074080c0c80351604800300c6900080980c0d105 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 341511906 1250 341510656 341510669
    0x2030a15061d0604020a091a0414060307050a08040227040c0501020c031f060306061707080d0c030c0515010f0801230708040201170a0b01120207020d170c07 69
    0x1410a10225000d0310a00010309008002903441d01000d00140d000c203000070300030501c507581c0042d031120490302940c4c40900400c120120400d866600c0ca10000840c1c2052191b04c94980c2d00010000f514540001201e02c60304075038590341d00b000b40801d803c07580154000c00480c0c01c01d1186908190741b080501041036442c0707407580c40040a2400d441e00010587d120740c000ca055500c047c00f501041c0d03501140d1380d02c0942c1031b1103c900c24016000ba0000140c43e081d400034148a1a280c40840c00c100390010100b01011280d04840d240c3c1da07942d00c0700c2c0d501c81100f4980000114194107410010b071144800110490082e0202d4840d1081c010300e4a2203850b0030780c00001c2d80e1880700010881072900f030003415002e00321060301000c000101a00c0b0782054600400c40b9041180c5000050110380c0100410750b0041040e00302000c080c0384c40c92803400103012460f81c20340811a50088920104914001c88100317036030150034421005140d56404000303055401000000710700a114465040d8002c10210005201 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 341513156 1250 341511906 341511923
    0xb0901021b010b150d0b1c0302010b31061703030403020f0d1e0c06060b030105030118120f110610050f01050c0c0f012102030708010b0a08040b040204020702030a 71
    0x10340d1168041c0c2100d40e403031031078450341000051025a41e4406400d0161820b54100e10350b50400800300c0e07402400e1054055901a408140026100c079010702080149480f90b002040300641040030040b203d00880c082e240e02410440d41400700e5024821001140300a542e00131901e25180c0c42e515260003514000300030a58408010001416810000740d680403000c90f0140c4400c41200c04018600200c030300414007401c1d002e00c1d02466043c881d10f00030020541020702088566200e25039064aa0b20a1042074030940c20050400d00311070340d4147e01501e669110b42e5094050a0484090f00c80c0f006c020b1040050156504d4441ea80d84018400c080c820303201611100b03003907800c0100b00140c03c0403803030b4201e0401c1824400481620000900e01e030740b4017400c13a010341544041d0001211050745c0c1c020344081d05005140f60a0040610f40c014601407803158403100c02a80c0c07105041074a0b40903800f100d44c0003605e000c01040110341d40c604a182c0090010704090324210603034011a1038000c000000f210750b0103 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 341514406 1250 341513156 341513167
    0x1f140c090a0f180506010903050a05100e160905041b03050606040c1409010c0c0b070b0115030e030409050c07170901080703051e0612010501080601090f05040c0b070f0b090102 77
    0x38203104981e01900d08000c004580504040c0807a40c2d50006410700c3c11420781c0c03000401c3c0f103030780a40407800055912208580c3d89800c546041c0d078584c01c01d03481c050281c605001d01c11900180100308072030415030116540006904d402412005440064010b0307402402080340c5030390b0043e90424120203140180010901420400103000488066040c000200081e9101d207c40b8000c0301b900f141c034150400d1070840c0c90b1390000c0c202403121002540c062181508009880b5003000740a4101398104c1da1344503401e82001003c4501078050381c40c0445080d2032038004110a004c12916076101d00d4001d500e00b043c035030a000702d60340c80b24203200c40a50400d0b5420808030f40130f20a580d00507070f000e034400301c3c2e40307401c3c000e030300b8007000c0000c044d602d0048940c042111140001c201c1c1d181c84604218501da80f8000b8005546c0d1824941d0b11200c0a02460440d181440d2224010340c0c42030040501070342d888070154944a150012041c0550001c0c441101e29144811004000c03942840c1400d0140300800001a03946 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 341515656 1250 341514406 341514409
    0x12113d15030c0f03030503060d050715020c03010b0d081b0c030d0e1315090e0111041205060a0e0d0c020303070c030b0a14091207050f1902010f050c1f140c09 69
    0x25241c0e40101c0721142c079800d044c000660701c5015039410220941d4108880350542c584a42403d842d41c00561301400c24a04401442e50700107046195181c040c0c0003005009417513000d000c40c08041c16005018140100f1030a02c40c080f0310700044038a03412070000d6800c03411202d40041d0408a61036608400106011500d980034640b03207000d0100d00020352402c0001d44d03c060101d00308206036100b08003140755103a1105080c1d40782034200001000711a003c4c41d42d12901c44041c2001582c070b0400544103440381800150340300d10b180c42201c82034820200100385608100000315080c0042403005c0383c15020274010f00d40029220300c03a02014521400300002c0d5450404840e10445001408038000c007100301c024440740e401d0125005440c108020041a980e98542c02c0443c90302074400b0410115218069001503c220071902912949100340ea80c0c1d5040031185000726003038010010503014607004120b904201948148400300850500c0700046140c40030013802c4408034000301c450310803502d4001129600c5 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 341516906 1250 341515656 341515673
    0x80106031208071e02030702060705030c0601060f050909070908011a0f030a241d01060311060901082701291005030a050603010b040912113d1503 64
    0x81c407501e02d0040b001d49000c600c020490303010030344a8081009036509a5584510038001c680c201d50700540307038650f1901689407007940c87d4404a01d043ca1400351000122300c4c0c0b0322070a8620b0303150301541d5500d030810403114100321801c5d001a1000060150b07054002030514420301a4050881041c030011885161510610549002d8210060720a0304484000c9000941a40c003100020514039440c142c19161340071200005d1520000d15100401400c041001b540015085002070320300c034031b6082422207580c03801e0024900440e08400e01154840c0300081d0b00d22030410100c4440d000e10700203800d0240c01094107508655405880c4206082c25031079050ba01d07da0458404268103054480b6a206449000018070600000c2e1040821035104d40105609540940100c00060001442040104a18a00b10074820303076502c01d00c0c01007034084810324404a80400e2031981c030030031124a01e000e0f000030b54018110405450315803803012071500100c110702a651040c00c50408402c03050050780d50841c10400130 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 341518156 1250 341516906 341516933
    0x504050d0605040209091c030e0c04090b09010f06030206070201050c1c09032306060108090a0203190605060f06090d150509030a200d050a032301050f030a0b07050c0f060108010603 79
    0x8183d408940c038180147e00340d40c44180a91300034a13000450424442c1414146501c44511f260721030b06210703c41041c0500c0000841c02035517520002c220b0802c0c032001c600c0c192903a0b8800070b03505c480c09001d0100554001e8009000c401100004d0740e660207428041d141d4841d0703920003a00000b8002800c2072003041080030720116403070981030301a980c403050b10a56654800008001504026044010440b801e00400060b9002940182924121030000c0e403059040d5041d4038096a00c1410b00000c6880c0f0704000c400e0712101c0f01c5c0642550314040612051150090700144211219102c1e459030080e80d80c014803440303004105680c040c2d85d03160b00170f07403005004c15402c1c05006404001d9904510f207030782e00042d4848805c01d240c1015a1583c08042098009012144c903001c0841c400071540c1c282c0e183c07140d01c41c80c144e61084030b5166000c80380b4400c1c950740d0703d00d0072401000003400700c4c082986a400390300036010b14446801150303006c8010801d107604100d400e0b07001d81c4a030782d10390000b4020044c04003080300 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 341519406 1250 341518156 341518171
    0x303210709060503060a1401111c030b06070201080a050606040503060408031b0424050d021b120a02070b090a0f120309121203090c05030102070c091512060c0504050d0605040209 78
    0xa00b14201140001c0508409100e00680305a031002e01c0d07102d07640142720301e04212420100707403000304000034070700399650b90301c0343c43c0d140024505401405a440c1100a0310403664040e528100c5580c0c5100b060801000702500169005a0900c00042c10380d5042200511982c030800076a61681404884489002e4601c540382d080540203000a0010080300c540407204102240d5080700039405d000380075945489501500c1030030a00014a40503501c3c0503100790081c08071403c04a8441c1540119854801e0042c01010750040e0001041001450789148c06850006002407031044c0082e6288032022004449031300c09291a02d1128000c2c0a0541100880c00140408440341e800c000c190364031082a1244004c0600925903619680c0c030a1020420b08080a00401303402195a041c2600303020158040510a440b20a401c161307007050050440d80820040700e02585034074a041c440755603124003a20380000401e04200c02031100261540e04c024800f81d070031b8042c0c1e0f4002440d09003401440301d5a003008000a = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 341520656 1250 341519406 341519417
    0x303020c0706170f060d0f030c050c041109091801060e0109050f1501050c010f0507020f0f19080f0702060a32250503031e1008150402030321070906 65
    0x300c2c21014402c0310f036a00009540d1901541e9607444000390304440e900202524135000340d07641c20b040607081488010b42a000b48100c61203036000300c040005840342582a07140c40b240078000c2d04000d04043e40516003003541c85c0500004000704c04071303950850740580e200420900d0042d004006d6601c491040d00d400c402d607075820340481e20303080c00320780e08003014420028108400000d103206464000e60010140a080000910060818010080d03403103081c551403c41c68050b1810800040800040c0d140744a448800002d0150000d503c0b00b00058011010410b02c82c0820000c0c8801665510001d161600058582411084190300505024114255070070380c00109001c540302c10b94260410f0710900d00800d42c030299600341410150000540d00600100180f0004c024880100880c0c00213800550000003001030b6940c8007100480803920901c50203450b03404c152044071040e2401c20400b43c0c8a030019040380d29003070300e00d81e91801803004c029050740400000018000c40d186e025004078001e190a1408 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 341521906 1250 341520656 341520677
    0x60201020405010e0f060d090c0614040e0c030606070b010b0d0b1905131806020702010e0907091e080607030e06060d081818090601050a050a120303270303020c0706 72
    0x203013516050300100f911500c0b2540c030408203170ba03540084504c2c51018480900103403426142c00388480f4064043c103000304d01d25050109000b003001060301c04813100b600c0b10310066202c0c6644244950f0000c1e1510360003c1042281d1004100ea800040f4000c0614510040d543c0e040300d000315040f02e03d00e0050320f11800301030465007000350b00b0444180580d082100e41c200c840302800f101600078030b200300081c1e4031007880c01110b8051060039030150500e54000e032218010b0130841000c0150030303401110a040843c88003201400351940141d0f00616070002e480303240501d42e49640250349001012030310480040d48030b101d48501c5001c1840580d400c10b0040c0c40100031341500d56614103641c09501142c0030307540c910040d041069565680042050304039001d2615550030040368403501c1d0102400f507103010f8822104000340c50300784450108100e4402c50746054007910301d99001c030058400b0540040041a1039034540c440825100741524000f482614016922031040e07244a0401c50182d1006040c03000d0b4504 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 341523156 1250 341521906 341521909
    0x100507020607030b04021c020301030204060803070203120c0309150a030608070501050405120c100804050606060f030f06040b1c2d1e0b010e0a0e0a021318050109030302090a060201020405 82
    0x110181c1041c2e281c10041111881075010070000d01030b070b0100b0150b41410030406401e913451a0300541c103a0307000341c1d014050152100403da940c0d202e407003c004e4066103c51003403d4408100c0c00074000c143d21400940303203000c440d00c2c0007603502400d03400240d215000000302c00d6017268061095030010801c03440503090480c0351400280141c002d0388607103400b40b840881c1034511441e05004041a801380208403a5003c1e29840008003004000c58040300c041c4503440102c2e58038038211040e11462850b80420310f1641e40d40c804c44600c0c079000072700b000d6003040e19030307002c2007940e6540415203100951085031030345004c0d80c40c10306034550307500000032030042c2d840c8088040800c0c4206203e6220607070001021240141f66809d0842585141b0002414032a009000480d03100c00892003c3d002c2c60380804140701c0c545a6161550300c07500540c2009502c26007880383d0fa85641318541001c501002c62040010f4100c5140e04d4850a480204004800080c0e0004203403441c0d00c2c00c40c0c08400034084501c02141440c0c1010f0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 341524406 1250 341523156 341523163
    0x60f190207050a05100210050f062704060e030c0105010b0c070e1003030c03090905010605090a080102090a14030a08120901111e090a08010e0601080c0f0a09050c19020f10050702 78
    0x1d414000c00116171009211030003004100390711941041f0030003d51038010612400e4490640300305e4407940c2c5101d400d03420190041440c0b014001448600140b648807684ca8900170070310701c0358103401c0c3c0c0420310004105500a2007028000d1000c0e01d440c50b90341c000c01401d0760a0a5a54000f100043d101c003060240020303a900c803401c00d40ea41810400c51200d814201a2a00603080c0c1c46181c080d0305200000c50074070f41c40b20203041407400c181d450642207612900d0003420f2380910900550800d00708801000400f012001755005900043c06503070311120692240406540a080d40030074070304a40c0700b40040f101c0248201001c503400c0d1400d540c14407182c0810040720340e6032035081410200b80414040c40c1035a506031702000510b007640080000781081034a403600d4840900c10185540101c0560601c107081ca4400c00c2081d0340002d05410003039050100560081ca001707010304600441c148284038042c13010044088600580b0380007030031014414100d0380c0c0381900380c1000824090411091051454002 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 341525656 1250 341524406 341524409
    0x11030a0203030c0705010e07060519050c0d0c1b09021305010f0819110a080a05060913060203151504090e191113050712150608130c05060f190207050a 66
    0x8203030f0030354412080c2022405003900001c1014180540c00002400e40c0d084801404107a03c0c4652142006611a2003580c45002c2d00304c1598964000051048216210750b07800c41c0310910550345d150310f540c00b20744007103a090a16000744501550004050710300d1010010741c48005c0c10240b924255100c2c1c0750400814030386011b4000c5103004110b841da496503c4164012560542000c4241034940070600c40040c0720203002e1b90281c50f1140380a020508508188800380d2249181110151840c07090b07a0b580c0340207610007030071480342042c2e0410015140e0f48140100d80355000500e841516141880038413021585031103d003105950188401e600045210301440c85c1241c0c0081305010040c000703101040c0f6203002491101000d0303141c08100450207170044003280004461344d02c10404048444407c480f264010b0003540c0103d0480d00004164188883e0000a040c0c4540c00e07000b000c5580d01d010030455000340d002c00d1003013000491000c0c0c541c00320409203800c0c0c1820f44003c0c10b09510740000b140003929903 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 341526906 1250 341525656 341525671
    0x6120b040b1818011a040e0a03020c060a02032502012a11010302070b070f0f05070503071214070c030b06010e0a14061b0a020a1e09150503030d090311030a020303 71
    0x4082c0001d400c544100640c042c1808008001d0240c0e002c146200d442c1c0c940000c9540c0e2049160450042c8020790020301c804015031316400404c080d00d11301c81000002d801076290034007188803c00580d280c0302000065101400034030031809070118031520000d400e031507943c600107018100c420303051171601041031030a13403d581d0400c1080840740104d00040b8003074031030458058005e00180701403026885d401480072403185071941c0d6003405540044c0084500388215100982503600c10300c10783d4045101207043c00c3c020aa9800d09030007011000c880c225043d0000341c41550000203401d801c00c140424107540700e5000c03009103041da807258414800a1203881c0180038005c03c019001c200c00300b65448a20869000325500c541416004444412141e40c03034181d520202e0040c8900c2d54006501100ba0354201c0c0c0c01d0003481006214141002000c0c0300070415284080c0000300452000210f9483c207100410b40451000f001082400e10303802d020340204124100c040680c0d00c02c000e805922680401540d8100e41c0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 341528156 1250 341526906 341526949
    0x3110a0906030906020f0a09081204050102030909060102160e190b1008040201030b04020d2007050304030605070c140309150f2a03040602030c010b01030b0901050607020a08010606120b040b 83
    0x426003001340c000d00803075070154045200011178002c5540c20803a90740444101b001215203580230003507504003902503481220f001d40d000f4800d5a291303140c0590f6090f030221061040342c094213039000c6100246e0485500c0080c00701110424010000c0c3c1c100494ac501015103141031108440d104042401c0da424014401d04000d1100d0206085a10a4001c04904c0342c0041c41503440f02444a2048000c1c040094a00140a51f41a000741000c400c503040d6005140c01802440c1041d1968907003102512004109108011081d1942c0740025588004400d42e141c0300341c0110749031408501030003403903440904420384103881800074120160080080f21113140020300031003d030007401040c0c00050032141038250038030700010a0125540382e000001e042c405034600000d0000001a80041d42107914180c3c000740c000c10204014032290410307a0040c44000d1000d48007829030350b5580b00690844140742c0081d0005940d918480281c00e0060041c0011400221410442d011600d400100c420450300c644044204 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 341529406 1250 341528156 341528171
    0xd3f02060c030f1f080c0a0801052505091008150909070605091914011b110402070f06091b082803050403140c040f090f030e03030405040608060703110a090603 70
    0xf55040c404400c9820003000c0c891071607111705441e5260f16008100340d00071144c8200c0007440300014081e01e40115951404840e14142070307409140103101c00f42d001d070184401003008134440d4440d04c0c2150390b0883c156a451440b820305070803600e440c01c82200241d10600d8a00c4c180103d500001c0303440341c101d8046040055990b000c0d2004240c801c41c00c1c0950301003500100800203031103000d201c00001c007840240e0b00e8001c8c40554a400349800d141403480540004000e8074116141d041c660b00504034180290a1000c19402c01e44e6048203171034072540101c1d100c0085480395904090403914210180c01188042c001c08041000c0c00c0e408881e0501c40502c0b0a00c26000c50018180200b003220044d40d004810780c13042c1040c41100a940e54454500207018074a42824084d00040c43d220306155981d201070040e04a9406480440300140501d50a691502003000000341595131882210003d145e0722004d802107252103007015040f01d111183d251400c031020030490031260b034800c140d00305407001400d0004154 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 341530656 1250 341529406 341529421
    0x9090606190e090304060e010507080901030507050f0c0a0c0602011a0f0d02031501061805010503070c11040e1c05030621030d020a02010506030f0c0a050d3f02060c030f 74
    0x1880e903000c40072580c0d42c14188003680744040014004e071441515580c51060300400110794620034030402034410107041c0401191584a5081550030100354640142001900340c4052940c0e401504601d4641c1d006e0011030081056580b01c10004200c02d000030001540720300000c5078544400252588500100001100140d42c2ca20600e0500354014040f00c1c2c0031088a144502c41401c2030060202080f807141e051204032440c1c620f20307010349006139142415602e8500c010b841400c00713260300715280c040c0303070540c0501a102d82c4141800403403044c9c005e0496001c0c000b80c16050480700c405c4001041030400800c0802c3d215000c89116071801c00c41142c0d0300c0503c02c9c1500e400c501410005941c41c03400040d203c40c4c80c1d6815007000380110401c0f8103540501807000d46d80d590392842d040806801c001d01c01000c210524120000b41100c901604498940c560030400c1d2482480e0400c565600407100040032074100c04424654082000c241d000a100da414041e11909203404000c00c0004800760000018221 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 341531906 1250 341530656 341530699
    0x102030301060c2409080a0201150501050a181716090902090103080a0201090b010303210606090510030e0f06010e0a09050c130209090103030f030f0204050a03030e01090b0a0e09010509090606 84
    0x3c082e04d202e0100040c188a1a140d18039500c40d03080980150f081081140c03006106201c4c100445005850300c07441c5c41c00c42c0d00191039810740b0821101c0c100b101c0302c0c8005003017414071800405002c1c041024108400c102c021080c040c44aa0300180069481c040b401e1006864440420341580d4100e03005903140e0840500032800b42c0b40c054002804c02c0b402100001c1090303008002c02ca1001921071003c0c4501804004c84030480728944035180006101a20401403070a003000c4401c014100f40c5404a0400358030352426280062120400c491035002000412250703242d88201904403a4009062001c0070658440e1070b0381c3c80018421078420001002d0b05245000c855040300c086c1c100c0036090844540c1c3d603040180421180340000000300707040c40740d00702c0400e0703061003194285c0780004c040c4c02195003140c600b140c20740d9141140b00d0600610b00408154082204007034210003080359101c60100c5200703810b100d00354006a0299001303204040a00c6201d10001c10b541d030340204161803240341041c0c500964441c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 341533156 1250 341531906 341531963
    0x30703080c030717121503101505030304140405090a0305030c0d06091802040f060f0e09070b040806011d090c130b0616021f080703090507240e0102030301060c 70
    0x4808000901c186943c040c3e00b024102103142c5c49925401983c5880559848400408507564190040c1e505103020414030f501502c081c3c01341c0c82940100507125000701e4519400340d0821425001901e0301c40b01c0a24082c011198000505000b43c05010103035900940a800060300008100202040038103500400d54004402068400802d0160050090145001850071b083c140d004500b00141c85903003240d0303405000100c49075501107040480c41c0c040d80b900d148c50090314230b00140c0102030002030a51018005803024002c00341c05407150307514081e62a0b040c1003169850540140c3c92004001d440080400e1080045070700b0744100c0c1d40071403a00030034402031542e00304c5c09503c400c2c0490212905003280841c10009882540c0b005414080b241e00303042b50f240c12000c941c0004220900007207803e440783d002407200030f00c980308491074141c03162040e14000c54440c0b0541102d21800322000301ca15840b01c0c0a0300f2849003030020354915414100020409036103003d010702128802c0c500084088a00150001d = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 341534406 1250 341533156 341533163
    0x40311011202040b0913021804020706090503220503011407030903030906061d01050301090206070201050d02070b010b190305010b160f0210090f060305060303190c0203060403032009030703080c0307 87
    0x543d80e03a1248102100c030380100c0c0405005007140c0c0042c2801e00d00a00c01c0f0f4442c1410702c100344001d130782c1c6441004060b41c442e580445646441c2c0b0186000240100040d01400b9a400303690002c100e110003440300200d8050380b189100f6810300c41583d10590b001c3c1a40b98001100b40750110724a405400c0640141500c400000d185a280190000707000325450264000c003030040b81207001d80d036a0341003050309a51104402035840b200c1000b0360001503008400401180528090150800b0001c2d2958042c0c0602603008a00f141400112040a800081464036441406040c01c00441d41403180b0145a4011001d10103421748407c2801014400d41c0c110052540781d0061420303040b09103c1500800004051250014061200f8404200e490103401445d1081e200507000394104039040f411711031242055403808007030103140408140540c40601c8403d102d80d029403000b0994512003021200c1c0d0207070300305a00140c00c0c0c1c140508141070f9000b00e42f14085940110b030301d41e2580c44448040e401c2d41318506004 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 341535656 1250 341534406 341534411
    0xe06031e03040801060b1309090c090525020a05070b030a0603060e0102090f01021f0f090f030e24040314031308100506090408030619180b1507080403110112 69
    0x403000080207100351204000240b02203580d80f007104070381d80a41c0c400b40c46203a090721740601801001e50722010b03015010340c05031480385585040c08800c0b10004e940802004621000b1380c0c040b0064851660005540e520003803420f800146c0b60b85850740c00e00d02401c220800d001010039850021500040081d40c4c0041c410010030060261241c000c2d40425504e502500c42d1071007481ca1580042454161048142c02210882817072284960041c0840610f11010b04c2d520310700b040105e6050a00704007c1440b82c1c0740c1503030503000e000400c100e040d0004080101c1800300c5042584221500e010350b000c5a030f01003e902043c0360000d000504501074034a240b2070001c0e48110004170300034002450860401d001d070f01041030f5210fa100b4000c1403c401c480180240c4402c00c0842c10608140d10f4003800c2210105200300100d80342c000001002c0c1c6e400044144150f103c6400554030711707159035100a84003080080c3c80c0390084075074940c4401d000310b03c00904084a0511101d00307607400303000c81c403100e081c44038001c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 341536906 1250 341535656 341535703
    0x150601140a030b030708120a080408120a0b041b0504120614040f14010213050121061706090109230c060a09030519020102190821240a0e0603 62
    0x1d000f881500c84080c401c0c481c01e2000646060003244940e401c58a80c000300340781510701c0c00305a85400c0058401c03607500500f04104200311050340341550145020728008241c051a450401068558800c6415080d955840190346002d82000031141225480403601070a140103041140083c5800d803240d541450071517040004000c0e0200401c106113214414151220740070980d114204d002d006801459003c14180500c80c07503004100000d8901031000034810303124099440c0c0e000b07860150f8814052294200c01c84482c1b44000e01040e94401003220082284e02421b499085560307240c00c9010306da4021100c2d038103541200900c541c5802440107840c090b41c0e03d412220003014101c1500c02a181ca00408440940f0050700d42d1000f51080e405038001d044040d4504c0315036015441c00354084900810400c0043c00c4551050400701a5941103100070b1403d01d4550f0483c4800803c10000010941220b1202403659445213030f003000340c8070440401c5099986000100e403500386903041d42081020715004 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 341538156 1250 341536906 341536927
    0x305060405010c12020c072117031501031a061c0603030c03120e1f020c0a050d0e06121302060d050f01050a060c030c17041503050f0f060315060114 65
    0x440c4940c0c074680c1d20440070312a040c070740400324011030300c40e61416044040c08010541e234840d40544070b0b03403640c052001807500940e070350200c020900f0780e500a55500841000b100352002d07030f142105164203090500a0310701d4060381008841400c64a43d104c1c0c20045034441c244001d00151111106401104022064a0741405010902241021030016088a441402044003402110441c102100041c1102c1520545507800721075200581e141d955403e00c81e1688000d010003e0010850186014214400d81d030000205070f818420f04040c011041080000006400700ca41b55901070f00e141802039800c0c040c0e10010f66107100c1c41020151542c1081d06100c0d43c0301c4e0064045048540881e401c3c55030940d11381c1d06481c000e07030080000c1d010a04412000c8085446807812015031078041258a01d025250400c0400514150800500003541d5008000a00401105042d0001e8001c9a0241246001700000ea40c404580c81c1c0301c081c0d8042c04d40400d04d04c0e40154030791b02400075041e41c1146c44252020 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 341539406 1250 341538156 341538161
    0x60a0309170d0513030c020405041b0e0f07050a0c060209030a06050a050f06010e0303071b12030207060201150b0405010f0924080a1812050c070902030603010c090501020c010f030204030506040501 86
    0x81900d605464080440c4c224a4200c40d03d041482e815110381c0090852a0204001458001c0050381c28408207400311101c81d6880703075060080c02d20344881c0204e6090080040f4400c0c00700900410074014204041340000e86c020940b10401540444090384d01e090001c0424104030212800610320b40c10a4140f00e00000207401180c403038108803d496031075030380c0c1c00d004441a40d00c8210040c0c00d500200104804110b0210308074001c00080c0b02024500d5595081c0b070410084002c0d0190010b03080f52800b801210350a01506c0c04410160040700807031810490300d200507100f01d02c83c850501100d42010000f4500846a00004052107102c081c2c14500140c2140004030000188000180201000400705181303407058003441021401d40343c6003000d65079140b03103000f00c401641200b449030600078800500400c210740c602034000110050303100e0400d07a06041c2910742d400c6025080c0503480e2010700c071599000502c83c9406409181017240b810090b58141c00a11854001034894007840f0200000e100054 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 341540656 1250 341539406 341539417
    0xf0b040311030a0b24100302031006030e0c210d12110f030a020304020607080c0d0f0206060d111c0c03030e0604181e050901050610090f05060a030917 66
    0x303072401c2040c01954010140c03100d0805034024942e841c00300114101e89440c00400031800c41c03488502d00b4000410000689404003a20f040000a40000401c0b080410102c030703501c01049207083c2800b00c40c0401008070b448003101040303d4001e02c2000c8207124011004440000318900e0102950a04104004010f0100502c00c000c038503c03c1c1420000001d43d04244200c07100319404410b2030b401c41e03d8610744030010f03500c080c005a80c0088244006c038080341250004010f50240400108148840420040c012071004a07103002550068030400030301d503c07442c291202c102d074014090342c140c54090300007492702c1e01c4203001400c003018a84041000c0010405e0150203803030180d00c03130311003003440001001428030946c082e04506080c041108602003c0507000750100952516010035486403504200c4100c2c4d41c102c1d180b8400c1c1c0c1d141d0051050381e04051507980701d002c1007131900000181c10310310b40e82c04482403440b43ca80500300005480008902c0f9a004c80e114551101c0c2c808040c0c046c6d40074101d02034000 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 341541906 1250 341540656 341540663
    0x2090d140c0306010f0f051003090218011d0103020603310f0512030106050d050a020904050f060f09090c0108090309090712050109020702090403122d0f060305061b040f0b0403 77
    0x2c200c008120170303124060b110216080d00940290041c1004103000307015245140d80f2081c151075101d20750050760b80320000f001ca81400d4010141c0e542c50860003058102c8541942004001407c0040c00035031034410480758460002c5520f20004000306100114025000c82440d8101079010204002c2001c02104c03076041901490446041c0c01e4000e4800c42107110030f100d00300c0840d1041001920020300f5410560380090b0100f0010305007076404022900392541160300c0114040c1c4d0604000a62401e644001c00750348054600c42d289281504505940d080c4940c4001c0c10f008120b000070b512483d04000312251040050030030724003400c1059010b0f181000f00324001140742d04020000c2524001d070302c00e40d50080d0b00245100c4036610750740c0302956841c890300c403030039a126194483d404030f600610180b00303800d9440c888104079807011102d5043c102c41000c40162051030803c04c00b000452400100f05401c184400c1c09540b498202e00180e950700c2c40b859200048d01c148024000954007280005013040700e00 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 341543156 1250 341541906 341541913
    0xf140f010c02011b080f0702100207080706050f0c0d15120b220302030d0b03030c010c110c0d0b0a240801090201090b0a020d051308100204030c080a0506010902090d140c03 75
    0x8001c0c0f1030146440744113104800241c841d03000600b00c41d051250711600210740380162000300d040c4000281c2640d002800c1941c504400140d02e030b003045150300c10b00e58420b500803500815803c08081c021440d100c0e091041d840c2c29213075201c0100008503882c81d80000d11010100c6201d2001600c0d18842098084500d404004186031011100c10218100e500d6005e600d94003861410301c80307140f00710003418600301080d05440140011201c4040910800b11948401e4460145a00c80c00c008a450900c441c0d19084c001c80d07961046034000340d140030449400c4503171004041a001452104205110204014100b0242103d80c0c006141036044d8401884e250003a42c40091050700c40716400c2d80b43c85402020346c0140d108925400c9584c1c03042c80900100707820030800c83c1c48160b444c542945483c004401000c6442d40c00682042002441c5400ca00202280c41c0039100b0404292942500d40304144500d0030601c0d00050034019036030b910103090070b615501600501e0b81c00094001c42da5a1050130b07194074002d11 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 341544406 1250 341543156 341543171
    0x4090b120703031202180303030703050f060307030302070e040501110708040806131a100506040603020c071a031f051f0314090c0f04060f0e04110406120f140f010c0201 74
    0x1801084100640fa0151500101010000982d400035030020b48815100101d035015400140c2e014001107004000b241c1d0f01250606213014060000440600358038460b5000000401c0007079004200c42c000c60b41a412498015552400e141d405050b000800300c8200000190100030420740304090002d0710008001c40d10680e8074000c00710104000c440b005041d0300e02c02c8100001e09050700e9010759010700c4481c2020070f00340d514000300d203881e001904080e002c42c1e004150680d078180c08000b1107008003002e60080400e1100907206410a11000c1c00f0b0411965294840312000b0848000341c400411001d40401000354692551004246040b21010700090a154904d41d40c8068017066a00525450000c1c00710002d242007009645210020010b4015440342000182000031500e0440142400c0c1d88281351460185001c407180078815506a01c1281750020038056908850040c0740d29a90121f0ba907215410503040040741e1070002c1c9040c0000d0312034118490749090064100d90240c40c4070303400a0001c003 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 341545656 1250 341544406 341544439
    0x18121903090c05040e0a020310140606120403140702100e040f0504080306100c0503040611071a0301050904030314101e0b0a050a0c0b011d07030216080a05040b04090b 73
    0xa80340880d010b04514880c1505101514041e400000c0c0041c2038004c8800080f084e0340400c1c180407a18a04208280c0e440c1c440b25208000b0042d0035902407022a000307460b0032458600c260001d0000740028081004180001d0104211042200c00c00c81d0018a448141050250024200c000c1245114011403d194a226801080c2d0066602841c0d101c80a2415551885c00740915046050300328010001918000004241c0a00061002d45065564280500b41c2c00780401d15194140d0b0060180c6500d00003500010b804500c2a40d055680c1102c408450740c5139030070100c014000300210300e8405202d043c20700c6040401109503408881e440c03d1292140c03000020840c0190015100f460405101040503540303061180009143c0c1841078108225200c559480310490440240c0117001c010041c1d0030034100404a000e001c82d4808818a0309624055120000301d012043c100c600a02c40c00c0d0105201c0b9005000744143c401600c40b695115803551750740d0a54030081d1441c99400d500880c2442d034000d82a = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 341546762 1106 341545656 341545661
    0xe0303061e012304030c0806090601091a09070809010f09030c110109080f0c4e010e0a060b0402070b0705090d061a040c022418121903 59
    0x4890452401d44106d40958001056507840340080004031140081c0d0107042d03c14100010442041328400303003069100354ac0361154049520350402225940c003864091080000b48000c0c0318507400f080f044411a036088401800280ca641b00710008a030012502402e102c1040c034000840c107a40b071440d10304254410300c4000381070308038421042a605e0a203400020b8003100c46101e0101c0512450742e1044c3d034140070480b0100d40c2003489000c0000003240c0340645803904002c001e01490b11003600c059111110400c1c100c511503d00305010324282020710a0320300b00d582c00b50400c041d5440703008007915107400401586a01000c1341200e400003d80a00980e204500081690582c0304002020801541c1040117250115403100400c0e02581201c548220442030310b0356055003541d00c900c407003e040001681d080d0f410a02c50b000f0300e0030012480c000108940c40717601c40200711620500d4411801e = true := by decide +kernel

theorem cover : BRFrame.Cov 341366906 341546762 := by
  have h0 := BRFrame.cov_init 341366906
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341366906 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341366906 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341366906 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341366906 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341366906 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341366906 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341366906 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341366906 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341366906 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341366906 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341366906 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341366906 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341366906 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341366906 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341366906 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341366906 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341366906 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341366906 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341366906 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341366906 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341366906 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341366906 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341366906 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341366906 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341366906 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341366906 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341366906 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341366906 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341366906 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341366906 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341366906 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341366906 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341366906 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341366906 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341366906 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341366906 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341366906 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341366906 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341366906 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341366906 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341366906 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341366906 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341366906 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341366906 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341366906 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341366906 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341366906 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341366906 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341366906 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341366906 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341366906 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341366906 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341366906 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341366906 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341366906 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341366906 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341366906 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341366906 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341366906 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341366906 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341366906 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341366906 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341366906 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341366906 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341366906 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341366906 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341366906 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341366906 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341366906 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341366906 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341366906 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341366906 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341366906 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341366906 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341366906 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341366906 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341366906 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341366906 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341366906 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341366906 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341366906 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341366906 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341366906 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341366906 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341366906 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341366906 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341366906 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341366906 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341366906 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341366906 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341366906 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341366906 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341366906 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341366906 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341366906 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341366906 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341366906 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341366906 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341366906 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341366906 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341366906 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341366906 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341366906 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341366906 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341366906 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341366906 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341366906 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341366906 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341366906 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341366906 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341366906 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341366906 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341366906 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341366906 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341366906 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341366906 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341366906 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341366906 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341366906 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341366906 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341366906 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341366906 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341366906 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341366906 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341366906 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341366906 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341366906 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341366906 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341366906 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341366906 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341366906 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341366906 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341366906 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341366906 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341366906 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341366906 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341366906 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341366906 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341366906 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341366906 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341366906 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341366906 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341366906 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341366906 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 341366906 ≤ n) (h2 : n < 341546762) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
