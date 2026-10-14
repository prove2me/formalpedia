-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0155
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T18:09:01.002298+00:00
-- url     : https://prove2.me/submissions/1ef57141-2084-4596-bac7-c560065bf7d9

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 27697847 ≤ n < 27877703 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 27699097 1250 27697847 27697897
    0x408030f09041d1612020f0402030903131202100206153001020a0e0306010b0304030302070201050c010e0601060f110a0210030902100503160503011d091c09090f05060303 75
    0x41004904454079440340000d0240c822001007404c008400c00490000c80082d501c44007851071220350075000354010000400348882d071415502540e000100041201d041950054a41241c0c0c01c0c1d64100700c0e0761242c41c20a0404605c0c2002c0c4001c041c00a0748003510300c6e03092117410210510000c1c80018840c5040b03402c61100100320b01c03200c00581814050300201c85400a0006000358080990b520008004408415030380c04c00113485030407a14048981865550785480c00c0700290441c14040341041002c01040c22182e409000700c8511003045000341c010303540742080252541038140c86c5072050111080d54503071442d40200740c10003a180c042da5400e5460601100440092840c10780080d4440d011091440105030702802452140140e20303200c5101401e00d07541500d850009200301690120007440d42d400d01d104503042d41e604001c58008807008400e2500c0c10322303420340101a50400180c40c00c00300b08034901e168040d0f05100d001e00c55040029040000c0804d480c1e11441c021080000d910200001b02 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 27700347 1250 27699097 27699101
    0x507020d0212010914060c070206030109020d02040e04120f02010b030d080a0e01020c0604030e0102010501050607020120191a01030b040b0c04090606050408010f050c0313020a0306020a0203030402090c0408030f0904 94
    0x4995100b80003000118800d01e4020007503581c0700d803144c0861141c0e0b00000c05c0308824804990f601500208420709682c0782150709030203580111501c04401d03809200001b0401504000240601e04c00d900792168003840d080300906c0204809060000c582c180708080405072004100070b50160410302d4401c0b11540e942c40cac4500500040816010690300c0050154640d5030007080c02c0380981c0c803da41b0540e4141c42d8000490a0b250203000e0310780e001d0000c1045000540c01030f0642120060000c8203c0764255403c50558200a6805c411b0641440b5140a8504200c840001041c00700f5203088070714125411521210640c400080000301a0007a07400410082d01c04902514000c215a40c0c0500206885500040084c0c04c91310580b28039608002800d07040310400c0c0102e51103a0794031031207075085a50f00e0144d184002d521100a13038102030162008008500e490008050030040c40c0c0044d07030759081a105200700000d0003020302c0040e5900780400d11190101000b2200716003c80064039031101115000100 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 27701597 1250 27700347 27700369
    0x703020903030c071202030601090c0f030e0a02181504020708030604020702030f0a15110a0f03020d060801050a060806090a03020c1e0904050a0510020a0917010207020a030b0415020a0507020d02 85
    0xe007480380080c0014964519142400300c5c40c0309600762802030341da40213000117a405000032030022917a2910444c40c4079100303038000d8600142c840122001c0307645603000309002a00000000d0802041d520070401d800101c600d60140c40c440540d0304500c2e062103522202500c0c080030700706a105507000250001555030410101203034000b50410384090b15034600e0015900902007048041c8141404550b2035204080c2c4c0560364015819100c0814100740a28100c00070750120040c40e5000341e4400005c540300c0c50907c5039030300c0713628a00000204281000d02031881c18800801e03501c80c80d0b2021000c04000b82e408184144020415205003200718011640b08011440713200240f6001003001d010402886030019061441e40d0080c07060718468418144440140d00c030740c1075950f01080c940d04d030806c00003424540100f507200c250700005007031940e035900050040c0416401510103407014028041403250702102110310403070108045151016111010b0418056000068403804414200d401503494139907a0f05 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 27702847 1250 27701597 27701617
    0x1b11150709030b0a0504020906010f0206041502130602030d0e0708070608040503120405030306040e0105060d1b12080a0305010905060a090e07170a11060301290403020301090804080607080609070302090303 90
    0x90f1292038080c441800400045a060303204540c07003030109009501411444d074120707a0b1980a003504c3c0e03585485441c54a2080c00004040c127508000b41c880c0d40c443c2241d00809021a035000c0c1d81d070f900c1d00b0f6400780c0986070300c02b54a40007500b1400c010801072200080d41400c0b241e00342030804156170785081480c154082c030100e0821900f441420402001000b00c001c1d44155021241006181c01d0886914222070040390343c81d0304030400310b0703040c00450020356000504103100b1804c1900d842c0c94845002c2c18801c50441101c0224012a11900060305070150038003508941104009d0703031500e0000201150b5040c13141c1c1e81c10f140c1c0d500c00001348500610000b0301500d000c0700700c0809021014215981c1c1c19180f074007039a0107601224580014500340f0201d83c101e482540203541201c464900740b000c1c205000031915255a420403000005031030071b0244501040c0501c1d0f0356504e46250000340317801c0c484000d00a50412014004005680d520b0700c038042e4001d0480e240044e01d40b100c0d6400301349184a02d038214 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 27704097 1250 27702847 27702863
    0xf0c0503070f063314130903050403030f02010e03040603020c010212100f060203040515220602010207120e030d050c0106030206030406020301050a0b0a0801060807090909061b1115070903 82
    0x25014440d50360090020382c0c075402c8519036081504c0402d05944004109942804100035004200304c4c0881050b0140d0080300403c0d060b03840d00559102d400b01d0b01000e40440120b64045801c00506400c50800595100c4900003440003042c0d03840c0103900c9100d5401800e00345035001c02c2440801c0780940c15550742c0380c40c400307400d00306040501a940c2224001e01c00d015040e141d2440100f205031010003a1f90071141d020f0b181d01c504002c40d2042d072003a0b4200e0000d8a07038440503514480443d003220710501c00109000d0700011b03503507012410809101d00408420304107218100321452020744002500301c040c1c44040c0360003500e460440c000e1501402d4280d0000e5030101d404001e10080c013010b540118122041210f070541400e0707946424520340e00480380302e1b002041082004205190040e24800c0c1e2010480c0381400a003511104c9560848805860a4078000d95881c56420103034814044032450384401e090404c50a06050032050f40e41100c0c21010000c0700649000c1681c0c24001c00d008405503500c0030300 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 27705347 1250 27704097 27704123
    0x10e010e10030b1305010e0304050604050d02040b06041202040515010c0303090305090307060306090c020a0b0f13210305060f0a06110313080303090706050421031403090c150a0f0c050307 82
    0x41301c60010800c0b103040e0b8940d4a040003400b42e4460000c211412900040c060605051405081000c105091135069810907241c00c610103035a519840140050080c020078a4550005801800104c03040100010780d0f0010664450206a0700507103440700c0300d64585404a90304c14a4a4102c503a4042c02030321a4040c0302d411000f18100350140c11200a60340f020b6410400c1382040001260744820b640405000b2640c8400030401d2000c103640e10303580c001d04074a00c0354076030560381d501c0d0b03000311000007840d40c0500340b801c3e007076001180d050041640008003100c0201481e100b510018948420b148191407e02c4141c07120701d80301c0312042c000c1d00c4000161300984070b03500d50344d6401c41d512a4000c840341506800340721030200c2e02500410a80381a40c0908115080407400d00c2c655080c484264081902441400c090000d440100703500154810203200014104680707140c000d101e81100e44120010310032000740807074005103603c41940e07001c049691038017003010f0f1843d040550640c0309403280039001d480c0c1c40c03070 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 27706597 1250 27705347 27705361
    0x71104061a040815060109060507110303040306020309010f0507080a020a031b05220b0412080d1505040608060f0f07180f050a080a030903061e0501090501080f0303010e010e10030b 79
    0x40c004035403c0300142c5140201c2c2034000c030a207500031140240442c036598000d1105034842d00242500c28458030070400c1320010716000910f1608180e00450b800c90700082080f00041080c00f03480340c940c000c0322091001e030a09032000341c2510320003849400e0f160303030202d208485c0610a03040003003240300c6803c155802ca13645541c01032090384000c41c42c2d08071796178900c0581030020303101c0c0c120004c83c4c403001c209508290074100d640705140340401d020b0f28001c3c81842180d10701d000d544100c41b0481200711040d0040d83c5000140300507140b1940c4101100d8006408009c6014144104264444c0041820310307145c0e5290002568058845084d0a801ca01c0000c0040392100d03001147c1010303a6811140d000d0600c0d61389002540d2030040000080001344415020000542590082006403000c141c0e8101d644030112034810031a5000da01a111003030301c50004004031142441f5060402e18048003940c07556040403001c07103505406110f064400e2408000090601107100b0041c8090b5034480320030820390070069 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 27707847 1250 27706597 27706649
    0xa030b070905150d0218030f0f06060105070b06040e030415090302091303020a060e071a030a060f030f08030603100501080c10030501080d0e0604050301020703090306050f040807110406 81
    0x1a00c2802080540d100801e2034601072040764511986125082d280500e45000c030b1029400c201d40079007503050404051416554180250420140200c0003070003015024452a03241082c09000e850601c07000b0032581000c2217806444641c000001d071808101c01400885d02851403007194812034042c42c00c1c2d4424000560b110f8041411640200c512906a0f1100100460030700007041000300981d10481c0d8180000381d1940041c1c10701281c078004d9900b0f1540e40d07891040c19000024a10002c0d01740041000700000080c030860000e060f40a0343c4490b0380d4155034a464045200d1007014181500c0800010301c1982c081061405042105106200950f51101d059540f542c9142c5518401c0c4400c880080c609407181c460a4121a403590083c510340e8041c0348240d030000a240c40d01ca8010030100800302c1c10340c80900050001c94400d540c0e008085144d403c100c41107170800342c60000604800010300000c5080a4262044643c00043c01343c0701204900019004200c582c1c09601c8680843d08600c0c2108020 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 27709097 1250 27707847 27707851
    0x3090a06170a020901050d0c1709010c03050a0203100605180a232e020c0a030b070f0c030e010305130c0303090501120204080a03180906080109060e0303092a0a030b 72
    0x3284241076503180c0861800c141d01503420520b0002d03105020003281c10750301d40c004154000305410a610070484044160110302000c5074401c1050391035aa809212940c540304c1c10754050315100c011415410000d560001c0c11085204810800c403020508200e914294400c0d03a540042c000d140d580e586a50300c036402880034040c40c440c01c0880b0400403881050506104180380700001c156101c0302c1d8400030f08095800d0202180b42c404510605800608644a01d0001e00155000d048410030515005000500d859059480b020400000084010000f500000e15000c03400090802280641e14005030009401300d16002400e0041110400024950040303103100981da000c1c0da500e00c114425881c160140e12607407040d400142d00240307410340030038459410448400d603071a00312200b0790754070560542510502c0e00142aa80d641c1e1229000b0840c075131081014100d1450003540c110f26084010300d40303c3e1800000d0b00644518404455024010309840100c1c5900080103c0c1205480c0e0410804403002 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 27710347 1250 27709097 27709127
    0x1704080a030905040f021303060c030f02030405010f060b040806010e071e11071a030610050c0304090e0706080f06041109150304020f0607020303160312090506040201090f060c0204090503090a06 85
    0x20b003007005c190a4006000b142c00011b48841c5103c0018995920440240401c580300d200b0107659030051011075038640003d50066024200204400003165001000c0717400e207510041c41080c003040100400741010448504459851051030106e0b95810b00075601c038880c2000840603c0b10720101c250905030010381001c8040c200c503040725001501c903e00103030004014011100d03a01c00c103100240d600e24102800d0340c00e4a07850301c1d19a040515451420b880e58002c0c2d001103c9554464130204c00005e070406c940c00040c00640340200c001d0904048007458264082d0020b40140c0d228038101c0002d4042c001218154140075024901c030700c07070800c4a40d00e9030304150b408034800c0114003070100e12480c042c0c069401854004000d140390050700c05910602104001c000c50512044405400c036003240c9108030340c902406040a03020701d140c544001040c1200030b400000c01c40e00400b4040c0007265002061014195041c1c50004038141c2038181a403541c080e6124003644400028008226290300c0600c0f50718204c1 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 27711597 1250 27710347 27710351
    0x6030c0d0b060c1504050109060524030c06070b07021606050a030e010207030f08040f0f0602030a0b03060106140d0207060203010f0302190302010c030305060613090213060c0b041704080a03090504 86
    0x92400400c0503c2c03143e42d164181d40d03840340100d6a00f1021002c201da402c2842280001800e416642e90002560b0044922100e41e08006d8040c00e0034001d00030f13807624900313401c0f000390240d8407881c40040c0150103102c10103005940100001085c2034000c0080c04c003125030180328a90110ba0710345005000c2c2d807121b0070510001c3d06040b00c6000c144414001d54600541c1074076084118150315008030f0320700c44010400d9800c100705200c0c42010680c440e5604030207600443e0056a41c2c41c020306000c040e0748001c0005400303075201c0d0f401003100341da0114110960421400c590b996842040391010083d0155072009841c1d14800400081d524a107094880704a030700c00d0380c508c500c54071503c01401c0b03450024400a400305015503864030009102c5d43c010381e03000340001e1146040503034aa403812502d035020740004550650004801640c02c0007401d19200078012482c08455082065840c071203503410140c001000750600049444a8924401c1500c003c0e01070704007181c2d0154160706000b040ca040c40d00c1603501480c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 27712847 1250 27711597 27711611
    0x1020a140c03071205041a181905040c0c1a040b010608012409080a0515010503030c15060f0d030c0204050c0306060304030f0e0303071104060b07050a0803040302070506030c0d 77
    0x225030300c15200e404080038090350a0002d1030f15a5101a03119180c44010800d08000204e56214200e0145000304441e00303074607460b2090a0380345040942c0f00d204c52031040c060801321800c1c91755404801010340f00240c4000c0391026000ea401e0364a025001c0c4000c05c0c41d00040300e04100004030b024014410f50069403880400d9a030740d2000e9810840038020b890040901002c9051040300d600d070951412802454070544099940000d80e0518070f00510464050308018801c400d0f030140041050b0240c1400c0b000f440c500350301181596034910000b060950443c210340005280e40e5100c1410000c071000c0a0501d0707001036884e02d0004c01c3d10711a0a401c0f480b9501d00004aa81014032f501130b40c2c41400090032a5103140c0303460b01d080c0c0e202c001d100c0440381081a4244840711689040c800b612241d8810b85215840040c120100000c4d2410380e08200900c41050150764003060001070540b140701e4122a98659948890070200c1c18407050340c000c0c64001c040001408190b0301180000d100e07a10020004110308 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 27714097 1250 27712847 27712877
    0x1107170c0901240c02010507060507080603010b040e030702041a1504090c0206010e01030b040213020a1d04051012080f0a0f02010b0d05030a030e1501031406070203030c0f03040303090605040501020a 87
    0x4460f402c030300400d004032076010b089000b901030359100d0290740c01410028100740d40c0e0395414095038412118403001a002030103002260609004a03008400c1c200d9007808007503000403c0d0303640e03802481406403299403900381c0c01000800500c00159060343c0500b802e4155920346da009407166100b4402e032501c0341c2c54540e071014a98404130380d403416100201c00c400f4059196450344890740320017a1081e40e100c036144106901c10906480241403811807501c88065402c101d52a2041d03580701842801c2c011814030702003100c042c100503108820f07070b500030240c0400110f05e800c080d4018000c01440000d0100006007000c103064100d0411400c8000c02e0340280001c12484044c08400042c00400910710340c828480707106064000c0d040802460035060403104070400e5081440c0e07440320207030300a85421541c241511100e0b40c061100a511603204d00080d40756041c42401e5105e588101802401c0c4c5c0c50010003c2401c1520079001401250f401c20303402e0010303092904085000b1f600014544011400300d8004000f2 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 27715347 1250 27714097 27714119
    0x60a0516030504081215181b21090102030103060b031f050c0d09150c02120d2d0621020906060c070302060c010507090b090f011107170c0901 62
    0x2040d10000c04215200e00060300550141c10064801c46204400b8012414841c0c01c3c160254840c0711350702e000c400d452a2003002c6c010340000500d41103110198650402c40040c0340c0640000444241400013607071079140704102c03003a900800c040f03036082c081c80e0030038820903036015006503042e0707030003048100410040201090b07034500d03001403040700d501d100000746c615980081d408194400a942c0b070312883c0ca2a18000c0c8011140f01d814101c5a880e8810b00c043c160802c03621070043d040c2258001412a03140c0082a41c005003d1702c01805681e5454139071254602d00426401c001e440c80e0031141414103050707280d02c200680014020b00f000d5074481107192520380b41c4001074691154019200084e90384550003170009551207100008020720031000c00100503140d20b80103013a0103110be000050a8107040f840204000740c190b016100084003880f140c003095a0b0030481c0300c6065004d080c0b007150700e5071081045041480991041d643c40680c41c0d100010101c020808050703840d0110750800135a0f89960040030 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 27716597 1250 27715347 27715351
    0x30702060c04030218040c18091406040215160c0e04050f030414090604091e03020606030604020a12050c040e0d0908120f03070507021c12020f030a050d06050a0b0705060a05 76
    0x503005483c1170b03009485107207207035480350402c0c0074030700c0b0700e11b0151121f1810f207012010305480360010769603400380e1042c0038498603d203029035040c0e0060401400d2a40014610441541d40401d400000007024104c02d402d10b0724021000b90b001d605c40400555911b005e0000002c201e9090700c00d03000e100c002440408012088805913401c00c01402c00380c8180c4406d1101140c80180f405400a9586a00b100400c903040a448444c200441c02101e10002d50f2070020304252020341414060342c0010140070040c2d9490010000b03481d110302240311071034050708041d8686450b0741022500986089040004544c01003260700d0842c22a460b21204280e4409040b40e13520041c0500d140c082c5418802c448600c009400150380090b041d251581c201100d80c1c0004030144c0c411102105006249180241000b2841030101010396035400502081124043c400d5240d10500706880100000042e64158503034141d4084805060301070031480e2107a842d4020342c03583c0c0e030004005407000e209020000700234a40070f006540c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 27717847 1250 27716597 27716599
    0xb070c111207090b0316092a020607030c0201090c0e01080d090f0909140102030a060515070302060402060a030e0a08030f010806040c030210030618060302011e02030318120f030702060c040302 84
    0x1c03200f403800140c240100f003200f41c081d900d401012420a104520449007001070020081c1c0010b5a10710302c8003001c5e00f0880c544103e190b4040150b0207201c081d4010a00039400242410045841c2d13450000883c01003a180e030005007000310912006ca8508070b00b50805050303482141c02c40e40a042001c205455591261040d1180d581c3c02e24014880f010642d0006003075144038aa5000c40f0780a01c804803030076030704100c03072100117596100010412407500382c0c106481c46100130b03e01c500c0c22140341c41c0207488610080000e8000c003400204543c03094809c1e80481d441500c1e10302696800c030b40f00c6c5080c0c00c0301c0d030007620120400c02c07002c03001168049000c039030580203036800b034070900101d8599801d00410444243c440380c18181e0751100000c001904003021207151805481c0000d0581c11031001410003030490000c0e01e100e80480d2510f41250b074002003203940003a00414003030406100020503d281c103103909080c610b84140400c03905000030542d0083e5000d5a5035801340e070056a00c076840a400f1f80110b10010b = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 27719097 1250 27717847 27717853
    0xe1c0c03060f1802061605030f090f040504030e01030e0309040207110f09012105100609150f0609030602031510020303010305010c020d050f0c0f0f032a0304050112090b070c1112 78
    0x2580040c902800101200c1034181154030b007600c6e442d00c56a0550b040507c4290803004001401c01c0f0910341f845083c910848201e904101a0819480080040034070f054850f06040d80c865035603030500010001d840c1142c8004109542c0c17540d562801240d02740e2142141d034018090500f044660746495800941030b5200c10108201c0b0200420050f07422005030302064402e030081c0490500d80c450705001d02d40142c812200c0114810140806900e41151158800c19150000510603c84d865006901d08110381c2c1101d80580c40380c840c16220140c0c2d91800d0fa15a91095132040c00d2240c05401002a40c100ea02980080260850040d002e0b40c4880301002c2a0f0001035042082d0400c450500c40a4112441c1c071400f10b50007010442c03c064680012950034048d250b03c040b4940c0d0303540c41c00f80f001020800d0403d90301c02e081c807281920740d81d517405640201703818010f80518100e0404000d60002240a030014102c5a107810903200141540c81c1c98041690344804881e2885c5807810200307170039103200c0050001 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 27720347 1250 27719097 27719141
    0x503070c060e0a08070b09010c0806011202041206140106081510020a0507060201060f17070303030e03070803130308130b07030506030a050708030a030605010219030e1c0c03060f 78
    0x11903518600490407140656a42080748607503004100559405104403036542d076803441410b00f2826150020110303021a814810302d204c1095101520b140c03c24002e0902c2c000415100c030301c060190040e0b4100b8541d0102d600694401d101d0b050300300c24014901d4075041c145c0380c2d80704c0c0d80884100004440d088402e040b0030354044814108024100505055031042da00242c1c0305a65260619405520000c0181c0d1201000d10001600c40800300090008446030040360801d6507003503444041600c0301a06259840c4100c0360f01800600803102c585030701c8030700f4503540c0c50084800e008a1080d40c03c20b800144180000400030a501c06c600103540d900030f06100c40030b90390220100c0142c040244820f07058001c040351040000c0b0108003420281c003000c005191200318081c40141101c0c0243e20240c110341c0091840d441c9600502000d03c046074261904010002a60300816554419504a900c00341c0510240d45c2c2806200000c160580b8407a8205010340540340255806a0303004408070451240002c070 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 27721597 1250 27720347 27720361
    0x50703150f0e0c2809060f140a0203040e1e010905010608060f0402041d040203010b0f0607080906071403030601080c040506090f1201020705061602070308031311101805040c0503 78
    0x9200d0350002d10030000904c0c0c0100c2c040c4040316611480742c581100b50032860303014441500255100044c00a503d05505101c40d6424010304000e404041c6c400d400c100010b8070f00f24184240111000340507a0904a003d5040060390680d07200040b00030717400c8407036101c03002041038405405068121075580d41d449000c7c0e2a500100b042015030304044580c490750030080051228050056025104031520010b10a4036250040c90300390b8568001152180f4208481c0100c142e4824007941d4030385800070103c0b6200c000e1540400c0311b44c07181c4e0700045c00c002d040d807803019003a10000005521030383c800e80c0ca5008945540c40304c1140ca0066006099002006102c11022402d0299005108160040001c400c0d00814503010b13003281e100d42019100e60304440100049032524200000c1c1e4056588002c0c5202461038aa151f064040034140504a0102400038800c2c4140c02c0043c02c19844020302036907840041c007401802d0211150281c8042d0703988050001207501c6e20b03214088913a03180f901d550386150b6802e5 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 27722847 1250 27721597 27721619
    0x6060a0f02070807180b09040803040f030e03100c021c050d0902011701030506180606030c010807020a060507080105040f060b0708030709030c0803040303030e0d090b030603030c10050703150f 84
    0x5540c6045205000000402ca141007210744000c24414020f4503001915408080684002103000e9000780908801d000c00100c041e000caa501ca504248950806c0d43e0500c0c0841d03440c150200440e90611580985800044050f0720a06005540c0d400300c900c4e01107110101f40925016000c01004036506001a14480d4038a4001008041c81403401d80746030f2981c010721503e480d40c01c0e081600c80358400301c02c10005880c54014117518000c00710080a00b0310f48480001d6a80f8048039906c1e04000011011031859402000001c0c81e10f84d02003000d2195160260008080c1d010910401d480f0303034284400c080180705507100d41400c1d41e044001c41440c0c0b0341c0030f8547c65415030026001100f04809140700101060005083d1070182c00e1010185640da481c40c20002c065407010241d4940c180c1000401d4090503801c14030b08812608451041512680d030700d40064114000c1c0b03420036405000b41d015400400d032250303200380e2040c800780d10100081e030001c901c8007a241c44980078462840e0400798003881800488 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 27724097 1250 27722847 27722867
    0x110d020705060315090103050708011401140d03030e030715060b0c031902070807180c080115031e0606022508100b03010605040c030504030305010504020c12070609050703031701090506060a 83
    0xc1013a544084104c44003140c00c09400764420b036400c0c3c02110080c00096003e0160388a0000a1140e8000c1541460040d18000080d08500e603c0307401c680d254401054080d802240c0010200020340b5100d10307590070485045c004140c03481e61040c1c035001c00411010440c009444080c1c98580003181810201c0c21140400e18480040e0815803160144c0001c001d0303810031684c4094456000c00500100d102e034a44015502c0e13004a1805204492006116441c1d4540203042402c2840ca004203080903d00d0540060780040c04c4451180b42c240b94010403440c0d00001d80901d00d04042c0ba1021411000d00601c800c407100c140140c0307000350084203034003044070002d0300441100c800003400000d001d60b0320303c0080d003110940c1c00c00744046602c9000b00804d140d0188545401070030300390303420751420000d1016151502c95424000003491000301b846410f00c502e503840b0010f0b495111085501c40d580780d0602511a010889420350140c400c60004900031400e4002c03180244000381100341000d2801c0010b9841e4201c2c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 27725347 1250 27724097 27724111
    0x305090a0c030f03022a010e040b1201020c060109020a0e0118090f060501020d090e010b0a0c020415051009030c05010503061206010608060a060203030402060a0503100909080a110d0207050603 84
    0x10320a861008610300c00c501e500110b1003100101c050404614020381000380d40e82080c25450307010480c15013600c1030040e42499200c401d2074048495044440010001d103a404881078102e241c000c403107491a40150b0040a01d03140110031201960707030341c4a00e0b02c245d00c1580c42840c000381c0f080014102039401140712148281d400d402e80c00202e0f03100c0044a00310307140c209035070002e651a09020805e55030180b001410003195450507844079801c2c00c5450081c3d203c10b00c2000c40c10200080c201c800648a20080213046500810034400818850462007116041d03000ea244655520905070b1070140c041c221006c100e81c0c1c840c055003c810310340070054506400c000c0146070403c181c4030344c8141034442840410702a00042c2c43e014a10f0a266080c081842d0454200c2030a41d4010002d0201580d50001a83c01e0101545042540e0b9136440c0303414080000c0c10350100c640207003083c4441007000f0242c009442c031800180d07202100c2d01071000c442c50752292203101040150300081360034480c81c02c0c078500440c0d1000c2 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 27726597 1250 27725347 27725353
    0x10b04050904080712050403030e090f010b030903090d0b040302070b0c060708130503070f0507050d08040909050f060c040501170f060904020102250801050a050106090603021305040212040b0106020616030509 91
    0x250540310b1000340105d510b454000950001400c0c000c068001031540344a802c2903644103003520703164001e8840910180260a2200e0000c000522003445c104201c1c0e41ca0b49019108800c140340d01e15100c0901c40d07085e1800c40c007601038000007264034040c9a05907180000c0010007003c41d625800c1040d550243d01a000e4407c910071402c03a14085041000140b20780303403103441464100c082608041d82428844c1c0c02003481004500021000320351030070162026162500f00004075104980b408520b4207200e060100c1c1c4d64003070340e02004900c450001c0038000712032003030301d4910710b142d41c0d41150b0400380700450b944441402d0040200303509061641e04654024810300480d40083d01000300503090104200c10469254404441132103a00028020550065000c540901c505d50401c01c000e02604003a0282c04c041582c04240340e0a04070001300904001c04000e003086655518080b01d031518450105c0d0295a01d4a201d000001c1181c80061158404c01106030101c09030001a84114050000900002040c0c4 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 27727847 1250 27726597 27726607
    0x110103140c0d0506030f07210b01060906020f03091f1205010b040311040902011b03020a081303030e011d0607081902060906070c111318050106051206010b0405090408 73
    0x4180001803a000341c400a100c07988a03284002e800341520f600034401e600903003007601040d4020707030001880000c3c3c0783d441000c1c81c041380030800d8199290540800142411001c2c00c000119171307030070240345400d8501c0340d030035501d842400c10145503692013181e21417900109907058a030840c0c0854820301c03081400c1e515121403514954020442035a500b070700030104c0c0d0040044c0030400c01603109840c0b00c1121f0107980c148208a465000078080307502c54000ba500114852261808261013401201042c940c0004500e480307074420202c484032155240811404104d402c9001c8103e9070065002c01880c8404410f406100c0c1c140c4410300110781c01001048034421030034062110501010240482036455680c01403148d8500301568038500040541540c05010f5403101c41c1c004240b00d501207170001c175800e4410540c00c4e071214080c0d60041c8400301c50585004d1600c2200010400706402034800c84008946071030714030001c2c0a5940d1030fa1001e10481c00480c5040100300124100031103a290700c03e00416559082c0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 27729097 1250 27727847 27727871
    0xa060f050c010e030307020106120f0609030507060c0e12030c071403030d02030903070201030b0a060801060806121507020d02070506070f081c02090306010e010522060b0a20010c0c110103 82
    0x1da100c3c64244009a0070100c2089007942e0709124a034014055640e6083e11a50303c1e8448810040c6006006070102e603e41001034180b500484c202e60015604c10700402c00350203184c5000b05a010142405841051035070b00e02035400c2c000000ba200040c91480c003900d00e1501d40000c000c00a2400e4050a4042c0800d1040300b03080c0c4001d201551258a0480c084c56030b60419200050031101e8400701d6510a40c0007035400e1180c075a1143c6c10758192400750414072000d03102c0c04009014454009581c541d2886840750b0700c2c0c000850401d02034020842d80c1c0894040d03410410050344c64246038000d03a41c000f50309110341008145003079201c88019004010711480d0442e031314046c10710400f9818091010b5038000900e1307803131401c003000b82d00d00521404008141c10350400300040d00800260004d21a0303203503070108803480d501e160361056004001842450703507900300e1000b0240003055158060742041040070061403d800044c003c11032411056079035051000f00e287d85a00302070030702c04451410169542101404 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 27730347 1250 27729097 27729101
    0x1505070905060c01021903060806040b06040603020607030309020108070e180c040b0c06160302070c030803060f041b0905030601360203011805070c1e020d06050705030f010b07020a060f050c01 84
    0x10741e208203000036031b481c2c413041200341810340c5005444040500d414000c001741000421400c3e00540e004091031242d84903180004c0180141e908060350140000641804240d013580c401440f0603c01e89484180307540302902622141000010740e5009808140300c60385900c00300c0e1035141e1124090303026070b09083c1ca0b190300302080e4204c10417911460b8082c500740000c603084141988098489454250310340701c0b081d620b000a60340c1920009084402c040040f5295555000c085201240c01034810082540c2c52005001001904503015010030700340705022440303007008148241a0b840784030704402404c030240c0700f0500524014000c580c2100c4c40320f2412140b5001400158003c1c054075103c08165520442e0b960704661000d4004810712200350340b4080068800e50310500c0c00c88a603641964245158008107000100d103c5e8003c00d2140751030100049280c1005c007850003504119428103190380c0760b109285080c400c004000e940103e07049801c001c0c403803060712018000051490401c0c10062007005c001e007 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 27731597 1250 27730347 27730357
    0x41701020712080702070801020705070e07030902090c030a0e0105010302060304080f04090903080a0e030310050111070806040c030c06020304060507060f110706060303030f020403020112020706060506030108030d0605010507150507090506 104
    0x700003880c1e1800e003e031140c0d0400c00c880c050000e00b0009c5260084940c3c0d01d81c0ea0f05c804e446411598401480044c0ca0399000c0d50080c042c0ca030f0094205d0159140ca080b0400301e41c0d200f03c58000c030301072400254002a132014441d460580b54040c0c101c524540f01e07512003003290382200311800408075007040007040d5136480e4050526224489d8a0f00324141c2805801c4034195040301215221a900600070001010403a0b8030050444a00303003460351301004600d0091b400d10b4080d4114110f2841780340d050008001c00325184000312070081d281c1c0f03250305e40c0342c03541282c403885240304070800500c05008140c0400c2003580110802c0011150020361801810307807003211900710784c2090b2101d41d50313840b081061507014010100c0d0111000030441c94281564000703080c40c1005000c0c18047c0354081911030410901e03511036005010000c004580740c2d030392150303130030355940c06082e0800c0c0c154180f200c002619401401541d0784a580240c008a0f01c1c00c6650b0702100600e8000d1000040011400c00081c0031303161040140 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 27732847 1250 27731597 27731633
    0x30a020f180102010f05071d030f0708070306060515040b0309030904050103030302030702010b150a0c05070909050313050d02010e0609040603060e031305030c091b0904020a050409050a06030203030417010207 91
    0x503820001d00000a401c460061840d440c04504080c104862a90301211009130b4000e804000500c008455000c60324242d41005038030024419218085941d00c1c2c0001d0110443c2e1103040140a416110f0003848880300180c2e144800c3d03010180414480c01d014200503580c081c02d0032045904040c1c40500040980c0c80aa006601107a4000140820190f0a00400b80803600a80b2204e04034088000760898610613200d40070208580e440c94041040300c240702400040072200c2007807040c00c0150401d181c49a2003040011080d03800c0020000c0d560034102d9284a4654058542d014600303050424442030703610410034150700540d12030b00440040c1081c4680f002e00720b8400e0086890302c4610041d50040040703a0000da01c81c1c0c0c400d21000040c4d035210b2026940c00315040001110700905041da0f000203000b55140b032035000f80041044414507a00c180508216a03800c3c109112649500e823000d401c9503044c0c04081d4240e0401c00c4240501005481d02c10140071002000524000458031848001c0781003212030 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 27734097 1250 27732847 27732877
    0x1c0302031519060c020102031b06070206011d04020402070213060b19111009030207080a150501060c03020a060e0709060b0405010806030f03040302010c1e06060603050c130308030a020f 81
    0x40070749141e251910112048040d10321281c02e0585140d1809280e91510852040082c0c00c1c2c241001c6910a0083e542c01a100c0810300040100b480303046a03c030b88085035050014402c020001900f4103e02400312401c1c134903034000800f0f6444070f8080c40080d620081c403c0c3d030082c0c4c1e01c0915001e50403e500c900802032005502031511107030035000030500498100d02e800100b00040800203014840400ea50308952044440040c01d081d0505c2d00340c1c10010580d220100c940240410503080c000c01c092003005035004060200000c0c0e0304c0d03940544510380300403409401a0301030080400025020b500c50b0303040b0204101101c0c0c42d69076030386080c01510042e801c69417500b2004103041181d547c001c007890303803c000c0132130107082004001d089481da80c0c0038912000e4100f0034502c505100303200407004032500343c1e030b0400d404c2541e00501d81444030142c0b20341e2143d07500017031820001481c4601c0100c240c6102d00c1c02c0c1564450020f2554507810066040070b009516034650030005984032909880c002e002414180c0c0b91 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 27735347 1250 27734097 27734101
    0x50706021b0c0406050a03050309060d0b15030f0a0c02030a0c0501110d0b0301050108010204180c0c0f050f0f0d0906030e0102090301061205070501090317180405010f030c0902040b040b0a021c030203 87
    0x510050304c07040ea001074010b010801081c400208084181d0f001d02100b95801a1a803018014060190080e010044d4105103582c913003252751110743e4001c500c9060105003071345640d240d20070608100c4030100070103001a0018401d580d0001d00c1200c404c04250f02130360001c100d51802c3c0c8503060107548003d01d40c0d10000e0f902d03042c88042d41001c2c02042d005041030300c021424076252404004150101901c0200e0260351500c03c520500e0007040131425050300180204480e040526005940d13045035410b0340c1c4144200203460241c00c60018980c4548005030740c0d80319201c1d1400030309901074510603507605580e540038450020207440034810080249041404200e13408414100541061007a4003d24100200150280013180c0003d4a01c03664220700c5140300c2c0d6079006000e44148172103815540703c0e40581004000550310741c02d01c10b424140c9000384007228100c0d0740c3d0f504210403882a07200701e1054010900c0100a039943c1840501403d8416005440302130103c103c6405009661400c030320007099000c41 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 27736597 1250 27735347 27735349
    0x5190303020111041a0a020a05010c0c05010506040911010302072105120903040609060c020f09190b04051003030309020d06050712060b090102070504020d0207050f280b0106050706021b0c 82
    0x83c0c0b14440c10400d0750b2928190804001116030340e01d00800c100c0050700050b002c0505803007080007031420341d00000208940038a9000061030300072000c030700b960075609140c04201546400d110324036049501070780201b01444401c00540c041d41080e80240c598004100201d401402c1e84007030400a803061b5642c3e15076500c1101e07040c1c550107201030040740b1a41d00620052004d940c03c41014000d0b141141041907a14a0b03510004400741d005040d099007006504061107100c4041c6801d41e5402669000c00340903045403074050000b1140e00711960340030050002c0301080406d00a5000350900c1e03001411403000003146454803030039181c040c4c0c1c01c5c200058180c1141c0601c140c140c032511003e4134000b91800e00e440c0c44000001d6440e00a40180e5200d03a5002070364008200700c1d83c0c100e40c9a5980a01136415051041d00e000e0344841c180e01e00c5895103135520f500501454040051051a158821810801d0b42d081000c00c54482c0c004000c102da09903800c106041c80340d800d102c814800301807203000a002c1446000 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 27737847 1250 27736597 27736601
    0x1905070c030207180e01150609050103020901080103060b030307020d0b0601090b03060d1103030c0109060e1e07060c11060301030605070e0103050c0412060204120803040303050108030a0504030f030207051903030201 94
    0x501040811610005000001c0c1c0c0c041658400c0b1810590400e0303c503400701c10701000404005050b1030b040c1d8a8003803010901c006d82e070741c4001103500b00d03200c001c1059941c1005605a105081010f0300007440c0d00c00520010380035600007150042c1c0602140e090152982c04962446c1d070550701962418205002c0000c20745e130010704100541541c402040c110708252000ca00c0e80000c8640050130603100302c1c4a81c6042d00c003002505c08000e1484c00a00481300300b400d14600412810443c18114000c8801a54480210301e103910b0390010300100426416140820072140d02c0380101d81280c0010301c183c2c14420555580d07000c0c501039400346000142c1400c0a42b4060110301c2004015410b141c204802c00c90509003c105030303001c8501d541c1803e80400390610b0428024841d54100c803140d24040464003041c0306501001d948a80d201761020401030343c9440c00c09640f0b00641c81c0020009004000500c00640a034441e0202d0a10900444003050348440010b40a040850721140d0218060201081499424 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 27739097 1250 27737847 27737851
    0x120f050606010f0f08040201140a09030c0504110405060a140403060b090703050402030309010c021201020c1501080309030c0d02060903010905030c100b150703020a080a050301060f03050f070e1203031905 89
    0x2428078040d0646103da02800d034100c481100424403e404001406690040340c0822414404900c019543c0c5075441000d44400f4150000347e980c0308000d00046818140ba229001400f000c5208607410f092034201004010382c40101540c00f000904140c0c1c8202d070740742c040640040e520070750f00450048030500a0100e403030b000404070010582010300307110160307d01004481035044207203404d0701041818001310305000d1480703e580d0103541c4002050724046501194050029403440103400d81079aa804455980e03004902c0e803144e01d60400c44078490326150016044a21a2002d00054201100c08001908613105140f050321150000607000e41115070902000c0003c03401040c04200740031011000c02c90a64080992600c2000005156030130b03d402045a6400644c1c80000580c0c0c481ea0b001006003643c0003032244101244201d000f915455000e4024548945004401c0c01c1c0e40c3c0c2d0b2401e000715aa05540d035007581d000b90100c00e0400340e041d0140010b603c80c41080040f41d0440032001c292004680e00 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 27740347 1250 27739097 27739099
    0x71703040c0306020c0705130b190e0118090203030a0e09010504060e04060b010311070f0b070801080607180f030308041a090601030b0405160e07080912090613120f050606 75
    0x800800001400400080c01901c1c0c01000041e2951000134501e460940940c00541d80509003414400206001360000d1044400650b403410642e8001692040c00f20344502580c1c4641d840d4400600480500d8402d80440521010010138080c8041d000303e81141e1207001f008002406a60a0052904041c0f51740da0040c201620100031552801050b00c0c410000036000520080e1030b540310305041da1107600000449a20400d28a98031a00c0d8a0804806000a50700f00da0141d0a113001910050058503003178100c421010181900743e49601007110220175060840302100461040880d14006480444014510985949a19042c241030440e0841c034081d0a0900360003071501040320040020406504480e4030482918468441d40717025800d0101c404141217852040d01000035400344030b164038500a000035121000c5944914501c075451f07034041c14410f4010201000b2189890400034010003a452100b07090398405516090001d200c1499803200343c034003c081520309070900000344205600000 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 27741597 1250 27740347 27740393
    0x1202030c07210305090301020d060f090b04090b010306090213020a030c0905030d0c030c0305090904030906110606090c07030c0506090703020a06020f06010902030402031f0c09080c0306010b0c03040905040807 91
    0x800c5000c00d075030402ca01c0e48000c0402c100840c803a4103544003501a50f1001940000512003030b901c9410301c1200c01440d10601070f0490074415600300f10b003400e2280500f156082084a4526800c5444d501c02410100400303d820008183d02185400743c688007401c0300300341654010448802036000103113200159003016100e034026100c03256005802180c4681000e40c0750500003010005410300340c41178003401c243d030340d0800c01c40402c0104240e400346505082e1240c07a19003030049801c01c1e0401f5580c0808681003600074000d840802d008005500192481c1032082c03902c95004641d540d102401d1010070350700d41c02558020384080c000c6162100340f050284c403041c80100a0f01e241c420740582e407840e061050340b8850b580040440c06640f010b101140200e002041d01d404205070f514543c1d4014a00f01c3c07480340002d00400d0b00425410710215050f401c00c40000c00401c032a90030108507101e143e00010700d101c0d040c40101300c00107840e8142c3c00baaa126500801c4c030b044c1c581b082c9040c6241d05403051600003244e09 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 27742847 1250 27741597 27741629
    0x60f110c03040306051b0c010915050907060503090f07080a0b0c07080a05090109032a0b04050915010201061d091005011215020408010227040207020303030c0d091202030c07 76
    0xca000002e86089a4200c640402c980e143e03c068520301c4401e80c903440c141c40701c3c002160b80c0d010505400035419107202340c1c800420380409031003400031243c081d215104150092041004451301c00c00c003070340d0403115007415074010642603550913180440941c03068540c1d4010b10381030b03c144840205c003075501c4480c0710130321441c090980d81d66294a00c00e080c44a400e00102290300c2915920404100d4059540b0400168810f070340030412845544444040341908415401c0c041410081d04065800b29000501942045e071520b02c404c00d80192401d40240c115175030b9000000301b01c41c04c4500881c00d440c0c1c2846103085824401c1c1d08a00384008002c407406140d04140041020003051501c81c440a50804d0490742460054114030b800307072180754086040c3c1e41c0042034500540300015154000d07441e000041007a0122000144400c0e40140d44020354150803d20004c6d103004466001009510a40240000d0346c109681e130712010841da8080640050340080741d4400d06280070001940689010340c0380103015 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 27744097 1250 27742847 27742867
    0x130b090406051003020918010605010908150a02090402160b06090103030801060809010912020d020c15030403051308100504120903050309040e07170c101b020603040816060f11 77
    0x55202500052400341e44400103100d1800007145000915070042031607517181002c0780c0c8030020050118031a155540f0b000d10004030740d8015410b4000301c80d8014040d200000c01012005c10a0390020030030410140c080280600c16504d41c030080c523405072842c15408103804c2c6804e2803661580020515405181035000620200e5005180541120518a0598169038030070000724090560030500400c00a6002c41400c04a41c01003100030480000383d003180c081810120410088081c0851480c0700500308001050100e48580002c00c52280b00d0100204142d40c1c40402a00e07010600f4140680175070790b941403008216408030f600900d41904e2614000603821034940c1d9459104606c56184119580c00b880c2ca400002484400020100b160004402e440581c1c1c046407125082e500c12481102103a41000361140514003a0703500030a4800c204002281550038000f195102600c203440c5460300307102d0800347d01480250121428800c2d0b0012520584010008040c0ca1102400c1c824040c8140300018003 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 27745347 1250 27744097 27744109
    0x902030c030c030403110624151812060f040c08010515040c0c050715080c0a020a06110706020304060f0c14190306030b07030c020d2a030311040e06130b 67
    0xc21450880c02d0780d82d40341c51400f0780d4800c3c18096888040e0042c8010030941282903241903420074050102c0103c1c1d13040601c2001400104050300c0448201d06201103103079401070000c4141618405070030700c5080000c80c00c02d94609a4201c40010800b41080c0400c01000008001c020080c40e041c5c0c003e02c41418a50044805111403440360303401940d5841c003985d82c031841080c0708154a038105c0142c44d200c641380c40400781814981030281740820540c2d4040341d02040720408a03800b02c80a94064100d00314540d5441d40541007150309070040c42406d01242010550910003980141c0c419600000d59a440480c10410b0b00c04020111007406012419400c1598152048407460500640030b4103421907009419001040640c0001e41801c0920b82005801b036099440419032002c2502110200c1d14100b40c102d0310034103280841e000d444124070303c82517003260f20310035000d0052103414003140b16501040301541c01d030460382c4940d046035800da091002a00b8045040c0041252001c800c0c00592a02000303d28 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 27746597 1250 27745347 27745351
    0xc060405100c06020d0207050106031b03050d050a0512070302090f03011a01050904060305012405040603110603040311010516091505040302060304030903020303180102011a010207140a03080a080403090902030c03 93
    0x8144207400c2e540004021440d4100d429910b078004045494500310b0a01034020041808221384280c5250b4910042142c034040603801c49500000411120a40c007070100e43e2038020b03040c0f42d401e00000b4032140f82c16114a038021845020683d0300140c1310103006042204901003080c10a000345d01d0810780160b92100718400344100300d8282081c0e542e4101c280d005c00c0c010310a075030014002d9440c080110504a00c500c100701004207440d03554080e25a112010001214054807009200a440c0140c0210a0800802075030380306020342807954148a241d0f0400d030a48404480140b88006200d2892101c1030300104200d000c3e1480342858441d4103641e62004e4068031460002922420022002604043c85a003d05003d154042c00b079a803a0b01101e041481024040d0020340c2c050750811040702c689891412520442040583c018200603240c030507000615140089400d401440c141c501001040d8484010b10b4510031594424403c1c3c40c2505000b044404180c22035400d0034010020321203c4003403007058035 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 27747847 1250 27746597 27746629
    0xe0901060813021206040c0e090c01090509040302030c0604080301060908011107061e14010306320604091a090c0a060f050a050912010b0a060203070804090e070e040c0501020c060405 80
    0xc04030990b07600018018050342100d00c01d16200308400c0208001041c1c504c1000c841c2000104602c40e101d92102584860800980b41d0005041c91010481480d0903a11583c0042c001e00580e4030b44406040740b03e00b0180c04440039500c03644004010004964080513a03c0141242d100802071071803104030b8450b182c441d1500261000da1500e013003c0101a01c914080541020010104080040046940c40d907290921040e2a2079180800d80700c4a4102044507080054041086c20035800701032500002002c000761055400942d40c26201e400201c0f040241c000712126a1301a190600c3d10046040c41c0c2420b400c035242c001d45030100100081c60308503024034000d820b2401d1150b142c011892040390a0300882030034a50221034080841c1c902d51040d4000d0200050650340401c015440d1003081e6581c0c4903a4800520310380d0200704c2004480190382c0500e075120600025a0b140339600d18055100040c20b441c144c60340d011125080180f982c041098056550041d83c1d05405c0c6850f00000030326400046803a2 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 27749097 1250 27747847 27747871
    0x90102040e13170301080105010303020d110c0409060b0303070f0204061401120c020102160602090103050907060e040e010b040c051809010303053907030b060a0803030403050d0902031902010e09010608 88
    0xe03104000f00c14003200c80d0010914461500c0750703501e40070b141c0604428803054015011740d4142d152a24071840c00d18180c00c1c540c0004140c1d910881c0140401000c0f420f0054581564640328890b40342c1d0300b4001440f00c0e40c000c1e0210003001d07040d0700410044901550003614900707043c1c4180041a44c105500b00548034043c4c2c0c000681558500b0240c6c003a2003503100b44000c0c24000200d100410120b80c1c080d25260f4002e0b0380400c000d030385220314203030b880301d40d40656404100b1810f488910703444e10790001050b80b4000c1d000800ea81403c0c401140c240e6901c1106100403e50214200152800000c100c1c08010b00455200001d07500d5524060101d1180304074030420890a07080a500e0814030813a00c0c86509641d840c0c42107240c0021543e1910752459000c210ba010030020081905840e02180d80002e94800314083e51031a140c4d6a07058480d40c0c0712100c4110b455440d0520403001d0703a03040c0000b0703000c4860740701d0040d5046080d00c0010181c414541d070540c0710310307244801881090341c08150140d11a4849080c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 27750347 1250 27749097 27749131
    0x5130f020607080408010606050304050d0807020c040b0d0204020307080603062a1b070f06090806042102070b04092a0f08090703060911100203070302151504020d0c0206090102040e 79
    0x18044c0c4a1034010340ca556082040014516510000851241d4010411f1722480a06003030204d50b071140985043c0016484407929951620f070950244c0704190303004001c070b01c6404840d8042020780c2c10450b0b40c04048bc48aa0030858642414040294040c4c000c40c071082c1c070f0514400804284402c1007170080d54400c40030038030174000d01c40d6142840303c1c64410000c40d40000d90b1000d0307520039a481d90081c500010300703a40c00003c144030f00050346400380c0d52141203418044100c005407454038442d07098110851050760000181181c820700140081c1c42000004100001e0001a08481e0640b004200302040c0301503008480c8540e00c0103007400050601e14082d51551a000e81d417900d081c115800c054001494060640c04000b03c00c1081c0908000545860407084c82e05041a6200c0c00340e0315001c1c0c05078104854100a0400308050b43d036001d211001c000c00419560004a0121b0b040441280000d682c0c8034262526a07404109056000c00c01c480258681341c1807030804804102d004d0034401743c0c0250941 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 27751597 1250 27750347 27750353
    0x1204170403080304050f010608010b06031617010609050102150402010c1403091801050405010e010602070b03061504030308063309120a030903030813080306090603010f150905130f020607 82
    0x32200110340050100352a0304243c02c200741c55a4803000e0300049503107070002c0000c00c0e20043c01080143d000c0100450300b10b50311040c400d01c00c006020103900401c00c1740306200c11100b5284007000c2c06020584c1e941c90141d03082c1302c006860300792400e0a04548244007010400143e84c46440415060703801000480e800500480072407840c001e11081035849002c2035072007001c5a02d81741081e4101c0e84100d50601450741d032440c5084400100b805050010381007080e0030301c032404a44000b1908000003801c1e540b01c035429159200019005908101c001540704404d00c4501d02d080c801003580da403040d02c48420f0122540f86c520842c000704651b00c41705445e02246408007560390003030341c1a001800d07000340c800714402490014900c0c1c03100c1c0000c40229406001203400041c14070500c81640b507000310000d10390340318002003210110000388081d80c15900c803158042d403086c140c01050f08800481d09401e2074a07040c203030b40c141034510040408484030329108180307011404a58000701401e0f015139116030385d078240741 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 27752847 1250 27751597 27751643
    0x2060d0f020d091707030e0603041a0f071805060412031205040b06010f0305040218090a020a090b0f0d050a0201030209120304060f08070302070b0103020f01120f020d0608031204 78
    0x1000414414804203040401d0342454200504441c410304244c4800c11502840c290307580144d28000d80014407070030084620b81810b50066402c00c1c000c004803407180203100d1004412090480e03650028604c42c100380414640c11006d0f15403840c8442045403071a5040c20b002c5140c0340280e208105c11421840ba4034024140100366001420040d50307020f12052401c0d040c44461120160340d41400604c1032203014110303030300c2072041601070fa0740140300200140010f99007401034000900011114040d9413444030060b521141000010329404070041546510b46003040102400f04200a0191252200b00d10001c3c4002c5800c8041650900740182c450680c0c6010031030302041c02c00c4082071341c8000035003c82c4071a0810310740d041900e11a03656101659481c401103059000d402c80092010079024010310051401000509090382c1c185801d5031110704000d03c10041d22143c40614920b640e00243c628040c0d80346000344409060031500441c90700b0302c840e0f403200307400c00b006102501140d220030000b10fa450703410b = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 27754097 1250 27752847 27752861
    0xd06080d0e04151a090f1005030412200a03110708060103060e03070f03080907090209180601032301050901080111030a020306010c020406060201050604050f09030706023a060602120702060d 83
    0x681ca0004c4042d00203155105030b42007440380c042c009001e2100e180c01ba5a4004001c0709944031415a25160b80d2698168144c8542c0000d0003040d500c01e528140c0038075072040045420340c0040240140360b08000c0e1421640100c0340302c0a0b00320010602902400140090440b50b100c030000075000ca1041c0068218050b00500a11406214684805055012007054040c40160040c0e4182503680d01c4a03004a1090140382074118901e02cbc55462000540180c10758001410306010401d8112441c03039a0325007100c4030741f000018000310b0061145040c420390f22400362148030700800c1200c0b403014110603980401003040052540000018441764429074420141a5007d001840300c1c68480307001038040e21040351164000e92924001404141034224440c2c040e141c103101452824600781c803043c000c0c0d0f015904c0c000c0c04110700c46503d512503a0702c14226a020042e0148001c0200003032910500755a0b0540c400d0046512580c001443c10742d205040b00c0280d0350450f8034541d65a000e041200140c030207 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 27755347 1250 27754097 27754109
    0xd020307050619020606030a150507030f0509071d07020304030f1407032003011506140c03280503071b051f05010f05010219020f030312010801020d06080d0e0415 71
    0xc0402c03446900e000d0000601c00030000f64007a280c0d1a40c4d40003d0642d1540410005402038480d20781912120340160303c400e0700300b840f618000c00c003d00c040c1d03090030a40700107450505c01684104000c000e03000c04000c060701c107603983c405240b4150600190080d681e01480c0005000000c0b0750040408000c28403184080000310760013a03400e103a40d00d0402d84030801c1c2c0300c140c000c1d401951045101e4075140600c0707040d21142c2002e210701c2c0300c9814480119440e5050540100c0c03051010003010080749805c01c040c0c81050f61688071005000035401c40041e504c40248001410b01070b0070300502100f541c00c442c4080003070b8894246900c075450142001e40c40c05092083c42641c4400c1d440d85d039011043c0e80e03042107040e900c81942d9a0001d5944000490342c84045030340c1411f0103d150385583d00189881041f202e031985005003100c1c282040742005954000089c0c3c02000c55030b60000c1e505032100b07158090540206000800b40c29040c41c50000900752030f4109440300c3c42540c5c0c50f882c0160100740c030140e481c05000 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 27756597 1250 27755347 27755359
    0x30d0c17060909192d0201080117070518040302070b03100b03041a0f041209030507090e0106051c030e0a0b090919060308031009061a28120e010612020d02030705 71
    0x20950401d400031003080c02c000380005c1c0c030b80b1004d0403130302c200050b800540a60680d03500c446a031800c0720055038070740148196003c6020744500040c880da10000d115200e4a400d50304038146007002e00e4083d140010719030006840c80c00a20820400110000705001110242e00d2055501d503101e1414005a4218420480c001032b040c07024071803808d2410703090511452154074100c0384210302000030340301c4042c0351000501580c41400180300c00708940e040103401d1101c0740e002007022030310b650018000d034075005072100d8080304030a903072010716030b101c00024888030043d0b179040011400d20040d02414070909480c24065210300b400300300204903030b400d080d0084150701c504007c000e0700da00d0061020341c0180c81d80b0814400c46000480d900380288a001d085604820400c03108002314052440103030016049400c110051400304154184000b0782110400c0e05640c0c0c00413015400303032240040700c40b01e51070303401e280e0b00d048014400400e4080180d0007103601110000e405803a82c0c07000924000e4550849038000d0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 27757847 1250 27756597 27756643
    0xc0302071403031303080714012f130305030d0c180b0a0c1205090102060c041d0c1c0504031e080a0b031c020625080613021b030d0c17060909 62
    0x4031ba9080903010003403003007000381d1000ba801e002031800d171088400c000350703c0300280f0340b1010f0380312220701200214859100c1c2c1900708181c4445500a0f11001d50090f6010b410000f0b00c8a00701d6034500c10142d090040d401e00c400d44401c0d000c000f60441c1054012441c2e0075200145800710349004101d103960a40d0300c11051407101500c070300000c0c0325400064806000d8481c00700411844c0e6002003d40b01a95002000f1252382000c1941d9080c0e42000a041030820b0442000b0480c3d00941e183c12010320301c411304101081c1814549030080c036884901200341286540d6420054040e5130103440c60760010303040700c00400c100d02501c00282c02c000350014070707640c620501d040d542406500403842ca4442c802c4040703221840a450710141056030080508540041c0342031380041c8092500c038402060003850030720018200000503900d0aa690404152100301e03074008105c40d20318003158000c07605450700e41d00e00100520a960607500c05020042c007010b01c1050181c0009201c8001081880c00000c014582c01c1140 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 27759097 1250 27757847 27757853
    0xa270e01020d1e060501090b070201260703050103022e050a02010609020309070302090c1e07060e06040f05010606051606090201050705190c05010302190305100b070308010905070c0302071403031303 87
    0xc03440103400340e556403c4c00b42c000380560003192500c0c00c554461642600d00680c60b401140ca00d0395000c4058803c00003044d0900200110101852251080d80c0300050554154010086080074441c4100845031044c0030310300d80079907401410b40e01c80718142401c949903291024143d0240005400c038841c41171011080100c030341c2002070f003001240d00a44000c00340740c6030807018000d6445140c0c404481401d070340701c28045219548008200351401100001480d28940103034500340304041d01c05980d03280d020001030050000030301c68540104150b0a040d8070b00f503040e890983c03c042005030082c000c03c0da18900e101c1907901840454005a074003030140c0e150701c0600741d5503903403a14881d41c080c0d564240c2040045001d500900c2182e51205902c14159042260005c049015000041c4440d079003900c0702c3c0c0c00181101c6031401411071184292100952036041070001003c44000520100030007000c0b40f4180d01003a004502030058400c401885043c40d80781c0c0022a21307610440c030030750080076072504c000014 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 27760347 1250 27759097 27759131
    0x1021009080d1e0b190308030a09020a0b0903060c031005090402041104080a120203090d060b12010c050a0e03010501050906010c0303060e130312141609180203060a270e01020d 77
    0x1400d08003c2c04204032503040040c001c0d00201000f5140243e0038a1a080c4041410107001e194080311620340882d01131100d40c04182ca070029907100484040300030850f00074170f00c1c05121044d4000d02440d841b0742585890b03d0002c0d4000d00e00e1040740d00502c82c0c5004070b401d40d11103820803070004400f440d003295516030f542c140556441400d001035544902448904002d94404401c488608000034500300c814031241d1140401040034400c0164490f050010101c2d0030b2030700f805401c040005030744500b42c8900070790b00e02628055100103400d1280c1d16200050201c0c9e500d21542c160410400c1c81c29412140e000c0c13409a0080843c1e402084085d02244100301001013480100090345201c3e80c0d6081c07405001c1040c803c1642c3e0003440c407070729a0b465400025003204000540b03d690480603c0c004456079a80c04056007075241004182d0650f540020412601c1e00b4090341e00c8000303008040460359809100455899a0b81002200c81107158440398403c03d060f0007501170321200800503104104d180320601c05802 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 27761597 1250 27760347 27760391
    0x20901050c1608120408060114030312010303030522080a03020a02100e03040501110607090603020c10050103140c0102060403081302150c0601030506070f0e04020c01140109050103030207120201021009080d 90
    0x40c3c03501ca103400c4101c13518802d0013074070b00310307050000100300710390801403204180800048025058441401030302d0b010216071505900941c0207403000070310360401c1524a028940710811440d44c071a800c0b541e030400181d4807800c440c9141001d150068039501040703030032400e00200900728000d440c02d02140c45081c040210003030044450982f100e82e4041c10034019585c0b142d90485446001c0307508000c00304042c0380250010b01000d4248000d0761030701c14004c2408001c0318402c0c3c00580c3c41c0200f2000c0c110010200300701e511341d405002d0004201610703042c1d0f002030181000500c03203803143d80150030100c215258602e200c840c0d2038803081c0b1291a0341121020030342c0c403682440142c802d4811400481c00003406001d100c6180e120a50300d00f060034143c42c0070b0001962000032071a0340742d9039645d0080f440c1601c0401060107013180d8200401c541d459414028680364031034000c660201003400781c400050384c00050011800c0c040d41c00c0411700d070503a802c01000324011410b2a6011790700b01080c1480c4803007000c607224 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 27762847 1250 27761597 27761609
    0x501020d05060109061d01031d100f0920030c060705010203040615050d0602130801020301030507030302010b09060a090b03120310030c0b0906030403050f0c03040608071b15020901050c16 82
    0x1a40e41c4180046a18440511410010070300b42081080c1da8819031440e546041b9041c18049142d00840024040d0648511404521a045845002d52000c13950140b8a030943c6150400d0200196684610304141302d01c03080d0328803442e207580300341c807080d00d040c001e080050500a28003611264a414264083c1d031080350200d8005141181d0b0001d45103280304408103940014008007038801c1036946450003503000b40c59010b181e041c8900009050402400110301030b6105030040c0614918525029080d01e4044480511501044040006a0311a54155402c41d0210800824402501c001207800d02d5039142864540d10380010801410709800d01c1c4141c110384c0700318089094169500500c49080c01110308565000104001040200b48a01c0c00f078982080d0768408070b03241c4295a12400c0c80c0d903000303038890004600148208264950419403c1d050300c0f9009030050050141079440c0344c0c1c69988050b4501040754007045007206a440b82065030305e003000000850b25015442e02d8141107000462140d6 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 27764097 1250 27762847 27762851
    0x3040201080907060e0118050301090305040f060504050303030412030906050f180303010e070f11060108060703050a02090f060a12020f040510210c05070206280201060602030708160b01030501020d 86
    0x3080c0b14100014603072088840341d07644d0340845a08070004517420303540414030301d1a044980001282d959000e104010046100781c81e02d680d91480c02d4034103840807019a008ad42800b105101c10445610048100d030f03131141c0c3c00150408150400282a40145500f8002070a0645444200901c1c2007600c50018003e02d2080c1c052030349100706444040d034a02c000d02401041d04e03a244045205103005001011030402d6034100350b103111442d030304000d01e010001d0340300c503031103a100c0020710604942500ca8603802400e034900642c5820300c41c5020568028070320140b1401084000340d8071000c640300e460326001d031008046046d0b66601d0714803002e801a41140c000e00c3c2c4a8460080c0c1c407a2294090840c2a00318440c14110000f844500f16015009080c00d910342014804108152070041c1c0d64034008248101000d4212140b0355245000880c030907050b00a003c065a02d400e03000e02c5856000400d80f00480d504c1a80d2558503410055004d1001410b4071004014268000012081103019005041c01030148142 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 27765347 1250 27764097 27764101
    0x9030b071805060c120304080f0309010b1c0b040f0501020903010204030f02030601050303070308040b0415020a0c0b010611030426010e07030303230105130b120d080c0711060c120d020304020108 85
    0x70040f4600c2824884215640301c8040e100040c0c4807075014640c014019850642424040c05204540754811904078849035560385c82c1190503d000811a0085044141500d100d413010f542c85007001d80001d080034020101684408040240c250100d40c11403c01038029510340380d503031138219009048448101e02ca4002c0c0c20003c1081c1c2800015241801c0c1c040c1c3d80e001706515151a590381000340500242c4002c1c0c41d002c865066817201d80003d00e808601aa2484d15200310740c113007203100c00d0041c1c000004116210090700c1c4021000410b54041d5001030088ad010b20400c01503100d5020032480c03101c3c81650801e40310080020f8040344010459000351401c0c80048000e42d003814245070319401040d45900c50788014003ca04001b030440c0c0540078001c0300002e2070310700d4100060500002040580095010b000e0001e401c40d40503401b550018002c0c00114100010340d551628504603410710240113641c0452026607450042200b400e007880c203558810750700c42e0580c00000182d441182c00764041010200 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 27766597 1250 27765347 27765349
    0x7030506090606100c080904060f15080108030a18050a090507090603020901090303110c0d08090a090213030b07090e0405100509150f18030c0105061804030206150109030b071805 78
    0x3030441e00c2100c00a1600b244080921307815140c0310001030341076490301c0e428040004603854610915014002c0c81e90300c8000d00b07180c0b1001c1e40b82c00c54038022040410850308010040c80702c0003c15107005c2081400c0c0b03c402c41001c20400d40418540d64880ea41c49000800000b8000d007481e4403c83c0560150360313403e24103e031209015000d038810860030754005a1101010400f2074481c10740007141001c004140e80394404003d000500d41d6600c01d8061780c10450005540043e40f030041e132060024a5152019410000c841d030342c880c03c1c41028030000e84a000030400041d41c4c0f91003014114040c104d40c10084682c4d003000d040843ea580000c1c60701e030f4004e03450040400c4403030f0310002d9030785010208140a0901542d03244400f40703603468054840c5d0aa0350141c0c80c0310311440c0c02071001d001004240300001175603250480801c000d2081040c0c01200402c461420300c03011a07808104280d05c940f100003001412541400100c07081c046550018040100840030700c1030440e400308400c00706400608000c0364480c0c4480c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 27767847 1250 27766597 27766603
    0xc0c0109080d0305180607020c0a080109020603011703070503070807110619030b0a05031509060703050f0c0901020c060403030309050d091409040c0306020403051e010c14030a06030507080703050609 87
    0x300445610350b221840e100d182d584641c210a0703206000e020f40b01285652000d180d8600941543c0010160f00a0710b4043c0260421140402c01000310b600240503a0105d5004191039101c103000d0001a064203d40c00c0300545810001c80384c125500c54102c0b96103040504202c640398100b40b0040740c1c4002110303443c50240c9006d400703541c01075510391458a10340364160f506500600e240340289800075a00c4000243d150f40a0080c6481c00410f45901d60003480c05002940c03c09400614640034940340c042403002203c1341c02602c940c0000c103915150341c1c130b04036800140d2804a181008641c044000180403080682c0b64101500041c480d82c100d8204401510082d80c0c141c5550088061502e140010350b0007515005041b607030094021081d901c0310a4803502c1d80002e981c010381040d501036001044800034920100140080d81d84090000c00c4880e01006000300011540c040103030002d000071005c20311480d80da40c4840c2c020366128088071020742e0317942086901d4401510054901d40541d00001d5403451000c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 27769097 1250 27767847 27767849
    0x2606040308060f0a0b03070302070302070504110a0f0302090402031e1503100c050906120108121e0703030b030109030f1701150c03050c0106080307230d050306030a060504080c0c0109 80
    0xd81c994041d5036850b40140202002c0301d0003401d03400070030440b00081c0c1000b0100114017500e00d41d640540d58914a0070042e250500035402240101e10f0501c3d1403002c200360300240c40c14600e03d450b0083c4100399003803048029000e01e5a250798014400814001e4900c42a01d2900c07017030780204850607840e5618110036270585044202c081c1c05401111000500240e683e009400d00041810114149064a00482e4598001d44c0c1490054641480103001c0140200720901208130340c1c01201345000c0400c081340202e600c0303144107003c1c0204003042250805003e90000c0c602103101074020440034515040041c03111600407824400310300c02005001000480c094228143e68548009040380143c001003240d188210000680070842e0a00603d00e40c00d2080c0101002041d4500041d41c483e001030800e002c44241c510301c000b5840c43c6090b0000c072200c001241c190361607842070a10075280ea8620000ca0b05049000c1030044c030407858041000100f02400c00a00310400300681200c018864141c0159045461 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 27770347 1250 27769097 27769103
    0xb07020a051c0614010501140f0a030507091806090609060b0403080702061b0601030b0c04081c050c01090326060d060e03090406120302010c03200708040b04260604 72
    0x1003600512640c14800241c0c9428034030004254080c0b01291102c0045441c1011401d0410000a0042003170307692056404040000382c21307884d85085558101e004091081c807403400b0906031288001403040d07000e491200c0c01000c00032030000403045401c100f900240101e01405604500e00030020809503064440d0500b5174883e001c45a107042d0a41c1c507000169003000508076032105c000c0044c01520010b406c00d8406183c00c580060145504500e496050903c00602811007000141b0040091100005042035400701506402180000c2144111814407910500c0f10003903081107035500416502c4881400b0703103804071001441d90061015650749859095601a501c50300c1e101e0007102244c1281c2c410411844080100e1b0714104201c0040b4050f54a0340d4851010a010b1a004ea4103040d020f0080d961440e8041c5400c0180700c12903003040b00100d407101e03660702c0744c660049081801c0114050440d0050412412143e45a96440001d400b80c00c41403038a08408260307052014480d240006601e50155134 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 27771597 1250 27770347 27770359
    0xb0906060102281a01090605060f040603050907031b0f08010b030d050d06050915100801060f0c020a031a011701020405030d05030901180b07031508030909250f03060b0702 75
    0x4800c0c0c5850720403035400d44090f00c1d01201a40340c80064191003010004541c02c003c0c050301585041045021106103612460003481d04100030008035210740100d5040d47c00500300052070b0748070070b0780107450035489410042450040d10400484108801510360441e0301070114200000e44030000070f0b007039841004240750140d103c4000c0c41ca050303008401030424148085000515030382d90710700141142e00f060b1280203504148100340da0903401c0250180301c1350041d50400100d5945000401402d0342c104c00d5040e000c00c882090306804540e0340b81c011000941e00035100c83d981802c4030b980902403007400e10a940c511078590181c03050340780044c001c0e6002c8031002400f420f02030b910001e050f9004c0d03000405140040d581c1d03400758600e6808200ca210340050140302944c80300e1400754009021202648036074444408092402c000c00a0000111002d280045c2e41030031054840c1294002083e08402048020421140502c02000d0340040c140000e10a01d035000c0c0310590307070754660480a214030480650080 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 27772847 1250 27771597 27771613
    0x10e2404030302160f0c050103061d010b090f0904060b03060105030a17030402040b1002010903260c09040e0a110306011a0702012a030302090f0102070b070303092105070b0906060102 80
    0x303000343d0107011072900003540402d55a11305e582c0e10764030f09145401100c14012030345052120b0750340362144074007400c1e013440454800201e0000031803034154140318400103400c00041c04001c2d5154400784100100c070183c0f000d20981003915000015000c0c800742140a88920b100004062400144210041e134001400c41031054060020806580c0010816a0013645991076550340b174407030750545000b01c0466400082d00001c1458003c00208003a000821008070003402031418841941e03406800420040046a664a018001c02e0140c070515200b10701c28019444c592050104460444112a10440594203140c1c0c0354440c4522440000c01c40200c000c4081c88900010350081021044d403221003084070600f048545010580495660f40c00c600280c0c01044174401c03414072601c5019104c030300340044d00005003010720303e41c200d000d002d401508050701c50071008148441e924241868110f05156444808403021020746641d1002e1b00c00c44504514038002040d00780082003050003010164080d0002d8 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 27774097 1250 27772847 27772853
    0x21612120212041401170421050f0901081306020304050703030210051e060a031b0f09050f0c0f07050114070f0e091314010f06051309082b0e010e2404 66
    0x1307882c0c41500c1070505c107140000d0f2088040f01400c40744107030b201e00c40100103c0b50008008911514841084051020500c400c501147e402c100b1303504031502c2844d00d008903580f134079144111400301050151016100101b844240807002c100c60003561700a4003210b502d80543c407800b00c1241d400b150182408200d0110400d615201141080d4101c28010304e04a02140c49840d01c1001600c400f09180820301001d00c00c00c135080b008050358004000c541000c202c580b602c040c926030480740c0208004011200001c040d4042c0c1201d60680b0180c1e81c11000810040c484e00c070380ea9003440ca00341c0b0706801142007000f0007500f480c07294401031a021006041c0441c1c41e2a429208004044210300840314854034508000000801340b044085a00c402c0002140d01454907051001e054411880c94281c107042585500106240c0c0d0200d844100b040c1c113203030958044244d180d5201a400d0386211424609210a18112640541020000d06208010784030a0b60009035000c0010e06000280000e81044100203004 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 27775347 1250 27774097 27774119
    0x10801121203020304032c010f020609030d020f071e1401020c070e06030132090d02071401030e061302040c050406120504050a0b0103050d02010501060504030f110102161212021204 79
    0x4148171f42007503442c1c241d811418019000448400104c02071030518101e0f0315682c404403402c20020036002130991030805524064403845071220243c111500040c95850050500c022104807a0b000a402010b45030644d034203001c00803919500b91101800c420070081501d9061080310010103007140100b01c00d51811040400301d1500514169055582e000c02403041030021070008880b00084294841c00c1c030141c2c0808000f00c42c044c001d22800e6200040c2c8050450b000502c034004d90b0050385203c200042d601c00100c001c2c0c811415481d10350f000708010301498401380300c9c031128407904c00c0f60305010005280508943c9030042e80306400002e4060400181d10070003075444140c000d8049c506071001e0b13100301e03201c00000040a074000c40d032030b0b40007a48280c1d01b00d43c207115217805001075103003051500303113152954100e9150711280580040400c0002200070713070017040603e02e80190800d2201d0340980d03801e801c403900c107032588050b00c101501d81c007c00585d520114a290322030030141c48650801e0700308650410 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 27776597 1250 27775347 27775351
    0x13090e030a0e04022505010c020304060207170a121d030118030c02030a020402030106080702060106080105060405040213090e07080105010e071707020102070f06021b0703120f0306030804060203090108011212030203 94
    0xe00a41d0030081000380310035404154150704021912800c6400c40752406e182181d000c0250041190000c0c44284001540498240c00f142e041722500070100c08262030903030070000320900c010001074402c00e41d4002250000d0042e0300b940840000042a400d146081c54242c130002c51340200741007600d40721540041c0c043c1c22207601e42800501115200241640410300b20b07030080e00030324042070b0b00c03400308007055a040014a01410003440d21100d694500030105650740a40d010b101c2c416900492038000d2030b070440010300c00502d00040240aa11910030900d5207640a034040c3d40610350800001181c00408590124080c03645681c034001e209807030800d100c1402070054440811950200b1064000c40d603580c46034880c160284e0030050346c030000000440507107540b8010540c6290402078003040410388010440c60700094600784002d9480b48080d08a008203100e800080002101080c003040055000014003624403084c2c0341c4504590300d40300310701d02d004a0032900515403104107400c1c8d100a40302c0e4000d55 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 27777847 1250 27776597 27776599
    0xd0807050f1b15060a08150f04020103021e03010501021506030601050103090f050610090f0c1707020c03030301030b010f29130902030f10060311070f030903021002010213090e030a0e 80
    0x205042c001c1401c1d0505040d41150a00078150f072860a004261610400b400300605134007006000015080039080300e659001880307034a601044074001425640aa011031305140480035500074000f07800409018590028010f07180181b240c803400d801e0080c0714405040c0101e2008004090683c03a00f030044010b80360324401111000c0114404000180c0c0400015000c1d4140400e415141c50811107294104c2e80000030111002e400e140210301d00d00c1d003040040100041c0c0144601e0a40e4540f2801d03854806c1c442105601480f0000c000018402845922030503110900b03204a0001e65460902c000c411125110010110f010480002c031601140010b20032849102e6001c3c2885541d000c11008a810841e00014000c020504015020820003040001b50020781020444003540d6043c41030b4a0280c03540083c00050140308200078107000302c40c000021a802803101000001c0684004c0c041e400c09546051200313050036001c501000c1501503402c80340d511000031400c280e04150212001c6100500d03403 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 27779097 1250 27777847 27777877
    0x61d010c080d1b020109051002042d0f06030b030606010f02030f03091504031e03020a090b0903071502030a0e01090501051207140408030405030705040e030406050a02010b0409030806030d0807050f 86
    0x6841840301640f140000500250000201c1c1d20b200d0800c141014035090a490030148108030511801e001c540a01c460382c07a83d55140400420041e590340742000307081d0030010b801e48551800050556040e0001e10320340d00b0590548540b13469000041d83c50500044140b40541c10a219001c42040803401a59200203401c04071090102d0740003030f2460b4204281c0e03003907000504080b448a0040305500d0001e80883c00b514045103403000660000302855050f006082d40803000040c06031003654208010009044c900f422540300038120340002e03680e588a44801d402185400512907070740e40c081e080002c11104103840355840d25a01c240340d0261104028900e406111220f20076011501c20f50b0050005089000000c50b03a41b401e110415140000b5580300714880c070708008034142403200110903a01180c0c91070600d640c41c0ea03042030b8181d001d00807042003160402c3c60543c05030281035020001030b00540c0180d040e641408865002211003400440d800000706c3c40402c42c504554000100415a0950070141 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 27780347 1250 27779097 27779111
    0x809030d0903050706200306010e040f020f0c0d02030405030d080402041404050708010b04180303090f08030a06030b130f020909030f0711090c070c0501030c0e0301021201061d010c080d 81
    0x31001254844041940003032008250a0300f005034510600068510f41100c508000f6507002d031501c0d40b032000030040ea0422401c84202902a15030b1b4004200c03119668005545480d09050540300c40d822040b25080c0520981d1061610980044220b03001c3c2d9002801803c8008030b004d8098940110150017240c01581d5261608142e80103417400038000c520440103002c6c0b07145030014950941d000c510205104031314241900c207003000b61001d16842240e00d410302107104101400d04034450200310034090001031000040000c851042c1c1e01c01019248540104547e980702c01031110880142d80030002c102210121001000d45048281d056209070182c00f120b00e8030f028411034000790b800c41c0c042100d04008003013010106140401c0e1041c6c0c028010b090850800b1a070b601d9080d040b80a9108450526a54002c014011841a0b004102000c0040c009540c0c0d03624064821003100800d1094100003544014124a01e404060202600b804140c2d44d840d40c94541e0707200c0ca01590320002c220404107070340b0a0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 27781597 1250 27780347 27780367
    0x120304031704020d0203030c0d020706090e061002010605030304060329060d09080d18021507020a09020c012d0605060309120f070203010509070608010f030b0a0902030f010501180609021306080903 86
    0x8010480650701c4400b070f00409d24502d60107441c21003542c000d4020321507106024040c2d994680324440d4054801c4481b841c000718566001c2e4010046c0e5004143c243c04002001f244203a0150003c40c942d04c14941703000c00046400c4081c6550100c5142c446501c01002c000403103081c003940d00104001d40c051802c00b8502142c0482400846451114030b42c1c0700450410311105500d054503030340d650321820142c00d0b403820410307a0000b19604824000c14a41640c0840c00c81c1010100b584020300282c000c02c0c50300114508803608805883d01f42e0301400080d030818002044d1030920f241070701d008000110050101c0280e10300c2e04256030f003240c060480c9144061100030b001d80d409016007401100100050320b5507e061080040800c01c0c143c100d01502202882e0401c0019042c001d415448125041d00180c0400c0398800a814003a2000e01c190003036007004004a514140c140958040c3c101840f810000170b669040441c00364000e070418481074a1210604001250052814684c4907100348180c9242c58107002c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 27782847 1250 27781597 27781603
    0x20f0319050a140417010b0405040206070201080a09020a06120c03060602030d0c0203070f080406021c0207090525030e0c010306050a0504050601090909050318010e03060601270b0903120304031704020d0203 90
    0x181c000d080780c0121501e590240d11080c814500400801d82e000e1209c0c2c81c10307070003050325407041c80c5009042283c40300c00034820320400c1c0d100310344c111390040440040030faa8140c0104140f001030031618001c1d2920b040c1991060007849890201e07440c503005141030895140c440c1008007170400b201815400b040281500003640d50507011442d61144035069201c0d418020300070318100d40c00c144012002503d5015070079260700041e80008030740340200c0100d03040d9601e02070707050019504420018100119906d1904040e0150003c01c4400640000c0303d0003d00c030304004406640252040a4000c03030146418411411f0681005900a00605002900946e6207210b041103607035405050341e103608041340b90000036003258803030091010b003460000545d0345001c0000e91188070140125042c40410b1812040f800551005845010202d0b40140310155a07003020111990190209902c03034010440f00004440360101a80e0046030181d8400d24904180f610020181d20b0241081c0d0703108911448400040e5410 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 27784097 1250 27782847 27782849
    0x1090606060c0c0302060a0905031911090705090405150301020304030c0618021e0f030a030f030c08010b0a1101180b01031a09060f07030212070e01090f0501021902040609050106090303020f0319050a1404 89
    0x500a9003000710001d0506d183d00d031941330060391042c1804c6003404002540601583c00e03007030046800041c0760300e07048041c00d48031512003c06c503019400482000141a080328404008500510050013200e886d08031421a410703c001000f544158400001140b000c40b01d00d04c035070720758400360002c01e0101940c07002919007024040103c00148046060386180c5034036004215042c0c8960901e50031650400000290a002c6c20400c6007c0000d4051070066000094220f2070381c1c01010b414164400105041c21f100d800c109000030386420a49000d40743d401d4400402c031600c00c41e9401c019006d1500d0f00010031112681c00707095402059001c0c030210b221078a03149550b81c0101040e844000b1a02e00d550009401202243d011412a5010003010000c698000c00e206038111203401101400c0e00c010f1000800601458110002044c9098000b040f40768104102006680c0641c08948423a100910003c2e40d84c13082208401120284070500c0f80c070b00c0d0140b800751403e443c1070300b000115450043d01092254000b = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 27785347 1250 27784097 27784123
    0x70803010906060305040f0305090d02040f0b041404020d02120f03041410020d021f1b0504031406090c010807110609030a030b0a0305030306060309030d090501090606060c0c0302060a090503 83
    0x1001004211607052032040c1d0340240a5410244568985604d89541381207008030080c00b0b100d80040c01e00328940e155104240800d50061040102001c50030442d00203041480e0250300403850010009410711900e0a86442507500500314000c1d0b03c0035500b400f02100c103909848507203209600b140c40314440140f000c0c10103041c2c000c4800c6c460f600e0358400c101c01d541c105032064055410852001d8885680272074003e071800c071000f030041e4581804034080001452000304001250081900000d5109c0d8010000c0007140d00038410380186610b084143e035210a01510f03801d9665114088035941c55001c1c012565011041d401c146021001007075540781400012244110070350000200d500c011501032050b00000c55060380e0340b51005007141c0e2029500d2002034985886028084009401240200111540c0c0800340b1130034000005280350440c06004a84000c43e0024100b5001143c080d1007031a40ca4100d43d08900c000042600e541c09021207680311b01030786020410544400f0441c7c1d1030410800e4120b0f02 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 27786597 1250 27785347 27785363
    0x90f081c09030228030f051c0f050403090b1903050a020f0a090501200303060927071d060102030d0504022407050601060203040b0f0903070306091a1006020d0e04060b07 74
    0x121302c558244450180020605041c501e00500100381e001c5e8420706541405d050003035582c4080a030096188269180352066541000c1401c60307078210700d404c4140582c0c401c0d11465200398440c5444146030282c02c1c0d0003908000380803120440d00b8405d4100729046488540700500d0000d01d81030855190703210201004c04510740742010070440d43d20a4040c08228000e82c00250000c40c0c0c0303000b10b0b45034440a0042c0d882402441c0c04102c0c0c036051082140242c01301d04003405100414081901e0f2112414860300140340c264146c540e00c0c1d2150aa04103100349c2059003c3d41c601081c0c01c2120b002041c0180080c0d802a4000041071098501040c81a0017030082710851a2946414030b801031404005030020ba085400c10f001c204000c140c1e110596503040307801c0b9005a100d600d5000828689949944003600447c20a45503509100211101991054a0740802003880e600c5044004484030786101c0c00700164000d00218080500c900401a041440203001096481c0c0e01c400d0100141c1190700f003611140 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 27787847 1250 27786597 27786613
    0x803010b27010923030105010608070f030c0c0209070905090a0209040b030c0a031e06021b0c0a06080c07111807020613031e0e030703030e040b010201090f081c090302 73
    0x440340e00e12000d03032580741c01103450442041c40020032490203032146103180c2c0c2040104040e4806100503420340c44030050000c001030360b924040100f08c040305541440100360004c0c00d14040610074010030f2160441c6844455103500c40d6130a000030180010002d10802404c2d01000c64203550305103425000e2003c8090260711800c914081004455000701020700c240d0041c1c2d40b403001a200d5801c44011aa007001e030303100d400c10710800c1400010000c41d4009001502c0054808110050701000300e0800e001700d404c40343d10051001c00d002801c00d003401904c001c80d030214000ac10441c00200101079240c801d05075454240550001b04200007002458000c0841d07100b0b081100c015810415a075001c0c0c03003004074124206050314060304505600303000003060414400906016400340c8103025105d0400f41c2200c000c1c9039a81030081a500000009034411130420426598540c0f05004112031940c001030041106810350365407002756840903218007120240320a903000a04581e21850207042e0182d0040d120359 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 27789097 1250 27787847 27787867
    0x219050d0909050405060103061d010e152d06010c0b04060506150a0c030f030b030f06061306050105031609080703030c050d090605090d06061502150a050c07030509040204030803010b 80
    0x1070010340200000314580b03410000420320001e8410304498201c4000992501c5601d45c800da0050139548c24441c46d07081585211504400086048080f40c00a903410000d441e40b00f0010520b0403040035a081d2680010f00784522207041a41664002c101410310080b035987c0f90b074a542c2c1000c4211001d48481c1e0b81c940c204112824211702682600d00400856807620001d0070000e0151a8051300217010010004100900240242d00620800c00c004040f03501e102085110103984650850703000b4011817410341e4a08014903140681d1007680d505858031030850365840f0700c4c0e0851072030f80361240c020810401c2d4001081441441035402a50207940c1c3c00d120380c01c4500f04586800b40e540001300c10015800c0c010825543c0c84000c0d91b1350314600315017010581500742001400f80205411030301c6428920903101d42c116400040110b0202c039a02d1020000f95100e81150f07044800840c1c00c0c00600f841040f2020000707100300010465288002c00041c14a9120344074000300c3d810907086018045400201d110403 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 27790347 1250 27789097 27789107
    0xb01051e0c0616090303030504150e0d020d112e05090f011401030c140d050304180e06010305060f040309150f031b14090301110a030b01110703120e010219050d 70
    0x12028184824841074a205400108054114030000d0300301690307640403504110000c01d00e04074100e00c0c00f0f4144280c004085103151111b0300a200700b805071044402c3b42c001c41d03001d0450000e190201c8030140107003049a02c0c0105840310245420028800854140310000a0340e2143e01d01600048005010385880382c1d040c2e03821110783c0084d44503004480c03001000010851000c0c3c20030b445c12070880c070b0035a1544002040240d00c2030700f0014254000840c0114890002090401048112042c01c3c41403201d040072840d101c0c40c0a01000d407250b00900b00144071030803040011900036119140c60390240d96114040c10a01d40100d20f28400981c44d021502c0d001d607807600882c111108003000b03400114252400261141816228280d000b05010400d0f95042c4d60a5000100d2501402030f442e5490301103400080003002040d50841c00301fa5004202c02c2000e0300003907440d094941c096000c3d6803807800100c00346d03400c0200000c803038114820022240038590408400004452143c00144002d1081d0040500 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 27791597 1250 27790347 27790351
    0x60216031206210501021606020d0b09060303030112020102070807080d0f0806030a030e010201060b0f0c06010806010b07020609040608030a020f010609020c03180105070b16020118080307030b01051e0c06 89
    0x800c050404400b4010b042e15265014180f6080e04103481c003840d140d141003406400f82000001c03001694000b1300c028130140342c005200440d0081360401c84107828074100111200140c074a1074241e40180014072090042403c54804a401401290441c564a8080c54605480d44c0c211440036003000d4201c0d00c403150005081c00c40c192207420109110305d41030000c40e98564204602800304010300881000b0b5034001c0d84640098040ca88205543d122501070120995100c04501c1c8117030300c94800001000c003c080384039070585403c01640b03032404c04c0316000c12940303412140d01c4c41c3d80251380324400612101c007000200701c07400c0a50040c10300103081c5440710742101c103550f00c50000103004209a000e482400700131102c1980194202c2c0d07030402900350048030640120100100408110800e01010071103984083c0301030405507009100c04d103200c3c1e40c01c0c00c1190340c400c1d00502c80030f024008a03140038082e4101d4000d000040c580607080c400d2021030b440c800341980f148101000000109204280010f2160507 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 27792847 1250 27791597 27791627
    0x70501080a020a020d0807030e1203040203070e061e1504031a1005010e010513081e010c02010b1509030a05010f020a08010503060c340606082a120a06021603 69
    0x508020030410f000c0d4840b070751384111004201c04000050020380c0607038800d20240c1003120440f000303800a00e503844074a0f1320039142030703100b441002c60008401d90518820b61042c0d001034903d46001c4065641c000d15062040411940000c040142c01e01040c0c10300d015200650182001800c0041d5403001c07003411b00340240a8110070a15100184802e0340c00c581e03051200303032003072801d10741d01d0040354242c0c1c039029629046440180241403c98002c40355020542004640c040002c00441601920580c201c60700108030542044821410144494600020304080c400150566104030042d9684508440f800341d5644001a03003c5a11640d20798841801409403034190000c20075130800d55994510f0780507103084103040755046c00b0b0301005039844525410303a030b0310785030004140342c125450000080d08040c025000c01d84100650407000a0742583c00c1d503007140340c1041403c1c0034a2480144408660185c00030b0140d841010304000c00240c01c0d10007031a40200840c00212812400c2c03400605503d002c0e4101 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 27794097 1250 27792847 27792851
    0xf13080a030306060e030f0601181808030f0703180201030e1606080907080a0203120a14040603020d110306011706030712150501050306090303130c080a0506010512030a0212180d0302070501080a 85
    0x2c801c241f0800120315041d50391900760350962040071481c62018112406041068a66001618040160400c0614059085800c43d124185d0303034114114201c84006404a62804449001101550296200700c07083d003000701c1614542600f580880150001c3d070f034400d000041c1201c0800204403418800c02016103203640280064a2103030f0000b982c0c07200e826262081c055400140400400c0c00340ca4101030b90b4942d1440151134a507958405002900100a8003601d9070400d0070300604031207030b04100c0e4814007058481e40d4030b80985c919821180c0500500f515018815120081500d010b521120605144200840110310400b046550f058410603070055009500c414180000080d0110a40e035111003040740380203070704000f402c21000a04440d407102d01240161210f0406100020401605850003551101c1420003c0c0071070f590350344101e0200340c0c010b03080180d948421540240040542100134200105040151400a444010604421405a840203100300141d5070040740b0707680e00c01e95540003 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 27795347 1250 27794097 27794113
    0x6040b030c2206020f010b010c050a0605040809040e0705040e01110301120203010609050a0207051c0f030f020409020c06150a120b06130c0f0801050a0b0f13080a030306060e03 77
    0x4451080c04041d00034140c1e0500070070081400102000c08103900c418115014040c0b99445001a450703540501291a40307500382161000d00703501400c42d1000855004000f010f000606403614070040001030411502d02c94200810031a6681d0340c000c59200c0300101020b000e030303136241c401000f040700d18182e5000c0c800d0f4145902881c0914280382030707a0460706446000d080207801840040c0c010866500160102d0f4a0882801600200c680c0a800c406110794203c83e48241f042528100d9613060f039081d000015422001890024802e070441e501249030a640036082a4445524400740d802080b03514580f5170251040000d00d010b88040040b800009032608121141890140001620001e00151400600700c000c541142c8801e8803c0700c52041c0c10204020341d240020006012021020344030300040c0b070305400420140b07000c80c1c019044440080400e490100e0182d07840c041a003001d105110010b002c0b120000326010b06000700b081c1c0702e2003590700065890504901400580501c040d4a0080d480450 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 27796597 1250 27795347 27795359
    0x90105070e150706050c040305060702070302031b040905070902030421050405010804150509010e071a0a180b070606051c0c0302090a0f110901030e0607090302060f0c03030906150604 80
    0x2801c40c0c01d4071400d407070360700e50006441114902807195190060101e0301e46410001c9a02e00e9501034001d43c2d00c90026940d0075281e03000d0899031985d550202075410341100180c54905168581002141540504089055079994076000c4c00d100865104940194000040008011001d40e50130303e001084140f0030300d404d0f03002000078054017650160030b050001c0030300441e0602a44e0503950110340c001650901a078035045010f00d020348540b94150095210f4440d0104e0710704000752940c480404103a007110b042800e18402140c0c80c0340040c0184052940d640e81c0401c038064180010402c0340d01810f00810030502d09018030510803024844021500c0c0e4880c450000030700002c500e941100d0b0105c900601c130780c440280c0000104504400c0c10901864220b0b4000d10040b10300107040c2010007600c0410a00c4102400241c03500c0045030b0500000341d034a1418001807610901405110305c2c1e8000c0740707040401040e4020b19640c41035071740019542c0540100503020102d01d02d005101d43e0152803071420a46001 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 27797847 1250 27796597 27796607
    0x309030c15011a251b080c01050904020708041a03060a1202130b0406080307030801051008040203070e040f020d03020a11031216060b03011410080102070c0302061b07060504090509010507 82
    0x64060002c8440002c1450b00e00314a401c040c54801031649201341e10780d00d1407501c155500f003480a41e0100c928040070020380c05001040c45c40792124180c603003a01e02a10710382080000e5101d203008881404060001003011040c00380c80e004580505d60300e1340d94034100b00041100002407580002e9aa80034036842ca00103032201c03180241e4030700801502144504070100003401a0141c0d03001402a4480420341006040e801040641264015104402941c03d0844100c0d01420116030207500b503032041104100d0380080c08505031b4054040e0800800b1081c2e40d50015103040603205040e401680440e00d2103092128051000308030101c22401402c3c00807951910140501810751262040700100c40e20070180031041c4c01028031020b00600030040b040d01000846003094068411a503650401c000c04a002d2005100312b400040d04030290040703451859003041840d91040100400300c166600642c000100d007042048068851070f00d805403564144601d450458400405050180c0e04100903c40c0082d000 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 27799097 1250 27797847 27797879
    0x70503010b13230703061d01060207061d040203010b0c0c040b030c0114040305010237080c090103020903010501060f020f0303040b1503030f0f0702040c0809150603010f020309030c1501 81
    0x180b401142d510118062030399a071088940907904403c42c07808110342258907601500603190003620a400000900c45100c6070682c09014910240c0e0080d1020b00c9554001c940701e5059071602100d0500d070180a4010400342e80080c1e00c08400c151021909681e070600038010042110820b4400308182c10101c2d0002ea0f81e96604c030356017810304c010b241e2541c0d4100580d04c2140d02a6801000a550f106030658a800c02120301c0c43e9101c45250011841882011401c1e0070001c1140d1f650340c1d01265500c6081415640e984000c1304241403541c20020741d0300131b48007070003000d0007842d0949540900c22080e210203410842500713aa201160810001c10000603075822500ea00210450311016200440001091542c8a10034005004402c08903003002c03164001002032a80a20030f941c18480440c2115083e1000482a12810101d4219108020b50031940000300c035403040340103001141c10010b0031031036022039200b6a8845082e82000800401c00d41c810030030700c0d481e06400110311045601d0414540404041 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 27800347 1250 27799097 27799129
    0x11202072001090e0f061002030f03010308030c0405040c031a0f0d170c030c07031506060503060108060f0d06020409061a03040b090c09070f120e0c010513030606060c05070503010b 79
    0x8840c8554540d11400030400a0b2604c44071040007420507a010040c200812241144200c582c540e42c0300b2514408010b455a03990014200ca0640e42140e45042071500000c0c003821a180007030000188550350390040c049258810340340098040c58841c03040217501c40605056008094010310b003006078440c82c010150a540040e018031405249602152143c820340210840c0e41c80003183c8a5200d490224481d0120781c807c04d10140020340d11181c8605407441842007001141e010f1001656950207005078030742c0010700800a03008820b1a5002414203c6032660a41d0680d03408601405041a548a0303440030301290440c05582003100e4410300078610000b4002400c40d1100710108049090401101818210090840030036203499080101070001840f8154001450310b02400c1141c2558840e800c101054100540040540000150382503409076400106a0113561000008502c0c6841543d02400c03595031a66000525410914503207203a0b504914844c0c2d242510388031490756144050a20419 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 27801597 1250 27800347 27800393
    0x10206091009020a0504090c0806060f010c030e030703080406030e010e28030c05010504030c11040501140d1506090207020307150207031e0507030302030306040f0501030807060908040810020901120207 88
    0x100510104e10912200d40c01a80c205040103134a10800c0340e1120b4000503103107480215032107a5a41700401642100140700c85010a091621070800f2a20450203003240c0040602180c2020b960307591841005d500c0b07079009038000b076918040341d06030309801c1c080c074024004064020702c01407000505101a81c40f00803610a100c0c0c0d58199268200350080e0820442a0b41000003006a8502410081e00350548540100c4030703d11014849031079481c0c035100d0141691100d84c4515a0000c826042c03048817100c4034025207100c00d00b0161081112228001e1030041c1104000158442210784140361070310340240c00504451084aa0040c0384550005d90348044a03045002d4444010f440b10407034003401581c010181c0b15008448003c820305030008019809280160350800c8030046a00d82032040351b1007800014240780c0200301c0040490f0143e00854622401240618a4690b0b1150043e1424600d03889807000ca54021911158548e081040782088080f400300c02d42ca040350b02d598540ad1f48510302d0f1580d000f44 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 27802847 1250 27801597 27801611
    0xf0303101502070312051206010302031003170702030703060e0f07030308070302070804030f0308071407030203091314100501031b021c090503100509070501030c0206040308060d08120403030b0102060910 89
    0x42c82000700600454214204110b90085c952000300181d22000484200d01c0315207010a074030354803070310807a40300c0d0042e210014072240c25030340e60311403061440e90284c100441c1408814056581071080000031481801c3c0002c03401c0140a21500708032140c0e4003c0416080001d003040442d4200b50b00741d07440300580c98010b17036a8071540707840c91840c01580c00c054035200131444600101034110390b240380109034944a0101c200e240d600410360b68404c200b030080060b0014000c5100c2414140d2420160140000e0007290044a000301079444070b10407600300c002d280b640c8208024a50309480341000d14109c01d172841d94013a010f20006565043c90740e881c411802c4035000d500e82050b02c5a00d101000d0300b8010140c40d146d20001e2100e102400e030565803a0541e02924100040c2903000f072040e01c014407520340140186589944050f221500000c0c00301c0c0d001202c1074985800203c1c10001440a8080080b607034220341840e00b0002c0807500c846031040d065600600601054080001d580c0c0341001ca0890040307a10 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 27804097 1250 27802847 27802889
    0x501120206040324021801090b0406050f0708070b0c0d050a06120224161104090c0501080a020c120c0d02012a0e06130e0708071202031512060105030f030310 69
    0x144000f01810141505c0819000e440c4c1d801c2c00380c0c01c02040001d91354001d1080c0c07561700340b440611481c802c0001044081000c240240c0064014103841d9000b000e038541045940c0d26aa54601c00c101c4200f104aa400105c0c0040c8500520600b070b0060b0700c81d030303081000d54200a05000a26480e85019206009240280810702140c1d03200200b07400f89405a5038840315042a00d04034248031b04811948961250101c8415081c035208080b0b00ca038011800c0e840b16840d00c8010755200c0343c00b130250042c881e000c010800d1340c0c00c1d0410007460100030803d4815038442082d1169414003061040c04000c40e414034054020440d9000321241020106004038001d00801c91402d0b901580104500c0e508440c02140318286140e00c40b5051f400c40f000c02803030180b0303a81e800d2421107a5140c1100c0e01400700e060165907000348003c0b54065a40405080462400901640006a0081622a045541c942c80031005201c40e04082c01160040502c08005504608082d042c15103045224001e40f40d10000b080038403126 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 27805347 1250 27804097 27804143
    0x150405011803030b03120c100c09080303071701090c210212010f0306050c030906040f060209090f01030501060f080a020613120501020309010b010915030b010e0a09090605011202060403 81
    0x403041800320501d20050924010b000f401e402003466100380291404a40004040b80031070340c8a1a83c01c01415442440d282da9a00505601c0f030403c040003204080072545040800046004081079103e9205d500281c051031000104160400c41901381808244403000fa04014500d00050354081903800b2780c2c041d010180000d005a0a00c500040e407031000000381d0506a01003001542c0c01440284003940c0d07001a030030024403044c0c0700c80e0203981c4080006408140d540c03200015a5228500143c030700a00d0b10000382003c04243c8006c618642004c004004100d000d11940c0010712841c60041d0920785040074182d01c030071f440d0402034003030140041d180380130702c0301c45e446603015245a00061060000604002c7c1c003e40044030920300c3d943c0382c1a042ca09a40c02a560321088402d003a078070407080103000d04114044c02c00701003440c0c1805403041d00c5940310350320300950401400c010301000880000c18203081b03040d584183d0001c100290090f03140d0001d40c840100300c400b0b80303410001c035074414100403150001e = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 27806597 1250 27805347 27805361
    0x50903030d05010e0a050714030702070306020f0a0306050109060203072409050604060c0201060b0901030f0605030607110105010e0105010c02060c0f0a230d0206011a0409140712050103020315040501 87
    0x16140c080050081000456580558160b44001410708a05d640e0452003201321001500d4820200b642c410603003003a58020402940e114207640305451000e5525914a01642c0004d00340907600d003c0801c002c16880e50611540c80140b00c246071849440d4500003020b5100d105803d0050480c0e11110965891030940380c480080e810490340f410410741e10b035400c4ca2516a582074a045a940c2d0405c400d03880d20900c140101e400745d4090b81c038071030b140c0a0b260005600400031804100e210944640c00050103a40601a4603c180403c4e03c030310b00175020210b0910b003165016040303407880d05c0820005103e1642e0084400201c82d40c12b0301c1e001d1752803005854040c0f41140c0d104040c0158412072076100100038184195080101e00c4119140031a003d040b16281c4940415a46800603409580100480310405e1101460041804010341c500703911440010242c2d0b0f480210f0010004010040c41006580105144030003410400304021700c1d419940081d888107841c1403101c0400203481c4c0030400380b260a40c0411 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 27807847 1250 27806597 27806599
    0xe04091a04030c1e110f01020a0c06081009020f03010b0c07270c020613150b12010207030206010f0b0708090105040b030405010506010210090c03140a0803090c0f010302070305190509 80
    0x1035980c6000d25008200e240c0c500d8084400750034105103c00c41d034000c0040d9105080d4030050104521940c0741c2072080c204110981303141184198990a030202d40c1146203203000d06039a55036500b16141882c03001c5612b140952002040354030410000c0c1e100709440003074078152a0094100d981c0c2e20f082d5000d5920709a03050704001804d203540c1c0c2d050000142000c20030100008015002c0c441e43c4003004050740c50300021200302c03040c400b00709002c0001941d1b004481d0031102c9090000500460b507000821110303ea44a10b0846603940091100103058040099600505910311a1185a428000c0068250094210040a803030001c0f440014581c081c5007a43c0c050104117282e1502e901d0503050441c00b03401309541032400350145100606000d07c2c0c0e800303412403030341e00100c642c403855186564041141602c0c60111a46000301101c06001a090784001c5004482100040054604440400071400407811420341410710401131000001c3d0407005a844401520022020010883c0429079403441b88143c1c00b = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 27809097 1250 27807847 27807893
    0x3110d05070801050109110412020d170a020a140c060d0207030e090702030a080a0203010506120901020c06090607030e0c1503060f100309030201110403020d080304110306160206070903030e0409 85
    0x2c194a201580000d048070040c0c44140041c4800d55550383c0c15101c0c50017400c1010505c0c507400005414a0628502024841c00103242c50380c40940b800c1d006908030342c5113000180c120030502c506001e9032040900700928602c4c042c01404451030005104c52041c0d40c0005041500400c3d60000e240c000e4981d03210200c0003501da080c051902d200002d48070390154900f1004562800d011800801d414401e5034141c9134080c124a24106050350401a1044000e08022080d9002c001d82d0903200341c14040343c0c0c0105038010060038181440c500203001d503420ba45200d009648141e20315403495580b1010f080d006036800405544c0d945905001c105503220002803175401c0b08980f00302021850f0315a0000e44040c0c000d60007000810fa11100c8403142d8450381c440654402c81c500b500c2004622004015500f061156403030301982c001c09000f107820a03504451701501148a03608060516405118261380a083d41c070302403c04508541e070150a4000c842016800f4a94a085010030400c1c0c82c80c0b10070300d54015540f8 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 27810347 1250 27809097 27809099
    0x80105040803011d0727050301020403030e0a06050f0306010f02010b150310060503040507380301060f0503040b0f0c090d050616021506040207020f130902090c070b0103110d0507 78
    0x1c94082a031080c450312a10010000941c0c001391300890003207000b400346079201c40701071030501c8441e01140894408402a4190f07194002099502480204003c5100707441c0c444074000410104513113109a03034024014880b0030400c4007290582c002c03c0300d84c060700c00d00b00401c2a191941040340140341400001d9003140c030154422800501032030186200e00825440200595120700084843d03000550300240240c0c0521402d1141000d43c1102c47e001d03c0b454005030441e00303140990280c50040f040424600c1000000c01400655400341d5003015100c4103080551450825903100b94841c000103000c02c1d000ca05d0900400e00c560315480c11101da8500042c0503a010710014100706032501d10a03202c0c0c40c45202001c01201c000f40c00803c0502ca84100540b40d030b4070540d01e400c140406074ac4103460032a0b0040701d10b910001155a00a0301e001000200b840000e0450050301c184024403001400031260310b0801c0c403c04000804000246054036448000c00c0306001510010a45180320450018030a00034240 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 27811597 1250 27810347 27810353
    0xf02120a15080705011b050c0607080a080c070b04020411040801020f030a0501170a1101020316030c02040c08010b04180209091f0501050708040512070305011503020f0a06050702010c06020408010504 87
    0x2040700600e040100c4050400e5958802c0d40e9104000d11507203021540e00b19540c01d01c4402c20802000c4540580c040e55105500d510000f602a840031500303c880080c041a046e01c00d07640b002800381c0c0b100990f504035182030384503190703c1d0f44081c00500003845280c45949007030781c12060b00180c5000341101c90096440312041d000d2141540c00883e035140e41c0341c0c50310000141118801d44810710040c60b01002c7e01d840b0709074ad00d602e4801401000742c0d44c1944006c00c02200032900081e880c0041902a82e64103200b2448ca20400c800d684020000c02c00300b02214006221409107501214100d800418418481c8600000400b01a01855822513031100a1a08100d00300301c0044009882101140036045031544680c01598180210710001d4411a405c0c0018403050921280304459111000112008036650707a0310207080d205410f0750058102d02e280405c00071403c1400000310000c8044600300510f50905000800c6802581703806810042c000005600b41309560303040f1406041d03004028030261505003 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 27812847 1250 27811597 27811601
    0x10203010f0e060f0906010c0f02091003051924180605010609080102120105040b060d06090b130219050f0f07060603030e040b0312130e010f050117010b04090f02120a 73
    0x711450980c40c0020b00011018540425807810780c0fa00141008400d0315400300443c1c1c000b00070b0500301c6001003900b0511001d80c0c1d03200411849682c00e104c0c1c0410341da0441c64500d08040c505211801c030607500b01d0388180040c03107400e84030140d15080100c151440201c0c910010282183d44d80d0001140e0350188000705210340c0e0341000c0e040c1c030703241d8031018801035903000094200d00c03403000840c2980c5400b0006001c01c2c0380580007031382e124030000d0a003400c1c82d4140303618808030b4001c0d13072026801c2075482c0700c00d03000b50400c50b0500b880403400d1031046007000380c0d009181b803c07284490400c5007041070001e041941061044255034a02e42e221000644418162178010000c1c08180030070f034045480d94448001c18900344c01084c041e207074050043c040b01140390306080899003090b032503800c00c91584200443d81d40312a600d46d034002c089000000d40320624100c000f42c034001c040c4c01803c29203200d400c01400b03410810b1084900b01d600f200e0000806050821050b0700900580c0d129079001d81505081c084c005c0f20a0b = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 27814097 1250 27812847 27812849
    0xc02011104080319140306040c03090506071d0d03140306030313030b0a0f02070807020d1707031d010201020c190807020a09050a060906060f030203130203070308071704050d060902030c03010203010f 87
    0x130700802c0030380d40c1c03c40d00309840c0041c91408246070400c00700000303901c0741010740001c02c05c01b03020304010403801ea40e61f030b9103420300c1c4d01110340303000003410b0325a1804595521030200707691030030070b03161102c84900030b031001885181d4541c00c0c8010020000041020303600c00308210342e0541880c04090002640303c0c40d00842c188416aa041002818030540c0340520485100700c40380c43e03030312141d51883c001c00341e03081c4051104614400c1d0340d1408007001154218039560b0060083d140f0950315103000340203182e0fa00450a0010140a04580c8184114103a41034006084850034025440e80c5403040b150f46402d401a10030310b20001d4000d4084203000912091030740040c1e0103580c0404040c00040c0e102c0800a085949074407d9000040c0000c40d507088290203a401150000c140c0b4018600c10140d03600442c0c6400d07581d520459103204001160000d1054809901e415074a504c0300543c42c10380350100284004c5103400000d4501a6a03411300030840d80c0400c030f01503001e403014009640382e603500c2d0a664408451 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 27815347 1250 27814097 27814117
    0x2100507060c050f0702010e010210051e01120b070c0807021e09132001030902060c0a051009050706110f010f0608160f0e19020c100b10120c020111040803 68
    0x4002016a40783d0240d420344a0307480040c0c0b4a54100000c94004440d40d5000b41b0300b5034154085c8480680e900768107400b8062013803001140b1403e070038030064065143e40704140c2c0202a40440550100001070750030840d0758103e030035481d02d10b10f04005410110240c0c499120300030360005510f415450918404503908840174402c60351001c0b50b50396030607900320034000c0e640000c00c090f504110007800024900c250105110040c03400040d10411940480c445e507100d0a5207210591007124410f0402c40e00704026501503250500a00c50041c0742d540d41c030750b500d40c00d000340300502820380c114511020040282d0302d00e48405200034002c841c40440c0c00c00050519005d030392a140906440d2401c1c072002c0a403001704640d050940780c52003510700180d021205501a0840a0807000d01107140410011400500784040c8000d025001140c0c40500000c11140c56240c2c850140051080416586070801034031500b030b028411000c102082002c1040380102007a0140498800001c600070402c140d00001810b41307442d07 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 27816597 1250 27815347 27815351
    0x301350c09070e0d230a2114040504090303020904050a1401120803060906030307021503060117040b1807080d02070f08030903070311010507080703080f01090e0a08160210050706 78
    0x41c0c02d6400c07a01455942112504400c00c48904c0b0002030a543d03800d050301c00304010450b100703c2159000c504010b040074040e03500c6804040b19104810350a18400503039045414882d82040c1030b05134101c481d00640c8119841581c1e45c60f801c006150194048824004005001700000d190082d88407004250b8003807285d00340100c05c800420300c007002c030810340400c64024420b6415580d581003003050010000f030203140c040c00180402c1d00140c0707800c0706140400c10000c06041d181e1914a000400d00880304042e02030301c4020f101404049106116aa43c12541501041e150300708c04045081c41c040441c2c0c086400d500c580d03c401807003035a010614000390b403031140020000075070300c0400598030f014070000c0d10352641211008000103009044c60603071000c410b040c0682400703400e03252140550030a00c02600030030900300030000b28174a1071110a01500580804100110400e81c50765502c1c03015850060040c03400040080d4041c8999055a030060340c02001181c0c8a2100040200150401d40003203c00764 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 27817847 1250 27816597 27816601
    0xa0c05060a050711180405031210050901050607030c050d090e061008190f050106031d0a0c14030c030f03072001020c0409061b0201061404110301350c09 67
    0x100e0880120744601e40195640c0703060040315107501c5948030740b0400c40303a803150860341300c0885100d0f40010503208501410185451750702686c070400305480b000b09540c0300800c0948040c40150b0b10b01714410705440301903038002c0d01c0781c8507403401340e440340e041940142462045c0b62401078a03d900c4040300301959540b410341c240580f50720040c02071001745510001c010030341c1040012041d50204000159405001002265801e02c8911040c00c441d001e07084100025150f403012000c28603d00340028074540c003200101202540358032004000d800c00e0040c0351b9504a04d400089140c0e40c1040821000034008003030f03400304c00721008044c1c2c0da580300d46421102c0ca4190201003001c0c520041c800c158212042e0090f0102c028400100b10042014440480b000e80c0d03504218410912400c0c154440720003035030000a6124100141c0d0100003004d03030041403141741403400c4d03801e0b41400202541c0c1121090f400743d48044030484c100c9041581001d04135400354a00044010740004c0c00126482d440034191a040c0c015 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 27819097 1250 27817847 27817849
    0x20a08010e0705040e0604060b1f080402090105060c0c0114040810020301090501080601060c0b06041803080402030f010c050702040c031b03020301031209062c1801031406010602070303030905010b0904050a0c05 92
    0xd1840c10b00d400c43c1703a802000014010815030313000419400402071404032001e4400070800c5015408002e070300c000620150411085090031580e072400350504448550074a0400582280d454000381746490402680c60b8000d503459a0388803e5401030940c0d98290340f9107000d40001c56000390024801d50a480c0e041c03e00010320303444080760080c1601d41c19600c0441070b15030390326207084460001d0007980c0c0096848154104200f4050b404044171880f135915403440d03092a0040611f08406030b064103200e6450007190380c0710b4a0300141150b0009605445c0480d01c006001070650040800a41000317904e042c985d241502142d143c0e0007941a00d109000d134040c1c125480004894004403802800040f5903180010190901c0c10f01c103205e07841c0600500700981110300d0011800402000419007842140807005004001411a01031010002030008103400d41c0b4092000b541c034415448080c051581d05d130906c0e418480e0030f40000d019941c000d00344d502c6604107850155a545d211007010348503010108404181 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 27820347 1250 27819097 27819101
    0x1505210c060c0d0807090306050103031707020105070c140106030b0903070309060503040803060d060b040c02010e01051303020a030804081204030c02100305010506030604020a05120a020909090712030806040207020a08010e070504 100
    0x1681d90340d10001d04003c410444295064203001d0021000d001003400c002001031158010070340a54071175a516200c2e2100078108440450001c1e241d0015641407808000005074005195051560400c02c200385000030003900a0040205800c040c128411800410054450000c02400c00d14865550b501101e90f480f80200c80d00d00050f60000e01c0c50310100003003901303860460140c1001902036500080c640e01d0100016003140c3e415518500543d444181c00350b0002028414680d0240500b4040040c24a450760b000b520b400304075070300a052060660110302404086400c0d5120508040307000d5969040034100a440c0d1803d01d13108030321804a06400040321071080c01014100c6502134140c5007140c42d8102080045d405c4114003a081207803d0050124441c04c40c01d4503402510429070040e504d03c942024072482190081c0802029400220108009236000741d6240005415241440c4503481e641c0c0060082e2180c0100a94001e082401c0414805410b61095000d40c400000f00d600b035940e11014030003 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 27821597 1250 27820347 27820357
    0x10501060504180f0f0501090e0a0209011a040819020918060103140a020414040b010506190507020103110a031d1b1320030702120c101505210c06 64
    0xa0400e000402ca00320700715000d481000d0107007030b000caa813a10303040b854011030700c00d0040315039036545807001000301d80100d1107000124a480c001400741034865030040742030b051040c8168551510824400c0302e061104c84152406480303802e080d501045001d5025040031070702484140e20500141020652203854000b01842d401d2114014040782e030301e55202c0318850003441061245038050b82100760016941c130b10038202d104018030070805560404d0b041c8404c0755041600407900603c01041800088204040300b04110f0038546480c942d14655440128094541d00c40800300d0303000086040c600c456007580121074004c40401c00f02d1904102c0d1050907079282002004860401040805040f150030091604600b1904238500440c0f03480c1d8844840804201b421a064601d0001206110906906101d10714005d40142505401d0920146481d41c4070501907103517004183e030720301011030300303910b245d64050007000001c1803416403910100441ca208450f260210401c1e005488043d9120300c2c01006880f = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 27822847 1250 27821597 27821609
    0x61202031311030115060903050f03030702151e01030b07031b0512090c0603070c030e03060103030801050f030a0b1009060b1204030503100515040603052401140c0a11030609010501 79
    0x18a821502d501d81107428440c6440e406548403010001d402c0a4109040003c1c19260303582d403d268514101682400320702200356a10350020828045083e50009204011011802907030440762034106481c48806008074000c081c01c0c0307000700004180310301004054801c03146600d00380b241800401c18405c400658416810101740184440303241261800d40b0603901064641c2114003e81d6004002101c941007240c04a0010302c0000e4410201580042c0b180c0306680d06800418841d415a58041c0c10a06c050183c079000d050038074140c0c06290b50400202c40850340101440b1282d0900007400d0020358101d014031100c0798100040012048614411202442594440e034025030710350342d400311556440a8901d21010140b400082425664481c8124808060b2021740ea076407440c040f0080e050303400007418540400308401010308103920712112501140402d180448110100c05122006c80c010701e0007010651052240301c0e000c118002680c07005410f4102c04541135662094500390030b0702c800340228 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 27824097 1250 27822847 27822871
    0xc07020123030c07030309020a0f050a09020306010212070807120e0307230409030c050709091502091f020109080c0105010807080f0c04110d0509060601080709081b0a0e040302030406120203 83
    0x2000c9243c50800390015500c20321b00421a4071a54002840c6102c031508031707401103503d0210401061520b000d5640051455810960641c640f07480042c2d210a40450041e851440001c1c00b03204111062049941c0e640d40609065240c54817044010484060207040501074424081c0100788030050300c0030b54450076640e81e0300002c480220010720000e8100c0800c201d00340300304241c1140015000340203200241407462400156078806d8248280c041d840700c80da0b0840395104200200c520b41700d030a0821041c49002c0d104e50b2000d07080620490040443d440083d01400c0003241c0a0046c030019005281251801d004a034641303600e840300e498541020358001344040c3c1c00b47ca1140d2060406800c403409203504448a182442d82a4240d18151a0203c44c43c074020740140040190307a40e0020141b5401c425140342050400d03041c0398081c1e94458400b600c40b814190301604103c5180c0c1e921010401501c40c0d01960300d424100303850065900e0308075004100110790804480000224680700b0340784241c4501c510703 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 27825347 1250 27824097 27824101
    0x6061704061505031002220305030d051b0412150212010312120212060306011721070503071424040201081e090718021806160203060c0702012303 64
    0x14000041a000d86068900c003551040003400313650074401e02415650804002d07942c3c203015240c4e12410f090920000820078411441440070070000025280740685ca80d10020342e94590304201c83c4e074084403007440f40d206500041c01158001d51904482d0351a4400c1d14181c034645c06440000e400ea01070208404030100c0740c5401040841c820520711403484559052004480c0c424004007004d0381e1040b8036910581030000144005801c04110842c018644440b816030244480001680c0392114480c45800d030019129071441004034080c00c0f21032059001e400c4903501c041c00e180951140c1020401c0b029540180303a5102e4414068030700140c90030101410000300350ba143c1d0300546030300c88064405c1280d480103100c00d24644d500c50f445107006d4038040000749186480e0913400180642015010544140140050f41c0303140700c0000c180700c50a10440300075440b4000c00022034107003524148080d5044c480c0c0c0c41404007010341c0301c000341041d034000c0c2d84080c65110320620020b00030b202503804100d54042040 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 27826597 1250 27825347 27825353
    0x20411041a0d021306030902030c09010503030f0a030b06030a1401060203070c03060c0507061508010b0102030f07030c0212100501060e0f0102071a161112070e04080a09091401050406061704 83
    0x100404441c10480001803e00082401c4030198a04c43c0d00070401084d60380041c8000e41c5010030850100c0001140c810700c0c29810080070036101d0140e0700c10510091008140070a400740039401103082d10ba0040c10650b200d02d48420b035007014004086a81a01039050360000c242d4620200c21500481d0b000203840c03a401d880c60f40c4140081c504400e4905c10407205200f80c0002640c280248550120796880c0d55128500701440c007400c41d03003205c4803030703055500411001c811085003c00b5101c104d0340506044124880c1400410001001008070862600440126004904481e4440e0303041e2074943d0f944121140250040c4004c641e01908101c1c0507901c004010130000043e2013000026800a0000302e060828100809401003e5510b044030b421200c10601142410035a2410801650050091240310b19011221030210009840a072a10000044000d50345026000390002400200d900300a0700e541c0070f4446c1180e20082c050144900c0c1401400600c15100d418800501107180018403080d450700d50f = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 27827847 1250 27826597 27826649
    0x80a23040303051e07030c0204060609031e030c0b04030c170a020619060f0608010302030c010c1a0402010c020a090c0906031b030207020301090209010b071406041a180d0c02041104 79
    0x59440d006150000013511610b111030700260401d24840e8843d011000c01910401098038081e8001804000070184100041450a100c40c0c0b403040708039040c558446980d00b0b084907070200d01040a01040c4120041c03000701680200340100090003900c0e6070500100c002c40011440c03040900110050f4003040200d0040c1e1030001320100040d450680c0001c11507581d18940035110010362041011a01d040300420641c102440004800c120919000340442c01c42da440d0b0106201c1a080c10482080d0342000800b1a4014525400e0158004001c0a074007650313100c0490180c44880003840c0004c501c458001032141c024040d4080d1286258103400c01d90501482c124029000b00c101642d041d0340724060a030141c0c44507281c960288c0301a48120340d644100342000705007412601500c2000768000420040403500c3c3d14458940c0900e2980840080c3d01d0b040082001248800050f90085c020102034050b070384d03044411410010310903501400101c0c4040181907179405207100d0341145022049481c0c5a1070300807 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 27829097 1250 27827847 27827857
    0x6050405010b031609030c0801020403030207080102030c0403080a022505011704030203181f090602120403021003050601050c100501080c0103140627010b0904060905061302030a020c01020304080a2304030305 91
    0x341c6405e81c210703130f03980d180c1c03c03220750181d40903d071203075800141030050580c140b195a024100700c02c006d42c65420240b50b104407501c214400130741001001301c0c140c220180b0a024440d41c00c030400c82044411f84078481c6d88046200c180c0f2480d400f19850703581c004100301081d00344030700c60b5826401a50070a860041c01c001014803601d00c2681c0f181c6d42801e4210221090f02c0c2c030100d810000e42d01d19902c5030034000701030714140100c1c0b06c1c8040a0300a010800040c0e031030b850118024100c0c1d10300414a0f4a0717900060310705000700c40c4a480c060051172800e91481f441640b0450480b4083d500315903603003803110015011111b10000000c803a248180000d8001d05010300400301142d0024030100100741c4040e20365462040c203070043c21243d50002100031581c40c25004a0b4040c200700c8804100703505003031002504440030200c402c040c0c5078002c0300168080b5440d038151010320032404029562440c01c0c0c03a00c01020b41c0454001008200210100441e2000b8641040c3e2a00c2070760307007003502c0c041c00c6440603100740d000 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 27830347 1250 27829097 27829141
    0x21240204050d140106050102060c0301090c0504080307060c030c0e1c170c06041110050a0305040303150f05040609090201023703021e030a0e04021c021c06050405010b03 74
    0x8210004040c2c803181000d01000c0e005144201c0180300c060980790940740c00d50b005034110b46c40a420302404c0c14507134003100d04451001c88009002d58088000380c616028940c0320880c240008264170040c4107507500030040b40708007950100506940c0710780c16a500500400d03140d0b045140001e058400710030084d19844000d0041c98200100020407420007000d5000e80c01727a04442e00444140000c03c410600c004602d600100d80320b10488101c0e0000801c68001c0f50350203820540c07100c01040030b150290344640d80c40301d00e00c48003540b120f440b881c110f0a84e151a11070b807801540b601c5030009290129100b005801c5c1d074140e02403c090302e003511402e03120f046a0380c220070301d004845081441c560080c1d07040d0100f0074030a401400b034450715814202c040300e800c98002d0a4940080040c3c000d203c0d4815282d0f001c1c0c2c101224010703240c03014640388030201d02c0300c00e6489902c0c506c0080e68400602c0320704200c40c100034010200344a59510f4405110688100f80320f016104101803010442107241a009070522404c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 27831597 1250 27830347 27830351
    0x7060905030706052d0f041b0b0406030c120b0901050607080c0d080103150905120c10020307050304050f070b030c030c0c070b220b040b0c1609062124 66
    0x81d448031030466809907412210703c41c00c024004100809030501703203a0445580f15040321841c007038a0311480c2400003800140308003028041c49880425076488074002c2c021100b14180c80d56194007000e0300901400354804046071480e04e05070035818290007035010284005d0b181d2011641303050f0a1012641092504035034940c0207100e1f850b042442040750030180c4040341c0e55408194594200140c1c0d8138001607421004505240704000412000202e07002d1403003101941c1c2d5a00c0c00d10008041c286160721000400650000083c08003090303005016500845c021000c1d01c40c1c524445e041c159440c2c80703500c02e10308980403d00000d181100c5082c06154401c07810101c803441d086c2d442d0320141c1019119002604001c00100d400e5070002c0d80000c080e049240039408021a082c02d104090708a0b014600c03c40200440005881d00e181d00f05000d80e091424446171000c24054031101d28401a010602480c11036290014201d10b0017100d10400c08051340d082104140b00400c8119003681860008100e900713030603 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 27832847 1250 27831597 27831607
    0xe01050d0c020604031403061813060e060106110d0f0c0c0503010e07170f030306040b041d0606040c030209090402040e01060b071109070206010602060705030405011407022409030706090503 83
    0x3824003a07003820089a5018003418a4285809048452440c41d003081d1a03900b4420002c0b0b6440301210b05600607014000c51525a940c1c149405048600d10001005079050001b44004a42c001850030f042c1c0f8115101d01044106e014019a5110182c030007040000b80e12070100302c40310780101d00d140010b90040540282540d201c8000c00e00b9513402c0301d00c030503003903000010411a0a214060041001c0d0400010f00030340d5000b25076080e601e00004e000144916510000c0313248664580e0b0140c0340c1c580740f0744d103c00495400d60105980760f004c111859400f490511a40d01703c401d04c00d100729009014020300004060b2070329000d1100500c0302140b03034107503590b8480c0d000c1140e044180103000740030320500410490401510900007480000b41640c801c0d0f42c482030060110580101c0c030705600489501d0706507201d45d91400c00502501c2c412144403001d990180a100344180d000c00c103484948040d200c0d00401c10102c0d06144254001250703400e0803504280000c000140e80d64001110060007801200d040c070b = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 27834097 1250 27832847 27832867
    0xc09050a060206150f010203040e06040f0c020703110a0e071b0b090f011406060708030903070807060b03060f041110030605090a020c07090902010903080307110f0102090a0816060e0105 81
    0x358150740c000c80c0159000307000f005900440450004c6402c8415128203030b00784158400031b9501e0043d401100c2c8e00c5001600080c030151070342c0e4040385c03480c000d1400510074203600310006500c40380580810364104004044407202400d00042000072035001e40c1d040d0b04503586100084903501d001c0e40c085c4180d000314039000700108012002d990f000c0d08814014041c90140134079242d00b143c2c0b8100581031105020710403c40c1e184d1758130090303d4050780c100601680d00d0307a845c3d16003800e520492000903c3c1e24400f0540a040c005298400100c1210940480d0740c191036481c6080707000c0303804803001003100c242c0000c2840a07040c0509c1104190001d0305011400355114000540311000c2201c51410043e03001c40c90380e52513a82000560b0003000342c00d0040119400680008024102e07900000e440c030000040400c4000344219811907841400c074050780c607008440307010107010b035201101040c445c0303090101c00309007030002150052004640305981da6005151007019205070004c9082c00e414808240f00c180d8030 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 27835347 1250 27834097 27834109
    0x11060a0e0307030b060a0501030504080f03090a060c1205180d05130f0803030901051b0915070203011508010f1e050702010b0604080703030807030b010c030c081c020415020d020a03030c0905 83
    0x3d948541e041c25150304c1c2000500c1504501c69220b81d040608003424040441c49034402c85050014140209a42c0e5a4152190f490942a51002000140741207841350103581d01c408440c051509180d01400030f0345412040341d80039000da00809626810140025081a003e6001007a400b0b8a80317102e195143d070749044030540204146e00154464200100b0050a61401c0c8501940100c0e0043c206007150300ca9017528100b400340c840424054500d080c688640180940d060340d2001f90700074020700013041e0b11f0700c5542d519817651140508660801e48401e07800c411900601c0035040c01940b03c04801105000150301500d00500214103655070b4000b80c80b4a078880100a0020b400c01034001c26209195160040000704024000400c2520f8041c0b02e0205a030b0003048204580d800d850b215443d0461030078040350a00c51448640008070311400c0300340400942da0040c1c41122161540902e2545100d030069840e111208051001a04000410000240254007049008031a4505050500d0712440841d00c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 27836597 1250 27835347 27835349
    0x405060a180917070f03050307021501080a02030f0c1c020d1a04030e010819051905010602010c020c0402040b040b03150402030705040e0601020d080a0c02010e03040b0306100305010311060a0e0307 86
    0x1400d444030340d40307424020f00040040014182c4145140f40103c282c8072001d40030301480c1c004040090006c0030400d010301c2006048605603507004c0000c0d16507581c0c0003243d43e69030703420400c0f4001d02502102030404000801c0030b0014140141424440400d2801c0e42044601e480c0d00490384070442c0c50b407070008180a416005000503010f0400403640c200f81c2400340c0140c54446a96040024640400c51440c44580900c990400000d172701090f02d03150b4042c0c4000003d4a00101c52070705141100000380540d054020007495081a0203407181600b01c141880103030300c100d00541d146071208210400c08038102074004d603400454282c8040b1a4210000000c00baa4010f840200c0010320104080c0500380c0d20100164200800340000d0002b0b0708410030182044c1001072103050020780d03130b81030500f90a000b900501d00d1018103505607580c9940b50405001103410641e421405000384218011510f40644141030507645c000e0156405100d031241003090b29844102c044c41000f4a01c0a101d22039181004210 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 27837847 1250 27836597 27836639
    0x1202030906100e0112031101020705010e100c0305010803041202030f0114060f03010207151505060d020a0e0a0b040b0307050403080711090a020702060711030f0a030e0102060a1a0405060a 82
    0x401c907800c000b4842c1e2400719071600100904680d80c0c004000500f0310450708080698141098080340405100e8a4024021040007600c3c81d402c01079800e1006002280300d8031612400c0348204601109003208604a4800340107802c103a6008100c1401130542c0150400580d034401411901221014a43c0b5801d4030100158030704440b11400520060b49488800c0c209401c0051340214100001512110a034449114140b0f4030036548201b04c01c0c03c2c0e80203180c000054040600015a641c04008241000b507000000e1900041e005005004852410a02c003800f100d80340c02680b4181400c003984d0401542c005440e407000c2c050b082000200051108000c1d150803402000c49240d000783c0d00003072004102000308005541e500c10090400181d6440c07081d222070039001115515803074800c0011070325241c0e2503001d00ca000c0c41020f00b10b200b0154800e94034140540c0030b078250761440d29448000c505490341c3d2460721054940f80042001c56040c42e078030440e03010000602050080c3c4c2c1e28504024240703042e1100f0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 27839097 1250 27837847 27837853
    0x30a050403150c170c040f030807050105060109061707030204050d05010b031216260c101410030b190c0f09050603061c0609080307110c040507020303150112020309 72
    0x10800c0c44203a080d100006884018140255002844020030345586400d04c0e05820110700c011a800b44d10342010b03a4080c0403014002801d09403681403043c8a908110b01c1101d4941c203100000b03140d544945050741c04c0b5500380d00d511400040e0b442c0a001c20f440e0042a43c000c056081c040040c940c0d0718054081005800b8100001e600c061060a260802c60910362030b8200d1035040200e152200814240d48414540000d42d06005080c4ca081e03105c00d90002c143d01d01c0580c040800c0b503603450003000c503070f1403910301812108000031781c41111950a2680d04031030341042d9148600040001c42d10700c03000035620008503004d8807071071404814028115235440102c440000c0904070110503450304030f1010000340404072440c1e4110325080d000a280001d035080003083c00301084204c801000400d400003031a090340308240c40c2c0c480c83d000300d004000003840c0c1010b07240c070311451522500034140351040b40d0080710140c1c017440c0703507035141c01340461504401f0b15030364100b0624040d00480960644003441c011190a009 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 27840347 1250 27839097 27839099
    0x90a1703091b010f0c0c05030a0605100f0e0403050306031c03050718050a0b090d06091a07110606010e030a020a0902090405060109080c151b01090201020f0109020a030b09030c030a0504 81
    0x44030302e04050118001c0011030022200301083c0c0e00130081c07245144031860034034040c240c2d51500c2400302c00b840e4441390f054854034074401c081011a400c024441c2c00b401c00100102179640c280f111043c401c910030058200d4903c400700300820702c03950040d80e0111000d001c031100708502580580d011260310703024200003a542c00c02c1c03040c0c442c0e0142034008002640030303109903140d0618001034511000c4e48500400000d001030b244503140c441c18070340c00904d6040300c0c040001100301d041c07006403442c0700c646400013000c02c0000507003201e010301684022030704541c00030b204558030a0010341e05840f402030f0140e450300c80c1d99605401079440c00041d0b40540822007016813501107540a20082d90006440c0b14140b0200c40000e00540d0790016049a42103002c40e0400318456a0030003102c205d105100c1d440c002c0400b003840e0742d0320009054200590042c400e908131080c0c4021107413a035003207a088100c000d6100310013140800c0801d54010910360400d1165081d6450302400d07900003840c0d5442100700501060001c28 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 27841597 1250 27840347 27840361
    0xb030411010f02010b0f10090803040311040b042c120a030e07150c2d060203070216050607030c1a04050d090905100e070c0210090e090c0607030503090a1703 69
    0x30301610240700b0b500007400000710200000301095000306040e0b0040c0c1400a143d000350f48100c8004009054103010390347c0c0c40391281040c038502c105103031250303004a0800381d50820b242002e118840816118161310042c5200c5000c0c0c2101642e1120b220b60a80d01c01c40b050082411010002848100c005450008030006144882030910005500030340d12807500e004603c1440f234100c4402809070f0b601407040c80700091034040340c0342e0508510314003504440c082c00c0364104210640d401517005022580894060781c03000d0070251032039500340c024540c001c0001d02070080082d02404080202134460540b44034203141044005048910480f800e0300c0b9a48482e4060b1541c5400481d140d02500303203444180500d01d000c1d1400b192400a42c0b2412101c21106000120300d0382c8607816080807280e000344800041c4100103001051040310740180c0301e000500c0c2c4041005540c0c0041e84000c5118090510750030801103440035203468000400100380307800340303082c802e00080f1603c0080c00b104800d251403d8481c18405d03 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 27842847 1250 27841597 27841607
    0x22d12160215040602030a18030516030b0a0c02101a0402030907150305040309060e010507020306010b030106111507210203010305101b08010b030a06030b0a0c0e090f06060d060b03041101 82
    0x103400b002209408000901850340d0200031100c441034181400649602c4424107009070008e5030b800039002e0702a018405008280300320061007142c0c007501520090f9200e0f004c0820860f0840007851016a00a405c3c26298207500d17082800c030a0450941c2008400001c40843d0980e4070407a681031985c3c200c9182804105140c0c4d001807050002c510301044a85000c1d80d0107020b01d41c1c0c50003100c00307009a51903030307000b117030311410407140c1d1503a0150030b554a40d690f9100201c1190000c1c042c0001003507440c840d10801a4001502c5404010103001c80005615000310540c0d66040005151003c01c0c031030741e0203503400300f03990008600075880b030740042036428079281c5190708881c15070740c0c1d0100c0341d0514a9600c40c4a036120001078190b0300ca400070a03941e5150705d80e48a005001a900c0202200d450340b0401c0358014403544554114200c44d01d98001503010b58040110307140c02100d0605400e8450400309509041000c00303440c0c2c1e60307035a0400060068881c11a141260030840e021550440c00c00001c0d6000d5071301c2 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 27844097 1250 27842847 27842869
    0xc1e03070608070504050d060f090b180a05101a06040b0403031b0203060601080603030c0a030c1e03080118020f0403150b032103060303070606060c03030c022d121602 73
    0x1450540b9541c02d00707940041036481540b080c140f040c448100880d0611203a640305d01f0350301e064070344100290b00c03040c5000c61550f0001c603181406c894000fa81402e0201000c10170780012035110024001d52040841401c0090020980c0c4404040e445050001d8980b2824010009013081201d1203881d1407440c81d0080c442c56228030141140e8403843c02c14030050b207000440c1074101200b42421942e5603910f0020030f1440c0243da240340b1f0304c0c2c46038201c034409140e08103840058441c0181010500c0d08100303010b01c15110801c0b04c0007800208400700402810000c020f8151444030041c9015140641400204140344c0260304155400c038042e00142c24a10103a02c0f1300d04080500ba030282a0304021410f2218983c180c41030036074a001d80020018509a40c01d00440c0c1c4160b91020f810841251552801004040103d5007200400e00d045000c820b8140001075109144640d000b0070524a00c00d120881c0280f061800125024420301000969000e220000380460a00740a61020075906a0040024000741 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 27845347 1250 27844097 27844109
    0x7080109030906050c0a061b0306050301020906070b070c0501050411040e070602060105060904020d0608030c2b12020d140601020d03060f060c0c03050609010903090501030c0f030e0c1e0307 83
    0x140c400c0303a100098000d94604200d600a003070080e00c604040d04a0750030031004540c000c000d6443c0410010b203941d444023800f100149980d03001c05c85191a1010f060803840703585401940414140145c000190182d440554804000c2c68180760123466580c64900391001500c086034594012017154105051a100c0c0805414801c1c0060800c1850900040d44440040c01090300072980000da1410707a840b0364048803c2802850010003445682c1e40305103450360024a52190223004010009030402071080d00c82c1a4102480d07006042c201c1e10940503034504003007030108000c0c03d40a100c0e605541c1000e108089040c032200b4103c80903071a0050009084c2003a1a0f9910185481c010091094580b040894001e0307c240b4140000601d8850604801d000304981c0300410f544a49010008840c4064118a0303a241c801c0e1140c92030303d81c8500043d0140c034494500c2c0400201ca4103544c8070650b11036000081d80710010340540d41044d90400120780c0380c03904520700381411024594828a1404e08000f05002003230 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 27846597 1250 27845347 27845351
    0x15020610030602310812040b090103020306120a140606010f090911090a060e0f040501050d0308060f10171803042903131406010b07200a0b0c070801 65
    0xa40111003010030691408003a201c5030b4013082000007054011071100d086490f001c07003200182c034040d04060021240b030180c82d465001d40e040c1c416132401307010140e078142c0308244007031403d00490100460094000401c0c10340e00440700041c2c0b014900d01404401e004d030b40600c00301461000913441aa00c1c1c0700c40900100d0400c070352b903021002c2040d48460a0410740f0103d04000c903142c001d800c1280d107280540b4041a07031000880c00001016600814445c00b207120030b845565400000c0d0040000b142d109208458110410500d0040000d10510fa2264070100080c580d2a40620103400300d0965100c11070b110010401e043d03c8000c440703008040360780d8070004030900349402d00d845641e0f80c0d499005903c01c0048180d1100d5400d10010a40d864070181100c41a0a00f912440d0815008090752040b050a442c01c071a080555410b1400105285040e034130188081c40c0303080e03a2a03072903480c5560020320310182d60307026090325000c950b04d80c9151b04c002c02024441c00e4403805680f5441f81080d4036607001c41400e81c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 27847847 1250 27846597 27846601
    0x902011e050d090c030b0106170a02091305130519060506060a0f050708040b0d061d090606060c0109020604080a020111071404050a02090a06020304080f03070804050f010203040e0907150206 83
    0x650107001c480303801104003004100c54100d8580140101d821750402403480c0c84031000400c005900940d50304031560f200c51501c3c156100c44102400301e11818003d960000c5080c1510914403400740c10140d00481941603e40000000707031900e500b4407880d24085600000441401c0081c0f00e010f00400d6088441190042d00e4007400c030401815008001184070203100021440f00b0506c81e980065400800c107a400081e5901500107110000f042036000302d40401c0e03ca041d900842c9880c51080303a00c11002c150082040d40c0707440301004200e0308030306c401d0350556484011260058540c2c03c00780c40200005801402004403c2c40050520f5580e01c440041d20f901040007000441060014030312980c8081e54005400d481d81c807031603c081d101c1c80154030b070000d220030800180d056002004004403607440c82600c1550586a40240c0ca0380300b40c030780180c22800c05006c00d1000340b900a82511030420705004036458640d81d04040500c4520448460350682c00860081000302d0301e000c40e40101026a2000d8400c2d8 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 27849097 1250 27847847 27847907
    0x1403030301030609030c06020c0105060a08010e0d110c03011401061b0f060f062309070306080309040f02040e0a060306050703060b0a080a0e0a0b1509040c060e030a02060d090201 78
    0xd000512015184039161030000701414041c41c00c0058880e00044199620740c070320318400f8007900d401d9610600031103854100040011040c49030001d0034612002030610b64095600071202d136200100101182d000b24044000582e509100703e45600d20f21644e491060740c9000e401801e5080c017000013041c0801d4001c0300741c0014800c07030f1012184680c00b480000703caa21519400000300802d4009951482c1540e50249036480c0420300300c0307103444085880c0c4480d9070710344404409450700744c40307074040582c803e0102c05403602d05900a80c0c2000c0e00c1c00c2d401403c00f95201c2ea0320042c184245c032040400c0d07641d42c030240103000b41405141c4e030100d0b003810280491854009122000d1051013020740c200514400811841d903c40d402048500000200310b41d81403035a4145024048416a01c100109202c0c80c13400703055090054059200b10380080901c3d10701071400d0410b84035652203140b83c0e40c0c076025400d803000050b82c401020340343e0303104070001c0040e1040c803034030000d0074460144100c840709082c001c022543c0c0c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 27850347 1250 27849097 27849103
    0x6160306030506070302030c090409050109050d0504080c061c05010e010303020c06040e0402011101111b070504110f0d020408061503010b01140904090503190203120f010302030a110d17090102071403 87
    0xa84c56107070050356070b501c80403484034038042c0600150313205080101d0202400b42c1500807400d010700030b00c203a8400740b400340303010703030300c0c1d114a2045c0c64043d045020114001d14010025012243d03506414000d9158000c2e94801295400d8015014026500c00140145a81044010b04541c0199140d5240506160304008003440042000303041000d140c2c5680743c41c6c102904594540140d50301078503114107200c074003443e0404540781d85404511405100180f94031301405443d0703400302001c200714a07000803d01001c5540c0d00c10b40345148425020400094911020050948200980010139a15003c3c0e01c00305801d5601504d0490b04111000001c41b44500480f422140e042000321400200e621403442d1090441c060b03011508044024928a41c2416401000411502c24980c0120001c0e039a030443c840c41c5640207000c00ba400d0303841046404005903100802610dc14001003065103803c6481c0e803804070442010010105100c40407a048429580400a44001d4000b1110b45001101e1140100396 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 27851597 1250 27850347 27850351
    0x40623040b0f070509030d020106052404091d0f07030320100209130f02030402090106080408090f010912060903030b06072001031d0115050d02010f0e0307050303070506160306030506 80
    0x212032042c0085a0002d00600480308800700203400d644822503800c2c0d01038002e20340c6101c1d2500030710350100c4100103c00724244a542c60b4403038020310342c03c05090076190030042001520842c1e8400c01000c4501c0c60304010080100c3c5481c0001c000d002e102d0562174018002092951100d82a504840d079250fa409404220a0104059914010b0300d0f11000400240b04844442043c050381d0700d01015654201020707002584035600995810009907030350b09045a90603001c0b24040c06420042c0f080880e00e140c09540100da0b07007414900b031030a407a120310185424070508070040381c42e1552000404105a0540103040094008440250416030641c80d48006800b621046c0c50306084a66010301d0307142e000b5880a900b814200e80392240381140345a1440c024540510b01c0490300c007000c1000640340c588032a00c1801c81e036040c0c0d15501501420780094134443d130f220107400c3c4d060003058030100d50f03603d042010300700150043c0014000c40c00c0018208402a43e02d85094040500f402000e0001c02e0001800e19 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 27852847 1250 27851597 27851611
    0xf08030702120c0c0f130c0507050c010509060d05100302040e060a06170706031104080105181225020103060503100b1e0105041e0506040e070206060108040b011205010207050105040623040b 83
    0xc05c80d5010b01000820380007115400c020300b285041a02d01c88103600c0303405050803622400c211021404141c0040d00c8600540c0d8440d5880710b0100701e00a401d0140d0707000b00e9001740382c80740401c10703082e201e0740040d00b96181d5000751342d101d50041080103000ba409014a0004149c5440b050748410f0038480280d8507031540d40550002c0c552510000161002c011040740c0c0180501c800030002c6041800305040b01e24507104000040e48504850752000d080f55904172403407042001002c51480003050f40711080e040385210180e0505588401c00661030701c0a2108a03140112208006080407840041140c80000003012141d03030003215511074401c1e40c1000c00c41d01070390b030303400c4070144006020900c80c5e4054a654000c1500208082400105980140049401003200390241e0310299a0300b00111440c95040354060001c0446800411413210100034407a03900740180c0001d49480a2070f2519400d45005440c00c071813883e0f5940214a031500582c4d0a06820068400e100c1f4040c20f05840d01601100301070800 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 27854097 1250 27852847 27852859
    0x70308180a052817030405030d0215070f020a020d0309080d0504050d03030b0312040f1406071511040914100e040c05090712050f01080105010b070209130c030f08030702120c0c 77
    0x7810354142d4803e01c0f0014400c19004003541000d86815588a4001c0d1103583e000e4414084a00c8883e4004509110075498035514403243c4d40da058802c5a03403920700303600c460070f6021f00c07100200541c0300c0406005146002ea01c1e540d41c000e180c007210901e0508a41c0483c03040100610081c41646d84511441c0c40c120781502d03010030b108942c540001e08012405201d81c907405000203002030580301c0420743c00d0880d001d801e458080300d41440b091058502c03c801c8001e10000042484480005c80c0740d218264594081c15401d041941f209070b00404c50389075402d03c0a905600c0810031080e2804e5056041c050b103c140c100c032020b400c00d541d90003104a5240140e911948001000920082c40748102c5000308098480030720042c05c10200390b0100400a014406895080000104801e40b0f6101190107499002e44004030356602c42d562401108000c031012126244041c4000010484c100c104070415070144064903500d042c60742c0c01038a070005000203202640805d008039408164003140e951070201c030035540 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 27855347 1250 27854097 27854149
    0x140405090f030304060e0601091404120216080a060606090608040605151807030c020d020318030703080a08010e010f05220b10021506030a0b0c0f070203070308180a05 73
    0x10440c00c007080d14141c04aa444040108000d02002c2e401a02d6803440520603a13820340d895140c2d1405840360708000c0d15422031154041400940200000400e0420701e00c1920408600e0351021003500c4203e6212040c2d60340401ea50b1030034000725109400090240c0e0a0043c6124a400c002502a160080014200655540025500a81410a000069200400d501e204554a11610b0540c08040e05c505000914140a104c40f090001850a48000c0c1640007942000421000110016510420320741c15000703c000003c0010b040c0c401406040c00d443e00c6d641d045605041c0c816407140e6050384460015012070404101988070031418010b19013910385250b941448800c10000030b400710030240303a088559251070401655001c00c140c0c101d8074030b80d4035101c466102c001c10182d60700e05e00800500350858500118503012078244c0108510449518101c1c189022500080d0a02205500c01d0b6940350001444500c07200c0d0032030744034541c1302d81141c80c1c0032203a007800c0c0826280d03c56040082c160101c4411 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 27856597 1250 27855347 27855361
    0x15060a050607031407030818010606080c090102120301080114070c0206040b0706090c08030936041b031109180d030f0e01020c03070605130506040f030c1a040c06030204140405 77
    0x60303c0d12280300c41c4055a6034121b1400800d40c1400f1542e80c2c066001291400c201d203001030041100301d4165076298841340d180c1d84e446100560184003500c0c154444c0f0100c955030b03010b0207409107000b080ca00000190f01c3c0300700010417001e51030041448040084244400e40141c4d501000d0b00c095506d55150035449161920b800d50081100d1785010b0a40e140e20080090203c40020041ca240042580c1601c0d60f00701407180f1000b90822410414501080c408030700c80381100811126078418010311440d030748012690000c006154072a0003d48540172901c101c44c4031030074a03c841a0700504100c080c2110300d0312110316542c55050041c0900c0415480751a600714400c0603422240441d0a8600210340d1044403400003075481d44a060119107007030a040002c1c40800ca2800c0c10700019401c2400b5022507959650381107401090124120f041c0000d5060f40710108640c130300004580800b036460315a003401d09040c080c2c00c228072503005a007098010401030045142c0c0c035403000c0c425901600c0104864403041e07 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 27857847 1250 27856597 27856607
    0x1080f040b180610030c121502090406150503010503070f0305100b011e0905030613050a0602070812040b07080604020a1d1203070503071e080418060509150315060a05060703 76
    0xa2001d242c83c072403070b0f080c8070744003448440e010b044912038982c40641035901e9025082c44146010b010f00100c807000c01800081c07110ba00203040c55580204000f40721619000e00d203108444003e181c4002800200c0140101d007420880e90010b81000b4400c0c1000600c0c55440320b0b560f40054465039a02c170b40700c44001d0b180e80d0082d03120f51420008260700c1b4801c0080300790001e01d2052188a6107119109e800d000ca5000d80d900240540710070741050150240c0601500e07104023a40c092103040b18080c4c0d0800000e0345560402042c217014620074145100d160a003410011305602001c2c002c14400c42c8100034141081d030700f1402510f103011000302c040340854203c02c00500c43e42600000d401507404001074170410020088020651a0b00c914418001c2540d143c040c0030b010441100024000e43c010441400a090461030619242480d55004500a0740340da01048103c0400d8440c07610710955000348001d2854248802295825051580380e21441d00600160040034203124490042c0800105081458860 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 27859097 1250 27857847 27857881
    0x180618090a090605060901050f010c0c030204050a060503060603011103180304030c03050304051002010209180c09030706030501080c040b0906010e0a1d070318020d030503090c0306090a020a0501080f040b 89
    0x3004a4a9031810348041c102030030080e4070403180303030340740c0b400044a038a003511119058070700141104030700361000c01c0156000405881c0c1940c08913a80300b00000183c0d03079030141034840c9030454008a0440d1412042c0b5142003800740031148664140304010400420302002d0341c0e0b001c840c0d00d07040d00a2540100c001c904510031508042c1c880000800c011003030040000080003100d6064800c2e5800c0c42d5150030407402c034011047c00d0341c0d000050518424003144001c60b080c0e0007000309422107290040f5680020301c1c10f040c1c0d174808008252503a00401584c0c03401c1c441d00c8200c9406407010f00c80a0080f40008540c00f100800007070501404094a0300c50340ca40e14200406000200c05000e80902c108010b0301c04580b0842d0b020f000039052034204407100c82131402c0206041e0707003c2c203078550030001541d040d9000c1d040103002588a00c102c440e2003d003581c04004160150300d03c230000c2c2c42030301c8082c018031107441100d4000d50706000d4008140030424420300b68035940190404814840c035294181443c24240b00 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 27860347 1250 27859097 27859099
    0x2060904090203060c090910080607081017011e020f030402060703031401060804021507050c0904060e010204030c1a03090613030e040c180806091f0b030a0c030605010902180618 78
    0x98600b0071045003140030060001d11011507071f0718115900c01c10400150b0701c181c081c00c110380e0031920100310084e000781c01c0180c0145082032003038078454a958004c1420b400c02c000c000c89980d1900b8144210007402c0080401024001205601d086158031152020380310240c4000e006200c00901c5e82c051622961040455a070a0401c00b00956510040205640c0d02a80c1c1640300e240103c2404158070008001c491048c2d500001816010301110204049a140100700391141c039280c1d075500307181e85002e20040024522641244082904040c0300168000c1c0402c00d1051801040003030002e4179400040d41030b4014450b00280d05000b03a5450304640040103500312030b4102c0d08124071215400e40041200b81d1422180c4210801180d64042c015070721a402c0c1e50503d5607402411514040520050741030200c101170540c00300c1d1403210300b00444e103803188a43c1c00384c50350031120300c1c06e00030010070b4081c0d40c0c01019132402c254205580043c802c140e074500341c0b065511842c0b0020700c0843c80c100e816014071310544 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 27861597 1250 27860347 27860353
    0x5030603030d1401030b160905040506010210060b1b0102070215070303020403050304031112061006110304080f0703020112020c070501030b18070f0908010e030301030b100e01080a1406040f02060904090203 90
    0x26540b0f14418000003800200c0390398000c4800203800560314400c4681c0c81d00360340c0d68607619500d0301c020b000052401030302544c11402541c1d150041080c4a0143e4801092020286555002c0342a01420864008141c001d1542d00400000c80580d55022500700d02e41280340d0155514201d518040c2d0091089910041c1039000100f4000140203428811020249003607504040750024448910b0311200b003220511a080b407991000e02c0014400d2641d0f007036101c403c204403403800c1d445003d001e151501070325102916501072072080c030031075074010340d440c4207001c521600707501704204407150b15103075a4940241c504159440198203500d42c1c421680003600b1520500b070f11650308241200510368100b0040c0c2d0004102801d200050168051151044000c0802d0207103055900310390f41c00017a050083c100b43d0310b2101410000c140310b854074005c68020b02c25880100480c02951504082150348408400c02070f400c03500070040491904001c45c40041c0e130480d046540c4814200015008025818002e50144 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 27862847 1250 27861597 27861611
    0x31e09050102040501090e040b15010c1506031109100905070306030b0405100e0307050a020904020613060c060c09080604060f021306120b03061b09030c0d080a0e01030216020105030603030d 83
    0x4032040d07000b041a124281ea499254640300c003000d4800c1007054074003d01070011000010901301c410b0101d070742d142105240802d2140000d407554800c500e543c0d41075148203903031200c1c10000c10480d190401283c440c1900d46003401d151500d2603040b03228544c85414580c0f0346500c00221414440da201d407015560101400c0c0990070310f4104150ba0b510680c1201c02018a0004d41d80d100d040300005a804540d0f2090080840807010350a011543d00040d1089801203c00e1003030326400714a030f403d0000a0702c125078030684811128200042521030f0f00001c0400d12062201c14490a140414240d0703115030000000b00b40c071030744941c90798005d11805201c00c00125140d030300400c03070542c040b048005d0800410740c00d0041440781420140c8508090b150641c080303480166a00311a20504060175400d4002015038103940c01c210082014502080400c483c00c0e80300058125400e504118444444d54080c41d0850410307091840388036110008031030183c180180400040c2c0b080d40c00300100d9403640c3c0400000e01402c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 27864097 1250 27862847 27862853
    0x1030501020a09061b030c0c0918050c010c030807051b010c09050a08030306010504060804050c0301060b1207020619110405030a050c0102070e1b030a0905160503010b03060115031e09 80
    0x2d4120700d401000150604400041d02c0d0700c030329014031180305811081980305845a8050b6014040048111079400c0502800904200c1c40d00c035022500c1907041003111403168504d800c6040041061705281445908100e04e0042548004415400f20a80c200766680d89014450f0341c1c000140b03090201007039800d02280b51340450348031201008071107054035010805038440c00d0207601d9000440c0d00303e002600c10300c41042110305c5041e246800500400c140c4407841d014070027003829209240c010081c4ac44c800500354040028008015500203168400780001e8200200c40700d540c000b0306400c00c1c1c1d18a071500b60b070003612104142160020500141210452179413403130110f4480403010103080c094094000d000815604018095200d4001c1100c440803021415081c00055080601190311007540d41c1900c2c3c0004504008214003e681c0c107101c03180301441c10040509642080302e800303000350020001048980c243d16228004d0544a040204905d85900a0340340d040d01024002c20b001420082c080303040c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 27865347 1250 27864097 27864101
    0x6090c090801020309102d06030b131a07020309030115051f0504090c03060815010302040e010908030c03180601030303140c090612040c1208040f05030d081f030b01030501 75
    0x40400989890340d01a40d607800542c200d000403031300d034009500180c90b81d585540d0f041c0e016a2055500c00745194518480185a9415030700c030117045003000b0b6690000b4028048048001540301e00f8210702c80e030170980c0650f903210920b00d10382e04002000e00c5510108110600038000e0b82c8002c04054002c01801e017060441c2051110b044c8a6030f40151140c07008a2a6103600f50f41404410f5407644519181c5803510002c4d070000c007003103a010070415990390008282e211051004c804a1440c18000b65200e50540c0104002c4850110a03861981c0c54031041500242c0080103599200e48000380d540e40b40d680320609081ca0414014001d505401240008000c01d5003590014814a5240803030121941d242441c0e101c080c0709607403c843e44201c0c14040d801c1c08148030070015034440e12841d459254560b42d603440c960100d80302c4204881e8410702141c08c0c40618500d959981c0100720486c024a10102c00f0752014080040260000c3d07140168040c61104150120301c6070710085501946011556035030b4184140 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 27866597 1250 27865347 27865361
    0xd0f1407111203041a03060406030b090c010e030705100c02030c030303010605031509040c0302101103030c07200a0302091003050618010b0a080601061803050d0f020601170a12030b03010609 83
    0x8854000303281c81c0c0c0080b050000c00d44042d00c0d40c0507103098581c0c030100300d0400142c000400469015840e00004400a11301081481c0100c040304000c204200070040054401000c42d4682c6003ea80210300c00c000c156211a040c0400704543d04110b100e881103070010034100386014601c0c54051100000020785c440d4424021482090340b9503400c5c500203c542c0c10894016010384001d0510160b542c4280054075050b400e402008915003804442d40d010b5030302003403c5400449003106461000b0840205100f402d8403802c61088070304600c0c0c01000c140b440003d10307212003804064002d66190300011695000303449071401442d0401d088505514220315a58181c41c201210b0b1001c0303501301490080f207801c103040383c0029941c1000141c80103030700b44141241d5000401d404241101d010101c004042001481108401443d07036450503031120716100b01a1409070b041e4080c609007094040c00ca01101c201040c03800c03045620007541010220743c400100c0190950b105d101c0e9040d46025800a00701443e43e020503 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 27867847 1250 27866597 27866599
    0x30b040309090b010f08090102120103050c03070f05030a030f11071202040c0804020d0204020c0712060212010608090307080304060605090a0c110a050a0f031704052d0d0f140711 78
    0xd64a03502c401c0c81c1000d80c1d950700e588901117401c450034118480e0007800b07020341c0801880001400e101c842c900c070344040c15080c2c0c001e65907600300c00c0c0200c005080034003010020f484e03d07000765800c1c28544000f103540c1d0a203064000d8100000f18014002c02c522070030340070700f40c000d403c802c4030750740e94544980031808042c20404a100b24035150010403101d02444d05c640c4200c0c0c0003094000032420300d4003030201070341c803904000d1100c0c02140d1000c43d0f00d078001c04144202c0d6020740001610f49101043c0c01c2121401a00068240407500c81008414200001201c403c5035004210329142d84541c50404040c085d00e8100640c1b018181e410401009503076444411740e04000e1391100c1c560b196855990380c58075a50000500203800c5504a0b03008142a801540c00301486464443ca400381c0d682101203801d1030a5804542030781150007030251100c45203007205070100c3c0c1100171080d860100106c9981c2c03820300d580711000780180020f60890f854000c0d820031100640280300b19540d4407140c81c20120700361680b0509 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 27869097 1250 27867847 27867857
    0xb0d0f020406080d120f0b010807140c03040306020309010e0604051c050405060c0a0c06050a230903010516020f030301061d040b0a12060f0e0309060f0d09030c120309030e0d05010603080301030b0403 87
    0x120886d5405008290ba0f102068440c0340441d00c408404070b0740300c4403107595101049820481e103083d00d00200001c0000318018040141c490034900f0405003582e400714400034150780142d081c040820b102180c401401300340300c1c0000030514495002510036002d99400346610840204803010319260201d0f080140700c0c413504582105a480c2e140940c0c0b580205400c4200190b6408418401b000b01c4186a08200030012603e41c1000fa101c000242034030012102e00c1100c928080d11780440c5601004144500f0841d00c000e10b0030756061201c001c01c1803040540d44a441d0101c0b48880c2001e854a511802169801400050f142510f82810803e41010900c1c11684c542c503207102c5106070066445046100d6541c500654a4103580c84100710040e00300a40c441041d41d010083c0d07170302000b0710748640ca080b9071290b158013207103002c00d051820b00104c54440700402c1c50300f00303112180041d90160485c44242400c40d080082090241000e500400c0f1b181c02c01010503000200210600c003850314640c0c42207100b0750356 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 27870347 1250 27869097 27869111
    0x90b0403030f0608030405040e0106030b040c080f0a02060307030203042306160311221e06090603090506040209190203150301060501020a0f080702041e060e0702010b0d0f020406080d12 81
    0x203010102c40c100e1145413101c2c2c0085c0014030480c64580c03c5000c4054403c0004103110b9202e8079200740204003078078110396102001008110568040c0030036012184020090701c00c0d0b480e0ba401040040c80300138110000c240d4004006000c00480041d5440c1d190b004403520b00880500e4002d9580d0750f40c06817005200204410481043c180c464000e81682203443c100f0b4605110441c405150510080e421040c4c624460030303804070341801e0f860300304101800c030b614445000d2841c04501501100554020f04101818491b8442c0450400104150001c0d03054402c442a41d503a403c0900e00807180c0c0c00e440d00e1a900020501c0301c503040280b41d00f00d00c004202d001b00001c1d9911001a030352143d810000500d0152405605400f042410001e408481e0000d01b001c103208100200e00c4020340300e00e0311030103d0f103541c800d0240403002240c51a20b6100fa100e0000308011014807000409152060310028461030348605080215159a04641c0091040714112403244e4150700001c2c0400c80b8110045418515000e0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 27871597 1250 27870347 27870371
    0x5010509010902010504052e03020a03050a060605030612030c0d020102030103020a0503060105030a12020a06060801090506010609140d05030706150e0c040e070806150f090901050a031109070c06090b040303 90
    0x100300b004442c1d0503124030345050b1800003400003440342000c0b92290381d07070184200034040c5503a441400349034000740d41c01680c540d00023102508680002d456080002c2c5007550a001094000c0100e1b0380000d411549274141e50041010fa528510800e81c1044841c000d0748241401b060b0150040c6050701d108440e1070103e56159010b00d40d59020920a169040d032000000d0070103c3d48200c01283e1050b0300c2d106450034082191606c0056884a0348aa081c580d911545081400300c148203050250540d864103c61107480c052140c40e1110307010b2180c611030341d012030794442000400c004031000154040c4080c8004403480381300c0002c10580c1e10503a40c1d18440040001c5415961600312429106850040340f0329031613004044507a4031000781825007207091503041c00c404d407000c94090010242489002980d1383c1c10a003c3c00010001a8001c0c0d008884e0f00509200103260341c060301c40c0c0c024042e5548000d568409200300c9500049140c064541440e148140c01400066150b01e07100d0744c001d840900c05021106 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 27872847 1250 27871597 27871601
    0x6030506010e160c03090e10060f0201090206090609040b0a0f030c0605030702031902030d0e010f0c020c100302070219030b0a0b030a030906050d090c08030304020307060f080a020f190201090501050901 88
    0x54406082000c1d0b494010710141c020184c07440c056003c0d00c4d0500480303886845da5011403070f054070707441d0300d100d00f500003000709582c8821a0546506148000d10a400042c1d02046c908c1c007441100d01d210f01d0010540c105031b6103c0c1e603c0800307041002005176189903520886031107501020701050ba600d0f92069000b1481e40c0c013610803a070180b591075004500e80a040c60616400d201c40280b8101103010821802e5140e20540c001c0010790000c10780001449140c0700e03c094100c1e4140f807101d60540d080702c04440b025507a40424085910725600780503a071034084d80300082a0740c1505201c1c7c1c40d1003420450200901032442079030391003039042c2d000800203003112004040e0b1701d0701480f0008000070001c990511155114401a1140381c01200c4040b90703a10495503140c08000c266048845554404010003040d8601004180010122402c10301030903012068020a00c0c500200001209078000038030b0044c1d03030500c60888078000046040c8540702d040703603840203018003001c0000b42c58560820703006c40c00200040c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 27874097 1250 27872847 27872851
    0x303010314011410030206030402040207120e012601091d0f0601050108010f030f03111623061c09021f0314060901060906030f020904050c07031805060403061505060d06030506010e 79
    0x84c43e4a031658035541c204035a41c2e03c000c1003243c001e502440788000046030b0701207480f411a080c0c0c44071407508040390001005480229244512100d4201c0b1544041c80c81e13164203410b4466403400428189a003603108101c4441e120082c1c030462040083c40c1e58070590104d00141038810980e40c000190b6a504164000c0d91090b0101501220080e040c280000380078040e40000160440c0c02d403801c8e0a840075042d40d60241e1503200a8002481001e05070300d0552038400480d03c5002114564140110041c1d06090380700504000c8100ea50354141880c02e41d82c40c9e0907280c0c1d03e2605102d02c4601e0001114008000d80480c10500301181c0b00030000c540c0d1440d1200486050394055a0344120080ca4080110702070101a1000c1d04220382c00c05c000e24280d2078900500703104009601c8071030381d40d0400d8039004000f0903400414240c50a09043c060004c2d503500d804860417250080030108890132201d040754160300442d07000aa01c80c500040018030320407035800c450304a0b03000e48140d90b40c583c1d89030324491080d542 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 27875347 1250 27874097 27874111
    0x3070b040504051e0903040302040e160608041110030204180b01050a0f030908070303270c0510050d0c02010501090f02030402030a1e0f06050a05090c09010b030a0e03030103140114 79
    0x4140414006402e1550206500042800800700c554903140140d014402050ba805601504002018415410f090158405003882400180528944103c4403480207515000f1390040042c01c6002c00e0a0001581844072494030040210003114001040940254400d00c52784196104c400c004848400080c8560710364000c047c1c40392460301034403030ba08840e0b00d4040030100c018190340c1d14031440490070220182c240705200e030b00c00103104c02d0300c1700385202541708421400c05005900300309040002d0028030300d44115407054452910040c14032809451034021515034800c0340b80b83c03070790724030031254150041030490707002e41d0080003450311044044059110444001e90942c1c050003000300090640c0c12580f04240f4441108490301034180e0f250054510581c0c425a9000c0d159024402038129505c64250800c0e01e580c003e000b41a8640c022030b10034041481104030076000440000c0080003c0c1d0070000042441f14252640d940c2c481c0342400e04085901688400d03980703040c000d40d50840350940b80e01d000d070f62 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 27876597 1250 27875347 27875369
    0x1107060e031c0518070b0a03150b0a0305130206070506040308070f081605070507060302070204050a0207200102010608012f030906010b070f2f0303030114010804061503080301090501050307 83
    0x10500b911503001d0301000e01072a10000700058441d81d07502d800c1c48114043d100c05851295284100c80c001403e0381d950021541b5020080f40040181c019010211041e030401400c011801d5583e100b000f00400701c2c0d17940086d421904c00180d290800c20007141c840d01c13841c40382d00c901a0720b40700c2a0302100c0c990510111500400c4141d80810398840178206a81840d05003450014a001c0880e0b91b07803030605040d41d0005020a4022644908610300b601440340d00001c0d100d02103060034419200d8149090300b2403c19848044545c0100c6041d910039005040546480802401000b0a0550901007103030200304813448190704046480c2d01040c0041228052102000141550707400d245032491580e0054502719184070129240782e0009001802c031040c2d542c01c42c10407140b8407100282402c1c41041c40f00c101c41c880d420810050007151003004020f1407801302032a002013a07942e203140c140c0003440c0408040601c1014948000108544000118140c0d14540070a020a0344c0e11803e041d40e4110034000c50385000 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 27877703 1106 27876597 27876637
    0x6090706030b180703060305030c0304050117151005040906060e03010b04050601210212040f0309060801030201050d0207150608010e0f06040b040f151107060e03 71
    0x40c8034142488240c000320300040c090800c003030b00d005407055410042810301e482a4069000340d0307071000c120b076650481c240032940d881e089449041e0000d001901064813401480700024000c0e604100c20a80c403200e00810800003110208248041141c140000154032009001d42c100518040c3c6440821608841c1858252031445526500890401050100c1a61f028118210038a5109c4541210070409010b02001e03102d002c907504c00c0b1310702900c20301040c0805030384140d8001d440fa0701c0745180c2640d50001501c04510911003c1d003ca04244007810078103a0750b40003054244d1290450f1026000385090500450300150864035481e0b6482685403100c1404004c02c1da200000360f4000c02c000e00d010360f21088010402031000707110040b40c4030403004220709035400011640300b540f4180406008019840d000d074014900540e451818528540844d04011048402c800c003800c0c5290500 = true := by decide +kernel

theorem cover : BRFrame.Cov 27697847 27877703 := by
  have h0 := BRFrame.cov_init 27697847
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27697847 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27697847 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27697847 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27697847 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27697847 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27697847 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27697847 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27697847 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27697847 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27697847 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27697847 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27697847 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27697847 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27697847 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27697847 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27697847 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27697847 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27697847 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27697847 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27697847 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27697847 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27697847 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27697847 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27697847 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27697847 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27697847 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27697847 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27697847 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27697847 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27697847 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27697847 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27697847 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27697847 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27697847 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27697847 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27697847 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27697847 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27697847 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27697847 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27697847 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27697847 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27697847 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27697847 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27697847 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27697847 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27697847 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27697847 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27697847 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27697847 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27697847 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27697847 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27697847 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27697847 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27697847 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27697847 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27697847 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27697847 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27697847 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27697847 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27697847 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27697847 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27697847 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27697847 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27697847 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27697847 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27697847 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27697847 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27697847 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27697847 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27697847 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27697847 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27697847 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27697847 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27697847 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27697847 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27697847 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27697847 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27697847 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27697847 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27697847 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27697847 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27697847 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27697847 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27697847 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27697847 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27697847 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27697847 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27697847 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27697847 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27697847 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27697847 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27697847 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27697847 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27697847 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27697847 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27697847 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27697847 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27697847 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27697847 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27697847 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27697847 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27697847 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27697847 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27697847 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27697847 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27697847 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27697847 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27697847 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27697847 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27697847 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27697847 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27697847 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27697847 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27697847 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27697847 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27697847 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27697847 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27697847 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27697847 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27697847 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27697847 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27697847 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27697847 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27697847 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27697847 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27697847 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27697847 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27697847 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27697847 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27697847 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27697847 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27697847 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27697847 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27697847 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27697847 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27697847 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27697847 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27697847 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27697847 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27697847 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27697847 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27697847 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27697847 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27697847 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 27697847 ≤ n) (h2 : n < 27877703) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
