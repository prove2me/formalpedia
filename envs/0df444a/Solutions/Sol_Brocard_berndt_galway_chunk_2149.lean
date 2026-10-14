-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2149
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:48:01.013525+00:00
-- url     : https://prove2.me/submissions/e17b5a72-79c8-4916-a615-050613f085fa

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 386330935 ≤ n < 386510791 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 386332185 1250 386330935 386330947
    0x20a05060414101d1213060e04090204020408060f0601170c0702010c122006010509041b0902030103080307110c01120f0f09060b0102071d0402060306010c05011d01060501090f090c110111 82
    0x2050a01a00c001130045ca480140030390040c16043c0386403102100c0007410802130002904d0045405004030395000303940113102042c0000c0604012609501c81e00070101c681203c4c0d5100001581d05080321010201d8507404280083d102e0140b18005200e414014145003110350100d50b01c4240e80920400103000041c51500175171200312000d183c00429402c940302030801d96050a01043c0780c41c2c4020005002507060025181030134046090604c0505a0707104150754030368403400c0c9000e05a01c1500e11030300080044420910422000c50b940c180c8502c16551840c510074040b41e56000b40450b19019066280c1d6030f10140480301187c4100380300c2c03520a03100400c100103150006418842940c0c80b0440c07600d120360001901c5c9945488443d07005c0e40c100c61040e140c1d120b0348012260303e5000c440082c0b6542c6851440c00418101e26002e0764030403215002404031584031401100c4003161031207014494a1031000034031114010703030815411403203149480940351805002840c2035800d01008161006000520 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 386333435 1250 386332185 386332241
    0xf0e0a0816060201020301210f0506070302180f03060406110909090a2a0b0a03021606090b1302130c030b100906030501050f030a030e0103060f09020309010606020a0506041410 77
    0x100c44002c04480c00214110740c9441040e01e0002c0300f40c1c86010442505c0802c01e01000384880c1c10146458002003251a1480c01c40009402175001340d4160058402c0412826414074000b1012800034130b002d40600b0403920380344da40001500c00c0130001800c50000340b0882d001601c0ea0001c4030300c50400c2d04014420580c071401c15101004240c140002082074190410103040541100da130201d0b1141118142c3c1c6e060129401c1380203001c0c0d40710704106000d000c0a91f5003407100a4200c410349a00540362a02d0070384500006501407a805480250884280080e404103150300e940b1860f17003c00c0074100440d000c0541c000080f9011644140d00011609200c01480380650600c90107002d04015034940071400c1c0040b00003aa80c0c1c189100c000d0400034071508416003a480f0b900b09400501d000300b80c035001162220305c004061340013121440340b690310704140016140d100145909d121500140030f07084070340311501d500725401c11341c000b4043c1320b2040515101d0780015920529600f20002e00c00001e2250040035 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 386334685 1250 386333435 386333473
    0x12040204150303080f0405031b0303071206140f191806060c0c0506030a1b0e030f0d080c0304030323060102010507020705100f0201150e070f170402010f0e0a08 70
    0x104003091001c00d414800241c004004e00d400409600c2c0c08074041c2e50303510b002881e40c410703c90500c0303004c100e00c4c00d082040303070001000d903014a0ac01d4a903800c951890419100441d1814460020b05d820b41d01c00822080c10f0160042d91010350140010a18030609000380c1d401540c3c0b81c3c041c0c0e43c0f0442c05001d40c448025180b00c1c0c100508507a1a00c90046441501c81070346003c454001d151042d00000046141600a0707071000b40001048054210000c4a000d00506140c140c050100d00a0055401004810300045000c00d5800319685403001141c459146881c000d1b01300500803006e2580e0380c210a075003d0b10400c00008410701c00828440035140040c002401e6070005002001594480c10302804569583d00303170404403031010310300301011520100080b405021801c0382c60005400005021800b51002c0e8600b42c0f14144c0d80d120200803000d128812a18034030b904074906130450201007c9001988111034a402d105003034a0441c0761510300c0d1000906007040355009002c07035441894061085580c401e = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 386335935 1250 386334685 386334701
    0xb040212132010030c02010b090709091a2112040906050a080f0606010315050d0f110105070302031602210709050610020709111308010204061b050d080a06080312040204 74
    0x300d00400400d045012400750907400010304241900c0305c50804d64540700f5440000c0704800141440c030f42c0d040007500a000f0b00b003c0d0040c0d100e4203041104104044d180c001c4c07500402040580110420307910640b80c01d1102d138400c10300e00380740c2c0a00c0f013132070b442d0040c42000703000034240540b000240945404200311441241d5802200584c00c682060f9144807804204194025420b00340800d05201d00c2e0401c2c40340007425005107500410425000b8284015142e210300c0c0103105400071002001118010344e240e008841004005034001c200c00c541003000c4c100c24010b010b1020780041c41c103c0e4a0704040d840c4003005480201c00740c2c40718034204100072040c0240d40d08180f003501e00d50610010450001e4440041c0c3c05503015480c1c90358a09502095084201ea1219164007038428034140c4480c0c10721b0103588240328020000d9403800c0194006141c00300142583e0b41c0c044002d04000d0103000c02903400210007010f207007040e0754038180002d200509100605621440e100c043d0032902c0d10f441048100d0b90f80b0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 386337185 1250 386335935 386335973
    0x12090c1003050c0304060b030f0709050a0b0d021c051903020102070c06030513020603040218160201050f07120f0902060412020108130c05090903190305190c050d0b04021213 76
    0x400140b2003c8004007003200d400c1070304490040f409905003000b00c0e1501e43d8290756800c2901c50800b0008035052254806400780c0610403050200500b51810000640361300038000c2e600c070220381c407070a40e064400340d9480e60951049007540c41364941078480c0001c2c8c1c000d46d10180d0150b500014240c042040c5a02442c018055a0604002030b0401c241c4035242c410b82040000c3c0a641c001011806541d40c404000840b03018104038280c551500203030215440440401010142d820702011441c4803240c901210b1140f2210780e100c0c0e813481460443c2c3c8024025040d000f69413a55244000c00140e21000010000b07801c9076100e0300c008882903c0010080e17400209180d51589130500e11074001108413038600b04484040305c0d0766107140c0b94400301e582144540c040e110000043d51846114290701904028450090384030410051410b14030898241d4200c80c41400000e6000c10002c1400ca400f644503c01c003004c043c10060518000c0303010110303100c4042e5104002c030340001c0a101c04110080b285c80c2015042 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 386338435 1250 386337185 386337191
    0x90f0106050a030209031c0c0c0603090819110706020607020f0111040303081f03060c14090906100c0b010b030603010b0303130918050a0320010c0212030c12090c1003 73
    0x1410000400e2805011120b108140e00080c0d0148569400c1002011030707001c0240800f4142c1409101406d0340140c020704407080700c02e4840002e1224000d101c0d11200f07070b40140500c0d06d00381400042180088910081000780b00752003244820000c0100300080140956030000d00c044c0c04c01ba10007a24110b60048100d105038101a08080e00310188025038041320b5050030015a1515202c074001d00214000600c12904c205000002042c040141c002d03108009003904d92101000c1c145880040c0e038854400d17003540000074180400d80031700b8411025100404103103010a404d0741c0981c1d80c10a1601e0a0f88034400c4440d0202c1070181c1d5140a03c2004c2c0d440c40110019440c0090304d03009110991401d01c5903207078803a5948501c5803000440d0b503000d68490340c044159440100f680c0307805080040c4000b41031800410720000304041810501c41d80d0181078484e0010710302c0f84070f0340710440030755400144040c03602c03c1d050045800d1445000708450088405e80d014014412114043c44070006142403070b1420141 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 386339685 1250 386338435 386338439
    0x318020604051005040e040609060b0a24030e15091501180506151b15090c09060619081815010924090f0b040e030f0c0a0c06080105090f01 61
    0x18540303040301c0440d04141c0380c029140010003000d4540d405070750711414695156804200c00c01c07040f80d1003d8005c6104610400c0b00e070b40e51070140040904a0300a024401c02c248a9420551003c14200f0348000113914012810a1540000b0750400441d0881007500c0181c1c1c0050002c4198184a0050001040d0021107120361400440030381d80f41403080b0954409a40d08007203001900c0c0e1001030324401e03242c100c80700d03926160680485400c3c0014080b608981c000e050807400790181401b060f502440c00302000303150080c044001c0101160025240c558040800c109030182e1141005030788071100c0b80d503106c01c030251420701000d01d2038060302e0f0404015604041662518901064841419100e00c100c0001d11404032000c1d820740081904401c045200b2540300000c1c40c0d24068000103039040500340e05000f0244000140816a46038014603001c54005103c602a43c40180003e041001503140413034031a50041d842ea489180c4031604400c0c005821100144200c1c2010300c001c03900700c41440450100c642c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 386340935 1250 386339685 386339689
    0xe0303070f030b09011d06040b0f040b010e040608070e0a0506011d031e100e0111090114040f0801060e0f06210102040807080a03030b03060907060e040e010c0f031802 73
    0x844020308410910403040c0e488044503110340d010025812000c0c0c561459540c54600711a14070841e0408103404200c4400000c49030b05040c040e14181e480c0240c10030b8a0299180c0400028254010b5000c2c108201e200e506c0800d5a50380c01500c00405901d40508451801c0c100120034a80d0000d10003c64203040001f40030159a00c004400e645446074100d02441c000c071040001e04001d0085205540da0040c10700e407611502d00412040c007105c0b48090104001e80120020500741c60311b03070600414845041c402d2400340e50040445070300250451100b01c0c03a15407500c6120300048800d03000f00340702c1d039501e0b40180f01c154010180c2d141c000c800105c09054900d0680005a00190000c1141100804810f0484010f00c2c09405440203000fa45007907030140d03921039160680c1e61040300340c1036000074100343d2640d905007400319440e4011203c44001e03203511414200180c90000c0d06002058019644030340c828600034084c0720f14140544aa61640714180c0003a2006060b01c2004044008d07110700750320008010703 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 386342185 1250 386340935 386340937
    0x50906030a0b0a050c040e0a0506030f0c01080c090a080f0c0405011706060d0501020c0a1b0f1a070201020c0405010b0a09050406060e0910080a030f110c0108180f16090f0e03 76
    0x1c8900c800c0049095a41d565179040a4041d43e03000e21032584158060260100c9180c10507032054034281c04580317400300042900c643d074a9405109a000c2800b03280495445c408200c01000784010251011511668a142e140c0c542000f10307031150302541100e0301034240b914040c01410300608920691812200c11030408503103441e80600f40c1c0703216034607441c41e00013008000e40540f4400403214043d83c5600a0500781455046001d282e002e8040449800200307a11243d50002d40958030321070300c441d41c422450b00240c400d80c3d0195405034190300c660406205142e40d0350050a0103030201c80c0d0f61544410002001400ea420325400c4a40310300d081c04400e0102c0d69200b10310043c02c80040b25a0440b81d1038102400450a540d40c2245032940610400f440616802849041c181121a80e61460300c52080440303d0700c41120402d401e000840103400300322025000100c1103aa000080306494145403158442854010358030040d014101d0584030400070038410340310b61054045c1c2418107200e0115004551610303 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 386343435 1250 386342185 386342191
    0xc0301110a0c03020703020402160c05120d080c0d0c05040501020610140607020d050703030906080c040e0412030e070608010501021204081203090f0709020d1b09180222050906030a0b 80
    0x800c481c039860ba206140c800c12010b001503030045d0007150303105101c07801000d0030521000f00b50340b80a02080300107503a04015000c69902d04030389010304a0000842d60031600110090800c450889050194548911862107643da00030010745852341c0d50ba01d070000190600c0e90003001120f00107030b50341041050f0403c0b05c41000e4081012243c00ea981e134800d05c0041d221660401c40a092407003a6038010080642010b005e80a594450300e41920541e600d0f448110380780301c1c0703002d2244c0200d001750104002440b00f41650701d8035461810089044829440545c0c50130300c655205400050001e001040103580610440c6609011081c04914041c01c3c60f9003070365541d0000c41c0d140c54080d0f001000030801b060a0251a00400840d41903402c880d86d5440320601a4004001038140c1511f400c2e0b5a0020030301400c8045444040798580300005450b10a51111540350010806001d9808004010280901b400c543d88581d582141d4045914142814030408800082040d4000c0e03012494610105c1d800d03518103030b8 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 386344685 1250 386343435 386343437
    0x1e051e100f0216080303010602060609090c010318020d0f020f01050c1b030102040302130614060903150a06050d0b0a05150a0b0a12020a17090c15030a0905030a08090c0301110a 77
    0x40c5040782240c100e28046000e1030525460070308003070100311000040002c6040b40c0b05542220000e45480b0100041c02c041525840e14942c084401c0d5050795000e074001c80c00c5826280400b8103034580580101b01c46454028080715503515182003401180380c6050702d900b40c10070a01c0c0003802c0a1042003d541d40b01001c1c41203544041300b40f11050b520b07982c00d4048502541c0c3c050402001c580801e038804000d00154003d0821802000e88011164200340307080e14a6624000c00603c01c0c240c8018042c0c0e8410005000740a0040d101c44011400d80c5070b40710100322040c40b40100b07a129141c50010305040301c80261010307074004052082002c00382d99150141c0207548031884c40a5466407419800d83c0c00d40c1c0c558190086447c000706600000c42e4000404444900d00e2070130a52103036450b14a002c3d1280c0c02405050f0b40718201d98013400c110380b01c250185520800b401c000080c00401500c440f4a580c102040c10070000301e600c1c0400040e69414841c003010f0a40541c001c2c40142c2c8403132400c03003140c0101e180e004 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 386345935 1250 386344685 386344697
    0xc0c030b092b180b1902060105010203131509081e1501030f020108070c171903060305030406030209060c1b0a0e0c0909281505010203030613090c1e051e10 68
    0x30381140c1561800d00400110042585e12080c4a10304140409420141c80160195200018040d40044110780b5200303808000003c01c00d0038211082c60403002c000d03020003040249a4040f0302d01e41c0400800c01c100061721041481e094000790003d1034030300b0140c1c6612000b11601700401c002034204501400300c690900b00030045d40d444c440d0849034010448000f600c20000d00510480e442d14480043c00c2000b100c0300100c40100480d00c0503410b80d422440000d0890340200010014a44a94080c00580c2d000514441c40c188191783e005203000701482642d0540016240c0880d201d1034100760f131400078a00e4141c244861b2900c0c4045441038081e0204040c01900c060002402035840001140d8142403111108840e0240c001c034044011b210b100001e281b21441c24038049282d600010035244180301c0141030b00b268080050040c03016100222040720300920f6070001103070102c1900e03000000700c040d684403401c0c8240780ca4100a80c40c090403105811a80c40900d440d12251a855000c0c103030515181015 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 386347185 1250 386345935 386345957
    0x90306150303190804120314060f030c03120d05131110091e0305070f0f0311030f03070b0a050c07020d121b05030403051c1209030c0c030b092b 63
    0x1c40d0841c031518943c05071200303148034589140c64002c1078041c000e42c05124a60108081404240c1c101c0c0e0000c0c50111442c40c01c0300018025142002900005010180c1500c00c2103d201011034a020141801c91076004000700e41c005031000c00c1d02c9000c3d8010500390301007462240c0c545410412017449050039004140000e40e03e0821400760203404001c0c42c08884003295004181c8449040e5482da00003110103000705c81c0002100300b02c688040d02600d1801112418180c51555000040c0c40c01442007900b500814403201803000041c40640b84050290200080d80e10f0103520310300489200505118a40c82c0520450000d43c40328080071340c1c0070780c1c4a0310000701e03441c41440994201020b440c00d04401c030000e2540d5003c100c00440648201c0380320743d0441d0380001d0704901c21200c44110105c19000111804924510581d07141c0081032000d02a01f4410b607040415202e00103094019001580c00f50204014818210000c104201c00096000041d8030741c0003900f00840c0c0540c0c0d000341401c0811140c4045 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 386348435 1250 386347185 386347189
    0x70e15180a2406020a1a010807061107090606020307051501140f18190e0604080a210c09240801090c030219090f0e1003150e100f0b040209030615 64
    0x1107800708480504111003a03983c810003035031020041c1c0211440100c0414174040390381121100c5d4180e407404005420801d0070040c0c1225460307000307050401c0601c203001000034140068400c482c05443c0c103601035070741c07600281880343c82c0642001d0700741c4184c5035180c010400089c40c0b0840e900010000c584124245c201580000c10818461f20f400348404100300600c8555540003032043c454402c1c0b40420320209481009090301c6d40b900702d42c007811000007004040b084d54801e84442a514440c2c00d400e2a503030039450100c5045409800d124400f20380111424000b0012905864240500708040c409482c40f0700381008100303c04c10b125040815860b0b0343c1900030140644c054889040c000c0701d949020102645000380240c2c01441802003c10f9031840105038030074558290b911410b15442025941e07407a42ea43c00208495901041207225901c0c4000e0000090621442024034030400001c2603210034000c41c0401c03a01c082c3d010314481c40c07041001c25040c1e100030944560000c64180c01c0c0c0040c61034100 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 386349685 1250 386348435 386348471
    0xb150418050403180b0d0b06040b070204050405030d0905030a1e141c02030c070b070206092d0303070c15150306050406060f031a0f09150601020708070e15180a 70
    0x4000254807500d4400412040345c17080c050a12138034808801e2245001c68400d0140500c41d5004680d0150302c20015032016051a80181d50041d1240046900e0141403d8506040300c00752602200c0300d800026541d500b5a6000000141d40042c0001010a080800c031002e0220b00d20070120740c0d10101c004c150318010b0300d2071984284074665840b60542d501d00c0c2c030011604069102a1301240c05103210400328141a1000800c2c070301c1910300000034808000c80889203a481c619201c0904481080c150040112241c20710255000e0703102c90700c1d0718030355114515203450052aa245100542490308194555aa4020b0000c00c1102d403c004000f07219240c60900c00050403041d0040d05508c0300100000040021440a410b00c11441c25645800754440c411107410444084d07400030f40c641c3c07002011001c070b202200003064100c201401140c2c4007a594801ca01e050070760641c0003500200c413803000c011403440b0072002c0500340101118030140c0c0c0c00c00081542c640c0302000c4c00d100503440d82d0315072814001140300 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 386350935 1250 386349685 386349707
    0x40309030209060f1e130606050d1a090c0f071211070e0702120c0309041107030201060807062106090e0706090e07082208040f2c191e0b150418050403 66
    0xd0814401c15485180c050019400a00b041c8102441c1a04210100c0c02c8540314421201c0c004cc0072030710f1625030380301c1410103400100070004210001c10103400014485012100c1903841d80d00c4041080c86900700b4542019a00d070b010304450b038a81030030081070b680e010901d135071040c60031005203840780382d29501c0c24614094405003540207803800307650a8002081c84040d00c0b07005d1082e0700900c0f80c00d40700c5800d07607158140c5100b200041a0700b004111071214151141150000091800240c0d80d03507103850380e00c1a10301e60300c000c0d8569003000c4e40900080e50322003c50b001404103040111070b5800c10682c01000550010a04464a201900541c5141c902e4628100001790450741c426125a04e5581088944a640c413482801c0481042d01c9101420040b40664078200b0508003408207580304a900042a51007070034a0072400d6499144e40b140b40e540200b030081e660310300e1500003050f80000060001c0700c801e840b1094044c8505000401020300e420350b0510700e500d800c0d04c001c81c2d607072500d240682e06000342c1 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 386352185 1250 386350935 386350969
    0x30903021503090f031303060b04090501050a051506190c03110d1e08041101030b0102030403080c03130b0c07140f04020d1407170a0b0117040309030209060f1e 70
    0x1440440620781040070107580107002880c16a043c4d4082d140b1165902d205495601c003001154200c01c2020401d40da00458606c90003800126148101b0b0350360b07908488013281c1d003034070546e07854061180c2d04040c2e5a1300e10302c0e580d007515000c2c6465141b40d40041004083c000340c90070001c1c402c080c5000c040c400c10880c40000c00c80d804950721000c000740003814002c500307041142241c16417030f54084c440d8030034400d190140d03070040d10500464040200440140c0440b80710345066110800001000a1183c4000d152030941c4101654030341240e00c0518001c0072141e840404425010b03c0764440c6000302043c2039080b9801003001044000b989404521003440d55100c444d8410f1001c1100c1e203031450290011203103101000b00e06220707070340d0340c220545450301c20340c2078080310110b21800a02c044101d0382c092890038030141041c070b68030b015085010700c0b06c041c101d0302100010502d00d4204110b0406103903054001e181202c0202d8400c1007072010032020b581b0502a0301c7c9590980e41002641e440d4a0f60103070200c1c8803 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 386353435 1250 386352185 386352199
    0x50102040f03030f021507200c1c11310b0d05061005010f23040f03030f080a090f0f030309050304080c0a0e010e18070b070c171501050d03090302 64
    0x42c03414060501403441c0400130150081c407105140c05418070308001e110340501d480f600501c00035113085904c03080d16100c184469104141d5241e10071703581c5400c840c141c1200000040310680311490200d040b00c0005084078010126440101003d440c102c1a08000b0100741c035400740066405a00d500180070111341c1b854010690b0274080c001e000d800b0810610030b040d05100d4480e4146d9890045410212102c500d0002825904001407a18a980d0402031036125100041d0b080c10b482d0110402040b401d640214085a40ca01000c44000c0c0c00c81c3c19140d200308690004c105112036170702e44000703104805000070115454a402603040500952262081d540c111048a4440f9141c410f810340e80c3c8110b500891140c1e155400007d80c80804082c900c0c140d0751a0780707203c502074803451082500c4900ca80ca01c3c02081c080c02d400482d40e42101c00c05822464040e07040031203840e240080204c074a48403180003d1213608035084a5003101821040da904454040c0d481d504402c81c1c1d420708076032598907070700f000f584016 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 386354685 1250 386353435 386353439
    0x40b0703050d141605070f0503030915100501050409020919030510110f090411040902030406050106031a1e04020f0310090506100906080402120d08090c0a030f060504050102040f 78
    0x10344000604044581104200540f403807403030307000e00d6640c0120796107040c00e0340180304002418810005030041510414071507407404040ea03991800c540003110765000315481b1021110710200c1141c0c0d00764000b0100c0e401c4030101d1382040700081482c803487c002c5516441d000640104035884644080c0c0700061445d94001001d0388925010351543c10344401c0c5202907040003942102d401200c821500a070844440c0305107400f80800070b02015181c0b404101281c407100307000c0000c1d0802c1c180001e5106600c200b00004066041080c05400c40d0802c41001d442040661a421504e44070040803070300d40c0d007849180c454021407100016000c0d10403180c90140c104800b0040c00a20745041c4406019620360b11020300c440e54031601885401107014030040000f0f40c0101003042107a018944046e00240041e05565940192031025858021000070060003c2e070b02d0b0f0200040314006110f1452a00e00484042094503d50b8507442044c5010503030290420784c0d40c074007180400600754115402400d0408100002d0740e = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 386355935 1250 386354685 386354687
    0x1312110c0120160603050c090105090f030109050f0a050d050901080f0a020d0905010b100302090603070804030c02060a0c050601060f02031806040305060903070b01270b670503040b0703 81
    0x1200d04c03030100801d042c100030480c880300309400d507868490180d481c3c504082d0b405003000800c0301078036031041c0c15542c0c036820007002c540c0c14011010207070501d0004010134103481c80d1071454040b020440c03d003007000030b1207040700680e030008010303420801440c00305010b0303150310100100034030580c414104518501101c000410006400220102d02e040700c100500c000c450109600784d00c540e9040540c010307010070021b109103000382c1089401c03e002e85003a025140450380400c03c0d50b484060500b01180c0311035461002c0050401c4101e000d01060326141d8100d01070107001a6a9000780030480b40000e648403003000c000d03102c88080e140195001002c50f0400d00b0000f82c12600d960051900340d4039112500008a810200c0e00b01060041d0842c00055a2400400a8030710051499500d210b5000c1c1032440602d01402c1d5203c0c0440d07518070103030b04106030080b00c00100c6a44016000c05850740c031503400b9400302c01d50400141c4007401101c4165a207442c58041c40c100f4254420758000090b034075404202003041c9 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 386357185 1250 386355935 386355973
    0x3010b1309030305010803044b090b030a0b01170316030e1005090607080315041103013002010f0203040e0906040218040c0314030d02031312110c0120 66
    0x1a5000b83c400300000d0f41c81d0b60465880e8403a81c002e0710782504095030002c142070030b802566103401c82e00e600c07400198400c102000f20b2010617912850120301c0c601c070051000115078800d45440090803401010714640f2a41d070460900814418102d003070003020f128150102d0148105c90341c044042071044045400f80c40d018000f05110b100c018052644002081215070081d0f049510b0ba220040c409410103131140c0d10010310341d01c020b1114060340f006050756140d40c0c0303985c0110003a400141944580300d6051001448007142c0e6003402c51043c684c50004425000c0d882807028030015020b00e4144003148034483d00b6880c52140398411090400f0003010410060400f00700c03103008604c216a407482208154080180d07003039040d14058000c11008a00b040041c50202980607002800e8080d06e04142d00d019202c0200e8200300c5107405084a512040010010100d14000d002c691074200303a0381102c40e050034295120314407184603040c04980e2500001010070040304a81c80450b140c112000e401c84076000c464a = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 386358435 1250 386357185 386357201
    0x80f041d100e040b1f051309050c15030c16080415091d07030506010207050604030606050909160b03150a12030f030612060906021608070c0806070c020d0203010b13 72
    0xc100c800d00001c15080b5940700418055030f0003c000c3d9040351540c031000124001c01403007885840518200c0020740d0344030000c08402a180003403000405201c01d082c090706004c0c0506100307206000807e440b07940c1c407405a003a203800101c010805900c49800040381c085103540d298010f05011404500055410091146003424032903a0391061102035484030761800c2001c0000602c0c040402c1000080d082612944c0001c4c0e2240c41441203c4040d640e47d80490019400783c0c209580c0c40303403100d005010a007491281c0c1380e040384c1c000001f401e01c084642d6446010307000078068400043c1c0d00202140503100510a100650030006020418407545c030501080e81210051044001c40e042c1e402d130800c094000e05c81c1c2c104407042c640c0c00c6890118695a82d1004001c10f10b01140c416500340201c0410621180443c03c0a510403201903076684842e007004e241d4200f26074410100d41e800714017002032069100d2040c01c035240d4190b400a844c041c5500c0002d01501000895540100400811b000e810982e81c0049030707 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 386359685 1250 386358435 386358451
    0x409050303041208060109030f02220606021c0e010503070e03010c030219090e060d020d0804081e031c1e0c1d04091a090712060207030f050a0c080f041d 67
    0x6501060f4001038030510401c60340140403e10400c4204040703050350080c114207920003401c503140e08507442d644030400c021040003640c220f0394a0405021043e0100004400507400054003244c100c61160010184000310040c0b034100000800414415070183c03844422215004000703004215464030004d009401030052800c404091030040301415018400c840d068032290b00d206e44c03555480e441440351005512900b00d80019482500d040814804000380c8040e20702c12010b841204080740c2c0a90f003400300b40c145c03030403250410411890700c1c0004440304d9851001c0e00c2c0000c00c141203503105284022456940c2042503604004041c09e4007507204100440019407050010301070001d034000c1c002103405441e0000d02d59404a03000c414038044050b1510341c0a00e030181102d140c00d07141c0848809200c40550704032085078004c5001c10400d0303008041c14405e0541c03450028280041c00c40001c00c2e20044142c05044000000761441c4a402c5620481d0050a031240c1104d0100001206400c2e20490403181c9807 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 386360935 1250 386359685 386359703
    0xc121b0324060318020315010e01080601180f0209030f1509070602100213031202100c051206010e060409020a080a0e031e0a0c1a0915090a03030e0a02040905030304 72
    0x32504080341e5070021003a400889942040d06184040d802040456440000c00a24801100c01650101f01c420f401040c07152002640307516045000071144810703004440381e9004080148505e51201d504c007140b4030511071000c1401088100c560009103c1e554000e50540100c89080c15100ca000803079101e0f8600d01e0400138802c2e82c0303122030945c4a0016003c2c900050f044060501c0d5801e64076000f400c2900f40034906104403940d0b0f556500410200103241d00e0160308100c40011030710103180b05102841c09281030070303803a1540040115042d218020300c02418042c01240041aa4541c0030030b44002d40885c040455561444a901034503403181201d15030201d60400d160034990701008400c0d42c2c1c04814030320301c614032030020b1040d2810980004450100304000180d402010984905200145c00c00e441c030300090900b0000f1001c1d0800906d092090900729020b81800b000c5400054481d00280e0586400224004020020307424410140406984141403101712424000b0201c01540180e11a135000 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 386362185 1250 386360935 386360951
    0x1b080105011d19052e02010c2f01050901201e0304050a06050a090501050a0c1413050910060909050c1e1c060614040510030c121b03 58
    0x440b400b0042221282210b451210411500c0c244201c00304955003a00c0340c0380442075142d0002c00c00a144846001e030820f41000c00540c0050200401240014107600c020303c050079404002902124108035400c01c5c03844140004c150101a0103100340b2407100140007407000c4d0901390380c6540070741a0046500501e00748010180c80c0d400113030781180c800c0e400100c00d00800e0070802980c0e00c043e03000107000740d5031409844101000912584a1244a10041840001c801c0f6050421600b12140104103030394913841d10700c034010402e421800700a0541c101e0b025841d9070743da42c4c03040d80c41c15148075404a50030980c0c00d02407240c0301c80d04840340c4083e00c0c090758524800c9543d80ca095000c1c4c880545043c000f0341810070024100d42200d501048034000000a82e52621014001030b254041c0412100d00003170f951800107022560380207040d80c101d03015aa060b6820b05042c6800101c2c4000360b50034039020b0603035821030344c85000d00800f100c41c100d803d41d030000c0000e451080b28038002c64158800d103100007071805105c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 386363435 1250 386362185 386362187
    0x501090614041505100210090303090b01140d150608061005120607052203020303120a0b0f130c09050603071d04021c05221109010902090306040f0309091b08010501 72
    0x52550000031035400f10005503d050140b0100003550001c074801c6000310003c42070b0100260044040080c8a42d0380001c1307103950b60614007061201030300580510410701b402044207981c2d50305031510294110b03054500c0c9019545140004001c154064861401401c080011900350013001e01c04450050711180e01c4851a803840b80d455200486210000c80c20900c56800e2110b07011000c00c840c00a400300c0710392040e44035000645103400601e50403d51741100c80400c100d8124074000c050310300c1400c0d02c0d440601600b078800104a0380c103018090364401d40e1500c001e9019403140360010024080a0003c559a0030318040090420b41c4209404800055880000d045814180308030340c61030701c0c1c15000408032041c0d130400402400e8084e2504480802804045840034107072159096450f104541058800e56040306012000c05c05a02041c589441840a0000c135140810250380c46540500060018440333841c0a40b94510107800408d00c044c64546034400a440050518510f10070648840200d40c0c1c3e9200 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 386364685 1250 386363435 386363441
    0x12120605031e0d180b070302011d030919051005070203010b1f1b08030112051f02040509011514030c070b151c05031b03040510020729070212010906050109061404 71
    0x13a120030101c01c0703030600b0041d6450340c9024101091081c4008600d0002c105428031806a02000d21405070304001901006460400d24180001e2034014a220300b1a28260000e40744c4110983c0d204144200000ca01c02159404e44c0007c200010040918000354445158ac019030139003401c404000c00e009004841101520805050030780745d0000c60a071542e800c2020401c200c0000002c00ca4103441419429940a402c240000c1101c8061440041e155031801081201d00c40060380a1301d4403c2c0c80c058401c0c0300c0d5a100c400300700d1405820b075520fa42c2c1c1d1540381c152003452260f4140680340c001c2d840140990482158100c0700c41d54012605040004c040803110011400c038410010300d964000c102d02020140c6425400b0b844c1c91014083e80d091546c0c54000c01c0c07008200300140030060700248800c2c07000589020402031000c0400450049082c803800142e1528824941c0c060320030003070f052050390100f40035003000109590001c014003c55a4441d42003000d0a400d0103009100d03010442010f030031b07007010700c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 386365935 1250 386364685 386364707
    0x6030b07030e030903070e0601181410120c05180f01120b0406080a05030307140304110904060204051903020103050106110318010c0b0708010f050d12120605031e0d 72
    0x102001103615030100c154000c11081d210024540401d20041c1c815580500050000f002c07101d002050600d4941c0004040740703501200700000380450f000c1840301400b0b14142040c0540b040d80c6c012241401d01500750740d4281c09940e5100706a08050707000c08002d80c000c024011040121000711184008041001025000d800b515800900c000d402c40440700038603001740c0381540014000003809500c0344421400c00030184020f850507440001400001a8400703503181c4403200e502c001c1030441c10300344e036203981540f880e0702d007544515102000b050510009904807802044000d0000d41c080c1c400f084044050103151100741c4c0400d180500026025020380e1400880056101c003441c601180310890300600c1480228090402030240300c4803002800858840d809081e0f941c40300405507241000040801400d6000755006410181529000030b9001c0c2855015151500348039403011820703248140142596403280307a051154004c00301c403001d20350200443d5848507400742e0744000c00400e0181ca01401d12 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 386367185 1250 386365935 386365943
    0x1f0e030717032b0e0a120201060308040306020c031306180f05010e060f07080708030f1308030f06120102180f09010819110a03141015120f02091303080a0603 69
    0x100101a055840d021803600404120580307006402071050340c05048907132071814a201036001c00c031140140921200030386410440b91001748a164115600c0c1a402d004a06c80280055004034118921040c01d03c03c1e50141074043c112207002e50f90700c0c000105a24008200100c0c0c2010441c008600c0512203d0032100b5140180c5a082c08050740300c1c140030003580a141401d5503030105000880020300b030000186800c0c0d00031502c07180c4a00308075410f11600b6030003420342d1025410000b40c0e0400960581d0580b070b4000b0705513605120950b038250205225070a0941c0c206083d5200041e0601111488400b2480715071095514100441c0c4800c28000c1408003801282d030294408030140d114911010040311344580301d04090044170442b40003040076400c0c4c0c0c3c1c0048810400311034038140c54040401c054800100111b40910010210104d11020740c0043c0c001c642e845000d410540c81884440060905050f90141402c0e030603140481290707c082050403411000211100080354400c5600d000d0b140c150303900 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 386368435 1250 386367185 386367187
    0x40509190e06090c011d090106030b1002010e0d111e0105090118050705040507050706090f110d020a030210020f0a060f1b050d05070c020915040b18010506091f0e03071703 75
    0x1032000640d48064004a5424500c184101c6c002d59a1654108a402006240c4002c1010058201001480040600e0f204c1c11685407284c3c40000c43c0c000a100e80d400c07002c4d070800d401041014010107003008000e030a030040d4031075a0a1061404441513120714492041c1c03100801008605801c008802c2c0703045000640a40e0040310207002520700b80c1d000c00c0d04480395061003482d005132030b40c03210709481c0911000e03aa4440420a2041445925244e0ba1003482e070458200765101c9840e40028480c040302e000c0603000c0c1c3c0f40e800206444034002c011560210f00403c1c2160b492460f549080327406000c0d282d210070034550500c08640151074680040c5000c040e095100c1d18203108c0140c54000090000031303e00d0b404c10500900940260702c40c114003a02480259000720301c00c2108109100c16503000620030f0b4010801007183c003d581b0714210035141505c800707c501c5a80c542d141c000040083c0f00660080e0f03d03201030140420310840d0020019040b128096041d501110b41e248a55200000104541912900 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 386369685 1250 386368435 386368453
    0x15161511040504021b0a0305070201030b090c070f0204020c0109050c10020705030d05130b0f0c01060b210406090b0f01210804150207080f030d14090a1205040509190e0609 75
    0xa00f503005801070104040300c040100001400240c504441401e0a41c08107200045130800e55905002d0f1040c2c42c07005981401c05130034062100340c6d50b8403400c480589940d00140008046580719011910104900c44c000e2015002c1c070304159484140e60a00c0c2440b800242c00c280100360300120f008004c65400602420100e4143d440948031a40030070f07669015503549180109500c80c039a0060000c0002d00200035841d003814448c100e0842d074023a002900c640c4001e000080001c14101c4800c001120484071140c015120380c0b4020000d0000c0300c4004282048001c1008282e0314000b50403412103d1613103c00070051804544911300d482c000401400343da20400041c000350700844551021172801d0320458800c56030b2404900d00f481a108050543c81d0800110514424803070300804801d80259880517800f400e280c0001071391016003010092406071050703000b40c3d519024800340e0f8000c210181c00c2013114a4035410405030008a65446200701f071404200c01e00703008000402d01e100304401001814445 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 386370935 1250 386369685 386369689
    0x40605090c070501150b030a0e0109020f040c120203010b070b011502030304060b03030d090605010f050a1809020111010c0e01031406010c0b0a06092412030207050609151615110405 79
    0x54400710b010b039065034071444084468800404544010300c01e031206c0c0e41e00d80c146000c0c07980c141c03140c007003041003160304140342200540d40300601c84440d00401c6400060081800c0070988070410b20020f034810b2644003000000f80000c0d080020003040388034090b13020041c0c2e20380b1103110656005080690069109000003000145190b0081a001e13500404890130141d46078201d20545400101c03c80300c5c113072075100410122482e40701d400040d01c41120218000760804030300c400340402480480e00c28580b115903007025a40100d16104602012000921003901075820241281488080d0300e0b00003860301d90b04c1407080105000d0180911416540c1c1407040d01c00740c4814600000142c080c44440381c1d03600c0c000400082a10070070681c51000b940c918840484e40b04024002282980515008020301140d0750010b035012a084080c0e6400700c40d81c079101c4646501240c400d064400030060040c800248003801d0902c071885041081e0f10500742c880810004000c40e1040e02d818030b131340144904060000744514 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 386372185 1250 386370935 386370937
    0x302030f0316080a030603050a0309140105071a06150a170a0218010e0f040c030e0c01020a0302120a0c0f05031308070614071103011803090f0b0d0b12012306040605090c 74
    0x10881c85c1c0461135540326203030541000e806d00c004a001c10318034641042150b201c40c45004125009007040d40c1007090f2030f01daa9041011200c454400520360000180d940c0d41d45906a0b40f0680c1c004c24003a450f03034207206000d44581c0074600c6108400303c5010009424000e64002c0b29007195007003c0d100030b9070340780500558a1501c44140941d11940c024401c0642d0344480c0708607041045150350100348441c2c40c1c52810304102c0701104c01811508000500008a50009450303404547c212440541d217106c0440200e41140c844c403c010301c0c0c14520007034a41440340003c09049281c000c1001d00c40c0141d611041540d80e0a079912401001c1204000b4150b11100400d000d8140603000d40094103041d0940d1002a08446030408080d52000b4102c2c007880c14903622400072000360050941040d01542090b440201c41d02820820301c3d20542c60340c0010010341c46901038a1042c44003600244101c64601190014000040c040c0411050121000810f00e160500601049900251840446032114402da06c1c3c1 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 386373435 1250 386372185 386372197
    0x90207020a0306180314120105011107080313060e010f0f12020708192006041502071b090f020412140a1707031709060a050a0f06030c0302030f031608 66
    0x449540c041c0000045120b600982d03221400003082d480e034942c02890054406c80b000248100541c2d000d025804c036942001d041d442c151202401e0461242c0303c1c22080c2c900d000740030380244030503020118400001240d14051354003612015110180c058411400440c0c50880200141c1c000130101d1080c5845180900c1003103a20f040c2816000d880c0c40710940fa81c0402d6445034184610b50400d400801004692060500c1101c5000080b107546c1d140e00000025a108000b03080504210707801c10103105084016030455801c640d01040c44102040c86010210501c40e41d4403a01c0882403e080750311142c20000d1003104d050701c8803610360b10010706090b01c45100c0d001e1546004409489881d83e42c1011940c1030300c03002400d04105514039038600003458020140e40c00e5440d038440300c0d13590170203112038030101007000c503800381000e0b10000d401e0361050780b10400b400310504000300c1180f60500100500400500050a0303031b0095040307500052500d02126034a2040d80034006000600500d6803002451420003800 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 386374685 1250 386373435 386373439
    0x30a0e01080f011e03050a0b0a0b0108010b0f03060d0b460c02120d0b1806030c0121061403010c1b11010c0605010b091f140310080a0b0f0a0204030c09020702 69
    0x244c094907952014540b010300c07102076070140800301c03c02c0200d00d114002e10003804000e01c0c24204070b500d000d1025000c0e0160111111000101200051498440c6074500c18640d41002c503004050078404c3c0c284240186001e52501c00a2840c4001070600100104200e2562800400c48040284400303006000300344900f058002c5004000c0310004858060014101080c28494002059055070b0100310181c1c0d0740d901c2650800030f203070003040311540d0040f0381861103240c00c2c00e1100580b10000f141c00380d50b400c07140706585400c1c40e001c40400d0048104000b040209400d500030020000f0f400e105807005000a100d041c0c440c00319400550009000a50036076400741c1c1030500150b8482641d450106442c0260402c400c00800031038516000d10700005110b0480c0c85030071256800841180e0024182e900101c09003003039190020220721500c034403160038070013003400000b036136110510f614245001c0c04003911641080405a004203140d1903103482140e084a80c011900b20f042882c01031100301030b40040718141d03 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 386375935 1250 386374685 386374739
    0x11e06030b03100e0f06092407031b3c0c08040f06030b010e0907020304142101021201150f20070308130e040206040b0c031605030a0e01080f01 63
    0x1050f50781d400b903681c0c0e0b80102c0c80a0400f40d160030707407280c0c07901c40010083d090f1940405450300d47c08102c44a170303180c40300710003500c000c25a1f03900200390054071051584006582e03070000c1d000301c02540b003a5403100c0501c01644242501860300d50b01d10303810120740b05282d00c03060108840c035121030090204010306031140c00c806040c25520304a1034441d4041c0e41c00400444e4a42c01750282c25a4040640006450101c0350f502860401000007962400386014400e13008005403c950201c5c0d540c480308400c40100707170b41514070007002105124081d4121101c0300000c020010b0010824500392009400f030001c607035541845403503041c182215800b440300d00b13041c180c00801450300b0300d0b2081801300c000510301810b2401e58510030300c40f081e00140e00f6a07115001603081b00041c000141d64039001c850031940350410a54540e00301841c12815403152400c0c0114203130414659800704800440a0310740c25441d92101c0c01507032143c00c010b64181d001201c0b442d100202039401801200070346001544d04001c0d001c043e03 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 386377185 1250 386375935 386375953
    0x1302030121150f090c05010c030e040515090a0b01110616030f060e07201b0f04020408100f050609040302250f120c050307080304060807030b04020d050a05011e06030b03 74
    0x241c040790f20003254402c3c0710762501e0340e501c184000340c04004000c01003864000303440040b40e01e0090401c050710036801d10583c9ca03140414004012010f5000c41c138800200100614100300c41442e0003801521031060200303600c0e0601082415020400038420400802051071141426804400403c0310212566005694400c0403a44c1000081d049209030b60948400d4007141e01d51000074414109624030300350b0b42d0300080021509824a842030b5031107100030b0341c10030030f41e48107440020b000e809150001d249910501098216001c0a0380005100d002010070411040c0c55030001c0c448c56100031500500541c0c8060005a503884414040c180070311203d03081c0005d050b0715040c030300d07000c4d03074495011056000303004040c4d005100c1c0005220000380340440041c10740380d04d030502e0035459029a11403542030280f842c000860303203406900008882070006108542c0c4890140b03461000f800f00b81c80031084c143ca444000b042d020314041d200c1c2d18128004c5558000d403450601d0172405071810700300079500342c01003400e8 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 386378435 1250 386377185 386377223
    0x3071505040201210207151a3a060b0102061e1317120a0b0a06050a030204081009030e030d050414060d0e03120c031303030b061605010203061302030121 67
    0x13490aa4241c0d41c03005a80c0d0840c50421140d40d9908040190242e807511694030300c649009440c0d1908030400b40c1d082c41c103074900681214051408030400000d21401d25a695900001c50400c1305440743c8611410480e03078413100012030b42c80300202c13030850003159500411480310026003800c95002003194202340c0d00b00e01c15034030072499921100c0286051840402d40682c0001c500c0141640414000c400300408207491000900f901c01602c212414464005503c905452194040342c010705122070880310308800c6042d07940b004107011581540043e4030340783c1003100b80c42c001c0307054203e00b0b5643e40c9a5080c0f41c10020040c44d6400d330001a0740d40010100440145074019024031800480d1103c040c5440341a904207130041401d0080107100c5003481001041150128050140d1901c0d4062800007407000080c8046103040c03280303d010020310450508004100001500114405c04090700d500c00750200d03204140d416800b0a024500010480e4000c440c55031a20800890455004129111901e190440 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 386379685 1250 386378435 386378477
    0x30a0501090c14060f1803211c140403030f090f060501050301050c1608070303090b0f01090b0102070807030204020a0201020f12102111060918100803071505040201 72
    0x740440e00310858a50411001038683c01990500c0d00640d10107103094040000040d040c4200c80034141186c40240501d4110b0b142044002c0c1c0b9200440c2288030f14643c9076840c0383d407030b0300a4441000c0e40001078000c05080459800b0b81400c181e402d040340080c43d203c0341d400303401504281007407402c901c0d50b4010a50100c1c40032a9000020b41c0640030005040d41418241425508d005000c0c002620041083e0341ca41c03a60300402601c0e0a40280e1180c1e1078004d24681200580007403c0060440c00c041028044046e80d0603441c0384c100c2e07148900400042443c8001680c8803080e92203102420380000d201000581040d40003090b01c0310451000510b010002e1814850b80e030010804060408401d404110010340350302c0c40e00029000600900c48080741c64904e10500000001008000085500c03600c2426190841900c0c1c506000034100b00e5041c0300854102c8140008444900c0005000b66002038201d0300807007102c449682160181c48442c901c0940003002d41030182c812410040d20113a03045003095421 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 386380935 1250 386379685 386379701
    0x1018020d0f021314060a080304050603010303080901110c010507080612030412081e07030306081b120106093902060f09070302042d0b1e010c020901060305160203070803060103050402030a0501 84
    0x100301007855003060000c0c4015071b40c2e240c001c4101540104000d00099586c0d8040c2c0e411a83d02d850020742c25038643c1da281e030242465a00c018070307041004c1210900726006421041c400c292a0b500c0b40c21540c0e13400204150004d1405000b185030700304100510550a180d100c0c1e00015003c0c481c01031400101582400e40d0051480e1380c29443c80e001708020040603494040c1d0307401042400d00034102004020010b140700400b200c29180b296001e4543c1030340400f0b0a410141c002c1103101c03020031940c40e200903800c81c2c110070140d0000204030400d440004142540500340390800300360b802400c0d5070b0345500800781c0520300a400754082e44203d03400000103944500420300108600242074401462904412071003100701150407800c9420001d000c100e64858821001080c406100c01d03e59052840c00140c1300100710400103900140000f0010905a4160b0002c90040d4000740b01c8800c4400100e100700e03140d00aa040040510804001185880d8802e8000a410078001001c0c3c81a80259030744250842c2c80710 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 386382185 1250 386380935 386380961
    0x6020c0a050a021311040b2206050904180f0b0618131104020703120b0f0a12050c100f1815020606010e030706090b030a021b1018020d0f0213 62
    0xb0005040031801c04a15502015202c1300b0144009601080e4034100c90080c0d01a00e40c0214020851300c0c0c141010f41c1c03c1c188254407900348000d035692103240040c8079500802085020381c2c182031030080510140c0c6919200c3d15003044003034482c040713a961107940c036041c00303881c0b107038000700d40001c00a0b803903010f00d40103000d4004810803c44401c15403030801110800c0c0418644500d2041c898107011a03044052020ba10406000020b000029900010008840d60300705a4204c118818041955280f4810011010b03000e6401c80340b1130718601c000c1242c0000e00c040c103080020003039030074944400d005030400b5400801c03d0550309001c1c0d0f04e601c8041101e20319081c071600141d0103c6c0c2804080d5801c400c0341c125044041e0b020b050003030704150015003020b18900c140700039108000001003200d0034a0f0b0642c0c500b03241030200ca003015032840d810a5039075400e02e00650700491401c0c40e130000e04d1503010700080c40c0613809081d001404030316886100d003080701504c00b40d8000d2003200285108a040d031107058414188 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 386383435 1250 386382185 386382193
    0x9020414010602100c0e06030610091502010204140a0b070b1306051617070203040e0619031407090203060907030216080a03060810020c0304150e060304080a081e06060706020c0a05 79
    0x1000e9424090b04c240f60034810610912411418403031f10345000b105e901c0350040d10351090000312503c0c1110702c0d600b543e0000941006140400c0001941034000b081103c4071081c03c40c00c10500f11041180e540514424000302031000c000c0710002501c0110746650241400d04c4102004000f81c0702c4000f540c0003102c3e543e903034085116400e070005801a201c450040c1c0803188624a61900b010040e41e070380703e18022840259000000601566144a1450070302104080c0460001e9034034a4030041002d03408035500214061900c0210700501c43d442a64802c0c8d100800000441c2c54014087e4002c0d400460010011100d0341d4441001c184480001e184c40314280d94009074480c60080b1642c104100c0042d04508030b401000b0240c40c00700000165016211235802c48905000b00050980700c8120b1040f01c1504805c01108010074002c0c000d010f03040e1140d180d100c0e03c0031642c1c2c0100c0450b12112840000140403800800b01f8810700f40300d406000c2082c402c0d280140f030401c100c0626860000e50752000c44440e44 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 386384685 1250 386383435 386383453
    0x3080301080d080415020c0715021608010903021c0e0909060a060501020f0c151207080a0c050a12020a120204080d0e030604030815060d020d1505012109020414010602 73
    0x201088030b188428030500c2d015150381420f0380c8116049018006031031540d90041080818480184240b10003420369108800114240f95006902e9034080f60040d6072484070080d00280c000011702811210b158964058003440900e2409030b800940b400c030601c404c2183d09014401e250702d0b070500341b500030749802005290514040300c001e403d071090750708058115000744002e0307070010000240c01100c1540444040c0811805000f01e04503038000e0300ea41100e0f001035107050140094022600030f000c1c8d074152a052211201c04001594148503c0c514200029400010310380004d14a60180800d2801494101e4403103a0071201d007001c0c1e82043c2c0004025402c0b8038a00887c40e90440a0044c8e0402c1c2580500070303c3c0b50030745025040101c000c008910000c070251150b030040c0e451238200e45141d094102c04540f03850300d00381c01000030140c003a0002d8a0407a8000003094540c01042c950110903040080c424000445c2401600902503403075040b03812645030076803c00c10901c80d5561f240640380315401400c000c4 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 386385935 1250 386384685 386384699
    0x1204051e0307020a030224031302030732013c031811030a1401050402090a1b03150312050d050604110405010305060117010b040618140d060e03030103080301 69
    0x1800140c010005034801c001c0c1500584842003c002182d40481d0800304a1444c5404207001c003000c4d0481440a8000004201000c0c4030568801038180c001d81c1211000d03520343c0c2c502c2030100181c5041000c1c00c02071000d691080b04188000000304001850007401c10141c800c052200c400c500f0301c07141d10403801c0000510700d420703c50350b03c041000020320f0700703003c0c004001c0d00b610030a540384000030b01400d11440131008141c0781089506066903201640915803a80390200d5402008180d404074032415400e404076007000c500340640d41c20f003c1c61110000381c625035084154002d2460103031041c00c94401260000105001c12840202c4480c551220303070f5584290060746080392001000a44681c0c0380c00031714407600001c00203031015504203080000340341e200d0000503141020400000003500022800206101d00600007a00483c2d03243e44800603443c04900400c2c00c0d00445000d034114007c0f01d150455440d02d040b203c1142d940e4024140026128589101c440c2190300c2604191000b600000c0108004 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 386387185 1250 386385935 386385973
    0x3060b0d0f1803090315021e0418090201020c100e040e0f06090106030f020f0103020d050106031a0306010815100e0a0c09080a0f0201050903030c0319030b010f0203070204020708120405 81
    0x407050403024840302d2a040d40c001c1c00312003880c04043d00c1006035528141003d140e65048409070030b03203a8030141c507800c07140b50101f80c243d009001c3d030001c0d0340d201005080141030320b0103017140069050300540b44403c28034040c0401c1c0d2018900b03540c2003002501e0055815121480b030001040306c00000703849150442c0c115a450110054021001a8074144080010503603031641c86442c668101c0b4210907003102c00d00100c002e070268803070310440240341c0800000c40c1900f5911136002421040310692011101204250316000b091103005015000b00354811820a101c1045582c040205d500402c5820340360110299204401c4400c00c10481d03440004804e070507085074481c80241005001811132407244c1c1c0e02e8000c0d0b8419840d0003410302c0004a9005450741e014420741d0040f00440e0304403a01c0c1d24a84042e110000c1c003140400010a1a110700700e6465485402d5583c40c0800580045251002c5542800000d500404054902d004103000100c17000142d1041140680e02960080030060140f400040788 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 386388435 1250 386387185 386387201
    0x21010c080708040f03140f0c0609010f02040b160201020a08180307230915100e090903030705031f120525180f0603020d0309080c0301020a170703060b0d0f 68
    0x6104000342040300140d66148496051039042ca0440141b40500e10f0005050042c20110440d60a0100d070607034982500082003031051110800921004070818045000c92281e401280c40845040062034190035410f84060a401d1040c4115107812800c3c1e01c07540321940102510801c0d40e12132500e840a42d00d0f04004071b1015092002c410540480c440500b00c41d00c2040205c0d6502919a10f0300280c0100c031038070151004210041c141c5000e0b0110b40c18010186620301409900ca403110001081030711310f00000381d13489800a07881da00d01e19207034619440040c9212250300000f4009008002c90702c3d0340d40038060107401c0d10807001002e42c200110f81e5000c42d9401c400001c8181c13141d1400401c0005c601a9246c800310354902c078001046010720f00e42002620850304080d410010743e11100c2d04041e80082640201c0362404241e40c6082c1d04102090300780d10031243c3c0080003489102c0511844100f0320b80c45900300e031041c140081c00c0e95071407002d00c1c0c05400140011170001d5468599803842a4940030b4540 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 386389685 1250 386388435 386388437
    0x807120b0303090607120212190f09080105160224060108151e120c010f21150812030106020705040b03030c0f030d0b030106051311160c030c0b070b040b0621010c0807 73
    0x409d0020000e10034440b82c0250b031200c9d003048507843c864804e0b14000c551210203070051800034400340c5041c114600c1000d2142a02d54010310812482a11251245425500b003401100f4880d8643d16050300448031140050040c450b000c0b003405240901c0c0d614000c03000e0501a455201d00810a403079000c11000c685425030301001d40c1c01842c1c103e0102d0ba03000007403031220451414540c6100703503000c405040c86c06200ca03500009074034141d08149030755240400c4004a400700011224100024614010180421320454016034002c140501091a0641150410003000b508503410600011000e138a402c28094401086820024600c0808041130048101c2139405030028840c44c1d145ca00410502107010320120300d50355468140100c001000e00850316072801d80000c801c4403070700d1400c10000b90940c920003291480041c0a0006080c0790070f9003540c175019040398044030300c4c0c0d0325078491800d0504010401c0d58000240e4918002c54002c41504200302c0c0e0700d104c00000c000640040140c14450090400c1c4 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 386390935 1250 386389685 386389687
    0xa0f0e242209230a05090309032406060a0f03020d09060513200603010909030903051c021005010e06010f09050301020406051809091f0902060c06160807120b0303090607120212 77
    0x1103070214144404540140d003143c0f0010b8179036900d0180070f0035030003022100d99142c069180d001d80c0280c00013403c5c0346070000d131444a600e152241d404100700e92055145604c04114120403244550b4003a901506442401160100d00428150703542412600210307515488660045052801d00c0740003404902030b081640310b5240001410780008446000c144102c03070000f40c85114040070075115800000007503038000c080781ca8040c2100032040c54008002048001032007500a412648511801118100c0d800700440809030303190302004403880420700101400b072205140000515480910090004100683d01c180d110080558107148051107400000d01c034550000500415450104030030b40b50400480e450326440c0c1c1940004005400c00c003c01a50020020400318440c100100310503200341d0008007164403a902c424010b50300d4820544030240050081c0f4164401405140e00900c20080d00a044904003480381c000502550f20031310084942400440700c1c014010340400c0003400315014403a4030b0b = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 386392185 1250 386390935 386390981
    0x604170f030f190c02072607060801080d030506100e0a030b100503010b04090206160f05010507120c02070b0a050a030b0301050c0c0d0203032413050a020a0f0e242209 73
    0x82d582d110900039420f47c94000c01c03c000750b85502100035821025080140e500c80c0307a84d42c00c0030745568424401c0c04010f01650543c42c145510a2040c9841030b940148003030800c03090404122568401600200d40000303c0203408004550174400180c0b00d44030b01807040c0942e40c1018203041c203450780c1c2400e0500803410400c07081b0050b036500084da18029403e1100748121640d9041c80740000d0a1418040d2103946030106010320039900410141000c00c1b404024849040300c52000c9a4600c9075100d00c0140c0001804600d0700d90380710b100182840c641525012442d031842000103821180300b90f480b1309240304c001903500c400d50018400f8052a0a00740040c6040d4a85200c90b5903c51100041c0c10039115005485040c03140d45000f01309401d5007204004000714030306219050002d600545148012400440707807110994455442440d01120280c02403071111805040c043e00391440005803101c0340000e020210340f80248280003243e540c40904410401c51900202d00304480581c40851500d0b400a282c0e = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 386393435 1250 386392185 386392187
    0x6050624040b03100308030403030c0801081b151b0c04060803030108070302361902071e170d050714030112241505090a05090604170f030f190c 63
    0x41e90225030340d8114882c2e82e5524104030000402c1150001002204044280002d066050b4020401c168254482a01c0e50340c840c80383c2960f41c03082c80041400035524001012660034000ca072003c14400340403105003009540441d0030780c0801c0e00051440c4551002d081c510745481c2c24058070005028100185281d54142007803152211014003000c0d004070ba60740001502e0002e04800039044074988104864800c8189800c0d42c0c0e400010f07078042803040100130341285d40080501c21105000da01007400781070003c45030003015900000c2101644d0f00e000c2e09a48886014030b0030024100c110084000043c0c6250031400502110504004445452030a0006000c92129107145460316034020f569840740c811155079144540c034003041c0e1405040e00704000d184251400c013080000351a0215a25000ca5940f14024003c849080700c0391010380d441180480c0c08541002083c141e8418042d040515010ba90b03801210181c0c011f1700c041c03c200d4004400c0141c261002c20b02807040c040191024442044880c1c0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 386394685 1250 386393435 386393437
    0x3010b040203041707030c06021c0c0f02030a030b0a08010519050a150303031d031303060605090c120403300c0908060a0b010c0c0b0c0d0e0a0902071b0306050624 71
    0x100132114000005008030516000d008070694035540b0040a543d600280451120b480f100e07045042541420320242428050194036600c8054a042d0700850400d8107141088024016490049400019568010a0010080c040d0501c10503500f8001000301c410b501e86c0c001100e10090008078418900155412002c0b603e0303010740300301e035018900415454964241060065560b0640d00d0300752100080103c14100003280b80400c5a004040c1046010368400510658641c1107414402d051010081c07082501c112058240d0050301920b0080000c22149502011031108405400c800407103d000765095038000740101204034019160031408185048103155440750060406800c058682402c000941d00c918039541500e5000008401d1943d52440c0700c00311b076400015007040a010b905030f04141035015035803c0b1000440900f850030140d14000c2014001e400c50001110f441510b001d16242019484032010051402604000b0709414601c08001d6030601407540041c240142d1004840c2c00740c8000 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 386395935 1250 386394685 386394713
    0x903120512090a0305270405040b070f09080c01110708030d05040c050315060f1507080c1c0c02040b15070b010602060a0e07050d0c0b04060203030703150b0915040807080c03010b04020304 82
    0x10000c0b441022000740015501080d030390b046c0b90807901d403074100020300c16580c41c02d50280549496103440305c0c69519007125002c0090040c02007aa002481c9469031f540304a8080c2c9a50802000344c80072a920342e0303203041c19540072140e070030100ca813550140014442d00d00310420050200303c1c014041030003112420351a603940102418424400a141503885444002e00c405440448244140d5144000c0c6031000e040d420503044481640f00e0b41b820444070204503440306c1100303503403526180064089076080201800500b000d080d007007200160001507000c04c41c0e01410200344592201c0c803041d81845402850030790000c042da01803d051010341e500214000c030760348040d50401c3d1591515400d182c18500d40a04260f803041180180000e4001011903000c000f440c00368205075000c0c80600038030043c0315580300c6140603070310168008000000e450314080300300c1001010403102c507a0503d0340c1d130b00f411030810b0b450350b000702c905801c0510429010b14080c480d021b440305089a0071804c605103074490f15481c40c851 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 386397185 1250 386395935 386395957
    0x804030c020f1314070c020109030f05010b0405070302122a0c0309030a1406070c021e0111030406020703050c040501031e061104170d031103070507030903120512090a0305 75
    0x80c1001100390345403068a95031214000c1d00316072550f08840b80c004002d0142e00d2200700001c00c8800030413480b61007074074100c11240c1c0580d90000098190340342c41c40001042c3c034048034190f60742c1003008819140e034000d691140f1036030740340181c96030202c01d42c0840e0030400404c685911020365040c40c0c0030720100c1c0f103c00c000b401d668640790f440e510030110141c60340c454051015811310403001103400f007141e480415040c0101d03103401d0780c8140c0c40d59101920007107000e1a0003544200c0e03070080d4006403002c9480380d000d520300514218000301f0304c585990f800e550240d00700c41d005801860060051101c00c00c240140b0502c10358040040b0762542d00e41103000b0100d900c010b003024469034100800c2c0032407600010b03c260507458030982e40700d40d285126801c821240140034694000c49107110041c0b4005d10552400d40a6034900c14030f150f4919004039995401820100c0c14010300314008404681c150522030a4540a41c030b4445c0e403242001005100c0000c0101007040700c5d40072a0108001075844401d07281c01d0a54 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 386398435 1250 386397185 386397197
    0xe04060e06070225030b0c0726030a0207050115150207080604080d0c05070b010b07120507050c0f0a1a031008070f06140c010f0902010f050403020f06030703021201060e030d030606080403 82
    0x8400855000c1025583c0041d00362400c1c00217010034260802c004003034681c42103684460a00104581c0b03427803051650b20301c225034401800002d20214254004000780c5119030000038a101429107400015041504a088003aa4040c40350140b980c0411811024100980c02418103140640c2c036140c451183c4580044e40c00e48070146004907a0244040da45c0c410360141c00d0703200c20b40e1118208052030300800015120059121040d1111500640c1120140d82d000b0000e044009000030500c90302d90341020815030001c0e0f0002d00001c0c5204070019100e0b0300b03105017001c1e9a480c1803039011810600e0007504010102c0c2c00c144000c0040407034080d00c2c4021580d460800a40218030b104412080d4011402c00c420a542002c1c03801f08251166803100010301c0c400d0700c2d07d1242c05080d4600311214080d0340070003904800d2414117071046143c441c002d1a4000310030301d400352038800c41641d58000380000703902440101c0c0a824858101d4030b014004190a18401d00d000c0081d5890450000d01a480141014043c007071 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 386399685 1250 386398435 386398483
    0xf1803050703060225051506151204080910022a010807033602131e02070203010e07030c0e070507030e121e030909010e06090106081f0e04060e060702 66
    0xd09081c101d104005d0307405c94440b00502410a2a1215010401c00300c0680c0c200740021403624114043d20015000c4021a5040503c3e07808403000f0400040c10544100c50b06002d41d004681d180c440702c060088541c0d005e0886001d80540e20b40c24030301c4081e8034080d072003080c1d0002c0c00d040c1d0340005420380c0101a4940801d1100308d011448080c0c1f44d0840b1540980e00e144061004580c1141b07542840030791080d0f80f03105462100034020f8044170b100d4245a988041980c0205410020a8000d031003007600040c00083c20b015141030181c540000e507481125008004407041101c00c0a80e00055448071085c2040c6103407811590b4000c10341404406804d1040d0852011403010300300402c41e5580d0f078118200700070b092200c400c0d00c00307559070868403110b441102c5680000c584a001d101215018000182c100340c3c0c140d0a02400351881d40000740000c1e045030070241105041110a51001e0040c004003042001c00e091900b072550542d01c145c5200000f0364050f50500070000d900007040401058420781c4020024 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 386400935 1250 386399685 386399707
    0x5030a02030c01080703090203030708120601030b150a090b070605041a040807030804150501140a0501020a1104110d0606030605041409150c070c090e07051f1b060c0f18030507030602 80
    0x9550030181d01442b011405c0001c0109560041102e40000103610381e20380c0c0d0b20350044082e50384500003107800c440030f80c0d000d05400c2d5400000d0a400c3e50541403240350b240d281c060180031500a6003040d10380d1034842050206100032401480320040b640e8988081a240075100c0c0e1019104003c401000c00420000040c2070104000f18040d040c2c62400e0148100d5940d89400903003c40724000700d91180c0c15034400021651b00008280103007a50010b08400b42000302c4080200420030315003003c442100810070800543c09030721601c1e004e04183e440018000d400e05040c0011902d84000d81d0000c50030000038480c501e84005209000604822a8000390b82e58490300d121060083c0c1d60002c181035000c5401003003400a54002041c008181c40480d070106984008100029007564a030715110723103075541c410541070710a6003103903180141d6500c001c41e10f8119079078807801c80c1c61207852503000501c0042d00480c8140c0c00040d181c02e4001c0003680400c43c604507100c65481d220148802010a54002080b000103 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 386402185 1250 386400935 386400941
    0xa0b0301030b0c1e2205030c030601090c030b10022508061801181a0c0a0f0804050321040213020f2704060803130b03011202041a041a090105030a02030c01080703 71
    0x1c46140307013080d916581044105e51809281445ea030803501c40380c080100e264100000da4041105006008081c40e91034081807000410400b1345844c105600d98014155984841c218001005003980c000c08402114040c26030139107094807002c284460b40303c0300410081500090240d04506180a0000c003211101c00d00c03401061003600e8003c8008042c100001404110792180d4244500d241d00701c03c2940e42d52400380218807886082c00c1c042503150400c451702034450b482d0b4a0340644240200e9161411401150041048103400400e81000c0c2c1c4082104505084a02840d0303030302d41c101c1c1903082c2030b4402d6448109008540c0d425040100803c0049092540403074800004c0c0b0024004122254440404603169400f50140049101200100140001c0f20303100b140d040710038a4144003007900d2303d1343c200009488503060001d4851703a2044180c1ca01c0e42c076840340072510000b900c09641d940c6882020b04c007004205030b000746e01c2030300514400300c0980c9010900d144158824038041400303aa030143e040c5d0007 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 386403435 1250 386402185 386402227
    0x110f060403060203450d0804030f11060c041404090203190219031202160501080c030703090606061d01020f0606011407080406030f0f0c140307020705040510050a0b0301030b0c 77
    0x141740001c510305108818030486600b5240d142074100d503003681a103010326a80c60039952503c0024102100040200e845002c0f88910010280b8041400ca181017400902d03101040d50018041e240000c1c0410004100180b4134000050a1f9400e200994058000a450f072905040c64880703c01c0c1c0518080c11941e81844107403482924007a0801c5030741d01e03400d12044044550b0361800242c4189410401c01c50700d111403903002c40b501691818919503801400b034804d5007010f00404281612113950400180c202d01844000d84907541d1a108200050000070804e0b036140b0f00b0243c195005100c2958814101040d080c0c1c3c046003e081c5180c541e201741e400d401c03c03485868400b91104c1d10109001c520258117411110114049139805c1c003001d07103130301c0402e8115030f146420800400c0c0b80e40c01d604501080200615403182ea1070064a0702e0964880c003040036510101e69941c63315051160900c49850300d007500c0000b42004180e030310306560459440c840d1400e0040c100b2008407501064039124008c405510b800 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 386404685 1250 386403435 386403481
    0x1701170f030d020705071a0a1d03010e0f0c12060a0207020102121c0501170604020d110d0b0613050112060230090f0f0c06161a04110f060403060203 65
    0x1030b0700c6960514040080d041102c080b40c96004030342001900d00035940e9041901310001c9071302460043c01d0442624405811200c1c081594080384a5240c80d07602032007164806003590010306101140701d8141800d000141080b00d115010f1004510002080010100c2d4001034180005070b13186403500060b494135001c6210515207110014220354000120040c0412694004e02c00348456600d4a4204107101c0c030000c400c08183e4030100005000d0700c0c4c440035034070340d560144854a80110100c004180102d8809000780d41c40b80c101e005010740b6040031000010000200c0c0410419035050803048440f82c0c1211001401182d00410000c2e0114900300400c0c019040510707001400782c4040070b0211586031304954010303444c003614911324400c51010413607440a4035144007070203a80008108208441d00a50610040303400b11705001c80004400d080140c901040f10903200507140381c0f9251070700c07003a03101c0c070003a074003800c0141080b45054032201c1c183d800f1360798040c00c056140e689003001214041081a0622 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 386405935 1250 386404685 386404687
    0x2032503150306050c04120c080d1b111201020c01140a060f0e0a0e0114071803020a0501180306050c070c06020114040b15130606030c0315140d060c030c08071701170f03 74
    0x1f80801004810308011a0444400c0d640120300d5420141d80599132030400d1309101111203000d02c0040c80b2601110842c0c400100709420411120b80407500720b0b0401c0da80034403542c0d51008040c3d005680516030542c07120500609110f84c5041c02c0c054215001c60b44124880500c401c80411401e0311203411199450104000820404564032003007101688140c2e801d0022078508071586050844031050320064035009814081400e1501004440e1074190011040138171007440c0000c80061020700410780100240c4200310344485950400d40380d6641260700210035603140c110516104816945a658060741002c00c00e1075507550390b034003070408d40c0b064035110b03900c078041001c141c080390050341c0000d05442030756500b0414101e8008054040714402501030380000c95211041004814104c80f10703003c184040c00402e500042c5a407071106a680d0b0760700030b07030100e80c407032101512040d0700c0350f121548202d09107400b20a0161000200040c464180254400340fa1051308a82451000300800350848190404403 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 386407185 1250 386405935 386405969
    0x507030510050d031403060a0308070b1b04060e0f010c050d080906090309010e120312100305060601031418120c01020301230303191202032503150306050c04 69
    0x18020082141c060201d403181d4a404140c5003022040c000201e030303240e180d07811052005044013000781c200802156100c0100c00e0040b00103140e01020381501d5100d0074154081c0c0c180746209940084040b910240307108024401009850350044d001c291100c4261003d00d4244a40c00048429903a2800050102d02c1000071410099600455081c81007419100b9202d898480001a41c0c40780b0a200d4507900003549605040300b00d14141802c3c2031078400110440b8507203411115450f40c41e18045403803002e8105803034401c00510005100803039000000346400c10504000c40c0f00a02c03040e2000c0d20198072004c07028120200410100070305003426000980541e16a042c13000450301070b5209001d00001c2c4420f805603584400c4540540301c100c124000c02440c2403098856641c400201110785503020040f03446203c0510094500c020f50050030017154002c10034482200c4550805601d01c8900101890558680c000152a001e80c20940303520070008151038a402d0080c4145025541201662005407000 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 386408435 1250 386407185 386407187
    0xc09040323030711010506100e0f031507020304090c03061511010603140102070203010605091b1809041505060906060313050c09070302120906040c1502010f09050601050a0e06030a030309150507 85
    0x40d1100404c8240280035940d188800d0040040d000c045c4480401c07240c0e44581858075003400305407280301d0003408890039540c1081021003a503400f9900032001da0000281805400194001c80046282c00d08081c0616803620059444640c0c00114902c10048a4520b0114124007904040700440e00084608003c0380444503040c000d600c003000882c40381d03181010000d81030a00400c403a12a41400450302c51500c540070141c170813a403040fa000449050760b0074162840707544007400c180c0a14054900703841c865207035540b54000c0711009000184204a000c04220310382e070781d80040b290300c01001560700611000038a03000d440c0c8209000d015520000110801c02010382c10380c080c5c02444d16a000c0101d4644401200e50f86480d02558042c03c501444d500502400c0c00d2060340c901c92110900c0005510800c0c6924202120b00b4a0340031200d940091004000d6490300d005008050000c80c42c04035030707038101440020f07564240010020241a00d400203075090103a4028175038a41120312405000c10729001d44 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 386409685 1250 386408435 386408447
    0x10512042a080c04020a0207030b070216060215220f0819090e130c0b0a0f0306090b2b141c030c0c0221070902040e01080c090403230307 60
    0x22800d511103000039480060080101c40140403107200c44081d0560340002d4051001035400300c1c51080a502c12000c00000240a404a05100340b01542c0582402c0d04033912104001007903a21240466101007909400b0b048d41c00c40c1e043d08141d012003503808003003110784450000d95400002030301501001170203100b8811000000c18140444000d0102c01404401091354844002d000c0c540b0703038150341c1e40001e070304007580819075144074001c2000d81c031103682d50300e000c013095400311174000d00141c02850541000c0303030540200d2b001f92542020034885c0c1c8114402080820304034040d0110003242c0b072808002d00844041d14140308640000e60045000a030f4122199a20117541101c4a41c0508460400f001486440340d4081d20030b0b1981d4002d45000c0e180c00304807292003552032000e1056051480d013650000100302034001040c1c188070168030340d490051840e1022805034024038460300054210051607450316821340d407055050400010300803940300d0b1680480703a908204154408000103100740160002 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 386410935 1250 386409685 386409713
    0xd11070b0f04090c08010f1205010207202b02040213240e04020708070f020109150309020f030604080a141312150b3003070b011e0608011401051204 65
    0x50b0500c102c00000004a17107100307092050404100c0d88500521000911004800c01a40904005801c1c481191104c4c000c5192032141c0707480300f0101700c100c007149003064450f600e00c20f154003114001036100c134508003800c82d413078000003803290350b0008035860300c464142d54107c007500105074804040300c80603101503501d0b18900300c090041440881d501c0514505802122012030b4416805414079005035201c0501040300380080703041c020080d001041204405495040f00f00315030750040f134114080e00500c14110311442145010740c020404100100703101070204c8859078118680480c0002d0301d050182128040c4803030304041c00041e03003800141c907c028013000100324081e804d100817034102c18918404035200720707100c0c40e000700340c0450000e42000603c01d1032004818244482050403035014040c0d04603030100c10102c4901700b4110050000802c0c081c080d45190040094400e02c050500c617010b00024014407800020796141c0b100452143d12500a507286400c691460700b46c0e6041c07031315001500306450303 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 386412185 1250 386410935 386410949
    0x1419050405031b1e1f06060c020d020f0315011e0b0a2015010303030f090f03030203060102330601021603110d021e03010b01031802091503060a0f050c04080d11070b0f04 74
    0xb000d0b217000044680c41441c08032141a100e0a45a05042c0d00b4000401c400030000d9906c020256509241500c0a2211194102c031011414a0641c1003803080b000c841007400c5440e145141080003070041d001b0b01000c569440309a03007401c4a401d010300c004aa9400754400ea04100d40c0102200c25901c08010020f00d03041c0c2c2c0c4661014044c0d000c40d0310701042151000f41c00074100034512840c09002c01c3c06940215003080040c4140e0741c05005020349401050441d400c0c0c041c840d07050907814250001030704403164002009201900c8916440c0b40131500014031400041c1c244003101e07240390a0b55403a00310804ac842d90291107201c9182204590203612291000228000d500b400c2a443c61907109100303c40e1040000250b0410f41a80c1d40c00307004488000070b2020107105112206c9640607034080140f07912403040d1640c049180c0c401c054212080d194040d010060200c0180300c1801885008900845034008900d00a005075400030202032810b880d981c84203603c0600000c5000210012000400680e089 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 386413435 1250 386412185 386412223
    0x2041a070c090b3007140a050d170322030e0301060807060504062007030f0618150203040f020909161a2205041419050405031b1e 57
    0x182e102000191088401c20030340c80210b104107012103c1032040d82d0500d40b41d128100312800b40d42c6441240c80c2210340e4202e03000072907011141d01403030310b400b41c4000050401540d101850141d1a030b42c41d01c00800d44003d2805003035020001681c0e4030b00384986502d5044003854605001e03907072400e0281540c0040c210480c025403d0840c0401e0249000580d2000c54015503556840d06d403401030210352a500165103001c540103511240440302d03004000210245000b11074281e040803413440d00c00200e54402601003080301e40c104410001c075003100c0040b0060884400c015949503283d14103104084071a1800075840705030300d414480d110703000150603540c8020340c2054500184e1550403442c0d07100414181c0004800f070400c640c00020f03c407001d1204401818015035440a41c8980004054498003c204010402002c0c2006010089200000164900c2150030411800e20b6200c081d200c2c8240b103d1004511900b4103003a251500c100b091300b280c0034070210491003001070102c117141c44034a035100c403c0c0aa11 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 386414685 1250 386413435 386413439
    0x318040f0606020c0607021906080106021b100e01360902072003210909130f020105090a03020a0902030a05160801050d0c03150e0d05070b06040f02041a070c 69
    0x1024440c5809841c0c683c0c004103401c40c04841003152617400968126080380345444810440402c201a260241c0003c0c3c451803040e60400c003001b2303e003014001c0b4038101c035400303200003c0d5039803550700d4048503240c0d0b40d242086500d52900f0042c1e9600404c0c5079481c406a94a104a0326030f0000c0b2074518402500d24400c41c1c3c950f5076501c00842c241e001d04440501311200800d240da20302c1221003900d22503054007505031009900352807440b08082c14401e0311403200d6080050701e401c941c9400c40d03826a209001c140c0701c685030741c000c0d1603410f0401107145000b4140100040c03004540e0b035500d540170004585c001c0501060a44944200e006900252080701010b420800413505e030308005105900c826036141d4800e511607180004200c15040090300c241c0d5002088100407000c1000c460b000c0e00d98150078200800e240000f4035003185010f1401c10310904001040c005100010855039140d50002002ca03404942c034200510410300a100b16848500701454145049075955801005065030030f00461846100760707 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 386415935 1250 386414685 386414711
    0xc020a0602071409060f030f0a0b10080a03030b0f060d02070501060f03120807030b060309010b0f031609090611030426030601120c0306080f10110901090512030c031804 74
    0x1c40d2401400f120b039150016403c8a070030700d00c032041c1d0321034401450b001c0c40c4003901011034180085e0b07812034207d13074000000c840c0501852510107501b02d0700c01c1c6074100d0350302e00d000d80d2030381c842518680060406480700d0846480b662411922000d00302e008010a550f00350006001000f0350006004952039402e1000014107000001101f40c1100c0d003041046003408640c0703d08844050b402080b030b60a040e035891a5050685501000d14462590f860000560704150810014660180c084461082e4418810110a02e5261380c014044680c08079011506044030320f040d10151440f1220200144c0001c010070084c4810390f90029081d801c000700b0b036a81401c0c04d420105245c441202c0300c1d808150003d0741c149114030319600081815500d0300c0c0c0055004d0300c440209d410003085640080c0164409040945010301d035100390705032508440c0c58030b440d2071120000640903420600c6030702c0c070402c480d0078508421081401190140d045800c141d03070761880603000843e80c4401d41000380380198509007100c1e801d4 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 386417185 1250 386415935 386415943
    0x1060c030e0f010f14070b01030c0501020c03010b0604120510020a05030f10030807030c0f0c090209040e0a02090114010c12031b0e010c081303020603040818010c0305090d14030a0c020a0602 83
    0x1010060307558044c2003a00e00825141d0000e58030ba212442e0300c040160034042903020303800754060351081441c843c2051805000a14141c14172038040e20076490940401d209a8074101101d0803900c41e8005030301c06000900f442410074541d030003032806850000845442c2c0d00d0340f202c01503110300e522495003402c98698a5002c000112980001030901c6400c2000502090141c900300c0780a900c02c80e040c8058010982e102107061940354095060141c010640d80020300e881c1c05540307191982c0d14014081c581301c0d5000500701c2c140605c40c1310300d401d501d0600302c00b6692280f0071030108190080c3e206810319480e40304c01402000ca494076890344580c05c4420f01b0a981c8140c41e0a852503005a55440d0303803030180d03102e85190b68807000b80c107580101c1907100080140c03a540003440c890380c000c0c6a401c1e00c601d00203208080e951102446c0300e04000c0d80001c55000603030407005a420510054a41d41c109040d2480d000c0d004a0100219040a100c0802c0303955006610041c0c91910a200741c401007056941d03040141e81d1 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 386418435 1250 386417185 386417209
    0x11103030c030f1915050f0d0804121e0308010302030c310f0f0207020a21031209060e06090d031a01140706140417030606070305130e01060c030e 64
    0x1000c41c1000071804640d140e22200350071001c4526202d000740200780002088030108040b10800441409040000340340c0b4500200f85030a050703800d1000280d0380d5881014900c00c600a403d040a0301c3d108071810702c4101c287c1c2844490109a0a000c1c01d1141c0c10058811003003444224403900c1440c099000c281002d80300502e540001100d100c4029110684000c10031620f403c408400540c0c940c40004402e11038000c2c440441266000103940b5415401407000401c519042958014403007501107049540483e20f1011140c0c140c03903d549507079941846d90000e040c1310000640703020305000489040d880040341d1280220300c544212070003100e04480c19020b03540003039440c03654810840c41c100d404d540a5010030845034109800caa20b0702400b591060100d851012080c403072149440c2c1000200510311280c1da00d0501c003d140c403400c614080001910910510300020b0410401140401b050140e1402d0000601080032852946603190480146000d036030f01404da0000e043d0b10514500e0781032004568031 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 386419685 1250 386418435 386418451
    0x204170717030f3001302112050c1b06091e0109050f010204060f033c0e060a060e010b030406050919060614030d1d03010b090a0b01110303 61
    0x81014000946101d0701a8840140b50135054480c061000948408001c036001e006110042400c4803a0780d4065030141072414111688556042d00300b00115542078402c1442003000c800012581e0301011003114442e44d00c050049207181040c09200103003800d50003038a1241104155401c0c002d855901007030790360009440710040d0307400c00c28204c0280302c01009140c03181c41541c1c0021036203001640e5041c0c600444e02840d526030344d5001c501030103552341c8402e620074081d0741440c1c14050511200d11050f04400c002ca20b0300c014010011072038955107007141003e10109041e020810000c03142c2940c454540c103044801c0804c0c6450404089403c5041e10400d5060302d1115010506503991607403004001c0c080035010144921540d2503011021f4220303a0b526007018030500020607a18078244280721042a00e40046220b500800390708174100303501c96a000041070f070b0704031408a0080c048010a00400d4018000c6401050100030010301e03442c15000402000e40c00e03640d4214080081d40c1031780d180d00094807114 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 386420935 1250 386419685 386419687
    0x5010e0904120e0d020603150111031207050a03060806130c05040e0a110103060e010b04030b1623160305040f080f0303040b0a14070809010501060503060d150204170717030f 76
    0xc402c43c4104000d5280f418064212443c400c0325400003400c9400490740b1540002d0300550580d032659110400e0010004654000d60400780100400d420590000702810104440825a15691442031f00100c0051662070140e5581d0700740b920f10140f0310000520251403e071010b85000603241814171034405100c1400d0007800d222621582c400409441d4000014109a04c1f44c3d00442c88001502d910303030003400068020317a601ca00c0c510341031264150050800030030a401c1161030080c15040348034807801d1a44054802d522558182480b4528082d00500c903c002d1540c01c6c08504243d007140c020001c0d1900d00036a0b220396a42c900d0710340d9a500f80d032004003406801c2440820001600400c8158200c1070320395011840aa51f03c542090781e150403107403e00020448010b001d520300b4284100f40c003410b4285001495860301a0126008404400c801010281e400c0c120105a20b495030698020304080e2203107500c222140c500440e600d010074001c0f91052855130720311481d1004004202d5900d40001c090301 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 386422185 1250 386420935 386420963
    0x1101030e03090a090209040221011a12040305030604150b0c0f030313020904140a0b06120d0e010f0e0d080702091003020a030807140d1806230c030d06030501020405010e0904 76
    0x4d01a41080c0d007015001a024403101e0a01600411b1020f2400d0319100074503425071402c1c0360582c1c01380e0803072222440b0100400080740791000034984994407030b405040c00c40d40c1e510340704e002c98020440f0f6a100302844005000205034014418010115260550300301c558203200700f03540c0c40d200c0c03000342c502181190030100b0310401400e0110f80c2c180d0080c06070a88007040640445d0300c80c14103800e00c0f411619285503004104c014134225043d48d026101c2100202070094603104090b0100c000020618140032b40c01340340d00c07200c0344a0301c01c031403000340080d108420302e202900d0070382e059800c5141d040340f01d80b6040d00000e6104a0b4032080201312030b0010100c0c00d1462454480da1602e911100083e42c10072001c2d40d0b4101c20302c500b00190508000b50b03a80d461024011400800d03038240c540e4200c2000c2040e009036000c01c0b40c03100c0c0c1c07060005d20032413a0f81c0d541d280744c2c0d08d40c1503156100c0d000e1024402c50400400005204066000d0320844400b030301d0707602408818008215440300c0072a80104407070b0620101d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 386423435 1250 386422185 386422199
    0x18060c030f040201090b07030309060608010c2c18040204110f0d090f0816060b0d080906130302030f01020307020712031e0207260c03012f040e041101030e03090a 71
    0x750300305006040c1140300c00e40310007040c1e01c04e9000040c280c003c81d071500902c000700561845528010320014000300010074070840020300b100700018441410090510b816502010025003400c804103008103180c800c0014407550021001c0210b9007a0302c130310314104123503040c15007010448003441088032a8610300b01da0389000d4801041450400d41e01d010b12205141e000a08000c01020140c00245051942c4010b51512009448840781c07554014040007c10500003a2440155a6000ca00700c942644031180c03513460010382501c540c0041d602d0b1065800b140306254065004601407a0f0385e40c00d489419480b9218462000d0000f0350080005000461141007020b1207481c40c07000040d103106a42d45503640780481000044082951407002e0140b40c0c040426110400811690050030380c000d128420704102c0c2039200c2d082804e100001e44075076540400d50b564165048801510320614030100c2c80c101410b0a811100440c01c2041c00310b0b14040d214030302c045001081e20f001070b0000f00740984c50380c00d00b15 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 386424685 1250 386423435 386423461
    0x14011703041802030901270212160b0c010b010905090a3801021c090b0a0504030204090305070b0f06060a111207061413050d0815040c020618060c03 65
    0x250155a5000612011407882d65601005050b882032402c05030320380c1410042982110301000d02d80f04503000d004182c81d100039002c0f9150004070780450303003610840200c03000c590034140340d1344a0745d0b154030214001042101040c0007410014212600030018a2045801035440d4000d81c020268031107400c0c00054464000c903002040700111001d00045040c01d49196510603c81600d6480b00c4c0024142d462081940d0411450300d1b001030030b180d042d005102c5010050b21a9400340641c243c0c00320001240104c030341c0501d048078000c45c0e02038030800c5821524140100303036400c007580c101c7c0c40c600300101080501c02805100b902071400205034a2030004202415146092030038011125800f40081000c1841d204601900c00030380140390103c0d150b24154070017011184014011904030701d5086898001c40c0c4000392f41e40024a00f810000595280e1121700d100414601004c640e115061104007280282d020900a00981d864005031300710082c0340810640f90401190546e41c42030303007480080e40c5841602 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 386425935 1250 386424685 386424719
    0x16050106170c0d02100c050106060207050111121602010203040807120605130213020d060503070e040b09030f0703030c05040915080d023702030706170c070803040b070e0a0f05131401 80
    0x814030041b122145e80d95a402e6644691001001d038022030410041d0f96088007004414203800c1001d40382101c0c854440b1000c601446440414904c010014181103900030000c40b17000e08402d1044554440da10b0300c00c0c1c1d42070014000b0880d1400d041c8008100000681d4800007401940180340031062560b541c0c501d0025040000381c5280c076600e0f06000a480e443c14080f44028004000c90f400480c0303000d0030489a80000541101e0840e030080110041c43d500700300075150050350514011421020244040750310340203d41040300002d1a0090624048003581102001c5810000940d800c01d10341c3d0b50b00341e0700c41d418402d91506004109003210325041d102c40c5840065502d4a00100250310507401191800e415a0051030100e1100811482c8c20070a280c24a644084000d07207040c6002e86d140c0c0c801c041c502025100408480c1e88201003000c0b14006c80740a485080060f00c0b42080e260fa44030000c241001522596005101807883c0d00003041d40c600800b010414210b203040d50a13441c001d215003005643c0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 386427185 1250 386425935 386425937
    0x140f01061211160203013908090303010b0703050f1914130e040f142103011508060409170409050a02030f22050304150e040e0c010c020616050106170c0d0210 69
    0x1d91184240c50307501688503500e012405449180d1549034200d0000c1410400c7c04080a1013600c030b003000000000002203905489101d1413094903101149001c2e50350740150030741c2c031a45a402180350030341680d07401000d0350051829540c0101030360200d50110018840d1070b0b102c4840301e10541c42031200e0908406410b401074400d4020300c0040d0625114900001c5001014440ca0740018601c0c3e0700c04008071030603810f40c0030a5000246154035003005101124080f498660600c01c805001803a0341ea2150700031700741207800510003445aa0400a4660a40d0050080c4c162180c904404a85604514400c5d61301c2120fa000600c800d035100c2d403a141440b010034448900c0c4804040c03000318000f50741800a0001080c0c600030703440d00180812000740002d000111070f140a1450442448020300b0005844800785600f801c0c200f1015070140007040c1248a1748080c4083d0264900750b100030400150f200008464402024450021401401a496203200e0000c3c0b64001e541900150161418404501080100d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 386428435 1250 386427185 386427191
    0x1a16050d080a140624040f0b03010510090b090405061903060509011d0c010c051009050309090c13151202070b07110a1101050f1c062c0103080d140f0106121116020301 73
    0x30715110784516207e01e400072180003001000401950400c07002c628400906400d201c1022405c080c0b81320f41900403200614403450f200c4002c68041d40f582036581d1040d080504608102c0c58490500e10042c02301903c0c000c07030641c0303040a00001e40040260290000754010050840840e4100c0112900d902d548003c0d101030003002e03007030f4460407014490044003034130a601035601ca4045c0010000303000c900400e2944010b0080103099078903480d040e0028290750700c4905a45507503005000403644400c11010030186148000b41c840c050280b00c0100c0d51007800c03035589086100b80126445615081c1a08004022a0440c0e120203d01d6000d0300c041d2603000c02811280d0b0612a206048488052044100811180d070740c5a09000400c050444a0741e241080ea0419003191380c1008509600401444003070301d151400b0500c02018030054000981c5c003004520440c1c02070401201c00c030030002d003c0c4500d40100360304020800100710a40606076020181000b024140704859280d078650010103081207a00d556 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 386429685 1250 386428435 386428439
    0x6040e010b060c010f060501140d0510090c0c020406082b020307021c020108063a0602130f05031c0e030c03100c080108071a16050d080a14062404 64
    0x54420161070880e02200010802d5440d051515041b58100c2e04070724100710844030100c01610301001194600f44ca0600001159134840151145000454124140300d034104120290031a0b03100c0b07881c802c490700840d01013003070300d590701045c40d6030780c02c22000001c03500c3c0d920341000e011040080c00d41c04a441940183c80c07907c43c00d540060401400c24814000f0703900500308900039540d210780d28a501050a45803500805100d1a0407001060b90a010070b003810340c0401c0b4500500303003840c01440d03081e501450964803620009000b0310b4642003405205000003503e50009114500052a440710103602203103200b05150600b011544155041c42c0c554140c411801c0464190301c0801150022120070329000984500c1d1200017880414103900c100e0b680d501c84d980c20301281104a0b104c00d03802440240391540c03a401c400080c0c4120701d52001c003810313502400030032400d040c1d00040281c2c451104007408021407508082c80070b0a4000688046402000c4d0b9140017000385015140741038101b100c078114500b001d03 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 386430935 1250 386429685 386429689
    0xb04031404240f050f070302010f110a110105040b0a051e01091a01030b10080709030605010b03010e0c030411010f050c010612030306080d0203030406020706020c1509061e06040e010b 80
    0x107031107603104490a4000e076041d8001404450a4108610701c1d9243c4407074004600407004140340120188011690000504241058000d60185000040440d01804010070125500e20036800c44000b01c0c0210711011075118500305c0622419205941c006503440780e0781c88140100c0d00405009280a1006031005d1290b41d559900c0440c1600030300da03920002c50600e6654010071480d06942c1d5807541403509116030780100756200c408154411219180480c0e40c4d0365201c608445400c550360014103001c1c0b4200c0080b984035502c5c0c00550503503001341c5154250741c56640c00070380680700880e8041c0c10041d20851004141d0300c2500a4000d90303406203401d03410004205002400c6480310760244d10401300c0c0301054400c050b014003c010042052401400d040150400c0c0a07441344401400200b40650001d156001c00030943c0c15105019402012a5162910400181c00c0000c00f59100d081600c81c1030001905e10351000040034402d485400c2c443d1042e110b542c14800903102031510814103540360100601c0d46c3d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 386432185 1250 386430935 386430937
    0x8041709091f0503121902010b06070302010506030705010c0f020907051b0a02030616170c0f07050d0806060405060405060c0f010e070f090c050a050c01060312050909010f0e040b040314 81
    0x594542504107500102030480d14010b038690740e00c0280603030820310520b1800507200003659a400480740201c0450711926038101c0c010507081c03800b00c2c0c2c0860041912000d040e815403005200d040281c5c11242655220401942e054a240c00d0080c5090b00c0d21004400508221562940245150410a00342900d604007840c6029220b2681805a403111014409500d02040030a0b000f140c0a081402c4000708080000e01070038402c9121030404507081d010500c907150b01c0007120241c0003c40d02e01034803214540307070403900c4052821071040001c1019000c910300d03150100031182240c3d0001e20340c83c170341880c1c90103104581d0070804100c800d90081580d801306d10402801810620b1521001a100c414204002607800c1d10707158001d00e240c0e919044125550a4015088407070500c1c4a0900710780703031425840d00901600f401d03040100800c0e8407505412555811034060030b100321007190520496a2945c0031070302c00d010340384544c09141e014400410b020518504589170454028500001900d846180c40c1c115 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 386433435 1250 386432185 386432191
    0x1e09051e01090611090907180909060501080609120301120204090c0b040e07050301051806030109050d0807090b180402160b01180f0b130c09050a0f08010c020604030804170909 77
    0x265140c140342803c002c0303188200d4400c03840c12401d445c00c000c01580810002600204010b090102a01003080d4040350011160001c2c054010f0605c4070b010300307140c1540580400c1c8124400c521480021a08001c0042031644c1e03841480d010b0641140c0c81c25114034102c0003001c0c0180c1e0002da40f580b81c07401041c200601c2c900a440c021040d560740f186003210036640340d54000d01400c104201400140402d036945100003500c11100c1c07445000e242c4407040041d00400b00c0705402407003841021075034642507400030f10301c9104071950b85407001c0d0150f84800d28801f82c41007400e00500c103a070900c204016460107a000d00803826800c0306800c082d00c2c81c0c0e601d801e0108020707000000c00043c02d40000740604103a016402c12000c202c2028458559800041404c0c2c0c01040c0b21b032142d04d03031100314403202644514202c0c0c00400000f000740303507040d039628a40c140c2203c140c01480030b59420400400c445500014016004680c0b5a5901701c00380d440c0c1e280d005180410004080c5800700400010321243e40f40344070640 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 386434685 1250 386433435 386433493
    0xa030f060509071205060a020a120c1106010b0406052a03070501050a06050406180911191a0f1603050f03040812071103070605060f03070803070b06041e0905 69
    0x2580e05000300c901d0b103001e02c81d44c01180d0703d1044024180001e40c0126903140c120139001c40158951a0801050b02c9413540200320303e100a00c3c000030105a6075120304941d0401d030b000000e47e55103989602036150184030320f00442c8040f906c00c0000142c0c003a0029007114100b50502c1d40c0c0072000041c1e284081c1182c0c03010000360f841ea0344881c14070041e14070798442c91005003000c83d4200b0295140c100c3d14855080389901e2216460781c2c5088207014230104501c41071131040024043d9901e1110000707000383c1c0c610b0a0180c800c5561003200d8101104100c20704071540c1204450031a0300b40110001c408181011092003103080050030b109070a104401c0310f0186000c0c0b8420700e1602c1d143c41c4c40550b50300c129400207012104225400c0680301c02d00d40c000c000c540b203554120802103040d5070380c0c1000c00c0c4040c10800185401d44207400001903440c0022003e403da842c07042c0c2210364191078000800090360b464480c00d0740d260714902d00c8a80140840d07881010701074807030703000d4940b000c40441000340314045c420341140c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 386435935 1250 386434685 386434691
    0x3041205150415060b0a0c0303021e160311210706020f1306171605090303040e011212020c030d121e0e07050d0b0a0c0504030b15010905010c050a08090a030f06 70
    0x19030201d040d0180130081d1200c40429420003140c080001c05000b00303200c0180a159000500c4507103800c210101242e4003688001595441c0e0500c5084401100c4903c0c041e00054145200d5007039409002c10f942c2010b10f0b4030010a4141d119800004610794425201211401c0e03007008100352032440100904040c12500150404051070b14001810311424115000f0780103210340c0030481213416010f02224051020301c0e003191122a0000031070b01c0c43c455070b003145c082d1020b82d400010311400c00c000c071280d149110345c1d0310b41d540c40f0b805076086c0d80c0c684000c000681e0681000c0300421000d440b4101d4090200307900040403078502c503081142c1002032000f9842c18100d503101c1d400385110f0b10701042140014007003900e5640380da0503140c5410000c0040a840c80c0007040c0c0760f81c10485554403d9080d02c02660708025010224200142c65824044168280501048010340300044560094141c210740b0340e0440301416140c44140c0c0c8185023075100300307149507004a5585020010070302c1040c0750740301544550000 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 386437185 1250 386435935 386435963
    0x1701030b06010f050c100b0a21060e12030403080406140708010f080c090c0c0a0b07030603050111040509070c0c1d1e0403050a051806031501140c030412051504 70
    0x105941e060083e80010f014003042a022030240015940300041800d101c0040c6904504001988040703c0b07a02c21500820701a10681514040302c402c070064600c50b0300100b1040f0008210581c45918105201d50310300e0041c000200420300503030305d5035031140c42a400052402c504c40f00e11207400c034064440000042c14800140105142503490a000e01011401004410001000902d2103240205201071103000401c205030b2a2100f04110b2141541c8101244118600054002c004040c00e202c15075141d030074010505240c50700001214180c402c094180c030f030207946800041e1203980140000319120b90702d06400080c111342c460325145682c900034003650707071330b040c40b41d05072000d0304440c00703000202000b103400e010000e604401140c2c0307002c80f030b070070003a4580c02c00c0c0d09100e034001840c2c1003854018100104003c1e00c010400015043c000090302c030100b0b443d405405c41030060042c0340110280c3d5200b00004d00100440c11910325205200d04122500c0c0480003000c80c501c03d006440440ba03c41000c041c1d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 386438435 1250 386437185 386437187
    0x30601051611090901051308090a0803043c031b090f0b18060907081807030f02041407081f17030703110a03021c020f1203220b0c0a1701030b0601 64
    0xb03da40c0050b424002032200d030030080390544180c00c2004006091200010300514241c4408000f41e004142c0d01040c0c0e600c840d901c2d07000c43c0c40100ca2501c030b84200c45054000b02d090550500e1b00c40c00309010800000c0d08182107680d02d6804084066210f0700307000100000091041007805009c000d10301d05000480c11100310340600418208014200c06513004210410041d51030302c800d200c0e4800400d1611a0b803039280c0f03110138503511a44103071084440c0034419000c0f040c000c1130498070300840d00c00d0304c0820044402100080c1d008205680942c001040000032401d21400c3c440003610f040100f0045000c450b0382c2c2c0d1b403c4504801540511482c0350004146113043c5900540354401c0c4c10b40000240c13220303131480d683c000d481d0182c0000d00000f40074209041d1400910030441900c5064290044a40c0c4800481d114059501b086030101014070708405440030100c401c2c106a10000e9100a042d5442c0d12a079040e00c185070042c0e1030410800c030580b06010300c4110402c1100f0b0096004485034035584c140540 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 386439685 1250 386438435 386438449
    0xc19120b0405011823010605030106090605120114040e161d1504020d1b12050a09030c08031f0e07020607030b030c040506130c051305011b0602030601051611 69
    0x40544207601d03200040141c4450f00707220a00805040d41e0016429034200551042c4070100000307400c948202400202e40c1e20341060046040c1c80b50b43e1244140b040e40d0f500100c405101d040e10b007a40200480d4010000b9500d0f00e58a0b03410050010b1000c92528400c40001b403030220008207054510311403200c00c0000358035601d6500102c800d9200c02d54220f240c0051501404003040c4c00f510b000d9540000c40d20140e0000740d000a107804165001030940300903246009003581e88502100080318900804940d29240510829000c907501da00c400d100b145490300c0d4000103410040c003266501086e030240e540040341403000d00e005092035040080e030506192800034503000000300400c05051030000070b105079560010704c0b404400411240464265202c07400b0401091040700070324840e07824044c02180142d04103019040f010100e5612150751682c0700c0046800000541c030458910f0f0494884d0000b03d0703099001983c1c4560103052651502c0e41c40300540400000e403141c00d44161803a14242a89072420301c3e = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 386440935 1250 386439685 386439701
    0x1b05030d020c1b2b05010b0405090109060509071401032a050d06060306030b16090801020d0603140c061b07050a030f03021524040902030d08040209131203050c1912 72
    0x14501c013031168005011902d00c2d2201000014845084558000400900350841403121402500600080c10310f4454940600f04101040b00d0280c1000002111248005400b074215000026054084041a40150002d0010f0302c6240d10032840e4503951980301c0203401482030099078036902c690b52840c070505003a00300c99054018408150410340d0400101e08425001c980064501c0c5205020001080c400d5a50049039400340d001540007003442c0c044a4442e52004044a009440340541020748001c245d803282c1c16a0318580c0c5c40001840b000c0d0b1584d1040701d040030640c0c0380d0021110815240c20001d440700000d03a004403030004181c0c10749001c00d681072140f41460041401526010300b059040c0d10318141c0c0300c0c4104082a00244146e801a0b80c0d070b80c000c0d0702c110b074003e4283c807690100f401000340074100403034050740103402c070b680400c604504a050404180b40c00404204148144d440b044014200c00391080298860500c41100450707907813841c0c60007200302c607215984d940b0000580c4200381d0b0002 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 386442185 1250 386440935 386440939
    0x90807020d110102250b09120d09080f0105040206191b0605010f0e06030a0201050f0d0f050a11130e0621060f010b04050609090a0e06090703110d02011b05030d020c1b 73
    0x10203007402d800f402585c007401540e107040003254450032905e0204030071910300d00351251188071300038050b0502a004010403094420000c192100300150610701742c20780e0350556009400841c00c01c04601c594903c7e80a041e42c0045038501071410f041d074610303a10500d5034040015101f403940c450041114035150000740000f808a01e00349000c610744507001070b0301c4404211f4060305114001441050403010001211020001c04204010358a20014520300030101220820140340c0391052203183e0781c8100d01520604034078108030181540c103184100f030300c206010702070940001c081182c1910f2455001366540307041124200910f01c80c038184004a042183c1a40800840d01040000344000c0d11801c040703900060080e60100c00c3c946032801d040009002c0908040101c2c0541014024680e2000c5000d100316400303009205079604928080040400a5450007404241c1e0b80000c5c04003481303680e030309614281c0180c05583c103040c03480b51080d050382c1c00704046002540014400309071015803449100110501 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 386443435 1250 386442185 386442223
    0x705010c120f0e1003021b06010521150a0e060105060a0c11190b0307020606091306050601020c03160810020403052d0709023109090807020d110102 65
    0x1501d89080115000301403204019100c14440c218901070305210301ea164024000418034440130780300400a40100040e007206020f40c2040348600c01d00065002d058a80091000c01d80065041c1c5a0810700041030003c24203014940389824809500c18405105001030030b80401c15426030103141c0c1c20044160031251160000307002d800602c0c0d0740000c000300029801141075002429520028503245121303841200c0b4020f6003840818549903441c0a580900390b10f808075110b903103606041014504084509900f0480105040c80200340f90303402040d08000306006640f20740b00f54401081c2007550301c0c00d80380e40715402d00d0b40410600c40200562030f0b45102c00c0e0700850400b819503072181e0b211200e000d141c2d0303c00700c1c4801960003406951180304003a980304600b02c4007103580d12111140a900704a45089050342e2152011004c05002810101d128000700e004550b12401e000c402c50040000300c40907141010103010003001030f02e07142d02280205004411007425442c0400c002860404c9035120480d484d11 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 386444685 1250 386443435 386443457
    0x3060311180c0a02070e0108071701060b07020607030e04240501030e190507170d0f1b0213060b030406020306030610150806011e0c05010b010207050603130804050d05060702070501 79
    0xa100d0100e800c0300c0a580c000780d581096400132450305015030841d400a01480000040c0c050000652008035018030203103200b803401c40c40c41e01d400c8032481d1064490001007001042c3c018a8034a00815000d44a400c0c001021f80c4000d0124007202d99241d07424403040840c07902511041c4038a80b140008010903c0c041c0304c80072085901c03a85868200e420522051448421001044028446800600310010181c1d074098044000d651791999001e240ca8041907041c1c04100409118516003800040c00301c5a080720824903900780000c003078840c4070000c200381e0340344000b240318440c00c0d00840c000ca01887e800758a07401c01004260810034043c7c4101c11980c0003940c01c2040c074040007a0f4021100c0c003421f10440039601c1c0740044e981441c500c0c0400c0c448c9503803e0403040c42103402c0303a1501c402e180280000c02007500030600580e0381e000c40780907080c1d210405200003411140c011050a6956210340c018505065403900811040010301d4011100e5420000400154a07410010315005040910b00211205 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 386445935 1250 386444685 386444719
    0x10b10050d0f02070b07030605041a0303070311011d07050901050103061802090d1203090b0c030c0409090203071212110a0b130c0503061e1501020c0d030c021003060311 74
    0x112484180c0a003540c2c50b40e05010b40c00d80d40d541030701c0710aa0054102040d0b40b0305004001c1c0203056a0150620aa1030290803015001d4421403800812101500852804080d5181a00da18151100000306d070342d2116000c1d440003000b030461043c9400410000d00789503050008006190105801c01410949865010042e01c1060400d65502c400076003001039581d14108080340114098000140030492040318940072113030700d075010000d054020300c03111040d0786884035406280e00c0180c584410794803040c03005101c0742c0c489510000700c107031004048428059075920301da1209135076440c0555018202c032051541c100d4200520001450110019026003480c5507140c8405401c041c01000d0310210184415081298480700a4040d140c001c0c100c5103a1700d0036807402e50000c450041210428000c000126100c031015161075440a00c0580241c05030703d484600b800420399030b008040c2c080000184010000d40c03103800d4100200c0040e0f07600840d0850460511885a100c0b0102150296403518440c100038 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 386447185 1250 386445935 386445937
    0x507180204171612050a021e090a2a0c1703060a060f0504030b0c130311120f06130f08030106050301060e030309010c0b092404020424030201030903050c06070f02010b1005 75
    0x296440d1303440120346071420300303106150680b1520020f40001080e48a201120481002164000e100301c941807829512203002c001a90045951441a80390031071517218590104d0001300e0156425141c21592400603883c1c150400420213240da403050070002c2804070500780884d081c00640050f08062180442080d4000d00c0c0f4403441c8805440d403980d240114038100748103001c0300d039025405519268826103900307000380f007603450340c0e210b0307205a12041c05000d50f10404039151070004060000b412007684c40003800c03107074800109001c035131441070014028009000e00c0040c5001e40400c0d070f5400c1c2c5075814180e01a002100f02c950461180c1d02c14002c50b20240e80c0070003004002d036805400c4001c1500c03542c040d141380074469503ca00701c5000105480c0c03041c00b640701d02d80c0d116500840f400d000740c0940a4050600f0064901c800079000800355091000d035000350004100f5502c6468010302d825100d43c221801e00700103660f04000100401501040d955090080c9216000211400b042d250090b58020b081 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 386448435 1250 386447185 386447189
    0x15180109030b04150207050f0d031505220b060304120909020f032a0d1e0612080a0c211107080a110310020a0519050301120206030405071802041716 65
    0x69801300500c40907691030340640b041181d1040444a8117200c00c01000d40302e4892135038450001c1d05c0c00359444070100341100070384210382020b42a1858645012425825644034030510b82d103081d15071540c01002d072035000003148107900940100169030b0001000400107a00d641c00407070080e0040c0710100304240c1040c00ca030b030000d2460701c0800204003076500c603100720320080c030b8080d102c40800302e0441c0300070003240c10500c14031291408041192003000512000c031034650291003d008180720300c46000034210001411401c0e0f01f820321441c603241070b40c0c0d0604a801c442c0b0000300f0750381c0f44030241d80145401201c032403505000303c4090502e0700d003800b0415680c0d0910300805050848084980c0b445a1400e202200341c08008000a55a032000904050503607400036144244022421251444c058030810a8034140d862002c4901d40101158080141e0380e08054402da4003400340000010320038283d13100800403460104005601e407807600a42040d5030035000900a0103070486a2025003d03100c400740001 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 386449685 1250 386448435 386448443
    0x708040c121113060806090111091c0c0303031a010e09150103060306060e01030212010c0819020c010509010b03070e060906010309081306021f180803130215180109030b04 75
    0xc03607500d41810985402d4010b04180c0100300d8403521000000941c001d030041c0e071810000c132030711600d903104054201e4102a44400240b00140b00d621039515000c0b0580c4407281c0d040550b62480030050329401c0030107480d507008401003a658542e0b61140c0010303103800030307034260242000038082e0320340c601080c9900c10040031040303252854507118046a00070303400440a9508a8010040681c4508002008004c03e000030780c42118082400382038024140101c48015400f41c0d41e990503520341c240007a40a059005441500a40a00100c4c0d254031091140e14407810800c0008a44000403100f07050900c489a0403009072015010308200e547d490303504010750040c0c401c0c600012000954141100a40101000c02c0c008421172030340050050360003c1d1000f1b805142001c20181204205242002c0fa80791004d03044030151149140340200d84031001450340300d07140200c02241c400181c3d000071115410010301c10425900490540381c1c800c10103102c8070603030300f007800c01d800020f00b552a00c0c29581c1004100038 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 386450935 1250 386449685 386449709
    0xa0303110f0105160e0909070b031302030f010605010801050f2b020312030105040f0c120e10020f03180a15021e040312020105090102161b050a0b0a02060708040c 71
    0x568020400c00c4540e4100300740d200204a03074140402c1c541004800751010b80b000031103a440340103240ca020740c00e140c010328448004004561402c21100340c05e420080140c00308202621226025880c24803c0d81c3c0059a240000100d0f2410400054003d00045c0c205501036a08258022000c1d03c4003103d07908011024100be86104000030081c4009103c038410082d09801140c0e12401c0164901001c2c5040e20000c640520645a034410032a045030182031030000019010203035040407000c00d601041c054204c003000c1e00e10100080003440180d0348010307840b00c6002000020088828071050040143d0102400a40603044140c2c903413010213100008601c1c84140c3c0052552041c0030f000b200c050340d148229070520749403992814440d4000402035181005035082000080e00300c80b0601c21a1250008414441062441a1540c142c0b82c0c4052030110b0001002c1d00703000c0788558800c0e00380c2e80204600510140d54003c021390003400c1c410013a000c0d905111003070062000040746003a444003a070700e6001e440 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 386452185 1250 386450935 386450957
    0x20c0f0f191707030804060e011a1903120c0606090c140c03040302040513020118030206030a0c050d020d0603031b031d061b0d020d08010e07030c02070305030a051201060804020a0303 80
    0xc504804460324a003190b000b0009a0b8408044d040403d0383e11507402510204110740000325200d0030380f004442c45044608001404100c285482100080842045446428011703200e603910400040c1025540b008510803020303250810840b40a600050078641030207211504d84c1d144054120b807280c1408000d024000b01c0d98040d0076804205860045070002c00600090912504041c049030480030242d00050b4081c0c081801443d45000039801c9030b5000e4240d5145541c1c2d00e540600914400c185481000410042d0400c14007550001d000100b04884001601c1841e51038003406080d10950661820700400d0002004603400c2411100410501080181c00c070f13038150001180391240304010352555501a0780811610000205c001039101d00d03808861640b00a0007040d01c0b0702100348129520003d04200148203103100ba00900025902401110b00e11600c1c0e9072502e081da0810000c1ca8002040402c10391b01506070b150010740100070504140c035060a294000c281180c405000107400e20881c80d001c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 386453435 1250 386452185 386452193
    0xa150c030221090a050306070903020103020c0c0306090c120d1407021503041104180206090f0d171215010512041e0515070e090a0504050a0206030901020c0f0f19 71
    0x440a0101070a000442e01e001c074281d050a40d0b0700420b58242c0102856900800d20313007000100140600c00c0ca48030806614034690044010f0f6000045056a038000c11214804c05c1c0c608110b0709005c0d9203680c0c0038110b011007000074003943c5001e90038505100e41c82a5000c680094200491701c10350b480301d0100c15503500c558000300b100718102180480030214000108030a01c0b0707200d010112040000c45d400d102c6941c010303080c1060015a0a0080d610407001c101e41032a910307007040c100900b05805842986d412138662514002004007543c0d0070145240000c0b841341c00c0000d01d00307555000409480e0340c0d8103115406d0008016024048100c62030291140200d020303c501001c2031030403800c041e4400c1080840d94641152180300c050f0b83c10500810a0000c102598001d0032250000000034200b01b1a9903500090000a0036006c3c0054505000380605d00303026840b030704c00861180d442c8100160f900c20071515058580303c1e1600e0311150940110040150b02c5002040d0402c2d40c070131024a40040c40d1603800c1c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 386454685 1250 386453435 386453443
    0xc0f180601050723070b040810020717040b0a09090606200c03070602010e0c10050708070809090c0711010f091401030b030a050a02190f05060d020909090f0c0a150c0302 74
    0x201030034101100306005804e041e6642008042d801e51000d684030140d031000400c00074069809565250307000501110788190b61540a4003010b0b0203030100f5540040920701200c21a80150480400c1010025102e100300743c11014070f00080c2a800d078100025840d20100800040640303054205103504c000203003039035403410800506641c02c01400e036031040d41c0d182000390007040365008030381a90050780f822031b4640c0b800e010315202901c0389032600c2d0300d081c0d52076803001e6032640015001c03580c1c01014828451325469410425110f508000d0210b03564100d1410000619140c50a816041042d0000c0c0d04040941c004007080030ae958517107151a4040c0200c2c0140c0141c012030001325018481c040c001c1052000015400d000203000b90380c00080d500c9440203901c0d160006020700c1220090151040006041540007881c1d28036094000501b05119040000d6040800780d4014070580d1201710003d001d05014040504128000c0361991095843c04070318002d5039000c1c0c8100400d0015681c1a401070600a02c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 386455935 1250 386454685 386454697
    0x3040201021606120e030309120a0c12080a18030c0b0703060513020316081015050d0e0a060b100c20120303010f0b04050616320c0f18060105 62
    0x6410180c683c03200f1004000b5401c0c82810042941042007072510980b000c02164011080c13034000d8246801000c0c0c02c401c40c1d91200702d0400400000c1d280e21804641c2c0c03c000030022090a82d03a02046040020801041e590075000451074000086c0c10040003a0f00240c802c1c013825441308440c82070756155102034004000c25800150088801200ea000040721503001718032510b00035002c00105a00d5181c00c50303150340115641948224406414410840400d55220030780e0141e140440c900045810b203e015100d0014405a0316813104109000f0050240501d40c064102662102d00c0f66080d403c1c001e2100e21400c0b4082c1658041e8444584040180c101c1c40c0d240300000343c0128010441c1d0400d00e942e0754824800c5c8045009082c1000c110f4401003002c0720708844000b462241043c40a85001ea00320b2803084080303910000051204400f0f44849000180d046c515070741e0700280ca0340b5045100d00344981c8900c424412005000f6003c0544d403000d0040b4405101c01d0070031220356a80c1001070b90b261241d8 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 386457185 1250 386455935 386455963
    0xf0b060403050619181401060504060914090102130e13050d0206070f0509010807051615141005360f0411090106050f07050115092705030304080304020102 68
    0x1800300c188140083c03030328001d0b44118002200c02c1041540076003118541c1d1031084c40700c80f0302040c05020a0310240385502054858000040c1140d80d02d00180c21144c0c0c80c1d02a2400b00d803122803a82038802e4010f0056400b48490000b589040008030a40c0b1211201e0300821f04508025800704259205081c42505415403110480384924800c0c08013075601c1a0071211100061090740b06450b8403403003542500c0c01d071b400c182c60b00c03902e0340c84910041e00c854010854a000c001c03514041c183c003242c045070800410403a981070010303a00c9040c2141d001d190784c00a01c0d16a50041c031260402c540d450710500b010405054100c0ca80e0264001101041d41c07965044540f0001e5030501d062141017200443c0300c40c00b4a216204a03034411000300b0521481110910036400426400c3c0004020b203514035004149092065000140b1400f40046404c208485500f1600e0075030b599500664680310004854000e10200b903044400ca10080da0f200383d40c9120080c0010400c00001c0041011a4004c00c0450800800 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 386458435 1250 386457185 386457187
    0xf0705030f190c080711031c1d0d050a030e0102191101030501050405090d081803070501050105100c05030f160b04060b01030b0402130b0a05041d040302070b0301050f040f0b06 77
    0x724034249100d030444102ca0310403101850410840e20301810690840e1540040858104400d90325080e00300e509400d452601401641251410454031201c81ca80c50302c1d83e91144a940038540f00c0148444c002440040d01919242c485900070031400101c2800d10760741441c04102c840007060040b800d140c01003002c10500540800030104000480c203903070400d07000a0740d0800240ea692000c01c02525419280090645c120740041181c1901c80c1c0441c1e43d2107480000c00b80d086504000c00c0c01e24560060307006a038165500c0c4014022858480b02e000305071a150310b080c00c074940540c0c40c0e1a49a2243c80304100300000005081d103000c0040070142500389401c880100c1076440c103803c00300007810707a5080b02d6000a1406500342401e25142c4252400318400d00810f013500703070400c1c2d400c8a15a200c1c019003c180301080c0070024406d559090307560303803228085c00301a2a41c21301745006403421110707070488108624140014403464954000b84040da0100b02d4000c540940314072070510041c58500301d01500404 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 386459685 1250 386458435 386458447
    0xb0c010b0a030303090b06090c071506080a03020f1203090717010609020703030203040c0621021b031b0c0109060e09040c0306060f0617040512070602210a05070806010906050f070503 80
    0x60994010310031036000e100035103403587d240700030880c004508642c40070210310203011102c0802c0c4103019950000d081280005030f07042d00c0d4034045207018000035007180180e01c08d80315030b95400c038103020700e600c81e5100f01103c50845c20300d0740207551104001d016880a41c00a00342100c005042508084002c14500600310355403415030a00a0203507204940550311b108130039000140302c030712911075544072a4500d010381304610446d2403000080e501124002107a0300d00c0c0300503000305641c180006e020310040010b5181512030000f5519042c20000d4514506106520608001190700324000e01000306049801e41643d903680c2c0303000280c075000c3e030300054200c900c1c02c200400c41c81c1e9042c100c1c4c0c0582c0c43c02d0f00c924216850360802090a50402c071030080c1140c0000c900c0c0c41c03040c451007000d0101c9500c90f100141c01c0c0301d041c07410120b102000c52076100a0700b1140e01441112001e902c40c00d900000e4520304400c042c5451000a072000e10b40d03101e00004c000001070a940c8404544081d6074817982e1010603640d0780d503 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 386460935 1250 386459685 386459687
    0x5160303050415090302010f0e0d06050a06050a0b030708072d090501140f070602090117070e13090f03051e0309010207030917070b0d02120f040b01050102010903090b0c010b0a0303 79
    0x500300740030340d00b030184400c070f00b5003041c034024507400342282d50513920502c5103281800125141c98010b002181c1001c0b24100f001c0000d40c40d8003449100c0c4903c2600050030900d0714041100c80903031540942e510385410400c5c011040e601541c040c2d400030050825179088030303103007110322a40071a00040041ea11081e0004900066000403107400304d41e8240d942c4aa55131200400402e24464000d02501180c0100b1a00d800121160003804c8a404141072054182c2a942d0110b4540b64086030b9003000034100b13010b1001d5a10304855003c13104e00c6000350400850301d00d075440c0449411074100c081c0074010041106040d49420101002460480d00c210329201d08000c904503010750083e100440104007034020200f00c02190880450403d1241001051024a0080c041c409540f15170010750007107030200705008041c40b1100983c2d000c1c101403403648429260608200005400c10b820050440e418400030601099100340302d030080d140100001c954038400c00b82d080d801404003803030a41d0807046040000041c9 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 386462185 1250 386460935 386460937
    0x30c040b0c150c040e0109111e040f120209060d081b0618010504050d03051005120c04110f0a1803051e0609010c0f030b010c061104050307140303070803040516030305 73
    0x400b442e0002011948880451048902a40c040c11031240e042c24010030010849412011454200e0030300a4504902114403c181e415150001c00309248005010030440c2c08007024600240301455103c00e9640f8543d00140d030446010380380d1441511031468100c180455941101c03030712295244c50104203400600174503107400c401c41c1c10302620391421304031100030307041030081c0c82c861680a03020f00708d0050014001d5000700b60203030056081054220011580b5180c408800b0340c0402c41100501142c94010200400d40f004650302007099041030100816102c0e2860903100c0015650a201c099480e224101c0b150b07038603003640003070020f10074000c01071040c000d0301e00c90b60100040d1105540c22a681c0c0380070903003a00d625141d00300002c4c5015003107040e07562190340084000302d4140342910007010301d605d03600300f500e2410040c0c248070b0000007000c103d680f4041001070010090076500c0c81c241d0100000203a141e01842030003030301e207410000002d01040014001e00c0410640c100241c2a80e40d00d07410002c1c8a = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 386463435 1250 386462185 386462203
    0x2150901062309071d03060415150e0c21040606180911121501060513050a05131119180905090705100201111902071505030c030c040b0c 60
    0x982c4a00741c0d03080c101e081010014074601800000030b035101c002c1c0880c1d9540e60315125005640703000c800f1303640c250740c1840803d00480c0145489104580110001c00c12902014289000241c901d882003000c09005401660b010107240c260741c0e10b030070070000b400d50b66400c10002d066030702c88280108030810005a1041c41a520400c2c1d4400c041444d803000071045a40400014244604503c4e0303502842c6040d507154101280444160390700c0506500c0602905c2100781c0004000c81c5c40422030388101c44a207840e002c000d15088401c50031082c40c00011400241010560301c0325a41c490558480e081950340c04c880d2601264407129a003202c00d4000100080c1461010302680c00f8603c40024242d48140510350103920050040d100c4e403440c2c4810822008000940d0000f9552501e05821101c03540750054903500f01d501c003180c030511360740001c002d0030049503402c90541004590740c903080c0a80e101d0107582e0700c900e034882002da59455101c401c0100f07000d2548a4049100c0c0020b13a2590b0540100d0200c1d0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 386464685 1250 386463435 386463449
    0x2d080703080123040f140f0601080603031c0203040201050f0a030504030e10080609040c1703030105100809070b0c0709050a020d1506020c041808040f03050c0301020703090b09010215090106 83
    0x40c00d0b41c0368500d5100d50310a18040c10385800240c94401407904d02540114034000207044001481d14400c0310000d00480110745e14800346201d00100121940c100e890558800c1d0100c0145140011564035803c01010042c14005402d41c040005001c59000324101e940d64005105507640f03501c2d413400010060b000480d0201c0000b00100c0000d020f9040c180c6082ca141001ca4446803042e9981e0750038001280c0b40240156901b0443c0714002400d141551410712415080c0b901440d41e85d81458207025024100000490401c040c850070460300b03400100e074450984400002c45030740e039170381101c90320710384603e6401600965107803c080c0040810030354014021084894401c1c40308003031486c8090b80031a41440ba10f0056003003c1d80542c40ba03d0039600000d80f4220401000001c400c4a4950340e07403d07007280e001440c940300380607002d00c140401000900c0b03820300100c001303520300001c50b600204801ca83d885250721682002c25440010382c024004031410301c1000454100138902800388034082e110030302c00c1d07035 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 386465935 1250 386464685 386464697
    0xc01110f1e2b1d091612021305041a090403140c011e0e0f06060409061407020c13110d09031101320c03010308031012060902010305070c0b042d080703 66
    0x44a42240f41c683e0214058006080c580329a4034480c10b2800c1d89211080c02e4200841205d10400c582da5034030141c1903050600092103c10f03428001480111500c0440305035200411410890b0150b840074859a4040c2d41482c00801c852501d1240722503500a4170003001d80c550034005490310025136114000070001d85c101c0c09000e0800c00d00c8201c2d40314900105614540c2d00b01c0d200041c12800c181d04550781c040d206801c001109203110400c070700ca81100b44c0e80391005801003040060945494001d03071415001c00c400030041640f61101c01c481e0f81c401c0c29484080310740c0754400a4203150040c0744111072000407000a0003440281d241c0c441e00808400d10b90200e600280a20141c41d80a0030340b2140300da010088241c3c40d42e42103840c0c003103c50300000c08815580310340e00d80101d070722411030f04514000c910031130002c1440d4100c0c3c400907040e40c000800880411580c0320300100415050f01940d034009812008250360ba08010400c031010000f1b82214100103c000d000180070812202d004040e210f009076214 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 386467185 1250 386465935 386465957
    0x2010c090914010b0a0210020d0204050a1d04020906040f0c08090d0f0504051e0a06051e090d0f0c0b0f0c0606010503041a0c1204050c01110f1e2b 64
    0x1c002140c610981c0750741603801c050014080c20102000034251110107004446900703001c03042c02d10590b030180c0c014008131078010030104824281030580d04064001c002c0f1050400d04000801410a00c0003000640300700804004604a901d0741c0d8004019510b07021001c0c00f00d895141d1026000d5107042d91955183c1c460706d038081424070701c503c0303c07840000e205030780741c9240914120400001c4c8003201d44116119003103a403003a805582e0004910001c0a95440f00340e15103030711400c4050301d06d800748010710b03900ca0708111140c51a5585264070111903401203200e411390003282044514070b00340e504607910026001628504810821014041010040381143e80e1561600011a0240010f0302c00802c4050003001140e1203010105070306034407014040c3d0407401c00d20340da100212038440a4400303030740503009200400c071996072001e8070741c0d105800701e0024101000d030030074000c1d41d4030200c0f4071101c8940125003844688941c140100240242d50910042034018090720805030403c0480103000402c50000c98 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 386468435 1250 386467185 386467199
    0x20a03050a12022103040203030d05161b03051c062628030f02010b06041211090c040b09030106081005090f1203150d0f06061a030103050601030f0f08030702010c09 72
    0xd81d1048115484c03c8901000e00303844150000c5d00040d004a905002c14052a030700000c00d4030840d4030600c04955a00740503004124080d2500c0301540303c0300c0710302c0c044090b10303408030703400208803020b64404002854601d244042280010083d58100960380881a09248110250300c40381907440310005042e10100c45100390b842e840941c04080c2039000d0b03201540ca02012a010b040030081e0350b10b1600012070b02042c550001900d40d8040d40050000900000f107540a0205140b01d540140d6415507051895003003040c0c5501d618000c0d8441c0210225001a4142c1d135504c0c03c2d000440101501c030100c683c80180d04564002134001200c00c2075841c400c1202c480b0302c2150020f00302c6e640c038010308105032450f150b081c0c03902294040c2103130031030304400c1c441c0e5030000188400c14142d60103402020001400c50400399406182d10448031204e15400d010310040c00441c0c400300e112411031707034070000b060030340a5145002546010030541c040c00964011003044151038042d044401141c0440e174a9103826074507181 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 386469685 1250 386468435 386468443
    0x3010f080105061f020f011506031d10020f070f20060304171303140109050616020718180f030807050313020f0f0a06020c0f0301020a020a03030513020a03050a1202 72
    0x601d240d005100c007807129442e0307041501507402c4c10610310549440c81e00c0d81d01c86909681e6146140c0c0c04621003680c4c20420158140700788001036440c0485a060b503a80080e095a0301c0f50600c112009607a400240e4000c050710f00000ca80d100c640c40400203503040c0041c20030108060380f596454444071030a002d20650f40c9000360450788150380c0148400607070303190201403451582001c07041a01103c0c0a180c0030001c078030111661f00507081a5000418402d038146409800c00038050064507031004514070980c103107038000c50f88100381d5041800b450700d01c4400031460006440c2c0c031544109035002503042c01c1d080c007880c0c202d4814030398065140d01c2180e0b105c100048905100440e50305800602407101304005140140740d200c11044001d001c0723011038580400007800603000c0c1e4041405640440441407003400e0012150f000e240c4200e0007181000480000a91201d1000c88014205581c132800141d14001400401c1661500542201100d9443e4078003141e03116000041510451455030049490750710000d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 386470935 1250 386469685 386469691
    0x9050d0804020310020322050f010c09080307022808030c0c0a0609090513020415090513080406081f0905010501200706110c0915010906020102071109040f0606090203010f080105 78
    0x43d0080c007074990090b41da00002d400141021900c0f6a07410701c120030850245005000050003100039040c1807260254207400c41d00c01180c040300380440000c00300310f4000080240d503062501600da85400e031b58140a0b108e110340d142007840c2480305c618000401c5196000010340312005034541180ea60b45069001c10080d0350b0144500306c002801c1e40c0013800340a4484d04100e8004580c0d5a248889100c0756001900369900905040704041ea1244c007044030800c280162501300300741c6d0904117004216529180100c0c03140e40152424008604c000c21a80600703295101a4204910400c64003543c40d600040040c1c90b0a1040c0c0c0d001403100803c048110a080c2ea040000c61550801004807500c1c0003025500911791807810036060086508210181e00c80b0b5507403030700c07403441c02c64025802d1170b1900025041759825000b003000c580c8148140400204010000c03040848111890001035a0721300c0d1248031861034190040c2b05070b050000014001d6041c1d000b940c1660a0344810400d03403500c510441d4200c40e821 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 386472185 1250 386470935 386470939
    0xf24060314070c0305071211010b0103230403020a08030c03010f0501030203152b06090215190e0f0301020c01050a240504020310031a040614240a1809050d080402 71
    0x590102d05014003801d04842440d00c6400c000e824180301d034a8001e00c180700c80d00b034070011425125000070808028130604da4894000d09042002c040c0810811114038044800c032082c44080c00e020800b0300d07000b0010403402c145d20200c4036542c0e1800700e130001040e0f00284600c001042d80d04001107003a41c0203000f80c0c1d201d00c0c102801d8200410406040040340d200910170785001c280009da0202d5400c0e203884014a00383d000d0500469460103d01c1807240c813240700b04d2a1903d62009009609940300120224040e00d807040c03a01c079201c0c0380310300d000490314415501d44903415072002851189100c03042d00041d01c5611b251208002d0217240c01c010340703101d20421000d2800051011024000c1d8602503000d1600020a0000b8205e0540c80f0341d204281c4102e40441c18103078208540801c8108041c0340188220b14140c0310721031107182080d4028022081030007205d1050a070100110300d28588420003680020500308010a81801404020700010201d00b4420340f0305001d22004020744502900003039000d10341c0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 386473435 1250 386472185 386472221
    0x7120308190e010c0c02030c030303040b18011103070e0a150212030a0207060e0714011b03120b0a06031a0301050403050417070302030d03020d1802090a020702040f240603 75
    0xa4000c04081034050a2034140c2032507a58102d120780a0400d00c00d54540001548414445410900400d0f19000700c540c07036070703120b90302c10010000060450001103400c041e1500d450303010f840031895401c0c00b4110440016000e82c5000c03040001061384a41096040b003c265031007103119407a4402c449125039816400405a8401c0794401c0c070000c80d8030003e607444041c944005007420420707560031017580c00e01c000302d40450384950b43c180145618080440d40840003400d09c101071400390244407030b00c00d00c1202c1c00f401f403242c3e100b45428031200981050a00040003818080c1480d29606c02400626107001c0b1084044206074844007507050511900d0f00480d0103460315810149450242084800e0500b500307009400385680002c0140c03001c21001007440301e15100982c0340e51410348000211454180d07c00130307501d13800282001580790801c450341c1001d02d001c405030781d400940c0003040240000b114429103d82c90483c004036030f41252040e035419030094011105285503190001c8007640d42c003210900b0b038510 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 386474685 1250 386473435 386473441
    0x92103060b09120f0f010c11010522021c080c0d030b03060a1d0708030307111902060d02091201090b060922060608060a0c0f02030f09060c010603022107120308 70
    0x98204045401e83c10081c040750220440d02e95020b040a08041175030940380c0d1200322074020b168000d00340303010758445e0b00d00801c0546441c160b0310307845860060103000300401c0340141c0000c0d034031210000c043c01c48002e030035030765582c0719071400d80c0080e4001141907072180a11100440c01e036200e4007179002c00c1c140c001c00811240e1a0411214001d160280301c40806e0300d5080205042d040b810300002000f81500d1000c1c5880c0d00e010180501031400c2c46a0664030b07504010790056208034001c0307074141c06035010340c1c4c19500c601403064000e0003481882c0b45240c0c48440c0da0342003980298150480e80c01c0714800da0451105440300000d20000c40c1d81179805031000760780008020002180890b0382110306004403401b04000d9034408800c0e0601c034050300c2c40041039446d1404d0744511500803502000c00d044500c0190b00c4c00c90484d00c2d030056401402402842034500044114851209400a03405150010051600c07031400400d8400c1221020141e800d00303014a220008140e40f41c510001852070b0192031b46c40c103d075 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 386475935 1250 386474685 386474689
    0x309080912010209090a022a03180f0a0305011b0804020d030c06020f0a0c12080c0405130f020a08100e0601080f090f0115090f0b0d0212030d092103060b09 68
    0x4032a1450000150340c2440034042990391017050718058980070f81d0042c0e40e590300c034111452001c80c3c03009800b5241580319408035a91400406c403141103d2a03004401090140750000b0500741e41d1911040d403010203001c0c08024000c06500251010444002ca921030219151055880c04070850b4003030750000000100c84e001c2030044440d000c00317034031907000146440071950402d0660740080301203c0001e0740c18030031074041207180c0b130b100da00581e07250a0002592402001c10200d600c6607000304c60042c840038021650740c03151600705030190069164250b4480c00d4400e00249076000485000f1031501514400203003c1403c3ca00d80c500a11060359000c100f07035250f00c1521507191000e07211602c140300350a641c164104003882a000188080c1850252062605250006403103494610405c00391510710000e6407a5942c045483c48280e0580c1c942c203008000b112468107501400302c041288508006a003020000030040041114200c0740359000b1006908200704d00f250301e6409040d06400c1c4c100001c250345c3c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 386477185 1250 386475935 386475949
    0xa1502061b07020922080a0e030109081e040f0308090a0f080c010c031707050d0e011a0d050a0507140103061707050609030304030212030d0605030a03390f060b0103090809 75
    0xb0360500c2401c45c07640c240a08901e8880582001c1c0d5990300040345210700541c0c04085404106c004600078030007490b298a40340902e00c1040542c41c07214600200b0041424042030554004084512800190300e81d2424070640c03662041c010148508040400881c04003241c0341304406586c10100101410a880401510840c446660580901910036244030403a0303102c0308081d204e0503540d030360310b901d81d1204081001a0b6110700071100e11a414050b40381d007050300c3c81140c4d40304500d04881e030740303400381c42e5007011801c2c8030001d100070386140a102c0e0003040341d581030403017400003400030f980030003a40b6584d2215003040b40150050038219000000200302d82c0c035051001d0100e40500600b5070b0f00d4147e680d4005030000e0b1400d807510207650001308014120b400944038420042a0540141510a029503001420340310100c440c42c1c01050000310026a075542d194107459890b00f5854100951521800c04814018282da4211038040c28498040f07150f502ca030085c0d86071161300c50341043c00d04100408200070 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 386478435 1250 386477185 386477191
    0xb040308130813031106070807110f09010801060e0f04200a0b12040b090a05030f0a030f0606020a02130c0e01120e010513050606010306030305090f010c020a1502061b070209 76
    0x1081e01c000c080750086a0070030b0060110103110300007485403602c2c3d450810840703081481201c0c4112818400c202c0883c07540703001c40b0020741d403100c01e40700842d11003400130714000c1c44080b5140d000305601001041a41c0154805819140d441d04588055603400c402c450310b02d0703c129801403484030a42d0540c4009003103801c41050025004250b00210f588070b41c01c90f900f0345c00562504200c00900802d001c06e01411100c550b0300024054007401c030480701c40d1100b51f034030322410100c0c001b9180001941120940301e035000e10700c0c0700c203010b07000d01c81c0980c0c4070700c003c0d56500c40c0541a80f040e444540b1901d090790a6108140482000340c4480307002e001e20074019588083c03482422000943c46e135426509010003849843c2c0300d0002070220001510050422a10f001070041c4071a061601d0f090041c804260480c09554286104a4410010152620040380e00c0740700500025041248540d011a0b404088000800b0160302542120480e035600443d40341012112460140004402c016a4000d41004400254 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 386479685 1250 386478435 386478451
    0x9030f0a03050603071e0504180c0b030406150909060b0a0608070c02010c120c05100e10050a0e100c02150105130c091e14221a03030c030408010e0a0b040308 69
    0x1e686d0380c5441c500e1100c2101d40c00b10701a0340d0003403401d101500c1c00d4821080749100c803584078a24200301c2d542d003040b0743c803850043c21003100e0003000180401c0300d030b50444440710041200c064141d90b95190000094031031814216013460400c40f441c206030138170b21001c0d01203800030b17038550a09840301c65041c0d5508e86803001c141d040165045041c40810113180c403c000259061343c580460f1004e07410604c1c205151031040a08480c180070b04001c01d4440001c00c0040100d4082c1c1c0000e068844204190062440401c002c400e0701410300c208480f0f030b43d580d000140c190050740035a400a070b103061704080600001d00070540e00c0902046150320200d090b074059008000142805000c2980702c12400489803c03072462038560b412010342c1270007024078955103040307032410568440e80f0503441104001c01502c07a80b042c4021880e5911074148405254005c00f10b21003101505484d682c003041340c80e82d902c80d40640185410396003031625032401072000007030703500351560810142d26041e2aa0341e011607a0709005843e0746 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 386480935 1250 386479685 386479693
    0x90a051803040f0e07020609031c0e010c2007060503010b03040602040e010b0301051503090c041a150405040b030703080313020103060321031506020c01180b030906040b09030f0a03050603 82
    0x4108100200700910107030528a44902e106454042c0007880c103200203024400315082681400740002000082d601d900d015140300070f41414482203c0c074002c11040c041400c0e51340c01c01060460080d0000c0c2040480c0d0000070044104d00055009103030750304414030a9000050781003004001200e450000b03541c10500c1010b015191070365507501c000d000402038120070303000d14000004104a28211354158140d1100d49150390552400302710320740c1c50300b012100c094080c64680f0194046a803000c1c203803104a01d002000c9201340080914805e50b00d401500641c2c0c080c43c42d000300260740b85070000d01c14049030b5112400318a540d0f83d0000b0304110140c1242c04a05050b00d07880007000184480c01c000969a003e42200b40c85910050801002c2d146102d429809104078140d0620160b039001c08c641c1a0a24203080680452102c1f400e410749a0b1420350000c41100004810300c03a9098021425500650042c031010501ba25800c03e07054a0348240c441c0c052241c00c0c10024581742c1c9000b9000300340d01c188010181c1d = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 386482185 1250 386480935 386480971
    0x806060909010312020c040c08010b0d0f060902071e0803130f0b0109020a1b020312070c0e13050d1404091e050406020a090e0402061209030f0a020c0a090209090a05 72
    0x106145100a8204035000d0844c0e581034080c10758100f00340041441d08031070a10100c520310401030815801030080d4003e42100090b8640001c4540e0060072a000403020200110340d56942000003e4000290456809807400044070b4054914007031510308640203284146503440f48020b4460341003403403c04030307808640c0d8a000c901240782010002d0080c01c00f840c0160f92100901d0004140014801c2800381c6520125001b00140e240018540c00c1940c000c0f0249903525902c0c207008200341510303486001800d0322030040010341151305240c154140c0c071034412603c0c4d5880b030007002d540e48030a8041000e02001c1c00c0c0010049110250040001040c82811030310a8500c4110f42900b50781003100d051303c2190f00054545002688901d1090041c81c802203402c040d030400384d0000d00d091148620a40b0071052034004144030725002d004503800e110780c80860303603558005180c010351102c1c2040e4803d842051030341c0001031100042d000321051801c00a10110040e565810001d009010240207007200c1801ea101c1c13 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 386483435 1250 386482185 386482189
    0xd0f110735030a0306050603040b01092f0406171b090109150905030d0e011e03060803030f0703050708061c051f020408190507140316031101090f0f0608060609 70
    0xd82680750034201840e5509a0958098140d4080c3d902c640d0044c1d000b0000c00011800e0000d00c20b046d10046900450180c081c00040c80c044040000078081c406050940220040104070041044400549452000c40c0120b160704041442c203c51000803000c003010380710708841c010300013842c41090505000f8100d0380c0b038455a10000461500d101c011424280083c03080e440c04108002005e0107a103040788040b0311080000f01000b04a165141500c00042400100306009810501c007401600c02102d46034540604a2240d403031095035000042440d02000c1440a0301c10000d0301e118200190404480280748241040c42c0d500d84042900d8030700a550340c21540c00e030800104404201d5080d809a1120308040602c0d0500781d09038200ca4001040741c0c5201d0008001054083c00c48142422000c8001108008281013074102c00e4a00c1c0007088100000c400c02c04520000d0070010400c0c0c1c0d503036154903101c40da071109490050041c550988480341c0f08101c2c50b40303d0103a556101348050b0203982400d0781180 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 386484685 1250 386483435 386483519
    0x70303111e0c0a0b04050117090304080f0303100801110415020c100c060e070311130908031006030b090108030319020903071202030d030b0d02010311090306090d0f1107 74
    0x218401580c10440300c0c1445883c00003001000703041070344002e42c0782918100010340300d003040603a0040d110700700c1c40000300000400e100703843c0200100001d550422507060802c03030322948111780c00610002c0d128804500740340148904e8a40e1701c3c000407a149060b003020040c503540d9005005200842c810310398007210341d48510f044441c4490f17803500c0716201e4240303518280060707596140048019512000341080414000611490f80030410b0354100d64049200c0a44400341c440c40401904840000050140344190450341d2002c942040d074041290700d90800400030300550030311510101c0d51003031021410b6622004025146e021003031000518000b020000700c0e041c141a0351120903c12403200c11002503040612000c800300c1494a8200181d58000000031900c0900c5032011b0b040507070701d003241e11003061404100c540040c0002e08841b12880d00c0100542c3c0c40c80d41324040c10000d00840e1450903428081c1c000854100d614501402d409030400200e440301200c1d100c0201c010659038100c0205c1c1d80c0d0301e2a = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 386485935 1250 386484685 386484733
    0x15191110090c05010201110c1002090111070b04030c0b07030804140109050f031b0706020d0e131d12090f09060a0509010303050a09050a06230d0c0314060405060307030311 75
    0x2c61050b0419140000290848030b0b201c0c201500c2800800800d0702e06400800c1c80d1165a000210041e12038110f000126603840714840105050310800d0b9001c80d60003500d20180040b00d11400c08510041d840d240300000600400c1401030120362202c000c81c000985601c202c000d0a50004000140b820305a00c4561a000300000300a002e0703000003c804040b60014040210381020442c0205100c2c1d1410800035554420509240108030320f4910321201c40d95400c1e01400203000c0400184090038404a000d000c04016001140c000e1054401400e00c6407005816142005401454000e40c00340803410f101e4002c01c02008035500181d000e001080994400040038081d600913030340d99480d4508180e0140a15046412140c41941d800000f00301c00b0764010031107214501141807150740742003a91005800c0380201c090f0514913500b00b020107800b0707a6142d401030100c0003099001c0ca00c0d9071504020322045810640d01d441e0141c00642c420304c00b00e40503019580c1907406007011610929224115000a401c0c80 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 386487185 1250 386485935 386485943
    0x705060931090609020a082b030b10030c0e0f1c02030f06071701080a02130b042c010609051e071106040311150c0a0e061c0204051519111009 62
    0xa00158017542004402040603001c0328004001c07250740e5070100c1240304007009032130619400d07501044850910a80115480000190081740403440030000500640070181e240400950320104040306031a04901302450140301070402640174103aa9a4410020b2102ca02a6094890710039900c500301000c2155600c81c4000303940c0c15401054030380031840c541c038040e401040c0e107034090740c2107802680c1c61039084500c0b9044504000350314007580f0042800f400403600181030305c0c07030808030b1629000c04400c10b8180c41c1c2d031004004c111958a40700e4050864405030380c90544604404007004075803c403100d0858200156080c4503101242c81078601d40b5020080720100c0000f1551030301405003240c104680040383c0200c042111880c81c2c0000d100d68070b40200c9000d07208010307070640b10007032644072201246c0c48410050107800314280e4207407001004e13600c90710610f80a601e6829501410b07650110650b1a9035114201c1000b02e0a00207104480703001000040c01c00c2d44c040c0c482000c0f03603c40c2d80d114103001765104e = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 386488435 1250 386487185 386487191
    0x3050f070201050f06011b0b070504140d080a05030c07170a080123010e0a030c09020c060907061d0609180a0f0204050f0d1403030106090807050609310906 68
    0x85805415000d021442960b0405040c080000c3d04c00d40c074140d00900c2803800f541034220083c00e120b208114504060700f841441401d2141c1e1030b03801002801a00d0403120100c140c060001c050206070030f03115502030302030182407026500041c030420085070401f02c40c14055041c00c5842d107074031700d4211030b0303440109401c44005100d00e980d540000910b0f00501070104a94004995801c034001c201c0300520801341005002428200b003555002c1075400a140c0140c0c00a80040e110070039103000f0340c4110178181c0d05c0d1080b480040d01128001800205907642c03030b500c003603030810005225041e00b0b0a40da40258002c006102443d202d440b41c2c03401da8100b584442c8580800e041140d200c4048884000f5100d403214010041031010f5180e98900c00c0c950441552100590440c9081c090300900c554600f000b00e6000c000700008100c1d41c80403100701aa10088141c03142d141e03031601040414410150881d801034100c000170826440584030a101c3d0121090368200c191440c410b03100100c6014550840d2806e036 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 386489685 1250 386488435 386488441
    0x1f021b03180307090c0e0d1410151e090c21090615050a12020409051518011b03051302040501150813111e090c0a0f0e15160b01060305 59
    0x150810840f0001d10025000300041d0301405801011400082d480c1402509902c0b03140041080d42413034040c14941c2c1c10191740c0070075080e407000c81c0900f000001904410505200201c0c02042c02c4007903840b0340c03c0c10102084083e1804000a018124641e000d1081c480c00100780c1581c0f2880c2c08882c0c942e800d03c1c040014035000d0b13901d821001c448460000c1c8410f1401001c042c0015200d02012100341c6102c0890040c200341c172840000d01409080100130701500038680a02e101c04490b002d101d02965192a9000329054494007803400c903240c880072a0610200a901d686206010b548016000090400108440c2e2f019030089800e81d41c00380d0186d141d402e41da5141500d0785034011881500210108002d03450315200f603e0340081528641020b07031003422550710a6001c241140c03008000581c011300000390314501a410203c183d004140c40001051000d16541d807494412401212034403401001d64100400c40c05030b4403500e800c103501d40d100d14500c0080000106d28403114003402044255408603141c6 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 386490935 1250 386489685 386489689
    0xb0f04030b1008031602060d1a01080702030702060301051507061d0706110c04320a05070201090b0106211e060807150309061d0d0801081f021b0318 65
    0x1500c01001d150b101c0842260521101d0300100445040d550541c0c007414030300d0700c1030001076514447c0c205140d516500e08040c07519070a8150552072090b2500762207411480d69002416a00d0384280c2c10002d44c851f80c1080107010a04e4141c039010051070095035050708044d4035503107132011034014080c4042c840945000e55402e94000700a03a0700030304081d281080740c1d92240d0815076034482051540c10f1080f911000f600c0441314041800e02000848403210b01900141101800142030017558686030341c608050000b40c40324014001c07000000d038440c06c40c1c03010b40c6c40d2010481c2c9065840490000444d0340800c111010051800342918848030016840d852503c1005039000302e0700d15602000c06504110070821110000205900c0200f00364100070446015629200c0700030903107001c00c4e08000341e00c850032650714140000c06290444a5440f0b40340c040e600e512595070380f903071020003a056039258840c00c02c2e0403c030b042d00a803040171008281c804c0343d250038140d601d003590041141d800340c040001001d43c4080c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 386492185 1250 386490935 386490953
    0x150f051005030a020903160306020a0206060d0b060906011209051501051909020d29090a020c030703120912020a0303141302042f0705010b040c05030712060b0f0403 72
    0x6010444009100044110029000b0701000b801e80352007590228005d503140c4c4040c802c106045443c1c40120309031075200d142a000030b400c10f15074a401441040c0002d8058200600031003a200c0d00035180c0e071459074410b010002e29200003000941000b50001c00203459044038040c41102034800e02c0036090790103107142040460b500503030090384290440000259403003007a40f074460136221285000340e9a801500e80003c00361103500c00d4031424400259000300f0140108660f5a06854115520300d0b0940702c428140c410780c0203107000c080b0700380c00400021001074003030505480c0e0038140607004207242c0c9883c3c03500000746140c204a83c001d41c1052040e60101640f5200300180500c0504105800d800c1c203130042c90005035402d030002d010f2590340090f1090913599400c0f0105194058000300307085110070311034046503080520200c0e42982010502c00b49440e15002e640403283c241d81c0d0381400d65580e800c085a413400c101c00da000101340d860002103040d4040c03500921118010f114140d039213920310700d000090 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 386493435 1250 386492185 386492189
    0xa03020a0f0608090109032f0a03030b04050604090201050901030c111002030103030807050301080705010825020304050a050a1202010318080d0506010f0804050715050408060907080c0312040b030a0f150f 89
    0x105d91402d90008000ba801122403c4180c14040709035132040d802070031035440c0160b000d51062080c482d6155000400d40d0582042d00403820580701032042d0f840da00248002c0c0c03251004002d010410a1282004d95442a40074001420395803600040c07130100d0240c11800e00484e00d409090f03041c2c0000060003456000200c0c00c6c0c0207900c41c640b00d840d640c5809050b90311040140241410000036501140b00000412250111044421240c0000b441428406952544148512805864000c80001b06481d10304100022030380d5140130200c03044091703801140101101480002c29191501c02c0c8008a02c0640250182030300c00f035000101c505101d000175003000007902d8503404004e421810040080c1c00410340c2411202800603100b0004580076007a10680281d8002c03030f0301c2e840f903c1c0400c800c1c2080003601300c085a01c0507060700c81d41c403d54801c0c10b4072640610030701481010200010000c1c4c40d50b43e0300443d070100e0074610000711400d000d0038200c16207056403400c000d0f01c42d10b904203000403000c3c1000100 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 386494685 1250 386493435 386493451
    0xa030617030c0139030e0d0806010f05041d130c0e01030b1b1e0c010c080a0609020a0219020109120303020c0606010206060f040504021c0302030a18050a0909020a03020a0f0608 77
    0x242012045400c920001d2143d00c0788242c0000c2446000c02d00d000350810400b51000c4001c0e203c0300020503034008c3c100d120032684035001480084c055403965016000701d800340d412140e440403a42c503805910785a64600903101001240943c040e2102140c0c5507a020703030140a01014010003940745040000101c40040c20481c5068900c4083c02d12904418045840044410786000915203a00b120048030340507101c050481c82d400c2103030300c031600c95000b0b4450380300e0483da040c10402c498490035064124014102c844025070320640038800c2d001086000c0035902441450a41c0c810b94680702000003003c032010085000c20740119401d21501e17401d0004550100b000e00c024095442c044c80003402d94280e1440840c003c954410104e4299105d444007400f02031b0362040d0b0810365000c5231400a540368003450000c00022040d031090580c919851103042c2c01c440c0002c0c0301c000302c41d0070140b40f080104001c0f003040f41e105652400c0000161039054044001f0403048150705245440c1070805424440000d11920b = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 386495935 1250 386494685 386494721
    0x1150f03020a09270f0902040f0e0c01050d090606090e0d020609030f34050601060807090b030a0e010911040c0206010b0708070213090b0406110703140a030617030c01 73
    0x110030683c04041d80040300d0581800f50f00c0705005000000080d04451800c40d04503040942c110b00c4507845030441040c1c50f2082d5400c100f841c40a420b80800c60f000c0c1c0710f81910a410074004d04140750711403409081c001e009580b00190700709941c1d484034101ca42c664804010181c9840401c0329a0b641884103402032159400500418a48a0308003601d9100350050003404410105002c0c1d00c0d025800d08800760400c02c2d0140510803e00b03120249030b1000f41c514200c43c14410a030020407043c0c0310f04c1c00b8502072607007503c3d0100b03801d00789015001c01d504000e00182040e5903a0715280c03240380007401040540da0045003054130604800301440306441b00c0c3d4a0701d10a6500c41801000719103480342c1103d00e103a800c56102e5494405510002d054540034800c1302c3c50700c9003031054072002c0c0110400d5050007207100700c908228001d000103826200b4001c031003000d4003103400902500f040d0380000d0000e082d2040d0034900001c0c4e140d10b07070724014a00b6220042030805070340007040040701554240319002240241203405 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 386497185 1250 386495935 386495947
    0x1b03020a09060f050f03040606030b010b070f230a120f0e03030403140102120406020301050418050604030c050111070b0f09120f0901050f3013020118050901150f0302 73
    0x54000350003441800c0400004202e0403191a1044003602c170003009014000382d50b8100780c01c160700940a1804150307880c81080000003403130042c880441d00f070381c1d40c002c49002c007050103174070340c1840b8a040d90070448841c5a6a00c403022581c1c01840400400e078401c5003850002010303464000c1194484041540078002140003081c0d40355000010f4504803907114201100d0701490380c06c400c0c06400f59405050203038200c070b010f02040107883d130040d505035982030300c04100d10094560056100e020810020742035400080210b00030901c41e20f1000751083c00f03140040303130190504440104c0c941c0310b10000d41d06d03007a60b40240b11b802e9050b6580580c0000081d002050f14a003001d03441515486184032044d519400040c40348500d074020000d980c0318811400840f600d41c407401440801003c03a09801144110302060781c00700481208205500807901c03072031844c41c00da0280d401912a110350442c01004440803103400034890792070702c00c410301904d05480c441e03501c1c411020303000e07124600c40d00c482401d1500610030 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 386498435 1250 386497185 386497187
    0x150f010207030816050d05030a1a15071703070507030801120308070c0c08070914070315050d1a13032d08070509040e010c12060b0306060c160602011b03020a 69
    0x800081e01c0d0004112959440100390507629681041d4004086005944642807511f4200000c7c62060b84060000e0102c20a20790840080800b00c0c803845901c080400003002803d18180003510500b48940c0390100385a0b1840355609036034000b100c1540000d03100080e1041015400440503005203441c01c030310b130a000c3e11075802910700a402041c0c0742c10072403102c1151090041d420f207150b00822038078059030b0303e041e02d41c0c07040c1020705070b2454a510054800390121751218481e10074203131407a0150603031920060070700041014100c41443c050307508014050f080142048a0280c103800b4030005284902082c01e107160142454181e0a41c039464501c080d01c00380b105080454040d0142841460105c1c030695600209580a0091031541030f000781ca0064100c41009055000503049412500e038000c003049810202800d44030280a042e501c0e407010b1010a07007904100380680a011550010340340007c80c14211000480c1e070f1541f1100040c0c1d100e0704028a030031a55858030000b4400741c0360540c036151160780 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 386499685 1250 386498435 386498443
    0x60403051011251205031b0c010f0501090203040507061e0513030803070207080c190509060a030803100f050405060603070f020304080307051e0d091203090914150f0102 74
    0x390360035140c0442540d03810b00c580840714000342d00740c080d401c0c03210140e1402d000c030070070700740f0032203a404d2012089503803d8028001e492240320050b4200c040e05005081010140c0c0151481c11362543d2609101c1b05019814040c9a018141c98100103840349071070305104d440c0c08429888801405003003a00042c54440c0c540d4944180e0400782811a9903429040842c4900c0c8541c0e4405011008084188440d2941c0419080100c03281b4a049072885d162003420045103041058131000c0030206498100000d041400d01ca40c0e010318002c0c85403081642c4c0761100012a4811155142440e000410500503d052000844050001031f582008246001c1c00811180d202c0505000188a071a001500c1031501c200115006401c41d002501e4607545a8940b10b903580c6149941014020400d166801080c7c100003100a460000d55581c0e030503141c0f4103a1032105084902c1c0781602004840700d0046494102806074003c000b000c50010040c500d000303400c4020201d04440301314801d0b60141070100c009da074001 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 386500935 1250 386499685 386499703
    0x915010510081e010621050108150a02090307060903120804020f062d070303050105030606030d0f0519111504120e180a090c0b07031403060f030111130506040305 71
    0x424115101c0d00c800e030143c4020034940040d0000b40341003000104000f44e200c2c0c4140500080c0380c504014001003000503905a600034068000035502c40d82c0c07a07110b00000f4045081e0008001d0707100500d03000721100440c0c11300450307400c0903003c104254010010000c0001da400710b08d60b494585504c46040c10f03070004400c455040e1140d4810303e40803e810b0740188012400000e4854551010030f0f980d401c1c001c48541e00d8000308400d501103864200001204d0901080292103000c004010341050705842c1403d4031744040c0c804000080020510180d4105207005010120303031651500e0b01c038000c0a5075201c41d03140c250400b450201314007920703082c480010020058a041e980150070502c5d695003034180803070b81c0420603822043e003011000f01400740c510100c0d0710410700503006140c00040356480d000c01e490305108080000b4001a240a810040c001c3c00d48003464026500620100c00112540b0000b404d40c0c0e03030b1340c212181c004000a40d5290207140e10b90128000d11007a68400d051500e0750b141c80c2d4072400303a0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 386502185 1250 386500935 386500937
    0x10e070207052d040c03051014090628061d010f020c15070c0308030702010e030313030309030e0303030f19092105041511010c08060913050319020102030915010510 72
    0x3c0800e41800c10019000411010160042004071902c020080c0a0b26017030703480746940d02c4407a00100b0050550022009408809482d140f1203450315070900409040848203068080480c04070300f04061810311040c0001d000d180c4c2c0e01c09a680004080b86100356803c04e01078180700444481c1d007005500409c02003500107084032400c1142c00420b01a04081c410b040b40140031000160000c020003009901440c090101c65008000c801c2807085859a24841030f074001c82c00c942085000800a44a5001078031000e2107850041c8000d5201400702e4595042551000203e180500420052001ca29052540740650800130b2061b000c00303459054003800d040c0440c1c980c1e0140b0f801c441c8281ca01070340c12a00288070790001c480000142c0c2000818800144840460039400c1420b080c20b228032410307100340581402030100c0010b03203920144035904815079004031003500041c40001d40302910040c040000c4001500007594038076280140e1810300c1020052004419400d0006005035255000040c49050305 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 386503435 1250 386502185 386502229
    0x5010e01030f06121a060d0f2904030807030e03030105060d1a120d0e150f0307110d0c020a050301091707060b0402040906091b080c160c0e010e07020705 67
    0x600754481c0a050f954000340075546460080e0004c0140902d4042c4161030402e148450356100c46007008411a06080090803403080410300c04041441020340d4110b090003c01e201182c1110032610f0b4180c06c00807a404e40102c1c02503010408181c0e058024004500141e0019500e0742d0304140020b40103000710240070400c20342d0b58480594580790502c0c0061010700003400101d2101c81c03503d9665441c2001c102e001c0014415991500d194280b04442d42809042c5005c03d0303080c01c003c001c03c0801500300078015820400703002010340905074140911040f40c00c0c0c90340c0d0810299201e00610220451590000703000303a2500025401161000072040c2c0706840402005550341407908042000c1c21840030b00700c1e400b0b03100050001d04071845e980050210755508200380f100c080c6601d00f40f05240004904034020610000c0020032a0001c240188426036004101d40000c008075183d0b1310910615800600e400103034100180b01011000111580c0900c1c1403008000d103a081c900400c075000b140141e6084014a = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 386504685 1250 386503435 386503451
    0x90302030a0f031d1e030403021014090d11031506100c1410060509060f010c030807030f0207080705060c03090a020904021810050415030f080903030910020f010f050105010e0103 78
    0x8804e401000120070803404010800c0b0100003002e403240c0e0505400c100a000015801c800c0d400d0102c295002c03250020321005241481030b4080c2e80c040340c2400c0208a000040240c490b00d90303204560306107500e000b03000c200c11001400040c945442548401040311094074010000159144015014100050325022030b00340d0f21407134084507604581d401007100e8000c2851068504805600403000c03180c00301c605c448180c0f900018030503910041111580012102005440405d0184070300c141c00604d03d01e400a40540d114510800301d800c81a000c50345041c001032a40e00703015081000540220709440f1840c0740d420800f200d1590f901c0d003281d00030f010310f000e64000b9040d55554800ba00100784034001d01c460b1803400ba0703030740341e0504d20f14001d061150380784c860040d1803410521100da003039030760184052000301441d80391107600360059441942d0510042080080d50b45660310b00ca403c1803000e800405081c2010904039082da160b881e0132484c070900d01001000715030b0303100014894211080c203002664030 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 386505935 1250 386504685 386504687
    0x20f040b0f06071a160f050703020a1b05120102030405060f2a0d050109050402030708030a0f080a0f0c0f030e010c0e0108062b0b1510180315090506070201090302030a0f 74
    0x101e5181d600e4145050600c0170410519035160b02a103040c0841d03524101e0035605920240e0340341c000c0380343c0680181c1c441400d1000107590410200346075000910224802680c1d040001e82d04e01d0344100011850750044144010003100708212a0032442d81290070003a480c0821605002a10b5144e2076003c9004200302c01401400c5002120b042100200e0144610b46c2c4602c4018080d00040d54120300070700c19558001400c9101100742ea00e10511590307046442400300700101c0702907501600c4d2a40e9071385e4030010300c501d030201440b408603803a00c0e64840f01c0d01c629140501400300d50880000100c585d04010040321681e0780941e81c036070406000d08051442c0e4551502042225081d428249030380c558944910074140648007070440d015100309480d5520f0f13542c9004120141465030f125541144000c282100c00314090016405510352100c84514219aa40c0794a660650100054030101d6559441001441428002c00b584540355000a2103202c0503964025960b10514800004015041c0c8440c4441 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 386507185 1250 386505935 386505953
    0x50f06030a140c0406110c0619111c02060a0e030304080a05070f03200c090402090613060902030709080f060105040f090812090c030a0f0f08120a0603020f040b0f0607 73
    0xc0039040a41203481c3ca407800903982c8a0b0b000740240303804215030311a07028401500107031411f450200a0246410000d06500425080e07410307000384018480202c103103182c00d0700d041000e01c2445041c20348034202110201e601a0070048082d1410342098100a001d1a0400c4004110380c0c005a100da407045e40d0300e000f003904980600601c00003c1000c0c1c1c00c8181c6105040d4003450a0450b0740991901e400a6490881030a5848802800c4540c001c91900001805072502c00c68142e070100d4003500f814150110b803100141240c0682e00500b2003c0ea000c4140000c1d550310070a150080c2007014001c1c0740244048520996503441445421f00c21a202e016a0140000681061100990111916844036450640c0b014901000c4950f502240f00360316801a052900060510172140c10030190110202c0540341c19012184803072040c0c0700c40d0710404c1343c2500021100c810a00c41c005401000030480c0c15841004400081c2c3d900043c850781c01c0a20000d02c2c1d0f9246821801e0740b400c2110400c1d91061503291800310 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 386508435 1250 386507185 386507201
    0x309060c28080708150a030609240e21030f06040b0d06090b06031218040231060305060a1412011503140a0312020a090806090709060f050f06030a 64
    0x8640407151200d485030410b00550180c040c6846104032640c07550170f00c110020007150800d0b1300100f0800700704081002e070f501c9451440c0c0140d6401d001c08031425419007a003003820350100314003030780d5080d5112008010321600d81c40848601c40c03680e04958400c44150980000741400d0103181c08030000c01c90950f80c2d40e120580346400a008001e609030f090030048002c28240308240e4804014400145c50707031401103002801d041c0340d4040e01e030a0013a14143c003100fa441072640c0300c0d00603600f0408154503800d01c0c460040503c480001d00071594a004044114503a815442041894100424040c4aa0b10a82400292081ca0705200380c0010f0300000100703070142b1640c0f000307040d5103440b46440d41c11450b114114141c902442000040b142e17108841c69841d00155405800900d001c10210f0494481e84c0040c4480659850601013640d101d00641e82405800c2d180201030364402d400800034a0550f01454004200c01002d00041c2e51034070f000f140a08a42d0248203129980000c00101110210360003c00 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 386509685 1250 386508435 386508487
    0xe130b01051e0a0b091302090105070816021305180d0e1c0b01151e090b2109031902010b100305091009030e01090506030403170a141e0c0309060c 64
    0xf5556480210790381e154000b01400b80a040c04d0340108000c469940201c4402030810380d5070b10720f49600d685440c081034005509810f80b0a01c0203003d140581c1e20342268041c035000c3c000740000e103400d280a03440c0e80302c0250142c0b40f2640d080820001a9a500004200c00c11142910320900e03d112101c0f402c1d46107440a031000f40f403c0a000000708406042d02c809104903026900d400804c8425004613800c2d81e280e0200120000e10709500911030414590041d024080381094400c451500c40118a110407004440c00e0380c8a070b0001c140700213900c209055115040f010b6000070055421f0910124001400c070040c0d4000b81910f46005c2000e1002c10800662282007844042045611920300240140c003060001800140d4441d4041610b00d8044201c80c0580d502d034503180c0640b0352042510900720301c02001c00084a0f500d8200284910400300828860014100c45108000800e800d5401445026094000c0030300c1c2072017082400d00b070025146400c5040305400988a4980350f00110030904010304500d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 386510791 1106 386509685 386509699
    0x170d05070201111b0108010b04060c0602090604030203070b03060a090e0604021207120804051e0d140a021309060501092f040b0408070e130b01051e 65
    0x1031144103041031100141041c2c5107500345000030000046060351101000003660303121140714090444180071034200b50800e8801841d124044000400c0035900203030031541039490006580c000c6500404030786070107031256403800d8160001d130703501c500a94503100e0118003114180200340c0170600100c003c1c0400d0340d40c2c1d000c00c14002c01006401c840c50103400340124401000101c0c1001d0f407030045034041d59492410003882961844e8051080c44210b10b480202240da031a448402c01803500844c0c01e0502d0070b458078000e402d20701c3c031a0000390301c0894040c130500c06503015005000da240c008c480810040e80c0c1ea807450070985500204007141090428902c0420144e0101d207182c1c000b41800281742080d131690b40c9013180768080e8000c5102c9502c00b40040110202414809a000c0c03d035103152010990103607110b0300502010f00070b040c13160186103914a840f60440503100041c4600030404 = true := by decide +kernel

theorem cover : BRFrame.Cov 386330935 386510791 := by
  have h0 := BRFrame.cov_init 386330935
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386330935 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386330935 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386330935 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386330935 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386330935 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386330935 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386330935 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386330935 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386330935 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386330935 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386330935 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386330935 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386330935 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386330935 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386330935 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386330935 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386330935 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386330935 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386330935 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386330935 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386330935 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386330935 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386330935 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386330935 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386330935 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386330935 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386330935 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386330935 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386330935 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386330935 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386330935 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386330935 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386330935 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386330935 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386330935 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386330935 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386330935 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386330935 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386330935 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386330935 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386330935 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386330935 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386330935 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386330935 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386330935 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386330935 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386330935 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386330935 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386330935 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386330935 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386330935 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386330935 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386330935 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386330935 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386330935 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386330935 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386330935 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386330935 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386330935 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386330935 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386330935 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386330935 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386330935 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386330935 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386330935 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386330935 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386330935 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386330935 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386330935 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386330935 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386330935 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386330935 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386330935 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386330935 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386330935 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386330935 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386330935 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386330935 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386330935 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386330935 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386330935 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386330935 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386330935 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386330935 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386330935 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386330935 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386330935 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386330935 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386330935 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386330935 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386330935 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386330935 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386330935 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386330935 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386330935 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386330935 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386330935 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386330935 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386330935 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386330935 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386330935 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386330935 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386330935 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386330935 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386330935 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386330935 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386330935 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386330935 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386330935 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386330935 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386330935 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386330935 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386330935 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386330935 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386330935 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386330935 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386330935 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386330935 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386330935 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386330935 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386330935 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386330935 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386330935 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386330935 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386330935 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386330935 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386330935 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386330935 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386330935 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386330935 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386330935 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386330935 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386330935 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386330935 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386330935 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386330935 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386330935 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386330935 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386330935 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386330935 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386330935 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386330935 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386330935 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386330935 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 386330935 ≤ n) (h2 : n < 386510791) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
