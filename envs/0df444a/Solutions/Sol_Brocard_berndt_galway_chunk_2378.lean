-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2378
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:32:03.153747+00:00
-- url     : https://prove2.me/submissions/b3730013-ae95-4d49-bd28-4a86de6279f3

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 427517985 ≤ n < 427697841 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 427519235 1250 427517985 427518001
    0x60403021501270b03010e031b1603080a0e040f020403021009060503191e0b1e0303030f06011e0809160b030601051c05090a12030c0e010302030c09060d02090405 71
    0x456410380d8010381d4410020250f0054048404800c000d0340d94456455080d842c80d513880038480c0c0110a801e0101640d03549400111302000e84000c0707011f040147d40403654025201c004000351609580e07210160943d21070141004032032000d06951107690161501a501c951400d46d0740c010011644203441803150036068880a94107034200c0e03c211400b0030320810018841142c20301070305201d48840b000018082c4118801d43c400201850700112140380e5035080e8041500d0560210f00020321041991064070007884042603c1c2d000c060104007140c3d24613004900e10f68018a0034000c21403452109450b08e1920940043c141e200c2521181038902498100246565000d803d001c02e079508606400e180d6150b481c011100c95212001b40c6116050282d94011440703401c0c00f47d00e010340400070007400c070f524160900701000c500b141410380c01d05180032036801c0c00b9071b0840d142c40b10000c82400c0051301d96a0f00541604144105c820b450362040d8001056500007510f5070103068950020b540401c410364403441 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 427520485 1250 427519235 427519273
    0xc0c0605090d080412090b121806011404050a0b0d0c03060c110a0b04020301020f0309071401111005150a030303061a0c10091511091002030301060f1b1406040302 71
    0x251440010b45801c0011340802d100e110300c110350070441d25080040603035500840b103042d042000d0900d6806540c0091140030704051481025011280025100c2549000e410305166800c00d880980a582c030fa40029403c0d00490340012109940904130802c042c078149010301140c4054001140e0452801c420078a02034419a039008407134001200810003000c560319400d031740c10002007040b6455174007000208800c5016001450150001c90002c0c1081d074204100d0031806002005100d04003c00001c09030b1200c40002841d160346a9502c50021f0203071990247c0b60300100c1d960200030741099002d43d0000816034103030b026074104c4450103d10040c040c1200c0050b41d45100303425544140d90301c030f00c0c0c406036441500c1d800141840d00c40d00b84e07111810f901110fa42d0507200f00358038468030035401040c0d42d0741a051100c035240480300e2900c003952079503060580c0a0200c1039030140d58001c00c031a41038034a2102a0646500650030340290300043e584001c203d520740d81c0c1004442c100c0060059000303120000389144 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 427521735 1250 427520485 427520503
    0x40207151e060b1b010209100504090e030702090c030a09080a05071a060303030417130e1e010b030115020f0109050f07060801060f03050a0209190914010e0c09130c0c060509 76
    0x21242602c0d1442013100306440c00000c0401d041c01d95400c01c204c681d140c0d02c2c01001014400b064071143d841f685000d0380c100c2241c9590007024415001006210010307070304c01188940c40071783c0d1541d04e9102e454541e0b02d0b8004000c1104000e0400d1070015204207182d82085c0540042c034404d020f59000c0c074440740d020340704442c401e0f201190140d1043c80810001048014004c840c001c941c0d01883c00e10341000c129160020456100c2d1951000303101c1403040d50107244440c1ca034858040d0300751107400d502d041c00d061160702c414412240c200028200c6a0787c050701c02d100c0007105548100003400384500d1400e080d43c03140d0031032044010911410400103551406001c0130f5040f5011b0740c42c2c903c0d08109604094016100040c030180c5a03d6080180d00c000703603160b40701800c80310f078500000c04520b41072803500421030b086154965050145a0010405a800d8003110350f4483c1070034141c1521002c0600c00704180da51941e50801c641810540c03e24445580540318840d114000c040900c0140c94152034151904120 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 427522985 1250 427521735 427521749
    0x9060f0e19020f01110a0303050118020304020f240c0303010501020c1e011d1807030c0c020f040f1811010e010509030618120c07081605061206040207151e06 69
    0x1d15030038030151030121a000040d40c0d06040500b10300130308907415030800d85410f104074082035540c0010303c400110042000480341a01c40114554101500001c2c45c25000e03402040c400c662800350b00f010b40ca440340000d1080c80841c0191a100c219101045440350000d014450061044a043d015180b8003092105990b00c3e96114100708a841c50300112200403103180d092031031613140e19204140307480d6a1841100d07035100e204040301c8c0d8103001b5002020384104540c0712041040e1848240050388c0c80c0c82c841d10038540101c40005080452144c40c0d0003900c03105080340c6800749902911410310650007403415070302000341e83d151040007820700150385a01484242642581c030640001d4082035200f0000000083c455048035480841c04103491034035809550b001c1c0650704200010001c02400b003000508001080050010780303410440800d00038040c4003d8070480300b2021022a0840d1501e074100c0303010076040903a124100d07080c061030030080c1c000d0100c5110a51030040b51100f042d0440c4c4100e506580b10 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 427524235 1250 427522985 427523023
    0x16060b010f142d071704060917070902190207061404031e06061707050315270303010f0321090b0c07090510051503060109090f02090409060f0e 63
    0x40404100982d030031145002e031910042c0f080c2001c0e40d200003040c031001070384500301c20740e5a4a11031401210650000c9034100381200300748024840390782c020500d20700341c401800010082c40300d1111500d01d0f140503607100e030f043d80e8400250008444010360504201e403070b140d0210f9880c2552660200c0381c07500d045420030a114000d21003880058449110080e2524081c42c082c900d455250301c1d00d43c21280294030001300c030042207045070401030052001100600c1c1c11005010920407461606400b600014003001c4411082c1000028120a0358403100f2100402402c90761a580c4131341e05001800b03481e00080d51025581c00131480305035115007403041b4011040e23903003021040c542110f000c0b140d0050080354030540540c20f4007090300b800b03c0c46105c0c860080380b8010700c6540e10b03007000e11442144c0500c40c2200004101b080008a0f60002e4038070085a5941e035002a501250f50a42d500a02801c1d4070300d5030140c2082000c105102e80e40c0c2141c001c60355940d0b82000b90650f80800541e5031013203010300283c100d00c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 427525485 1250 427524235 427524257
    0x1d01030f03030f0f0f050105030c09131106040f0303081012030c0b180109060203041e03020c0906060f130302030f01091106070f080403030807080601080108030d0c0306080316060b010f 81
    0x48240c0080c411842c0044000c502540d4620762a000e5440480c40305d0b02c4199500010000352a0400c041d640300c201c00d80b0108442d01307080420a440313200520700500041c1c00315003441240e840710320403600101400404101a6074492600400d5540d003510400b041480c0808042080c8094640c43c020440e81900c5147c900c4007160340d1545581c000401d032141e00c0802c03070240000070901380500a03142d8403c44006a07030740380918221802e82c5420821b07a410504447d80e0341c0002c1d8001444c003004850440d00320b0303416902c01000801910410448101030100802c080c808480f510002c401501e10072000d40d440c0a0100e4091400c95003091409130042e01c0303d11004d5042d040c040c0090030294002d20010310700c070b100c90322601115481b0b035004030001110b0504000807035901074040b5800410900c0e0200c10707940361200c1b5a60746c2c0103444200f0107007580c83c00400c4040d4025030086006001000030303a51503000c2c90040c00e00d4031a2100c070540d6241e061640415140d807243c40300580c440856254203d00d03031 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 427526735 1250 427525485 427525487
    0x30302070f06021c051c02030402031e1e0a02131508031c020702031002070b0f010e130803060d020a1401080a0c0207031509060f06030213090506070f0201060e07091d01030f03 77
    0x1255110703080a1140030000000c0c1b1046007500e2480341041c1ca40c0140c3d481c02d0520506140940301249101c164441c0300b5000f998450104e030314580c0300b80424a51610b51168501c0d035040a115580080d404002569896004a6207812001c1c02c2108500204c1c035281e903071008241c8911a0110b01a25101405040305181d080366000d0031100c0d0010f800ca0700ba215041400d00c0c02c0760b10003502074a062100302c040003003c101401d041d50140002010019950402d01c2c1130a80c00800840000c0a2030340c0400000e4040e1070350341c03c01c007a094004043c2000159a407141c2225000442010742c00981028006103010341030340542c000748980381d070041140c541b86440b0b03800b8410088494850385500c400c080c0380498068019407040d2900c4e0203002400500d140304220400109110f0381481506000d0610045080811010f07440341860034042141ca0a00070700301d004148540000111402c404140304107e9403000391034040c0d400124074040d40d8040a4143e141d074420910006011118a8040900103 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 427527985 1250 427526735 427526773
    0x18090c041a100504030f0b25081501031e050702010b03010506210f1015060c260403020405090c0a1e15051213030207060f09031101050c100501030302070f0602 70
    0x78001c0b0346032583c149a1070b969400d0b00b241140c0030070b030380d00d0030342009201c54505c0101c2c1400c11a01e001440a440742e81041c0c0250210f000240484200c800030006600c0c503074000d42040d4174401e401e8040d451581c41500d841c5004003c10b480400056290440700396503418140b113402d0207400001c2c400071321074200300800d0103861703041802c800d0305008400070703410440020041804654262400812034911008501e01195071652210041180c0c81d503006000c2003041c0019841e1080d5121750200f121103d181d443d165205582c002900f040c50b0a01b003000e0307a030f000b0881c00700c003010488103a001240d0303852080130008000703e92104c401c0c03c000002c0284100300728841e0f2246840c4d08180c2d080100c07810440401d80700032070356181c039a03104100800400d82c0c180b200c0d10142883d41007002076644400c800502c64070070303030100a110708c00790524041580c0c040e005a03504500c2034000c9030400c1d0480031103c2c014240a100803800f500c0713403520100b1203103904c0100000ba903000340d0080100000c0f08403000c2030 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 427529235 1250 427527985 427528009
    0x30a060b03010207211707200f07290715020306190612140108070b0c0c0409030c06053d0806010803041802030105011403070e18090c041a 61
    0x1c999820440c1100003440340e020440c01c01801c2400c3c51050b140d070980684840c1034103044050045808040008054100458a079040303042d840d13145014860358a07152802140e84c2d0703154820721424100003191503091002c10b083c40c40c0d2140098610001d0740e008000703405a02c0004009088041c403800d00090164043c50b4062001041c05844c203c0c0465500d04070407603a000307500055000b03555044c0501c2c05000314001040145907840040d8940807020703445510601070b82d41046000107218451060400c003021110100500070072805078189800760842c01e620700120707403131400c103c00149641541001050501081c0c6140007410f100108400c0d2469a46100b003004e40c0056100032681d5002002214060403c1000860f81c0740c1c01d00100880c40400300010710b800074010001408166844500e003030b007550030610b90329102c0c0c54204040d40c0c9100e0102c026030304061900302c88034039490b0161205025000c1c40c802d452500c0d00030014001034a102c0300341c414075010917800c1041e99043c407611640c4 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 427530485 1250 427529235 427529239
    0xf1905010804030c020907030b010201050f0103120c03030f110915090f060c0a050a14010e06010b0d0e10020d0f0b18012c13050606060c06040816080c0d02010c0e030a060b 75
    0x5102d444d54001000c10800759030200c00a950b4001135202542c0901c5000e80107e00c200390050b00e503156542c2d0944d6030b028a8490030410107105080703010903010380c02110b4a602040c4007445401001c403144011508549001441002448810302041d19541c04907400d01c2d02c00b41c10401c0404440c0f0034881c0c0755102d41040c42141c0300354064040407480c18410b520701c0904c5501e4800311020781c08030142c01e4445074031135800c1d1a04114010410440324100300c031a0007030302d843e002c0780c410402e00981e800e21440030f00740a40980002699290744910b680000c550070200c4c070382000359440761014400342281705035030180807944140040c80303418558140e1160056081418148100001c01e0000381000180c1d43c829545202c44500c000308031060020503480034065030746504048011b0801039441a0113040502036001c0015614030455400000c1162260003200d00e6a44000c081840e5646032040103271807005520300b01103400d40500c241e000d88116440240200048012925010010500d4514180e = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 427531735 1250 427530485 427530497
    0x303060d0f02040c1701051c0b04030509031b190602030a20010f1a040c050d09110d0f110f1503060406170f0d03050f040b0402012c0f190501080403 65
    0x40140c1e070f1401101522026503a8000d0420700d00d1521a10513001030700b16510891024401c07007180d4542200816100ba04106d06120755181c506007943c451180303580c1d05415004003068030f282e0008480e100380b00c41c40d040c5d5084401009c04020217a5165040c003070807005070000c1000c580883c2c819130b120f080c442501c0e110340c0b4820680714401421510401c0f90140001c2d21a011142000146110480700e154155800c2c00180d5074032000500703920034035809203510f0380d880c403034801800b10040070702d2550b5502906255555a81d4104040348001e200801c40b0640e06010540140e0308040c0c4c0c42c1303d143c0070040c0613201c415145015002d4140c00c01447c00c1d400a41e518400954002407410602148a040026140389080b48000a00f82107500c400801810b0502e8280060001244c200c20746c0705d40c00c4240420309031540c0c80100c034000c601c00e10085201141c114031101d00c070000140640c1d80755084901b80030345a00ca405010020058495070704807149400402c2005501804240b84c0c064400e103000 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 427532985 1250 427531735 427531763
    0xc09030111030a0905010608070506070201050c1614120a12030c0e0603010b130609030f060b030f0a03020106170f0a031b081c050c030402241312170c0303060d 70
    0x46035260b0400c4480312034040d21804c4100c2402003c0c454100074003154009480c455041c040850214441c024009040000000700110b49000901403600002d481660010701184d450b510320081d0907544000c144510340d00e000a03400240c00040401c02150301814000c2217514112080c0d006001c4401044140483c2c0e04024000d0743c1c1d0b01c8011406801c1046001c0e842e5041203440e0003046905401003c10302581c20000d2001c114910311003540582e22103408108048003a000c64200000855069407510901c1148001c00d0707010b400c80c4c41a07620305803503140044111041250f48180d091440c1d081d94020855900200303100d44240c2400e800341c1032200b41c3c80d0400b5524504654403000408000100301c3c1402d044150660003020303040203041101c81e046050540020b90010800b0290f41e0b0a03101d16140d140c0310781d00d14000e0322035903401d04071a622a0350740d0784825103a26542c0c2d90115140c400c0011450b1065800d4010341d850b41b1b118800560a6176504c10031300c00e50b8508080282c0d8007a1151410b = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 427534235 1250 427532985 427533011
    0x30c1008070201060302180f0c031005131103042406030f0b1f0902031b070210120b060c0304090f09150b010507120e0a08011b03020702060409141e07080c090301 71
    0x20b14047d0b40c644c0da40c10b40440ca0509001d907800c01d005058030703002003400c20900210300441c107641400c2d01c8040b01c2c0d0500800e003280300c030070007414080600c080c080c10120400c0188402c000e10b00700c05082000c140108009815a81402ca400c0c078000200752080019802010880c111211a03004083c1c00c00903100c2c4200d2034807010300c0314860740414103298000007000340303c00a0035070940141a00194050400c0300079400500d40010b00704000003080300d503038041d00b0643c103c0c0d009001c2091024241c0c030750760502020241c1c3c07207511501949105504000303c048900c2210b2044020503a006903100341c0c20040300c406480580340301d4000c0d504116082c84000c01007000310044845031103007500d0f041251004d07041409203000d8a07901c0240983d01d0260391220804640d1131050020b1194500182e41c0c45152000590a025540240440c246071000c000380711001c03c50960300851103051402c0001d5054221900b010500311009000102100045544005410068641444020004262800c0140e0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 427535485 1250 427534235 427534249
    0x30718180207080c330417030714040b07030810050f1e03060f01240f140c07120b0a050405030d0b030c0d05061503031216090f120201030b030c1008070201060302 71
    0x82c8440702079802031204d9454800307403003005500e1142d54081c0750704c1c4c0380c1b6840310710081e001c0041c1b00c1d024034000000604440c0c400c041e901541100c80f030352241c5454607003078009050b810201c41240410b1030440840e502c00c0d80e003035802c000c440d001800301445030300e008140072011003507400000d00000c8891000343c01ea6800d200152003030000c0c12050560758540101030802c04518100d11000505c41c0940f40301e5240c0c4245580e02141c090700b00404080203140742854240700380303003942a0741c2c01000408120b8050345d0540c1035150b4003030651080113440e141c601004581050750002d20540c030801c01405104401d0700318200c1400c0043c10b44007845101c8000c80c4403404004401c44841d0080000c00120001220405d0f2810005800075418111010b940180584000c1d110b40d031b144040d00d0720491200d200f56070000c042c00711100d0f40a50a40d070342d40c00c680201c4040d107080740031034101040c200641c140011040d1a040005044005103040d80c101036a1401010301010119521502c0c044091b0b240c00d2 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 427536735 1250 427535485 427535503
    0x2060a060b0408280b0f0a0b27130803090a12020d0e09060103090828110703060504050c1306050a12050c15130303080603010f0209090c090a0911030718180207080c 72
    0x101c050647c540030240504482c10007400c0c510880307500c0309000c0c000c2000b130650107201c61003034140001a26040919070295000c0c0c20002c00396800042013214038040400c030003920380c0c4155a60031019a03c240b05a0300c50620580550004100169600243c54035411243e080841030400056034912511000f03280e50100c01c10480d6004550b01502e4541134414110f95142c1c0249010020404518025511a640c520000c1c047d0b07600d40c004641440024040d0741c15040b00201000725407500820340c00050b00b15071084911a404603480086c03001c480d50340001203203510030301924404042404001001d2032010074400c2005040c0100341c04121030021280c042c50090300c8041e103500d814800c050a42c0c2d00e031165010028014800208a520750501c401d070045080c5020a40b5a08601c0c0451030003c0d443c1c1c03155880307a0410038418a20132200c40114021000c503994020348100c03000301e414142200e4880c2d060001542a13001c2e21101c041c2d80900122486420420324240c07420304d89a282c84118 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 427537985 1250 427536735 427536751
    0xd110c0a021009060c0b04110d0f120216031e05031803060a02090a27020a0e0906010c1101050d020912030a110105040809010c0602090a0602060a060b0408280b 70
    0x240c00003815454560340300c210742c100d2880c15008090902500504644088000a001c62440c1c0042020010341a85010700411b0240c15208038601500b02580c00d03040e440001d85105050f0050344005601c00f28544516812455004e80c581c4d00d10340c2e0b000c00908080ba4042c0701000700610520005005000400000031800c952581d4004484101030070410b01925440c0250310401070f400080d10f402c2c958104403003180d4407214032043da226036001986a44100c4040d08e6200082004e01c050304503c00c40c1c104901902d07400c0081c0d4a102c01911078207844800900344010742005c0c060700b076100c1c00040c10b0484e6800310240c102411000400d18254036903001464542000c81c1e0104d103a81c3c040c00b0a890900110000d00c40345c10191114032041c0700301d03440d007810042d0001d5401d00303010b469011500f2498003d00f200141d996502c030025142c12068031502000ca04002c4000342450102043d2000d0b07820300805000b00c1c40003840100d904008510914178048030303020414003c500c6401440d4895001c0d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 427539235 1250 427537985 427537993
    0x70b04030215092a03211c02030709060203280c170a020610030314250620040e13051c0507060b04050106050304060b030f2509060b0703050d110c 64
    0x40ea19600784c4041d01000071401c4114914000144c0366000119042c85080400c1090005c2d40d00900054081c85900c0b058080c200500c510314042d0407a0b0b0f4025441445d05603030300030034a611043c080342c03a0300c152a202c55250700c00c10030038500080d00c80c011a4132240c0908040c130300400c49a0301c0002e00501c40c02c04d203042c0740021900e1030f00c06030107000980c2e0080c20005284101400d40c1c1d030240c045034603401c802c0f5000001040810b46244c03107030600c6c0031441d9242080300c0c030146245003800c060302c80c040325510920712078a4084900710303100c0265000d0f550314940c04600c83c0c1d032700c0454840c00d02d10520f0540c3c2a10034000c640060710b98000a0000c0802c03580d4641d40c0d0769101d824000140c0d034903001114011490007004103d0158080c007541c1d00140d104802040020003940040d2603c40004140ca000e4083c010020960070701c071611442041603556406545682d440400104540301031081e42c000380c0e0100003900000380f194005001d4420503050000d10f4a4074482e65a03400d41100d2442189580 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 427540485 1250 427539235 427539253
    0xd03081005060309060403030b0a0f290c1207060f02070506010303020d050f030705030916060207050a0509060906090702101a0414071e050412030302040e01060e0105070b0403021509 80
    0xc00c004007900781550a0b500d542000340100e43d0f40d01004002030201a6115401e46190381c9454500c001040d007110041a250384039000a210402c901c04005c1c40b4401481c60185000d040d2010341700030010503800781c80131a410540d02029070340043c0c400c0314600ea5918006000c290310b4806018080d00034030003402c0d250b04602d0080c1c6481d0a07203442d1000c0c01710a10030500400b04800460354001c1841c07400710307229100c07014442c0c80c0041d002c80700030100103950400f0900c164002500012600125108049075070f440061183e05c0e181a00e00c650442c40520005035a802e1640c0f200f50040324900c1140c8401c03000320154011622055400b5046a6083e9402da031180f42030b00800003890030180030303d4000d040c034540152940c4003520210500340a004403c0741e40c54002e000780c800811208840c02004250791600800a41c460b00842102101150021981c1440b0f05969070780044180c41c0c40e483e0031481e856103821000020021002c610810b00c40c07411100030055114045c0d8100d8008110440c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 427541735 1250 427540485 427540501
    0x80f0a0f03020306130c05120103140d18060503040f080c0c0f030c09071101060e13030306060207080a0308190c0e0319030207230a080d02060609070507120203090d0308 74
    0x15462031181001c06005106000c13140ea60402140c1171407412800010304451034200030380c1d007802403800025000700001c0000003882008001c607801501c0040c20f0700c01404010109456000708540e80303c1e12040747c1001404000e0259000b10b82141c00345c884c92804020599941c1001e50205402d4205034002d03c40c0f116190030068580683c00c0400c40c0602240e9003810082030311250020245070400c0b5194a000511b81401c0d403016019010400c242d03903440c505100e11000d0702c0d084a00c12000030f45404400030f1001d00c08540744c0103031010070380917009108951710200c5007400007a2030244024118a0652074010180c400c100000708241c4489541c900c00b00b082504260b203580f2088140110f40480000181d40403a0b90f1054800760143e0342a284403180e804460712703000724101c90b00041900e1000c1142c05001a103800221400d03421030309941d554030180700c41d544040d1002c0005c903100b1f001800025801e08810171407923110788101c0c3e0421f8a00c000045220119800a402140c6140248046d030 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 427542985 1250 427541735 427541747
    0x1060503071503060b070b2a0d05100b03041e0809090f07110c01021002030901060312050d1a13020702040e0313170601030807020d0c05030303161b030e0409030507080f0a 75
    0x204085da4015042040c2a01e52075043d020082090000022107202d000c3d203501100c200b859182d24403c20907445007200115000140300681e0324140f09040e1110008035203400074200c0f441254041850300750b04c03800b108110b2003a103c0480072907402c3c006000e010f0302c030349440e4800d0f44a0f80954007035200d58148040b014101d004c1e80c440200c05508036031427a000c0d40e41c00058602c65034507111b40040e500c1c0c3e02d01203054010201500010000c079842c049e001e80c1507900c58058402140444400c0015105241c0000d210006c0080c040da0040c1d50340c1241500a01c90394003074825140040c00205210200c601010b042d940b0080c030301141120030900c140070401c03a1143c0302944511880043c15a5411916410b869010300705000b449007400421a40c10402a03001440081c00054200c81c2c407424a20311400f4400d0851841100054110070b140c5050040000c4034040e5079016282e00c141020401c09001c098030303180c0016010f21004200c04000195200b0080c150061003929190300c0e032090355001417803 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 427544235 1250 427542985 427542989
    0x1140702030327030d05030112030e0d24020310030f0503120c031f0315090f060e1f0c1e020f0a0804060f08010b0d0b0f06271008180106050307150306 66
    0x26841811703800070b000e400104607419941082204040c0140c10724045070201589039946400819900345c1c103080142480d2410255107500501c500c1100c0c08a40c400200e0004441c8100c0344200d0030310402c08502e60805104802e4020402c0d40d20381076506c3e00c1001050000d643d481c0c1950000030400c980420f03040382031920202030b10f00700c0404528589a140081030034000140007140d5414040c01042100403440084070340c000020b100500c111606a03880c1ca10786041859040101400e44811071404d00c0341c070079484281d445491484050790880106221251034034410f622840000303803101c80003008068100b41c07007440c8081e039407800c0010040200049184140600150030014031000103144160b820050107000b001407417918010014100400441456800c810009191401d1f0500b06c415201d0a4180014618035904c400061081d010151410703c000180313030101240c0b1900d141c1e1401d40420070a0b10020401548800000e03041c50255448001d400078179543c094036450b014010400 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 427545485 1250 427544235 427544239
    0x303060d23070f0f1d09070515090109090603080a0c08040515070228060e03071508040204050f0c07060b0d08040e0a050c04050a0e04061103130506060603070e01140702030327 77
    0x184484ca0b103100b40414040b0494401703440451400000c0e24004104059001003000038001c40001101d02000f031502d80c440c8a401d40080c6005101003000c0da85401072400b140e41c4a5041031a05500c403c0071143d0000d640c2c0120356200b410840000d90f03681c2c0c02000c0001c51519802c103542e5220b0b5104000724030903290450a04001c2e00c1030403105200f040c1d9415000c465103810200c045540d140002428007a4540106250100046115000d00e80c0013040714030640c4240c504001030b1f225040c0075070100400300e40c03680402c0e00400c00800029004d40206148100c064002450162151740705501a0020341003d08c000c004c0b401004200001c031301450f81c0050300805118500340c207140200707008030818012408840c03180c402280c100302850f84032070780000c1c40c10070154403801c1c043c03c811680200800f040c0d580d44540008203000b03282080449005415980f41c2c00c031109041d200541d1948400e140f4601e401c0300502045000da14284014091000b0244040c6074100351403011080300004210298 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 427546735 1250 427545485 427545509
    0x11060a0c081807081b010f0c2f0a0806040209070807050f0703180312021203012d0305011107060c0512041104020f0705030a09170303060d23070f 64
    0x844150308010141c0d00b09084140d2440d100200c40d0400e407401c60b503540702c01200d1040e00d00f0341041840078034400b0401e071005d80c2d8001c1220090707007003210302240802c005849018a2103000d00ba80d5262850302c903d140341080886503485a4200091404c0310b290320030046500711070100070440c680884c50f09e41c08032081c101003140c0e08003158024194011904503603191030001400106040c06042c4d561248804240d001040b680c40340b81c5888481e501345d00c51380142c459000b802e4095130801e400d4a040c2d40488201c0320401032240010260f4551503000200b0320100443c1c0800407400a002c1c1007440038038040b0055a80280b807804400300e4000b4000102040300602609508883c000c0e4013541240c0c00c40c0b1084070351700c10300b00002e009110b0005a0243c00c10001851020080c01002600048030107840b400000c540e603607090003121014010215042c2c008100044e050310307146402070300c81406080d01e80003c0041c2010040090f84001030301e03281d5070214100b000b100c03581480d1400a010600b03646 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 427547985 1250 427546735 427546751
    0x4080406090b040f0b09010c0b07020f01050a0209280f0b040819050d030b01091e0305010c020601030f17070b13061d0307020111030c121801020d0e0103050a06030501060611060a 78
    0x2d0401510f142c0103111005d100026241440e0388283c0300000311581290115005051441c1c01950703c503030200c40c880703540d400d020004006034028802c0d9003540c80040c0200f0200078048400400c401caa2540044021301000300101e0150200d0062074060198102207075a502d00703040045240c0050110b81c548001d6510340384030006000801e0401420782c103428081800b50b1120f0045c3c03491404c03608179111000040d0101c03441c030706144640d042100d0080700200302440c01c1c031500b261500800d000c05031410f071610320f02c0e0b00001c2c822840d402c072308182c503512a4201169940e035100085000d48001080200001102047c00781a1080d448050894502040c2500f101c15200d40c032809465000b07814418442e030400d00c00c01041c000c80e49480f0420040c1ca8040e00a502450440c1d04481381c440240c41c1114501742c1554000039840356880c9991b115000c03010000300046002d044010040b01929450303000010029000f40514806049a620341c8100034500840b842c0c6040002032010140500340100 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 427549235 1250 427547985 427547999
    0x1a0420060f0706060e1314060106080f07020102041a040305010b0d171305041b11030406140f1b1c05120105010e2205041101050a090b0a020c040504080406090b04 71
    0xc40e00741d215070a801907114400c60510038003c0c203855002d98500440c10041040d115030040440c0d413524414008890b007001e1020720944d50300d5090140d240411002c80c08210f0040d20034080503032100c003034400980b034181c4400c01e090f06c84880700c004501c0700c0f00100e0140b0802000380110b91146005541d42042001d103500e0b28803203444080c24101d0490341c0020b040c03071000110744282001d418080c0051012819914010380c0c5514044800000204140c920303000c1e0070000304c1118116005940c42e16203518000c1010080b590000d10001403a0b801000800d100d131404ca00c7c000d810304000c03800780c410311030908500d1046809100310711040240400884005112484486055520030718000015032000030110f1003040303a100141b00e003480c000d42e46855114a43c0c0080e03100b03600c04e48140101e1071002006454078043c05405074046500b501080c0042d0804030042d1289809910484640200f06000b06048950659060b1004440000d09010203074000b4043d40c010040201001d281600d004c1d0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 427550485 1250 427549235 427549237
    0x60f0e07030c1e120518010c050f070816050a2f010c0b0a1d03070c05040902010210240803270102060c130308030c03091203090c06161a042006 63
    0x141c040f1043c0c008200c03507812a20800c101002c00c2e131102c10410860600c440003000420340c1c04198290341d03080005840d441407050003034070601240026901c0c10200140c2d102103036500b08441c80820501c0c000b44810102d0300400c038000c03000b400303030602401004004000c0c0c1031200d0050344551480c42880300c4a001039070b11503a880307180303a0018031849071912404140d0000d0220200f22060171350000c2c4104520300e10110040c0100c40c0b0481c031450507a5607402c280070a071100480701a0158010a0070012080312540011200030290302c00884410401c2d01c1c4a4a000c446070800411680b010940c0c501848500c0d0001d21000441100c0099040071540000e542d003200134941c105000010030144d100041c0c00c41403202460740709484507180e1901c0010f01046800440c0c80212511898591074528911101100d00a199030350143c680c4c0e141e400d0074000294480208c4d0386003000032102c01310218070300740c26800b044482c41d004d02200742000d04107908441007403018184000321a0160703000c140c0d1420 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 427551735 1250 427550485 427550507
    0x20307021e03240106080f16021213090e0a0807230307030503040318080303161206170d020105102304060303091703090307030222060f0e07030c 64
    0x85094101e401c60280d041c0d0400c040d64002038061051909444800c82c1e02260800f000101000e40d940581c0d8499040b10a088141c40b43e1402c24001800f150500c080000c6ca44840c10303075401101c2e41c5046001c03941100f03900c1034074034001c02070461a050065241d240500ea425000b940010580840587c454040c82e00c01c02c100107044803034004140850719000042080c3c840107041c152a140c1885040280681e80200c40c01c50000340090803030f0345504040700031101a92020b10055082d940c4000c1c0c08a50f038a08190b1000501c8044004c0108d000c1040c00761070060f1100203d02040da000c1c4131811860108000f8040d015039040c03c040044001110040c002103840c0e141c0702d028500360459100100410380602c0c0c90300f0078103012002c0309054100c2a0350040f0303000130500c0502c1102d410b1220b622401100c013405c0d4190444141000903140400c0101511025901d10490000301884510300f161040e40c401e2540000880303040140f078140c2c03189a64488034030704003031108542c0c640d03001305940f4a06c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 427552985 1250 427551735 427551739
    0x10b090a2408090a1a01030b0f04050a03030b010507080301080a030f0804120e0d02040c080f0114090109020f0906070f0302010f0203090634020c2b03030906181101020105070306050102030702 84
    0x20700d0001d05043d0041100d46105600701000c4170304440d0000e60080c0000c0d090000b542c074990a0b07030200700c0000074012414030868100010305a03451072580c080307001d07120b41180c003810007a09101d81380100c0c072484004d40c002e044034001001207051500c3c010303100c80412a404014040a1130401002c560402c2580c210740c00240703407008845504000288a038555040b02941003440e104800c8402500007031042d01480512002d000f450b03a07645a6280a01441c01d629604803070142d00412a071000f5030047c0c5003020810500c02e050601410119641d50490141500c0400100c0b000d81c00340354080c811440b1181c4200700640c40d505d441d6440c641d4540c40500000d280068040b106000c0141c500c01c00c040905180744038081072003003098002c1d5030b824103414192180700300185032520b02c9a41190420145800000300740d0403c4181c605600070f203c10302c4180c410646907050844501d00b030415007000540309460020651844800084c00c4400040500041c1481e21005004503a00001a50086641 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 427554235 1250 427552985 427552997
    0x3080c090105190305040317190b030109170d06060e060403030f030b040509010606110303010602250f0909140c03031603050702090702031c060506030a180b010b090a24 74
    0x1a440121903600c02c62003802000d1080f290f40c2c0c2ca486034941c000c203001e540a80e41c1e1860000d810720000c48590815030302d51010b0b1011029000e003040c202e401040d0458002400095800c0281c1c0b2070229107540140303003211003440010625241c490603c12031001e0861803030111141c00d00400814002d100301e001c09010722000c9403180d50042e101c2d42000380107030805481441103050032813600b8041d0803103024007000b09107003017070107850300d0b0002003940c4c100c9400743d00612550004483d229002130480e1103400000c4a646c00200d80c0d0035109105000401c0c8000000600f8000d50070011030aa800e001d10000c41d410401c0f20036070998002050320b4602c0c849000c0711130307018000e01d41540c2c240b040c4071000390082445010080c00c590040003030015041c004400349900c0c104140d00700c08030307001030240f507502c01028401b107840300040342d00400309c1840404907003003a0f02ca1030311a112400c5003644460818200001d00c10164108181c00c42d008103104880e45e44420740c0701c402c658410021300414810049 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 427555485 1250 427554235 427554247
    0x1060e01020c01030e010b040908030919150c05040e0108150c090901060f05160b0906060d0b040f03030914011506020a05070e13170c0618060708041b06020f0106050102070303080c 79
    0x170f0a5000a5071035900500420480e901031070303c407407190801c80d810f2186001340a9038000f86000040a03003030f1039610a11900c800070012500d80d004200b5000c1c2c0748100502400040b4052511a42d168040c2c41818000e04205040b084034a1304c4010091050400c0d0005002c2c8034100d48800d41c000341540c4090808012030010032808a500f4098103d82d40c02c50401d820707500003030140800700c440c002e801001c2a1102c03030343c401041c0000010b02690080c606901e04001030b000c1003041646200e614464607000c155800551103078100311203944a40b01d00f41e5500c030340c1814598510040040102000d0018040030f42d0103890700f6840d45068407900c00c100350071200143c11407180004020800e81e2003605075421004e04c1c1e1a01400d03411804020711244100408a200c0303481c48000010780c80c036540001e007030959480708102c40e0700501400441d0f1460380300c50492412820140d210025000950080c0603d01c0c41003855429201180e11241c15500903010a1000c2640612403d42c0b18055800242d80c540c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 427556735 1250 427555485 427555511
    0x406050d1e02180306060105040810050703021b2b020304090209060d110703030e030301260127020103140c0919030b010f0509060a0803030a0c020c060c0601080601060e01020c0103 79
    0x460785401ea26006840060682014601c1c100b003400002400e40840700990754410040d41c1d44e10540c0181081c0358020010108800c03002d030040390f80401c0905e000350400001195483c0120300c54803603ea01a0401641751204451050b40a0b0155003d41d2555404404500002c0d48070f1050b4003c80218607000034540740c9a0700e551003100d4010103052004c0010318000300710101150081801200007a0030400011a040c4d8000b007940e0603190409102061550829000703820007504298082c0300b5500c5614555018008050302e036010a10041c84c250340400502c001800c66000c2041c0d500c0d030380024000d00031020203020684841040c00d4500c0c00b80200c201803064a21040ca5100401781c03802100007241c0d035a5000c1c0d20710100c03841500c450348070b5190380c0708000409110b402500e085500c2880094250404c0d07800c07891402c001401a01d104458040200d0398660101a002c2380b00c0d40800010002c82404104035401002589088581d55410000003910395010b181050f04042e11228024104 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 427557985 1250 427556735 427556771
    0x24030304180e190302030406031805060103030203031e040b070c03021501090603060f0b09150f06030115020712030804020108040c170d0e010203040b04121415011a0406050d 76
    0x351158000110303910901c4074524000c1d10200c040028680240d01d541d40d0000706540099007401e505402450500782000001c500422100e440104081c0d0380c40703101c030049075060111501840c0280d01941e070f03928001d07440c82401312a40d01241c0510004504010104031722000c80d41e00203034146055045010306040480c0380074203103401c2171220390040c000050104800d40c030280c100c0b445a030301800280e4040441c01c00b101c0030001c0843c0c02c1519040002d42068148185406a90004000d1409800c40d4404102140c000341c01c443c8008860500409102c0e40410042d0001d19030441e400e0000d02840e40c004000d000041d0009060080c040003103070804c034640d00320f00c001d008840c0301070240f00c1a0340c4082d6a10a000035403007022a40f140c0520206501c0481203609540d0204545480e0a2802440014034400c01c0819506002c0f007140e1024120024400c4010200901c145100e80754105040c28000413000c104411800004000c00c105454104c01581c801c120a81c00c00504401303104040022 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 427559235 1250 427557985 427557989
    0x60207050a0203160317030408030a0f0e07060507021e0a0b0d06051005030a0516021e0a1703010e01090903080708060a051203130b070c1a0d090c0312020624030304 72
    0x814050003c0c103484410804c4540e1040342d0185c00d88100a2490b141c9040c410f10045c0c5020740810410400110b07c401642c010b4604204292070008400030403200d2107003403528a0300030350b001510001d100c005501d803031b580381405010f11801854001e00c1e0080062900880c4d8131413951454408a54092061205e81c0198000c00010b0300c010603294004c1c00c01001d941c822a88a1040c40ca41800f007030030310602c171400c00081c0100b9001000c6201d50300c1c580321130610a9103103940f500e01c228801d100014110101103602441c0300e01105e40c480d410303c100807441600c142c00000b40c0524050591004c80e0f8400b00403504282d0608001c130203929110081600d544a5801c00d5070000c0520550345c0c40c25000000030f00c01e11480c2c01c134401d50701c3d0710307450221007078400c450300600b40c48000c0f642484800c10f080c071040521000d01000a1a02c0c2e41e0b0741d46c5600b44e0320803000981d16440c6104081041c0301080c10b40740245000752016103483e2400c00305101003040020451515560707129038480035500c0810880b00 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 427560485 1250 427559235 427559239
    0x100c060c0807031506020c011b06140403090b030f0402040e011d03130504150303053103030806010f090e0903040317040503010c0918022b060303032007060207050a02 73
    0x1256035010362000d070014000340ca60200103450010200011600c18160806485241e8060724214090100454081840301682985003040d00c2c00800029203070302c10080020900e240c0c2a02074503090402910009081e804100822410801c00c400d482c3c5640203158801d6040350001110074040c980e10340103049040300101c0f10b44120005044100d4004050090302209202c00201d150b107510920061780c0764204955208018200c09000080c01032003c0c00212200c0c100c103e0030250000c0a4504030408070040031004c8514400a2082c540d0200d9500c0c1e2020382820652105040a480205442428407800040170200008100c3c0403400b0310464000b95007061000e441410824451381381c99020740f2030988039610708031180710104c1c06118240100da0030303441c2e031007c500c5013015404065441080c50014606403d81e0f00240480403080c400f002d40700d50080000d10506501d40901241c2c1403a045002c003208150800c6012001071003113851203580008096240c05003854014902881c4200c025 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 427561735 1250 427560485 427560491
    0x303023705010b0f041e11070b0c0403031404080a1205040f0906051003050403020d08070c12020f010f0204080a080c070b0c060a0c08070f0f0c0c15020606041505100c06 74
    0x800d01c007054014403065001183c0c4e400166a078036080008452440008541c0c0c8150300c0c0c400455000c044d400341e00180c1000321402e00c0c00c400c40d0b032803003008032003103a0040d24a0f41c0440c4c20b0080c140c1c003048449400307460085013442c141c2082007050391920504001800380c5449d00c0708187d01b6101c1c00a881c014902e85204c40310b4240c890030000c2c081d00007401703071a004034a03403800ba806461003401983d0159405401400300e00d00b43c0c880848907500c00811100c180540c41050308000f80d10080713144000d00c015406449030010740840c55003590703c41140011000e00600003440b0300040412141c41c1c01350301c12000c69982d283d035422542840100d500c01076020344085902000e0240c04680c05100700c0185104020b0458000c07015210040183e540400003000190b0b0100d003180502d40c00200b0a20b5401e02c0300c0c0e03100341507075002c00c440501c1c1c1048000c08191584401110b8041240a0300100c08990500c5150000c16840c0d00c8154980300e110b1251200c00340f803082031030080b282090f166030051024 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 427562985 1250 427561735 427561843
    0x61821010606360317090a09230c0306040c02010b060d0902011b080d0905011409010b0111071805061c050c0f040b0a06051e0d060e10030302 62
    0x58124590041646010040060312200302c40001d0080c0c0c0c0886043e4046200143c00c645540e80100d207054a02030040904108030ba5240d640d1110080c001c16a140c40411013444204880200c4242c03513540e04441500b80c030a100d180310f50982560b03842103003070b00c2c001041c101c40f60080b4058240200380942111001070022841902c0c0d401c0145002e000b83ca41c0500c103c6011656071500c880d03088040c1840c0d07003e206003c40c058198000c4d0541a0040001082041e40041400b03c0c07840b043d0788000c00d40e035450045c840340396002050008894040300c050131820b4548504894000b2031802e20a5225503140000343c015034805040f041c140d07565546440ea29012450190b42c0c41c250b48070142c0c841e03400b1445600d0286401c1c050703800c501c2e40c040c2080803210f04d050025541500840780c90b03811070521070301000d2940c03440d80143c055016554004100d42e031528145107102074026110401925640c0400d00103e6000195100c0484c403044400f051100345509111070300f0801c140f081c68130001c803409 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 427564235 1250 427562985 427562987
    0x2040e0303090d05030906040f0f0501021303050712050303060409050f1207030e2b03021e16140306070e01021002041d01090c0f18090207080a0e061821010606 70
    0x90342c8102640740445a0500103103c050741d13140000c494064899001700006030000d0180c0846044c06403042202c41c4403d55a996180c0c266003158142d0b0403114002c05041051110030440c1c500242200142520012100e031034094407440001c01071400f0f1070321f8100340d80c20440100005040395140b10261440b55040201710581e82c0c0c01901c0a800203000c0c0076200d4606c0c601400a030220000f0803d1a041d1101c507112460500160f00c0d0054040d40250b280c0f107803040c010385005000c01d00c4600094007585140349900600049250013a20a0240140c07803d2005e850024400c1e82100c03280c1008959081640700403490440035a802ea0102800400e000650905806e49422402269a03c540d0702d80e88500028048070140743c04a80000e0b04003002c01106400341080850303260407a826800042d80b03030300d86082a640a4842103605610014003094403c0d030140d619040320904a58141c50035240070345607a5403822501907207100720351038038105183c008080e124080c0c1403042002071200a41c1c0f4a0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 427565485 1250 427564235 427564237
    0xb040e0f0609010e07030e0c0306010906081b311514011e0f0c05070828050a060209060903012d111902030f07060606110a050706080604060302040e03 66
    0x14240c66000141010038468030702203200c80d05841181240300400c0d1340c0d0315000c4001d021410309014041c000c4da00a003000742c405014450182c0103141000c2407080c80e100c013040c0f030401c054110711a452042d0750003400e1075071904401d00441e4046480c0d00c4504650f24120b900ca080429440100d0b10718207025801421503803403011044909401004001046e54001034580300c1c43c000301450b04a490041010019010711055008440540f400d0184460103645507494146e10f07803c04000780d8450300d05034492a0325145003450303a40c00d5008020142d00305540d0310b90b9a908c40100100041e0300030411070362540303e410903903810080040c02444201c909000500500081c5071014944007000c0b00070000e01040e40c0148403811030f010b03040c0752a048034841e07840c2c0c1103103100b07103000114001085000d0304903000300d000e40f881c140250400916113140c01070140203039042d44c0240e02035820698641c000700c0c4010070494100d030081d0508ac06555038420001e0000e02d91600020f5000b49030419259055a0000c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 427566735 1250 427565485 427565491
    0x140d02040b12010f090b0a02190503090c09090f01051605250b0a0b03010605040c0c14071203030605031b1c080c0f24061e060d050108031c0615080c040b040e 69
    0x6c004040c0c8500115134164411200c0d8845541c0d422383c10303010024420001950b019a0358410784402c110414002a111501500c401d001e070382c000c1640080c030400a1085030707003160208080800314420b10402a24030301030780e03d101c08604092880e80ca0a10040b140000040340d1010841c040e030f2421000680c0140400680a4000d61a090001c2000e007090312805c03030000800d032684a2089910303a42c51b0015040340030051014000c007900055502004880144601d100340c501080181c01c04e824145007612014210086201039001c50041c0d8031100c4c43c2e207500e4102404981c5140c075070ba080035800d0b80325080c40184d8521074294901e050003030125001412040d203ca4009040a41781f0700000c02c0c0c4001e5804992102c2c800e000e07034884619079860150060000340940e401c103a00f29200c6800c54400341e11800450f000000d8001c0d844004118039050340e40712001c00c00040703042c0740da105159180c00010300c007800b6000307000c540150f040000380c1c0c0041009450f126035a43d29042c014181071025 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 427567985 1250 427566735 427566743
    0x30302031012141203060d0b06030708060c0a0305060105030f010902030a06170c13021e07060e030301140f030109030815010203070b0109020a08010f050907050d0e0105100f140d02040b12010f09 85
    0x1130700c044211a808801200d014003801080301d941400d03580c450b008110809402c40d0350611a582c0b002901d05824480c3c540704e858501001511000016005000d0b1040240001c1c100002001001035410f861a840b90540300100f0300180c0ba0ba494481060082c1110380091081900b80300c40d441c0c01050015440145031825505540c0990550034040181d00031061001d0703071403554075040813000345101c02074008540503140114403488680d10313040c00d42c1e000380c00812825080ea60300ea2098200100c052070950303015070080011a01c15200141607901c040c00d40c01c403110b602003202c01e082e0310802c2074a05003600005986420f50b507078030110700258000b0031018045001e40c000003c0c50005189080219517002e40005440e81e07590310100d50651082c407900b610b0a40d01d02002524890074401c5611500c0040404032403039051a20140c4400d5441e07101c018600d24000d0303001d100e6210761010300c03103490b41a1008610240c010000523804040c03400780a00c40d61802c0015030a03001190010400a809 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 427569235 1250 427567985 427567993
    0x210606090801090f060c022107060c020604050a1e021503060907020a080711130507091809050c06030705071e111017060301020d0f240f0303030203101214 68
    0x7a400d121402d072401e40b607025000603029010742000c101550064411036207944107a030f8407540703400b100c0400040c0b18000c0c4111001c01207140c80800035181b14a54080c0c9140c001808c4030302c0c180d9a0a0703074401c0f440c84000d20080d0f14803084000c3c0403440100030711041c2c0c001c001c1d4041a010000076540b941040f40c030345100314080310129240d50b0012681c020510342200c1c03664504091502e0307000b4002540c850158000c5c200143c0c04040c4025446800d000355115520300b00c0341d501d8000010308a02442e1641c0c401d0301d191140322000180b0005030060070b0350054410f030780c6907654500240c1d42401803e0000e00900c0c070203204a8552031946007031200583c4152036240340041e52000340603031483c10140c0c82003c290148224070703000184505050340041d00500251400c442546d419040c0d6004000750300b00743ea100c20b0703601c5010b274201c22038000303180c0602d2a46410900e4903441e00d050714850310001d014543e002010446a510901ca040003600c0d507590f90f03403458401450300c9040d440c00c100c0d0300106401 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 427570485 1250 427569235 427569239
    0x18050f0601050c0303160504030609060b0405061c02040e0309060c1f020307210e031303171602010c140109080a110601050f0112020c070906030b01080a051002090121060609 76
    0x2c0a801920a2018100e0045065554035022010f4a512043d245014032400344000800103c4900904c100c1c20720400b800308034ae000c2c04041c403058030000760201d441081c0b80900444464507140003405144d40407200818030500c0031070710700e09510030100c440390400710019403c02c4104001038440352040e419503000510b20864400d5030201c3c0425540300000032902c3c0c0c00340003104014600403600004420700010341e640079007140e034550782c004201881f0507041d1043c00c00502100c5910001c4a14a03e02101d103007422100719801020f107102c5000f41484210300080003070100114100c00140486c00c0208004009401e24000c290048414180007032500b882c0a4010440414082d0403614040c194002500d0880015203c84100101d030140150782445650900766080120b41c0081442d0580001c10604500f0548207006058205a4641c0e110070380b400001000000c0c0f0303100c1c4540d1181c005803280c0c180c03401221492080c1482c114140380041040386100c4469112000312512910b8210f00e0b0380d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 427571735 1250 427570485 427570487
    0x602070807052a030615030313060905100302340b0c12070c170f0c1f060509040c2303010e061504140a1508161805060619020718050f0601 61
    0x640440f503503400da084500400c00b042420800c00c81d8420000f0203503810034000c80d59540d0070010035804400041c401d141c04200380c0c14220002010320800386401d5281075001d81e101c9885645214400c05580066055032045407242c040c3c1c1208290322400e40001410208407000c540d402003821801b81c2d00320b141c08940418060b01c0ca20a0481d840905a00e09100b2400020b01d2500003220503000004100041244e081e024000f8940c1d10004443d41100b0b0141c80c0b0300c0340215203880e000302d8050f019403028040807440810b40d100071191440103402e00d401c00c00c0340040303208541c1803900341c156090111b030303580c041004102c007032140c0d070b410840c0b00100400c0f00401081e13540d01980c1c00c80720072806010940c1e48400e500075040d401e07046d40c2d40340c40c032907a80c1c2c55192074184026802200ca102a9106101c418160b18040d00c851070792440a10150038010b0006e8068440c0302075400d0791454030501c01c00d001e4002e01164000f49914414045078589800e05e02002e003400320b60002c00721450900081c015 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 427572985 1250 427571735 427571803
    0xc0d0503011203080601021204080a0b01122001050706020a0804020103050604020f0906070f05070e0103050d0807080a0e070b04060e03010608030c03030c0a03060e0717060a050609010c060207080705 87
    0xb40c0c1c8814024070041c00546054804400140010341113000f001c0d071604124501600034801000310303100810842035642042c0700c40c0350042c0c004007e0159203483c1e80010500082c25211500c221201d104000d04005c1d0050b290751003001002042c032400429552505900145271a01c254000e0300c003030105540f000300b00000c911500000d002000000d0200048a04004003d04105403086942c1520a1031542342d1514050150344103800102d420300060041080500041e6442d00c0c007070800b0a4035091400d000b400001c07000b8000060f4541d40d299085800300c0030003100b40285800da905a540c0c503202d140042c009003406000500941c2001e100007155400002100c4c1c40d0814140590f040d9124800d0044903584540740c042c041544900c1c0106013101e12981e014007880c4c01e62641c1c4908103003001c45080d2004005c1100307108600350001040176032529000c40b084a0f07801d2a008820f200d1502d0018001d001e0081c015008590109004080000004040301c0525004503051440c1c08840c514000d4 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 427574235 1250 427572985 427572989
    0x12150c031815010b0a110304170f0c0306151f02010c090b04031a2809141c03051b0d090506011208071709102a02281a0c0d050301 57
    0x52080d110b401004035040f0000507011414407403620301051400c41500502d10781080c3c0042ea40900815000f103d2460200000305405205402600d04c860f0890000b80d2601c41c0101030380a07440344112030b80344c00c0c1d0b00e0040500c031080144100045c80140c14400034002c211902440d0040707461003201048250f18801540c040320ba01080c0d00c400000314540222000d03001400ea5407810701c2504c0d60022516103000c102001c0035204100003060622410150f0720f40725400642e02c09074014036020f0700b035012094118644070502d8107003c61542c0302c2c0d0b040041850030b900102c18200e240071910b9885c10602d40c0103407002030b000e2030407501607988070003c8030101864850f0041c5508820803105000170805034110860303158000501c1d003001800340200d02c40c8540750004400081e0702c40810340412102c1c0039207452500d1035001e907401040f850380c041003008103c0c03104800030300c13030b0030440e404500c02c1c1c820300e038014008248521034443d0351104040c0381c0d50012540c010983c002c1d84a8080031901c90019281 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 427575485 1250 427574235 427574263
    0xf010b192102040b0d060b0406090e0a060c1206060e0a140a12030207121a0702010522020a0b0406020303071407020a0504051302040608070905090309010e12150c0318 73
    0x15100c00031201d007101580a094003241c00c19140e00300e000144e0341e240440c0b034a03140105c0740400c2c584c2468040100b02c5400350018091070f442c2155540c1e04900c0090520740aa0b489880000c0040469405071201000c4252440301c990502c0e2010030070540c020409001e4050554070300c036059864003a0f0404c40d010000d030b100d8201d01c1d08601080a040580d05140085000e8015144080d454a049880034494a0002e4409a1440030008030075007282525075442000c5200800c51810601c0c160b0520f000d0f1071118880c0b2405034141e40d41990385299050b001401c0310941c1c50f81e529600d120181d02c0ba0812920100403800151003003213510300110803600c401c3d500a00c0c46008a09010420005150107411110480301c00c100400058443e4072076100545800d000030541c4a150190450540e417004020a50740d410a000a04059030060b000c010b51040480e08072100c01c1a00c0c20322071521041000403036180c40d00500344546042c1d82c10003103010f400740300d0f0784c10a204031302c9401560f601c5146044007 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 427576735 1250 427575485 427575509
    0x306050c040509060f0f0112020d0c1d2409120a1416050f040c1b08090f0402040f091806050703051605030403090308030604230a15030809040c110f010b19 68
    0xe61f507108070590b010300c48181c0030050800704000500c2c01222105919036002c1028420f20b00840100102d50312281c240c05c0399003c074250141507071b0725041080d003015554480c2001c956410305980306070700070f03410300c0219049580301c1c400f80c20107a04d038188001c5203049074010b0600c0c2c082d000701400010780a03100040c0810f0002001c0340240401804c0e41603013201003086002448000350b4480d40804130490090346800d40b100700c5c010401260010f04003009204030302c1000100013072000c6601b08402c4455146000070401c911619020380703143c550030010000351808081100b280d1f010b03445240a0f0074003a4903c4030401c101c0c0c400381c50078801070b0390140100c0c445080c10000521554000d40c0c0c00007002d80085801c1641100f085105000e00200310f4680b500e050070041c00282c4c0d48950418611203100202580b0b1450b102c903202841100380d00c41c0159200c0c0303c22007607075012b91900300082c95014120707190340b59000c24083c000c1140d07000e4503118000503034440c190888040100c10545a005406d0303 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 427577985 1250 427576735 427576759
    0x1a010e06031b211902040f1e1805030f07231f110c0709050609040c060c020409021f03050601030507020d0e0307051f030c0f0c1104060306050c040509060f 68
    0x1200340d480511980800342e0302240c0401d1406000c20140303190b841d4130100400c1060b104000940d58001200308a0510704510000311005007081505130307240000d400500003000211070407400c404850040c4c80d0f44800680b500386c2c40003101c0101031031406010301c0728410400003041180e0182c88e003442074050384441c0c00100048404810103104400c0350340700041c0c20708121034864803900070a110300883e8100b400708005c480c146003c3d065009200329620141d6150a507641184203849004000070044124815000c54680d030788003550840d001045015001e00e200041e420340c220120b0f54000081c181004a20154064050580508201d030083c003031008031220110b640c041c4050540c1e90610500000190a454400f461030070880340c0440324422011540018040d1103095081004108821346181c40b2244e20500141d01d865120300200b0322141c601c80001c016240c99080039001038030f46401d0001d40d440030030060048900544a00f69595034a404000d1041c2d54000c541c4c0d00a00740c400e80b = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 427579235 1250 427577985 427577989
    0x9060318070e16020c0405010f030f110312071e03090b070f230706020c03030f03070c020a0e0702010c030209060415170112020a1e05090c04031a010e06031b 69
    0x1905880008680c1240d02407907a070803408030390200541d1400340d940059001d0710015941070190010604082d81c0a001a500d0710454580031411840084c18240e002280501000312094951004070001007ca0313041d81400c1d002d008450340841c404131941c90007540440c0d004407402800f243e086030075450304041c15142200c020104c0d03000d00c0003283d0380400043c0799800545000402008840f80442c00090713260040303605860010180c1004095510000c080f0380d05030780020444552189100c8420703104c1e01c58400035a80c10031181c00080d8403610344c00010620150031b0211500ca50b145074024411310800300800e13012485148003407074000c6402c100c18444011980101c407050b07003081c07404401013846d03400b18961030750003a00401c031441c440004003419880c0118070351000d400004030072140d100003500c104000c40103c0c0326840c010344002d0001100614100306817001150000740c6032540c1c030f030800d144154948090140b40120700000c400304989040c0003c503c004014030250b030700b03010a00041 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 427580485 1250 427579235 427579261
    0xd0c08070e09210d0b0411030f0601021b1908060f100b1303060513080f040509012309060111150105030f0102040308030c2503030e0d020613170f1603020106050303090603 75
    0x68444c4029480318028255503d076886a4200306101100076910381c188400c2002c03101e60040c10f194110b500240406001d8030513a03a801140450880e00d0341c0c0e482da8060080d486c441401e500c2050346009440402010703c03040740c0b2440c440d64100d820500d00503120259051a8050586600b401d8085000c00b480010416481035070007032a80f030585547c2415030754807140c003607006003a601540030001c102002142030640394107000d0403c500f03403c100308101c20300e649000f002d103590303a80c881c03080d850103d0056401340240c40001d103040e0741070b503040d02c0742d110614200c081c080c85014001d00c50308140040980040c82698103480c4c3c000c2a02d85076494070240440307182c108001044031942c642c140005040d4510300c40342400d1b8401e803000b1134030061907101282070800d8031800e2019500031008011003003c06181d02c09245034041a191050280c145001d8040d00410b01e100c2c98907080016210259040006d0140c211031003a402880f00741d4a9030300789a2240204406542c00a0090000c40d42d8051042 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 427581735 1250 427580485 427580497
    0x61505040501080c090303190905030105060d023304030b0c0c0d2115060e01080405100c021002030f0402090903040806180307120e130e0a060b0d0c08070e0921 70
    0x54038240004480024156846103030b02c0c000c110b500320040c8c0402c2d41c01c08038840082004034003c204c90303d401408105080c001c0d5070024030841020b620542400740743c030140355604100e082d544401080c400d071034a0942e842400b05540480009001494260900f0101c0300c4000f40380000c5d2600390202d04007a5918101c5401240c03020308005056115108c55216800044010071504000280703000c1c8050b1002d114081c065040144070400c01000c02d100288844990058260000c0d40500e0f00004a0416000c868103211f000d000000b8491054652404a07000c0d50085440c0170094032440d480c070b50f03a4821841004500d80102000440300749510b841100c3c4401c0060070f503480c048096580202c00720740103003494040340e02201e48144a007403c03104990f8524043c0410412240b941c032038035544001101c00108407648602038070713001e40c44110080900d5580001101c114030344541d126921209903000b03500544007000001101590005400c1d6100b24500203201880400342d030b110081e41d8440 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 427582985 1250 427581735 427581751
    0x150114010c02150a0216050402160201120f06150906020a120e010e040203510f0a03030e010f05042d0b0d0504050d020105041a0a090209150406150504050108 69
    0x101c08907480740561002050004d502e44d01400c1100c2d80045080300d41704c0c103900b01038010361042c003540c0500010000f4001c203203502420321403e48084029400007410121030f21041007424900009004400401007284050094454405081d1503050499440200610140600380131103000007066000303103600c2260034070601d4810a040e9150002c10140d030700547d1102d44460300c9801701c240314000f00190320700e01610844404025502008903000740150316120302101018002407209560390409100e5440e20040e100c0581e1a0b520b04004e082d024031a1040c034041240c500031802d400e886a0b0450f070685a50b07c40218180780d0600e0605071070700d0002d08441c07091240003408190350410b40007404512101400c0810945000e241c400c0c00c2c41c5c4e204c514002035a04000610000681c03680d2246100e440c40d043d5140d10781e880c0302c01d8102400990602075044038280007030101068540a901c00300450944081c45525a01e4943c90010b0030410b145800003501400140300303541c0308100407034003c890 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 427584235 1250 427582985 427582999
    0x507081602180601030b01180b0d0608011404120c1e1a010f0317040602073003080f06030c0108010603020a0e1c0b010603110301141206010e09150114010c02 69
    0x355a000c59032081c1076048801d95400310300108281c40d079040c0030340315801c0c500780fa00200b8201800c4060515900c6406104007040d000309000c3c001c81c69560044006098240092100405103580301100c03400907601994080d000004203040030303002e41e089500195001c07000700d1402c583c1aa5031091086115011a00000700d0002070b10b8003000160924040e000200c40b6082c990700d141b82c03d1001d01e44c0210740d03041002043c0000c02030181c002c0341c00b00898118002c454414102600944900348181c06c0200c4410351004800c42411b6000d04510b100380c4001140c0030468480d031080642e00c0c00d800304410700041145005004040c4a600030340b522826508001c4001c07901c0d60009075024202ca2141203102c410712501405010080354010b006141c0390400301300144814110145520050140003044c070080070005600d91201c40b42000c01c2c0906034107940180d41c44e04141d4413018015210001180314191549082c1c62642180718102c0d10502d80c5034510030381c104019140d01d01c2051040c0c1c6c2c4030f20 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 427585485 1250 427584235 427584277
    0x220b09042108041716170406020f0123040302101e0605040e0606010e0607020a030609020103110c0a020f06040b031828140a0b180d0c05060406090618030507050606030607050708 78
    0x8180100314070b491040140b46e616141000e000030700d4954114002e80981e8108489c1982d1607000c00b50807514199050303003245243d526400c3c142e01e481d941002212506280c61707074012001c803d03101880504034000409000540e40c0d0b0041205139482c9072000c0c04a5002030004c50010760060000d107147d548050004c0d410415182c0018401800503403082d10b82076114884041150391500c5404d99031040c0300145824000d00c070071420b0381d850b000c00009000380754482906ca0f1503698041030302c0007000b0003000d0075580d181516034244030002041c0c08040c984110fa174403044c6110f11040d07514030040c5008911014000c651950000b21040359440c204030b008012000e8085842265220f03c241c804042003410207010002051400403400f0744d52080050f414132600c0080c6d8046202600541c201001080c804414101a00106900200040c1d091042400c5c0070825410802421a003400f545c207a803030340c0e510801819120102211500c0c0000d40030800706000491000181003c8260940c10b100f1b008 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 427586735 1250 427585485 427585493
    0x20c18070818070605040e0a1815020d091b050102030c0c060f040905040f0b0114060307050703120606020c1906090302120a0602031510090302220b09042108041716 72
    0x100d8104400041c00094288108540d0180c0c148d0446180f0070704010700048500c4101411a0701c5400810001d0b111903070094444803501035031421105c40c0c5040001e200d9500c1e00c09150950958410f0010100501c00151503001005460310351101300d020300241d103075420800489a000c0c01880b2200310080c800829039058070305c1428440d600c1801840540111400c1c000380d00c02059006119094690307950440545800d01036030b400202c1400c0007034441034075180507201844000c16050704146000000988564000b07403040c0303603840c00d4554100320a40001401c10000c824003e1074040751010700d003000107040690b240c8520b1040e8405a954068496840000380e07401910307500002c1201181c52032051612018102c6034001a00b0000c110070300c4c2da8089002000d502480c21070001355404020b194500d0790704001200352005000d441985042d240c00c40c03901c2c005440d5454004060f4003404c1d445402103007200e00858020062448501c040b90140c08075601c40c12400c141c00f80300809100000b = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 427587985 1250 427586735 427586743
    0x1107030f060b130c02100c050c0f060105040b0d02150f040f090c0314070c031107050306190c0f02120708090301050a1a1005030a09140d05070201020c18070818 70
    0x561103000086110207400301041084480c400d10031101601d0a03150380c18180e000a001d120301a06d403040414014191542510075010b9004035450380e00804180820702003000c501c29041c2c650444040020003015000c2c884c2520440800039040f000e20044884046400d03005801039010f2800714038985a1a00325902d9801810780c000300c01d050310703950203000172909809103c44110500c0309040c118544000003d01c42c03101c030840941130080ba80c001c0584903409225000140030082c080752141d041150b2030702208003203002c05a10079440c141c20b480a0701e00c5048418400c2d103040e0300512100e50307250300740c1115900058085034044402c0140070301d41e8600f80501c1d84148144440041c6070004107000003402940f44078100d120300c58000c0010341d03068000c4282c9400c60141c0e080000c0d005400e01c0e01c0c942080310144610b0503032042040030714459a002001f03004451003a8242c0e6140125102404801e161604005840c008900300280c1903074815840c50b5070004204050707940384440034100c2410 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 427589235 1250 427587985 427588013
    0xf1104051c0c14030d030e15040201090506040803070c0512030a08090c0907080f010b092803020913140106030206032a0c030a080105030c0f090417030a0b10080f0601110703 76
    0x211445090f400b0191301e000e02c1503070482e100604007800a4610b0525958030382c684110312205209041c000300d019644581e00880142c54042d00a558aa4903004410b5403508100022984c101c004040881d681c1040c4c10003803445800f140056041090402083e0fa507010000c2514480f48901034284d1219034a51440500565564440e51110b04001d884144da19138141c0103080d01c0182080141540d8036056418282404910b1444110800c114006521240c00e6400698007048403010711451200421110003000c1c0302e00b100d401e0b8900e1024466080c0c580910010350f10035403d0000640c540691081c11030104001481600000031040541c42c031600110b014007841c0e4000300d8590081d030703002132059014060403401800c402c0d4070340002907680d100c15500a4040d0307125002040070005910742150300711104405e419228903051260400404000039854481d604d1140248240b50040c50514021842c80d60200c02e1a601d410054500215240b03140116100e01c2a00201040e000740140070 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 427590485 1250 427589235 427589249
    0x80f07180b0a0e010f080727080f0d030c091205011d0c13060503071703300a090f1103030d0e0303100e070f08070908160503010f1104051c0c 62
    0x515040c8a01005196840203e1480e05020f1380301705400b4041e4022041903404500c51a120b54440c140d00700c51030568039110864030160910001c04142c500e2701007418000d0406c0c4200b111164507404404074141c030900c076005030110768941c0c4207018050282c106041342c80d02440001c11540000d030b0414500440c624001e0005801003200c4450920349031918450805d0081002c0c81802c3c1403000094462a881c41040c110640d2161025500b5609005032000901c0480a6008440c1da610171403205150754106621a610f8050025a0005085c0300e20403501e80c000702c0d040301c121515510714500d901403e0800b83e1600c005e01003900b41d8005401250302c140f4255015688034100741d603220303103002203a800c1041800742620400c940664003044100403111030340360000320b03504c818a080c1c8039208a81c1050750140907101050003d907401e007408004858081d402004092a0400c150382160065282c10800c040100820011481d1490b40440000300b0140c5d4001000f256550382d10701e95410fa441aa = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 427591735 1250 427590485 427590487
    0x1211120405161202060f090a0f03030519110a1b05030a0609050606090702120304030c0803040f14030a0903110a0b030f09010b030319030c11030d14010b040501080f07180b 75
    0x25540200450000000380007050f54010780c0400c66000880c18010190408070008001c00c0c03003500b550f124010700c2c00030000400e400c002c145c1c40e810000d200c1c0d400380301c518011a90071103104004034443d00c441c00501a03038001500e03140040b036a03041d82039000038040501d04280c401c00462903a40c24400500c03218403440c0300158403803003481c1c807600342180141950b20400203201000318040d00802c04400c54000164225a25500c0c3d01d010f842e000c3d4901c2000d00441c1010041004200312049080502c0d4021540b80c0580c05810f0325440c3d076407144442c80000074161050400000c0e8000603c2100c12a00030200c0000c0c03034a82c04161540d03041290041101d80d0300341e0034409440c10030300c15019900b2080e00507510308590380360301942c1403007045104402c05995010b0201c029101e20300312581240360384181d80c2d6a9001c40404405000100c00c1c25140561075000000d6010000044408603103046c3c40d110310990301d280303610741c0d1444000d005005200d01209152914000043c818025000c010615 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 427592985 1250 427591735 427591753
    0x7031211040807080a0305040e1f1d100605191b2102031206130b030f07091515030507050c070807061214060f010e0909010c18061211120405 62
    0x9503107000c43e80e80c80300400b9004048800086940f03c0c0458003650f0094103881d1180e1140d50740f40308c115451482d40c1540005210010414140c103402043d10324408115a80d1251034103071091500201c24401c58010070800c01c064000300c40c20b0541c0c80c000c60724504049a00b200783c040c4805440d07528402c00c5a959200c0061180e10030b0300045000c0741c80d0314a2005509051036503e020750045400b0f004180314281c0d068000d04004800d03005152007401c0901668040001c0039401c1e0703510241401100ea915040401c146030180342800002d0446840700701c450002e03001042309170300402c1301414060400070200000d048800f800c10a610042c400c8500502c002c1c0d181102c010000703205500707255521424080b0500c42d98454240c55034101d90b0403a079501580d810400140c403d4104e05560641040903081001080d0300c0c190301c200030102a644400158811000120224a1242c0900310106001d03452a40e00c0b100309031f114514440032403448a01e8440003010200e4507840072030b81121164040065 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 427594235 1250 427592985 427592999
    0x403201506040b0d0b101a090d060e150108120a05070206031e010314120306010c060e03090a080309090a150306051f0306020c0d2309060409180b07090312050703121104 74
    0x141800070081c3c00801101000250312a801b81e21510040622405510041e03505115680d4480610450b0034402c55070f084400b05c1c034032880c1d14401d118ec41c0701400f48160b182c98400383d480403514030015030303510203140030410b03030030080660005048040142c0c42c1604070181c5140300c2c0401e0740614040c0c5003e240008828020702e00e40b0780d180d4002c10701c03408140144130040e600104496000c6900107408180c0540e00c0304442d185009000c2c00315404041c0420004a01c5c0021009065906003500c2000203584c81e105001e0613506664110300d1b0781d2003e1041040031510341d601079604040b03298804042d0b0700000300c01e60320481040e081a43d8483e40010550522401009540d00c90341d15410000411510f48640d40c40d06200c804103c80c1180001607422a159120b100300c501501c514041040640410380991001ca5010101103c0000c0300801082c0a0340c000c0300c019003101c0e1310500150b0760080c02304044039103070400f000031001d02000c011510040041801000e60360f410311113400751a1032400b00 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 427595485 1250 427594235 427594261
    0x7120501060b2208010b010c0f030e0301050711010509060615250804051809060c0904060f060c150e0307020609010e130c0f03091e0302070f030501050403201506040b0d0b 75
    0x4c40000c0c140c0c03610b51a920541d80081c0c00c0a41940c00100c2c08884030024103050f140b071024a80341c1d5915500e40303001c100e5580c0e00a0242420b010b03a02008110660300c88020030307603402095504580c080f0020210390214520f10008005840d03003c1c400c0b01c482d0301c49082030580041d900c0d404850151020800384450309002c45010801103c07101c45103100d041c404021621031002070048008840002095a0191110340110004061600b180000c1a82c2c44000810030444080212981241d14410048410290060030441c0054030091803402c01950f08000e007079804480a1418402c088150f10702d1692421001c2900f040c103840080b418280d0240010f18443c0052100001e251030000342c100801c034140c2500031594018016a1002090350505030300e410840d03841040c43c07043c90a40030040282c19040607014138440e44808941d1807426a0f10140079030f80600a951681c0032400307103800c154110b21101d80164014200240c0501c00d03c01050f040c1c142ca8a00b500d00e46501010b0003001c43d8000 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 427596735 1250 427595485 427595489
    0xc060305060442180c110601210303090212010f110a050717070203070f08100e0c0d031b0f120503060321120f04150203010807120501060b22 62
    0x3c034011000d00072440020f074800001c01019489010a452401010340a01c582900504103c43c0340d0388801c042c801000000d0302d00010400c0000e02c030112114207410303000405605880c0f00325000003144802a0118a00c02035034041a410103407502000405600c40c0740504201e07000c031900206603c4a04030b425800e850303041c0128548560304000c41408507a000702500c42060740403940ca0001c4001040e48040b9004d0400069414021403900244044080401d03008985015040c0c505c007081e41540d01048640002426009030010b4840d640c1c1480c021003402807141c4603091552282c640c88240020601413800b0440d048800c5040100c06e005240e074445000c0343e914038205240d460030070f002c0394490b8011622840c002d022130008240c040d001c442600c085001c1c5e94501c821034a007480c0c40502d80c0c24185e405071426010070507010401c106a0017202d0603900036a006049441c9001a2500d50b00503509080d00c255594103404525003100d0001810701c02d42ca42980701031640c520054143c141915 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 427597985 1250 427596735 427596761
    0x19090503031c0509010b03010c0917070617310201090e01080a021c0f1a0906010b180607080c150a090b0402060d23090709110702060c0304030c0603050604 68
    0x511541d1845810b0190303051a103900c001d40410f442e04c0304a18280501300b034581e00c55240d400c03d4240c040003640908040c3c12901c5518001202811a40c4007a40300e0610740a2400000d140034150350070349004d020200e4104030518500044903c50300b039201d04611041d0300c240340d44042c50300b510b0299130380081014090084074203485965450031400950b50b18680f40001d00410750f41146080c01c06503143d82000e403d80084106c91241202d10b0010104c08003000801909a000070208034607402c0012500d043c0d54142c00348915021541c03400c2441c03403407020310055020320100702e802c0c0050041000b030141455000d000b011607041e812240c132240d11004000300307081854088110041018144900d41141c0c054505607a104030703181c03125000d001c100358020043e45a0081c134541544041148600c00d011040a07510819160301c14071041c0d41c3c54440b030106001050042d2005481c0050041c481c803450681100d00d015641d9890015035062a400f200100e9540e01c00c006090038180208a41c0c0101c0f = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 427599235 1250 427597985 427597987
    0x150b0102011116050a060e0102130e07080103420e031c050601170907090c050a080f060109031406190c020d03051008010906020315030a0201050a0302030c0405061909050303 76
    0xe6010004014080c901440940f0307110050b0010501000780048040150425024024199031100c0e144c041c0d4040d048441105d0f0110200040c1e403481111428000d81013540c0340540d51f481e6480c2c5015040c4070003c80f40c490900702000c28549882d00114030702c0328410380c0703c0074080b90b4120000c0003244c580c000b40898540041240c900d00012000c8011301c489802c1d10001103075110100101d880800c84410304444c0308001c400d00c100c801d80041c50404880d00200c050040701070880044909002e16007212000ca4000000f00e4109158030200c280d2007001803400b140c0c1555a61254120a051001401e085811000601000d2000a0746030001e4111044003032002d4550304100940e03681016408904240c6e0307400200e40304504001e600001010a00021700100400d41428402036200351599100c43d000e5400f074210606010079010181c5805845450801c0c0e14050240c001e5030000300f10111a0a0400022842c2ea0b11640a02560b060710101035031f8400310040007410600b030581205220fa80 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 427600485 1250 427599235 427599251
    0xc041e0e0603120706110f0d14061c170c070326040f050d030215160909090203070b0d06120b01180e19060e010606081b030106080c07020f0d150b010201 67
    0x103a940104c80030789900c880d0009201d0324442a000c214002c00c08241072140c07002031101032140c001e40040e103180207003130911507054a1b040104403031807514070008041c4884546805010440c22990320140410304031266182c450090103003401d01505400c200c0c1d003411665140080141c400d1328152078050442115460319040c00c80100b103003605031003400d1040469903204ac003094030030f00c86d52100e07803e003001444035420030340041402688007034100310000d0f445140000da8800640a4041040e0300540984503407802c041d80140d0981c08488030300781503602d50000088850b18000180d00c0b860107401700b2201541440110700c50100c003070050301c00ba103040103101c000d05031000c80c8482c0e00c4680600441019003551402001402039100002140d51030100b0000d00780f034010032901c1c822070344070703201402285500c012080540003c4c0520310029a100d000150725807071032001050070300c1c0010003000d25140d070303400041c01034a42c0985c202e440748a4001000666005800b4024040e01d0900081c040c1e24 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 427601735 1250 427600485 427600513
    0x3050d020a051c0203190201050601031113090c0c150b13140f061306082401060e010c0804090e0136021306050904060204050306010906050d02090c041e0e0603 70
    0x15840c080c80f541500d2078a01d4500e88940204100c0e014030749920f94104034400c100d14068000c4c041290420f000c203003400302131107942030072038200d41d540e11801403d4003d0341c0c20700035403a0007808040c07420300500016600034004a00440d2084400541340c15021907455505401c4c40000c07440c000d0b96900702402c11015080d045100301c405503000b400394000712078035a00c82001580c4440485038080045d490031102003041c00c0c3c0415400308004407640d00c6500c07070000e6581c0e10706901c002d200d4580090052002e42c50658442c01020381c0880c00340c80c0c145d0070b054035119150115180504c1001c3c0a85d5100e050301708403015090b40d501000d10440c00054040801100510488102e42c80240700b0307070716045501c002e002568401c4d40a443e0242607140a80703094902000203511900a40f446031042e540005281300050040c0c6050350b1001e0b105510b031042590078003c2c8040042c042c0718500205010129540c07207404019000014084149291503143c1410000d0455010340300900a40109203005a08 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 427602985 1250 427601735 427601743
    0x603060f0630090628020706020301090f0f02030c0a030f020c01110c06090106050a06030b01450501050715090c031217060f01120902041503050d020a05 67
    0x40426140d0854444884000450074461070312a4900b0715810080d01400d0902c40c019011140c000c104040403584070800c0c00b5030790b40c078215105084841c844642e0b005841e05600b90105003507295070094104140e42d99410142d0f0001d8205003c410b0395010301c002d2501d41c5000340d80c05420031640841c51400c1441340d000441c454901313043d05058441441030503a03110381d0304a4004040200c000c020b6035003000c480b031456500c0028023940c103105a030042100405d041c410402103403002001243c0740c0349014425409011f0b045c924906008104442003003c8007030118410200b110300701c10019644000400404820501c0740c80c6e09000545201403009907002011100c41e10b82040c1d00401d903c083c65038080c05401400f80c0140f0621200c1c3d800410030603003081e21240b50346aa1540c840310440303c40a0002c0500444216900c40701ca0001e9060310b50003034070054a54820180e000c50441200c0d004101030799040c0c01d42c2c10594203040c1d02001808801c3c44010072848413403018109441d138503140c4551b2 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 427604235 1250 427602985 427602991
    0x5010e06040e070507021003050f19091406061003020301230a0b0c06100e1509070e0a170c01020a0314030a021908041101050a0206010b03070207050312070201090f050603 75
    0x61104416846109603509025140100348080c0420640d00c0d00807401003072174001c2641280030b4007a10b800e410140e4000c1c090700e442a002600201c02e6a9030f0428600880d5481402c0100700d40d64460500c004105490710886030042d8010041016050080500901c88544844c1c0000c02d8810701c01032100c0040307480704007c55900d0000f0403000100311000115520740307d41c000400c00c44001460301061101041e000d10034a008072418421903598482802203500c00c6031200d080b03991001c0b031040030b03140c2a81016000b02d030900d0b003901000d0b031070000314048040940213140c00e1001c00191440d852400c00c00a1741105080c40581030044095402030034500d105560054189400b0002591041c2240d060391800c0c0030f00020245c02c1030300c92402810a4405507025141014040b2054409500881c01c07950035210076030040005a2910204c0725117600043c2000c000c5004807140040d869500304a100407440700c0c003105565501c1782c0c2c40003402c00d10503640030f4a02054581410002940e414050b01e80c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 427605485 1250 427604235 427604237
    0x5070f0c0b060603070327060506121f0209030f0c03010501080c0d030507031e03140f0705091216030507080f12070204020307181715090613050a06020403140606190501 74
    0x244a485d100d00c160054400d403d203000f0040e0301b250342c0302010a20851710f040c5250003128200520345480c0b05011a030a03030701a07492040da000c1003454810401041180030600e840500060404002000103424100000c0c1546003a038003000804038645020700c1214014004540205140b030180004182c1041b50a44050280000803465900b45405075040c2d00d29504000186072031075941004c0680101a2030041c00449041c03000028050b910f050480c0340102c40301c8d111182130040c0b94040010003208402c1c0c0906032700840704450180c001c4c20038803e001c0d5100c0d002401d4158104114546002c51410082c0d54542c44042105440f08100013180c007256015280544e5a41d0f1315402500d20204445142c02c04020701000001c1070341e1200c02d090007151039501a50000d081d4881c4030358620009981410f0650006004a80080e506084403000103104d5826245c2c0001161034010890300a54003e071440e000f6503070034544440c8c0c2848555400301d011038811383c2d102200074174119216054014a4 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 427606735 1250 427605485 427605487
    0xa12091a040804150504090e0a0206090f04140a050612120d0207030315090f150311040905190308070e120a0b09010e0f03040503120c060a09031b030305070f0c0b0606 73
    0x7a09004400c42264007405010310000340c8140004c0d0b0044c1241d215201c1d03554058505200700034124808204038801680061405003000044c1c5e0800109c0c0d4000e18005520503544d41030714115180314920a0701c18002034000142d01d150002c10b1002250310440c03090300c240c10100450850b410010706490090384c10540044e00d0304618681a001030028044410107040030309800100d01030b090b0004113141c08500014051942c0e182c02040031944d0a000c010f003402000b13070124490741069400400c60a000f08103c4041c120a60840810340004540c141e000424110400043c0d940080203698251401c0e92005a40c0c1c00c0c8510003500c909500030000c010300070321408901807607000d401401c004a8074000f0740f100747c5500c1e1480741d5203a1061040600034000c0000000ba403d5250059540f120030001c0030303014507620420350400030304103460201e040c0302c40d13014484030b1050040880941180f003900c0001e00b6041440001d062040e51400740801c12280d26481000100d10146090b0030a109550072 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 427607985 1250 427606735 427606741
    0xf030c1602090906100f0501120f061d010807052d040608030f04080105070305100e06011407080a091e12050a24230105062a030a12091a 60
    0x31594101060344003035488944941072055015001c914a40a4040000c0355010300d90b0300d100001c1d954800d4410305000c200803414401c0d880320b494100b582e04d03640403038000a040e51285d5200d02511000307649003403a0042040140b002043c01c0000001410b82218002c1d586080c40388124070010f2a40411024864084041700c419281c51700080040e15800050b41c2e1038400070b644001242d0002d1180480035070800c03021a142e01d000b07201c0c041c0244074410310703e98584d007001c484454800001d0511030402c070040b00e8031a05841c040014200300740c0b281002d10b9a030708164200400010054004103211001e80c12120b10034410f40300c03071000b1a0701c4003400800a004a042c02424079503c00405481c04050921007154014640c3d45c000c01000012010407898848080d8110f006030b1000032070107240d10700001440f540c94090f020304a49151601038a0740940c4200301d550010300800d00302c114560011411641c050740202c103c1c0f8441070045420883e80c0100d0300c0e1110075000716540704400e14049008 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 427609235 1250 427607985 427608007
    0x2904090209180129060705161212030c09050f0117090304051002190b0c0c0a11011b0c0b070201180e01170d140a020a050604080304170f030c 62
    0x11060290020008032240c07a02c054480d4200224840c980225407074a608000058042d00c4400c01c0c02640000103840305000606003c16684070a20984840c401e1001d400c01d0019000001c801414041028401c004281d10b011800c03130745515030900616050000c1622072640c412403180494900310b80e0441103070319500060f28110030310050300c0d0b020030701c8004001f0f4101c00080140100e03582601c200403500c0b1003000492301c40d104d0324180c880c07440c11070101c800881e0031007610b03e0f0041140c080180c6400001e25110f840c00321858000c40f026107a08103945480e41e0001c2d40c0c1c480c020703980849440c01120341d69600d030000394180a0350068480201c0c000b400e43e48501d03d000040e95441c0348541c4055261076a00d8014442481060442e907820300190303030010004515110641c102e81c44100002c0c003244940789142d0070602c0310f03004503c95030304417071b011401c03c100c16070149000d1908650f0b24109400d00030008031603200310349e95084040200350b0014440e001260350000301d051403140c0780c07802092 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 427610485 1250 427609235 427609241
    0xc17030f04230114150d030e010302071109040f03020d03020f09090901151d01090e062e27020702030303010e130609030203030a05060a05030d260702030c0c042904 72
    0x305400b203a62030800b480f24200b141d450580e005a4002c1d450340c0f10080d11208001c0207040c0802c008000848000380b211165009030040c05040c1c1c4107251600403814040049080312034111800d03140604181200c00505130180301c0203543e9101c500d01545032141003040764400384a00e26003180a0020314000070b102400a40c0401180075039407100d1000c5070b95480e99104544000c1204040781c420102c00001d106050b44519141d0300501c8001d0000c60f5a0300031401007000d030f02103c40c40e0902d8403070b040901035907190a1002c09413003105440d40b504043c1c009180030102140c00e2010341180304200310300141c0d400005030390454410580c3d00301c8959440000c0c51000c48104030060000d41030101240c10142c000c0082d604c0b400c503500c002c1040b55102e0f010031585208500c2200d806030000c024440c0da8900c20a038104100c1083c003031103146007850b904001b00c0414110354000c01a04007055000c00e40f2401d21a032802800e00b10380c1030000c1c0300149a80240329640c1e40d071072805e8a108031049851522150 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 427611735 1250 427610485 427610543
    0x120c090e07090b101202090f060d0f0e072702040f14031605100c03021f090b0c0408070501050901030e01050406020409110f04050607020a030f030c17030f04 69
    0x50400d1104100e8914a540c1d240d01d9070240d240010b0074001410441d0a100100c2c03941400c0c00e0340c940340c0d0340c500380030b448000b5840b03680441c0e08550001040b100d00d4407040000c2c090120114800039030549498468001c4035030f0149800c007242c00c4084100403001c102c5a002e8044c4000c22201592000c205a154000344941d0b03000001030795000c0300014680e40c20300305074810f0180c1078095654940d21450b0301c46100c1d0303c0d400380d594421807242035400b84a200720320140b81c09210b801202d0301d140803406c504002c8080384540009039611360070316600700800b0701d000e541c200022144140c242400d10170a0f030f890300e500d402050304000c0d0101b140710b41a80300303030025030414848078020043d1f030800e820810041d40c8075008440e06141403241480c442c442d01c10448494644404013103041509200802280b03900010090743d225000d030b14080045407104040e0132010340310742c45969604000e4501584030200002860030140b0050040040080030042c840d0750140e4071180c4020481c03910119840c0e040c10301 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 427612985 1250 427611735 427611749
    0x303030a051f0f3b0601020a1505100b070c03060c0c122a030c060b01200d140301150e01020f0d030e011109010f0804050a0819170709120c 61
    0x2c2100040c80032a0352000d88141c42514450b1850b030000c01c80c01c51800b2940da40703020b10350b070b4852a8010000381c50020f010f810002c14030580d0f0b801412030f00d582440d141c2c80c0b070194101982c0c410612825442d889968801420343c24590743c140081900d50160800722480060115921402e004591074410a42c1e041d1083d8019038100040113460030041000500c100f28402c1024245685441c8120040343c03083da0945c9a9140701500c0855a22040a401e1001070076052010390300301c0c504104607140700b10281d08801c00081007075401841c0020200d040007480700282c14002c100601c1000403650113100914000e040c2903c0441c50180100d2800810342c2d00003200e80500c1d041c80d007040c0c0c2d06030000154404002c00900c5902d840c486540c00034030070744a8090105240d40107421802d4080e040c060fa2081c001ea0580b90140040c0d111a1015400581c0251000690300c2c9a1001031707030803117882a266000205201c01500e8440750203002880385000f003001300080b00c036202042248011040019000f2 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 427614235 1250 427612985 427613041
    0xc09120507150c0303050f060d061a0a03080304170310170f0303091b030111091210050a0506040f0902010e120102130623251103010c11010605010e0303030a05 70
    0x82d00c00040c0b80005000303040340000e0130721000c900001c4100f660301c2c0c0107440c0181f0b203200702d001c0f03a500c00c030041160203480b02104c02c9002c01c404050340c818030040c00a50103880050350b41c0c81c0600d800d002e2900148031a0310f06c040240184000141d00d0103504d02640d00840111401840b6400741e94581400351034600401d100010411a40c544081080712101c50741c141a8241d040311764041600b61260341403520403406060044004030310341a1000a2040c180384207035204140e00d0542d207019101d0840d4400e1059032030b4428416a42014401c0c1265000c5010040045400e00c1c0c0c0024282c4010f116000c1c800e00d0781d00d19140a4804c01e41c12170303104a2070280d20603081a62000080d141c0e00c11b42e0840300c0c026400040c003200321707800348040b1444200d180e0714002045510340b00c9070740c0700e001c41e51041d070f69001102a40001174600744a40000383ca801d80700c44038000308080340c81b401c1d1115074000c00d040040d81e4a80603035580340007090702d0b080503c550020449654468003144948102226071502c0c440e = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 427615485 1250 427614235 427614269
    0x30d09140f0312060108060a03060908030711150708150d0605061207030c3606080c03010b01020303040618080a050913090f02102001060e010602010c09120507 70
    0x4824500c03540e060000c00c0030380c0c04050080410544074051616507414841e07074440018650b600c0740380c0003680844010001c03481c0640703d4030f070f802c210b55104000b100d402c1c400105010400c0d4100161440b0301c00007070020032500d10550f001a90401c80030740070701c0622045074040340000b50047c1141c0c0c003403000a0400c000910f142d0a01c08040d1000351401c0d4050a43e80e0851038003403101040c90f000b502e0308601540e0085180c4181c400300180351078100c840380418440c03040b01d81190042400c02c075480703c01000c030304141011401e50400784d8074400c4901c00e80c0340100c441d480340d80200c20f40e40e101d074001382c001800c4103009500b2100c12440410003019007200084a800040e044005801407000070754034009181690500c25089521000000c0d10314410146080f006203841403d940c03002c14980b804040042841011040041d02d49040344645d9440385024020602860320407401440da6200074080760002c0304000c1c01800c2140a2902c101c41c1d4038042c501404010060304000300441c9800f0340313070a2 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 427616735 1250 427615485 427615493
    0x80c070f20061611150703081b07120e030708191e050a11090705030c090d0b0709031a070c03050a021c030e01140f07030c0c0b010b030f09061302060309030d09 70
    0x103e444111075160a00400c2c282a04010200700104180380c902e0a29140407920305680381c40e0000c00700b4645102c40300301c005001238017802602d0100e01c0b41038882c01001c48105c000d4403801402a145000741d20018041050000c005854181000d801828105a1134641000300b50744e0b40b40300a00d20b00300d64040c1c401003003110001d001090b483c0070b180b0300c4107500c0b059010407100c04015101080015414804280c1ca141040000c02c00b10800500303045072482160744051020b40304a60400100b0039801d400c005101c402d48048113010075082d801519443c04100290581101034030140c01c110b4045103400075203008211011144e10400d09064584000e4038006018180305403d10805500386081140f08000220b9180d001e200424424195640e80100440082008070000700c2000340880060010610030007010340039000d0403407101e03528138200604c02c0b0406009482129136903c480b007040441804100486c084581c1203412507901c2d15421810f0f4a1400ba505042055600c0d00365980200 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 427617985 1250 427616735 427616767
    0x207030204020a050a08011d0609060f040603210c0f0f03121503020f0103140a020c0111031602070503070b0703051e0d060e06040908070210020703120906080c070f2006 74
    0x24803100d0391b5071000d036a00c4000075041c059412901c00703806414903008c502d01c0d1900600c1183d1004010706600484022040064150b900a0740309841152800e00080c01100c012803d105403100d550605207079040041d0b480482c0d0901325034014121035030b15250081018410340e0180c04140203040d05010001402687c4c011040039407004030b11614448000b401154064003401d085503034810241c020940d600100b407000782d0700101460070995030711145080d50080b03602c0511300038030071710300c00c140d4148001030003070303d400204e40042d44280d1200200308002c0003a14120303810143d0505d030139610703592240e13900c5000c6046c14501c100c42d0000803400a00300120b90b4060304c03c48415411446054035000180804c890b04103030050302181c07040101c2c40241c14508014100311010344100c90321182d40380c9484480c070044401510000d80900410018140d10030300a070340200921000310b02d040382599900e0903001c0c0004004101e100190a001040c1905400e42c6517000700161155a0303404920040201c5 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 427619235 1250 427617985 427617997
    0x504051e040e0607081e0c03070e1302070605061503010b160203031204032d0c03031e050f04050d030612020108091501080f194b060c0e010f0f0207030204020a05 71
    0x90300710a05c2031b0b5a07284c03080c500d01c0d03802410f8203542c03103185032900c92044400407490700e0f0183e00700c0041e05031020030030351520040640b51300034030f03001440f41040e000f0403080f501034030503001c48220203100502540011400319041d404000c1c143c0400c9008070320100c2d095009141221003414036603030802050503004004040341c00341d4001480c8407000c801a00400c1080030101c4100000c41480580340024000c0d80006140c0c0303c5400d907a640443e100c88010309403001164500c840040e01414442085400c101400c4500a1800c09228090401005440003041124003904010010340442c040340000d0101080ea01c039101101e41656844281441da607142039101c50b00540f0a182926451f0841036415134600d9030710842110031914510415904018058000303045e5081c080031980080004a414a44080040c010031441d41e001c5d051a8080f034507d4941102844a544030041184ea400040300c0d105940604184101c1000454202e152500b15080207410500c000740b10ba41c141e400c070b405030030 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 427620485 1250 427619235 427619251
    0x3070806241905100e04020a03050405010b0102070608061309052d071d0c07060525030b0307120c1203030b010806040209010c0212030f031906080304081b2e0206070504051e040e060708 81
    0x307140c3b07044004a80c0c03100540303d40c10000c0c0313440b00030490900d8241e1800301c2558420f90045405080e68a4160070300c1c952508844184004817680d10f00303c40c101e161745130071540010140800320729040c0c01d90340150116030b413820441100000203d100407690240d840054014508000e01e1811401e010303501c07504071002c0c0c40924070b14810303414507501ca03002d048000c5001401810445140588600c844580024110b409003d00d48000c202403192089400003240607903400710b81c0300d41d94400500b400f074015010a000d140100241d00c44e40e41c122002c49801e6034162281c641040c60410010b0039400340305c50f81c04680c8070000c10300c010410200d40715602d0300540e030802c200a580e07031f0500b03039680d120703502c615a1340f6044154150b8440d007031610f1414114602034205075a0400b422420858250011905100c4460941c0044180e59042186540c012100c0c245a80341608000002e41c04600c0030145100c54501c1301c405d010942c840d0f400a0b50310400040407255a400c01442c00b40c095801118405 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 427621735 1250 427620485 427620491
    0x6021c05010906081009060b310b0609010c1403070807020f0108090604110a030210030203040302010606030b13020f04030c080303011401080c07030e03070806241905100e04020a0305040501 83
    0x410a5012071058008940300130b001032512089208010f009443e81040c1624010713a51710703d1211341e0300d40450301031035109540b06040d01a5005161030525000354903080c1c03092464056600d40036205c01044900084003400c1510360b1300380b1803504c40030103200512400403500012844030304000981780942041c1d40b08403100d80003865050b0044500040490304e0310380315031015011a0200381304d4141d003030507111701400c41103080f5220713004170b03c0405000d40f650001a600104010626a0a01c07980001e000146400e02140515000007002507141d0364505880640c005105051340c4c011000700c4004607402680003101c540e543c5042516900248217000b003404030032800c81c3d1258070071801c05101d101904032460603c001178a013258a210b0012100344c240c400c0d807102003014441082b0442c407a600c461241080e06040408001850300e1503c001c03030154800640c07900c2c2e10701c54040c0c0c075400d503901695151640c01d40c01404075184c00741c2102c0135421a20000760195011b909d6000148158002c200038 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 427622985 1250 427621735 427621739
    0x806220204080f280809100e130903090b0d0f0614010210060b031605071401020405011d03030d0510030c0806070e0d0215030c0d06090603260f0f040306021c0501 71
    0x10a03180c0402c2e06500145000d0319080d000e60642d030481110b115401707284518109108403001c1401804081d13401804900d810000315000c1c5441c150905180200c1941070145842c82d6030054032501d054001c2c41680030001c41c46506090301940844000310038031405019580d03541c5013084180c110016020b0043c0944403030941c0102941c040c0600b10b80a070840c1901e1a90b89000c412050b0030819018810040b0422205012a034126503207010748024000059403149040001f50054a450944024003845440720000c0d65401205072181c0401e41c0001280b56522840f02000303141c19900024151806600085188030b0300281c12072141450303480300a81c00015500b0040b80d200100d4000303500000040c0d184202404c03100146401810341201c0c45d003403c500c2202141940c001d500f185075070540c0c54004001381312541502a203894603445034500110101e42060324984102102e6200901000030303140342c02d80c221001c8070300540d003022003151248003110300d2440c80f441603039074414014100000 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 427624235 1250 427622985 427623013
    0x12010c0e0103020f0909010f0f271104051009080f010b01021009030207030b0703050106030b092205101107050c010302121f030c080115063002070f0f03020607030219080622020408 79
    0x1824545202c0c8080d24442008500c03140006e0070314524200003034003060200240f16280c42001c41c890b3b26450700d03451851401e04030b5003860200c0d000c44559180c2c1c1440a001c07007c0e40c0100c0d41c41c020443c04e40d004030f809005410b05a00c0c082c083e6100a08806008040207812a855402503050310900e98003400484048010004e03442d00560f40300c440769501c0b5145241043d80c0341e041e8828144a24142c4003104020780000044450500c0c4400c80340c030b400100641004414000c1403001002400d085041c83e900090b40c0c44041000bd044158000900c6060704003120b40300c403050010b56000c00a0880c5a072654007603400307080c0301c1c2e40840d511079044030041590390007542c41d104603c00201c43e460380111041c503160049143c9500c0f0002d0750394204600f40105402e403290807542c600403102c12500068074a0000d29243c001014501018414000f074109004d040507002c20003426454068a145c503207100143c0c072903a4100140c0c403280342e800902da4001020307401500888000d10155800c98035503005d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 427625485 1250 427624235 427624259
    0x308100506030a050709050901080313090504080316030e120a03053304090c0605030402100306030b160e0a031b090626070801060f0512010c0e0103020f0909010f0f 72
    0x1820791154003440040d20035012903124540c081007924052249540d10b001091501d5000c3c6c0107000f04da000000d03001d0075515001c65001c001c2c140840d041006140c01e40340c0c030480e8000501240d042d1580c1c4520703200018440e402200a040d0524152440303c0d05841e80b001665102800c50342c042403c2100044041b4400101e4440441306100411100c5004400d03508260502c0303002507a016603541490380c007240a04107000081d0070261145a601d06140c0104014500300d940308004141c00d1603007d20000d49124241d503008607070203002e6420070180c03000a5550544003801d035508031a0001d800014401d01c040c451111000e400d820000c8141c07244403c0741594218080d600e442c00c040c03074900c81c110b80980d0311034860080200039106c071141c440e05040d007903503002d0340005460300b2007840510031450198000e4210055080c02042102d1091030040c1401d100710b040c0364141036020504a10702d0b0510300c00c070360419500501011072580c40b04024160511075000722040104038010209040c40c1d044 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 427626735 1250 427625485 427625489
    0x30f010e070507051213120602030702011b090501050703200106030624120206160308061f1b0c051c1106031014030312250e0f0f031203040f030810 65
    0x5d0080c101e07880150040d9603000100d03041c20340210400010b05500744044400c0914410640940e0704d0424020007800d446020801600207906401e070003d5603904004540e003242c00a0074000d0b150261403c00f603802104651020380c1c0032400810402c412a03041d88000150307482100108001503e1500c0c1c0790902da2140320306042c005030b00030248501217000d00116200d9200400a520b04a015110740086142c40441180440c00d4201400260315080c01480070441640d19120144414143d00401d21418000c0401200480c0e40100050240d40380c010130182c480a01503401d1800006240c2140002c813800030344404c03028041008180c50041c0843e4040d80c1c845110a446030700341801c03a00c1c8001002c02c16036143c0300402c40718501e80c100341e101d588203a00324440c21910b030b01c680d00300c6051b80680b429008104588208080780a548014038000e54650680e039030b090383d404110110b442e012051a0b4408906404001c12040105040c00d20701e445200e40c0d9500c41944600002c0d80c9016094 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 427627985 1250 427626735 427626743
    0x2010f02031e0a090615030c0b090105070311011518060b04050a17010b0310050708100e010b160b010f03020a1a0403082a060901200d110c03030f010e070507 69
    0x6000c1c1d82c8140c1181240e695040741c0c680c000080c1014076503403800200c80490302c0f03d401450f20400200203104041001100916a6507456441e0151180c002000381c030920364020280940310a003207c201c04254051680018413520b40d800980d10f803a01942004000d000c1e0b109454102903011640c41c000030160303412540e0240c05900140d040c80400b15500110032030f040050f40d0f0f1250805c1e03041da0200a102c0b9420003030400040c0324101908001d00d41c0d000105407a17040e80440500b046600c194682032811107134200c00c11a118a5010700050701d41c0c10f06e50000e0014103281c000845d5215040e08850300b227034130803200c2103000740e5511443d5420006050b0000070008040c081000890700b070700011b00c51249010050000c440d03c4c00419900c102e41c686031403540b64030100810116100c24818440c895040c1000c404145a02e261100010f1003183e80d1207038003a4540407990340c1d01c08030000ba1406002100150380e01c0b0b01d0450301e04484818240300d06280d401e1603002140900f8001c0b0b003260b00c0b180d00 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 427629235 1250 427627985 427628011
    0x10507020d08030606070b130c12031d01050405130b091e01030305030a0603060f0e010c030b150901090e15040c03020403050a11060c010207030809011a01050331110102010f0203 78
    0x140b91500c04154000400300c40e0040d03410082e100001c0e41031801c941c803803619104d42c60100c40503424401c42c0301780380e138102c11001c10100c59a04c01080e0000b0300b902c100c4810b011100301c03c400007030040b20b00c0d0280303074849030b0422401d0640c500c01e4181c5400003065444281c40d1180d1580d6004184043c1825118000e00900c282d60014404a07214000a583c0711144010126005549039207150488040400140d800d55480014040c02c8c1828040e2040c000c0040c45c043c04551020000203046140045d10218004000608001c0036405103140304020114501886070341d1802c40f90310007100030500c980501c0307145070144c500d210702c1c081e1007500c0c29250058003e0108009c0e6070f0381d00104111680c0030035848102030000511000c0d09000801c1414842d640d40c04090034503141090a660004008003100e15080c0d84619071039030b100302680e030701408288100d4003d0b00b4110843c90301c841036041e40700c07160010480c2607060042415040c1c000342e80a0740204034000509400004900058500c140d02d031403 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 427630485 1250 427629235 427629259
    0x906030a0b0319060e01050c0405130f0b040608160b0703090e06040e07090b0f0a03121805100905091f05120c030d03091a0103110105210403180501050702 68
    0x12240c0c054a407a000c00b9046520010751604090b46000800701c04684e01911200300c0c2407401003e015045e0400300b20000d040c00c05007014000340340c42c03504150300c640d69659190440d144031082e40103c01e40c031201620401c99642c9070701d403668403010a0f0544483c4800d04038000a0182e507420200d0301400d40543e50301c0e00e85800c020b032001700c9078400341c40c0c0f42d4803e8a405100b40385030001d003c0c1c0740042400e4031001a00039000002d026103c400c1125251180d040c0316800c01c085650203101c00f00b14030023407821489234544d44980d0001c904864104079049424080c0c880d05040e040b210160a40d01b04851a801c2a07482242e400350300801086c0355004614180f1301040541006c0c88070300b5508104805445c02074100101203440c010640c804000080c0d1546002414400020320110601c030031404072224960454580c90503000c4c40c46e00c1141000800114400d808055503611004400e8855600c50581000e041c010159407048541110503c1500b40008444d0f0040e0212040268060b0807015808 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 427631735 1250 427630485 427630501
    0x215130603110c0f03090103060f030503030606070804031b061b0201140c030c03030a020301030317010e070c08070b04060905071d0115170408190e0108040f021c0606030506070203090603 82
    0x1120038400540180701c28001c2420302c00c0c00b44820b840201643d8001c40c0c0f01c0c106c0d41d00040c140c81c0b035540081da11202c01001400441d05c04421254007203800d036500b40e170340d244615003030761940303d180d00187c10480e640c0000d401c05a8254800000c40c1c400795141ca00c84a210b145294000031121030082c00314800c51000c6810780c2c4030001420580c46480240e03410040440301302d0f819548200c403104145a800401401010703000b100400f803980c00200d04012640c140740408400b00c2004d0700040900c40b211032040e040040000880f5082035115907074a509051502d001c40141220001c1150350b406400342c00b00781d21541201031226010020b0104c1d402d6464806082c42c4030629000110820103050320b082c0c424180c2e0703400c00c0d008511880045a44003503154801d0003030749002803918104118400b0000b01030f81d20004064001303810243d142d42c000c040744001495242c04071002c034000c8108070100d0062001650113082200d000d01d082d00c07205e544800007240c0368072946030340d0307075000e441440410000 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 427632985 1250 427631735 427631741
    0x7021e0703021905060313231e070602070e0603010f02040303030b091605040e0915070824210709050a060f0b040b0f180a0b07061d0c0d0606090e03070215130603 71
    0x204d4050b03036441c07601103403e007040c5001c903568030794441255000e5082c0c0d04840d250300302950271101c0101c014200f2942030410017503c0716518400d100740a444180401c0b5146c0d000c0d8803d991a0130018030440d41c0f01c2e074034600900603000a00380a440344150400081d07040c04044121751400810355180d0340340c6418a10103200161020780303400100c0c41100520018100d1044c1b5603400342c801303030300e5010091801d09001090418400403075038075140e007035070550b0054803940380852000612a800e10707401c4181d042007078648805d50f0700001b5150304100a215a00e0840c0e445402075038800d0048009080d118101c4020b248114451080100004c00170056034288a0000d031804600d14081d00004170b148100003910010b5a401240e1182c0f4002400010040305100c1c507041244000b68295001280c00c5001341c4521240d001d40d4003070001d9650100c00c00c01154070900c0902280700c0c00304810501c201d21070b60b407604000d408a008010000c400a03188000300700360341c80d800180044050031400d0070400c9022b = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 427634235 1250 427632985 427633021
    0x11031b010e0c0627090f0906070203070b0c0a03020c060703021b0309060403060b0a08060106031a0d050a14011d0102070311120f18131406011701030b07021e07030219050603 76
    0x40c03e2191300d100c240da400d010280661590413411205050041c1001d0420102402d180290b510800401001521660032a50702c64905600e43d91075000044041c0d01074480c1d0140300105014000c01c101e01d20350158040c0c420600b201d44e4903800c3e506030001d010f503070340301c0d4104441d070201051204000240440c1c00400c40c9250290144072441d41d281552807030715200b13811002c04a501c80240424044410710701d290702481c100c4120600e0320041d11459164840400007920140e1094080d041844094010350742e40c81d02c10012451345400c02140e68000c1d004000c0c2140084d001184401c45040006141c00241c40380c071540301d10340303a60f08420201b664880d0300603140c03010503643d8060050ba96181c0c0075100c0041d010022800d202400c894a24a01001340101d050181c1c0d1a5185907103107003403181c170b4150385c0d111a101c80b21761518081030380340c080d2243c03240d03000d800e84071440d410451001c220131084900c29940100b01e100d8403015031000300100d010b401d822090070f20001e03108103224442c01d48 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 427635485 1250 427634235 427634287
    0x20a080a1d03180f0607030f0c05070807140909060108120a121e0e0d020a1b05030d0f03050f060d02130b04020c01060302120105040507051011031b010e0c06 69
    0x70001d001d000806080d60031040c0070b8014003550049100315824400e00348002064121a00d40c42c1012680d006407480c804d41c000042000b0444440c50100001046410040d0400e08119007030381d40d0b01e0f540400c01c45200d0030018040d10405001c1030036003400140e464141c400c140003500c42000440d9601000b60080040002008017840c1da12060b6510351280300c5859000e0581c0780d0320045400251020303592410107126036036110300700481d4429400300c5c1d803101d01c1e540440310040d11040191000c41c0c6003019040300b503060040000e608840c6410854030f85840f001904c0501550382c51904040182004684103500506000c1c10780005103041c2003680842e4409260000303d507160314001c5030484e0041d0310b07030924580d90303040e0a10541c50070034400000100c40e400203000e186483c4d0741c1e02c0d49505561040074052364803c265001940c2c0280129094441602c048130f85841d02441d4280e081811507901e55155480c0218602282801080000700307490041c0c0391501c0c00480e80524036a5182c02000b20b2 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 427636735 1250 427635485 427635521
    0x190308010e0c0d0614030d021606121d0606010f14030c1c0f02040f08120d020c1009030e04060e0f22020303131a16020108070309050f150604020a080a 66
    0x2000d160300340f00e0440901017811000c42d41d40310381c105141c5003003080c501c1c3c1810740d4071240c038603625407a0540321882598940c2c0390100031003c2403e281d5019198005000b030081c00400721001d80780c0c50024007503209c6c0701d00360b84880040403c0c042c00c4d034002c050702d403054906100c100002008011090014a090010416859608a01c0000500803190404c4c00707403440b15000030f01002100800e1103c440600344003805171000e4011548061070f203118020300c06030700d5500072a88020b800814018a440074010b41824082000303030f4507000f800100d107255150320940c60310360089401e01d04420510720916000d800d43c103041e1210405940c46402d008110305d41c451300000b600005031802d00c050094844c10b045030094081c18201c13645240c14982010b619049000e01820302c9100e554010911050b40a080c003081c01e46480a00b01d000d084010805400b82c0b00d48001c0018902c00010f141c3c6002e03c0455103a07200d500c0701410403051b4400d007080800020411008685401582e5010340450015207030f00c1 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 427637985 1250 427636735 427636747
    0x6050a0c02120a0c08070e13060e0a0311060705030c030f040512070c030b07030c050712020c1c02040e0f0c040b06071202070f0503070b0a030513020402040f0602190308010e0c 77
    0x1002d50000c0d10200c28603030000d0080c401081010320182c0701806030708002e00541820942d0f554084940100850151804c0440007010311407568041c02080c400c0d5003d40305d07026004d0802034641d8460b0780514005104100004985d5480740302981d000e121804455459a10b8540c045440c002c070284c0f0580c0c981c01503aa50703809035941e01d4000c140d960711487c0780d80440c91030340c105a101c0381e5000701800241418040907003a4030340e0080c00c035000960701101c0b40142c19009003003285005410241c0e00e402098911040f605028200031040304513108a4040c801a83c2030941d00303072280010700740740c44282d10840c000e00711840d15402c114503003100a8940340c20302030a91a80b07441d8140d1086c0880158101c1502403005c428041c04083c054041038000303020280c681020003a031442520000300406941d000480c41481c0d43e9840455480d40042082d5115500c2e4008100400490721039000903115200c620980440404031007080c0e55015102c1001e1070b071030003400e11488900145050143c900401032 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 427639235 1250 427637985 427637989
    0x4020411160309051008041704050a030804080f010908040909080909040b01030317040b07030b0f1f0329060c030d1401060f1805040b0f0d0b0403140f0406050a0c02 72
    0xd011010304070001d0103026191800c2c050007a401a401280c001d1000d0484407a680c1d8219105030b4019a105418000b0030341d05401500f6203010f00c1e0040c56001030340c104000288040d550150040d038040c28182c0b0812321030a16114200e503003080005006c0c0c4402c0c0010072020003a9804058010b000b02041803800c80c0d41e00002d03441d4042150700700c4030110103800500a042d40210819043c030941d054101190a141d11042c1d55243d0080580c810580c80d00880381c0145c42c3d1780490706284030050010640e051282ca9840e0415040405510020345407101e00d4110004802c404108a01d1100d035180d400218403007403280300d9104000104003440100003400d61000316214812003031045103400c00455041500c02801e0081c6160001c0401070406401506424074681c2d4104450080750001081483c03480460b030308100f407100c0d05a0001c40524000140464520014070540c82680c4190b500c8420000c1040603005250103c150348105010a01a09000324001d00095603c0c0c1800741ca001e400d640 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 427640485 1250 427639235 427639237
    0x90d05070f1e06020c09040c03120309050d0914040905030f0d06090f0c050909060a08010e030c0c010306120303050712061221021518151f060804080304020411 70
    0x4411100704507112800c101c1000c01a40305840401c008020302122450288000d644213140701d2800d10402844001c1130030441014550401103030302c0100441d001e15200405802801d044006595501961a03c1d00c801d44c45040c54074140c45807480421655141c1c2c40a0000070483d2080446041c0310401110b10b80761074000103000840b0007440c022410314140a00c0750250b0b19403c4040880a0070134248a06154010381603400c911000d8880c10f4175941c407040050708001d51a07104009a518000343c4401c1e618010005190600c060000c84080c2d9007084011022130346e0700c0c818001000610400000003c0c0b007074101039000409851b101c120310b40c0c880c0c54001252625400046681d00700a5800c040000c4501107903241c100014804000d600c0300e0202940710484058515a10124503002540c250165040c2e040948001021070b600852190032040b50a41c0a8603042442c02054552000c448411a11101500d800c1d9a800c2120303112075543e2020382d0400340c403c0f0b0340b254031508001e0010040714 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 427641735 1250 427640485 427640489
    0x1205010621050c09040209060d02040908030c18030d020a080a05040807060e01020d1e0f050c03040e010305071a16020102150403091e031101080c21011d060f06090d0507 74
    0x5400301c04440440d103402807030410383c424100c0c050f80035101000003503035454600d990300c401c0941e81040300009a02c005402080c0341403000300707180c07008018400c00f10f070640040d2403026851034072841c07103810789410503546401c0e90340100b006912000c460307000520100064102003416082150400d80c680c01017030b04041d52504000002068158905030350760341000480b012446c1401c05004000c0329140040b20318010005400c241700003980d184084501c24421941c203035440d07105883d2500c1e140c060740409104288030035070b40c0e881051000b01e850b000d014050b00d46080b001942d1403070180414a1380b040526031503030990540c001c100403095a01800390456206a210365100703c200c42c1490f0031561942d07082e00401c222140302d01e000744001024040c1c0709501c801c090800d4101a80d40d6407402100b48a501c106211103c0b03085800d9221408048444e81a9814054445070302541140319140011046440d6039000740859004a010f0424000404a1000c0640414004440c64a449140800903 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 427642985 1250 427641735 427641779
    0xb0409021c0207030c1b09090b04020a0b0c10050c040e0702010c09120c0b1605030c0309090606091e010306080f060406060b03070f03022107030e06011a0412050106 72
    0x5922514032040c2000101c80c0703151040218104442510700504d80e480711940182140c0180c84032030604111400c0d001c00501400b0000c0c0000c1d0f425251001d011101a502280180300001300443d140030b482042d100d603038511500400c403024650038010702524001e040e00035446010440405d9101004184d944074035006c0d00003042080c2d110300b00406c0741c4140d42c04900d4040015082c4400604120b0107401100e1001105688580720000401d5558000e810020003901c8000398101c015170000c4040c2c45d201808035181140f81da10031092010503c80c0e0740d9090f511001c00c5c50384100099106143c6542d010040c540060401e4071002c040c4c0c501403600b04031214681c059405c1104201050185802420350300b1541425800c0c100000f600c000700c1c40f24440107068021031b49540103980010340f80c0641c0a100500c0c1200d00340700c1000340c020100000d1101417801001700104120290f07143c8010000082d400310351030b00b840c01c02d02300c80546c1d03c000c00300d038070b9503c404001548002c3c10180f40303000c00071 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 427644235 1250 427642985 427642987
    0x6020a0b0c070224160302161509140f0a06020d02280308070e0910050f0402040b0f0d2703080604060503030409021b01060e1f050d06020a02100609150b040b0a0e0a0b040902 76
    0x82d0800d48c00382280540c0c0079800c0207944003803c02c012030380043c070907040311a1921000031420000b00020711141c08480101c0e0003915540d00007034031a600003041495003506409070b4040c0d00f00714028040c442d080468006080c03074076402420000340f00d0361840364040c0700b42c80c0800c400040a40010081103043c2e804683d2a520803000f8451b03450000c074540813509044404520306883c0c44007240c0da0b07000b4800c00415920012440540c1c0040c0f070380262581d811455095042400c1c2200303150364a000103001070f80000c011100040090800d0711a0005550006000754141403030000e588000c0d51003030008409551400300c010508540901981d4080c059903610000300b0b1426080040000b4107000c03940d42600304c804410400c0e5141c50405958050b0412000760f6511401e0f9810fa01d00095a0f0030400424a01080064103e103d940024240800340d120001c150341d444072030050600980c001c0101041040190800c2c1c1806410003a06400001e41100403030745d660034040d11980c100e40d018000702a0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 427645485 1250 427644235 427644253
    0x181514151f0c0624091a0904030c1b090e011404110a0803040b040e091c0e01050403150510091a0f19030303020919081f020d020406020a0b0c070224160302 68
    0x1c070f010104806480ea05e20100300640f004601030b9606056244040d002e030300d800d4041400d2501c10229421030640023a0040c1e000817243e08000d038a181c051046c104a0391a2031080d160044040c050381d01d0542684c03c15110b9a00c4603142c09075205001180141d00008851001034a0320003800500020030454140707980b01c030320b0140c2004004000074425141d980084040400c10441042603600004081c5451182c4081c01001601d881c41075030000b900f2640114480303112030b01d06401061003800c810b581a020395541d0130842003524429404c041c0105589281c40c001f03420281d0303080e0b850f1640203121004210390142940210344c119041a80000e800150307001190420b020b101c0558a8408902d200c41c80c40d044905407119942c0c48a60034444510200e00003200040d0141c170070814021504542d82c0f651004065074a82c88a1301c00c0381d1900e0210300003008079140c0c0d0309031620590081c02c40c0d94081d82d151505503000650311018a2180801e200148002408480b25130040f0b100781c0007012510 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 427646735 1250 427645485 427645541
    0x60e1002060403031d1f0c08060d06051302041b020d0201020a021e07090926070b01050402071104061217040605030712020720120c0f04181514151f0c06 67
    0x600300c071001d5001c0c40140001c0c82000c0c1c030344cac065041d903a5421840001e117a85514108007800a0683d0029600608240c0074074004010141911081040d0f42c0844070415030058041c1c0c00d030b003c1c0c0d0180c80301607006000d00104403250b004011040405410a0718611512490030b2030461300702c0300041c0c940105c100e01035020f00484205203000701901c110307124207240c003503035035492a0401401761602a40e00454640c0c00c0207009020041d103410010014005140c45285581e10480050011384810b4003500341400e84944810469068032030698a461071592000410b451458a00854a048136420424070000c80c03d1400300e021415610000a072050104904001f404014029038080340c0d00410107111180d0780316401185400e10988001c540040029130701e40d07031402e9801380608010380c00900e1504114456200c0345103942222348107a1151101c00506400200540049030000320613841c56074203140001c400410300b09945001021804195916000e45461440d00c1007865804001d4400038 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 427647985 1250 427646735 427646741
    0x60c15010512070e010302061b060f0603010f0219080621030a090501030203070c1103100f05060102060f0106091e0b0706090308090a02012f1204060e1002060403031d1f 74
    0x240110b4000c041550401e0000c0c0c40248061200070f1264100013403451008604052840c8400420340503507403603262800303820002e10803c0350554800d501c4c0500f050090030b214401c0c0c1c0d00480c0c4d0494071068071000500259400780e8080d001c6603005078a0313103006000c83c031800c0c1140790000715007024541318800400302030320071920354120905040c014800c02c980954049100b60685070000310055000c441c1e900401d0919804001103a407990a110200d40c0c460400c1d044280a03400030ba00303e404941e42c8100350461020203000f02000545100c400304440810320001d040040608503411003581d81c3d5030a0098194000700044072502d481d20380090a150300080380c1580007040c034010b481c0324a09540002c00349402c0c1c0d541ca00c810507200c4a40491181000c10f06800d00741d0b000e04660442400e08450b00321174100b40f196a000441029582904d030821507040b0030341d504170740c00512040d1075a544c142c01400300010b05489811891080e0418500108810000c400415020300c800300441c104103400c3d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 427649235 1250 427647985 427648009
    0x30a0c03020112091214040510050417070b07030e0f180901050c0313020d0c081207050c0406060f050307020124090f11041707030614010623090f060c150105 69
    0x30f46480e100903000821500382950400c8009860403401d044a49140341c0114010f640140fa080315409900c2280250040010000e454540448404960303120100307940d00c0c5014090b07009410000d00c107260000e07004044106403404003c0450100c100074401140b4011008e6081906810f50720050014001081c0314050f00440d9001101d869880e010182c5580500180d900900074a4905a07180c1403220307026004000c1d10002094840c0100001281e64503a04085025140e5000f00f006040103403516229071022500181c80c0c4440d811203103a0282c0e156000100a441555204c03101c980c040c4450303840400d031005845d01c10400323503801c19680ca400c5039200c50850301c4891078860031181c1e00c0b00f000242e8086030300c500c0c40400c0c443e800e40111800d0404a62005000b0b41c03c010764a00c042a40c840d4a9060302c180d41e0f1040f41101e0358503003100c0a80482041c9400d0440304003c890802d0034421003048100e40b000d0441c9190072003000c1c0030383c90058200c1095100e03100e444018041844c001e400019 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 427650485 1250 427649235 427649267
    0x207030906180302091b040308040816060309030e1e09040b1905130b04051504080702090a1404020906041d0d1e050a0807200d030c0c05030912010209030a0c030201 72
    0x464641141c4c049400e294014002d1114004c030f56980e101c04102e180c04580c0610b90122038075484550b03800c1c82c0da507203218014600341c20000e610340100d03040e031003445501c8416030076944070f8041041440030300608038102280900b100c003200355074038420346480b4040c60003140714194841592800507618090f0000c00c0d1300d02c0310390300e007000c00b40071100d890303c4e089441d11a00026480040e0f152898424070b00340c010703400e800c01040341a042206111a031405484d030103000762405903840d80e50910100c100c8240120400309042c09102260250921540c3c05511003c00740000401341c541062489000e084010404210742c4501003060440760702120700d919a00e4403d8915401510b00701025040d40100c1e44003c2c10015490005031030f2911810141072007211800d0000d00d6040d50000064954500345552800709050039075247c1a0341c0b080c648044031940041c00755080000110420446d1003041401016540d0284102e40c01355805000042d1090f215201911009286100140c001124a240c0358 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 427651735 1250 427650485 427650527
    0x203070810050402090609090709080a0b06011d1e0102010e012408060610050903011803030c0e01020d050d110403060e030a0e0409080d0902033d110702220207030906 73
    0x5c05622400c00740c85107018101c80f4548660365030b1104481c9010185e00c101010f208a00703100e000d00c200c141441f4000c55080c6e072003c0c0703035041d4800d14880350500398070141c0d00b140102c810311020741d01803071701011144014400801c203403110a035028203451590144a640042c0c00340e0320300385e007144801d80100801d03040000d4141e0707103070000c0046c10950388490b0890502c040001c180708542d07029440b5451032107455582c2940c15001d0300b0001c00400d5000030100110b80e160102180641c0000f501e050286050b0f541d503803600c1d070500c0039400944070f80002c0344285c180078080030001403150b0241d905000d400d0801140c8a5050500080049039000e5800d40190b1030012060b000c91482c404984000318000d0000c9004000f901c0070903c2c24040c000400c071102807807000c0810160b080c50740707250083c15405041d019540c030b0342c2010003100e0150076440c141032001c2082c0c000606210070410240c0e03014040043c281c9004422040580c1d002000490000c0c2004009000746070300304c0c403501c0b1164500301c490 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 427652985 1250 427651735 427651747
    0x150c081c0b120a020d051009082511010c1103030d090b0f01030206090907021509010b010201142a04092f090d060f02070c0305060601020c030d140318010203070810050402 75
    0x30b540b54846031034060b014460100c0000e041c040104146c00d05507482000800c00041e85050450090b04111076021a02c20700c01540c6000c804102d20142c0e040743c00c4014074013552003080040d905014181012920b0b100082203400c0603581c184081c00b1508a0b60b5004a55903003246000743d6043e0700204001500940700c801800561208000d0391460042522005503985071200c0036407518210b5103005141c0036002080180c0d0a070190840c140d4520281c009004064030b00a191710b001300704440703514044c143c0b5424a40050550114245000080503800d89800e89807080801510b6010021035541c003048401a200c40b2000f00180140c4d08407400d600e4200f030888800a0030b0402c00300d1010784100e843c0d801540c5007401c998121100698803200c910545a624600300c2d0704c038001203800314094000c0200302241d9042c041006804101650349819902201060261168102600c3c00540760155194144840f00c00d10003036000780381c60389403030b03040b490081703915800310f009a00881d0045005201c0303 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 427654235 1250 427652985 427653019
    0x2030a0f0e0109090914070801230403030e030a02032701052b0204080c03010e0f15150406180510060912062301060e030601030c150c081c0b 62
    0x4080c90380200d403501c01d41800418004962081554003c186481d1600403820104a42c4100d43c00d11004e0704c0054456642c3d9818116003201c0246d80f01440c4040c041c1002d4000b0408898132650161081c100040c540c640c00d400186075802481c2c00c8405a400010b10039400740d1000019804001c03600c04162109600400080403401030318516801c0c9046604a007405002250704402840040a070031911940d03200301c1c5031307a601010122075000e0351031b1086600c0d020ba00411660390b40d4500d8801031003400c0400140014440000b0121180c105012000b140950f0711030084400414242d11020050414101e42d0f00c111900900110300000400c00100490f641101d100c40c115a803401c034105262425041000103800950003252078090030b00c031103280280d805030059060740e440781d40b107820740400341003815a5210280409802010b030110104519142d40d03042c0c04400b0250310300300e081101c6664802603150003840c0711004a00340344a0342403c00030355200352807031803d04813030400644070f00b0b1403 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 427655485 1250 427654235 427654247
    0x60f06031f150504020a03021c06050d0219240f0f1e020a140106030c09021c020903011e0c0e0301020f0a051b12040914040c0603020d090b010308040509010602030a 72
    0x28070620040d40b9504081030b0400d0804010006050191003507644c0c00084100400a5020b045031802c010a000c0741c900c0134031081d101c2d681c00c0e03441c003070301d244a1210389801f040384082e00303030080e54000300009801044040d50030141011001590420b2800c0703e4400344042e10790140d280f80a41040034000329080901c0d4005210001003a5001c00c5001c01c1104030012070030f060744810007034030f40c10441022001d9210150b1009040300e0103001c403c0c01c01d6464400c414142d100707248003441c00350703514821500c0c0d0101d103500400104800400028150383c1c00c4010311036541170701d0b09417900306954501380c0b000c246e0007013840c0300030900417802145001100c1e2070181150280001d5081001340c04a400e880250710303c04100301e08402c0d0b60441e1040e00140014210b030350321a0082216440c10105903600c1d40004031000c5004070345c460b440144035810f00400301c00a4100d44a0901c0007074580401c4004180345c062100d000e0740c042d0101a96850810b0b040c005d038800184d00c0340046600420181e09070950102e = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 427656735 1250 427655485 427655533
    0x1303030518010201053903040b040b06030609030d0209010314190b0f030715091706150f010f0c021f0905030c010e0a12020a030b091b0406050307060809030c0f060f0603 74
    0x2802000441582c1b203000c4070104415404060b440c0c40041408140852500d005106610a000b51142c4c8d40c1c0e00d000740350b140c0c0c00035a09048164410300044201c000144c018180c0070006140c001040045616800205403050b80c0c180c103170341003288020304800e210b8040c21141c0349060307072a910440402800710781e440c42540301e110304a0201c001c8011845110300c181c070004000da0340e10100310604030007482d03490340c806035440405003c07009624640d509040b4210050010142c617400e600806200080c0c6803881c2a00c800c903130050200380181c4075040020f030118041710b441c0d940c0c04486402e0109241c60310381c92071041070621009040c001410341d40d0680d1030080c0d90310440e000405103501d01c0800d03c5205950401003c494103402013240842000030110002140803400b802c105064a05000407a200340c0a141d815402c20003080c80400d0046407503070f4200302188110791402c5c8851318030605002d08080000b60a802000500501c0c0380040241034010102310064051060440d407440e200302040 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 427657985 1250 427656735 427656781
    0x20a0e0102070f0e090712030512010f030b0403030b0a0305070603020918010305061b070b070c1a1009020c07080601030c062a120c0501060e0601110c09040f08130303051801020105 79
    0x1130000509220081c00b201004000f00c544040322103559107800b6003541c200c8000c2c10700040c03141000107882540d10b9452012039402401d1070495032516203049001e0000040c865800c0308a5850010004030100300103001401d03190390040c6c485482404100444e011101d0a000311903905006002080e4003040185d041910301c0406801d40e035440048000b07600505a010b070001001c5020000300c2c603000400f51041d01d00c0f4002c0d03408650080841100c1580c0d080c2c41031401909448000d00ca420306650060200381d041000f214510740c0e403095041e103014826082260741400210023000303031075040080790398030607081c4d400302e0b070040600010034150304400c0001900c010340007500700c031026012350552070085400c140203100c1c180c0c5a01040b4200c913419074515000070000030710003101d8200840c03d4414050010184a201d031070b96180d414092503052001c2d50a844108860313407540c07102c541c44200562103078980684412040346d02c0c0c000328204600c4076040d641014100110381c004012450914180 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 427659235 1250 427657985 427658009
    0x1403010f0b031f090c030c0305090717070e1006090b07050a060903050d180b06031b090a1401082a0609040905100905030d05010501110303070503190c03020a0e0102070f 74
    0x103040e00d9141a80165903210f01d1818040c0c0049114401c41c3c00c0042d4208250320300b17100410741008200c0c102c2d403048a0040941d002a40140844000e0150f40c0805000c8842260400c5848826100342c0c08000e540380141313208002002c218041d00806100003c0c031034560418201480c944a454880079104802040e40341c0d00c0d50380c07000f014000e905403550001c00d15070800110b040c070070041d040000c6440080c1c816a146100181140c070f00003d046844010b002020032402e0800802d228403c5000307401003540315290280310841c0000311010600138600070f402050a10020381d140c0210003441c0c200c0000d40003040044031080d0300d8400071103080c1c0d5021f681c001442401814103500b4081e4210788034001504002c20402408000000360400181c1d1460401150f41e07034038010341e8144108561414240c100303200080307145000b0340246502981b506644403004805038103042c08c071102490810042640400c1c100c00c800d61100760300a40701400c0c00200f210070704140740f0b00440d1525106a03c10429 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 427660485 1250 427659235 427659241
    0x6090304270c0c1b14060d0209181012171b010f0606140a08010312030905010c1101050a0b010815062101030b0f010302060f28020d1403010f0b03 64
    0x1c004201d80d5440510348030304110141da80c0c003008114244000c000d031040c40380d501c4c40a000c00005260352089072030106403c1a203800490510186da00081940a1103550a001d1070b0b806484842c0668044580ca4556024518180c2108101c0ba2180c0d00805400b1051a144900240c29042640850f59038404000e0b207400c180c1240c1c00304104006030103061542484071707100d02d210321a0040c0003a5400b68980c62001403070408041d0721401070030f1000340001d84103001000860704c9108002d00c02c02c0c0f0b41c507011485c9619078030b42c64290b40084c0000700c0000c080e0880e40c0e0800100780b0402e5000080d441061000350709100000b4803c0202400d001680b20001c0a0700c1d85980d107000840d800341d0961808107220255440c006e000481342407105941d01c004007400503540ca02041c01c468140c0340d000f483d240c1442c0040394801065007145c2c088100b0303c580c0149100c80340d000c20301c88020f1030000e5802402c0d4161401001049003813050420070040100f40014043c4031101030100040c0e074200305015449079 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 427661735 1250 427660485 427660529
    0x50913110d05070f1e0e030f01060609060e01110c15072f042a0513090b010905030a0f080706060308031503010609091a04030306150e04140c090907021f0b03070806090304 75
    0x203082c2200c41c0c8c2c06c0e41c0b034140002400c640250890080701e40c075884804444206000564003200c402c040e43c0026042150100303094906401e0500a410510014a0402c80c46541e07403942a203208000ca800512071020100c034032402e000c1c0106100c00f050b42c0600142c0d445081400000d10071011034120f0407122403000038124802e0090f00d0344150341c82c1c038440c1c005070743d50718220061901810150009080070030100d0b09050003d1100940c9600c0070720b480203900543c80762040c42d0400881190141c0c9c84080000110b095000a14000c140c4030280c4070b9a00350040400d82141d05550246804509246034a000b1030400c90790420f002d101c0c000c0002c1c0a54851804070000d2440750081e00951000c3c02c070103501254407203805103421500f03440411000303128404041c45e90304200c034a0306601a080000900a0612200342608104240102d54135209840c001c40d41111601034030942c1c683c0d44440d01c00b034070700d4104900d07801032591030054842800c6c0780e88803a03182d20440c060030013038600703c4507110052 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 427662985 1250 427661735 427661743
    0x309030212071115040b0f0d1404030215090d0e010804060b030d050a033603030f020d090605011d060621040803091c050913110d05070f1e0e03 63
    0x1c00820a6003654905036440c0103d0003400340b0200b03134000c540303a81482ea001c003031140c1180c0c00d4405038019281880444607110b45076034408000549403c1c0c99010169100d10048a60341c0158860380113400c0c00500742d900755141000042c441056640580c00710a2325079044050310240310402c1c40d0001c5180c0e220700340003016000c130381403098051040360a070010b5140c1c00005440b50145076030b014803001d5600500e031941501130501c540c1d0100346081040c1e18170180b03804c0d031440307052103818081841002e6030034010032a00401010620940c441900b9420000300384901d038003500a041e801711102d105403030b8190880744002e03c034600034400000c01c9800f1244a100000d07a4040b64510792025281034640148560426600c1c912148940c00100007007019401e002998540540e84041c02c2410680403c0714a0140e01c2e10502d01c0b5645409503a040d480d114000d09103020600c03008039242c00d03c2803008044098030720b40d010401000074507081050000c5096010021068a0400c4451450400103804c0c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 427664235 1250 427662985 427663003
    0x150f0e280b07050a0308100515091201111317120c0f0307080d06060f2f03180108100b0315040617060109150303120c020a080a030203090105070e03060703090302 71
    0x74501001c82c0b070380100500002c40e001142d1181d0340d140f0041d104c48039003101519550044540c032400c9142402d01601c01180509414840100090030300d031401520780b403c581414041981c00e1034000f440c0608920a100001c0003480c8000c0d05d403a4101041040c1e9480e0601c40010700d00c1410001041a20b06004201070b11407040c103442580d50342c40b024513040074254019240c014506090a40000f020b034041c02c107500b103640391078503580c4004911841101100d1060109445d01c16100c0c0c0180803540020006014600c4a035000214080e1001d400900b800d8801004405040ba4161062141d007500000fa25040060a00110058821240081c001d807185170071500d4180361090070140005000905c240c100c540b013960803c00c0c000c1d1058400c8030018213000c05000310394240c40013020307401c481d80400446140c91050b54110a0780d03645142c40307503100304c02200010340c0200a005100c1401e101f0190020241c0c203100c100c10301c00b81c01003074841300300410400500d942e54007107805040c0280580c245c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 427665485 1250 427664235 427664249
    0x305040e0c0c070e06041103010612091b06110f070f0909060f02030c091f0e06160c03030f020f06100b0304020d060618241a040e01150f0e28 62
    0x10b071076625403120103a04c032000c43d500791145050000301030300c8041c0f501c2264142c415542e5021a08940c032400000a40000ba8044901100c400f1401d5569195240050302800307482d42d55030709641c5e1540d08585400900109a01d1941144104006910245921b4000c9450030b10010401e0281400c1c002c0082011600c01e8000354000020005401c002c030004080c03001c0f04880f80952490680f16030341507a0621411394001c1460318500038000d18010028000b10400000754440c071000030b64403259800c0e110381c400c5010130000c0180e01002501032104c1349050014400800081c03904011101d20070495220f00c8044110020101d019500d4080ca112041c07030304004241301e0b55680e8141e0184054110341610a01803030412a40140660480040c105241c20044045d2145c01c18900c110700000804101d07145090800c4005100100360b003800303000b000b224200d251051414072010303100780c038440c5c690020007012809440c11a40d1781540205c1d030004149190b11090f4070300740c0100742d2202c3d0350040e41c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 427666735 1250 427665485 427665493
    0xf0105090a140f0316033f06050307060201090b0114060d110c071e0503032113120c14030702010909020d0f0603060b010e0d0b01120f060f0b0f0d0305040e0c0c 70
    0x10703c100d401141e0300460780c0d00c29502d000407c032020300d1038901c4911610294880301c1440a1507030440206034001065804400000201c040e0340f04e00003481d1250652080c0c0140c3d45036241c4c5014080603a144500500319100d0440355909864009030306840307510840041c9c90b580c0c0c000080481c99280584402514510880722226240e10b42c5c44240004020402490b901c003c001003000c1c2400300c1614044018410701d420000790410240e038010000900313501121018094000c00f1868480702c40701e82c90000d0b00c031030815100d0b0741071441400180d0740c81d02040d64810080c400050340d0200f0b00000b00c4106d2030005841d000b06039610b0002c1c1c584e03010208015030401401100740a039a51007511204400d80721806440348410920801e80340030314002d440c1850140041003032050810540345034610030101c1c00c2a240380395a402c4200c0e54604100360741c00391344e1109040c1c6030038001c03142c40c405001111035208082007694010040d205600074403005a0a020115402e440d0203400e440b43c1c020700c0320640d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 427667985 1250 427666735 427666747
    0x4080312070e030f07090f020a08010b1b0a060e0601060509030a06050a060803070507090e0703020102031c0209040e0f060c03150d050705030a08030a061a070f1104020307030e0f0105090a140f03 85
    0x40390340c0c10345d602807410558500700303005181107403c0c030842d414618a42c80300d8085c2e038030300a40300600350048440003081c0b000e84000038504c000d0601584c001e0921902c40000c0d08201400d41c9441d004c0160804802e00c038042000414950f400684074022640c0030740b01152540e110b06000c4041c02140d80080924880130a150701040404201d00094505405041251800c05940300740e4446052001a0250b0010405215446203c000c40d200d10009190302602d4184104040340449050004580e041d801461072034040078002d00040d501700e041c05007120b046003083c200100003903640d0030509114411034000441006400d02080004060040a543d40687e0074144168168000c9034882589413510b140420402c401040c1c201c02c050340b07240c08030f08140300c84c2c0e1190910401424152423400480f42c5181c65607846000842c440c009507a804901d82030420092481c0044a920429031130f4141010010341100010b00c202416410007620070060290b512441d04128000110f0080c070b00002070710f = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 427669235 1250 427667985 427668013
    0x110315030c03061308070507051e040b0a060806041503020d05060105100906022e0e07050a05041e02091201050103061a0405040b010b030a0f0204030c1a04080312070e03 74
    0x10064100015400e840c00c1020540800d038689404031060040e40c10004143d03004240007101408038180f0a07800c40e4402a01d40b0001810a08500320300340c05d5845000c80910729007014015a508684280c4d050a003141c207000c80600b0003040109042d000303558560184070b01c80c03000d440c0396000f1a00a85a981600841c0c10070a450f20401d00500340900006103980d20000d11030121390341201c103217501404113200310501c40d4140c4030991105527659540c0d0b0246411500c1070348240443d0240e00da0044c14040d1030401401400e18096010300d00c254035205a40d07083e809626506d81d50b204050b4070042e43c40c1141000111802450f8204e003a20b5807a007000070081241541c041148038401202012241c0900000c10041d00c208a07801800c0c0c400c042c0041044042c007401564003e001140042208036a12080a08980165009440611341a042003140e150100a0752441e4a0449200d41c502800c06030f40c260784c1c1c46080c44034841000e00c0702c000340009104003a40643c90800409079141c8844410f0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 427670485 1250 427669235 427669261
    0x50609010320090109050406060e010b03070c03030621061a0a090209010203070c0b0903070e0606070605093a0203070b04080706060b04090209032505280f060e03030403030e0607061103 81
    0x307012220986010720100329401c141181c0be0489010304201c03480c50f507070f20368221407100c06917008605041e160107000c603202503030321540f251040383c540b41031241107030500f817500550710078031002c0e81c070314a001d0020312140e100c40303440d1420343d11140c0000d640e460181d40101d155208441c4054082c0307000780004581003114000030030b40040224101ca0720300d600c8086482c1e034540c0c20b848823503210030b00300441c000040580d00055072046610302a102ca014180382c090442c1500040c56542040424820310054010384012245603800c1e44003c0d41041c3c002d035925007803a00060000740601c1c0740801d0070030400030950091005400558500340d02d8555a10485000c0d40010302c07045d119026484c003000451a000e040701c60120484048041d000d4070300340900040d211941c500c190003003045034404014043c1c40c03102a0081c00030710160a8002d182c440300800003029401198401d4100300030400129500004451131000219507450b5282c0303485c80e0450003403914941032110124080100812a48510 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 427671735 1250 427670485 427670491
    0x4090507140406060e0910080d050c060c0301060203251a07020c0d050c06070206160318080a080307200604050d170f0c0a02070e0c0d0c020105060901032009010905 72
    0x40d40760721001900c041080103546507801075400041010111090350710304909245d810101c4044180141a112990035080c0446101603e012030400507007550400350402c01745500404142050f0b086506040c0c000351244101c0300800002d16064054840060300c0440100c000356208520752011042c0c1a0104500c1c54200c400e0005800340c10700c03440352820030000d1258020390040181c00400001c1c03040190130b810135401641c00040903c00104000d4142803443d209a020752281e00c00312800078a41c40da0109650061000394002e44103550000786140305032a00002c19052440b8a420442070301212003082d840c0012552013014107000c280300d000300b8107150000d5180d8074040403001c1c1c0c030886000710805030b85120400304408005120401080c0103009507200300c2c810b461405542d030503401d20194066038020380d00c501c0092510250611441007007100109400280014a012400214541741c1444094881c16048000c64080c2d515007999405003440140040055615641e403070005013000c03 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 427672985 1250 427671735 427671749
    0x60f27010806070807020613080a0225030506060616030c02010e03010f060512161406041509050f0111150a021e0c010612200607080a0c02010e0406211104090507 71
    0x911301180c5041c4c40403419511400c41208041c191030704668611002d54130040000c82103004140515a0000070981c500744007541d0000d8400b5150f041d81805410041c01600c3c1912410303040205040195100203411001901400e0075840348a0600050711a50407184031540e25510704000204510b125500800580c0c00076076410f102d588104101503564040c200c070048400c40381c03031020080d245440c1d84241241902510039400c09507251036000d0b032041282a0709010414003402440903043c4804503803154442440d1900c0c04950041b1101e44490000d0a62410051030400049071101c0301d0301103c4491071a0105040030404014000c1c80c2d54008a20801c1d0700e5080043c005001045900064941a0403080045038060401c900c80d2007406000030701c6400101c1403003600007040740400500003910294a400301003a856100051442410910b424410740ca8000300740081e00420418400001e01030ba429001c460a80c10010080b025003250f00e40d2160800d040b0400b00040411001c00700c40754 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 427674235 1250 427672985 427672997
    0x30904090f1b08073b04060b040213050906010309020603090c12070305030922020418050f070f0e1801031a072d0c0b010306060807060305060f2701080607 68
    0x1000c0c0300d030410211841107100c0c6034840c1c1001e011071408000030840b0500300c0407000550785c0c00030f650010b003281601c81c54101582440100000e010041c051001409011142140341001c0d543d0310440c000014080c0c41c3c065001040091866400303a44400035858005150680b41c1c604007a240d90b0311010922454000c64480c8010303c08002c0005520007a80c0e4894051800c00b00e02c001440390800b84081c0741c50031000e6030031035583d102d6524802400901010311009456000c0301c00000c00344c51b00540a8440903901d4401c001005074408075124000381c191600002c21030a410008900200d2070030703490b00c40007542d0000020040008136800c07c3d20303e00c6080300b90a03a80c045050b15040701b581c180f42c0c092008480c0f04240000100f8a8440d03c01c09424030034001c141e035850307003c040300b401d0300112400d0380d80e0708042c08805000c1103070f68001c020924080c8803d140c80004200c10104503c4094000c03403415904424400810b2240038a925202d03010301440d42c1d5880140350b441005030341c030030003040f4 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 427675485 1250 427674235 427674263
    0x3130f120f0810031202121215120c060f0919060305070203040e010605091201021801020c04110f07080910031b0804030f0c080c0f0a020405090c090406020c030904090f 74
    0xc014441244140107183c00a441d0601d1610344040001045080744218003520008031140903641024100310400703204050800d00c0c0080707403480c0320200b5980440c810540300000401d20080095100e402d1401540d2503611540003540c2440c49000d0480c1e841e9001030882d03039084000f45840300c0301c0100c1d0410398081c4400e80320040b050380c80780300f03c0c000c00c0480f80c5450010300c00a40108028400020042c00040070001c054400030708a810a2000407017000c01401c41c00501d6a04000498100004580410070780d0402d03004850030384100265400c41d59008108078007400142d1055942050015200002040d0f200300020b004043c0d02320030100d00051002e00c821034a20070109144140d616441e040c04404000c60107450304007107070340f08845000f4104012840100c0c00c1c00018046984040100b80c40113180c0704020035214000c00640140c0e1000719824070315138403407105a1300503411200040c0c2e6140d001901608502c01c42c609030742c000d0b04080607a4200010582181c4140b17015403000d03d2862 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 427676735 1250 427675485 427675487
    0x604050604020f0a2d030b030706090f14030c09070c03260604020d09050d0c0b010e07081308090301090305070212061519150819020406050f03130f120f 67
    0x4080c11514680c0c8003c00e0284e10034440c02010262540681c000c50002008001821401180340240000e00001d4903800b4450040c02d003004918040d16850500307002c098241030780c0c078941008038420041c201e03d034001d01a2450b181440f419999200c043c00740422840c14840240424403144804c40c00111465419540106e001842d201075104981068640d46c0314841000041c4d0420012800000d64600078000001d0303040001d4a111019501e500c42c100c00c640c00c0032560940161300c500c0c1070690040410802c00e03441641700b64014800d10040c280741e481820582c180d4020300c5080341e059071800303082d8000d25400101400b0558821a035120f50a512403d11549903407054528058201d07841e61110751074500384d000210a202003011201031950b964848501004402110f0300204014805003d401d0300f0445990510682410040d458030b45400d070024141e110301070061500c9a0f010020071800445480c0c004034045d08584c0d41d80080010707062000021a000b0b0341038001c9842d80351050089 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 427677985 1250 427676735 427676737
    0x6050405031207020c13020901030209190617090c2101050703021317100e010b040912030612050c01140f0d1d0c0901090b180f0403020d0806102102040e060405060402 73
    0x1780a00302d0108450b6503a000700c0a5000b101c0c886050640a00205203240c0310000e00c100c4a841140c15001e48619040e0058610b072481d61040c8180c8409a080000c03032440064400510b400075201035102c8c40610a2001e06280c1c081c00c0620359508041c14809280c0d410380140c4511500690030031a990b80e14a8154221142041802c000750010980e104003592540e01101d078880f84174002090a00c2d804002808039507400104448480f860385c01240c200e64917108442c0600110b0724001c100070826123501d6943d8580c2844a41046103500c410701d403691924041c0c4081803071070080c258449101040030b1001d4488005521900c1031000750740c0341c00000014500c0ba00090241000354142d0a0089a0340903001514103941c0014000e00580c4d0001d0700c1551035882900c142041e640c1a00f490b19000342041c1c41c0c03086e50410403140318144080c41d5503090043e00480600d0030701c000302c040c920740c1000042d149440e090348a01d2010600084c4e480d007400e5464440e03c0200c904010f507503215401c1000f2 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 427679235 1250 427677985 427678003
    0xc061207080a02041424130314010b0108040b0903072312040f09020c1203040803160203120601050a1103030c070b0f01031e0c030206040b0a0f0f0e0411070605040503120702 76
    0x20880417406580850b0404140e00390b82c0c03a01080380b004060030460005c1071150b000303580391501100074020030000e0103c411080c000741c400d808005c1c80000342a800080501d980900043d220242500114440341010070445102c00c1c4d000352807d00d1034420788880684002c140d41464040e000d150010030001030103800b15000c3c2e03482d41d22200b05550030182d0a1000707402002249019200d0744404604070003940010710f129501c106038181c3e880c6420240244100c8400340c5850555009021041c0c2e10400a007029601600038038155440d00e8800c24101d404802d0300d800c854007070100005102440e05001c008040a5010310300c0e01545031101c403641d0801e25030034071010f40601c51034014480c40c086455901074a85006100480106440e03400040c01e50340036a004104100c800200075910580143d03480c2881300c00c508058480050460002d40b07000b008201e582d20a42d6a100440c0c5000c84510a55480303d41080003000f2514040c90269503a900044184442a0380e01d00021412840020f010b59 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 427680485 1250 427679235 427679249
    0x20418120f05071a04030f0c020d02090c09040603050d030b030c0f10120507021f0b0f04050601020f030d0b3d0903120206041704120b06030c061207080a0204 69
    0x4289410900c120303246a5011214000c0040c00c010000c045603d190040300c81036504401c801d590704182c5800303405030a004007414144850800468090f03034441c2350f11110b0b585c0640e074404c0302c0e5072440840c02003032003120700407079005140c06d0000c818000c0c0003c81c4844141152000c100141c041410142d5504161410550002c0b801e1104005401d1a01e41444a4400390504080300c0a080c4d4051003075620441d0340310016400b469030b0300c00380c440410921112000c081e80404c030400c4414081800f5014191845004540742e80c080346c070a9200b00034020000c2c0c0c41030305503034940500b922030101500440b034003e40f140030303101080c19a01e06100300000010029000c1d440241c4042d03011282c1c024600d154520502003a0138002011550000b00006070020990290a00703141034a0a204c04002c03149a84030002020b000c144100c1d8099050640195040181412030740da503d00043e19210601280c82d82002c00400d031095203540c1000c01d24054242612040005d40e101ca42c1b034800c9002e1486080 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 427681735 1250 427680485 427680503
    0x5190b03100e0325030201050c030108211c0203240d1509150519050606040303030f0207080f13060e060306190302091e090d020330010e04020418 64
    0x140700720351022403242c00076001d490810020b0541100200d0342081c203004c6450011443c2d008050307083c4109680503c02c030a003541154100b11030255503a8079111102054415003d0b0303210043e4108064800010117102020005588460180041d4105990692240c0280d8003c1360645200c44c91240380650042c100c1c480b18401a02c035a820104140a01c070f2107141e42d844c0e060003061540142005503680c4120216843c149102005c1d00f03034001400b40c0b0901c515003806e00500c3e5850508071800c41c1e402d460045a10610145094000c1c41654002000e0b031000080c070003651405800a004001c02100001d07000941d83e81702035525020411085501c0322041001034001e2400030411705400142003070758900e0035101d07401328074504402c0d0380032815008a1925012001e01c8071020f03503440307c0d200d8050004521003110117548e0340240d40100c50b0029510b416038541e01c9d00e0081d4505842d0302174641d0344555950ba05040e50a1000343c3d8141d0145040c540f8000d00d030806448944070081e445210a = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 427682985 1250 427681735 427681753
    0xb01022b050f070605040605041b030b061002070b0301170708060c070609080c01110903190c0b09030a0f0c0609090b090c0a0e1f0207060906050301090b010314090105190b03 76
    0x4945940c41426110b000801c24800080400c40600c0707918031951044a00048130705241c20400000d03100d803007954600341e80440043c0000b41e808915690040d00544904044c824040400c1e82010f155130810340481c00040000103c005401020748250508182035032102340c1c480040540b110001c440000440c1010080ca00004078030382e0000700c5940c01000034904200010340c6aa0a556421820a81300c00000c5680b05040c074041c408c400b4001c003540340d005c0c2148075035543d1a50a0a0034030074a0620240490325641648060000c0311015522070401c0a04000501d0a144628920300800c00014a010404140d0104521442210740001007074150a81e4540a1b406a03a6102811200c10814a000462103580f01c0761031616005007007000b000000b066610009241140c1a40410f0804c403051030200b2406400104072819984c040f00c0202d840c0713840c04010303005040301e042c0c2c002814910608101074100c3c1940118000c1142d12500305908101c0d40c84c4c0c00c26209180840365040e0071407002 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 427684235 1250 427682985 427682987
    0x1d0303040f020607120c050106140d0803040201020a15020301060306092d0b04020f091c0209070309020303070c0602030a0e060f1c0902060a120e07030b180f010c030b01022b 76
    0x860700c05075100600703203403400103035035648021298200c0d002c8000c101e02610305020440b082c0140c0006e8421482c214100710428030011301e20101c0c841e405446850000041425a40309104024000b900128800811a14944460000e500900c100c000081c40c1a201142c444420301440e0b490007a50a103c01643c2050200404912050208520340035a10f40c120383c0f07191900c0c005401c2150801c00201d0702c070841d16003404860201141c8107098a044602c100300107075502d904a5030400480c1c600021110f40b14070100c0d103140301d422400760070000440c200003140c6074000000c201040040e43c035080b0000340343c01800080d01809201e0410082e060004500c800d0350640c6094906069000c00701d01000c180d0042100b03035011204190006004920042c3c1024203401180c01120280000b810303207901d96140d40d01801e20241043d00c060a2491444031807072003c014100281c00e0050080102880220001e0001d010389804203016004d039108801c01e80d0b14648182e0000381040b41174804000510710 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 427685485 1250 427684235 427684253
    0xc05010f0207140f07063609060501090e010e0c210c0a031a2b080d020a08010608090d03090203010906050f07020d09030c1505041502030403060b04051b0306030a0b1303031d030304 79
    0xc0c0c078481f40200301c290040080350005c0d500d000f081d000703800050140c1014001080b07448281c001d03600072500040100411088403454039030101e01c44e00f450707481d0300c000007240002c5801440750b408051103c4d010304c80b80800030001080c0c0001c00b6201001084102034503d9800044528030b035501400560420850003c800518081c0d69541034026410455030703652800c581e0041c1c1c2550741055801b03d10407251941100e65140508440d00700b001d020324280c2500380d914000001034004142c2c0b0340301d08200b10744094101d40b03001a070124051009107021900090410001c07545c41c80140700d1000c074a0100d0307004102c6c100c2079a4002c07035008072032814200d0400e0808401d12030b681c02c20408000c0000c10380d11030341c1c1840b03104441c0c0e400395544a01e103050040c10350b004102d00350310440c80d213424841481444a98240e024509281640d101d03514000000e0400321219000740c8a00214410080c1990302006000c1c502c03446500d082100c02ea807048040001360315210800010b41c0200301042c04194003907 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 427686735 1250 427685485 427685537
    0xf1804110f09090a060524040216060519050705090a05090601050c0f0616110309040c030e0a0f0b0c0304031706040204090c021c02010c0207060c05010f0207140f0706 73
    0x6003007070700101840400b08412500c100c440300300c83d42010640d103040181500560f40c2028200108050014410070344410705c146514005124a60010f000e04d00c0c60020690250ae0380e0b0081420000e9203480b4420b14201e90701132003c011805d20303000010701c9082c065400c0d194010340140081001c1030908090000c0c4a8010b040241489014003000c20340d20350822121001c03040708000790903181000054050820b5880c8898001e214480920090300c440c004141c0d00210812500480c00ca445c2c50019402803c8110f0071030f89600a4100312001d201e050f2020070801ca100c0c210b105141d07612030740c20000d540000d44000380000c3c0080c42411446801d4180036400c82e0008100500e4150b03900c421408407450075070443c003d600100d41c8400321141450702d2907074090041c0000c0c01180d00a803002504c9480c03030702825003440401c460138807d1201c04d61040c0d00c04003640500315a941c4541c01e2840010300c1258044080d40f080300d65842e07494a0104210007146c00f1601c07a1079001d00c004030003004045400b = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 427687985 1250 427686735 427686739
    0x408070302071a121305160303020c0108010b0304030f0309080a0306060206060d1112030c010216020f0d03020c1003061509052107030206030901090501150f0e10090c0c05070b090f180411 82
    0x44094000c5201031118499042c05c10400080c814234520f8080e05000d00f8406c40d506011000700100201602c400c00c0380d0303000798545050301d49908200c006800510036103070301804446010409000352605548000181e5166030212551592024108000799054001c001c09400b00000c10500700d09003054a0844005002c05880c1025a0302c2c0108e422a00465058052100c03140c10403829800d05107030405003400107481200c0a4110382c0c41c00383d560400f9119060041382d191105040c6940f2a07032000e0701070031548551034101107072903100410160040c01514420381514403d003e16100a0800d206a40344940280c1a920300e56003c200d03107038000414039240c55481d1501d002c0000c0702032107903030004c2044d41c403500070180c2484000059403009030001035901c0d00c2e03081801500100d44581344115060301001194103001440111031940712058004e0091041c4003001c1781c00101440500362003d410381da00c00010b4401030410550180048500f0507485180300440d01107030101068880170000 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 427689235 1250 427687985 427688011
    0x1110a080d060f0305151b030f0f010504050f0103020907050f03090f0f0f0d083c07020109030c020d2f130b060a030b150c0a0618030801150909050408070302071a12 72
    0x841e105070f10751f90744102e0f85c8680801e40711007004810710091000034094031058504001e1883c00c12007010150744103010181c0f10703051410000f00c04512580844408181f4281c52544900300b038071f103c41d03070384210341d02e42101406501080411500b0001d07296010420100040c030104d01380e000300f903e85541c09444d2000c22103446584d440107411030300180c84a8200d41d90b4020300d0b0300e03110803d910181c6014052078116410081c545011075030048040380e0464040b207401000c600b051030240b006850000078003000c40c102100e81c00008880ca000c1c0d009000301540c4820914181c08203210848545004d40d59002c5001d00c80e00c1e64261003039004120844000d07280074411004400007a940b60031414004045e035120b60500350801c0f10b14040d40c00043e901c480c0094160b80d031030341d002d4031441c41401000f0b0401f958000c1888854410724a4170010848041c1c100700c2c901701810295410341c0180420360241c410240f000401c10a240c4010503410701020030182030070840210300c4005100904582d5041e61 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 427690485 1250 427689235 427689271
    0x306011218060c03020313061d0a140c010309170921010b0114040608071206030605070504030201111501140303090901060512070f0e010e01110a080d060f030515 71
    0x194621030103103a1204060185000000d514000c03003030f60003095403001014010300c207000d00c2061000403401e0095010b035002c9aa00310104502c80d03200700c8910145e4076880354100308010300250304201d40d81c0c0c003103600588081a0f00740005505452602130002d0080152138444501780044a016249040000f420208444881500d5058600d00c6010203030f95659030303034800300603981c008424400c07001084a515051500d0b02c000034000001c020300500901520130400c103070b5402c0036032140014591014040025003442740b8014810b4006000481c04540b44a8541004410000c2c0034251200d4010702c00354540e0921440c40c00740c2c0d10301528941c1500c01400f15030450b03078854040a01030803480d45c0d981c1e00e60b0142268603188042c054055014030811000751980282d0088030028004401e0070150403000700c0900481d0051084040311403a401400a42800c22a65030010100e180c4001d8060010540702e400e40300d00140903200040032640030381d020700608622220076076030100c144016040c00d10 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 427691735 1250 427690485 427690517
    0x1603020c0904060606021908030a0c09081207020411030f150a0f14031e070504091514070201150f170f030d091b03020f1e030102070311070b03040c0b030601 69
    0x140141c400f103505a865400910996904000b03000d0040469003241c8440740940e141c0e104076200c00b40c88036668680354038000c1e4604e03014417889001803c192040328804031103640402da06401c02c5408910483c14466610321105171039094a001d241c0f00e43d02c842007501d0b01c1c000c102002d1105402c45400c050301a60001d06000c1540c41c46009114034110641440800000c01d802c0103100e041c4901c00d117192030200550040001590310544405460001c0d040c21a41400500b00498440d000f406604001c4c1045484800c03044190085002e60000d000001c141051000d01007402d0045119140306044c04000003100d180440c401c11660609940c0e0080c05060382d142994409190359003800d03219a10030040141700c04420a1003101001c414002d80d0860b400145c000001a1005200f010302030f403210618a003022050308400c2000f0001c5513130343c415144c003804800c14003041d1203181c02440c0001038800559011280b0566006650a40740b600f03180c41c2e882250009800b540c100b100a0180800304 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 427692985 1250 427691735 427691749
    0xa030c02012306030607140307120b0402030901020a080a023a0509071d060a170705031e060f0411090a06081603060c020705030318012706090602010203060102031603020c 75
    0xb6415006442d190300d40b04041c549441c3d005403441040000303504004118840107000d980c0c0040c4245007041107a680c43c2c1490014018503500c0075849880001031044143c0d056004002031501c544624525a0303501c66818100d0040c0f0848a0494044007405032103822400310201c48040c0600698007003400c842028001c65104807416807443d03104030414082c4c205e000c41d04089006070100c41a07800e250081c0400c4403c1d007184038101400320458203542e1401c40030702560018080190440b00c21003081541d566094101c900742c004a03006a00c04150606084202c4c20b118540014410f00400e0241c014400607150061417502481d544400c082904d00050000310307440214007034120101803c43c141031040300c1c0c02c001000306641c000c2d40c0420280d00e020055441e9101365070300c01b081601c0312000513250048800d03d0040124000c0da102158a1070090116054442540e110031042d903c8180a900b02d120070f46000d0301683c010301510340242035928031100c0051003031040d1101c85d02d01801141c40 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 427694235 1250 427692985 427693031
    0x160f0507140601090b09090d21020d0c05090a05010503220c030f0807120c03020a0201080903040e0a092604091d0307200102120301090e03070f08030901050106080c0a030c0201 77
    0x10b0b0784032036900300603241011060780c2011940c0050240601c4c3d0310381c064002c252100e6907a554001e07450074035a5121150341a186c40c8040ca50bc14006450b20003801819540308440891042440c0d4201103060b51144056902c0341041c03214180321260f803450165501190840c0403184000c4c16070021000403c4418175851592041100d41d80350301c400d04d0f02c0384500e03c04614820810801401071000310360b00117440c1c88956028203120050361980110f047c298840c640008917124800024024007e001d80c1c0000c0042c2e001c2c00035411b0b030707201109040001130b002045034855828180420301c260f150960107046482a942c0007068070802e040300035819500405030503070301802c2c2899001c1b11904000f640a007000c10900c05801131801c1c800705598140018051080c2d02d990700c03105001919000c000300c0760391f540c000c2d1404401042324540082c0640c82181c403d1b2065003000000601c15001740c0b02035010f442101a01c1d400c02d400d0203000c0300280018500c210846d034071144940c0c01064140c00d202c1c0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 427695485 1250 427694235 427694249
    0xf1809020c0307121d090906060f031923010605101218110a06030209061b0f0604050a0c09020a09090902151801020f160302011404050303030f0f160f0507140601 71
    0x1e5000c415004c10039440140c05d51306400b403d42001041401b0741c0108205070312480c11660001c058410801080c540801c0b440420b00840b1801940001d0280c66244c40f80c00c2044e104e190320a00301c0e400d009030300344c480c10311450b0340044c2d450461401180c055044528030b040f120600180d06424110700498400c4403000645e003040e044011080541811403180380030b414075080951500094002085c00703445640c00c10000c8061030b00c403e2065020030b01035040c816804008682150826003440c648039102c41c50101c5103000c0030500042c0c2c00c0c80f50b00030360743c150f50544ca0b000d22641c41d00018501400000400726440040900201d49882c8510040c1070568046244002190b5581001914242d0810b8000029510042101900c0b4a100340c171901525070a01c0c04a110102140b4003601d103018a4026680c5400301000b00700c800703001c0c4d80c02c071031140c070100001c1da4498490751806400003401c1c0000000045401404400c454001c034003e000031445003900c2280e980c100f4034020700b80b10342a00040 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 427696735 1250 427695485 427695497
    0x30406090812060f040c0e061e0d020c07090501030507030b07030e060403020d030c0c0b01150c05010c03050a061202090a0510030f0b0a1d06070305190504050106060f1809020c030712 80
    0x40424240b80e80000c0e6941300a0307034200900c452401000d8009440341300440d104620024890000d00c02e900050001c101c0030007503440d11410b0391082440070750407924680625100d180000a04124513000e894100c981140141c010036007140c86881003c64010304a0050545880d640081d0300e00400c2071600c503074080d5001d03040c0c5140146d401015116804050020041c0408000380415501d1a0311411615200414035102c07050180640301d400c5a902c01a0165107403042103104260550000b9101d905003d0f0100107103921038141c1c0010340350b00440603410080350000036a46810942c40580c02620400b00800990f940e0781d241c0c2c5500d50698800c80d03100a0f0b86091250708565409241008030100751844071001c6112080b035940c20b070061591081680780c0e004191050705d2440b2002021544400174401ea1a20342091806072145101d5034001030100a1003518151058100401110310143e4980425181c12f0b040406900300c4481000c07980000c210f000d00050045240311040d0100351141 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 427697841 1106 427696735 427696741
    0xd03030e0a06060e010504110a0815120102070506090d0f030504030e0406230603060d02010305090c180f01050618091003120302071b0302030c06030406090812 70
    0x4160289038041014428143c00c40e805444c042c0c241d07008180d0340c620901080301c641da4030b0460040000d010303140d08544283c03800c64011464039844002611204002442c0392241c0703550000300e070350015400042000521240d9800171000029100b11424400007130030b202c600b04442c1c0c00f05543c0b00005801c00d4000c6401300812a0041d0040019a44890605800d01500042d80b181000c002c0142a00c514114044a100d80400b230941e001000c2c9540c01503015210241c0104214020b440740c01c1040d8a524900b0981003c228080104504000030180030411041c2c0206001c0c0e5000c1150201a0134000001c40c41e80d242690f0351107455644c01805840d43c40e4641000b009004841c03c10502c0c5a415000303000003a014400a8030480d01100c6400b51580081c80001c0d0140c00c000126030462500001455026001c0e503000301e0039400c1541c0b000c4855111004002c0640e8406042c = true := by decide +kernel

theorem cover : BRFrame.Cov 427517985 427697841 := by
  have h0 := BRFrame.cov_init 427517985
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427517985 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427517985 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427517985 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427517985 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427517985 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427517985 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427517985 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427517985 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427517985 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427517985 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427517985 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427517985 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427517985 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427517985 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427517985 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427517985 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427517985 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427517985 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427517985 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427517985 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427517985 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427517985 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427517985 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427517985 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427517985 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427517985 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427517985 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427517985 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427517985 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427517985 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427517985 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427517985 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427517985 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427517985 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427517985 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427517985 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427517985 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427517985 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427517985 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427517985 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427517985 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427517985 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427517985 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427517985 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427517985 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427517985 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427517985 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427517985 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427517985 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427517985 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427517985 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427517985 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427517985 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427517985 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427517985 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427517985 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427517985 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427517985 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427517985 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427517985 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427517985 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427517985 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427517985 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427517985 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427517985 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427517985 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427517985 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427517985 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427517985 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427517985 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427517985 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427517985 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427517985 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427517985 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427517985 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427517985 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427517985 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427517985 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427517985 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427517985 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427517985 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427517985 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427517985 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427517985 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427517985 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427517985 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427517985 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427517985 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427517985 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427517985 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427517985 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427517985 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427517985 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427517985 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427517985 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427517985 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427517985 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427517985 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427517985 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427517985 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427517985 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427517985 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427517985 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427517985 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427517985 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427517985 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427517985 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427517985 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427517985 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427517985 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427517985 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427517985 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427517985 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427517985 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427517985 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427517985 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427517985 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427517985 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427517985 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427517985 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427517985 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427517985 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427517985 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427517985 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427517985 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427517985 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427517985 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427517985 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427517985 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427517985 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427517985 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427517985 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427517985 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427517985 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427517985 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427517985 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427517985 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427517985 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427517985 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427517985 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427517985 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427517985 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427517985 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427517985 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 427517985 ≤ n) (h2 : n < 427697841) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
