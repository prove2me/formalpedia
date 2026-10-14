-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2609
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:12:26.014+00:00
-- url     : https://prove2.me/submissions/8dd67846-7959-49e7-8805-f7ad83f52a7c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 469064748 ≤ n < 469244604 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 469065998 1250 469064748 469064753
    0x120106081b12060601051e031003061a010f0e060c0106140a080d080c070609150b1003060305030f0a0e060c032d1603090b0705030c123604050901050a060801020a050403 74
    0x9000d183d50008501070550407200303045481e40d0051700c0d54680841080710a20911415100324cc550f0b43d5240c0c10320060b002001c002074a01c80110365108103001401040d4130711522080c0031904242d46c06002041b0790fa0f120345500c500003158041c1240201c200721004280f00100049940401c60691141c442d02c0ea240e002000a55228260460f00039803031700020800501d0003003203141030046090010412070008003d000319800e448480704101401d001e07040012a8001c030460311000c076410620fa5803141200c1003901c08102620700d80350058800100f80b0404240407010b8580f08079161078068075034010701c00d0350669810054004071102070400c1108418080c101c84001007610a081c0120301540da41d00040054129035002d031065040080e40780c00b0031600b4000500b0b0740308003090716801c0c4107803080420b91401610710390b000003982149960039200100c885811013900020014819450200e08141c0a0402520214281400c14002050900040c000d50307061032465078074a81054990f4 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 469067248 1250 469065998 469066007
    0x30105010c11060f0d09031d010903020d02030c090405060a0f0b090610030b0a0f030c0f0b03040f03021911010315030206030a1505040f0b03071a0d0506120106081b12060601 76
    0xa8194a034030103c10004104946a030b107014100c03c00466000103464845402c02600c0d480301002550403a01c00d45250410607038000e0304941c20389805071911094044144042407400c2000d1550710ba0018034001040100140015aa4440d00482005000c440746000d0358005940b25210b1440e0710482c20710009034182460324821480702d20381d00e03010500b00c512102080c400c01907900802185504010240140544091442c004011000090452600d40481c2c0e29803408080d02c0103100c101d8229809090501c00c2103502c5030b021440188010101841c03400080c10580041a1800b181c03d0003644002c644c55000d0420803650041c000d5132840e40c40035103110050056801070205690724036400b0039561a140b00e100302a10b01000c00082c01c00c0f00d0000c16103402d40961010492200004900003100c0c54001690188401400045011f88884000070003034280012105440d42c81c00000040b40b01c0d0000b8904001400d0b040450448007801003482580802d408a24110743d020501003503181d44078 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 469068498 1250 469067248 469067273
    0x1180e0109020406030b0a240b070309030c06050d0b060a02060f0604060305060f0702070506040b04030201030207020112020c0a060f0b09241008060405060d03020a0b04030e130e0c0402030105010c 86
    0x800000081c0504141d001404444207504243c400a031200100007208500e48101140904c4440142c42c10208602454510740064011140b001c0e00c08181c841c100f502a441d950099940400c1906810b6203c41e8001c02c02c3c0c02042c40710f64054208141011242001c40496440411680c09803a0560b00c0a80c081e07456070001e00116040360341d4490000c0424018050103000e086003480720305035401d240f0402841c00c604cc0d00558442c100403c41006041200c400b100e04482e07081c00c0250320368549000588400e039215600c400303158000182c1014601002c0340d240302c0b26100301d0302001101001d207074581c01c03039041e440c5180d0044200700c0841c00c0f074040c0d401030b454543c52a00f0001a03c0699001041820b003d401c8a8030205154105105943c501801503d91007082510348586550094070029640d42c0c0805c0060240d080846c007180038144200302e505141c3d030000d0400740c00d0b00d007403011500040061005a810b58040d462001c800c03171400b4000c0341d040b1a0140e444003901e1149490b0b42e92440503 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 469069748 1250 469068498 469068521
    0xb0406170c09091c031406010212030414031902032218020d11280c02180a110c0a05010b09090619023703060b0406180506031005180118 60
    0x1900d0100803c800c1c10407010f000c0006a40c3c1c0030034051b45c400d001c001404805005203040d90013030003006e500300c1d09210a4940c4a41c10020700f20b0050740d010407507401c51207442d5510b187c3c94020661480c3e220303000401003420407161203000035900343c0e4000b00c2d58a100f06024401d0b500200741d4540011110a80150441800301031002409003100d00507143e44d0b80c0180003990b9414000c1502c1440307c0c0450000d042c84500310705101c0032025240e8000b0711310400c05000c0c4202c804000000c5039100d60f642c1c0c011410150b60031206d070341d1400c42d11010350384c4c1c00007840300300d403030358207002c0001d00604140025500841d1158014905a1150b036a80c1042616128542e084c15509000b0001403000b0211007081d041c0404040b4018003440141400d0748034580d40104042c5030038100104000f000803000ca6046880300d1070305000f07070080e078040029440c2581d0300c116071080f804814040b66a80c522032401c200c0b07000302c400404040643c2c500000280e030034804d42d100b802c0300c0e0800e0845901c85800c04525001c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 469070998 1250 469069748 469069753
    0x3305060f0f0117130c06020c030d08071e02070801060b0c07051c0f08091c02090a0e0a050f1005010f0e040b071b05011a040e070308071a010602010b0406170c0909 71
    0x4048440039900030f049a1540d500b245140c503610030300546001000180020388042c280d503650b00700100e5075500c0f210340c0c80d00070040074030001146203110b88848070440007000320f514000f16440358002e44c0c4074201e0156003825482c200001039004400f004903400c03d0b80c01c101034942d0782d240404102c0540b1224248404507408007500350002024402d104200314411160301e511401c2c00414040080b440c188a28402c841741c07210f41e40035a0f2411415903010042c41e0001c6800c40810500d542410b000507001401880b0352030f142c8040b1000820781c6484402601c1080003144ea0360a4000038800d030038890360340042070b08404a4003107802103100ba54012540e05044190001640c89400004210941525030b41d6482d02e40c4491850064000c03190300c2c00440f0103003d44680c4a4004d43c6407090751000030f0411303a0004030402004068450b8090844040b4192465036959140183c045c1100300310745403080f85441d1022900c51081070348201c00c0941e200007411b01c0c48000045c0961320070050141943d51 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 469072248 1250 469070998 469071017
    0x3060f1b041205010c0305010b090904061e0603020f0a030c0311033301050405010f0504050901181a01091401060c02040905030406050702040501080c0105030708133305060f0f01 78
    0x110800c0300100014010080000d0003000b490034280e084420403070300c0c102050700386401003204465020903284011802c41e0b02011035101c907d444001403e220520b41c5e20a40d10b0021440900e1140c0c0c04002224001e99030101d280c1829403c000000c2d500740401400034484600500107d1000300c00510b801001800b1200002054480840c0740441914484001613100741d03072a00048452107103500404007900c052090b54100a200c180080c0da44c050300c0d010301d40ea4000941000000d40084007042c095a00c50a01480c40341444070410304c40c0781048194800880c0002072041c00ca1082051095244000c1c1400381d00f070003404c60f0311900350401640d11a440300108400310f50144002c0005107190380f00c140d682c48141c410f10003a1030059000e030b0560340002c81d50701d11991300f10341242e51202d000d1038602d01c6a510a01035003024008210060600000da0300c1c0c00c41c5610b844141000310380f00c520070b41400f06005900d90010f4683c22598207401100c0c0e101d25000500b402c01041e00451014108003021 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 469073498 1250 469072248 469072291
    0x170106151b0b24010c022b0602030a02070507080c0f0f18090303062b03080c0d020a170c0c25030618031803031d0d020d1202010b010e03060f 62
    0x32200b094400c4007540d060700c040c040c041c1800c0070325503140306420f090074000300316241c0001f200301140c40b05101d0030140e0300c01d904074101d40d015020340700964000c10454880c2007404042c0c00942000208840074880c01901107002c0c4000154004200d800400c14803469000c90140010481d054440a0708a020299080a030030780075500c40b445200064001e40e240e19103c01040900311a400080c281b4407081c3c0c0200c80340c0d03440440d82c1c0b14020b8050612030326039110300c010060944071b071200611a0074030101315120603a50020b090a104014081c030502641c4418030114100d101e11601c00c4040c1d4012542000031303040c101c181a080b040700940e210440d560343d840705015100d0468480c030074480112110000c00d6001707001a1900c01214983c40d80e110b045039000742120705240400401803c1200c108440303503941a09040030b20741c2c003400401030101d803460244074002d13102c44804d0155003450050051035200d250382c0905ca040040041c0856210b02646248200740607010000607007a51071008076 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 469074748 1250 469073498 469073513
    0xb011b1b03051c02010c05090108010b0f0408100203010312030218010e01030b12061b0a1704170a081905100902070c080d050403051c09050f0f04050709170106151b 72
    0x812076841c06983c040072000303200007421191501205030501005000300f81050b42d00044c2c0c45d041d00c0410400c11358075890034407460402c0c000d6501090051090300c1c524028000242c02942c100c0384107032004803254094090980c280d004002c4d56081c5040100e080305c1c101c2d0312502c7c2070151788006040c0000c0c406a0200450b070300c1184101390850960050b410300200803c241010003c001140240038108200c040c0002d040d080c21031640c5019140d03241c0400c080c48900e040c1c01c8907143c860000c241d600c4680140280c00c84000712582d64402c84460390b03070b00c1e43e0055402058800d10026008510030b505011455009404c01082aa01c4985200340803c85030005c211510b4284496121951920303d0741c54141c0c80d1030746469a29007120074000d0504480c0b07421030406000d40700308031515410b044c040d40100320340c000e640b842c2562090034201806001c43e0420318060607078140c4010b4415a8542d520755a003030f144a817140c41c0c0c0c103c00042445011622034800070740c22078401c558404610700652103882 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 469075998 1250 469074748 469074763
    0x11070b0a140c0901020c060a020607142701020607030903050904200d060e0702030c0c01050a0c0c0b0408010e07031a0405070e15042d020d0b09190b011b1b0305 70
    0x20040c1400040d98801507170108071444d0320071012201039142400c0904025110710f00641510240080f200e83e0900c80e86141b82907410703114400b8101c0350019543c104181e50058000700c518091b01490020a100c1403090241c541101c3e0591545468094100d06000060030028400a200f1407504440b072800e0f403040f402419510010407002c54054200182240d80d82d1020b0403103819940700f00000008640081800300c8500c1d0242095502c0c4d050443d006e030b034030809203080203103101400c000105941020a0152059410803002005851903507041035541d1266800040c1410035400740d4008803c038803114080e802032045003900d0041b0b60340d64661306115002d0314001d15221842c0101903460609114150f090a00c02080c4c40f1128a5840c90000000312803081034192074000a42480e1000f16410003141c1780c03400b408002d040d02e400c00041c42e032a0000340c43c0103075581c00c124164889621402c811890200c0e43d071140140103115580d00001c1794005100118111070100000003c030f0700c01c0c082c0c907 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 469077248 1250 469075998 469076011
    0x6030a0501140906130f2d030f0f091a280201051e01061d0102010204150c0219150f02010908030103060518190b10050d200411070b0a14 60
    0xe10909003c2462403d045005200c4143c013240e141c864408150b00900106189800c0f00c80f155000302c11082e42858451030300801c104180e00007034500101584038104800d0106690790711846010038140403980d4440301d02ca1a5840500381c080210a01c0c0c89000610040ea494540309449491018400d0080655449590302507552001002451455126000c02c101206903104d4115814110045d0119000b84d039203000a00c5241115004c41e4001d40c102c1d80940b40021182c0c88085100200400e21641407400303d0041d0601c460b1001c074448000781e41d03000e84070102d06242c1581d804050444403848802e9031481190b40b0382171041d01107590340000318040c40c09004089441e281100d06540c00e040d40c0700e003405160b03200f40380c0034580e80c080300403041c480c550065880c44035403a4100e000c0c0f0100f14540050b41d10013910420a0100103c1040c0004c1c803a201c00c402c80c20700012041040203e500c0008280c3c207240c02080941e0026030f01d82001a4440b10a090000707608020340d503465015201100c04 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 469078498 1250 469077248 469077281
    0x50a1202120a080c0a031401090b13052703191d240c010213080a02100801050d02010c050f060106020304090605040204030c0504051003050f1605030303040b010e06030a0501 76
    0x5511556506101c0041484640a60350340780048a000c010445800181460741d4100e02264014001c0c0c07182d0400800f2030000c40e40781c0035558482a00740010445240020300c10307400d44011002c218550f010340ca21440310070f1883c010034002c00301e400c003024202084200480c0400c201c24400001c0070050f00b8050270440e60342100001c003d610f021103121800f00502d01ca0040305004d810916040304440280102c0c2c8580e540d10f48010080340c82c0039008131000b5a4001c00054004588a0304c00034185150364001c81d0010560b4445a00641d50400c0a0140580008038000c5002c09540602c69074910f10b03204070304681c4030b60380c101441ca08010003a0842d50040c1c100040822410680f801034101402048504500d09407840ea2041d0a4a0440c4aa01e0080b84c59600003240c2c90703000b0134510000c42e08503080e20440c600c00613400c0d0312103e01161f142419181d003c030210303250400000382d034452903000914003041c0e420281c0000c0344010080846a051244d144c2c3e000010702c3c01c0c040c410001c01c40614 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 469079748 1250 469078498 469078523
    0x2091f0320040e0619060308041e05060301061b0f1b05101403040f02010c0f260403051009020a0b0a0503090106060e03070306090c23090106050c03071b03050a 70
    0xa2591208001e070258480c41c140300300114111408501d00350454801421a8000f40e207100f10b020141400e035001030109071001c44c0004800c20700014018030140c408007100200d070f4440b801c00025000a0140d032002448031205003021a183d41503444400b4011180044072194a0790b400541c1044d41c0451500340045240070005800c00203000140006641450742e200145213580100e0f84c00010800b0740030600d0341c01c00d0025640642000342e4410340000301e004280c5d0680c1407030b0380004410b0201801a4034007a501403401203c4601f681c1c192944580600b8000305000041000f40030300d80d1060344d1010f00c0c2c1e80c002508040d176200400600006885240e107910305160040d0071203600c1d500c03150038000040a04001c5640c00728000060b203078000340018030750a0300c0c01c201c5111980ca8110820150482403014100000c82101c90403251045560024980c0c03140c10442e902d00603060705140651051281c2000111004641000800544000712044e0754a86a152804400020a0310040321252 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 469080998 1250 469079748 469079783
    0x220306020a0e03010507020c0f0d0b07050316031e0e010b060c0c031009030207440d0903020a17030702030303040b2d0109020d09020d0302010203070909061202091f03 73
    0x40107146900780480c000c002614046c6406502e440154000074458807044648200903995009950310980d00403031000a5498880c0000d0016441075422004500c1c80c82c040802d424424052180002d030780a8517030507400405800c1c400a0034602c9203104465480c0d10ba80307a00b07a190000070b0510704032030400902d40d0720703411001c0c035003007a299070318410881d41004030309008079800180c00822203044001b481324182c5666001d00e02c0d001915080a60f20030003030581c03440c5102603007205080021f80015500c41c0d12920000756060802c502c802500078465000030488258000c100003200000c0030f007034030319012041e4006401e5510840e421502080b001c02070290040341c6c0c503030240f06408000404c8004410400c00c0c60481c5605103c1d040b07815800007242c690b0074400d80c000d2080c41d9406065804003420510f0b01034040d400454441c0000355000c000011002c8040c052442200e0b800320a0f051603164680900140c11001860064011020182c00c0b100300c0d1180310110046014000301c00c10301e1002c8 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 469082248 1250 469080998 469081007
    0xc0d0e030901030612080304030c0c030b0403020715030b090103060b121609050711030d05040317160f020d0509060a0203040518010312050711010c0314181c0308070302220306020a 79
    0x79000914800c0c15405d050f4005014071003100e4025815050413000317030070325250405100d481a0401803120100c0401c1c88200340d0005030b46025281c4001034905a00a0540304908032400032808a80c4004103800400110310b1580c401c102d50342000e0001482004510065441c00a900d4081410360f00000d00400500e001d911600c0e81250007031424102a00070f50744c4641d40c07406440910490709641e00c011404140c00f0703407940c010f10001c0c100030034104e14007100441c088140440080300496042c209a0040740d10104044001c101035072192410404c582084c004550016200081584820030003c00c0940c0d52060441420401140146503581145000403000d2070080984090010610040000410541070422015406e20b4000f0010106050848003040c01c50b80d40b440d007040000c4c821115041080303140c5000d80d4240c60580c156843c1004149000c92420400b800207560b0202051000703200360001c01e802201d40da0143e24582014407980c4144046900c00c842e110342c0011046600c41c1c12 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 469083498 1250 469082248 469082261
    0x6111206030f0303070807050310030b070f021608101a0d1b0b040303051611041e050c030601050717040513293102120906090102041503050c0d0e03090103 68
    0x34003d5402d60418000240545202074501030901c00b0110001d1209804103007003100454000904145508001f903003d080b0501842038180103010700340542e04642001030380801110940c40c014500d00d00e001a01da0005c1000c148034130b27064844041d0320042d5950754000012240e000702280c4603010908100c04d003c851040e4045000c001003440304102003500305050b501440320b001c82e594080300c6580740800c10140001c0d00b072075000780b41c0300c90740c04000711030450703d0b001c180a14401c2010703413a0101140d41502048071120f001400400c10003001992500d4031188402e0000701880c01c3c5074640d80062030f514185500280c49564034413200888072105c0d0304000740b00d08030703c030b01c9400a0001c43c04914925103484200300840c3c100c40d00110311106010001e5030003102c0743c00440d00c8054800f010218204151110b040c103204d400c0c00302d9040c0c0c60600c00c4504803030810340c280b85101c604180580152030010100c40b000802406181c0d040794035400703685000c400c2e220145130365034404070015044420 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 469084748 1250 469083498 469083523
    0x140105090f16030c0c150b150f090f01170c07060b1002100b03160801090210020f06061c0503070c08070f0506040306050a060305070609050405060423040611120603 72
    0x1062410b00480700801042d201c4040418a4040380c0e18502c50025101c100000200903c044604076294200340203e40c82000c100700300f112141010b040f1201008030702e009040b40042e40a00801c807100403482e0103400114241c0c818145a4035404420f844201d4484044555082d04030000411000700003107441010403413107084a5030144020b180100940d41d00c8134001001d0b1a40e60781004000a40d410030440e61070000d034640740d40440ea00e074a5154041d2481c110f0890081e100035070030300ca0103800822082c941007203080052084c0c0c0d80b03180400c00542000100c40100c03145008041010600600040100f00d009900e1180b405107081e006626104141e4403007220704118910a00403680c8034011a81240e81141c408500c54640341c02441c024241580300a086200e2180b00042d4540c00540e00c5040341e07812902000381d5500d180501c01039070f07107985001400d9500140030f02e000031040103807150014021130700003880386d00c04140c811441d80300c8a1038003080322082081282701d290030820400c41c0d81 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 469085998 1250 469084748 469084771
    0xe0f010903170405030a1409040908070507121a27150601090b0a14160507080712020a050603180304091523151e0a4e14010509 56
    0x41c00e919181d40b1713030054105c4c80c4104030168000c050718130301c1001503a01d0004024070030028442c0504e41621554000d2004039098002c00030005100c90889a00116a54100c9000b500c000038030802c1c042020030040000c007001000c940d5510b598044400a00092841e0360000d0181d5906e5100c00c40c25403000800d2581001a81c10741440039075100c3d000e0700c60380c030710314104100412012401250140035031040710304a070800c1040c07801400300000d8940304950b0240255010350781c850006000c46800c00001a40125101008008905005c1c000b198040d0304036041e070442c4401c2032041421a4055403010f00180d0320750b04550500100042c0c440014220003185e075600311241090075950f498610301d101e11990442107041c145800c03900c100c8800200c442c60a052001e0420b10403032140d001145010001031188484441c04013000c100c000000c078198031a0041d140c0010701e200c03d400940c0412507000c01c80b00c1d924a507000054080c1000c1700071850281c20b0b0a41c141810302c110408002c02280445 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 469087248 1250 469085998 469086001
    0xb060f220b03070536160507110a03080c0f1501050415080102040b0301090e2b0e091005150711010806010309210f09140d060e0f01090317 61
    0x3401089030006008040540109080014100090410b800ca511094104806000342008280351a07141800d440718140680c02c048000841c5480c02e0a08403000c01d1000f4242c000324041c1d501400140c0b40c0d09108460100b100250600402c2108450344d00803102e0039004600e44011580c140311a9010070b540394000c0100b004000b2940050450601c01c03540526524403441c0514080b0510035005481008001d41d40c5540c0ca441c0000182d00034801d501c600340c540511111600800300340480700c10310910003403240c8440e40011001551140d40010b0510036204622007040e140e0001d028401c4109011b005202490300051003900c0b4035492035004072800820101000400196443c0702000d800c1ca4030303d145075100401640107101c0400c003d090008035140003e440440194600481c1d202995072041104c0801d40a80d4071307a0749400381004401c00e00300604010b0404920140d0350314010b0700041202000068210f04cc1405c260162495944039169a001e140d005100e42402141d07079104100503 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 469088498 1250 469087248 469087279
    0xa050c010c0c0308160b0405060411100c06110903070605040f050405010e010603024608010825030b0103122604081c0c051c1a0112060806040b060f 65
    0x140900341c04000c0085102040721100c100b0004000784085d90311905002141c142403c1c803a96a0344221001c5401611142400d10113040c84400c0d240302c0481c4d51910080380600d651000080c0010b0314000302da002e014007079507446a40400040703006000a8440ca5600d50410f03042c1688032166400082c0290304100041010300040f001090440700c02d80b80041c2c6a0240c800b004c1c5181120004041c88046154400c40041c0e03c003016100a40399051340c01106a1403030101642c51500c2482400340c20b4020f65550001d00440c4100c0090305003111031170383d4160385ca030307a50485080d20a80050300e040100400c003804080c0c0140c403c8541031003100d40d034030418100e650900c28144008100820200010583c20040141e42076a41e049006440081c8102c5100c400028101d402000c1c2c0102d000c401c288000300500c500b440f551060010b03d44045404141c1c1d0b03801903600381800c41c40c2e280015035400d00040c0d03000080c812a4055841088038421034103142c41001400108840c2e864070072900c18a42820 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 469089748 1250 469088498 469088513
    0xc0908010204060507150b040203010b04091b0f2a060c0f1d061602030d030221090a0f05070b0a08071101020a082e0e040210080c04050103050c0f07050a050c010c 71
    0x10f5180c6d00c5461048502e040700031030005000b51808840c1c000380048000b1071078400f800e0207032040c1c0310000d208022240c0000c42000707a080101104001049100740009a094404c041007010420010030991100451039540ca10103445003205941013a640d0060681c02540107800d030b2860180c2c0c5c90030b07008410741400300d01d81c0c060141540c0c9206150000309501d03240561410b0718180340d0028183c1d03141004080c40a4042d600030341c500724440620179a00e03990140401481d84c01014018018203c0191550381c0d0561012069819500c9109440c0c00040c00c4910f01c00514400310b659940c40718034208039502808140d2446801241d60340148485a0300380d50201e40c0c6644000501c4400051541001d40d10a214451200c451400b00e110140800c001e00c0c4644800c0c0102c1c400d0340c00840c00112108100c8100e2026240d17498052001c020420071580f19802240d040894154103a1070304030f00c0211803480d903000a20458841d00b02c50801400c2c01001d2100d254501c1c400e080c000480401c030755aa01 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 469090998 1250 469089748 469089757
    0xc1e07080c10020709020a1e081017030f0d1506180e0103030e210106034b02010509090124090b0405120c06070309140307060c08091207090c09080102040605 69
    0x21710303165011503c07107291032080c00f080c41e001c03041700307002c02c4802c0c54105e0007410070b44112007800720a10f14003000103003a010020b003030401090540203035042c500720701c036041540d60240b4111141c8503120f0a00b40040c901041213100245801c3e1a0282c0300c816070403101c0e0402c80d5a80c0142d554940310401040829040426103010340e100700d5600d20280c940c031440c11044928858459003940c0303004c60220805c002208012a00d40000e548174604000040008070780c1400b0414001c00c0c0c04401e00c5100d850720108421603a028414180142005100000b04110090036440180d01c0f00298000c0016622003818403c80c0d00b41510740003007501e081c1619120b29115511030341e4040e0114031494150a8820300080740b4291006022a55503009802c00031b00b00d103240c4c000c00c04520412410718140d840e000814108542458680400503142901d990505800104003507412158510040315050303801d22464028004030500000d15a030f9846006040480b0380e040300b07144c0e0f8030412082c050340d0303040010b03113 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 469092248 1250 469090998 469091009
    0x1b23071e090c0915090f081b130906050a0606081614070303061a1b0a030e0427081c1404080c03120103120f020a02010804080c1e07080c100207 63
    0x461202007481086518203c5580325252280051202d020307220352000071201240c10b032580c40e40b0b0040d19500080c0c3c55100c0ba0218801c00c0020741035040041c242501204810300101e03100107a40442c40d00c0c0e0310103482040f0b072041074040d6501010b0103442e03000030a840c0c118001c000048061300621801810307180d040c10b03c04040340e0000c00d0745401c2521030780040d0040c02e54001100c1e141c8142025130219500304002007000c0105208405500c07a00c0028414207442d05540d844440440800c00c2c40014101c0c18140c00010305000d6282400341d10083c1030075140c621a022032030340c4002d00d40c1d03201d0703450303c40c0c41c074a1030314030300f8280d00c00a030713400301040341c0d0f001504500340d2656040c8000389645140f0500c506000790020b0000000240210510a802c1000c60703a150701414001004080b61120303001c00c0c00901161410000c94042224040505074002c1d01070201c1d040c0d0940c0c1c1c666801641c9030030a420344a58400d2500703015081c4144408685c02d03c00703884d403a4440482c1600a519202ca07070146 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 469093498 1250 469092248 469092251
    0x20a032a0b13020a0e04111912030507120206041407080c09150907050904110f03070e010302040f0f0906050108131506052112090d031b23071e09 64
    0x30440c0d42d0b80b120914019507900a003900c40c0f05907203000c0200214401c84095490aa40d46c6108095040420321601790b2a80005801b0043c0c3c248014003100c0f035212007040d03042220501c512400100104056080b00409800601c46450549401c81e8800360405003500540c06c40e03074040040240000780d2124540048842c0b80c816543d2210044103002131490f1680d01001e0f103828000940d8101d40103160001007a07400344404040e00240070740920035a080d0503d40141000060366081c8510301003590030300c05140161410b07036180c0140c0c1c0a003280c0d81240c01c80304220101000055150300c0350b44020102800c15840710714060000625401854402500310034285041d003850020300c1e4440c4c00901401041c0d0400b41c0b4a00e034488000c100d4480e038082082c4124102d80c14100d01d140c055404108008002c0315000801e40c1d0221102c20321501030a1020132343c2c240d10400900c507a0702140703581b0300a0441240d54503204582a243c03420380d51140507030282c1010320811340056103076503500741c9544020 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 469094748 1250 469093498 469093501
    0x150105040b0a0e1e0705220e0c07020301060902270f060405090a020702270709030c0b0703020f01050c120c04031a0408070506070315050906030601151e020a032a0b 72
    0x4810f5403030700104040104442c0340c0c4d41001490ba800a02500807112481e00120340c203a0070380c5504000b02c4107030140a0480b007100e00000c040c004c0601c004c2410b188040c0002c82c001e940c030340302d18090340c000005103154190803d146850203410b403111091101c0d0111500c84508001c680410032901c16030282500030304402d00004c40080c1650125100309a000e050b5283c610081d00311001110002541c2c001005210008501801c3c0304001040540f03030001d0400310340c0e901d0302c03c0b00e584582c0040000c07403c0d800740c110416800d402c2840350324070400c140700704103075074464114440c01c400320028281c8803030f10b8007440301344080340c03d54201d050f034060110074100b02c980b2103040038002400364010041182c070a841c10082c2c81c5905802013501d00ea915240300040d1b0352140c1c20031200c560121441074241e0f01c040010401c485011028160004c1142000220f10002d100405400941640d03100c2c00759000c050700d00704150340b0900f61341d00c5030381041d20b04640c0540f071100c41e40700488400380034000604810 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 469095998 1250 469094748 469094761
    0x2030f070305250903110d0201020709020901030f060810050c030709150c02060706140903280c020d0b090d03110d0509031c05010911071e1a040302150105040b0a0e 72
    0x40f07104250094042c000d110404005800810815a03400116861101c48065000f1810404501c17403001d5816005009042e003013200580094100c28880d5040544400707529260b150035100c0c84014000340f502403c07120a0489004d425200c01405a0003418010020816000e40c0301500d2010344620200308281401c05080c100c50b40c81140f9806540000002000c40c100a03481d0f00002c0b41104200b1008090365072807020a03242d0081c0030b040d5022514a48070368202e40305543c180c03250700c001c2d8100290040c1c0280c0101d443c130300001d041141c03049039a000b44191480b041180c0301540b0fa00c0c0c9001e1000342800e07000c11580340594000008100d454801154a501c0c1c01e1054583c4221a07600592410707012507000009003c003031058a0960b0324041c03d11403030404080403142c607290800300380980042e101c4071242c4210640d210a8590394510310150354500d401d001514000e901035401810b248507406c00901c120700701a0320092259290104002050725903400942c1210543e0840c5c41450341c40c030 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 469097248 1250 469095998 469096021
    0x3040b0f070203040e0711010e06010b0d0b0d0606120b0a0603030c02010c050708190b0903040f03140316030309060c0207270603080a090f0b0c100e03070c062102030f070305 76
    0x940003184480781794801c0012240c0c0c0300c59040044510b4000900006242101094842d90280a0300b601c81e00c003002806601403094200320092500580841110003080e143c03002110709907044441c0c0c10b2406041c4070140034100d0410764000712015000c0002c2442c41e179000c0c01031901c08100a05100c0d0890103241032001c144140c90040c0707061780517140403001c1211800001c0411840460740c151807040850306032103000041d94141ca03807035544460601d0640e201d2050b21440c0388130032040c1e880100140000155200701d4031034030720f10076100414161114640841540d500e50780311001c6500569007000a0111240c48562640c0500303001d0144040025034078000e0074441d00081c02c450030000703154580f0307a4000c00714400c582e0940151142d190721402101400c0c803c10300d43d40c03140e41c0007000c001e60f00a40d83d80160304811214044910700020b070b64903800c10300324507440203021802c00c00c200d02c8802020b141843c2c410000010462842c501314191480a85001e8051020141d80e03030000380d01240e09 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 469098498 1250 469097248 469097257
    0x1101081008100b1c15110c0d03110d060608040c0504140c0c0a080403080408070f061d040f0f0f06060302091804050c09090c0a0605090d020d06020f07230303040b0f070203 75
    0xb5800c003d04d103020070342481c40c80d03501000e1003a11803925040380c00c40700d81203403800d9502d090f40c450040c00c25031020703c104070003510a04180341c0e5449000c02c40b0004240d0382c0c1c49014020141c980b0b1303840c0f4a00d05810f06480b01d000d103910840c0100d00301000861540400c240482e4400200340c0e0440c2c8890148070520701d42000c80c000202640b8000070080700f0b02c50740002420895038074004032688942ca034800e045c100384d03040c8a00004030f550740780f202c03007280c1c140410504102c0014200080c48004130804100340ca01c0080d001510b035507914195010701d001809400e0217005d01e812f0540c600007014010440940d403125103120b16518800128041001c10b004d00c1d5a100001003030304d802c90070882245502e0740e902c5c809091140000100014049010b5001d13941c13449001410008404010380901c112410201e004845075036080102030703804501c040141c50864040d58080c021504100300c43d1504400c2c4041c2061968000e100300400116100340c080e41c0f140e0303d0f802409030340d2906e02090b403a5004 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 469099748 1250 469098498 469098529
    0x1d0105030a1d031b0606010e01170415020a050d0c03061404090203070e0403050a030506100f03021c0204090902010e0a031e0303020f0403060e24011e050406031101081008100b 77
    0xc00034140361180030150032800b45180e44000d40703d9640b070380c6c4015140300b0383e0030300000c0c041541d09080340d448006c25071b07003554440c0c0a1010340030f0010762011540b04a90061400c0c20200c0d40102e15500d40c407105108000224201c0c3c1000c0080c5810125a000640d034440442c034822900c0349103101c00c40d1410f100000041085010616103802c1600d40500355800c40c070b1000c0000f0385480005000d41c5003220b08482a006591229145d02ca41088100c01a5100c0c218056800042203403085c0100c1d21803005000600a078070700040d12070b000d88001010741e052190854468a074080050000c00e0807402e424844421495107903003828010b02c2e007039000e0f000d03407901c0f00d58441c0d01017800418444507030403e24030662054140c139202c0401c1192041c6c62014641c003980740d290380c480144446000e0290141e0300c0d18000c41010041c503501c000003001c0c4e6902d0b410480c0c0e5900c070305c801c40c0c8155800c0b4030aa5003240114640048032401c0c40781480d0f03240300e00c2c08003100c41900c511040c2d02c0c0b51a81e1a8000a0b180c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 469100998 1250 469099748 469099753
    0x6220b0301060309120314070503091923030711060c070306060e06090c0703020c01030c02030f030910180b1605040810060314010b0a030807141b011d0105030a1d 71
    0x1a0340390b4020707009040e00b540c01d8400e03880c086120745085100c0d03c41c0e904805030444401a864070f0b04101102d15401c02428411075200d4181c5520305550035146c0900558454228029100c10341140e06001d4a000214050a40d205006980010b015403491171441a400e4603a01d440b0300203400c51601d803103103035400034100d07904d800400710310442038820b000e1103035401790b03403030902904c601003554182c0c03040d034501074010703000000d141000e076210790000c50b425065032044074140b480c07202c50f00700791703900984485400703500c0340c01030011001690081d0311070b45841c070801076803241d2079840711059828010b0803106c0344421841103000844c01141a28080c0503038404030b522800c8140706100003046075020544008080a144840e540814040d5a81d01c200140105060525655450403aa080208120748901264000346040282005100c00900020083c09102d082c3ca0b40050318065034050b0308101c21040342400c040b43d0745c100d000c9039001800000d0004241c0707050b040080c81a40700108002490 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 469102248 1250 469100998 469101001
    0x91f060e010e10051c020d0f0605100903050d120f1d0709050603030a0c020607050f06010e0606120624030903130914070c1505010608041a0606220b03 66
    0x450380022146420282a02c03034040070314012080006070702c10b0442a000040c01002022444154261a51007402c000701026040070b900480f500d0907601c00e401000b280558a40d4200400d150001a0101542d0070303041c05c882242c290b440d020b44804180d52541c003402904801c204540000c1d6100943c00040d072001001085046500b92140c0014460041c21901c25404042500c034140d00ca072a015400003402145400200c19007511903005051040e60b00500a11034200410007e0201c030250f9050540030f84074642c140125040903030b4024020900a110500c0620305d08810303903075425000002200c02e0102800181440340000e202e05c011464201804810b0001055000000e0314030b00d00000c0c80443ca803074aa64a100440e03400480840665901001049400d8003075003034900b04502800c100c00360642c80440107425101c0a0b0b110b140001c0c0700038108014800e01c01604610070f40781424000740760401000054490081000f46200700003c4654003d40000d8500460000c0090300b100c01e469 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 469103498 1250 469102248 469102259
    0x9060904110604170d020105060a060f090b160308090102030405031204050307020414150d120e0109080d0e09090c03070e06040f060905060a0807030c0e13051b040b01020d020705091f 80
    0x1c00488440340c0c0161711418448089150060041030300c5050b0260035000c41601d0b01030215044900d1000c0030050100781c00e400716003200128003d02d03a51001c1c030086c80c0d140200d450010501d0b0002811a02c043e4414418040050b00110071a0b01a407444e10071203544e07440310305180e802c61140303180096202d0718121030641d03a6940316411500c244031494094115040031014440400b26695006000d0190200a640c8180c0a50b2070a1070005040c0342440c00355495244452030703ea209116003022915003080500c4501d41291100c1e8400840c00c00b8150f18a0b07550003107030f540c079028043c140341e40e03204400090842e29168400001694001d5007400603035a945080002048103423003203800396148681c0400c5140001030024100ca60080c2c00c2c03c6c646244c0f20368041d01c40d0780640080c561120111b00381c00810b80410054280c20301c91042da461540a420420040320440c405090540d082404a1100c040d00482d5203812250305640414443c0c0da0429800714032040803400341d81c51841c0c03905c0811ba = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 469104748 1250 469103498 469103519
    0x60a170a0e01060f03031715030d0c1e120f030b0604060c140307051209030304030c031101030b09160c051510030c09020f041403070306180512040509060904110604 72
    0x4044841000304101900d4070000c4e6500801030001501040c245c083c14403080115002c5a5403007486101055101348000700000d0400c100b800c55000041c0c0010400e034113200402020000240b450b1000c04220750300c07941c40c1407000302d00c0d0344040c0a104d504c0c45141e10290090b00141014440142015039594070f9190240005044c07403426142801081c4000c42000000811903902d40e420500514405000d120510032540c00321803417a8060105102c00400a20b03041007c0014601c205803490300c103070702c9000040444000e24401445030aa0009205075950180c80b1061780000600c2e05400a100c203041c101d28001e007102c100f59006840104100c1c05d404515500000c0d24401ca441d800b54555884440e02a4010060352000c50700c0d01304002c101001610680700340003d0090f003136680c0740f562511414101d4548191481e82551003464800400000b0310000f00a1284950b6490a1506200100b250100700910b80c5029074024400305003800410040c030015020001c009682e034030b860301b03030614 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 469105998 1250 469104748 469104761
    0xb0408070609152312010303110d020c0109090b04090818011b0b060135010f05010201050f0a02090d06050106020102070c0e070e060a03060504050a0605030d020a11060a170a 76
    0x900260b0486404142240c0488a01d150000c07941d50702e040c0e138403040c0840c18142c0440204c03d044c0210030004001901d54500d0290300950207503d0700504915101001e600b04500c00b81020215040300150890070f070782281c2014141e803a9000000743c0c443e11503011070002c054501b005003109502203000024030030fa80c000e20006990a03601c00150300c4925200b4100d850090314010300d800c05001c0007901c83d51080c170f206032204880c421981550b20180214011800004203000c104d24800c0006001a40ca9182e0b00002810284000c00040c40d001d503036101d40301c00c0a4034618540e0f8000440f20035070341c1c03404003003c48240c120300c042000356900d6034040e000b58044001142d8a0014842c0000d081c801021500d00c00e01030707901c580305600d41110400050b54003181c1800c0516582c0c0d9030200c6c0a0f1204d04c2524030440090a002468501b0708040625200103028004119448550800000b420031300340410040001d4070070070b0311401c000710f00384c0342c03c40d0600410050071420010050041c0031a040f08 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 469107248 1250 469105998 469106009
    0xc0705011a0120060112030e0405041a09032503030209120a0209060f01020307030e13140414030a020304140a0902120f101d06030c10110705040507090504050604060b040807 76
    0x541c2540000010b040640c0080e0000c0d2655000213004008a000d80b42c000d4090070710034909420090007401c00034080710016901980d841d01d0504201441c0c9171405040da8002400300011410321a0401c2d5003c1b00340d00000804a00d0000c24110f0380c201402070b01a01c200ca000104500c80c0700e80201d041030341d12004001c0aa00c940403050104080e402c00c400d00d500141010f0313024511340380301070320103440c4036240f0b0240036080101703084695030894540c428070885980c1d0354585440d5043c07908002004000e00c004000007900304100d1250043e400004840c05c03036207078a1082010700039800000b500d02c030b42039029110450000a02d4040c2c040c0180c445417040d0240d801e80b0419880340d90050360304401e58020528244441408441c4070340c880342007290b102030b0080841d50154401000304544040040c41b00000c40c1c10303181c019420000521612003d420266402c0060b854a010b00420428151240d54025540d074804200e40da200c641000020300141d2410b181c0d500d60710005a90b83c1d0419103c3c1 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 469108498 1250 469107248 469107257
    0x703140d020a111002070f1e0c0801021b0313120c1805061801062a1202030a02100c050a110f0f07060306090b0a050f061b01020301060e06070b0106080c0705011a01 72
    0x140d450311300e41c9100362400136402441c007080904242d40c1e220496585d800c0292628031009240c8400114520f1720807024010078000582c50704004039140c1400360100741301d4062600306100340e454000900000c94226041c081c08545808010706240d2803000f03054110b0081c1005407440d1619164482e08a0b6008210035169480240c215106c20043e26a00380201400136400411090f019602e0201c0156140c40214030105a00c50f02da030b0304007001005d4466040541c2020407000c10f8036030140803151701c51103a04030600c465100814020403e109140a01e42800000242c8804104007006800400e500380400c50b40703003110741282e00341d441e1000d22400740003c0c100103021030741000c6800740c0c0c0500b030740c040c0c040441c136420030040001000e401000c00c0d8005c00c0070321003800001b00008402e0011042000011b0741ca50401400404030003444101900980d000c11841000940c040c9045044583d00d29040d6515155805a00c50754494400040e11560800d1041041c81c40c40e4615819500c030242c89 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 469109748 1250 469108498 469108513
    0xf040807060c021e1615120906140f192a0e03010c14090f03030708160b060f1008072615090c07031407021c0501050703110703140d020a11 61
    0x9104e9554050b170901c25400b5280d1007400c100340c1300605d030880030b903000c2c41c10300086080c00d10340c10b81d040303c1e48150140e03803c607140d81108031049000807100e5041500d0400b03043c05403518169460303449076620132030700407030780c0d01c20240d0309002441c0d030314031200346880c20f0f403841c41c0b2440e2030001c00c2007606594452081d40303402186180c850203120034a00b1050580d0240c0d0911303894204000041c00b001032a1a0140420021080056000c0000342910743d094510311420100f6418901c104600042a01d03014540e0014445440d90352a01c911444010a1610041a40d40d084044800c5107840403855065042124a0204408075900c107134400c0d00c5104550b8610220a010041740840a442e002c190032020000c0c90b01284c4100003450302020181d41c104c0c609959035002c1151003200d0001c490002500e0340c0c410080101c04e008454011659250a11148511700e501e40b002d8815140c0007014440070050a101e40c4500c00300361020094110b0b8210748815030540e016042401c5101700e2800c0303005402 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 469110998 1250 469109748 469109803
    0xd050a020313110406080105090a17070c05060d06091805061e040f0302030903060412081f05040b040e06070309050f2b120603030504140111060f040807060c02 70
    0x4252031090b01d1a28482c2d40d42581600c07418865801040e40341d410544030075011402203030074080e01d40211383c0301005008400031410129405503104d841201c01d10000c114110103e144408403405070f890403240303e6529000302351448000c00003030303110070380580c00d00e002403240da611480c105030082d00510a481980c7d0703498040502c0f036aa100b0350b01080001c8031010a0115a55008000d0598881d00440e8949100c00000901e03112007102e04644070030000c0c408800342d661000b1115000112920208100b2003101030a041000e018042d031809a0341c0e642c5021090782d503542041c11450a02c00c1607504904011b00010040c0240d910180d882d4401c40d108503810b03a2000031920303942252f00304240507040807020307601c0d084203002c00c0312020841481c001e04a04603a5220f5500114440c1d21090303a1140b508000c08459040443c289051008a10301d0662008001c00e60300d901044080090001d580e0300d1400e00924020700d00040d182520703045108100d10317000255140383c0ca81000c8243c62140021 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 469112248 1250 469110998 469111001
    0xe16031b0b030606031b0d0e0d03391713110108090a060c09031a01030302010e01060807090f06031b0f23040b0321030a151a0f0f0309030d050a 63
    0x141d603a21341105040000440d030b40346031000340208600003005c052034400041d0346078003610000444452a034202e00c1090291540600c6a003074001040f89030740d0131211090140d5104500e0014000c181e10382a00b1402d4003151041401000850080c04052124100540d0b040c680603c0c1540440d055000d44040110320b600803407450b407061030b2140c02000321540326034070203018181d50705a00d0148801054040002000c404550102011480203c00151b1550500a0a6032040f660203005645028024804160003003101002d43c1ca107210041401c40c4c04040040003000780394000f07044105401108998541e0f01481d41d81115204100d40800d96254000c0360b000d04546005400041e8030007101c26118105500001c9141c0001415548010800a003407001001c40e0301411a501800000b0040341004038402c000300b81c1043da82940c509800c2c4021000d43c205424002589240b01042450740c41c18510211303a85030810002c0b80b13441e802c1c400b004035969001031580c54a2a0b0402000070140b090a = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 469113498 1250 469112248 469112251
    0x4030507030602070f14010c030f0506210c100f02010b0117040b040f15020a11060103170309070906060503060f0d02300303042a08030901030e16031b0b03 68
    0x858054404207185a90b00c1000390700c4080b04079440481e16a01034045524010420080d1841000201c0d888648803c02022100001c0d12036a1042c6050140202a100c00c01300001c00115940c01c10341d114000130440d45010303c401c180d6540141c045e030b08029096400303c141000c801e6103800034410100440019154900089842c103980c401c6000001c003c1130740c50310316a400c603000c2c0308861144241602c800c240b150070205d441511940024400340c4499003d00b0728000700b6002006006035504641c0c40550303080e410300c080c045501c4041301044041200b03001160043c01d0780081003026503926400074110781c0041340d0042c030070180344058084500b8085200505158020590140081c030044854000c0500c09070300351002980e00b14211a0340001c1008501a5001d483d1243d06a100c100020710148601058400c0395100c0714020803a40328004161500d02c1c800f400c01159070400c50824518010b400c4550b542e40c500640d00c0002400f525140c0055115040c0f16100212912940c1a45142c8070 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 469114748 1250 469113498 469113503
    0x81e01020c061302060705060a0203090f0a0b06010c051906060e07210c0e0a0b1e0f12060f0303121503030c100203040809060a0f0e0f0f0f010210111902030403 70
    0x1107440040d810350a0f0070580380c0007500c001c1042e42800d90076298140b400c1c03004c850902c0655070000600c10315420803c0307825a20030300c40f002003000354800e5035015442d0354050000b60501940c290000c1c1013003418080103185000d13040c0c40c0c1c00581e10038100000500007501c80d510081d003000e80800d2500c0e1080c070814040c10007220a40c03406440c140030070303001001782c0d0082104200c029000168240c1d25440480d00138600404003949a005d10714012502ea85c49080c101c5120404000d80300f51400700a081ea4407411f00904110110351341c020224550040b003030f0302c86a05000000c0d00d607a01c118034800c0c06000c6c2280702d403244600030181042c56a079101d050000c1000790300000c03904070269000d40066034441d01c910340351800e055103035001c500150860341900c00070900019040540b10351201990307000340e400b212044000070302030000c41c000c2c015822590380562501b035040c0c44107034020080480c0c00207100e58104084021008450100c2c1c00c44d850041c400100740e030740440d207240300105031400c0c5d98 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 469115998 1250 469114748 469114753
    0xc1d0906090a0b030d05070b010603090b13020a03172107050f13090903081e040b01050609010315090b13020a050301060c03180b0306091b0307110c0901081e01020c 72
    0x8a400003045144280101105036954890800c020039440c10301c50710500a00e031b5240c0d640c0315290361421440c400816000307002090301d00b15840c0041030702c003141c0d1500400e28410543d080d608500201e1502c14090700040d08c5444480b113002e1003401c4000c010710001c0c05600060704a4014071100c04020b080650744200002c43c18020202400c003108010814214003800800036641e807003040000ba1045a0340603804150203004002d910b0600c10700d540050011500c42d40310301d1601c0d035100300c16642c040c00394500950010502c103d459001c0d5002100c4940c003540a0641680e035014141d0190408004c80d034084c01c06918001944405802a2110029a6118030f400c5a08115045800421240c0c040c0c0c01c2140491810000d50845c1c0b1000e0050f00e9155031495492816405020700300700007806480c800540390700340031640d840540075281c010f400c6140c001c1c44948540744151070100c10701040c5501189200000412003000240320300496079484101c1e60030328421003c14201d0085450101054 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 469117248 1250 469115998 469116001
    0x30213020901020c0a0f031a09100207061401080c0f0301052203140a09052b03081302040612030818061b120916080307080708030a0905030d0c1d09 65
    0x1014580c025040001062048650b00c0040c000001c1d6004ea8a40c031241c82203c04140610500c4500c2c408441d60b540000b2010700507082c441c890656402204001c81c00540d404a0f18000f007100a07040b1940c500f1034030f2000c5215503103940b1101e0319010380c3c101061042c0108641451340d0304040c0070f4244119481200403103083c1981c10031103481c2102e42e1003101000070384044201100d691101802c6840b200391740d01101e00341880140f00540400f82e4417500400d44044c60400e24001011580307108a616181c0140141c550b14a100c40c01c010915000358820b05101010401600030022198030500940e120b01d60740d284d10803017400210a003a54610310b504001d00080381c090028040700700040140c0e8482e072401c40c0300b201c1c0552000042c2e807a65040d4100740042d01d003008040c2c4540e0060312100740a18a0844503981e507034400d110b9000014182200840007440401c01035000b43c120a400c20b056999807110040e20900802c0d900d02c503200480c41d04165842e00402b049a04540c841e805000400103 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 469118498 1250 469117248 469117279
    0x50901060b0919210309050a0302092e08060901050109020306060301350606030d080c040e15030106030c06090e070f0c060b190603140c0304030c060608060c0301031b0302 75
    0x12802c2414501c49030003401c0000158070f05442d19191424002030710300c060441100c5c5001400e03465030754401441000003020502c05641c42a4030300e500800f00760714070b0080012004200d00312a032090569034244610190001e0403050201d11103101d2103000008000b03c1c0e898203c010b08a000540e800744e008a020300060019117840c0b42c0c0e1440590b815154580c4d00c0c03464882c0e480380180e032140d410415070450418014282010080003005207858140346405103010f42103a000750150344617102e28440740740d010074868500c0e01c0c815100050302800030300c80140c60381001c6840c000103204a00004200700b200090490990a001e0b0103087c3c10383e0f618603102403a100486031303082c40d6001a03d600b0782d41c003c4954265241e42032981d034200c02c03158405c80e01b49040030141c211071001c4914500b801e10340d400c00901044000480741d02690500f02125885d0035800c0c50401011a500300f1045071044009000300e00300d88202a40c102c920170307040121554242c1c09005c421586901c00290043d0880250702070 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 469119748 1250 469118498 469118509
    0x70503070b09010f05241002061501050409060311090121120513150f0305090613290a0b040903080a020913061707080d0e0103020d0e0d0e04050901060b09 68
    0x204042042e00110f520380c3c1c0104403008681080d21550544c003121745100c2c00301784281800c4a0890b0b004c40300314100e480c511030702a4991a00410188001c10440d0000b1201d82c020020b0f01c015010010741009259202d1802000b0405040a0548501207440001980e83e0a109104c10010620071101e5000d1030190303203074035050b010b0b03402d8501400300901c14800c0044c502c0d02c91000500003c0c00c068800340040201400d00c41100c3c1b200c40c101410001080252200000c1154003d0303a20301b400342d5402c6460411441c100c144c241200004403242050841a03e44003400314003031000c20030204405814501084102e940c00040100426600400101d111b440d542c042c1a03034900162003140e900700d40301110300803aa4140c0000c003085061008080700080100310210261221400500d858141400003034440c40415000504050700061f10034100030b92034003d102d600243e6003c6800405030101d018001d05140350b010b45c01a0301d4980050601d0030140580411115000112461310307005605100 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 469120998 1250 469119748 469119751
    0x5060306160e0a031b030204060504090503070807080c03040e091c021b01050f0403060f0b0405061806010903021507030225030206090607241103071403040501090213140c070503070b 80
    0x140e1043e00303d10008045060b04400070070b8402282c07951404581548100310441e0055000980954542158440010000004c6031182600072805588a040d28079201e080f91107541540e180e02e0102050009607180014000e901480240c07094601006296030090043c00b41010a0001a400007204980c0d0302c3d6101c40c5035900c0001858003d1a02001e12002e58070f03903201e40d104031101c5d580c0702030040941c11303248141203109200300c4041c0040c0c180603000824201058210040a95645021a160380c0c041c0d2407440c01140d029105100481c0743c0b04c1001080d4200c00c400341d001d8007440c1411010301c454820303484400d050621500780000d00315004e0003c40d421901c000381d000902000000f000c036003450001d15041c1300c010701d4441d1140c0840700942c10346202c0c0064080c4907a00340140b000060308443c01c1402d001010000e60740700e0340c50707040c844e000d418801006034204025418891101f445604850001c211503600503403d038030f5416201080380302d40c40307000d00700d50001d00640c000580c07143c02c6135 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 469122248 1250 469120998 469121027
    0x2d090117151203090405160807081305011404030e190b0d020d02040b07120903030c030305040213090b2706071103041a0702040c1803110d0506090705040506030616 72
    0x40700c0c40800704011a500d011000d604240d607500106580c401860540100d0341d000c2e1840400010a445e8500d000c1e04607240540300310706003e40d0304002011072000c01600100150008000d10001ca086007050101460680c2c0c00d0300090441c2414000604060060280003040c0300321440032689009403003400c940001003011005502042500361030615400a040604004d2070384c16960706003840c05000c810245904203007486040c0c1d4040022036005118806895018203002c00c5d907542d24800940042600c0400d106540c4c540160003003402140c03180e2034444d1003904d005499000135005002a1041c420500b06140d03804480006d00c901e105170218074001c41d00e0800c6904040d250101100403880865401140120115130b04003503183c035004602d20101c2d0b60400c032240300e45070400411050340da0b0001400601e045c1102d000e10351981d040d503c05554000e4213981840c01c2010109403119a103118a40c03080d802c02d00816010315000c54400c2c0100c090b02e904482045890005039034034040f9550f00c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 469123498 1250 469122248 469122271
    0x705120c03061c0b0106080702370b0406050423070b09010e090103050a02130506010c170c031b010f0b01050715090f030201020a0201050117030702060f0706022d090117 74
    0x60f400c5061110071141100d61007035000030520746c1410307001408404018040d000b154000c0b02d01c0f0b40e01c2408200e0344201e481800c40c8469410f0300c0810244900440d0180013084490070404000a1140740c3d8445402248070301c01c5051041c5d80d1720394004c0c400078004550f0540f03820280b002c1140c5102403004200c412411305001490880d044005182d4039000da0083e50203801c8540c2150031450009a6000ba401454200700f05904104000800c0c01c0340320300c002803481090300c61901c000d1444a096401030364110041700d40e92038103203164111040e02c0c0a01c2001a40c00d060b12103103a14000d0007103484d44031040e907849041c044a83c4501a41c0454480d41600155480d0011400310340078960f80081e06000e90000f603900e0b04034501c02800c460781644844025903100c1c1140345100c030080201c449168049810980b1a803010a0101c0d81d88240c96005004074400124035004007400d00c800c0c807201d21352000e00c501c1411021b603c0016481060071081c00501c40000c0380d11815010b180d40d54100441204 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 469124748 1250 469123498 469123519
    0x191206050307060c05060603030a0f20030a0908010b0d030507170c03030103060c020c0121020c011d0109030210050c040b0c1c05030105040c09031502250f0b0705120c0306 75
    0x72a040100540006000a9203040c0e10700034410708210b01c0d41c2095041d0010b501d07041c00703020000e11850481071010100034104500d60340c801202071404503483c1089082d81e0340d629100310040d0990006108403c615400c1c03200d852058688110b040c8205609038584510b41601c2d5921180407115030103242d40301000038020121459010009035020314414180010b070540e00000c06468048007000b0581000006c200d6614800701c3c10155104200d4092800344e00c0310351903040d81c0d003d000c00c4030880e044020300072980204008150040401603011b80c003501c2c610580e1580c00010764000320b48100c00d40d68204801c0043d110801e0080c83c043c21803006841000c0e0003907a50350001c1c200c03480c070100002c0c00400144074038900f600c151548520701c0c0c2404039110f8510b50b11b050038090200d07241c0780380c82d0340400d000024120003080d00d81006c0580784a942c02480b140390840c11100e070700d441919074035030314400500d51030300074801c40b048034004401902441d03640c1e00c4401d045170704c02844c0e986c00104450 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 469125998 1250 469124748 469124759
    0x150915030b010905150603060a0501030e0708010525110a030f030e19020f1c0210140d0218010306051c0507090e150f131202030906030114011103191206 67
    0x5040d80d019150b0050301113a07070305042d40780f00150b03005808101c1c8140d0742081400310769660340c43c1642c1120360a0802082150410402c5070400c0900d5004440e1035081070b04002d0386400300c00491b100f4001018222210311000c510407942d540c0b2032000704809512040c00c10300464000c511140f050a210b00e0042905940011000e003400d000008002d401104058004110301c0c00c044015440842038503810b80720b80d411808200548000304011380940f148403200b142c0103102e0f40350350b15141c0010316034555034009a41c21200030340c040300500a00c0c8804624080d0590b00c240500011910010138418002d60802a1a190840c0450041311184507151001507111080e0040ca52061050000b5041c1c01040c5a21010000001400010b0840d0791008020340e03103446441a108554104002c0030301c040c0315282c26407540c469402c44079803100c004400000e0319140740301e203030019030000c0c0c2e03c4510950401d01140c0da01d02403480f501070107000c80c4102c652006d1182510b038051031140080410919030b80ca = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 469127248 1250 469125998 469126013
    0x1014100806040f1b060507020f060316030e030706020c1623060d060807121a040209130305072301200a0e0303070f060e16031a07120c020c0307080115091503 69
    0x40d880071700410000b144050540c6031450801c0a41e000070b81c0c2e86455407034071000d14000703440c4121a24041c1940c0d111811042e05041007512045c070741c050421961110a00c0c0c0c110380da12481c99130542e001518400c046415000403000c2c461140c035003100748203019814010400250080402916091f40e10580011801d03800c00082e801401109001000e0481508003210010841400ea41d40b01c06601c040c00016180d0041d0f60f0b602015a0505020721166841c0031610781c070451030007422400c2048401e02c0358107000307100d0141e4070002038020480c3c0d0142c42900c20701340505142c480131240f800d21440308018000e101c40d4040c0c02c0d00805136854040032340e0341c113031a01c54400400d41c0c21a80d00c1c010307554814000c00c940c4120080042c1c502c0e13001482c41d03942d615004003245401c0c1c00403000d0f60220f0003603030150100d014401900f540a01901d0340f00b000c0290782d080e00e030210714441c0c4a601c01c00103e90906100d030b80307922080e040e448084141001c80000180140c1c02451a141a2218002002c111074 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 469128498 1250 469127248 469127303
    0x35090d0210120c20060112030e01050c1501170a0f120c0807080315060316030225060f06120308040605060117011401120c1d121014100806040f 63
    0x141d29448040c0c10f0708013404101405503448080a07070712410060000703058040703442d103545602d850400d8007e04003000480c1c1320300950740086541d204207040303001d114560f15503050613500e1140404030302c10740b9000d8443d82c800c0382910141c13041c1009080d0300040344850003803290003295400c1417a10002c00b941c4202c0654008141511009808000d0001e8030200e5906405000f104032203290450a01001110300c1914104084044c541d0008140d6001001b22140c0314414210007140200d00745c0500348800909450380030406154940b80307000c1900100b2500240e10341d0b8140da13610320349030b48507a0b4410043ca000b40142c1e05100701c0e040f44e00c0040503d80c035164003800c240009525010050701c000f40c506c41c00700010005c41420f20312640041a4002c5400ca80c8610500302d00c0750052aa0000c01c84052940d0303c455400e005585814070034019580008000d1a00515001001d5031004140b01c0d00c10854041d4000c607800c0751000c01c2c013117103440360651410f6000f888140660f9203000c04581040c0c1c807 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 469129748 1250 469128498 469128521
    0x703181503021c0504050709050a1508030a11031305120106030219030302120316030b2d0906041b110111030f0106080a1a0d080735090d021012 63
    0x300050000344006000d080c006072030303e48010a0040d424140d482a0f21580c084c042d2806a65582001910105460b0050014506504203440c0c403151505611030300c0c1d0740650210030214282c00c800c107a00d01000000c68802c1c1c00a030186800d040d040000f00081007803482e02c0000d00703640302d04001c000f584c2c50344101c1d409042500070b840007407440d602d0041c4c2003070108502c881004a080c400c22140c5491490300f20700da4a4a072400044018080b000100c0d03502c10400194002c81180c4540700d000e04d80b02c1181003e51f141100d80300b055580700010030054411003419004030103190050060a10f0044802d0314010703200d07000102d0811120361000c1915003040320b20441c0012200c004015064202030704a4000c0700011040c000e590721152881d20881070074072024040c810001a030014080e107501540c0c6156400289505080c0b014120201011020302e1a800000c0310381d10020800c1c1c0000c41281da50300d10190090213429440d03020008859031a100ca1014420421040441500180b00e40c209802 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 469130998 1250 469129748 469129751
    0x5130e06010f030314302208120415020d0204060306060c050a1b080703120206070f0801060c021c051506010507020a0e0a0912030b010f0806060703181503 68
    0x2190111100d240c108103900c412081000400c1c144086907004d03444c402c0c100c60540600b55545400700700c2c4003249452205540317545800302c8039403040b2035807107298500603000d96001140d0f082c0c410501421038610038200400305201000004441e40d07e0b0020160b00500030900104ca103180c8881c2c1600b40e80c0510221000301c0d0380080e041c0701e01505485610302901e100d1804001041043c1c0c2e4440e95100e000c4000b81800c500303880501340c4981c048602102500030b05042d106025500d2030020400004d2240c0c5d140540541030004003414850031038150f261041780c1d502801e903403811400742c0302200104c5050741c100c142d00c582c20403802182407007403030f1052056004143e551540081c0400c0540043c0c89141000f008000c00340169440500e9207054030941da20401c010b03100c1c0c514050090125203c0101000000c04400c46001d80607401411005802e0700c402044040072102103907002000c032442640807005004d480c021138425898056035202d60802d040e0307901d0301c804040d04841c02c0f614080c0c0c0001d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 469132248 1250 469130998 469131011
    0x7030c0302070e01052107120309080c1206070809070b1902010f050c07030e1305011511061b03041b08010c1b02090f130c030803010303030510061202090102070513 72
    0x1541c104012001860120014202d9504050020b205103070322a92001001c0920400001100c405100c43c00c000e003107e0b00c4180543c244ea2801400c3c8002d1751260180c1030044010807841420060009460120120054510381d59200c1090320710446c040c1000c00789214240000c02c00703001d1000101a07402030070091000458920b10001e094881c0c581d8026202e0b8107003014003403402c00b54070035240d03d2a07160600907502500b20000c616040070580c1c44c2c0e001c0c03c9c00c24000091030700135601120f48248055680031514100103491660350342c4160740c0c1c03003010200c100d00e40400d44043c0d1b01840e00039101d88014445580845c403006115106c0e0303040401640d6494601d080c5044e0841c0712045c0300001011820901412500024401100180103c0200101c540043e9411400000070385038a54480f8006d00e00f56181c0c202046250801d000840c0400c1c44d10f804121080b500c034120354110351850b500c46620048030b544142c0039421038403510b8150311540402051640e2000d07040400b035000d466000a59 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 469133498 1250 469132248 469132253
    0x308040e10050a0b07031704060902010f1b35040906050a03050606060f120108060a0c111c0201020f0d0906061205030f18040e060906150a120305040b07030c 69
    0x41a402038038441c00c1d049841c1c8100010b480b0041c1180c100e0311400d0030b407521a80c003410151044c0002410640c500848013080108200040d40100382c00380c001c0c0c0e10020441410b508c00d54084244089c00c0e1081c4500040460009542c0d00300c45001c0403040460425005103c0e070b0314145c4100308645035182c9a8042401d10640c43c15109040040c038085440b410401e1039510340c282c81d1300000c0c04407400340c10009603045022a682003103a5070700c1580381d84001c01c1e6a403802c0c1c40e62104070589808000509040c00851540e10554115850b14942400303000141c00c601104078911141507502001d65400340401058040040d02034003074181c281201003000340051034907a045800a81004084400c650420004601d000003900d2111414580441c1e0b502e0000d00d00b042c840b6040055154094282514004100c401042c010b000344805001c40307085441d4170510100b030014043c241ca82000e0650f1040089071109014402014001c0c1821881c10b0f80301c401c0c03541c1035440070324160049240d1034090400c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 469134748 1250 469133498 469133519
    0x11030a0207090e0d080a0c0504050d140106060503160305071b061a0a030b0117011508011a060412170c06010b030907080106180e10060609080601090203010602030306100c050304030804 81
    0x1101183d01c014101140c840300d0301528820000d07084c902c5c640d03a1032001c041c006000794220b070b020300b03001040311100583c207141650280c007031060030b01c5403542400c0c40000c0f80ba004400703490041206017495800214503800880090000030301c50790800c04038444804548c5202d5581c11141c0e4000c1602142c20381c0c002030b9900c92012a043e0b03480c000c0e42200c9003040401c243e50550360545030340350400c50141035903074070701030250184201c01d00900b10300110010780c0c2201503000c00000b890100a0f000e502007114108101c50286116188445da6201050b5000138007003c0003603c1da00e07916640d03030706101040c5801c4d1319000098104542025002040c000902c03410401c810003400d500c002402120708114900300200b010b1302e003054506480e6000c80700e550100f40426021130050038010065980c0d98440140701e04984c0c450024640036010000c80c1d90000c0b030085a043c0c1d40da940080d451500c0d104240100c508e04516000100b0800420141c00160203200400c001c600904074aa120350610b180c419 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 469135998 1250 469134748 469134761
    0xf12070807080d0504060f0207030206030717060a03050714061e04031a2502030c1006090e0115052e0e0406120510020307020304080604120e220c11030a020709 70
    0x11070760b1000100d1201544d0013001c0b45c0650380b243c0340c020f1192040c014140c1c900792082c1c0009501c51004401c02403199401056480390300044188520701d40c44130010f10102c2c0089000152103034100180a1200c11080e070405140e800010b08564504800400c50907035284281210000040d0000340800c00e00401d5481c418038183c00c04914206030400c0040e0310011110b5004e41402002025034200800c0d00034800d85102d08814010760b81041d80d0b01c3c1c80385c40140315500070081e12a260110045112005118003403400068500001c01903040004200010302010461032900b51100700d807042401503240e8610301c60503685c656020500c01c000c100700c00c1c1c450319000403450107090211071000c90800543c188200a09030001a940c0e1209a0104d0852045410141e100d215403070a0104012900041d121400c0700c56a8059282814104210b00ca0300321001d500d0a510a0708080011000558400c800090f0b02d03090a00b450034410030a1130854000c0b0f400b603c090b0304030b15000c120950042c00b40a = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 469137248 1250 469135998 469136009
    0x90f060b0f04060e060912010c090f0803120603011e150b0c03070228030f120201050601022104150804020f010806010507060905190c0314160b07020f12070807 70
    0x14200701e4180400001c1e8040c9204080c02c0152522200d0040d89900040740d0390b410002d80910560305914030410301130152240b03240d00041c452400080c0c11444031004605449900d40618a042c02800081400c40d9000d0900c6034103568035014880065607501c0e0a000c2c071580d0090101d484400e00d141801401c019500141c00e00004105d8041000e0001c000c5444060341100c100790303881030a0080d406401e5521812410503070602d1008828001410303603141d0664411070402880c941c21144c200e003a50070595005026a2010050801080c581c0840c41108100d610019041c141e607075444019009401c491540801c4064041c8419411301d040d44c0c032035180003800c2c024110b0600d600028664443c0a0b005400c0f40d503035580361002c201e03003400301ea00c800881e134820807806141803c056402844500c812100300300242132203000b88001080003500450036088002d462403400c40c02c81d02030b5211520499101c14458922244c4d42c0c0e503482d040c0301e4a007207040186110781c18603c0344c7e031a010254201 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 469138498 1250 469137248 469137269
    0x5100e07062c040e0c030c030313060f18090509010e06040b060f0609040c0f0215040c03150b040603030905011107030b04141c05210907030b1005030304090f06 70
    0x5208068100e9a040790101402d10020300b000c1d600100044001c888040d03560303200d0305040c2c09001000c80054241403454044007520012611a01003581d079104a07400034140b0f1030a5201007001c40d00a000c00c41256070b85081541c94071f040c00310190040c035250307007061021686d0344060220246007441080c01200d01c8100904032420140c65841c03509000070151841103808039015401d907100c030340aa0b1321003240a80140f25840000030040c009890b48680400188a501144403003143d440e038506000360b40101c10100520708580307505110f6490588500946500d9000048494880740308241c002e43c007a03a6080300d00d0741480001440c0440000350940c43c5c0e40301030303030a0000c036480c002c0030340e08660b21400352a500514110382c182800d40c65001508010318800141506030341040040020114030f41d00007050004515981029a209a640881c2a07210500034400951b01c0c2203c2e0b6001000c0001800c1401d07540c400203031865025801040740a902c4190380a074101450282c0d00290080399030 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 469139748 1250 469138498 469138513
    0x14011b090512060604150812071103030f03040b1005030a1109010f051c02030f060117100e0312040219080a0512030c0d0902130f0207050d0201151a0c060405100e 71
    0x20b100355100006012076104668501485205030300e4114a240140350807015100c0481d41c0389050b550a40200c54199241044441c07070032454640401226040c002c0e504000d41180c481e5141d001d80c0c0a0018111250188058004102907604020341301074140300b05a00e002d00700c030400c04d01c92540c40690251652141c00c000c14401655800000d20400c07090041086a031181400044c1ca4014001d80d008510300a0030300114121f00da20100640c40f0184c14226072807826082e1785402121030006907007140f0b4005000261010607039898075500b160004009807256001410615a4544140d100240b03d034002c1c5210402c210382403048440c10012403940381e0441c84d00101c840b083e8800c0c1454401c50325a509950411585c0e41b00b03821036582b0307000004111501744880038200960004900355898411310501441c0c82c0d00c14000c00400e11030180140780190f2404440d04000285074011203160002404610b805030404c21806116a0045c0001c18110541d800140c04849445009107060f030080e10 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 469140998 1250 469139748 469139779
    0x21c020d0503090a1b031109010308030c2b0e070906080d0f032a03050a060b09041104030f030c14030901090b0a020f010e031e0414040914011b0905 65
    0x4010a0320011800c1c890390b207a64244555041c0038040328000d01c040c05948074640c4801c5440300ca0000e407032003440300303400300b80f022801c01110040c00d12000709543c1080000400454414014109000d01e031401d401c42c0001e100d903000400c1a1910540540c25514025a840e203002040302e100200b11311542003141504260045417a640004011418800039401040040c0d21a034800d00406052081c00020612040c03050b032800081300601e180007030700301008a07490003414840d400844210700d140d24601036068003480b01a108201d400d0705403030824000000400d18168845d0b603010311075030300c030b401c150403034078101c0040c01b030f4003414560300c0c0d10510104449903080390840047d030356110300c119124a5440d100b00d20382540e207080070059500701051a4100c04002010f41141060a4070302c01800c01c0302e00d40d0f2410740c0a203120740321314041d0620b4000480e05080e800014414040d004140644441520b81400d5174101040c2c21070480d69889003a10a952201c2c20501811003164100034440072740 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 469142248 1250 469140998 469141003
    0x110906090906120601120204051f051e0306011418010b0708070c080313030b09030705103201031e080306011107120b15010e10030c0309170a021c02 65
    0x1021680100716180200d105030b81c0c0c4800c0508603200380c070308070380e842d40c1c4508450900d540c900404030b001e00e080002040652814400c1c4141c0e80300b08503803500d00b44c1c0c981b00c1042115440405001d146013040c412a803500d80301400350360701828903040d10608151a00c82808014450a20504000d289002c010700524650001f16a5181e400c844955160700d42800c10351031094859128000c0e40c80002040d6011745c0c1843d00c4034044900500541c1e00c070b80d6030301c0f03105500d03880707002c000401e036800001c05145241c044ea40080c00d04405052004242c214841c0d921440c207070754200700d0000b1038100004104000c2280030190150b1007451007261491055690b410b41c501001c0c0099051050b00d51703840400000c10800f620007400e600d40c86c2040d0510b50300380034208000568141503a81081252032074a54004e088140140340c0c05032480089a030b107c0c004400802100510b03004050b00c40b03203580041440440ca1045101801c08655a99413400f540079107040c4891449913520031520442c1d00415402 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 469143498 1250 469142248 469142257
    0x90803031803040f0e0a06051c0204020d0e032205010509011209030c15060f1205060424023f01090903050c030310030210020105090d0f030e01050c0904110906 70
    0x300a100121a5140030032103040d0b010325081340e4260450341c10700203040091450b405000c0d008460f420000075480e038040c800300000070084918500b81c4c03041803100506065004040d001d481000000300c682e4542e02c01800c0d80d000500400c0840d5030321007000e038140c0700602c0000c0104001d090161801d03000800290609100301ca100e81d40e696140d90f91030506014000700741e180e40d40160b400b1a05401c1c0e2007050000d200900035440b141648440108910b9405c84501c420385801200a0000d651150b845071003c54a404030a40036040200d413181c2603010600240c14448000c1000c0c616001032501c0c14082604080070b22000982d00c606d641c1e200075950312006041d22041c0e00c0c0480c000c0d0072410166524420451404a148000802c0081c050720810606007a20300c00c4400c43c203051002c600403800c0e01c8040d1030180337594001e44560010207005a01c4100e800e8260300340840c078a001d0300d203803a0860394225860714030306000060754400c501d0306200d07042050500e019524200700c0100c012a003180038 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 469144748 1250 469143498 469143511
    0x204050103053a0e01020a0501050109020c070f080c101707020114060d02150904060509010314011404030206061e100f1e02070306020a17150f01030c17360d09080303 73
    0x12142c500d130718580d20901400382c80f50b0f004802840b180d650351804500070b5100402c0440140200d0f400031410303200c2c0400200031210755500820f800107810040100039906000140107109030320801c03801c015592045180b0400f41e58000040c6564206501030020a0080800b8031565035080814016279a81c2c640281034400301c0302643e141c204803c00305000f090950070160b0700140000000040140700310f0301c40d04241000c0b00078410242c0c0c48007114264041958001c015801040003c2c0c800d041c000b801c803081d241d143c00e140c182c90400320f010900920380300043d4000551080c2108925513001940c030702d50800c110310401c04105a9070fa0003900c03950103010050003560005090f280c0c4070301c01c1d02040c203410309400b850080c1c1d0030034240c080061400030304035034010100e50041c2c5c146036000e40308041d034401d02903d41c126241885106941300d038900a142c14031218940381d007800c008940310005060003403241d14141c038168580c91500e2500c207404400f00204103500c2c43c00d1081c20004010f0300c4c0c0081 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 469145998 1250 469144748 469144757
    0x6070c0f061a130213080a03120e0c04020c210a021b0301091a0f0f06060a030c020a0c080106030c0e09031603020a15060303030f0903020c120a0204050103053a 70
    0x61040882c940842c00310010190b10040070a00301020ba00c1c141e00901007803030032001031400140d40d504c00c151920300120000d80480d042d0141c44050150940001c0d5041500e01c003a80d2243c0200c00000c0c040741c10900f802c50260b4010b5203180301201d640c88450301c00c211141c0c2014100350750380d440250b0340d219481106817800e10707069045080307071802d40240e04029803000c650303d500030905071007078034110f02111080e6841948202141640c001909c406020342005410989400c40c0d05d4030a40203000700c90315140071441451100008a00c80b12a014068040c0724008902c1c41d156041c0504504850f4100c2146240420701b4082d94a9000048030f803241c081c40c02a6441c04803e0405034104201c456000d4030000500280c0d160f000c815034480c005803032081d2000c001c001400c8400c40d0860f032280d40000d015130710034014480d00d8138180c120680c0100260040320044400790340400c0a80c0c84c281e0045882e0340c01070140b84402148101095013100038000310401d50340032102c184072900e02c007520035424031 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 469147248 1250 469145998 469146011
    0xb06130921030902100c0c06050304020d08090112050c0d0f02090901030224040603140106020f060708100302060d05010312110615060d020310232d030a110306070c0f06 74
    0x42c02a0081c014041d0001d0080e10305815040010b4a02c94441904550000700d10801241d150700920a0301c0c00359402500007041d21015a641c0d0903c1c0c3c0c03003481580c2c10f001d2144401c400b9035041d0300509104010700e100303050f00e5060a110401c141d50a00c03500c0308500e070051254041a85408003003071304407a01100c00300e84a0320301c18800d6107116540c000740740190720006808030300359070180c0011101c13403103030a1440b515a0343e50344101d03102c21031545d060040740c01c0301000c1602c0341d21a540ca43e07003000c08941c0ca04000d544d6680011000d6002800c010301c5184c4075001041880000d10650306c0401e06400c00103440702140032025260f00c4000c040c103980032000501042103480b0802540e07100800000e0455580c208181245c00c008128401c0d0504040c40120000143c0c914100c0445280d8000d444000c00100c42c1010800300d0841da6149a94840ca01c20415441e0341d040281d88007684c054000400c09103e14010b0600b0002e000f0804000c0c0990114241c0009d04151100070388542c012100040d003 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 469148498 1250 469147248 469147313
    0x306050f0307120b10030b10030b100b0d0e0106080703031d0a03170703020c0a1e06050c03090f0d0f150f1104050105090406030b01140103061406091306120b061309 72
    0x20360845e04042c050030007c0d810403400108254064040d0703402036400071400d40e90510b0150f00031200b0b0103411500718091003840384001080d000ac814814103040041038603511000042c0c1b8103007050f4400c0d8001480020100c84e60007c00400400941003682c42c103602a003982c8075242044488650f400c60540c000070400c003854070034865a010807500500740c3e040542e075003481111024000f20b010300790050708900068498000c4040301d41c2c070310448001c6c5090010740d4003005003002d252128aa0001c0b50b0074400e400103008040180c1c0064468856210030a409007201d00442c0c1c035090000e043c8519003032520500c803c1c120103442c2203440900c0c3c10f0742d40e44040000710b4040c11ba20791000300070305000350000c5043e40e1581e28600700341c4001c1c1e90800c015681c6150580e154560075214030b410080810896107141407400134041d801a101e072000c99002d0303541500743c10070384903020107640003080242440300a10303104400b00c0710700401800c1841f000e40f2a4a4014010f040c0e0b0350014000d200b072008a100 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 469149748 1250 469148498 469148521
    0x1f0b010c1e08030a06030b06030a0c12262508041a0c100203160203190804031701080a0614062803020607060203040302070510170717070306050f0307120b 68
    0x107582d901040c0161a03003070007204900074191034041268003140f0540083c1d0242000182c22542d180c01c181403078440fa103480441c915984004c1c205030341c0342c00e1080000e929003011714288100d00c4c8858007120f5940b060401040c1c454520034001e506081c1940801d440031800001c02d64056a0003064007103d42c03030407621000d00600c90003110f01114020b8992000150a199002c1c610400300c1d2038903001d00348101c0004a84900c250301002c0c0e140d40340340b440211414030454501e6072040c400d0138640001441ea11000300d119009a20a002d2540111003040c10420340b4007402ca48800c9500d001031840c1803440005055001892501048101074041210071070002000e5000842d0064085070b554215414407101030b40c42150240d015110f10600002c842c00d110b02c51110790040b5980f4800f0450304258000c0030340381c2c050006010080d00b0102c0d03581107000d020600b0300400b01510300003025032801090110000b079401c001b034481c1c0c0100c01c00300044501106284125544602d00304d01c3c0b81d5800d0704048 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 469150998 1250 469149748 469149803
    0x602030c09100f0905062b0b0306040c084309020c06040c080601050604090b06091f0206010b0a02030a030b120d1211090618040e030a021f0b010c 64
    0x154841c40121940c10700da60044502c64008002d0354444c15a141c03241c05001d0039100700001d00038800e48656091181045440054070f0b9608004004221409550000b03840c0507010b0340d064030105581e0908000d0307000c04010700f0080007000030a500b44080c2c4406c01c0b643e001d00a0603020710400b8004810b07803c4010041011740a001c03030b070b0011501c0e505010200d40ea500800c860464100b904810080340810340055081d040b88d8000301510b14043c20200c3c40400750002482e02904030310180071040c2d140c6d40320342083e2007220707444603c095004805c100007880c0c0601079001130141c007410810129034640c0441100c41c00052400c010032054425804191100c104442001c618000c061920000a82c00014001c185108203010f0203040b000040307808103031041441c5035a0001c400c1200415081040700e52921800c0014000542a1100c04580b42154040005400140c01103149000040150071081c405500852000c11a00b081c07040041c0502a40c104050207031601c1909000480d60030340200d2 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 469152248 1250 469150998 469151017
    0x4270c0302132405030a1712010e091b0f0f01110f03070201090e01060c03120e1e150c0304140313030305090405090d090b03060d0501020f0903010b0d0305070602030c 73
    0xc070741018008010200821540e0f84500c0840320034421843c070541c825203180c064640040160038000340981d554010402c20034005100b40c54280b02c419004400298007900801c032800003c049450320503405400d021a03e981212901401040451152246d2000d00c240180a59604e040701c0d8140c001614945881d080c00d001a1140d10f41ca20304848011003c0c003003680c1300b078950310b22507a03c034031b40a406044240940303000106802c0c1e18101103403144410300035042105100203411b03001050751500302560000d1054000040300c10009007120104010391071021030340c90401c094208500c081c86e6511001d0300180000e00e07000c041c500018001d204680143c0600800812910b5a030314020b041c9030880285144a03600c1c20b400141003d5000c218044209000d660721642242420903400d90f6400141150740c00200f138095050009800348002d0039442c0c03075581c04a0310741d03024100705400e4605170140540104d460b098450006a009070940d005994080310250b125511002c1d80c043c00c3c09091040c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 469153498 1250 469152248 469152259
    0x70302040c020c04061412030a0215100e1e13051209030102130609092d0e0304090603060f0605030a0b0f040615030f05010e0303010b1804020f0c150604270c0302 71
    0x150310046d0410075442483c0541c0e0400003072603103882c03241c0c40303000d51521031000d41c21003000302c981c0d600703003545196100150b40340d0440301c01d41390060501d4480088130f000c02840175000c2c05440c2146800140c6a00c0809807441845401241d56682c1d20b41500b2102000c0341100070940000941d400e4040e80e000b03903c448204001c1d41c0e51042d00030010300f100e104607040140b4081d01c1905044102121455141a442100d8440700546480c48004c003040c00c1c00c1c080f940424400402c0c0203070f02f07000e101c00950050501182003003a1400c483c00b15581e40e4016486a40052030707060006440c0d00c1000ea101c801c83c50115102d0b40c89013090409400508210142984003450100400174040911004035010301c00030080003400d80d9005941e84400e020b101c441d02c105100b2524404c0704020f40600100d0050000741c245811418cd0021603005a80c0c8016550803030110020000074121000b03034095012102407001c56095000030342d10181224a80c3c2d031420102025009100050360020015507001c0d04 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 469154748 1250 469153498 469153511
    0xb22211509051f0c08041509080c010c031802031213050402161b0506031f080f030a08070f080103020d060212160e010804020927030703050406090512070302040c020c04 74
    0x200a074894080c00080008007006142843c3e4144080c1300300342100c0b00f07a880b28641d13a200c3d900c0b810b00a00e91031400700c420a480702d09030000910b03d40050140c0c0c1502c01c00100740400300e80c074082c0584420000080840c1642c5042801507600003551130b44001e00400e02070303901c000c2c0080d6440100d0264004075003050000400000c02e5032840420070110740945610410b0101b69a11140e841c1d81d00d2040540c850740030710102c2d60030701214059200780e42841c14101d00d204c0e90760504034100303001b01b5622080c0740c01c0030230314018154201c0241503000c013162034899140742840700058011201800042c2c0105821040401000b07002ea0490303072180c0c05001902401d20b0040c500c240b0a12420350014002103000901082c01d500840388207010325801000e207d01039903a9080b10200c008401c0070910080385042140200343d03c03d00040000d14081d56608cd135480c100903010b45443c070207504ca64080d40050200b84003054001c030300703003003525070440d0f0101c1d100400c1e210480c90603c00c4036030f00764418034102 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 469155998 1250 469154748 469154753
    0x1050d060602060402010905190e0712150504050717010303051c02120405071a0924040603051005010f020a0f06020d0212040203010c0809070905071202040b22211509 73
    0x100107124a200360390310706447e5240d4061048a405000145565404440c0203024805036410340301c0d0312903254500711411210754800ca406036141400c0c00020103905110a0159080c14002c85511507680d05101e5040154020b0301d2002c010b052102a0421401007042c42c120303003000c1d00902c000c030350180c41503446039010042c03160041c0c0262804c407058810000b000841d06440c02c038241c0d070441c0405001e81448600820301c81c030601e00c0c405006140001c02e00c91b0010b186444054800f800d82070b0f034001020b00c0c041621204000e89600003d040c0603201c503100f035119030300042c8560300a80c44414800480c500e460100c02078084c10b191000c4190002c140d4010a12550500901c100d008034000d000740400040240c840580603100b41d50181c01c421018441280c0d00e030843d682080c440e2074591424001c8011003001c913045504501000e00c400648400140d4010800c6111110071200c02c1c141d080ca0a900d0741540402020492500007442c00e080c03092104c1c0424071242000c1d404401e001c000c1051 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 469157248 1250 469155998 469156003
    0xa12020d0e0a050307140402090405130c0602011e0903091710230105060f160b060315060a060f110703050f15040506010504020d0e01090c0f1211090601050d060602 72
    0x6000300059419480035128a03001212200721000030b005007182d141007440104030859803001c0b481d0825000c00c08009203403901e1241c1071003003244510010b030005e103500c1c040800b61065403084045a042500b07500c0c0015030032718850200d0030103010004403002c0c540b42c141e40a90f2240e10200008414140d82d190600c00400c441520000544041241f06049035070505c842c1c00102600c40040d01c11001032009040a00c000d02c5102c8030504240e040003c80801e01d0041c950401c0d0807a4201e81441c180180303400d04020900c03440e03050380a503400d289440c4000c18001145840303a40c040140c52207211030400c1c01041c11020440c00c00ac2034590240d12402c11907a0343c5100e501c0502688501007915295520f48080b650281c0c1d800006480141d1030101040040d40100105580c0c0c0c40c2d6a9040c942c0b500c009114004d07546205950a8203030b0361038031050b0259030343e00ba404a9090f2080003581c2000800c1000c040318a41022550309040c0d8540c940103c0303080c000d050a01741c2c1309207051070208403241c00 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 469158498 1250 469157248 469157263
    0x1051204060f05090d0f03051b0a020a050106120b011d160306081002031006020303041502030415090f11040b0306062701090b15070201020a0609060b040212180102040e0103030807020a1202 83
    0x102d846d00081c001030188101c3c102c820445643c0c03d1080d0036044c441805207072100401c424070051040740c1ca5140f05840d05802c50740d0030350003052000c040c0180d0108000c104107055004002e0994403410080c901c0c00407200c000c0c002864040010006145411142e000b60300032000341c5a186c044a42c98000c101c0c19800039030042e2900819a00c1d5807100150462000003143d20075a8417a680a9506a280c3c1c12140a0f400240085581c600d0350940030b900d076003861040e600081c0c01580d03600200c00c1107051040a041325445080d0041c1d090070000d81054500080b0aa0020700c01d47c1c00d00c04844650070400c0180820382600c1e101038403068000a480d65658028004a100c1100c444500c1850041070f1102485041e20003800358010030081c4010414540c0540f05040c0500004078200300d580e0000340032680070215500d201005107087c0188034140e5054801e07070b656000021840c0c513052441001e2035440c1484000c0401c2407000004a03c00d00c04d0010003c85680501d400a180c1071000c030203900c4d00031 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 469159748 1250 469158498 469158523
    0x3050903010f0504020120010615020a03090b031005150d0903090905060108131407090606120605060c03032a07030e18220212030c0a02130b01051204060f0509 70
    0x80101c242500c440c00d20800c0e0180d5070585800c0801801b006000802c211407601c0707c10207541c4c8020000e80100304004008010b00d059001e46404010b41c500030303060480c241c01c01d524030754040c020020724031648000e1034180c3c0c03021180c0c004840c07441019044240f01b101c02d0411000d0506000204254102805605494401c1c6061206a682c0310044842c044c0c00c0755181c1041481204000c00f0600804108032010b04940585007916110030343c15040e6941e9a01140025100c144640520015449040003503d0100d400d903240c890003040e00381e540c4c0809031004040404454603003810080012521101d0442e070602140c0700e81540c100a07001c852503080c3c680c002c526549803111810303018400c0c18030070114a504c0d203d0f140c0225860440c00c1000400c00c0f1780203c2003030300904c0d42540800281031142900750040400895500c1801070050408484044050500c80c0310301c91607070448150b40c1210040a0300c1002079882e82409800342c0302152051101a01c1e082c240b1407108800b0070050030000 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 469160998 1250 469159748 469159751
    0x91209130c03091e020d11031c020f0c09010f051512042009071707051303060e0c030d0c0602210a091101050c070b0306030102040b0c01050411060909060108061c0305090301 76
    0xd484201e008422130144038000c1d40550049a118002030074076904070301c800c81c060102c4a4800d80511050000780410b1143c20141c2d02043c4d05807400c0008119680f8810820380e0620003651400d16494004451802001d100f1000040c8500003010018240d4029211040f681021420641000e0410a125100740b484003140340300c41c448603080140105000d408160340d44050280c0c01c44601059040c050045000c010b001c2003444040300c0800c1151018501a960010391114641c16aa24000f403403100326010b42c001402c450030075a088a0801b42d40b40e04400050b81d03d0280000d00264400c0c0131008030401c48104042c4020500c1a9002402881c0f0030040e460406410800544040c080c040e1a115a0b078080300c0f080c400030070b0341401386400010140000d82410349910500000350000c0582d4801d03a95500700700024081901c049804804094504a03c2c00c00c00c00701141c04000300418040c140b01d01000801c9103911b880484819041c02d08259841c0d000c4589001071042d070080f01070302d01c00d6 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 469162248 1250 469160998 469161023
    0x4030c0902040311041a180a0614220f020d05060901050609060904020d020904090f0c090606080610020a0605011409161e02010204120f1406091209130c0309 69
    0xc144900c00c0ba415240c11462014001d2141c80822014002843c905040c0100d02d0a0b0b000e9940c50320051405154600180c001903441c0101d8130b40c0498480e94070001000070030411171003183d1184421000695034440c5040040c0e421800c0c2d070030242c80c40c0c603020012548000b4999694007041c5d0310050241741c0c11030b0010041c4c0d90f10f00030458940601c051702648280100a05034a1f450194020540f500380078a0160a040106001a003103810010040d0b41c01d64800001808110100c00a03101600004108001c0c1c5c50900c0c000400d54a0000d0440e40a018061541d50b22107000304803000100d98080401c1c1301c03641e10ba0402010b184075000e405070194110401150f181c2d0b10008008120809035a11207072002001e010a0300100071440e4800e06556003004040b07002292051b1148007180190782c0c1312003a0280b480c04c68040d450480700d022854021100740b192502001ca02031880d481010f29036074940d0034600000309251602c02c14101d400380780c00c444254058240c0c006039180c0d03000c0c581e0600c10 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 469163498 1250 469162248 469162259
    0x40b0103210905221a0306160f11030c010c09080c04023a14191a1311031003050f0f0a0b0a020c011a0a06020c010c02060a022104030c 59
    0x91161a0310030004644803002c144018101918402e58840c0d801090285510300d003012001142c000c0c6480802041c4400c81004207820100b02da1500709803030008800c142c81d07940b1001801d000d512002c60041010080c040a42041c017042a501e030818208001c2107202400030010b450382200b403003100640d0043c0180c0c4445840c1c036209650608421411440b031304c054207028940d0007800c6220002c1c04540040c0017800b0401c2900c40c140e0240e80e16500d00c802d03810030780c10b001d86031038032054031915003810f2015281d0300e8241c1c41600f548200c025903461030701c4c1c494410001c000d41203461040c0000c1c0800320400a01064440c05002202d010310140e400f140c03d2800216140d294145000c1096484041c01400040c03030102041d1348000442401801c2002c0c042c091800d45400e03155a51541003642c001e49428940682c803103004201d14001080125000c200280c02c0c0d500e0840b019100c0c40c170101d40c10030b28a00034000021401040c20341e101815080c603810100350341140c00250707000d140c100b401080 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 469164748 1250 469163498 469163543
    0x2130501030b0709060203181207090203151f0e01050c0a211806050702010201060906031b0f1d040203070f061808010510031101090302030102130801050609060609010507050f0303040b0103 83
    0x4c5d11059409140740266207091a502e111341d032a08a6000303550031024501603481404504060308645d42c001da900c1c202031701301c0381d040d1001d00640c44c820174011a10843c01c00d5440400c131a025094140000020030400068800d8010350a1040290190780840020803481007050110708100480440c014110b154086030000e4180013425142c02c1c00050a1000c9406000902492032051001054190715490540c4c240c8201c0e9000302c0d011041181e459480c4040e0300c281001522441003e1450f40e072a00000300260560b02003c04054680c0c2804942075460510880f00500070049030410b40c2552083d0040950301f04c1800a541480301c2840032034000c40c18000c07140580758a000c0301d40100d007151107a40000c04803c04c41c82c1448020900000183c90078005401c000b4200e240001d0309910f02041c0500351407004040754810000074080084543e101e005a5490351000e207003080d211070baa8a052850701540c044d12045038440070042000300b104a0004d0b42c1a244550000509240500daa0b6107 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 469165998 1250 469164748 469164767
    0x71508100e13150b060a081003060c0302091f12150e041208090303070e0906010309050f06100504020c030706090f0803010816080c150319061e0602060f0609100302130501030b07 78
    0x1179205d142040301000b114402c2481c0d0380c21400c5110300c5003410b5605c3c0d40e401e04488081000c08046034002c6002d1905140c0700c8a4007036a07800e0400720384186810603000911401070a070300d03000c0180d6a10036180041e0481c07254440980309e014081055400d0a041c0700020883c1410000d0000310f003140000e035040c1700442a24001c2d00541c640b10b902000f94002c11550ae90f000305135030704040d62281090b02013a020801007545900381005041681407001c5103d10501c542d401c240d00880c01085a5042088000101e0302001e4118200203085021842c1c4114500101040501580000b0001149a10300030480c1d074626030a0301030038514960786810890f00d031b00d025580664000d440712101c1c0c9995044034011940b11283d0000c02c0382051221184100300c5e20a5080460036281038400c06030450485440d51020300824001000b0703610f011502c107807500380d004142900a84a60b00859042000b9800c0d0a0240d5402000391948551040103000185400d2000392599500b074400710700458010003460 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 469167248 1250 469165998 469166021
    0x70503100608012f0a12020a0f020601120c0b03070c050307050601050405060a06051608090d0804330309110411190e011407020d0c0e010314071508100e1315 69
    0x340140425140c41c04413a41000100c5001e100c610340d0161a002d8003803004041c3c08042c0d448410001400c041c000740340403416009541400d180c1c4003520b004c01c000c07022910490f100d0304031440e500d60702c044045a0b05144444010709610001c00d4036410004c01140b03013810b0f1202076604018580d2034004101c00d4a07214820362000c214104640010409802440d050560003010301d00d00c0d1002540200c1d0000601900603030740c0910204080c8240c0030000000c141401c80d1800220040055111244410b4240032003102030560321144d03071003000103c840e0180d52502c0140204921075407961503200f59442300101c4003140b00c51500480e00c840c05054140c00740041070755981c400481c6140c50303080c1540041c0341680d00c52a44076901002030303c03d41400000d00300440300002c582d490b42c9030203a4203231074215944c0d0f000c0d0000d00d13090280100d520070b50900c01c251450007510549940380c5c41d04e404c048503000305c02c1219407041000b6010607000e200140c11840703940da0034500203643c0307041070881d00c040150 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 469168498 1250 469167248 469167311
    0x1412040e1f270c120f0e060907091103070212070f06050106030606031b051e070f05010b011701050d0b0403030b10020d0f05031b0a140307020a02010e0111070902030907050310060801 80
    0x101c6401c680340d0741c4200a00610307820300088104000c441c6c6442c2c03c0c1c00f1110103180e64000e075024021f25409001c0c20300c86045858126046040030384001c1e44541d082e203d059140c58010499805106181c1d4100c0038031600080104400d5071240300090151906004403004207050403c00317412004a04c40b01d8221b0020303551002d060900420000e8803000d5800c1c1159411101800351101242201000980f018455000011203201420000d442c65100c103010310001d03680000104181d8580648444074290700480ca10610743d524903065000380305540459401080d8524203182282d0001403480a808107501c80e40070891041004503860310080721a184240000340b20841c031000318101806030900907040c0031000010300241000b081e0021900f140040c1d0040c00301c00c003035580096002c0751020f42031900c500540030f0050b540b5a100c072130744100c0c0130755a8000b000581f510410b10040e03028200c001c4c2907075420019a080320010b80800e001d810b045510744142588114000b00c500e0700d00c01040c41c01c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 469169748 1250 469168498 469168517
    0x1b070f03080c180105090303070b0c0909011d0115171504111e0d0b090705040911030603061519081501080609100c05040b03131412040e1f270c 63
    0x44a03146c11082445030584003d200100c0043c10b04000e0310b200c0c000c428801c2c0c1d02d454550040100c0d000c2d043e40951b148012548003240203000c05034030a03054a090203914500d0214501040f6541c0300a550401003680e1041c0510486055018020869510881d000d10016503d0b0000080500c0740b52842c0d40c5a443c2e080d0100150b5423030310091302c00f500c218040043c6054002c0e010425581c0101c80314400100c00090030b00562155104400b00383e1764030b0070201d04600d48100825a00d80028081145850b00001c002c49941c0e02c4001d50541045812400340216594104541e50395110b03c45c0c4941030200580003203240d00300026a01e100b26004d1000740701840d2400125801001113410070b1040080030080481d8881d20400218000c2e8498002403000300294207104bc6040c0e00510781381c1542c1c11000c4907035600040c001c01d880c241c5a10080c1c00195880303030440014501d442020060b0a04401400041c0c2c0c07041c40759550f210408809504a54102c0e50380e0b058080721550300c13292020890800 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 469170998 1250 469169748 469169797
    0x30f0f03020d050c0a03081b030c03010906090606121a0303160201020622020112020f21150f0f040e01150302100215181e01020c010c05040510081b070f03080c 70
    0x85403141c2014004090711108e04c4071550811440c1d20450300c3c4864020000010000c6640324841e250090409090030001c290814400801007a13104100b60890340d00c030184000010071100c5040840c0c1001422255103600201981c500840380c0c0034103a025002e0303080000d880d00c6595030b8050092510031035241c1002c540e0360041d2102442c056503079140584c2449080340c0c03289614002c0030640b90000c0b640e68441044040359040c24002025601c0c82c1c9403000300004546c076030742c424080d00710040720038000070020000460010240e040c403511447d820540110705442400000006030780c0203036940e0400c81004901a640d92040ba1415802001882c0001e201d0344001105141d034bd080300010380e803540a4035a03105d52514514212504a41d42c00254840d140d40c09100e04c184c11600b9041c81070410f46003c0c006a201070050300043c05000311a400241d13094000490310b0000000f81842e252601040d08000404a80b45003040b40401c6203580841c82045c0c0e40000c0d210000a46c0e8954120b0501c0e04 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 469172248 1250 469170998 469171007
    0x50f0f0a170a061416021f0b0d0503160c0806090307020d0c08100606080a090c1406070b0c070302060f0411100203040b0c011416090e0709030f0f03020d050c0a03 71
    0x302a8003071038064102410000348081c026400030b084448401c0c0c55030700b01038044191810600c0c0003a815903010099001d02c1e94580c14414054804c50440010318007000c0b000320b6803d28034418003c141c3d003c0000c01c1e042d003523602d80d00760f05e4440c0107009c0c2d031501d2030f02d4203441d5941c1e08094505849540c002d00c0104c0c018545598a04242d0b0f110380509060903680e090940c0c5002c0200390002c8500b070303d84206014051f031046d112a40038082001c10302848200da01c0c0c21640e80001e0203040018119012450209d460b41d000b100c2882c2d07030200e00c0b402c1511f440c00d4088d00d136401000d01140140a142d02140001d02c80750303852401580c1041603034503c0c803c405c0800901c041548008019800140b0002409040d050b0241071514245c1c03002091002c05d42990303c48003c0b0003040d2020200200603070520640e4850b2100303050340e002c9021542640c8820070301341c8641c4400c1c0d00041104181400304010001d11900340c0344010f2003034080324504401020142c40e6070050810011296000c400f8a4005c0380c4034 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 469173498 1250 469172248 469172279
    0x3050307060911060301030b04030f0f0c02150f03130b0a2702150d1a15030c0a14130810050c0a0f0e0405040308160815090601051210050f0f0a 63
    0x5003c041407450300040820704d0342d0400d81c4141d4003414510204000e044d0056120110052140381c85524000001c134040c01c6268107031000390145509185492000380c228007250301e020300548a040d01c03031500018076011483c070564211442211103002c146040700342e02400c04240001070b054849016110180381a00e030721450140e134443d281381040f40c400c014800040010000c1e081c0e01140c40140e00c030f40b009044907051170240c021121364640441e00036443d010303203810400b8940351035039410a000c0701711040c1040104107640101c0000d00c100498200035098422a200d44c0d058038070409035808960b007110703801c6401d1001400d0810031207016620480b0401c07203000403402d20120071174844c00420116442141e04401040712482400747c601524041c040200c09545820140740c43c14524000b48038aa071001ca5010740e1000022507040d0f070160341074a079902c650314000422850300a03000700760004184121402880441c4100000341016840100b1f40704019000c1901d2030701d003080c60f09042c01d4 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 469174748 1250 469173498 469173503
    0x405030708010c020d111c0909140c071e080a0c1202010902011e03020f070b0615190e0f130b09060d0f0b04030e0613051003050915040212070602030d0b0406030503070609 75
    0x607c1707115007004207016030041105c0d10559408001300d0401d1042001c036582100e00b03510780400c9904100030705441000310780200e688502c05401250300069440840900000010302e0a232020807241d44c00d80e8407950b41c0b40d82c18080c158040e030003d00110180c0c00c0320017010340a800118880e00c502001c0e50104e440d40a02c0e20030746001850b01c000b0b214040e40b1a044030380c0c01c03500101424140081441c00311494580f451401411900e07021001040144000d0029a8902802080184600e440d0b5030b074103084080740c0c8044c0c0403840e49546801d17240010040461100c1c850041040032803402e0510054400e10507a00405078100c850703407929081e21002c0000c02c1101044000010000c5a0711180c01505100f4005120a070006040800b00a01c1403100f4482c40201441d0804100340488000384000c0802d11000700a001c0e0340301d90004c5142101e521701594034601c1110030021305564004010414406a09401c00203544248100020b84200380720103006603000340b01c078002060303699125220f000e1 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 469175998 1250 469174748 469174753
    0x7050a1d100f080a0507050a06050d0c0201060b160b0708090d0302130801110406080a0209060d020a0c0503131706010303090e0c16032f2d120405030708010c020d11 72
    0x5a5801c480250a074464100a5242d001000111304000741040480041c10046800c84107940c02c080000784117010b901e12074035181c0c1e120a064201c03603000717501ca0b90241c10344071000b0b9680c1e0701074200c107240c1e4008003e00704c0e41202c007280080c41052041c0e0099009044180281000303900090044010f03400c004c0c001c02c0481d02d01c0c00005401c0d2000d11507000030400c17032603005444524020004d45010b00051a12541d0780c010051000c26594040858003050304400c0010386030407148104175407443d803a100c000e115200000d28000a071404101d0003044038204941501100c40c451074071502c0c2d00c42807100801040485005008071210358628640c0721910a80c0b26041280d000e6107116108940350b010b230041420741c58000300001d1710a191072407030365101c03866900c29202d01e00b010369140d1400e181c002ea1809489142d242c00d10412085041001c41c0034100c440c1002c00302c1403020a039002d403003044d00c64460b29400013840101801007103400c44058025051274aa440816190612005440341090 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 469177248 1250 469175998 469176031
    0x70f0207050a0303020703052a060d200310050f06030a0e0a0605100e0601030c0801030305090a09050406020c01051003050a020105030a1b2f070b07050c060408030c07050a1d 76
    0xe440d04120baa00650190b402003101501c0d40c00c00b20704000b01e25008041070201d406003010319039110500c9240c043c9090305c1c480e6030340081440c0c3c4401001e03090b030300305442880b807100c940800d211031001d10300039041c4e11408201c1075650070800040281000c8403030b03003000d8103000040100419034011031005040070250748441d03078282c2d02e100459a08550180031210303908801c1c0720580303900c030b10140e0052081c00e041001001070703c0042c2c40b03848148002000c01c90001042d84140c1c1341e944010008240354281400241002d18099000c2e40042c541040d0340d6113481c0001d0607a020080d1010120f80e080000f914850400707400448055100804071101c1d191036241c0e034200e1745a201000c084801055440500300240340c0a9100310303011004203454807201c1c7c0c034200e4000c010081551401c90720400092a0b407103c10785489420a48080c1c04150f2001c004500060380c0b11002c401030042190000584204940714000c01810301c195001c1c60b61a452a2040c101703010030700d0868203070011500228813412 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 469178498 1250 469177248 469177259
    0x6020c030304050120040e0f091609090204050606120a0b180403030912020105071b21020303040c0e01061209020d050f03071a0f04031202160c17010e06070f0207 71
    0x840d40242c41c101c030569524007045e01100400f2084084809821094078905032604c4840040c241000d0600c40109440c3d50210745503034410801103105515051940b43d03003540d00d0030f0040c0101803040007a4011403c0c103000500503d0403008441b130b280422001c210307894403210b2103500107015400106030803134511a0707000310003001c070002284100e1081d0f50111350310f41c0c985468501c915140c8920030a40e0704102c02d1008103038029401c3c100c26800d601031150101c80368149403034010741100b00340000811010b040c040719035011009611450195542d11885c0307940e0150140d41c03500902c140000260204500b8244415580105516600003084500e01000c4d9460302810891100c4040050703610000e000410040d0040441c81618120741c0d03125802e10700900100c904010090000702040740b030400600c4081807550507105044010610140003400910305480550403c0c014011080c400c640484120b02050280f00c0b50700901c540901856100e5000070b450a172507825090b0254016118081403 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 469179748 1250 469178498 469178503
    0x40603141b0d1814010c17011202060403080a05031f05010816050c1501090c05030609060904080705070f030c080f1e07091e050f0403020715090806041407060c0f0f06020c 75
    0x10f056000b40032903007100302588006400c585150b94040c041c0001e40403501c0d4011000d000e00340c1105e0540003100301d1130240e48009410f5108541000349000400700d2103080d5075074480060340c400c0d8007042140f41c00340301c00001c10415100a100306030003d191070000665446c18140001d0540707509007000c0d802c09003039a00e0981058004d2840c448500d4160307004010128131070159040a021301e04000d0319500780140480c1180000410b083d004a000e80d0200d000c02607210308491000741c101040d40e1000c2d44640c0300060340c1303c2030311041d07400100022000c1001140403c814001003540e80040241e1020078840090000c1c5007030400107280a86000011342445a0140011034500001c201e001c06e05000c1001302160409000d114904001130304020010307800080810556008442c540714000e4100c1c800c8454080d19003003010f80e0b00515050004200181524481c0c050780042500c0000d503c812045a03000c0980001a0943c5100b004850109810180f04003400e40a1a005172415007448206031 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 469180998 1250 469179748 469179791
    0x5090c161113180615081c1b061a010809150613020a120608010e030a08061914100e101407080f0c010605090103020609060c07030b010902040603141b0d 67
    0x348800b02158100c3c104030007032056003508031601c5402c00c400740c2814040c0d03946a4200000c282c0c0ca4982c0320340b46038000c0c05484d01c1340a0581c1c8031014a0382c4034143c941007014040b400c8403c44004c2d4900044420756000b034000c180b04042e40c41c0240802203c3c4840b0b0b0b420740d60f0183c0340c1d6401803103011442843c0c0403c3d00041c42442196105d00078140301c8403500348110380055000d07480513494241d40c1c207001840801102d502c50080d03d414409502e601000580012000c0882e101001c80b04500148841184042c4240d40600b1100800080107184040c0c0c0c058841440d096840520303c1c42d80e1002a000d02990003004d941c1c811944d0401308281c0c2c4400c207a07803162550028104010425115240d001d00410018010640f4440115491503012a03010301500007a075102d003c0105007107a103018108002c600450304503a419800356501e8082d040254441c1c00b41c440000d040407a5190030302c40780000703140141d48103035510000c03541303204010030984c016101040c0e209840c1c44108054450b00a55039 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 469182248 1250 469180998 469181021
    0x5030403200f010e071a0a051c052e06091502030408030406020f0f2107080d051602010605030a11010c150203010602100506030a170a030e150105090c161113 69
    0x4d41e254007011000e2038140c0540c018207211280d1710040b1112070550080c0c40b1100c81c90b082943e04c81004003040c09410020440c0000440d00c1c020801c4601040b040701000d5000c08443c40c0c541a0307240107001090143c4034040e10010400b400010002c0585c14002a0080c030002e106407410240c8942c1d4503400c40d4071a07405900103038045070700c134600014180040720803c0e20303c0c00109100d0010001111b4145404040b02901c01c0c0c010070000180400c003001c031090203c040f641040300d0310703005449401055131341c003000c070043d0710700200803610f4100059050000b6422a0300490749640c0c3d01d00469541320030241c22121110f050b010299224440c1c00910f02030a403540180820700c43e0b2440550849500815151180d4000304240b00070800089220b6600007141600b0f654841160800b900509041701014510f4450006600004a2a515194141c5008032122001030710b541a00120f68061001c00e489103001c00040600061600f8038280814800a0f042c0c140b041c90425480c4100d0b81c0ca0000fa = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 469183498 1250 469182248 469182251
    0xa1a01061106040b0f18010c17010510080c0d0605100801091406011e0207080d09030203210a0c0c0f0e04060f0e070519090204080d0207080303040305030403200f01 72
    0x50098503049101d010903a1450401006980380070340b10100c064401a105d54001c680c5180407680c00101c00c008050040e14520081c0104685404020300000c03448407000c140490303040011686180c81410101c4444141e5140c44042e2150580c0804075407010b00f01c200c03400d640329000901c588840d80000841640c50f110000030303600d0002c102007a1481d0002003844122010b00b0810f01c2da8010510f081c40003010310f84024203030002c04c0141c0ca020280d030094440ca04c103c031404050f0f268800d498005803882602a1a03280c1100c0b0410392588113140000c2c00484001e111595603a40300c3e400c02d030101e9010b01e48020b4510381e5441800484140c0307402090300c9030801d1003000300384401d60007814254000300e48100310001040f0142e0752100454020280306100c410880c054004410411078050410b40c4011036803241c2e41c485a9a0740d015850f04000076000d0030000298072070001c803c2c1e03403095405441d900e14503030310f8be6400c85861412155100a20941d8641034880d00c40400144101e602d00000 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 469184748 1250 469183498 469183501
    0x1b02030a1e08150d17040f050402071208090c04050103030c060b0909100e010605190807120305030a020901050c0115060917070b0903071d010509010e25020a1a 70
    0x10060040d680410a40c1c58152540506911198842d0310154840c0c41c442072402030391004000290030780100c0c070001e40102440700001c912010118014400c0f14a1001d00099543c1d44005010070382c0a0300501401c402c41208070308140ca40140d0360030782d109507030f2402e1700c403004078020004040f200e027a0070540010b0041c4441f002033246030703c25000c03502801c13200902103161074401e103a41c804800f604009840d4071a021000c24500c00d400c450041e0000811160b214031520503e02911803084c4150340c9148a90600040c03c000130755501c070807681d05036540c81e14503903ca00503100650b0050344581d04000040055a0f6240000e10034848010b0000135544090751a004009203051056000200b8044203218a0712018900044400458002d0300d135070358403454900006804c0c244070354004040440040320b615050300200b03a003031b4141d9030200c03610000d42e41c9600c0314240740d4004564400c90340c051502c880310580307494855036400fa0300e40d1040780d450500b00c3c4e071040c0101055140e0501480110780 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 469185998 1250 469184748 469184767
    0x22a0a0b010b13090b010908010908030f0106090e0705131809061a1c11030a060522032124030c1410140d050f0702011b0f030b041b0203 60
    0x1440d49005191500c1414184503540c002c08803008920b2044030078003030b0f40d0101c0c404242d0245012a00414414008000700741043c00c080c103007940202e50201d9204072110021a2032800f804482d0280c03421422070031420303501c2880c240d442c1d82c0a103042111200b03c0341c200090030121740c0440300801181c1031000c20751043c245420004e880750002140700c031050360f10361171320140c80b10761030340c110000000c513614400a16400c0a02115528548143e05800b40300345c01400d00a00346c0040340555152442d9071807150300504503600002d225000203002032000401c0500410090401c1410380740218000141c211420f401e61a52403142c120440c405405c045007041448141d04034500203159034082500747c0c0b031b9002d0004240580c0040c564041c08a03680c5d10000d07003000982a120f88040c204010411400c2c02c0b000c80c546107404481500040d820200b41085000500e200400144400d4840d04000b008200e01900500a44240203810581d2107000042c491110701c01801d4416544e005144d8840c1c010 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 469187248 1250 469185998 469186013
    0x1b070201050d111e160303090c030b040327050a270219020f010506010804150608011406100c0503030109020f090307031b0914060d1109011509080109110103022a0a 72
    0x5454016600030901c208542c0c103181c4640045c138960b051900054181c5171789095240c1052503003015005c151514208002c05400c1440300e06422052b6010302955100d81d02c4032940354015009060b000304403420100a407110a6064000314900920700709000803551030036100703d0f080707501240f111503100090001010b405102e00c081c4000c13103400070b2140e8a040400688402c8d0051b2000b4000510520012030500066004074043c02940c0024440c80c010060b031080020f4094a003944a84031640c02054618003548141100341e0348040558250781c6401000002500120034400390000300308940301183d9400d004c1c420246110b48a00c01c2c1c3c0d4a4080c0344281140021b030031000c1d441e8038040d0680052403070a00010b50020044840c2480401140380c0306080c00c00c060190754005134840c00104034030f021041500300d490b40300d03602c000f04039980b291080d0a0700e2071b034200500005000c0d042503015500c039030010f00d400200105c4a244c507982c40e404512140c840c80100c121207820000c2c3c00401c00004 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 469188498 1250 469187248 469187287
    0x705040e0303090c060c1009060b0f041404061d1c020d08040302070306181b03121b0b0912030c0a08060409050d21020a0c050f061b070201050d11 64
    0x40c100440c2540f80000070541d4a48004407610b1003030501051402ca041000c00100b103c0c00f904181c1840368410f07515009000d400c2032022248184401009400981031500c9a0320f0071450110380c82d9520344458a82d480240300038904d50b04010701300e100c030700c071030000401005540301b4220303103844944807481030002c1c180504000c03071204100b42d40050001099001a051041c0c81c0c104100240d0744018910f81d040200b4080e41c010081e00418184203540048190300d4004c50f4000e03040c2044420300342801720703138810742d44a100f45200c440310191808242460303115a402680c0f40c04440e50f4014100ba030039001c0d007048604c41d001d20000900d203420076030301c03100c201d81040003981c040c4990182a85c0b510f0300c0c0c0c9551941c2c0302c20800d00e0805202a070740c0411100607824200304c0f085694a40b10b1000404d440310000c02030f141d501c00d4054411041d5000260340348910040f029031108400c00280c84400c5501110090341002010700ca40c0c6030148a610601c00801241c2d101c541d1b9075a42031107800c00f030516 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 469189748 1250 469188498 469188521
    0x11071b05030718020d0c270f0e06040e0a08030406060b072f120f01060e06030a03110309061201080c040c0f03090c0f03061401150504030b0402030312040302070504 72
    0x4090804104035200069034100b41c0c0d0b80329035110086081961004000d0042e030b100700a0560610004110140c0c00c0030301e413460b150040391400038196010101200d40881c1d44180d50044071098410451071040e9604036400c81001080412182c0804100e04d10f007aa540e441510908000814001042014030410000f840c0c0b181c1e00a050071455210880c5000e4a1958488000c0ca20005604149089448241904002404c503106e26005856a0395030b080c0c00c00340703501d140d8030706000403400d02e1400074214882c1c88000d008102c407550a0f601200c580c081e0f5544c50180d44810300040380c01e5540c17400030f000c00c05204159003046615101d001440c10080540281c0a00d14058550001c0381d40606040c6110995080200d08400c0c0340c0381254840c01c2551068865010800c40402001401c1c2c0002290b4101e418582c0d4541e600c41518881d020901c03014280482d1007000f0410010f0740080b0b6942d8040c0c0000d09490614800b42d8070407580c018200c1c0c0803401600410000c3c00b007803802d072003000910072 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 469190998 1250 469189748 469189793
    0x90106030807080c0a0b0708010f050a180e12030a0506131b0e0a0801090b0601021e10050601050702120705130209090c071b0803090f040203150409060e011107 70
    0x2880e5850700080c621800101a04003580000c0805101d03c041240e00c09855110000001c03030b15002800500405c2c080c0508400c00c200310000140a10742080c4080540d681036040c044000047e8184d080104401007440840340a490288074641100300061072091140100105c0c036490704201304805030b00382c4505034100525000d455440e0110f503418205000810382400c24500081070009074a1462690003808690300f418580002c2000480c20310340a0700083c0c0840d50502c00400508111380c1c400441e500545c6d01405540495200f82d0308450303000314060500300e160034000d8012440310900300c90500090307401040100003909003c0000c0d038802803007900c01c500700782d0b0002c0000c4221f003000e04980c0300114040b51020074408030940d282c5150041215020072140e0701c0e40300c0c41d2250004000c03a4422200c1c0b003002c0d60301e4285030088034800c04441d4100000b0541101c100401010515802c6e03443c540e03070382c001e06480c007803d1059004080840301090b0b194561454560741d9140b106103d2080c00c03 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 469192248 1250 469190998 469191011
    0xc0503040b22030606031a041e06020f0a0207030b0c0c060c030703020702041103071d0f060304020f121b06040b0a0f17130b09010e0c0d0807061b08100806180102040315050f0901 78
    0x8407001e10601e1001022780c5c080c804c0c0e04150610342c0103030181c00c8104040000000b1072203030072a000510001160b1107401451401e641e4000222054080c0b00391110207908008000381455600d44002e680c45041410010704240e03158012404840003104004100d940000c20f0103003c41e00140342c0076a6508022f201c83d651134646003c01e40b07184070280c005019440c04400715086589100c14016142c50151903c06e020500b95102079032403215400303440c0c52400503102e40300c16080c0b2404542c155448110031070315240604208803854076000000c0e40400c000c1040320710040c101c4400c0d16025a44180030b0f48410800c900b803890030481c01500c500b03481d0385000c4603d880c060010452024604044504d004815a03e0500400b24802c0550040060b454420031104084034845940c0420240e9600e549655840d403000c40d540b00214001c03990300781d11140010b40041c0740385080400704c800c900000350815a41e581c0b5440312020319035607218003940b0b5030100108a00304c43c0e002c5600007004802480903 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 469193498 1250 469192248 469192253
    0x120d020d0c17271527180712141308220807080a05070909080f0316110606090412020109170c1c090b030a09050d0e03010c0c0503040b22030606031a04 66
    0x80f0b20a00c0746071202d11010704060801c0240e0403134100f814940c060400007030f02e06804264080106c1c03c540c44000300703e242910950307580b030780c0c402c5500b13015807850000026140ca00c94030303c22543c0704600b01c4002c5403c0000c4110b010244100c400005030140d8002511820610341c1ea0410325030750030204403030380b18003072650200b040000c034081120044038002030080200d08100b1031a00ca10000c0d0805810000140803894481070401c40030302c41180d4641c01c4181071074099a0701c1308401d41c2c2d07155101c01c2210210300800e10700c44280144180600000070900b0b41d07a80e40310007824a0340800c414000d40800c402304050380a0144140c00c50408019001d080315140020f000c40b1031500442c1c806020110020b105541035a000e090456001012074a00b00b51200008020700c0c20210128025420254510b01490007026203d401e10341c0140910304085c00c0000404250b000303102c0410800304854203810001c00b144001201460044401055850460516818401c0100d031003203038084c03c11042101 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 469194748 1250 469193498 469193539
    0x50c0c030d2a0c02011706100e06090d060506030d0c03050409020315060c060a11090333040317010f0e0c09010309080a030209120d020d0c1727 63
    0x41c098038903900000d01c008140c00d0030011124201e0410451a51810307105842c6800c00b01000f0041e100340d8441d1045421007240d80c808402c1a1901c43e005100305a00d580c0c01c900582d10b00c0c090348006400c250912540320005250900b00c0072040e035403681d0308d10078805103003400d1102201000680c2071050a4184554000340148501e204000030550b0100c042445500c40904051054000805554030380b9036040c882512000d06075440480c0c945040140c105007410581650140e2900501800c090120104400b440c100500c48140e1810030700d4400e102c84004c0c00c03101a000707601030f9403110044042c00b100411460b8068120000200a03807004110155000d0540e0340c0c40a50a5501030711013450a005030702400606100400110000c41d04030000340c0d055002c2c04810f0801c48441d509940d0820015442d80c100b00940c0c80180c1142d40194800c0340141650a50385200d141c40f15000344402e048031245410100142c0c0200f02c000d01c0782503180842000c0107441040450b001012400c0da03030009107 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 469195998 1250 469194748 469194757
    0x15220b030708131412030114120d051c050c03011505070c0303122306131103060607020a0f0321030519110c070b04032901090506060d0f06050301050c0c03 68
    0x44100030090f0f854000c00100b80c11080c000c6101e402102d441c010100c03400007854009020b042410329480800c0007142c0b401300360080c1090210f0028280c1303620308100c01c49842d4010003c120900714801d00082c011451446050322414500103140d8a0794100808011004151001881042000d118500102d000345a82800b1264103050503941075903001c40c080003034080050b13030200001d9408140d03c0b001c40040c000302d2090710115044000f000344c207c1e00704101c5aa0540c02000302d1000c0c0700140361414040010451980000d003000c041f996591078641142c0e59680084401307030b0704540002a800c0c501d49801103805590f00b02401280f41244001503c0b03026944001c0390661554040070340052034004440c0f001c117003801a900c4454032241310030306590141c801115402464502104540b02800f44180f010420134031001c0c5c1c2d80d2030030030203201801d4045c0165900c840d081042040840441c45400d4800d0740c816030101d04645050101421500c00800e9031400301c030100007120603400003000b2203 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 469197248 1250 469195998 469196011
    0xc0a060f2301150e1206060f010c110d0602120903040f050f0d02010e280e0c03010f061d040c030b0306060303040b121f240e0a031115220b030708 64
    0x4400c0c104040d14104d9800074200034080c3c11811000c005e01901d44045007070361003a40705449099520442c40011150a1040000a04070880e44a2105403078a01600d5040202e40600340c0507003056180400ea0310400c40960f10602c080d4000502000400182c010710b100900003215084200642d84010480c4002d004100a0410055550890055880c181001070140d105102802845000002270001030321900404030140386050000d6500001041140d0503644544441c8d09030320f20b800d03815241401200504690701903410103000c040c0d1924403481143c60016074011a0420000c000d1501340301001d80a240284c004120902c071460002084032040c6141d2250020720796507654072101d2080050a040f44000d00d10940010844900b10701e020000c1d0481e000d0441001c84002c00341c400c503001080a50700410b62541c2000414010042600c0d1044050040e0000c180110904d21903540002500740d05a40c50348402c22100c0242c001c60009003d09030010391540c200703084003502829008180 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 469198498 1250 469197248 469197269
    0x1209080f03040f06020d0905061302030706050a09180902130b0f0114160506060a061701060c30021006120b04050f0a060f0b010c0f12050c0a060f2301 66
    0xb040400c0a0100990011504a00119154003008150b00060214101e05070b0326445418041004054a05586140158010300500e03040b4500706080e11141c100c40141c00601035003100000d10300450b0001c0e007900d007520078000546040d00c3e10402000700e9142c00050021490a008141d41d600c81c0290b400e242e030300909000402c0d14441d800dc4020b4410700c0c1044100f02024401c0b8010000700050490140c807040300d01c5022035440c1d40d030032034405c400040c4188900701c107000100700141c0206000c203c118020020b030041c801164104001e1000b1282c05d050304400c0300d1050707800880e07040c84051900304004c0c1050114929010281050080a03071014108003d040003060070400200a122550101a001d0392103013032007420410020440320148440d414140a00a40710f50703c98645204c440da44040c4403642d402c2d2684500c61141c4180450302d080c04020008002010310030040c00e49094820480415204002100d02c01500c10500c69400888a140c00550305203a03240441c03415100c12000 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 469199748 1250 469198498 469198501
    0x11030307150912210e0c2220040e0705040e190608010605030a060c0908250b090108040f0203122a0c15090a0306090602070c080f030a030902030c0415061209080f03 72
    0xba03900f014045521030b54014030402000c136482410940c2e190004181f003a0030452800c142c0c620340004050712402e01c4203617404010600040b0300c19000756030080400e1601ea0700b80390302d8168541040d88180d6541e1189024104003080c10621801140b01401e07441009104070351900c4003183c0c2d1400c40c1d039001006280c0f1042e141c0d40b0180f103101e6680040a10710308460034032118030500d040100140c50071f084203048050740466404010411200141e80c185d6419146a0300d81d110501d09007080300049a260144444280c2c82c3d010204c064030b00171131000000c2c040d9100c1401e4840042070405643e4041e80c00103100105d03a6564080052908100704062a9603181c42500140385017016400040c0341c0e510707102d41082880401d0740900300040c03151000c611120348900c042540d0f00d42c6120502c1d1254400c0190005d49482a005000410300c0a0112122a1910b90000d016500701300009582c0b4980c0d00b8040115692050707411841c080009001c11040d1200d03100c004242c45205070b48003c0850000 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 469200998 1250 469199748 469199771
    0x3090d020d020411031305070608010b0a110c0a080309031608120a0306120f0b0a050402060d0b010306030b070f17010803040e0601120f060f1d01031103030715091221 73
    0x13041142c40d40346415015550349017400340446010344018040e80c15101c0c4840101d00309018800c1c203410703501400d102c00e08028a46a00719100d40da042400781250050100c2041e09450700540c44000c0c00d512006107480c2c02c1c080d42454074001446480b1100d69103416800c0142070004180200c82404c008419555020000307016030140910354004003c0b80381c299103403000e001002c0740400c80d951061a0b00b00050300c448418100741c8005440103580070000f00050307281702a180e800040807580c1070401041d420781e00d80320038100e40d408603002c0c00460507610203c40c04a41c441034069131250412021091035041550b038955070301550140307403008240704000c103400741c0c00303600d415001d448041803e010403903809207801c000c0c103c40d105903a05452525404140c01e40500c41c0c2513441c1c01004024203090380b031605c401c121121a981c0700d43d058001002644085002150f900b84040010040884e800c225031401441c0c50b00004410802c101e0251000540541c095000402d00840100080b44a10340130 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 469202248 1250 469200998 469201001
    0xc031b03050604051f0c020606010e040609090b0a1104032004090b1003030e1507150b21070b0703020613150204090501050405130203030a080a0b06070f02090903090d020d0204 77
    0x140c10203001c0e4840d038000c0004220300090380d034888004010b00c0c8400544a48481410b46542880c401c01603080f600020301154071507081c0482001004101142d50fa6603149040100e8803c40400d60380800c1e40310030042d4880085c0204114040c00c1c030180d5140034035503214201604001e600441200380585101c203050768aa81103284016000015080b8904200c60010801d03080f40c802240030901c0c01210084502d00f14250200b2221918100340c07410505a0310394201101d040d04403695696200f48480c007544a0110030a1600c210b8510760407815064240e203454103078541e00c03107580004100040000039501162907034101700d0181802c0c1c40f851b414a041c3d0f4012101e1074039810b50a01c04940010003103a00e401540c1240c81c261400c0146403240d21105003100c1062001a4040e0300801c05c110b03203284518082940245520780003d01e028903000024241c0e40708410030340e800051300c1c103c0025440c09041c4a5004002d0030015490000b18001150100e44039010291049600303480000564489 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 469203498 1250 469202248 469202303
    0x30b04060e011a13030b09030903010c0f09032a0312120207020a0e0403020a02091509060a0b0403081e040303050a0806120d03020c010e0609010905060901020a0914040209040e0120070c03 82
    0x5c030a82c060181f0f4030301318599030380c2c00c0074640c2c070310940c00d0210703007102d0a00648402c400000300c0d0352108103442c02c6440701112160301c0c0c12544240c84403884840914150545070001640c0714104d60303c007440305000c0080c00d046101c0003221100788104a540016520002c2d07642c101c0791000c021482541c0c41d410282c1c2800182039000c0d400400840070000040701c444c540f0128403904840e00b2601d900c8a40a100c0c0c020a02d00854205440130031052000c11102e8002c0c00000c61030003010080580104180302e019003150f4000c40224001003200030540e0707000107100e5885102551092038a000d03050480750340700101c00c02101030644c0022003e040340070a401400c81000b0400454a05e0300f014032203a4000c018190b42601c0502440000c80d80d02e00c018000c0700c440750780c15176582800a041640001002c154240350070352199081205c0c280d2510b0b2802032103803400c548400082c4103544007006410204100e1f000054001d01042406d0004040040c00d4003071f00d8020f0004407032000211010340c0c50850 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 469204748 1250 469203498 469203503
    0x11010b0406090b18010b07020d020a1706040c0602030315060315040203010e1605070305191b051005090a031d06130e0103150b010206062e030b04060e011a1303 70
    0x411001141142d4543c00c601e1a0010940d20000c2d1070310f41080b1842c02c0c2e2400c0c0a181608541041030002524202e405211000e00050180b14000c4e981c0711000d007450300d0502e070132909070821000c100c2070180d580c01110003440749001562444c92700800c416206900150b0b183d104020100114a03580015015119508400f0740115565611216617001c002401c9a2000e40c40143e100301400b81481201560030517a410b49515043c41c0c400c1e14000e020441180321001040211099585c031541400460f0030405c1c040d20280c80c1c4c017060b01e04c0d00030a0300c00040c2000d10a5008403483c1002079400a01d081c0c841c00e00f6900d01c18005e0354030001907250300ca41803d03201c140304900e00100301072600e0030440e8100c91188000c0240d05440700804020340302861021405070b00080001400c5060007040e84a4040e56048510800300d48450358065818403100043c002039680c0d4410348850415201c2c50000e00030300781c9800c000358582500200080d280c1a0040200f170408100d0303002064505601030041d5070b = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 469205998 1250 469204748 469204751
    0x1150e100e1e0405100608010905090a0b0703090516060c17040f03031101050109090f03081b04060e18090712080906070305120a051603021c1d0715020a0311010b04 72
    0x540000102c000b00d1440c03a94607102d54a440007080344414454007060031180552610040e0768600541d19006050040000030f040c0a5410803100041583c00c1091003050076440c00226104e00c0d0400c1c61500d174100182d046000c4402c802480500d40049805003a80d52000203c3d2410200c00c0711304c00540580d0340400c0070310034205000710401d5081902e014910003200001c00c0b80303a81c2c0b05010300594800850181980c240e1172112008207210f40000340e40a80c03d5000481078010038001c42d1903980c03080d030003000050910078954800d03140c8801c1000d00001150103001182c14150172590300c0e2400b62080d040058072124081003081800c50540f0408040144200e03251101c0e828003416035404810411030300b50601c1c0018111a145e8440c82d8068120800901e030b074141d50034810f030700a611010425116040d00c01c0c0f000409560b1740150103c10038620600c0c000d0705045400780d450190187c01c620307070000d0782647d185101039000030318030708154251906800403520b001c0d81c0c500510031010b0f080e03080f9 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 469207248 1250 469205998 469206019
    0x4020f0f150f12070e0d0b092a01031a0a1203140408070501030b100c02150409020423062811010c0903140703030e04050405010b0d0b0f01150e100e 65
    0x120810040c1a9400054100f00300542e55071800326540d451100c0c074564030070401c004000100740640c0019a004502c0c4c01158220701a07481c07210951900d2411000003460301c40c205442c1540d15028030450711150b80c400c024465241c0d4001f841e01e4010740100c0c0500a42d440e804014148101520320302049440c251a030f0380c907107422440340c4950389406103a001c00e0820032160b003e803e015410303545550a5541740003646120b9400c004503241d94000c200c0e540d075000d10021a2184191000f0b0004111104402142682112620110303050100c0e04e10311442050000c2070f011f0010b0011030205031101890345480044002042e51603450000c00601650f01c2e000382c02b61410341010090303060f40d005030001c80d40c140002c440d00e580d84003607010007000103c0c6c1019072481800c0680000360418400c0c80041801915440880c0c20b41e200c0840035079149082d41305001e0840400050303c2e014040390904080840208000900b880f000c640005024000003160071a00c13a2040154405200f0000c24940c0794 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 469208498 1250 469207248 469207267
    0x1208040b03100f06140714070f080c090f061507031205071116060509130e06101404060b0f03060d020405130303050c0901230705010216050f0604020f0f15 68
    0x14102d00071518407002c03c000101c0c0f2607008840b50305280d4074201d01c0a14040c0c1c0b0799a01d036000d22100c480c4140d588140f68000c2030750b140d0b1045640290a203034000f0016800707010108a51000c0243c09005484101c2051200039201e10004d0300c404101c4800d01c0e65202014030f02101c0c2e8040e40301800c08002c0c5071500717000301140e100101220141154040ba04070300c0182420444803881c600c40c11011400821180c1000c0c01c02c004101c04007403d0040000f10b030030081400341d00303280d011070f002c4103c283c07080002c0c8008012804a505554401d0701c04002c4103040036041c45061081041da40c0c007004020000801136a11540003840046c0d01070028001c038244164040340f0024000402c4012038100030010716828030b940c0a44450b807605039100003405071081e128030040030280ca1650355034107040144501180b02400204106031407240078407286d03481c60424608050302c88400308950303000f540030b00003d40d688100c130b00395098044444d026840030311070000700b01040d108008500d040000c500c8000 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 469209748 1250 469208498 469208521
    0x8060a060f11032808091b1212040603020a0f050408060105040b0d0f0302060a110309070302060c1527010b090c090303041a031e070503040b0a0b1e190b03011208040b03 74
    0x561078080c2c0700d0040c01e031100c4000c030341c480000307044400b1f42e030544221018283c50301d44014401041040c0548000040948840e809503015800200110742c0008030405440c1d800800222091204d00c0c080d403c0034100001d0644840c010710030640304680356450422240e40c1d0503210283c4640c8400e1212a24034075184c061b480d82c1d000c03034004031042e01d001046044600e4580449200e0f0040300b01910042e03003140c1c00c00940703400c107039100c4000384120750081c03610b840c82c0340700e060189102c031844140407990582c040c81c407080300020b04013041c0d050483c865071a032620340c0d000740c02155111000c0c1e15800050f021074514016688441d007060303160b4005210014042c001103006004e254032900541c080104000c11854083d11800d000450030000600840c07411001e09030444845030002c02c0c02d09040d00011005000440300000c1c800380b42815101c94507000d0074400c41003040050120100385080c0e5100c040740014807e44058010a80aa20411a12408031740142c010300e41460303280d0901c906600c1 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 469210998 1250 469209748 469209817
    0x605060a0c03030606050c0601030b07020312070903020a0b0c0d0e04182316210b070e0306160905040f182003010b150a031509020a08060a060f1103 65
    0x100400c2c603154005c1341c01440f9408481407510769200501c0c5503481c6135524162003000038200411400f003030045071114040076040600031f4601c1d0351034030382850071401008140b448039800f4407007081e0f04000003100c000d80402d0604942c02a403e2100d511400c034000704020309035500e20904e6842d048234142080182e91605028200c0340c0da9896010414400030303199541e65440400b00442209071410412090310042c200c580c2c0902e03075002c1543d034503680e65908403403101741d9011000c40c9130b041101d06542002c100003903019260007440300050310102e0018103404c1d120f001d002c1c0160385601016412103119008140c80c0c00108007c049203540504018108006903540c0030380107000b13402d0042280c030301402203108148000f415580e40d989a05061105603001401e584280341d1101c6054041d0843c401103100100888500940da988035100001d20880c0005c5c00c00f031054140807020700085601000c107103200c1840707003450009460000c2e445c40c07550180c0081811900080940781c64212115040d50 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 469212248 1250 469210998 469211003
    0x9031b0e071d0607050606100c050106170d17060105070212030301080115090606050f0714010f0c030b041406280f0302011b0f1502070204090c140108070c060c030605060a0c 76
    0x900c00742c41400b0400842c0d00c11039034050020350203000401d820f840d202c03c1040043c00d19003002d450303c030f056584060075540785a00000108030b0300d00f01800c00c8078007409032038248065850084086000b20080600c1d040c0d001c0c26480c10440003040180864031058902800085004100e0303440b90380d6143c4040c0a03040c900c0c89030f00300350341013040045c2c0c444140c0550410340c8c0254a0326400c1800500b1200c0c295040886c090351001c40031444d402000b81c3c00e00c00c0040c0b03441030f190041004440c990000e0240c0c0e41c0441c0c901e00861400500752500800c440c4113a400000c01c451374800c0c08505110a289201031251070201003030b40344000900c194480b054507084070b01c01e880d0000c56050039200d5070481c0656120140101c40c80c1108080000e521181c95985003191050043c28188582c02060442e9212a41100c079107070403081c28054007950b50070b01101d407502480c142c180c13881d155100a010b0201d910000385029100c4c107040000718087c0d081741014040c00b030709981c2c845c054200c00820f5000011802d = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 469213498 1250 469212248 469212287
    0x10260603030f1603110f060a05070c0b07030b0a0807050109030605310201020d0813023a0b0f0919020406030f03050a0f051305012f070806070f09031b0e07 68
    0x21410300141c0480c011000c800d0321400703400c0603a586408c80014100c0106000c0c00c001c00012110700080718085010b00807002550300242c80101d000138000c20091a4102103800e5200203000c00c0140c0c0c0c0050004240d0f0352025012845448416130f801c00301141a0100c07186030202c000c0b40d211854451814818103000740c0c201d81001016030310644031010706032215440e034047c0006000250500c0d0560b0044a07040d84a02c200e50440c80074465440d8804941070281e60745054010702c00d2280102d505030b00310941649600560503e4042c2c41d655203c00c4a10302c58440360307031541c10250b50b1260b0184004680000b40400307044902e183c000c0584c0e12102c40036022035103000c1003450361b81c0b00d1002d0314009142e074140190164200001035850184880c8178112011005030b48075040f0740c01500280140301c06800030070200e82030842407414440001c20020400588010351a03a0503400702030341088030340120580700d0851100c0c48080803e41c03250003038002c007070181091003190b17a0301007004800d0301001b509 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 469214748 1250 469213498 469213517
    0x1c02041d0a0c0914150406030e0c0618010c080706050a0f0f09020306060d14010e03091f120902060702090708090d05070206040312020a0f03090510260603030f1603 72
    0x1410402c03500c501000700d00041c054003050220040c811401002c0d00c1c4001e101c0c1c12004000f140300440c0740d0294201c0700010b9101c00008030206c8003044421000d010480e01c0c00d0500079030110b129209490358030002d04110341595844c00344600c07a01210480c07500b00304184400d1030407e4103003010b400c80b200c100c500c0c64a0701e43d04140b015a50300c500442e07075500401610041d150f040030001030442d01042522410400007150866403801d01c00c04001c0d09818018540b258800b00410110410311110329141007140d1a111000c10781c0200d824401e01700031040000d02c3c24071400824154054035400940100700d03d001d106c45250081c40d4244503040600407507501c02180c110465241c025200000d411036000d0001b4000500b8508041c011105940304558442549480780d2401c612006002d8021071050002405075080c0149103500010503810030a000c081d4051058010107813002240300c4070b075003041c0406d10f9aa028000c481061038a00005611600f480708461075032040c41700d084020607da031a = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 469215998 1250 469214748 469214761
    0x11130e041205090102191b290d0f02030403080105090a0606170403230c0c041107020f19090b0a0e040228241206050d081c02041d 57
    0x48024400e9a01524941c0c04001c04003042d200b80c0c118101c0541940140041c4c04680c070403500c890f106d500e000d080203003802445940700c04410040d80e00300d10683d2440c840c10078062111280003c140c0d0000381c20007a81c680001070341200400062251085030b500000c1804107042c1d2000400d81a0741c403c55140546465078807500c3c04441b0280704000c00f1232103200b00500c0075801c0740585544079000382090040c101c50f02d21044408030616400700340385e40001c20f030720108442c104082e49804030181c03400c00c0400030114170400180a10b01d0001d114450880c2150101e40781c208040079041424484c0700169615800070802600316554030038000c0a112000041038840141d03507600640d0040d01d469450301010001c2c81402c0c440150801c1c1c059460000003915108000102100b0305882f801c9c2c2d501c82403c0701000b0b00f00301c1e000d00c90451031414400188104c0c2e0303441c001120f099074058407485e07076200360320f100c02200b640d0b1501810f05603201081c00108400c011754140c66907101112264101d54401 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 469217248 1250 469215998 469216019
    0x307030b09070c080c070b16060c090f090c120f0905010e010501030803060d0c05130c170c031833070302130b25061e060e0601051c1113 60
    0xc44804001583c00501d0101195191004040c024102d400340da0110b5294847c2020a900001c03004030101e2500088105100c403501c281000305503076150000429180400545060700d043c0281044c0b2980e50b240076419501500b40701d0a586002501844600d0203600620002d142c81403094440d5400d049007000c00c490103118040c1aa9804942c05040d074503500c0500030b80400c6c030300c01110510702140f0f011900f5a00d600384c0a41c0711000c100081174400c42c00c1402006550410b030811413001038071080c044038101038425070364410301c4242c511a00d009803860b01450416a40e01404022f502d00459100000911916000d0701da000d046210154440702804c03422407160003c0241480c00c2c1c0801840021f201000500760502016894410420803000380114040c6141e01101d043e0355884041c0742401d146088090064032400040042c646405200e541025000b0501410030600040c04030407002c0c801049005080180d4003040350038441c0320740004681c044240d0a00e01c2160305400100200708 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 469218498 1250 469217248 469217251
    0x1d04150f0b0910030b0a080a0c1502011406011b080301080a050f03040803250209150a06050f07121701030501151401120506120321090c01021506040f060b0307030b09 73
    0x5403030344400c143c0c8003908800620328500416480010440c000505010070841609050700880702c00040c00c1c031301b0700c1e215502d1811910103001d40e418503161484666138410035550001e42800c1545000034030110b20852400324000061002601100100360000d00040c4d0741c010070303c5041141d0024829043d100d6807401140b0902d4040e178003c10901c0c4100540c0b21200441641c01c265441c4411415400a40c8000007110525a040d00ca2415002d02d460300d41d400c04011318240c14060b14040c152101c00d42a880307046000f0340240380c466130403500706104020b0603440d44000d01c0c0401d002e507143d25050f4081c0c90308a035055140da10b41d480101d801c10b00611050340c0020140c50b9216003400c1c0b40300000261900a108580c4001c0d00b210404014009100a045064800540c03d079a000002c946c041c03088405040031030790b9807002041c3e4141c0d9800241000c030400580d0010842a0f4602000401402c04121140d1040d820664001120301c0c038034001e180030b000903440a001044d501c07814031107951780 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 469219748 1250 469218498 469218517
    0x60612012a0923131a04090c090207080304050d050345030406080c120606030916151b05120a050702150318060907061d04150f0b 57
    0x3001089a028480d000c0701c202450704141030682046a481410201c03902c40450011281c80c3c40c0b030310030740c0b851a000300300c1e041242c03514208101169400442c21000c070001c1011501640c0e4912681c400d0000c814030440042880c51b00540d500d0b012860b04003410742007690120b0712445103003000341c3d14034003590980380328001c10305400c44044540801e20025440c2c070050300e410760f440c1540d15075210404004400d00200038100540d0354034038210006007101c030010900c203500c580500003400e5045901074480c0e045503044035699207946842003010f050240c0301e14001e1540341852000140301ca00c040e81c3d1850054282c480350301e0144071422440480b084101c0080c41c5800180710b5081d01d40c00240030f04030b1030615151039400e11810344d0101e000d044107a03c030b107915500c0c040104040f48508510b07a070545840d00303010305654141140026616119405a8401c1c4424498040120f80820904466105005005201c0c035000e01c00811410b02c3d4030300640160122002c3d0205114020604448036280b = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 469220998 1250 469219748 469219781
    0x5030301140913080a030209041b050c070501030e1b1305090601060905060c062e080102041707030c091e020a0c02040b120c0910030b0702030d0c08090c0f0609040e06061201 76
    0xc68003004038025807022350015402a500c810318809103980d19140151000340303886950f0b0707894411407034030f15100342640848d04160a007404000101c0020519158514000e144005084c4804c2c001448507202071003d030002c0c0b841c0104000da0028001076240c101c55013034a40400c1142c8a500740801403042c203408216991001c40800c901490b010310744460509000784441210030710381e4010122601907440842180e4004c5000c0c88804e051240c40500c00b1403450041600c01e1442d0740324102c002c11880362041450381c82c480b81c060905403c080c0c000d010380c1c27102d0840d50340742d5004016003a440d001905a00135460440420b020b1b050800d0740e8054034943d100100044c082070010031401440c010840344c00c101803202c0010018415843c098081c00d442c0e0042c5845290708401d82e401c8907d402a0101003224040512406c0700003c21903410082003a41d20301d01d880c0d040c07004103256220710b40c0096086440d100b40d140c0f121801280080c0030f5103049a11010200140ca281d600b61a402803030b8244a0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 469222248 1250 469220998 469221007
    0x507060f0b011b0c1a04090c02071d071b06050a060b030c0f07060e030c06071e0905090a0b1f030b0a0b040e0a2004030b0a050c04060302070c030503030114091308 71
    0x12022968144003038884d0b21071606080d110000198502e0840745186042500440c0c144800c2e1420300804c1202e135014801820300520f005a1004405540c401605a11480d00045400d041c4542c919030700c001c507540790300701888201c1e1520030000e10084614120451810b20007191a014050403203001d051608c00c02410b283d4018000413855001000c1114626510707030b50701242080520103040500942c00c0940700c80c6c80c142d41d01a081c1d412005824208441c0260070000a07070304012000160f07401030301c800350a503441c0b8400c1002405062540ca1340800c0c013141010003581340c184240300394082c0d03a50500840c44440203100c40c0050754024401c4c0d45005020a005403846810303581e0703101050410102c1c3c10b5041c58a103000c030512050280f41c040c1c000050600600040270001c03500400c1d581d10030009407520b801a0526401140101020136400003000028445008014005550428152941c0e540c4d24841c1041c1e87c0c0401d102613000301d0001c8002489080d541d00c881c4425508690a285030 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 469223498 1250 469222248 469222277
    0x50423130209030307060608070806070f02030706052a03270d0509010c1b1d07080f060d171b060c0708070606091a0307080d0e0402031509070507060f0b01 68
    0x80e4202c2d0a440350107100c00d20481c03011803402d00400c8002c1c01a0350141000300e0a10b0f40b81c500b0020010b019406000d20241510003480e4000119501c107900002d0006442e00c900441d100312000c1121a0140e03021000f07240044800c60034000c1d80214a020246480c140e80400300156042c00089244459005542001003007030040009080c1c0450514000740c103010680e942da50807107281c03c00c0410700060701d2428440c00d030880700304c504183c03540c40d444202c0c1d28018074000c0c079030b40c0f005101c050f0424188003c0b44071a00e60803a01420b09500c00c11448c21051441643c0e40a60006140b581300c1218450845101000101d0118011030074220320324540001900c801505034800c0d001251240d599100006008200f407107056460b248c000203411024181c4400c1514207240b41e007102d104be0304082d1040202c0341e08403190982e1400103407030250f100e80e12a10125060068680300642003482202080a42e0f41d2000c010010244111006c22914488169803002ca81e20025140c1c0410207a90342400c0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 469224748 1250 469223498 469223501
    0x1e0d1205060102070b07050a1a040b061003150914010e091509100c12110a0f120b0a08030d0510050105070305070c080d03020409061a03130309031205042313 69
    0x14400c1040c0111003070145d07035180110aa0b888040c099543d50000c8540d4010880001401070f10660291482000c0c2d00b459111340009204c058090740c42001c1d071840030710710316000f500200c1c442040b101502c61000c0c0c5d90340b0705002500c891180000a4a4480004500c41c0c040c804d0700e90254a241c0018029440125403249035802d024040043d01d200d1000013504e616034501410400c0e5190740d843c55440d03031003c166001980c58000c0c01c40c0c4003c0051200390209544504102c801f00c103a86400200441c40002c854000c20440d940180c00c00a80400032840304000002043c154040c90380400c00e5640340307210354074801424003e01b40000d4040102d000481d2080001c1c144850140301080c0020b5554401180b91407254120b090102c0c0d00071800300000c17803c51103003c000303001c6913607107202441e1082c0317400c44903100c028852000b201281e4500f00a2603c10702c40d4074061a8030007414107600f200b0a070060000e401030f10a4102d5010b60717240040000d00710b500700c040446006444403006c0c4004060420 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 469225998 1250 469224748 469224751
    0x901120308400f0311160b0d020a1407030f08180c0d1b081b010503150103110c10090b01080a0c030213021606060801110f0d0209211e0d1205 62
    0x40080700c800c448003140980d00f0700e0030b141c1e1203500c1d2500b02500103c00d090030300d41849031007611138003001400c1001d002c850080b11010203403281e00607501c2a0600b81900e40181e240c106025154020943c80c04064021001010943c1c082d140d810050b580c1c00402c90186260982000e400d80102007082407d080c075494510009106411407010100403a81b040e0480d074140e8850900ea50080c1703000c03070403043c04400c3c0d80a000700030701c1c203546075240c441004000d440694400e07504041d641c03022070042c4158101559009189042611400b2901300203460140c48810b0050b201c0140510000a4403500050119121a40851201912483c5d80c0811021920081d0008491b517000c00684403010840040611807a200325400640b403801c04e41d21500312140b11041c240781c22410002c450201049406a600215100b01d0241c1c3d14045000803d07102080105c1400341c810560b5455400741c1404034454a003440400803070040d860b500d403c1c850399841e1aa00400c0070460f43e44042454040540100e03 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 469227248 1250 469225998 469226101
    0x80403080327150604020a0e0f03072d090204080d0e031603231504080901021504030302030948030d0207060f05030408040e070309020901120308 64
    0x150040072030b40070b91030305012003a4001855007150440004185812200e503130003410a40381141011007000c0003528000d400c6004900c00e13082c00c9079400c0156020407544003e00940d4040326a6001032190300d1513103c6058a5444020040100c0441e0502c250700c00d96044852030002880d20368440b4074241d40c50030441180302c1d0140100132601081c1001d40102000441c4200c110082c4030410300c0d01e000700c64015000451440e08a074022291880c0014080c503000f82c0c010302c507039907285c0f52840183e00d000451030080881190340c401300018181c142c0d010f10311964800301074801406035504641c0141400c0b00d00301e03045080c0c40c10b00901520045c0b403246e107042c0040200c0e40d1f180307000340b00203371074000d0741003c8400503408268240800365001c00b10b214250f00c242401415400c20303542e40724060145015004440f0841c10003d0352180c880e402008116401600080082d42c45250100c203188010070b0640c007244600001c210064801c0b03812042d5461500385e05020360703525111f002041040100c80 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 469228498 1250 469227248 469227271
    0x70504090809010c060608060108150603071208161209090b01030c0503071d041407090806010303020a0803041e030203040602010605031906020318030a02060a0b0603072010110d05130804030803 85
    0x1203440c0100704238440c040d041d4400244002d80003007401d03600d02c810040c0f815001e03800c8501c08001401802c041c9401d0745601c0b61807940c485650312060074170701080c07090141094481c20040320303c842d00403606200f1344820820a0200c584034100540603200014000c2001601c1000051115481629034030790600c2d0920300581000c16150001f001d0f00d4441002d0030080c45600107005d480743e0000215401000d0b0100030300314645c915240070f5240c180820b8041c252420000010b010401c05060110601102040c2d09001c1e80060600039a640c1250240e01c2c0550b180501c0450a85000a20507089240942c3c804405004a50390040603401c040c1142c51901c00f044d00c5e0345041c0e00b0030301c06030512403580d034014007540c6001480003003900c00c504045d600030403080051154169000f4040340c509a4548024000418210f40e29844c00c1c9501d050000d41614140c003052801001d14010b011103d110f003c240080e403a00c0d9007600c12441031a50044c00304904000801c0091056005907030b015840440 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 469229748 1250 469228498 469228511
    0x11130f05010801150503060118090c240f0201060e0112030c0f150f091101030e1213030b0109050108030406110a0b09060a0f2f0717030108070504090809010c06 70
    0x8450094890a0304100c0150351212805400440c20710301600042c08101e00401030307940b40c01c01c4010302000d03550803c5a583e4440c4070f070500303000c070401f0010001e142010940c0113000c000c0c00600c0c4e10300d40201507500040d1501c40c02c3e000c002d105000341d2050f100c1212051a07503918126100305003220710b200131018020ba102140020414480c0c1001659000f41d2000d014201d00307020350b500b16009403544019451030204004080742c80c0482000c2d01d00000c0c04e001403418171010340d20740b4000900c2054441c1d07000001d81e10641a0030200d8400480b80f094142d404181d03240d01030b420076a0b2090003012341070740c400d00c4100100b84c0305540c1018034540507829240003150300d449448100704121200f00c4603502000c02d00040014602c1640c3e01c40007110003c0011710220350140307a1101403034503081c2c050f10840440700b034141d42c1041151036143d449541c13011000b1615004603542e4109206550150042c8000055103003403e000d0a031321250712107640d61070240d0318001910f070000c1c440d00c1074542c0b17035a410 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 469230998 1250 469229748 469229771
    0x105100e24030106020c0303030c1614010f09110a08030a050f0d061410020d0e040c03020d0c08040c0602060c0307030c030b2110090215031f091d0a1113 67
    0x300810380784200c0d0594a581e5814003601034986505031752114001e0b0f00030400c0200758001002980e01000c034003601d00701c40001c103007025810001807000d00b80d459407900f4a4104074084c2da521500c80103108e00d10703058418841400b00080041a03100d0b0142a4004100b8010b0b0244158001c10714001e070503002e9820b001c04142d0080403155141c10483c4414140b0000200524101030301010414091005000040b15060020040c07111684503a010300d4036100c00740700da103020380c042d40c40e58009040100504140100024401c200642d01520030407c0e9620102e00d0a00c04074a0034403480c2c85000c00c6142d0345418808038000c0c10016115000c041d03441c403070520151380b80304a5000b00d10800740080d0000b110000468240305100c09003404c00307881c100144c03005032542c10310f401c403603060140300c04c0c3c90359a40c5070301c0d4031600300d038850082406015203408208080c085c1d101c02d00840728042d50060303680e47c40c44d443d60b83e40c5007084060301200803504008402d151a0003140303600d00941c04042483c00288 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 469232248 1250 469230998 469231039
    0x50a03020717010e0a060e010f150e07020d0f180b031f090c1b03170a050702060615070210140c07090e072102061303081b03030105100e 60
    0x110011801a0080c01c01000b42003030b59140050368504020080040e82c0f100d4007242ea0760301c00300b0001424a621002416500042035003c03190082c1504400e0151041504040f10603603107034010b0995042040c000305108a100091058200c245c90301d901c000150f074030078117803005042203048800310310404001081005585000c1c40c002c00c180c01001c0c00c5405c528000020500558020700851450103112103006035110300f1540403030102686500841509080807281000c81c484103407060317520101400004000c0341d20051140b0043d6099884603120042000784154204904030090201404000098a4030305100740d0408440d00744a28954140a0006079a4100c1c911450a6800a401c20825020349010711100b0003d90303800740c00c9e0b5034100f0410307500c44001c414804c0b2504401d0544002103440740c0e41201e80342200341c0740da0100c00c1c0e52841c180502d41d000f9084107080d40d4000741001991800001584c1c1a1070004141038603403901980110380120921040381d50000080300214000200e0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 469233498 1250 469232248 469232263
    0x20904090510050f0601091205120301031203110301030b06041d0f0a020307080a02370e16080408090f03121303020a060c0c140316290f070201030b030a05 68
    0x41d0007070502c080c2c000700318038101d4800030003080007030740c1040420489030780c0040c18900b620119114016500075a0505511701090b131700140f0f4000b01c000002100340441c200d103880c2040300301d540034030030040148501d0b900c40c002848000c010710806000300d160b074513068100f10b201d121a42074940070341386480c0031607180c0800b200d00c8000a40240501106604040c011707540378154400042c501d4210a0b4007003a001e8040b9002d0000c82e4084032a021038003000c7d80c03100889204800089a001c2d80c56410980c0190b4080d5a4001003010010080c28094068078941e0700c684d030840c800300c0c02c00c0c1482003800f6103c0307440f100b9154140a28101ea145081008001d802003144880e01d100784641944140040340e40716030001801e22000c214500c0011b03001544206c10b84001602101248030b810300864600740034080c03940f001c0080484041041100015411179000b00300c0c2d480740d05040e0702c40084d0203510031200130b41c40e4034204110007400765000b600903030580da4024046618a0b070254480c0e0b82800e90 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 469234748 1250 469233498 469233503
    0x60e1507080a0f05131b0807080d0806012607090f0b091005030c1e07020904060c08130503040b09062109061518060109081204051c0302030d0e0102090409 68
    0xd540c062120103240b03440b69624890307141d00c0400040c00d000c030110101d0013480000038013051180040502c403286100f41a00185405012114916220086c45880f20128000c020000380c0c613000290746984148031045603130490b01c0b1000d02e0304103401100f12415100070100c1c02405800c0300700160829002a428000b054408000c3d500d46420b9001c100d080310383cdc103480c0c008101050062100001e03030700c01200c003066180203900710520f03048003c810f258001c60310040d60101c3c1040400c024440d007038016089028003503403848003542e2180348200691415a030060300135030060006104a159110040218840040c8040e00380304044c0300b006c405804214000345510041410320100420401c0101d40084800418204c0c03003900d9000b1401500500407001d45140c400008603c8503401814840c018042000a84071074010a0790207200c04e078410f100786401500c070050100c80c400b000c0700c0c0003089a545940130f50300e405400c601d150043d054201002c0d01a541c01c202103002603581c1d1041c2c0c90b1907031 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 469235998 1250 469234748 469234757
    0x3040312151d01060e01080f060a1503020d0605030f070b2a0d0f03060b0f0304170307020c030c041512060b03030703030f1a0a0b0703052505070b120103060e1507 71
    0x41e015981d82d00d8011042c0e201205000c01c0407620041603802566143c0d100900c10312025041c0d85142c009240021982e100d4000389281846100d207055064000f81040046140c0900c28103584100303141d0344c0e400b060ba000c1602c0e045400140030141d00c2c0402402c140300040e405804201900c0040e0900c0c150b0a00f1300d01003680803000c55511560040181c440380180b5003401c00c1202c0c903241c40c00e41d407807041600c4416200340010004d800c1180c40d10350045201290b000c1079032a468005c0020390303100d4006038640c3c0300c0c4c0700f4130b0500e50344c51616000e108080000d2000c801c03400e07071403c0c9040b41103041030102190041c1d1100d086d00e209440400190108900a64001c10614284110f4008a4611103d0810082d1070715400d1885900e83d98078081c02c4481e4400030540e0380301c06090031102d9000350004a0000f1514107400c811001d030017131507650154060750a448000e51f440c640000e103880f07115032010912000100400204119900103100000b2607802d640200c2c100b40d02c45540580f00310b0304980881d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 469237248 1250 469235998 469236029
    0xf1e031002070b0f060303070209070302131e0e040f031b050607031418060408130902040902180d0c050d030507080307080919030e09090114091b0d02060304031215 72
    0x48085041c041d003028104c03c2c83e1086040242c0801d40302e204141000e8003400402010408a07403081e411100040303043c0646484070b64983c882036400e40c0c545694820000d00140700421050004800c40d80aa0b03800310581c965001d15560503100540500e0b40c01a1340e4242c121840045841481400d12900042d40c1c00118020801e4554200300c201428444000c03d44200d1800c800c07034000b45480d013183d0440210b075110202d80981500070f58581d0010008203002040004140140d41c0241040000710030042c1c0d01104c054082c4001c090314280050600c8007c14410405400d09001204040d03000e4030b0902c1c0b410501d80c0f03a4020981c0162007110004140204100109405000014801c04410561020b40b40705031001046007403a0804244141d011002260008009500010311400c80315204440c1d0300c1c0110001e40c8591501110740118036a0001501c1c0500d03007816140109540148400e045849540f8111034402e05038016194450740d03141d1604d501002184c00d04001c005048200d40d55 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 469238498 1250 469237248 469237253
    0xd03090b0c0a03080f0603060f0a0b0303040305010e070b03040209040b090c1e0a0f1d0603030d050903030a0b0402030c1b01140c0a1115041e060908041d060f1e03100207 74
    0x304c2000401c01480308030100c1c1407140590b0007050780c54110010303000c0d0440e42c1e200ca540e0f10000b008030102466140c40005000000c01c80103421840c51058040281c0d4442552582c49441d1807000304e40007940003200c80002400075003050503080d0032032032900031525039900600c0410102c9480c0d001103100100c03245404005072802d42c1c004006045200a110b81992030403550f0102c8540400211506041e0304000807140e4400b00300703641d0007484866003807026040c6026207588a50041d0703400e82109040030280c00c10340c100342c021a030281c4001c00420f89030020804441c100a8080781d444060b654a80e40c000941224601400340107510700c1c00080c1e6902d602040c09000400640d00e00106500300202d100e0004110020381079005800c0300711034242c51817000c800400c004019038018029403900c0400d00034083c0c54000781c01a140c8103403045450405d0303400da1464419084901c1039002c1030507800110036081400000c03140701032000114160f40740c07010001e130405503425950990650b010800c00203 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 469239748 1250 469238498 469238507
    0x807050f0d0b040b01020c010207090b01121508061003080d050a1b050d0c09080705310b040e0c031002090402040f090c08060108040302120a090b070c05010206060307050a050d03090b0c0a03 83
    0x131000800d000601d20b000481c000030792241e03090303c01c40f48841c0d82d41c0d50426103640150791108040070344510802c1007101c10040801d0f900e513107001d4000c00b403080d5400584400021a90305099940044905040040503054032001d0321000340040c1c0f410783c0311038020080c00181a181144040d160701d8081d151440300c403640044a41c00134246080003009035040001840106550061f1078007946c090303281d1646031403140c400144800402244607688203140c2c0c00508254841885a50211400d102421754140019650801e2070135056158004d0791080017140f00300d43c0101041e032405000907003045d90310024181c0f00005581b104035110345440c0320380401c9074000703940d0f0341c0a202402c104509003055100203540e01c50500146e12081000515404494000c8081d0030007040b00c00c3c0066aa024945884041c2c40c0d1544160350142c0702d00030105040b480c0100b00142500e201030035102c240c515103020482241011101a003d00c514020040788a40001c4010700364960900300619080070f8a1070f0042c03 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 469240998 1250 469239748 469239761
    0x1205070e0a06030803010e04060b06180f0d120305040203010f020a120608030a050a180f27020319111312110d031704050f0715090503060112030807050f0d0b04 70
    0x20780032440c02c0401d00000b01400103690544400705943c8496680b40d01e041c5005050203100e566100c4030104024482c810051203810a2030000c0e5030024100001000f0b000b010340d0703008801410400d1080c0b0380c0901c01e1003a40100da11500080001c56000103007010074007264003c100600014a244403448106411800303000010311203140203518011f0011401490760203551164400c105900c208841c074556401015800b40080c540c400412983d90b40490751f610b4003c49186803660340240b000d0201e44d0350b510950b88182c0c481c10080320845004a400d40050003000480d00940c0c80510005d520700e03003c03007941c50141c0b0340b06445030100b56403418503140400a1485151041214108190000c1c0d808401ca140d0845c041c0d86000e015141e41ca05681424182d40c2c81c03212620900c80c00103108001018149050711103520341c3c4006076110401d040c1c5840090141c15a034004a051203400207100f03d254650004103407811a05103141e0f42c03140c0b00e030381c0d210750071200e00c40340c80f090035070283d241510591 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 469242248 1250 469240998 469241011
    0xf19050a0b09010c031404050a0b07110102160605161203020a270b0c010932060408031b0c06040c0501030b0103020a0815040216060603061805150a061205070e 70
    0x100d082c4024500020060310f0300d10360040c01c121640d21044940211042a200504001016090190f0315a0362000131508040e8050325504c0c0170031a0145254008507250608001e605054962181020b03016030304d03507000103042c06512580e2500040800c03000c1d2040d4410000c0341d6009070340c46950540080800b0541c4180c00403459051011036020b0b05245046422a100dc04005031900b41c0700b829140140303e40e0701d020300020072814140c5090171b8160b004007152840401c000340101220410f0559070f16040f50300500b4918200b0205111034012500301d44120441807149140580562601c4e00300441a10109c444141049060285603014002c55290b80700a217011410701da00c00100419144005d000c190068500d44014425a2103940403950340e0100042001380c1386a0b61b160148c01003007603220a07030344a45003010001040075000a00c0c00541e0b00140100340c403003100000e60b0b008090181c00c000805540d03400c00502c141040c0d8080820602034400342450a1515410705010b01c1e009282 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 469243498 1250 469242248 469242269
    0xa05010203090a020a060503011401030902010311120f09121e040807061206060503063307080304050606010c050a060216150207060f0c020a0611130807140907050403110f19050a 78
    0x1801000d0a410760084482c809133404261061603000690061545021074680c1c032800248580b41400f0304800240200d00c1c21520701156903c40060503111240310400c41c40c010006c11000f40c10507100c14411030030070220818035260070340d280341c40c41c0f0f801465440400424902004d812101c00c8502c02c0200824040c103000d81746150000004866108040b0b55035000c032140c0342243e101c1521403808268003914201503954454507400c3c0480b131600215802c0703509114060009a2a52040c0c4048601c640c0c40307001486402500d944d603030041c0d080410400b80320010300212201181c0304030390302c1491101034100140d03198a60300b0100156807050511403a0a820440001074042d400222f0000031500121300042c10303102540c2011092041c031001c82e0210520600c049001e01d004201e05007100c2880e10300301e40003040c260622290340740850328000824000c0c001080820010b02800301a80170003820b0011050f503081c0010310704200b41101c0b40d43d0342e15100060182c0d040c2200840082d01c65282c0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 469244604 1106 469243498 469243501
    0x5031b0c0a210503010620010c03091a0103120f1209050d080a0b060f18030604030503070906080105090a0b01090f030308060a06050306090a0e0a05010203090a020a060503 75
    0x1029101d0701890000c1d008150792600454229031980c1c2c0f951420341e0f00e02101a01c2520015100c0e011407200894401840310081c42160100c44d22501d000806a40364101403c008540c2e01000b4607a0320500014030100e00025000c041c03406413884c0480042c21480d50071141d840200ea00b00c01c0590508900004000c4042043c0352044407940e01e010310b5030340d020018402d030707505500c0040d0044010892000860903400091004101c1402c0b818158000711012a1a280c4c0482d0140c0005501005110515901c000d85070300a026600d0a952194181400a40c08490142594003180d5031400717840f101da40030b070460b60000c1c542c0010164400c0c0e0789080140400340c0498169210700c01c40c0c40c01140041c06401501d010361400f43c2600307075a6680200c02802043d84c22070007409032003000e105000064090005600c04c89045020b460040c145106120346012650040340134040e0030700 = true := by decide +kernel

theorem cover : BRFrame.Cov 469064748 469244604 := by
  have h0 := BRFrame.cov_init 469064748
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469064748 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469064748 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469064748 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469064748 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469064748 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469064748 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469064748 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469064748 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469064748 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469064748 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469064748 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469064748 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469064748 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469064748 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469064748 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469064748 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469064748 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469064748 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469064748 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469064748 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469064748 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469064748 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469064748 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469064748 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469064748 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469064748 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469064748 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469064748 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469064748 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469064748 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469064748 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469064748 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469064748 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469064748 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469064748 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469064748 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469064748 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469064748 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469064748 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469064748 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469064748 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469064748 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469064748 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469064748 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469064748 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469064748 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469064748 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469064748 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469064748 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469064748 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469064748 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469064748 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469064748 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469064748 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469064748 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469064748 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469064748 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469064748 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469064748 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469064748 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469064748 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469064748 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469064748 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469064748 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469064748 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469064748 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469064748 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469064748 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469064748 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469064748 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469064748 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469064748 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469064748 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469064748 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469064748 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469064748 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469064748 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469064748 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469064748 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469064748 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469064748 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469064748 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469064748 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469064748 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469064748 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469064748 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469064748 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469064748 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469064748 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469064748 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469064748 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469064748 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469064748 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469064748 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469064748 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469064748 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469064748 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469064748 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469064748 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469064748 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469064748 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469064748 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469064748 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469064748 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469064748 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469064748 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469064748 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469064748 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469064748 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469064748 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469064748 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469064748 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469064748 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469064748 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469064748 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469064748 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469064748 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469064748 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469064748 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469064748 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469064748 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469064748 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469064748 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469064748 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469064748 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469064748 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469064748 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469064748 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469064748 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469064748 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469064748 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469064748 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469064748 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469064748 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469064748 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469064748 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469064748 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469064748 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469064748 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469064748 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469064748 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469064748 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469064748 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469064748 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 469064748 ≤ n) (h2 : n < 469244604) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
