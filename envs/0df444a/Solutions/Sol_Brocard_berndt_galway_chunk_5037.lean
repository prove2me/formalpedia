-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5037
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:32:17.856682+00:00
-- url     : https://prove2.me/submissions/c4454e2c-e720-40f3-b46e-96d7c14958ee

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 905755395 ≤ n < 905935251 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 905756645 1250 905755395 905755399
    0x90b06091e0420040603080a090e070e040906020c0724030204030305090906190f140411220e010b07060e0c090714070c03030504150c080f0906070c0807080c 69
    0x44200319001d009940e060010300001c0070201d0843e404991094564900321071900c00070300030810305940b481c00c0c80c040e0b4050808131010a10143c0d0014044075104001c0348030b40065120f42080741d8040f0100700003010592000c42c0c86603401d00c2024100d1108010010152002ca48684e0400740d0621a103034005446c800b1450401d4010081030000a03400000d4411001094034225116194400022001d0301181c0e0300f011a030b161280001103040301106820704031001c185071800350416003800d00c0240c44552140d0028524200501803113003050402c40480382d45021075521072103888001104201000b07a200c854981d01c003180040501c03031907118407000d1440c000020a0011001400704004140081480d0240058101420388030f9440104840714640e10040c80880d203a180e00d8045c1c00c07604103001d0140b03403040898183d81340e02d000d0001c0c0c40c40381c0c3d042608035051500700011040c2d16800580f8441e000281888180c0016008500c0301000c0c3c034559014000300d50401000525000c0d0050b2064 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 905757895 1250 905756645 905756671
    0xa06170607050a1b0b0906073c090e040f12081902030703020d021309110c072102120c01122007050a02100c0203070b0a12090309050301090b0609 64
    0x1200907004400c0343e59006090525078052401c1c00a001d4440703408a102410740d9400e0300401042c81c1003c03452a10070301058440300200c06500d07100e0307440d03007078000c005062050740e440005c0c8003492035503100c521031ba07036602d0030b1088c03030380c8030008901c6520b816901207070702011400b0024200300d0700c0900018400b580d403030722803e14031703143c6541d48040b0319526200e6481540000400c0e5810310035012a1400c07a00110159600d80305a0744c1808098094400c2c050807078030b400e1190548042d1750080f16041d00c130b0480144003a46c180000c010864002803000600748070b682d4840c0005858243c0880001e1007c28003030f103c46e0f51124009405061840324031403845240a11030090021405600300401181e422083c0c0c46085a2070880d2410700b5401001c0d51001030444032803209907000b02c0950326240b098081d5103255603125050503080c0510500e0001050755101c4035400600140c0c040740300c460291400000c1980e4400109003101c4044400343c41236540d800400150b41040392442d40c020040940203 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 905759145 1250 905757895 905757901
    0x14360708090a150216031206050105090d060e010605120303070201050906010617090a0f08071202010c32180f0a03030203220504140103030206090d20150a061706 71
    0x90b9140c80c0c581c0c4005101c00448440a00c41c0c080e9a810b40d48410480754484960440905003e0171100201c0a00c0b07000f1030a1500100301c55110b00306880c42004081c0c400d001407402031365036102400c090f0b00208203540d42c4006c0061a6640c900121800b00c0030030001e1a602e0920440c02401d49100410040d0301c1d511040c010092250710040000c250a4416074a210503284c0480c00703820030703100d600050481e8140d00000f505002101001b04440d51142c0040a200d03c00c070f0000783e00707a0352070501000114000748604001c00c1400c8451046042c000d1020395446900385207090015000200000c2042e0021040d0401030300f04892801168141150fa5445061841d64029503078869510a00201180d1941c0ca203000d003560007c4c1000740200410a0180a0750b1340c01d06000c00c8001d10041d801407060b1808610b070b0740408603d108004240e030b07403a20032180800e41c4040042d02c0759072400d038891103404e505400c1e841025004038001c620f580e0300865154600741000c07408000705000d02034950814014 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 905760395 1250 905759145 905759161
    0x103602030d051b010e0f151005060c0a1b06110705090106030c090f18140f070e0d02090405010504020312040e0f0a0b191a070c14360708 60
    0x501c4889250791900360342e51802c0c25401100c0b2201d82100902940c03c00384101d048082c003050703032500c0d401c42e00d044403003007a260b01d443e4582a605903071448000d900010306000900b0904001d05041074148125032289001c1e6540312031061220692080e0310340641000e21481d036000c4440144441950b004181b19410038000648064040c81140c0900d940c41102d0000d080c0140e0307604000744900504245215a00c96010b030600382c0c00000036000a2800c049111101c61460119004417031141d01001c280e51030980075940311280b6107441d43d120081c0e41402005030307107003001706104a2044001003600e0801d8418545050741c5035614412a00c0203100c14000343e80c800740229808086821800b01c1c984860820b00c008140c0d41940a42148120341800e82c0c003800361142c40215501e000c0c1903024400d60b10f07009080c9004442004007800150001040f450301c41c038200c020403010090429864081540d14107452160300c940510b052144101403095140c586a40d555010700503003401c02e05803404620f = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 905761645 1250 905760395 905760403
    0x915040b032a010201090b0a09060f0507050703030c180b04170a020306040b060109151e11070302190e070917031201060f020f161406070308010b0c10360203 69
    0x42842c0a11807610540c03495a20035008000000d40110648201c2d00f0b2243d0b004000d040048010307542a030078044a900e20405912600303120b2005a901d150400c40255001c030050320304030388901c0400210b42121121301840c1050b1000405905140d103035290b18000070600300345d410b4280e01d1080e4100080c17a10242c2c1340443d00c2c03640310780d008415124942e916030050b01c0f0042290859050820760382c5a01c8251500480c15812480d00c0b2038001c0e2201c070100200301d4803000394030740140303858000580400040c00d040a622500314014422201403680754010580402c3c0221001e0f000503450210801c207604030b0303a0091006c0c415000180d0700c2c002031020404140c02044c41540c040207000000c03201d100d0b00c00c1c000b2045510a010982d11403098410310078500b00018020614501450070201440b49007180458101e1a03140d201c0c0d0f015603281c0007690445801c518044001ea002d58020a2548880d5104038000303000c05c140910300300880020401c8100200c00c00c8000f0082c18449034802580c1c0000b = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 905762895 1250 905761645 905761693
    0x18110d17030c0705190b06090a2a1b170901090b120f07090e010b070602090a0306060810091a07020708150f0a0212061c0c030b01031b0608160e0915040b03 68
    0x280c0c123a8050f03100d01c00101c0050410315080d00a0030900085c11848034130b2565000b29900341561a510902c41c0700d84003010030601160001c10340e0a4100c1090700142650b00500595441410880d0b8203d03034852a0001c0c4e68010b00d000d0340005d0403241003000243c5103600940c0c0164481c45c144505500b04030a140c5001d0040c011901d484001182c035604100300750301203c0b031050014002e072151907580c0c507101d40030b0065406855074034040ea10765483c00c200d43c0e1243d03412683d00003c00d1000d000c0314419080d842103000e071190341140a080404100c9420411021001c200000102862464890a82d13140e0100c042c000f421524010000c1f002d40b61011440c07941c11540403550100c40c0090f20400300d40c1941d1460006284480303141d000404e111206036410304913401010720b4134010752070071031407552030b2103d0041802060900700401e440250712102860041c7c0542032240c5030b0001007000801788801101d203c54090207424076400c0c0d5041600550302c041340150300410505400b01a44800c02d1658 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 905764145 1250 905762895 905762899
    0x91011030903091e04150906080c1e010504080a05281a15040c080f0c040608130f140d0e010201290d0b0403050d18110d17030c0705190b06 61
    0x190518641c2802412510300450b00c005004100c04164000003903920b4421f0710500303154914010300002c008001042044450b04c00038406105007910203244643c03485203a051504000b014803001c01c40141c2000f01110b082e02413002040025001c40320310320810f4100108606106103c0d4001c0b001420012200b859506081405400303a138407400403184c2002482d12155225090407440954960408083c5004d58420b182c0304509603281050301c611882607224100c00035212200241c0c512010070b44850070740348600e45a84150503692950090100e0030404070041d0342012214200131a08412030007401c40e020300003030100d858031001010030100e80c01404240030300f038151640f113540d680d4450210741c141d109980041a0402e403c004205800243c01540401e01e0030302d6103600807840441d4903250950141039212110001c8051048600f48150100e680c4204081030305002040f650146108400d440c03202510b4101e242010303464080e4510120031100310000c00710b004248403c00203030f404401 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 905765395 1250 905764145 905764159
    0x10c03080a05070c05011d0705090103110904150212061206090606100e0301020f1b010e0d1b0209070203090a0e0c0a050a090b03100f090506100e1809101103090309 72
    0x3e4108183e8403000b00c1c1400510070351909403240d00d10b03040c04060b081d035035181c1000c07140c400740ca4900340810031400303000c0501030020820981119180000c00c207513006200744403003000000c03661024020381c1c000c92404004499200100031041c18880200070a0410b0403008080702d04200c041261180b10103000f0310300400d42004540340050103011407481c0180e000e00215681c00300700c08000d42c03640180b0800c80c0c110b890400b0300b01c15002e0502030741c0b0100c203140c80608010a8000380c25200030f544500035070345041e84501400d015071f481d165010320599164029640d11941c590421240f0768a98014440c500207180901141d0846030050b034841c1c030f29a04109540c1d00740c0040981d403040d40da43c083d00704000000304002d904060900500102e403410031054001b251949103407019074104444c07944c0c004107079466410031503101d1740c14008500001740c50b1ba140d0304800607e400900504a404a0303e40d8001c2204600e51a102c0c425111483c0300003600d0fa09600300485280d45920480454a114080d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 905766645 1250 905765395 905765401
    0xa021801030b01080426070b01050103060602030c060c130e07090519032a030b09070302030c06040506161401090b160e03030406050d0b0607050109140c0f0405040606150908010605010c03080a05 85
    0x11504030002406e8483c2c50b400340d16480e003031508500d8240240602d40c002400c1460014400f4000800d0f141907405c05c8018208541e2550801501da40245104c0107140b91440300000e4042170411015008128968554141e2400c0c5414050075114035003501580c60900d00d01080440d00c0d8080c03190910040459000313034054105001d10194040fa000500140c5e00e010501981d108002154000c0342d100790103030345c400305841d0208045406588138858101000f08614070140003181d0700e55801031b11805000065501070b840701e508407090640c08440c102900e40a02460351411041410303100e00b1881e168002620301004030341c80e4092449240140900419550020360a41d04404259480900580c1c2c640c02e141c140700740605113030101501d00700f24408450300c04503008070303070718012410161036501c50040c4441804000d22000f40301382c1c0d0355980c5e20030108446500541c5a034010b015070390381c0984031303041078070316401c4484030b512113414400007803595000a81c00030080e5a0080090000054640e = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 905767895 1250 905766645 905766683
    0x1180e090102071416050117010b090d05101e050105010203120414011a040516020d210f05100f0302090705031f0f170102070c030b090709050a021801030b010804 71
    0xb004601e0300900084d002c40e00240340c1c1a0020302c800d44a179a40b040000790711340e90300054521407451002c0c0080d0072072401c0141310f01d00c400340040207c2003018004000002a94030b07224100003030001c205044e19120a05408003010050380c6241c144851201080300f5407501001039540c3c8980707034141c0640d01143d40041c003488548900c21035248113a078000d01c84030201045a0120b038001c011034034819440c0c003001c1151707440300304140c000d0701c80250018500ca001c03900e400d80c2e4070400b010310381c607500d0780c007000c0108490300c0350149003002041104c0c081407a00b03000d40c0b0050244e5054200c400c00c004c0e10901000560f0300c221020b600480182440c0b07559464014812140305100801112082c89d03407540011000c00f0540844102c40c3c295090024401c480886a070a0b4400d00c080500079800440d0700f44003260b449100d41c1d030050800d004035000b1541d1007000e402941c00c1121101451680030a020461840603030903080c060209103020045450400d001820b80d0348082e0003e4000b10b91410501510 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 905769145 1250 905767895 905767897
    0x1050f180d0819110105090d390302070b031303031116050d11120409021308100f050109020304031d24190203040302030a0605090703020a080d03060501180e090102 72
    0x11500001d10b566561641c090011082d451582c0c1000094004c0322584c882c0601840f8290248400001826001ca442002200d25004c40080402042a080c810501c29102031540b4504800b00c000954210310036030601038108132480e40000451074041041001072581f1002500c1c1c4141d15040000d8540704400c41040d950051614489a0400e484120410b205000610310300c003a1040d9181d8030007080080006854102c0084503e9000c4410301c400c2c00600c1058000c0d0151030414148240301d107640340d010728034021080c00f103c0340c030320307521403429062003240c0c002c06000d408412010b5196050543e00104040d402c1340503800c4d00500c81c424040d881ea20030082c0d0390028982600340b4585502c5444000c02e55002019000b00c5021040d550001b950020003558103c1c0e8000b0050944005291036400c0908001446005540100d02c00440143d4600c134056000e04246801056a403209501c0907045030540d40107103062244e5030b411312011459148230042501d400c5010311606840c1d501c0f01d1406 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 905770395 1250 905769145 905769169
    0x30a1b0f0f0b06190501090603050a020d0501030c060807021501090c02010603080f040807050906011b030e150403050d08191509020d0c0813050303060f03100c0809010b01050f18 78
    0x1c03010034200101c00e00c205840c0c030702d00400301203501001042002c903281c190000d45100365030214142400c2000344c180030703901403a80680420703c00b40c81d00d0007002c00142112000d030000c0f80c055048080a1040d13545c041403440c1c1c0209070b4001000e281c80c007a6240c42540c0814464480c00d651140c4100c41d2140c802c2d00407000a40d400046961509401c040a040c2c5400c6809401c0c0d4512609900040300d28000c1c0030300740110410b03119080317004c13445a0200e0035080100b00c00c0e824040c10041103086911014868061405503c100946560440c13414034100b0303440c0745c000030800840b0000d00c503a1a0000e4410071103c480c01800003120030070f080481c5d44090301503001c4100d40f840810464005d04c0503411070b20002c038aa940d4100c0c6544c4200d0112024400b0100180c06513000f4400514242851010904000001001c9a0084040e040b004064075411110500092040420f024070000240a0710485142c2420094101401c1c030030254220b009181c15840141242c18010103a501c40d040d1241d0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 905771645 1250 905770395 905770403
    0x110a0b040f1a0a02180102010203100b0c120d0b1314012601020f040501030c090b2a0604111c021503061513030510060308030403030c051b0717030a1b0f 67
    0x1010700c1c0104150000390401740012811250420b0070608030340c410b108403032143c2201543c0302015800c2040c0028035800c184000b0b6100d11500554401c682684005031800c0d0384803000200c2e510301c041061100702401801ca88a070701d824816074450b20032030b481413107040d40e02c0400180203002c2640c2c2c50611000904c02401c0e225407001862410b40d0f02c1c241c0c003c00649000707880c148004141c0d50000c0350601e180f40304071084001c0034271003800405c90005100d1504001c2010032010200711000260821505640171244007141c0b90000e5140d0a1800480100e544555500e800c001c150703801045201e42d00981070000da11000000034950b913101e20300c00c4548041d01c0009500d50017032460300340c81076841c2d01040d0350307520039107207119840b80d060701071001500d80c01a04641141c440349d07800e034090040e000013801805414070148460720081219100d20f0140c1c030008241c82450190803035142c0e81c030740308511030310341041207081011900403065400c880c0c2c01e404a400c0051460802c07841801a4010040c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 905772895 1250 905771645 905771693
    0xc13090f0b040c0f170d0503070219030e04110705010b0f030c060d1d0f0c04200a0936020f030402010c080919060e01090e15060702030f060403110a0b040f 68
    0x81703000d8100364401500304406030308503845401d501d14103684c41c2c0400c48405005a000f0703074015081c0000058910b00326803107414842d404080520014003500c02049800d1a10800814140c081c020300340500b00b060801076072804005181d01d0f01103601c9080300360300c00303018100015080d2000c80751072f486100e030800d442618100d54400d42e66070715110542e03808001481e220b4031b682141186024401c0da884441c000d8140030040304540e2411010b07800000e186020b1007030540c0000b601030380c5030b00f18405048401c688030700d0000720051803030745105282d032066502c18414401c0701955410036081325001030302424414011102403524407118401e180c01700da0010108000e004030a601007200d0400c0c0c0f50f0548a4040f1091041d0044600c11503e105410002072104049010101820368401c41307490090005803030140d07140c01081c9000604801c02c21141c0c421000c0009040d4004c0b0222020140030340a4010429540c90f4118890000b42010f0448440c101f021030030400380452040303906005200e11 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 905774145 1250 905772895 905772899
    0x91b14010e1f11061f090504110301050a061505180607080d02160309060e03070b03070219050c0f090903030a020d090f030e130c050f0708040b04080c13090f0b040c0f 73
    0xd00c80080c8022659152103010003080700105d12140c200c0404001d810040c050717524021404018000141082c1c9540304030160910240e1401c1c05220f10540d80880c003c1a0f440c90a089508410f40b6054254100401403107461488222070001c000180340888149413103001a043c440c03103610036141c0300541030384006440c2800701041e0700402c0b1001c1c000e80383c4100c0b2940d9484180c4011314210845a410b400041c03040c010018142d014607081100ac1c8115448402c4852980d08402c0819800340d0f980c0e030004500b060586000c0100c2038400c0003c5d5810f14050911804455807400080e200920483d004582184208906c0c6c0c41400d80d6500b00d60314481d100220308003e050045200c280c5401a41a224016512071150180c03901c0000346984091604c0001569403a41d0b410140e02100e41180030000001c0d8000050064005000d201001c0c1045c1c42082042051503005200c404440f2410050110f010130f1450841411032030300030380e600619070343e41d140540b19134250307400081c4040510040 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 905775395 1250 905774145 905774147
    0x7090f180606030c0902030c1209010b0604030309300b090102120a0506091506040509040c0902040f08060901090f0201180b0a020f0105090303040f1211010f091b14010e1f 75
    0xc10b0080344e00504809000c0c540700c540e0b1109905c0304945041130310000300600491901032010440d44a00a000009620410840000e070554044d0f030060340001c450601c140a0b100f180510b44003107101c00c03091225000301e404ca0401649007e2080540403491a0000550214013901169030900904400106510300800c01900910f0240d9075940540c0041700040c01c000f0ae8844002400040248114242032401c0e08000705520700078011114074602e540b0000350401c2e00d0000c0c0020b02501c2c20701007945410309180925004d801070521200d6810010010042411400d4800c2003940a181022203d8100d1440c42666156580030414160b40041d00300010341d4003103040166403550900034041a20b4005409a590005890140150f65102104000552540c0a20b204180303a810480010054000701508403403a09441c40100c0c2d4503070003244100242c0302c030404800c50a005a02008a06020b1012001e410310503125041c00302031401300d8010341d94001c1029074801260080c244c06042404 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 905776645 1250 905775395 905775401
    0x1806160e0409150e010513120807210617010c08190608100506030616080c1813020d06060809030d0c021e1f02071a06060706060b070303150b07030f050c150103051006050307090f1806 80
    0xc40c000dc031060f0080021340c0800180202d15581c1c10559920030a62101c12001116035820f4400401d2956140c1d00060700100a1100803040400290005621319002051500b000d200818040e9000c900c1c1c11091556038005c1d60054012211000550b16120200041d55002001400b135690015811458a000d51210340003010141c00e00f003c00e1000c07aa507680261204001910700b1862034205000594903c006940581e40d9481c85204443e641d80e101407550303224410168104600344c2080140c40261060f445102d60035003c0a201140f9100044d00c5800044044045a100e00c0c0c0384e00010821325a034039030075035140300d804c02e404200380c550314804a11b040c1d000030821030209040c00103504000c01110b071040100d44500c51020f00e0707c1078640d012225400940c8040c014440d007070001030144041086216500788a20a49240d01c0d41103080152510344c80c004880761039800e29805101707945003c0b4480301250204003012825020b80e01000019146158541044850800c89003060003d650 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 905777895 1250 905776645 905776649
    0xb1215040512040b0403060908040b04080a02010e090f1302011211121501080118060306060b0702010e030c030c060f071a1806160e0409150e0105131208072106 70
    0x200c0e091200c845124480c00c0c001e9214406881c40140b20030400f01d46241c2180440758450b0300744610744bd48a200404081c1c00c150020750590388007018483c1156003001c05406425400c0740d2100c2c3c20f1502d0600348a40040c010a610702c0d00766100500380131a4040c1c2c10500c0f42041207202806880c540c00f10406c81c40d00b1031801000c09250074404280800d160820b420304070342c0181c1d00c01d0700d01c1e800c1c03041080d9070003400d00800103d503a030380d000040070038664820f2001074480e91000944d03444a600005001c00b43c05150244240c02c00c2c0154000340e07034000b8007255994002d481c11512207014100c07009940c011620060700c010013101903201003040ca030140505ca00c804030480c0f511700007002c0409503076070000c4030a44207003c190310b41d04101902840613914402c1006202007015070160361423380349400d4000248041b0f44407480303111815803c0c040e2551107070b64948c481c1000c0308903488100f14101c10960400c203124011340481c2a56204586102c00c1c0c107030050079080180b0602a454000700414 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 905779145 1250 905777895 905777903
    0x6020102072d171e12010e072309031b101b02060309010615030e10020304020303070210030614061206090c2203021005180105130914160503090d030b121504 69
    0x8540c0703650340300d80c3c0319045e508001240070030001c41e40c0c201207000759900006040101070100e44412031001c0e80401000c00032101040c80350a403150450024589011419051442681c1d0903900144041d280d503c024900c0b40e2080c0b900420b2091a80c010700f00954003404060341000c0d0000c1000240c400540000c400c44030310391600c001801d1080d8080f4100c401c900d00c03130f801540089a1410522500da005103070028001802d80c3d141c58001c0d40080c0801d40354a070b914010035110b200030400112445c0b040491400251081450011400c109442c3c180000b00030502c02e00004000ca82003449400c15640c500054141450160ba00d0040c0400350030018403007288076401d1074001c0b840345886901034495048160122a28280a210065855810203510701300d0b815102d21000544803014020b030310b440d2610b1a505d001ca402c20094095050354410304180500c4402c100303100c0c50003400243c5081c0c5010501c1d001402070021780000b01ea104509040c41d01502c146d4400b44048000d0b00e0100d4011b502c070b = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 905780395 1250 905779145 905779177
    0x170705091303090320030f0708010501080c0105090603070908151504020a08060904080c12190e0108010e041b0305031209010507171f030f0c06020102072d17 69
    0x100a0407a4031031890450080c0041c0e0311800c100006020303806401c4182903a103845031500700d081d1000c01d20348082002103440366444034001700f02e450400e209640c00742c22134401518201201c04000f0b0b01521408202c00e000e10000400281701c24030944119019040340e5045c1ca00c0003524403101807050a003a101d0f40168032010600b500c070b500c3c0601c00c8614050858861254540d255010040405e400a109841002c0c0800400341815401e00c010081040003198203600c1c5c42507140c204010071741900071542848166512000540e030030019907411103c4e030154021681e071f6203140040c06000180c1c00240c50b400300030307030100410201002800c049902c0900601060342c0e000012400d841c802d0716034102003900d02040004400400346000c1e480072803034a00ca0040d0441c40e1200c40440150340c405c0d01d13060b55002c90314082000c1503000360004d10721440250300300382081d19050700c00440c500c0d04039002002d881c0c2c1102c00211b012006509036804c44003402a01c5c000130b01c24a0194880e040101c0d04181d = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 905781645 1250 905780395 905780401
    0x20421030f1704060c030f020c0a0c050405150d1416030201030e0a0b010915120804050108070207060e04091e1b0b0c0604030509010207150f110f10110417070509 71
    0x2100d449030118010500d448040341da190394039491300900c103e02c0400105521002c4034441c5a43e45e00041402d01e441134010007840003141000d407541012a04494426402d08043c441618910001154600740441c1c54200c80c5d405403409460f0040f0401030700c4001c0c0074a04008010106810402040b40d000b030700c0501602c40e000d440d01340c9074109020000c12802d1000c0041c0803085141e031144440c0d90000c2000c3e0700c240d03110388002c510064403c1d03088500c55000a000d02c82c40d64040c03061508643e550008118140c10014041e10500920a80c140141d50f0341800c18141f000503100c825464003007250b0300f809140d040c01c045404100c0b20103080114060503400080242401c02100c030502c400201810f155103991b6801c451035449401e4140c118420000c02041034102010100c1a59109440d079003040800f000d00988096a5030401c061540c0020052120700c0d48085004a840b44a1180009000344104140080c901035504192690301c080c20031079074035000014580041d00c40840b01b814182d6 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 905782895 1250 905781645 905781647
    0x4080406080612060415020702150703180e150a0b1b010e030408060c0903010209130f06331103040f080f1623060304030c030e1507080d020421030f 65
    0x1048030328600c0742c503030200000034040761b240d00c2e0240c20789610a1002d86080c4442d00080e582c80d05040f4005000c00c000540c0b03104241c0c000030600d840f00b0035221a40066407418268070350303241c40100524181c848441141d026a541c161500c2e01900c06c1c1c840781a143c60302d49290a449480d0842d0804240d80b078486d03000101c442c000165012200d1260080210303035100f886807111508240f01c402d800d036400f0f110b821280c3c0d55102052840204c0b03100005143c1c10300b1054081598910b0340201c591010f94055181c01c001010a4850741c144900b514000d000703210f2070f0407074a60100c51591481400007040100c2e00b1502e0701c0340c2c1812540441c0440311101a0320030b100340c55008a0b545d000210305140c4d010800103440004000c84e0580780c407801c5d00110300000100f082c1e0380c0112011070000c1c0c0c41c0707400d25041540190315010070a8040d24000360001c420890b208007403140ca1006424007201140d0036460100700d070101d501074900604c130907a00c8980406841071000030801d0480100340e14003003d101d85 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 905784145 1250 905782895 905782909
    0x160507080a0e01092304090807060207080d05060f06090f0d020a08030904060902040e1617010902070506090c01081f080f030417010e07060c0602090904050705012309010809070e040804060806 84
    0x20171805c92407007400c41032101c1008003c0c64812001c07210001d00f031214002207041480500b541500914202c1d03662446041e5a034220750b401030002d03200e0001c40030300410584030502035840c1050260b41344001003040300700044820b180480000e60028420f83c0c00304420b940800035041d12081602d051081d10b480300403030401d0b40624024042480c914000186421300408010381d02c21500d03051004003a03002068094003440260400340c1c0307031034000481004005041103010750042c111406409448101c2000a1218030060b1007001d0214000130600c0c07204014542c1c0e0401028994100c034001e903040e12100c0c0d240d030032521540c3c1c881e10540003200c00300c5006001e511001c440e00c402415100e4100002070b41c0c1ea145200c416201c0c07660a02240d411a12040c202030f00490040e00205120f40ca003100041050252200d05075400e9192606800404013540c2940c040b10401d08000c0807aa440d81c0c8664540841c0307070b0200760303013559a40034007050001a000400a40344655501880c0350380d00f1041c4048 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 905785395 1250 905784145 905784179
    0x40c030204140d031101020a020304031403030f0406200712030605030604030f080a020903100b04151d041a07030504110a081b041d07080105010603090b160507080a0e0109 75
    0x89880b820072080e01c1854000004111548207003480007050451030700c0c0600b217801c0b00d034204025a000040500c10300c1007036404d92448ca80a28000c5246103044403070309010030b002510040070325403220003421a54205004c91410402c6101b00140c58004901306200c00c03046000d6118007103898040c010501d03040200388107104a03010740310011b050390803040c00c444810000f072503484c1c2d4070b500f4030558406507024030801c200034560100c003003540c1c3d17080420001190720001c6200e21407204900d003000300003001e608402c0240d001010008440e80e60b814001c0e6950071582d000c00031506001c0c100545070750168400344c003882c0a0b008002c558141c03401805241c1d091405801c0803a804003170284c20300d20180745983e04403507003e0808200403035100014245640e02041d0003106400c522400d10010b14244182d42c01444e40e442c0521456489813940c0910400c00380440f510303030484409000110340a1000c03200c010381d00502d40e0790358803100e010083c0002c0100340b4103400927030b050350000343d0070300180000c41d9 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 905786645 1250 905785395 905785409
    0x1303060f0b09040803191107062f0903210c120304030c060e0a05191401060f0614120a020c0c09090d030c020a02121e0d0503010e0601121505040c030204 67
    0x850f5140c0d51181050b54100a10110700e104050900302c881400b60f001c0c0f03002d01c80021444540700d4155103000e90580e030002d240341e44007507a0105065071260781240c8604515040c2c030102230b907a91075240030a0500c29030220070610204203e080d802140c540500400021084209070396940712018071941c0f140c0302c2030700c014000464940324403001c9041a0b01a540d072420380d20444181c01e085513030b07050034429061640000840908007001c28048181500444520202c000300708440c2000c1c0c090780c075540ca44c01041c1c1013140a041605901003008c0482d559080b84002c050401d15044507924060350156100a880d4054499000f00750f0508289440c000d010701b1001d41085a0401030460080c030001d0b15240440c070402007400c000d078458051840b0701070380c0d001c05800407070009024215030380b15007041e800c0503a211407004100a588102502d06503007600d00110314944400c401200c6540e4140031034a041b528003001724207030400d000c5c0d01004a95041d9024080e0100c881d405900700e0040d403013012 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 905787895 1250 905786645 905786659
    0x30706140406050f0c010c2c100305091501080705100309021e030c090c040501090806091c0c30031a0402030403030e0616180b0a0c05070b1303060f0b 66
    0x202c200c030f000d680900720030003e08040608200c0b04850080c2540c01a05410001c20203c0c4d104000401e540070714441c0c1590409002c04205001c44040b507210181c01a8000c20140e95a001c00c050001c240984055401c0c035450302030301540c40720645512a2841e01c225485040d0b03070b542c0c100d8079500a025091003a6002019020000c1d0540650302000c1c41551002d541801514150702d80390303451008640c040c04a01402c1d6031076904200024040c01c03100e40204407107034030100422442480005000c0036a4014503c0d00300d00c00c6070309200743d602c038808160050081d95104003100c1c032840c02440c0b4420400c16005000300e1020320340415001c03038001104911040c3c140c0182d4002c01d0511ba0001e5030883d1083c5400680035141403889030034840d040d02c540000b10368181000304150f174072080b9080e4044001d20101c0f101d620f0103c0d188014429411082d043c0b00086001c6424400140940c500030500785040c00d5640d010740300c1c1c03001c0c40001800100c0308903241400c9124180228452500e640c10090112 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 905789145 1250 905787895 905787899
    0x108061803070615050a0603060e01050418060b1f080a1b09030305090d0c08160905060f0d110a0803040512010c092105100f140402030d05090a1e03020307061404 71
    0x240f000341450422a030400b0f04650800605500c8821002c002442c0320360740050928100450001d000c001039022a1040d4100080d0070f10400601a0040364140e100d4000200c4031380d19400b1500081100104403081491310b00c10b549440d80142101d4418000f16108006800c1c41104100000ac0300e400342d080050900c010600003c4d0050009007001d00005001401003082a42c4000950542e5001500c95421144006c02903100090101c0050302100d030703003400240784c00c2010401000c5030080c80c0c1e200d076162108140030711802e608500039002014184030940c94450822550301ea01900c6201d005034028880212039074018890ba040e4210140c3c1d44a9000303242071007010221112228140b0104224100d90000500400043c4a08450204045500c40e40703500060101e8260940c040d94a4088108002c0141d401040001c00100c040c10090340703955030721000c2007550700c05402942c6103210746d10300c41000c40010f00d0501d04881c400c5080310040c41d107442e42141c41004409202c80582c0040c002 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 905790395 1250 905789145 905789153
    0x30b011a040e010303050c1920040e0f010b011d100f02031306090f05060c0606120c1e0a08280611070309050109050604050303031b0403050f06010806180307 69
    0x124540303400c040040381c20962200c420b41000340e020707031044002c00c0b0001f880b1501c41005201c000344003503025200008a01381521410003510f03458442c2e149071645441200201d58850303110030051540b07201194000074492681500a1508621544c0400c02000c8820640d00142444404c484c5010701504070404141c08180c03800c8202c40312800c15070005000d000c00e6807000f4583c001c0242925524982114034050f548440406d40d50806400fa82041290909070a0300159050300844240c03060000d44440100040c207148400d040315a2200c0c1c4401c43d0600c000300050041c031811001c0707400d021207a03a034040580e0f42c0c003071f41305c400c0e20500f92200803110303009440000040414000d0101048843c02d4075841010395200800890200c0d01414044c809940d1050984018000035034005103403c0c03c100001ea640d000041181c0054034085503440c01d0400d03070809640c021603105044884050b2000c07035135510381901b4006c02d8050b1141c140059600d50044410031a0302d04120082c502d0243c3c9a04d0b = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 905791645 1250 905790395 905790419
    0x501110f07080322030f081008030703121d0318030c01080a0b012015100609050402030c0c0f0d03141e04061103090109110901030206300c22030b01 65
    0x5401301c00031820301140349003044060300030100341c0319a0f039012007190716007800340056030087c112006c4440260310078060309000004440031103815003007070109270b80c0640786000030301710307060134482540c030010452071401400101920b90744c00b02d2242c800e203040c9420281640c81a54200c0301d0b00191440c80070903080c20459200e90a5a40c040c5014500500d540710070651808008414520343e44c03213002d450744500050000250072107580240741c040d09180400c001c04001c050f0084078461940000440c3d81d03e50100d003101d40d0b500c3c8e80c1c416142c41e1540101e0468403400d4000081d008603040c40301d8000c84420408986214410031180d01e0070400e40e0b01c1c501070704003100030003c880e40d43d07442180f180051003003005180715200c28000815407032900e181c41318060754414881070140c0440302c014001a5240e00070703215131641071154071802150000706c50055004165804c084151440c051100c1c00712128002e0100d200d060300d60521080030710045000d070a0043c44040c00b0550180d00500c84010000 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 905792895 1250 905791645 905791651
    0x405090c092d070e090f070801170a020d060509071421010e06100501020c12060c071b080a020a0b070c031709041a0307080d0806040c1b06090501110f070803 69
    0x884988101c01c0c40b00d40307035040400580d8500013064111014400c1c40c42c01014640e8041551010b4512605082c00042c10302c0206005d499080c000c80d00c0c400c0e2102070100700707000e2001c0c0c008002c9980500c00303040510040c1000d485401840c0541080440d14251000040c110b062001d08440760704540c04800d8401082090249000380d501c82605c180308103400c008241c01b5417680c1e4074500e02c0d1850710001a1030080c0300542e2034020400701e07840321002d402c046a40f40d4494052424107035540c2e694642540d28040c1030300000c20791100e04c0d0000c2900c050014a5041c114801e8810868642d1283c103034a081c0d028200e001040e5000408051001542c00420207074240c101c0c0110504058032a0001001d940c1200e03212949181082c035181c10074581000385400510119002e40200002020f0007400a10020141c40c091034590301d41c1040e191051000c00031030b000e00d0313480300d50140d80c925008020b001030010540e610340c2030140c01e48161000c0001c80e00c00c25100d9120500c3d010302c2d80d4403480756030002 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 905794145 1250 905792895 905792941
    0x60501060206040f24090b070e01180510020f0304061e050405030d030b04061d0415060608130f080307020d030f05070509010e060417150f06060708030a06080f07050405090c09 77
    0x290711101790641050203010542c5201c0c0d204418145041c410003070400c1c0300e41c3c07125070400c0100311140408035003030140c19090f242c040c2d41000311100c00c1032050b49012192a03d4038000d210020300090020790240b00710b4001c000c0050500036841d08601d0489160150b4011141d00d074111040d00c08000e40032394030146544002800c00b149465a6a001c0c00111001707042c4400308c10060010003041142060b8004018a9480c1081141909141d0024880000141310140c80140c6d42c120b131090200000c1c0b40003010342c0c0501030071359a1070105002511030303602002e400042800c003480143c16242034000c0c0361240c65550b40d0582042198001100c0303140d40402a103821400c10480461900035a02240c540350a02c1d030000c1183d00300b07090318692040030041c5859280810241071042e107a407030710304558046401180185c2c9944070201054004d120a070711001c41391043d081c840c903030700001049060444070215001c0000755203c1c20710705c1d16040c00081047d80104118000395100381519201d91580f40c0c0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 905795395 1250 905794145 905794193
    0x60512060a090e0a0501180c03021507060c0f0813050607050d0617030703110f0c0904080c07170709050606031303050f030a140702011406010e0f0904080304060501060206040f 77
    0x9100e60080c1101c1d2244000f00403134200c01101e40911600f4000e00380f0b031210702d005101d950b0081c2c0d00d9480c10680c80c0e00000703200c1c400840816400031924020b4426480e00840201b004403000e08001d00017410003405080854105400500e02d090500600241150000050301581d40d490350222200e500c140003803613031941c1c1d41c0c4010620020b0902d4040e10b20213483d0080d80d132042107080251414110402e034410990240030b03a1811010040303180010b00c5400e03a02e00005464501c0c0503060303030040e11041103591103030480006050002520042c480451070054500058071b601c1d4003800d55404940369900040d080012820020012800107140c0e03019250140c20030b08070f9060445d2507071050310306204882d11209120780040d405240180c000340c10340020845c079448201d4880c1418402403030706042c000240c04103038031601d41c0c80c0e0300204003000030050000e600c1c2a1400d9001504186c5040e641030785880004100140005070150150f5007040982010742c0c00340d80c603100901c0e1041146520441 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 905796645 1250 905795395 905795399
    0xc050f101b14010b091f090908160302010621020f13060e070f1b02030d0e0f040905060a050105032b05121501120b010e0d060219020d02060907060512060a 68
    0x2c034008201d200640042850b502c0c45041095005000e40400384031213030995848404860f000244046a00d05400441c0303405031810070030014003c07080003001c00360646080c0300415030b041d8000400e55410b41d0032502001d00a8042a1a050a160009410001040c261801c5140211141c10613156a1101199642d00c405184100b118165203090128000c5480302d1012604180b2018000d07500784100506561203400003560b40703400b203000d00140100d062301c0f0034083c0c40700220032020400c0036001740304e030b03030820b24056681704003c40303c00702c0c5a80741c180040b48515010071183c075807005c104c600742405030b2403c510380200e818099902d024840100011030510403181013181c030070420385401d80c1240f003078040050401126841d841d20100e143c040000307200da1f0800c084090310001a9044244000b0301d01d0311600072701c540d03028142005a00050860b0f150b1380000e1254551280d907094480e0f507282d40c0381c0c1c46e03a00c0415001e800e01107a07090094800103070b00300d001554800d6005047c89017441d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 905797895 1250 905796645 905796653
    0x40204090c200a2301090f030e060703090b070201120e0a03030b0907020c190812090102011b080c07020a0e10050a0801060302010e060a0e1f090f03020d03111213030c050f101b 77
    0x68605c400880d02c8211f600b103007009140c4c200f0541c114500090f00c840d40b500c40a41c1e002842e024160040a04004001c2205421340e407080c1b8015a0f8550805000c1112801c2c2144450b9a901c40002c11400a41401c4908400e420809281801644030303400604500740c02000304002c40c001e0014100c21603850079000200403034100841c00e00c0c0480030b500269260200390009081d180d55550b694089020242c02e02c03005584288966030012460158070f4440102c1d04c001f540c01821944402160025074080c048042c003080301810407034604450f0685d11035038a203241c500341c40c8644030180c0441c55002485101d1700f400c0b0024400d00704180b40c544505182207001540c07d08515104c00e13070300c5a4203490381441030380151190010b4071031007030f00041c40c628560002e864206505402800c100103050342aa003407204000b070315080405020314640310121100002c9c0804160b200c00d03102c04150200014507030414507140014404041e040d01c1140c0c044100940d01c4090000c1101c1c0c0d8520302c2c1006901003 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 905799145 1250 905797895 905797901
    0xc12390706180f06050f0a0212010e09071e14090103240b120a0302070f081f140115170c090f061902031911030720040204090c200a2301 60
    0x40f80c400e010025590500581c80ea4041e50f008081a41a03481006001256141da0500d281140c214007191031486d41c810700f455082003920360041c20000307840100f030352400810800c1a403d071605c0000c1540000500010410080c0080c800a070629510121182d00541c0020641149140044002c59403040c1d1201143c0201109400c0d01c4c50780c0c100d50f640d0804c06074180b007120000e042c00c0c126018410300340110f40d41c4400d440307101c4200c02d403084601410038031032079005041c4000c0c0c00040310001d5039460603801440120707411190002a4603404001c00302c0f8070940a54000c4201c11502d07400d000c1c0020a00c4409817034100d009a00180500840c20300701001c00304000301030ba055016503118040a5111511810004880010b110080c040340810007000404d0352007041d00400740b40010768102144920300c2d5810740009400500000b07001c14440c002c1d403c02002030708d03140c0d070f0312101d41d2402e18a00300108801c8607500681c4c100110617404135028040c3c3c4115032004008079028440c0002000e821 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 905800395 1250 905799145 905799173
    0x1110a030b1f05070c0506191206080f03040f0f0609120c051306030b0109020906270319120206191a0d06060503120307080403080c1239070618 63
    0xf500002e0500200481c02914100501c0d0543e0801d0030800054103004100701e000904100f0022109008244150150010401400088203071214030a02c21042901c0f80e005c4d0107250940181c02c0c40019081643c0110b040c2114026038038040c406050203454580546119070170381e9a040c5504010400380d984444c000c0407465509000581c003465464040444081603000300c1e403541c418030050405031180310032603008101d000b0305050001e40c13803001c45142211702c0d001140c061240000e003031800745050304ca0401c150f000720018402031003000d004030b9540000300e90181c000f040e2010103060724042e9400c00030002c038a405401101c0030722070020075180c101d0204107841494940f0300802ca1410300748000c00055010403400e629601d800c3d180a8801240a04000d08000c0003400003443e00d01c0310303019112110401218605941009a0748000b500c010028589240c1940c123a10203140c035221056444c03980100501e06e0070190162500340042c0308c0715800120550201442d4400903400c40e0034400 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 905801645 1250 905800395 905800397
    0x30213090b03011a030703020f0307180c0305060906030715030e0a150b0a06051e0c0f0c0a170a110406241206081009080904060602011a0301110a030b1f 67
    0x1c081c07495100701420345240b1001c81c5005005014800c10326140428040d05403074050307031a5802c811104020071320b4a12035a01c03800f9401c0001c8110022111300d50131007814020599401e201a480d01d9081101d81c0005642f142d90660100c2d0b410400d4210001000032083e4141c10001034103401144000e080c05e5091008580488040610034901c90051050303908042059810140282c280003025109100d025081c0152040d404420216030454504a0700d82d00c1581d419540504004e141169031402900035540c1b14490960010810500c4401c100c1c0b5103060623401400d828030746032034600c080c0c0c8114075507c2d0440d03140d51001c900300f403504091303003469240e0807510361000801c41d5009245500152295400c0c1e4240f200401107903000180103081504000800100c1c0030040c5882e071040d1140d203540907005400c1940000f0303407940651020060105015680d0701c0080040109804c03078640d810801e864801c00c1c001c0c8941a80f003544508580b010140000303080040c001c01101c040042641010 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 905802895 1250 905801645 905801651
    0xc0a1104050a05010b030403141312021305190509160b04031b060e1909051305100c1e0207090501150f0f090b16080f0c1203010303080f040303021309 66
    0x5016081521a107035011000190402203941040b0550381c0746e120240020f010051030001c145480c900d864100e03501c40702d91030995a006035803210036021261900c00e06070b200311010074141c0017195180c0240f40c4920380b0382032001207058107420b0f0003008100240c071031410352296114400215045160300005050701414540d1a0303495071420390109481c100702c0360900d14848004100c1d054201212814521303040300d11a107000c0c40180071140605507580700c8002c0c14140009e0101480d006102c881200340902c00356001c0c1e1000305180000c1d2014031050500041d0004c00a551300c100b03070070918100d0a154070540340340c190f8422803501994004c1c1c1120191034446540d4960046d00200388402d01521820800d460010100015203840b007107205610310742c200000c1400c0d4281d00303001d409840b168040c0180ea1103110313598040704250000a8120f00f00d1056020000005508c00c0541c3d0403243e06a135148107960701d442031000654070240080b0305064082c0001c0014503045840313000500310740d401c00 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 905804145 1250 905802895 905802923
    0x30209070206100f030201080a0915050a02041509030b0f250f030b0f0a0b091504090902010e180403030f020f0d0b010906050f340602040302150c150c0c0a 68
    0x2e150143e4140d440301c41c00ba95003190800c01031b60804074150307004000c0000060113008504000782038019600b03041c603001d0301d40341c200441c40384540c0c050400d86400a08411480c01420016904241e450202030480076040c00000c400c4414801d0050340100354031841a18124200340400c0004103441241c400b0601230b603c1c2c3e00106a05118001ca11802111340c1c45900c520400885c24048060140141502e40022104026101c00079800d2741d644040702d00a60360386d6259220001803000103012400030b80c10300017840e030518107030000708403030030700c000300e9510075100da80c0c0c00e07401400e40c140b42c000c045c3e4003404100c0200c9403400c050000710740d920b00c02141c4040d580c4001040103800c0c1c1c20001c00d00c0414401c100342103800d501500c4111410483c0030544540c0621300181c040c1192a28250543d00840000208507880d00644200c910035202d1083c01060b500c2c1002e9140900300c81251a41d0018040e25004004200f2650b0040f001380521840c0c200b4001030241007541c240700607a03800e0091074038 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 905805395 1250 905804145 905804161
    0x60403110c0f0906010e030f0a05030c070614040e04030e040f0b010f0216050d0807020a0b04090f0204051f0e19050922020d03090801060e15030f0303060d0606030209070206 76
    0x440001c04a50302c0742d0501101001501d540c002910f064100a0b840891045036141041801200c001d85412905254181d2803c560f490b404034405120f107010b1803100040c52405a400c2810418040c0362480c00c20f4145110865504001082a002c0025280101e40c00e5200c0e482140ea00154144010440340c8200001400d1050402400c50441d8060f41060420004e2001c04100b9514102c0c1d104030800c181e030416031058002c141c0d001e07500c202c00391400074154140e6001802111030a1200703000b58200013500e0402c9001d14840d060f0021079107000840360320302400f848582140113080120000c0344e260085500080004213070440c1c01040d00d014401e92070010030f10742e4400200f98100d600117020801582100d44501c0000313005601c81481842058003070720220001d805048004c0003216920060180300ca1420b039880b0003403c0c0021801081070801107242c0e1010140800298516103c4030280711015560380c00c1620229600c1c4808401640d5030641d09014207180e078010600342c10320301c1e1 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 905806645 1250 905805395 905805403
    0x302090f061309020f120d09120c1a0c161a1c021c0e211201061803151406180a0213091b1206050102060a0e0c0306040311 54
    0x8624420040c1403410040c10303550300004108800d0945a0100381d415007403001c90b240300050342149900124102001c641c0ca407001500720a0050b5682d2500091550307407007410413181120030040e211148502040c01001c00c1038580d0040c0704038920840f444e01c9920801c9609140c103004480007411090750041200515220507601d4400c0000c50051418540f000608442c00c40c0302c007100001500482c0005401d61801c0c528550040d03042c405101440e20703044820348805100040035004a421051601c0c0d0741c580c001070b186560011010385440380d003003a0007a9002c0a240e81225150a01090088005141e80c1c0f403181001d914640701190130981080034450b8ac400091110780220040401d120388040a444850741010280800607a9000c0300201d0980503540f907000720308128104035101c0c4111b0126504001c5640d01c1d85d8401d403910250605101c142c900e90b10500e40168040000f08440d05850750210030100c2400049551325001a0082800c242c0c2c00c940c1030b004145e404508141d4103400740 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 905807895 1250 905806645 905806651
    0x3050a060c0306090b010e1005070b0a09050714010f080919050601051018180906060b1206010206090a1713180b0108040c210c1e0807082113060504030209 68
    0x240b4180400301307818000034041d010308a1f1107482084004001075003903001d003044a03219034001084149a1404015410185c00000e034103c0f050b10403500005031504031035100c0e0144510503914139910030300c0354404540141c0302503c0e05c0c1017409038644845420070a800c01c2c0c25128441c0d4042c2503190315203802c0040216050400c2414031440c000f4244113400b00300c40000c00c0c1c0d800300c60490104468000110020007151800034500f51804102041101a0724081c10314441030840b824915a58000126100c11091390140300c1940040c24010001d8101c500c1d2001c0401032807101400e00b050010080749515060b4132840c0440e07100d03503100c10703022004c0c040c164030084207080941c80c41c2400c0d07468400341c108902c903440b422800307100507043d02c0d15806513980f03820381c000c0b84602085440b4883c0d4401c0e88402d02c107503001040180f00015481d540443c0c10003c0f104440082c0460400c01030030b217500d11203e0820f10b005e107401080700ca540d070324114034024081d09a80c0d507465110750441c8103200c80c500000d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 905809145 1250 905807895 905807909
    0x1a1b0307020721030503040803130c030303050f1302030601170a1a011a070c0b03041b03051b0a0311060f0408011406010f0e030c010f090e040b0402190303050f1303050a060c0306 78
    0x156290f9030219400008681e041640001c0c2181d90ba61001c82650048001380c1c3d0040c0f284a00e448000141a0305410550140c04104111001511285107030000c900702d181000303405800807001084000e00302840590b00e415940e013940c0480c42e46a5410806c4c0900d010301040002c019401448170190300c1441c402601207020718070f841c01541c3c0e2280282561184101f4000c0d0b000040000d01308100204840400e0600080d4280000d031649802a15500e5100d022811940c1c000c0f402ca203a1302d02030a098003101e400c80c0c450040700e1807800a000c6580d04c001150340024008110002c2c90ba0b07024440c203d4610700d101142c400c24200580010b003111100d4488504010381c80e0896030341d55a010600000300f180034240480a82445503041c1c403110115805204407200c940708000520210700d90651045200302c841c615103001c1c0d000042d0501c5400d00016000840a20202d0003115800008100072103860b20321810b243d641380c0c1c42c3d0380303032418542c021986540c58980c1540c6082d014080d55001e0542 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 905810395 1250 905809145 905809199
    0x90204090e030f1e190221040f052407050c01020105060907080621070f03060c1106150612040510140112290c0c10091a1b03070207 58
    0x11401007218030380506200c500a4900d1044008003200800d000c617070030010252172010411074a800069100d0080c18241e00c54050040d20b140c1031880b125040301e0a4802e150301a61950381082d0510000c40707600301d21000d92404400450b212400c026020701140c600c120300814403903610100082c01c0d550085c22850150700300100313100307010307801001055014106803a054500f01d134000d12004554440480c1c00792078001d525000c54001080c81181080c3c0b800781c81c00b48079202c0d000100301c868a8504003c200e07142c20000c007044007003801d5845203900788402030210342048940902d6540c003a2007544c0c105e416502203805200d00c16900e0040d00060a41d5034560103a0758541040c3da50521034498000b028007104592800c11003040e0350910400080f14007555125107005c404940080e445009400350921902c0302840381002c40740164a00300d54040c0c06005064245240060448009011106401210360b110000410f2440103507201e000240c0c024640c2134540101d01004060b100030311600046 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 905811645 1250 905810395 905810407
    0x9011218020d35070f030e061908010803072303040b210a050408090f04020d0c080618090a080f07150f0f05060319020a0b120f0708130219030c090204090e03 69
    0x30303007030f00b42c80b1140c1e04245002400207141c5011551a4119100151300140100d0409480e400c00d513050820110310b6191106142d88495519549000c0c4101c004e0110944200041c003181c0d02c1200c64110001070000c0b28101911068452080e400c130300030402c40022004000009600d582c56400d81001542c6400c2045080540700c04903648140d00c003581c00389007801c00700356154072039904459a00400b1071041000200d2503e00425481003a600140b043c12200b8001101412803450f613401030f1071600c0106512240c59071105903d40042903140780900b81448004046801405c20903840c89403038000095080042030500c08984814010f130100900e42000c100d181e8400050121920a5011921468460910000c0d08600058200c4031081402003504006d55a1101c0c002c0e0041215070314070302e0340b40da070707010200c8154070101c03507001036aa896103107440517050086480381c940800b00a0969241d0300c2e5110260248280d60008081c00d03130008041291f00603611030b0015a03450800a0740c5405 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 905812895 1250 905811645 905811743
    0xc06050a081806010e1308031312080708070c02010c1406041502070302100207050f0a03050a0801090507081f26010606030c080103110d020d060209010e0609011218020d 74
    0xf4105006501140344d20a001c5141341a2515a80b1485030703000e186140e5034503106414504103140200100d8602c038401c011400041c0c0185185032141ca1250342d0038289646498044034906102c100aa040c4113210f00540d0100c3d02d40ca401001c00c0c0b44000c0100154140fa01c3c0250780180d02010200c6010302c14403138080065800f05d0b20148804c0b00d001e0150f00c45200703040583c144074480000032418400c000d141010960000c0c0506841c610603150304040340c3e6908050401d1341d17012200c0070002440743d80007031648031142130075028074004010320780c0c4295120b4040911000c9014105c100d1400054415110100e09010b001d000d0300c494603007840300020000c070143c5010418040140311031802d40d00b14a564032091341070401c80e600140411203002c15400d00c54000c1d807041580500040d407100b4001c419042c40303c122210040b06135280031410786ca5040c081c00912500c0c1245c0c04200b48014940d02694903100c0001708580942e15040c1d0503030f96000d10a1108040118003032021451088000c908 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 905814145 1250 905812895 905812903
    0xb030c060c0d081803040e0f0a0b0f131d070f14010f1d0a06050c2a01050702030a050d0207180c0f11150108100e011e0b0303070c06050a0818 62
    0xb014490410301c9564403540b41e02200c04101c503c0708640b910000c20005600c55245458602410768084245565100c1034102c00c1903400d028070483d04850700480000b0b0609001140c107000540540c0001100d00182001141c2014918101c448035400344006001801d88402c40c40000e00000d4043c8102d121040000b8004660714030405003404680c214000440440708141040311200800c2c0e20084c3c4d444010282494112200103001d9106001c90114803400209462034000c903801c54001d90002000011100c5602c00710701280c150240603403040c009481000380030001003041e0007404c901400c0441103203c4440350352540c06150300345000e80101c01d8100040c22120740c45490881c044c034100e9010146807020411180414481c07442c0001186000130850405134a85010103018641002084134203071a20000d40320809802c0c521020310340e00c4140e000c0185540094140c0e4103114980d00c40c0e042900007a805007003c140f0010741d0550a6601901069003d0a24100e02250b400c00c0e6844903070b9 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 905815395 1250 905814145 905814163
    0x10e0306010503210c0607021b0102030901021b040f02041d0717011802040b0307020a06050105191e0503151012050303041101090b1c0f0e030f0304110d060b030c060c 73
    0x50314408803124100381c0344c40e0045600390105401241e5035800d101300000e544082d4040c8000300c0a041241c01c00342584040100c44258605034002d2043d01e601c8256160400044c030745030ba0b8856030301c03d07a40b4507001d403d0000d84010101040c00c01c5103024982c0443d00c0680c1c00500c80c0042044003200f0303040d0078041e151684d06441a010100310425804410340b4002d11858100c0c0f03818400201c00c124200780c1c0007420215582c41000240202e9a848041c0010080c0c0c2c07424442c22034568804c24041048180c201d42e68401c090400560035590703441c0070034102500f4511801d0a20071a03400c106400d5101414440107000f0b02403001c142404031740f00c0d503440b0302005d0b200415180316540c0955035680b041202d04080d01007034a1055a54001000a86080b10041c0e00c03041c00380d04082421f40c06180e984941000015810040c0d031608150350309811090740001c00031501d40188001004c481d44031034004522081c400e401c005004149001050725115410301d00d9032043c00204800f00949401017a9050 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 905816645 1250 905815395 905815423
    0xa0b032d01030318031406060301060807080318190e04050d02060c030a02030402012a0615050f100302041a09030f012702011b030206071101090201050301210501050411010e0306010503 81
    0x5150300742000130000e48881e44041c00c1444000c143d0100381c200421350a003e080100c0c000c100071541c500e401c94031080f8600c1130341c2c0700390410300c0240d03242c1012580031402100010900e4a01c80240c50070040684030b00c0c0c00c046c0040180e9401c110070000200641441c1c0d28560005000364503019101035031601c8010300e40c5c1078403a00030020504590080c42001c004002050040c192a41050891000c402c0c1e40c0d8400d460701401c20820340c0c15100d9445142050715800b6000380c1d4510242c0d4148462010400b01240070150b08200004412400741c5010072544140011241d45009040815251045c0c0c0054200c0c16454034a040300110f424501d180c06603a01111081201c09039400140d840040d5440c54940182c160280d4108040d80803c80d18400c641c140c4801c4000b45050300a22300302d0313000440080c04200104018001c8244a14480740041c10b09200c014201d4419999075094410075141114111801e2840c00290340e00401c403d0100c00007500245100c0d07252000287d03036204c0d0107034450 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 905817895 1250 905816645 905816657
    0x1d030d0c02190618060816030c110601141e1305090709090b07141201030b061f0804050111090a090207020102030705031306090909121d0a0b032d010303 67
    0x16046480300080d03940411072107860010010383d600c40c0500501e080b8041c00b1054100d9440106400d80100311250058010b030789034502a4024442c140c000b130151001d10030910a003a0f124103280da804110f15406403980780c1c034405004205109001c01003403c00300c0c1000200c811004011940c4a020040c42c905020020201eaa6101c51001d03500b440d0b130b50340041758402d0618003e1028024400c0200380641c0c2c2650702e55400107521802e125440c090f1a1003400b0100c1d05000400204001d00034841c1c100f440100004c0740d44400c561b0b181c103180c0e5040c55000218101c1c40408c81800740a00c1101200503000280600d0246480000742d100b440c1c90042c54034495001c504201964401c005035010a0350000880b40d90f582580b1102081d031090f4440d410005407001c80120f2440d81074011036565640c0810f542600003031040041e52600d59000c14000e40c02c140107803202131039880c00d0b8103100034809440c2841d41da041504080d21520400c05502010640940c1c8802c403061444180760304480e0545006 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 905819145 1250 905817895 905817917
    0x10905071806271109041503170a14070501230a0c0e060d0e0106030804120b06030c010e040b011707050a0306150804020108150301021c0e0109021e0a0806010602010c1d030d 76
    0x1142e524011100a5a00a41f800d040742e8400f03000e40b003a40c01030383d005480b002c58000c91803008030824440c400c1c05900250080c24400c00301340d40130f006004400d110780004a5000344490000380c4040005507400440b4082006201340c0c1e080c41e20030b060701c1a82c40d1500c55044402100895403510800d0108441165a5420340d40214420b603c8a0051903111020035038a035507510780001558041c2d4070a407a11000c2101007582854001421144240b06031907843c0440e002104101c000c0c2480c0302c10505000e0004a21980c0004034500140320713039401c0d03d4640c0c4500c0b01c640000c04a0315107030084043d604400c1d18a64200d82c0055003c0c0e8001c0d4240f03013000843d5100000500795002e0b00031219095030001c141d517400810400b00c4a03000c043c3c8600c0400000c041448058281c1d4040940a5004012000444075507030002005905030140035142030070265440d0701152502c1000d0744a1401030755150080d12407254015074608100721084402001031901200090f114100072501006005904000b = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 905820395 1250 905819145 905819171
    0xf0b04021f23040f17063111040c03020310121a19020c07050907230a20060f070f050909070909020d1d01060b04030f0501090507180627 60
    0x40742d01802c0854030010f80f25685554000a08446003002c14032405400c1c0040c0c50401802521010300c40404064880080300343d0207c60459029401501c4c40b40c220b5280031000d4a0390f0151404800180ea001070313691070040050030300d41132030390481c1000c0300840082c0c102040074881e04403940c40c602d006640460301c1c0d800501e40c1106220020000c0180007194201c00c0d0080400c01c003080318401d0346c6440c001c6d5603000b81103c1c0407107941050500d2003481000340005000301c03406814003984500340452100d08058500b180100003922408a40d40f16904001246041545103034108102c0d05000c04034600f52100a00310303018150700f1074000c030414800509032910648a0702c00400d007030f800856032000f10300400c1d40030340798903031007500400c030362040071000e038001442450111100960310301e041a08550f04d070301115401c0d0405650b03079920b400700c0c100802c405020301c40003001d10280d55064820401d20309416168582d001c1c004901100d00881d0007041d9440b4103401005400400140b503000f4044 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 905821645 1250 905820395 905820397
    0x418050709082a060a0c0b0901110c0c0301060e040b1f0308040e1602070f030206071104020a050a0e0d0c06080a09050304090b03010b0402070317040804030f0b04021f23 74
    0x200808007440b882c0290004010540420f810b44050b070340c250f9079010704034401d0007043d129400d034000029050350b140601040f0358030540c41d003201d154000031444410b022074404854002e0030090710719402103500315403145401d109803401000e920740a050b16241c00d465200c14001d00074601808800800e140c00081010002441c000d903a21a80c41603c1d5629404072031815601101d44c4c940101e10b464414580900005105044504594280b40b1a504680c00d010303d940061004507030110b41201c0a1030072f5940c500207016145015078401c1e4aa5000c41d000405030865600301600400400b900007002c41c8090202a081e101103003000d15440d2507503d06400186120007003d0854000410089588405a000440e1401c8120000d2001101400c00c10049129010005010400c07508c047d60903a1214180c241e0301c54041d5004508003a604d44807441801032003c01101c8070b0140004010441c9000344400041b80e9078400c10030188000114003500b44d100015a841990350900484c48141504030 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 905822895 1250 905821645 905821649
    0x117040f080706020d0c080417180a0816230103180b07110f01060b031501050f030129090a1701060519030b0f0c04030219050907080f010b0418050709 66
    0x200c80c10740d0b90819420070344000e401007a00713040c54030708180008002c24031503c0040e01468010f00028020807a41a0703500341c1c0d60007410080c8204201d00082d0045564000e0007000500c156130140c854401c0304442500d165449821004594400301104072207038a01d00c0200505000070700300002c0016102c45c00280c4000003d030003c02001e002d800300b050300f6074400110f00d4040d900d80126180da05c0d40c1c491450076210070307004410b004e070411310020784040303602c454111944a0606142c0e00e840d400002c480c0307051344240c00401f5083d42c80d43d002c11010030703800a1003000c0204901c045003426010000510000d00611039592501071100c261018040294001c0000b040010b24040c8003d1840740c1100c0743d10114070081c1c900c0c00d030702d0300012a429100311069100340c06113201203142c00d0860f0f00b0080a00e248a03c1c0e40807e4001c203101285903140d001142e03015803840d4481181928040d540701c09682016004100048810f100c10048496011001501d0700385404010600d0b0361003040c2191404025 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 905824145 1250 905822895 905822903
    0x140a020703020f0a200d061a10020307080904090201111e0c0a050127050d050a02030f0736112a0a1520070b06010c080304020d0302160902041707050117040f 69
    0xc00c0112344000c0540e0114481ca1905862141c1c05d094001000d03600d038001c0c56000750941104001d06040351820782e0242d92842e01c1410a00b400304000514580340544c7c16440920501e542203a08042e030f00d042040c000381540880d02c41060320b003081d000034021550260304840400340416000440c032950901d80c00907042c0038144480012050410990303441e0021811790190060142200c5619400701e103460681e00b900c40c0d4641507205001ea20718124032070f800610303d06002800c0b0010171008030300440282c1174007580402d4440e003910703401c4100550500c640320100101c540040c106903501141209115801c20180100007000c00900384c00707000800f01c984840c120f490a00b030580d801100190171890700906900c409541c0305401510b42d0700305a44003a0078010140700103401440c0c0980412807485c07092055130400c036000780c0e8110203401c554010b02003154000c00c00340a080702c0351158065031152280200070003460040003800c491410b00d0002807003050725000034140209612000f03165588 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 905825395 1250 905824145 905824151
    0x80f1e070605180123040906050603010308160807080304200405100b07111018080a050703110301180305091302091014040f0f0e010e07020c040b04140a020703020f0a200d06 76
    0x82c8940f10140d5506c00d000307540b6840c2c40c00c500425242060f07000c0e80e0581783d104004610301850300c01e200f0034400a0140456900204002c007200082541e006540694800c00c1000d003a84402802c00000c00d00c1d00c000103014514001c00c001d0840c81d101041012140c801020030b80d40c401500303200c0702c5000360720000c9030000c560071010300c0398540c405403681a45954007020006941c483d4012502e9000d280c601a1032030b4031051081c0049585500501c0c482a8001c00002d00017804a5a906d42021501c40aa01185000c0384510181c240001d0021120865131021480c01c461000041c50750311082c0c101204100c502c10b000c005001000085801a003980003111010650352113140031060440d025071007511518000001d011400814618050001500a0700d40d43e044102030100501c2210745007031b072164440c2c4481c540c418900e03160b107010721481c2c540035070b40b03184604020345401103048140c00d840e4081000800402d0000042e040080440141d4180f0500c8140000b480c58a5000c0b000d05860b00d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 905826645 1250 905825395 905825447
    0x90f020f030f060114210c0609130c0e040b010507051b0a0f0e0a060e0702152d064b06030a1b05030c160c080f1e0706051801 55
    0x40524418144124100d4406c044407840c85035084488012584c4207040340e000c2e00460700a8034102029150036040903080c0c42076001c00f00e05000642e0340c1c000ca5a00030580c02d039140383c1141000c0c007542c6041c0c0000c1c20300d07a20304207203540e505d5940e0514504405d0303c0010958000d1142d0350b500c0c5a40c00078050646540070700c82d01c076040d0309180b80c02507444007001460848001120107400e0140342c81029540c002d000701e401e140c4c0661882c804010a01602074803200541818100301c2d07032910b5038100c1c400304154201c0c9002824072880d001e41100d10301881c40c1d100d11000c1041c000c001d00f511a0340a03440019a031031201003500740310520800d00e03503a01482c040b00300a4048465407200e6426400200d00f09008c0e0599107040c0c4081c4003c2d20405c04408082001e0380c40c05802e0070701000140e10980e60003450303aa580e00300301d0402d030407031816646540014000d0264180e50509004007406040c1c0a0005e1034680803010b4024803401c83c00400e40852001c0540c110ba005256054070300d0440402c030b4843c90 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 905827895 1250 905826645 905826659
    0x7050f0607080109062123150a1a1009030204050705190807020d03110708070609050f01060e0438010f0e041e2a030c0504090f020f030f0601 62
    0x1050464406001034022400041c82c08881d000d284100c4030840d501410350261b02e00e40c004042c410703820907513009150703005000700010214032002c90700400c02c0c0031300040b1741030612501300c2c00c1d000740c02041010b0401090107084039680e888018842c4d800c541820811241d5101600c025045510107076110b4541020400c203160810010894010708040d920507040b40d481040e03800341015140840140d100000d201c490701d01075840451355002c1c8285241c01c1c2007080d9140c414540c007250f4126841515032050f04204802042403826989500300244901c509151100040140c02000904540c510f10007c0c00d65000940c0c43c681d08070700b1070182d40c4c0c01c5100e03042a040c5401c028451b6000551000b04000b40101c0d070009010702880c3e1200240031401c4015030a503041d40b403000300c1550b0119104088900340364499092104814814004045c058514104050071a1251b80b02c14015400e001041000524055100e010b042d03045900d07041c07014698000ca880c0c040009a140079911440d40007082c51 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 905829145 1250 905827895 905827903
    0x608030703080f2401030603140f16030b040204020d0209040207110a06030c08040818030304060210060e070c1709060708120603030c10020a05091e010206071e03020f07050f 76
    0x500d0190b181d400803034a410030100720303c1c007040764030140960642076807805070301d56215114640b00d0145404a030b01a100e440e40701001c0d8140d140070490341e1107000d16504544042c0480c103000c0d1a0a40f5598a4900d1510f42420940c1c0c0104002c1c85a03a00040b4654000585c4d03064a003031180141045480395500c1c586500040b182010b628807611881500090891090184410a1103682e90703480b155100c65403940f02c1ca4011000020041c001903410181c103450406c040c0008019641c0102081a031110304c620031100f80741c100108051024041100d40c0d41c010b607a580403282d210b00b00c90504500c043c50b4031200c0c02841c04150f48210002a02018072140308050014290a1214451251113400416650744070720b2014650320380007010270700761040140e8060248410b80c1c0c2811450f103900070300010030b00c80b00300c003001d83c42d0038800466440a507810081d059100403181444900d07180034519088501172440503a07070401d900050301e40000080041a2040d96512604540640650450f09512 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 905830395 1250 905829145 905829157
    0xc1e0503130e0907031103030408010905030d050c0f090f0d0602160203061e0f040c053c011e14070b1e16030b22022505100b0d06060803 60
    0x2010004210124090151106003800f480d46100146491451591903058a0394440d98503945800244400034450600703001d0100103d1094001e0b580d614200b401081c2220f40240c0f55070400a01030110a0300080d00900b21500214115420000b5410761000260700242010000341321900204003585507000c2d0440c200f10716442181503031100d6072072402e070000c20004503080844190001d0302245408a81c0300385203420171700400004840c4c5884002280e481081095824801d038220f21030102040010b541c2e0034444d1007205070070400c0e44000400203200c90039200110780020340c0f0180700418903000c1c010441c1c046050b0300d1480e45a030f0311402c0c047c82a2100b00d80d08039956202c1140c1000355060130300c0c0f8901ca0001e184104903010980b202c120024100500d010781c00c00900c0303081c08400049040c049110b54416000503a640b44a442502032441c03c03035403100c00350b80c030f00a8100300150f004540d107181900d0710031000400024103800100b50040c2040046e1142d8945200418605000300003410 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 905831645 1250 905830395 905830417
    0xe0309010e0117010501140f040602061014010c0209090313080c030708030f1602060c1603120e010203030a020c120a05030708060105040e15042c061b0a0c1e0503 71
    0x426145400150360082d00f4803030b1640340d000e100d00180515801545e61244d0704000914207400c1c03a00c0d286007484241e1094201d41d0240c0e006004100552103101e0210300600150800e50160041d0140042c3c2500c00c071701002031150052a0009a01c00020000e49550490801d9020300e441d83d10301c034507605c401240d03020a02900a004d8081199440042151000c129010b403061500d0501054612400200035041b82d202004015085111100f0040a08407040f0042141249442c0d0301d000c0762000301c01c40b10507040c442c0d03114688a60760b801005480c0d00c09d02070b0300007698a050011202d42444803400c402c0030b10740008981400841d41c0319018500c60724058071000d800d0384071000155007500540c800d00307003500f4103040040c3c0024000074031104526000350011880e44852a0300c00039101429544141c0d41001c0d01070580b03040810440241c01c07100c1c6484801628a9440702c2d000303544a0101d484091280d80b1141c00c04011107120300000e04504008028144421494015201da10500c1000 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 905832895 1250 905831645 905831657
    0x2f03010f060816030209030c13150f050d0b091903020706031a060f07020f09182112040c23040f14060411090405010b09100e03070b1c0e030901 63
    0x300346540607a0700180218204040d0f1016a0380070901100030b503100b4100315815000b802c0450303002d0340714070035080d0341c03071721085008250f0300345120400d40007800c26400b80026550b881401c1045860b0061035502d103607003000032074410740d42e44040d252912888260101001003003100d40c500345540480c820003511b60743e60b4140328602000101491b802104443c0e60703030001c010800381094100c1c00f0028111180f0144c088000d20403901d00088144400322460740107060002400309480e601400050000b003111140921032002d0038090250501440d000b10000c1120540490b044c8240c0c01c031040010101044041d0454000c1a100a0300c5142803030410b00403420420190405a1140a10b1030700c00b5604d401c58403640e40300030400c00a00307090041420b0444d002c0109910305e80390382c09a0750181224290496451503140c00b400f920101217401d100c10040e5179400c00705140e0b40803401d80112118200a83e4a803806145110340303d5a0741d4004058852418000c0380340010048054003210009889103 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 905834145 1250 905832895 905832899
    0x6090108010b0604151e091404050408070f020d0506161d0915040906020c061f0803030412120203040c030c0504110306091f0602071e05060d2f03010f 66
    0x40c01c0c0c0b100020426404142808107100d041e54142082c04180d0152901e10002d00b0191005000085002120000501480c0040c00346504d1080200d98600090700d04001c0c52030306031101d40703860050080080c4442c40b00c011244c15035590003600c4080940040c11f850560400c40c140780e03001100c0c00c0d800c602042581d040c40d5407082d42845409802e17200074015140c1680e940c80c2c1c40c3e090303180d10000703261b102e550780308400007040161000d001c111000100500345030810740c80c0601c10851014500008002d104c40c00d0060300004020383c0e03082030303001114841200881c0001d40d030001a41030030a540750b10210411080c0901000e0010483c0e000b07034407050036a0b40320000d02042e505042c4000004603c10008900c4c241081900a940558502c100700301f8a10102c1d20724a8221442d032000005900c0000c05010b0000900c06041c5013400b9001c1042e1054074000224900d4041c0f0205024880e9403541d00403607615000401c00c40100c0406940d007911650724184134800e8100b806200c90803400c100700 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 905835395 1250 905834145 905834159
    0x902030105100809160f0f15021903020c060d0b040e0336032d0a0b04021009051026010614070501021312051006060503011806080a0506060901 63
    0x85034180d61000c0d003415814060000180c2d841a07014000f03c2c418031841c0c0300d50f08040c03003090050001d410703c4204920030500e8040c030081010b0b120f030800368403a060000d5091145800140c14000c5542440502d101030328541000d80c10002e840700317000e0b088140012248046605580308880200c002c560803c9031142c0e1507280caa0780e002e011141c0880c80401401040481f501d0000307403803a40304201140c4400c01900001c41d040512807146400a003144444888429500c0d400e0b12400c040098000d200340340080e00d03841409100540b010780155118070103007950034070440b0410301a10000d42824490040c202c0014401d50585241516141898440581000d0b045c0001c42c102d65007507661042c81c003c90b9000341d000f544821800c0303c2a65081181c84032085141001c800107042c0d88030f90682e22000d500b03025080181c1494400425031501d0414010329820005032030569810005401e0052421000315009000d80d8022440c540320f03101c600000c02000040d110b210350400c0d96040c030b040c3d0b83d0b000 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 905836645 1250 905835395 905835397
    0x90c1c0201031505131104090f050f09060c0706020901111e1005060d02090c1b06010303110a05070611010213151e17130b16030501210f02120303010603150902 70
    0x40c4950021008981c24180ca141e50170180e406d000c0700c030ba01480c0c00d03035410048080f100c0e4002d0820556843c2e500700705100c00304840b0580d0210b5400050040303490303d41c00a501c54419154000c00312640851900d02d9640f25030a600c040b80018001c840120f8003240c7c4091800c0401c805100c035a110b403014013a48100c8130b01a0500404010b4100d812203502075003081480c080090900c40006c4d8180040c102d6018203080d1030700400a55005080c0950440c02d0040100501f14031402caa60700180c106400a000000c500e0700325180391801d00d03107071840d000b0910f01a00c00d0061086c404000280046000304600c0409a243d02040d11a1428400340412040c803070b90703c07040428041400e050010840851071031120b07034040d0420210206d5480c050b982d81905c0034040d40c41e685020b90101e845050a9010701c142070141002042004900245515045c1d800307007001c10040603041050808811500c403042540c0f64644000c06030380d02da684451000b4014659040c01c00403c1404c00f000180075104d81c4 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 905837895 1250 905836645 905836649
    0x11061302010903080903031c02072003030901030e07050d0305030604060f05061210030204020c0102031608090c010c17042418092a0210060806070f08090c1c02010315 73
    0xc0c40c0c51200c5451a140d1342c0f143d82040580c69094001008140c40420b40000056084400308000503114082c03414071f036100526602890440c15070070803c0130007580d030000c00c4e034a12040920307000c20703040c000390760541c1024296405160082d05100c1d5240c2015042000307140310700002c0e41d0030002d1940d22004203444040ca8400c280d0028010080c1c04058120203515a0b40501d007281150400c664941c0480c0c1242e00c080c80384100da075070100500100811411000f950b2154a2901a0305c5040c0700041c107443c0e401c07441c046030500590020440030054810b0481040d90381c9642c3d01c40d2101e541d8804400c1031a401c5460a4060790003442c5414494018440300001103800c4492960302428555500001c26418040c900d01041144221151400340c0c0348200c0c0c42462a400740c01e40034402d9036590141d54803600002c1c080c0d00714a00b00300714168001b03401881d0442d940350480c4a503c4007072041d8100076000c001a40c00900c1045104100107089005040d51032003a0703400c0095070365200c2101e269031024 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 905839145 1250 905837895 905837897
    0x140c2404210c0e0415110a050703030e06010303080603070605040f050d0809040e0102250f0b061306030c0e090f0a12050d1a210a020103180b071106130201 68
    0x510060021411040014030940314076801868550784544440782d100b925544600204003d4900304000c000c00d1164810380100030702001c4c0600c015101101400f4050040e40300d003000000b094030300515100b0341103265000d0358003041e2409542c40c0d050042c18080c1c12520240a40b203804000540f20344144201d0301182d00b40401200b0040c01c000c200107031001c84c00e1003650b100c10b050101882e5960b55110b0f240f94004148001a501d00d8130039005800c40f080b030300da09006550900003a07000305080380c0415a441e40c2c000d90304622603440d10f0010b0014506200d185564500e0803401004102d8042201800c0c0c030f0846940c00d40c55074507810f80300d5a80d06060190340031500900710341c00004005030b800d04840300385400d0041c200300700700c0c03d00d004441a0740c0c1020312100300c040c460400e50400351603441c0c1070345403400142c1481e410840d065a0b111424100281010f40e00d2040c4d54102c00c500d084404900e62015000c20a41002480201101c0c0014201e4095010b500e0124000080d17a8061050441d41 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 905840395 1250 905839145 905839147
    0x160b09131803020c120304060f260a0c0203070201050f13030f081e03010302011b081b06161403010e040501061706060307060e0a05040207060b0406080d1404051516140c24 75
    0x17440e802700c4940b07405c2c5503003a0601003c0000303079007210030004d00040c07600301441401507240f03880c85200f03003510103151020040d900208410340260345e201045078031100404040700d40c4d03100940b2021030003040640c1702900004054504804100703102c00200b41c114505404403c100d100342640304480e1100303200007400f01e1054102c0400300030460741880700083c01040449d00341038000010b42c900c1000c13006e040041350451808c100c401559610390300300030026031900d020b01d0007500e00314501920040c0155943d000c201e40026041090035004a0702800001d6241e0807000d1078104807070341d520829100e05100c0d0080b2200418507502c1054120310364400207080103802440d1101f40300007544020015683d0311307251039035102c3c80d46607030080350020125800101924000002d0050404660001600d03050108020030000d07965191450390040e1072068645070f4440b51803107015241c40700d410700142009030032015050410000724131b83d07010070006e0359040d40071040580001c0052050541d0303641c680d0b078 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 905841645 1250 905840395 905840399
    0x60d06092109120609051e0703150606020705120106030501092405070503012d03030507051e0303011404020c0d12062907021215070e03160b09131803020c120304 71
    0x101c0c4c1014070118007800a860314540301418025110704013a1f0304134055030000804004000c03921002441001c0c21107010810b080c14044000d4070340400b0320610f4852404000403d514800a600640003103512100800c011006403510b6003145c0c100d0085580c1410000110081b0344550f030044070f214a03030940e5000d04d1a803c1010a840c254154010f2004100350038031003103070b041d500e403011002440c001c1e2a9151241e2032031900c1d502d401c0f00200e0205244014000c070f009250000010f03241515050a942d0303000444030004640280640c09903d0100d200f00624204d085812a8402c1c3c05040101030a001031900d80304109074a41e00550f03481c0383c540543c00c0c10500003946401601003940300401c802d0944185070840c1d0f1408040c002e00c0c0466850340c80034400101d8010a04042200040c4c001e07051a948109403419119214030884207100e0000402c68095500d6040b1b000b5030000303000040042c5080c8801513900f4440d5184120054880d40b40403079900d140c22070756001155403202c02145814 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 905842895 1250 905841645 905841653
    0xa03061a0c0a061a0d050a020f010c0b0112080d140405010b0a030510020c03040b040b0a0207050a06021518030a1106090327040f09030201050411060f04030b060d0609210912 76
    0x4c50600600b200100e0740016452050b940d4110b004007442c0100000d220b03440c81d03401041143e10381e50010b1030500400441d13510004410b401c81504481400c840f503482c50a840c200b010043c0b0800786001400341c03405140701020004d80e00028019809807000b042800e8207801031048100300b500018100d0392000c458000c0750051500100447c0d014503042e40c0c1040d170f0394400c2341c100d41c2040d000840100f0010600c203035040d9041143c80002c050417981803026a1400d28003a4603207410129903105a840354001944404030300400c0c040c83c10501040b65520500c811004020b50001200701038507001e180c010801d90384c0000180c580d00c54000d903840d0301008035010000c00c112446110301d50440d40b500510380d8008102d2107420840e50181c1c0000c40e13107243c64a03280c0c00440a20036510b20601d010b001c400900030003c1c0554040e0f96204034000d806445080010302d0240541c01c004000d0360802100d0710801c5900032910388486004605419401c85040c07090b50050f08034042d5040384449050650041 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 905844145 1250 905842895 905842901
    0x4170f0f031b0a20010203040312020a02151303020f0c0f4e1b060c0a0c0807170a02010e1e041113050105031005240a03061a0c0a06 58
    0x200310034003140b16440c00d81e8850b110742d030340107000348001155040940400e0058103e480318051150300008624528250750050701100008203070421465021602090b681d0003000032100d107108142e1184a1031074a0100240c007451440f10450050140700f040e0014a400050040d14442e8000c201003104100c210a0001441e020120742d40800741c20721203030901c10005c9021407c1c2d25030350340001c5502c0d0041400e4158204400e8402c0015912444e803585242c20090240c5011040c112070441e0796444c2c10010305e1418010400c0039000c140360304000504030400051030000c4603030803c00106d0032048400303c903854450f0b04030080e0209001b80c4a03107c00d89043d401054084841010394035000051070080350490366844241c0103003010000302d40c507070407030071034030a0380208000d1804070311758607040860340300c06076140c800c0078064064200350001101c80030380c3d4a00c01c081c1034400d450b160b02240708020007030200c6101d40c0d40604402284001c1401d2000119864000f2000c001d05070084941d44903402 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 905845395 1250 905844145 905844151
    0x140a0e0c090d120801051008040f03110a170306040c090f0902030703021c0c022a12010b130626061803190809060f010f0311011b060504170f0f03 64
    0x8490035428003040003e5002140302ca140d8000c1c1d8640c0c05642c1040c0a102c25501c50640e4070b024007044008101c0059020151a200f0550500c1c141d940c058658141a240c140c50800081201c40b91205020000e042c11002d14850101203c1c107100c1c803110b1085c140c0340f0b00003501907030754803030015241808001016001160041d509240040c42c040120f22030300200e4241e01099108152600394440406a0401165250081000070480f40b039100701240650075040c5482d160140b00d0710440112440c000390b01482400002418030000d1640142e04607008001c54003c014a4200a000c025040d140750510000c00c10b08a400401c41130700c0b0703041564071040c42184c00e90305a100400c803030301d60a251440320050f200c00503210050a030500c50002803e04900030001100032184900400c0162001d1a50200b169040001c050b01f48020900403160b100001c00920025026504603004100946c0d1019206502813203c08a500e07120351290311061188441103c002d02c2c050081003840d841e00801590 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 905846645 1250 905845395 905845399
    0x6030a0b0712060602030720030a0f110d03080a06120305180a0f0b040f080313170111071a07080f16170a0203010602071508040b06040b0316140a0e0c09 67
    0x114400b201c00c120820343d24150028401a00007041840410040007c290204403081642c00c0000c690742c00420340c3c039441003502900c2e9543c4410740f08103001c00342c1c42e02801d801e4081d14071401c0080c50b0901510042054420328426803030840c001400c100003504041149234140d84036840c04104601e8290440d2089103941d40c000c506400015040001039040401419014840340d2280d281486c2084110b00c4d960207905140c008220781100600303e952a541510710b000b000001080f4011407050041c50f2400ea004182c84000540b0428000c10347d4094144854403106031000b50381302c80302140d4241d019100c814907904c0724008500000442c0c1101980d4801e6882c00d80d094030400194042c4805059481100303240e40000140304280d8148802000b500020400486001c10b43c10020070b480801400502214145004a852640d8a40114580210003411203168610144087c50150a45d110300e03205026441100b03402800e04002c01021580300c00c61004140c1d44030820764506038040501d031a = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 905847895 1250 905846645 905846657
    0x609030f02041d010506030d0323071101060605090a150806060c010e12030f010e07050f03060a03050a12090f1220030706170109110d0903030e0d0309060b040506030a0b07 75
    0xa00c1c3c8149035440022048001800440d4a080c49800c2c541004c042039481c0741014180003500d1b400d0f06c2841094400d41410004081c029075508108480c55000203282078000d5003001d40015000b80e000e0081d0522807002c4076480b40f82d540c1c444120040b501c400100001140040000410b18a88100079040407146100042810084210b00300e081c40c2e495407180c580003030701009000d100d0841c201e500b400340c20f403026034404509040401608a010b0103d009000c00c00000c000b40300c9407640134581c0c00a41d446401c8401c501c48526200d071040c40400d40190000c3c20170900092202d00300c501401c00c4a610005402c2001c9607a22030110388a450130030109080f41c4a0704112040d01c0400003c001803909540c0c13072103c85400c510700d02882c00c042e4081d0601384d05100700803c1284580085a500f825905000101000300d45020b401a010101c50200301c0d000c0c50003003002d540d4264010210143c4a00010040151845d040008135801030b50019010340c000010000015034044003140c110742c50342444 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 905849145 1250 905847895 905847911
    0x2160609030909140406141e04030903020d050d02011401060e15090613080601090b0a0608100806010602030a0206160c080a0513030609120f0e0f0d06061418010609030f0204 76
    0x42013554110101101000c072040200004e00032980b080c42d041961042800b4041d092405600c6039101c654100520b161200c170021404240c00341c0288001183e018120135000c030220f003012070301e44088030344210144d4240001e20303e42005054480d07051710120303100d0b1544000c40e203080c04102c60f01d41080403110242040b2030452643d601011300040c42d40b0129441180341031544160820300c040c1c2c802842142406501681a900c0310201000c0e02c28600c0c00c6045551002001440c009103540f0100d084c0c05128004200b90360301100600d0fa1492540031a150794540ea241640e03013070414000440040c03002c5481d40e0008981c54010071000314071303290660400c0b82070700312101d0340c0c1c0c031643c0f08640890341d48501000f0451820500c03c00c103081c50400c2c20712080ba102018024101c005040d9100380d21058420750150b840e840e8905030f09401c6042007180325101c5243e00241c59401940912a140c00b280705010400f001c00013038181e41d1242c1c0c9210301a0f01d56665550310002c9400d040b64802c0c0c4802c41 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 905850395 1250 905849145 905849159
    0x2100c03270317011a090d020405072309060a05090307030c080c0f010809060601030b0301090b01090504030809070b04090b040204050402030f1008070e0c030a0e0d0f030f021606090309 81
    0x8440408145420007600450700e454043e0031402e40038100420441820010010b8aa4141c964401c41d069081d000e80e0b900032000010344480c0d42801f0081d40940f5000a00c2074241c0c1c80304184028090203006030100e2081264491528050000143e41c04602000825030891040c0003810300d081c0090210b6890503181c2e038402c1e48940f41074002ea6419806507021142c0c61404030300c00c0c50b0000080c20901b141d82007541519443d000001e1110741450b0b01e4a030b404846817801d6000f20000ca4204d00320b5806c43d40c65014400103080e0a4409a0004000c4008a008610089001c20131034117518070283c40e0134030307007584032001d000010010784d4400da09100014150315a03000441c41003008000c00046450483d000c00d074507000e641c22443c0d42c3d9100182c10321109210b00441c80e00407601d0071000ea140d0341c922501e03001410031821016420b00400b807441200a402c444040301458442c1c405000701c15010814000b00d0180c0c10900010a181401c020041215039100c00b4a02d4082d18201e100c0c1512440 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 905851645 1250 905850395 905850431
    0x302030c060c031c06150f030c0801030206180a0b0705010e0c06090330040312020f01060b090418050f0d0f050a0e06030406060b040f03030e150403081602040f1a040c02100c03 77
    0xa40c080100307c6000c00310200a60510404110a0050070060615419600070427503501410000203035980f50b00c40c18005039610018100b000f0b1220714022540c4600610340717180641800c031020a04c51050b4081d8500c1894154250351403004058000c00760a4080c411001062140351000c02400b03030500078840f4000c4103040140061405868441e1680c040800b00030310303100ca4410039046903454408280030200d41d490440320012000c59011038540400d07406901c0701c40440340300819a20504503200361074000800e0b0b8030030300070301c41d1a440c1d151003e0000684e00c0e881100c011034001343c2e45402045151614030055600140114000203589460b40210074480d40306401400e91030495501c20810164400f80284c807101c0141e0714001b245140c25050349507400f403400001e00d41c5a0108180010390100007400281503002030084c01502001e4524000409003070006100844660660307801d00d003094020130105000300d40c0103082300800c90300c03c03a0040c00032131840000c0649071482d400308070911503 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 905852895 1250 905851645 905851679
    0x304060b060a081f05130e030c010606090812070503040b031320031e03030c0f0f03010618270507091205070510094a010302030c060c031c06 62
    0x3d180c1e44507508001003d03110324026076408500d0314450361001e100715110110764403400c0101e035201069244070400194203600070f8508100035907280c5200040c44562100c0100102c0301c49a066440106058000c640c0c18850b104000d4643e900421041000b00f8181d4002e50b4407402198041c000103095550752404100324401d43c0c0010b100181d05000c207481e0901440096102103180f0301c0c18183c031541816201d0100503d807580d05880444c0340c070407500c040c2044905100c07807000001c0c0c1d6076031510005001c010301244022070402e0b05510114901c00626200d10340c1355a00c080f400c182c00b00110184019100060640c1d08002000740000340c50910841407050380351164014002180c01d203400e02004010b24074150741000740c0070404001403d10380490464505000b00e886442041e0840501001c200700d04085031003030303007070040351610510244219043e00d1003202911051700004082101500940300d10140719081000032801c485540c8241c001c801d20081030105116a46080c0685000012 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 905854145 1250 905852895 905852897
    0x503090d02060d14040c060c3519030507030b0906190503160e0f101202062802070504021912090206030403080f011e06050307231e07170304060b060a 66
    0x2904c11301040195040306071002e802c0c14500010b4003079854940c100c06840180c1310000b20f00702c1c640201200d85001505000a00821410301e0f0384000c0d01c8403141c0702c8115006d10360006850400440c4050b8031a00440240c6a801803802a29840e00c1c410002040c1d01408104c05860446200007016107040c0040c81d01d0f4014501c101c1e490a140c4190080305020050403028048010800c0264600a00704071805483d10305e00d003c0d11860403403001c40d181e4030071300e0810b0030031220040e44807402d211042010450191694241e9002580c0d80b0300b880300b43d01820a402c00c1110010b49140340c0d05220b822074149004c3e0400b00820030300e069401250040d4016070f000c1c1c001400010070840c0700d00c00e46200c5e500402200c03042c40035603044a00150f1906903a400b405003004800030114a0051144491504400f4200d070424281e042c003c501036020b5020240300c1a5548100400002e400c201d4020b440700e00340c001c500c07180c1d4041a800cc0c0d98080c0e10042c01242d11590303a150300c09942d11040d001e45101102 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 905855395 1250 905854145 905854181
    0x161404060314160e1605180a270c0207061b0b01060206060a0e0105060910031b081b0910050c1222050409050d120b180114030a0503090d02060d 63
    0x900400300e00c031110a030820040302c144c107014441e00000c0f00b0302081108080b07141c51500c60300320b481513142c0f94200c002116400b801c0709102055044400140303203040c040c02c1c1d480c100c0100401d66205d0940c0c02911407080941c111780003c103c880d000d14091105100c91081e91000d1014540d9800b000620030f8008000590244080100c00d007007410100d8050000740f02d150200790324040c001a96845413001c0240645502c0c002c180350a40250000640c00100c5108001201400240144a250100c843c032010401c00f40345a0070044110301150100300014000b0000c20140000c1510160722000c52041648503400074144800380c00c601902410420000d1904140e001c00d40040202c10141c00c111b1045c1c0c6050420300000304002904a80c0413040d04280c425200d03e14000c000800488120541164108800c8038965510f000703464140c881c01c0005c03000c40300c103003028155a00c0070820002c00d290302c1041007914510303001c0050010076100400d62071030201030480352070581c0c004940307441c00340704 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 905856645 1250 905855395 905855413
    0xd0b07170f07020f19170c01050906070201050604060f030212070b0a050a17070e010c02130f090605090f07090905031b010209040b03010b011d0604090c180503161404060314 76
    0x1505001e040303404c0c04003400625070001c6500c0d2019251101450052168085043c002005641001a01e007200d02c1840208003c0c54912159516801c08683e03c400552801d4001840b41c9000c1c0f00340c03416038808481401c1c103281154280b01d452011903941e110b5130b105d110800108508001b00420349030070141d68064617103212200161074008131210500c02d10072030380100030b0420380c0b00d0310b0040c101c802480c00410b0961030f070000c9003d4524a00c18201d052303080c0071145588820030380080c0d00c145d200b224200318590f90801d1340c40c0c4454240024440c0368111070410014910181c008001d242e000d070041d285489000b07507101211410482c13019003281d40205104045280c18456060329640560080c0200c500c2100002c20f0a41010b100707150700c0c1e201d880c8003881d545442003944c0c040c0422040070072140c024030401420a00b182a0448040c40c0c107118085176600340441d1040c1c61441400c070b14080f8500b040312503a44400d00e8280c03e03400580d5190300102059131aa03c40d10041d80c074030042e1504d40 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 905857895 1250 905856645 905856647
    0x1203070c170105011505070303090b09011505030c060415021504230601260a02030109080913110f16120807030b06070c0b07050a1a01060306090b0d0b07170f07 70
    0x44508901000c0740d143c0340042020030745465481d00304403d00e1074215038a030021b10703066008107083c000290074011000c0030000c044105505c0704c041200c8400b11020400d0f524001c2507a5a44101e0019402041c1031108100c00f600350000f5180c0c0f0010350040e595543c2c40c0c11504003114100700c0301580e11304100c0c22000e02c483c0082e8058200d062080001e42072541c1000c40d02c0306103802002083d10000302c08100c0e480c00b0380092110050040d4000c00074098080141803180c016041406558843c158512a91980510900c2032140346212200f9190800341507090b812080c1d0000340019a13140404225407001641503903070000800c10300d031111141820246401000c070361240050a004200400100011844031904081120100c24090350b0f282500d240c00c2d41006203045000706000d012180780d400e074a407800c403014103943c41035404100b8603507110b1415043d910b9440300305800810303040d0f051020855186032254044454146030052030a440e6000351803070b0013166414224446ea509101c0b0903 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 905859145 1250 905857895 905857919
    0xe0d052b110a0b181209100c0f03080a140a140901060509040b100f0b0a08240409030509060c0a060e07081e010f060602211e091203070c 60
    0x525000d14100003034018441406a07a0241c02d007000d00455012800100f100038000c01d841d0589180c1c8054440e02d4101980050003600104440da10543d0220440105e05200e881c002d00d03541d41003030425403a02c04a44094800e0800501070700c09003500c1b12000c4560f600c411400c0786c052840c10b040000d6141d500828900509070203084083c035039050042c104290750301c3e0040540c00940000008410f611a0302c2103100310820307940801c4035444100000529070480c000035107201c02c425280c0942070340c1c407c22500d00d404c00b032200301c19082d01d150b100c2034494241640840c205511905000e4175002e84c840c00180a9005001c00b100e0a500c05040002080700d03a00030141d0107110040200f40050400303905603201d2403840011144906010086220368009402c446070211843c0010000f164450074002e44410b08290f403113100310050f00d08000300200d03041c03ca6007070701948008110114000000da0180d5030100c0e11140e48100e803016a03080e00e00c802d100030000903204621000c141890101d220443c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 905860395 1250 905859145 905859223
    0x50304031206050109030201180e0709170d1e0e03010501142b030c110d1202010c090602070b0f0729090102181c060e0f07050d02060a0e0d05 62
    0x8490700b00b201c00c102c1079801240c2903050b01d5090910010780e40f42413000482681155200300c4880b00e80c2d60600c800181c00c2540c4006440303100741d58201030a14064541c2d40c58503921003600001b9071140c0420003110196a101a12080300e1403c0c240050380800006d003516003e07007141880c9480840002d0072440c18040007040480c5080580c100c0781201c1d009a12071402814001c0c1c207200001c6418801c21000000b00e014500000740705814800386c83c00c12901040710b0911420156182c800c01e41c520901685540c1c0443d003d46d0b0040004600703180040740c542d0001c41440c0d60b00c8105118040004440c04044d142801c01c40c00b090346a0300c2d03e44e100000c4214007520402507644104142109803640d100108a80b5009454140c111004040c0211050301642c0c4080c003480d140200400d55910041f0324021680c0c481000c03180c00300e403074400300710300c03050300101c000d501401c10132059000500542c0030100d407601c01003684c88003030496100e8a08280480115043c45010403030b581e4803c228034010105 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 905861645 1250 905860395 905860427
    0x60c07061b1e1103030a1104030807080a171303050c0114090d2c0d020a03050f0a0c17030d0c020109050a05070e0708091f020c03070b010806070519030e030f0a05030403 74
    0x14149500c03c6a4035100d00c4040e080100751070304c8055441c410402c0200701c2c0c00840c3d2058100340c1e0b91165041c07940060300000e0381c502c00100308100300d03240e400300300c134132a4000c3e1100d420b40320310b00f0210b6074103865a0303110a10000845d52250740998900800e6900a23205040d000c0151840a1924400805012504000401d0003c0544055903848180420030380807400594142d01041c95600008902a44580c00200030f0f10071380c05c1103e201d550105100c002180705942554000d0f4170340c60000d00c9151101350701d40c19a401030004410401164006010b20036050000041210298481604002080c00191410b900c40c442c10001034240c0c02c215580820f26250956003403e01e04038032500e5260381204440852005c41800c1d651105550484800814920031a56520340ca80b415050220342481140300501820000032000d5004d001104c000a40301c540e907000003100f04030260014014400e0210042c442402804c0c85041c14100500c1900c3e03898079099141e1900e0f01d0000d0000103903000e07a003 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 905862895 1250 905861645 905861657
    0xe0406090c09290409140601080c0d180b0c0309100501051003050a06091b080a1506110f06010306050a0f1a0f04090210260702060c07061b1e 62
    0x1115070081c0302c0720a03035004802c480340381c003401e031140314140329680c1521180ca4000200051001115840700f256880c480c2c070010919581d030310042d00c104008880321100350404008224212071039900c410f8184a490510110783302040c1c840001100d81141d00c02d0000400009000311000100722881000502c060288100e43c180400320301d000999188031020b00d600c0708041041c0c070110b500444041c00c03040000b04110700c05195058503020828030b048001c65901004514409014083e2846101b51649068455482c2460031103a2091400b421002c07409104616105500140545402075000d020007141074100800310404540414100c2c80301c5a2900b0310146412003802e82c6d221034082c0440300c815081050f6400314010700345e1580c000703611a414100b45031300c95411100c010003010510142c600584000c00402c421040143c60240c0540d00c0140040c441d0601da8004214179840ac442c003107003030ba010340300100e040000650848045a400408101c8891071b55000355540000c1d80b03008 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 905864145 1250 905862895 905862911
    0x1209020105160809100905040f02091c0203030f0304051509030a170603100603080c060c280e030d0207031e0b130f020306150405060a0302011706030c100e040609 71
    0xa8420b01c14040b07a42d403001450701c003040600c040c3da0f040e50f01d20203014042955402d10200018019078403401080d1155141c010070224103000c610a9601c80b002c060b24249180e03c03a0310011401c40441c0f0000c03641480104001c100d21004500558000c521802c001c102124007214403c0c190000240001c000f540280281074051350b02030600c040103500c40480d55282e444080c042414020701c0e20507944558144400042001419402811012940000e4960380d445010b10b80c0c030079100e40803400740d0900d440c170680060451014403900b01c030318050400ca141e10003a2070101e8100310201c5044800b68010341000c000348031003800c8200d01e02c04c401c601c0c0c004080455070303105131040c8081c240100c2c910303099a03d0400c0041428a807410680c00901704e400c00c1c9006a400654000d01190b000d02441c10600482c0341030501065101c240e940c16102c12100f40350a0070080c4034948028101540b62048000440706621100c04005080c0141d40e5600e241012420038002074882a43c4072520641c940241 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 905865395 1250 905864145 905864147
    0xb030a031e080c0a030f0615051309052505300708070203181306080d021b011d1318021e18130c09061e060f27080d12090201 55
    0x45482e201c3c01c500b0b00003010a4440d529000600e1243c1046904c3d030382c0223a06050b19900711029204280110080521450b1144c03200c000740c4000769402c2c00c0303800d01d10920704560764504001d0000401d40b0b2a200b0306100000100380341030301d0f0303007885038842003540002c1c1d02d048503180340840d030701003041e040003182d82c180708034020340d2803080046401c003d410640010815680f0342a1160201860100502c411500c40864a03121243c1d451210301521400c0340c904507c000510115120010586946c1c801e910854901080004581d0308240d0210ac0303a41e240c04400101c0c401c0e5040c80440303100c200752106251041c80314510400304503920350301c0d602c44410160b60703905401103007102070900000d84503181c10105034826840c1d40c2000b0f04403604a2000300303160f8140d6000b10110386030b50929284000c9000c0080310b4001c0716014034800a0740c0d05800644250184904040011030700050024504002100e82e00102c015000b00d900d40e002904408491540450342d0840240400000c11650f0780c0d50340 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 905866645 1250 905865395 905865397
    0x1204060201051b090f030a0b0702011413020d0b07020a1403040501090e040807030e01170906061f02070603020f0f13050909030310030b25020f0706020c0102120d0b030a031e080c 78
    0x10892054851484961254030305001340c428030b50344200d030700d22346041c11308010707028044918415400e094000c00181e001c24010081024094016001311224601e40c2c0b111503000f00020094419481885031a07000074045859080d520800f1074061a1a5400d00000601d0300300035a020688401c4c8034001e010104101030100c070241685400c250055814060059031007165004801d018480300303600b0084040b4001c544a0b06c2840101c440c041426040150307560481841007c220040c1e000c00400d221441c0030360b00400e0040641340340f65040c1804172003170008591043d104c1020007800c21504002504014140d81d820421101c040d502311310f84188000c481d84424407018109990344400f0681d180000c07000001030408900b01c000d0903400c00500039584090b004088a01803282c4440011954404142c0a00c4d0304016806000080500d558540090304036440c42d40420b540c0d24104031080c1ea040105800b0b46104c1d444031000d484204001c900d01203002c1d0f035101c2c1031140748401c02282c040310030 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 905867895 1250 905866645 905866657
    0x31f0b0a02070e1e010e040b06013608010c23070210030b041413030806061303080d1b02071a0a0e1c15020d0b0409030f050a111204060201051b 63
    0x241407008580c0e0b075840140c41041c2012191301d0701510050011485400c049070a81c45280107010b5011240c46407001142c0d540c954100305172414803821241c20141507144008003a00303a001001e04240303515124881d0858040100b13000c04102544100020704e50707114181c01240c01032050807805c142c020340118900301f80403401c80080613a02c806402056840e94440134aa0071b0710012014603103401035411450310010f24040c0c0100c4e01580000781103241250864002c001e50354000c80c81140b842c1e6600740981c100c0110140d40c2d5460760001c08050442400c001e2261142d40d00515920b0b160242803d4605401909000e100b54100081040715402007007541803a04261040a1681c0e082d001c2d0012032134015800400c0806260312000080401d40c002d040700090480081150224400802084944080b00100894010a0507681281c06078024101000b01401c0603c060b020240842e401c0c45102c0b0b846413210100802c0034410300b50f092141503130008010030b021048001071192050940906 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 905869145 1250 905867895 905867909
    0xa0305030f0a03060308120a14040c091e090318080106061706030a05061611010b09010308071412072f040b0a1a0903010509120706020d0e03031f0b0a0207 68
    0x8408030b140344282d20880c000d580000700c440c0c03159001d1640e14031111040d02d001d502e01e400d00204580d071089000c58180540d03400542c648402e80340a08c8000642001c000300742203218000381410705903d860207a2403a00c0e209039500c2c05490b01210200440c00240e0f00000c4480c8e00d440c8061001d80d03000841d60b100600c08442e4003045948a100280c40c000ca0614018020700031002071203030000a080510302248103988505580c289003410032030880d209401c80c4c50b40301e0402c400410109404c00014040382d40940104141c28041d612038526000000003582076041000903407205212491740d0310111503600701908516640100c2d041c04101c424440300c0d170f102c0c5588107030b0704405503a5122010010705407a0310a1202102c0d003032000344140c0004030b04074040d500b04000584944d9001c0390755821f41003501540b81c14809d490b202c41000b90480007900001980d81c0704d0030f1445242c104013540c81001d1110469404481d086100100316420307510942c3c0495051002201c41500810300c641900c2071 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 905870395 1250 905869145 905869147
    0x6070c0b04020d15050121031b020d0b0c03040618050c0108180f0604050c03060402060313053405120a02040f1b0504080d02060f1f030210020a020f0a0305030f 70
    0xc0c5000040780003c1c2010020441c0c07202c00115500300c5030982000d4100d400e0164104c0b850b142004010120081da41e02c0100040e08582c88601204040d03061030382d42c6030000c0d0003850f07050483e81d0707554500380055411411401010040000300491806800307008000500d2544000d41a941c0d4240d0711055006910305200589001030002c01d07a0056810040801310110340708003042202c19600c0740760030342c1e050315035016140b4000ca56060010340c00e0300465010b00781c00d185598490a0203103100c8403a004542501464007002c0c650080e00b4136040c00d58840da0301c20036a21512000e0f550031201c103940304038040d540001d0b0003a820b01c40486c01d240e09030740690300854002540c1107004024400c6843c42c80c9500d000768048605158810054402c1e90740401c01c4071040d034940381c3c003070741e660b0000c40f200071604c01020f0003d0311110403008041e2154103103e07980038909031254000750131b00b50200c2d0710400682c052400303002945000a103050b482982078a80110301d44c20340c0c0700c141c0c580c0f103503c0c0b2020751214 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 905871645 1250 905870395 905870401
    0x6040506030402010c060606180b0f16030e030a0303050609330f031606020d0e0d021201020c0607120b0a14091f08150f10060e010302040314010b0102010e06070c0b 72
    0x4000c0580040c0e06500980c1041b016807a0b801c007404001c071114582c40036000c4603000ac035449040108480711032046103212070400d0b440300004414036401c20340407000c025040c4100919600c0c104540c0c0c00d40d500c00c1d20049407038904001403000e2000002e114034081040c603d050301e039003180c03000b08600c07140c401004040c1c0900d45801180001100329402e80c0c00d0710613404c89000105154420009403155542942e40c4002055000c840388030103014043d601103011142d030401850030340c03618846041994005428442c00080403428640103e40d880007060740f0100317040300d50845200d12184144100c0b10b00101508150016540c01c0740c0009150160041c08041108040d0084580000600440c042c550044d01d681c0e01503181c5e03003001041c0008000250102c2c011082c405012880b48425010440600d8a008070407a6084c4441c502030b03062680c2000048045441d21440c0075a80c054100017007038200d8000002802c555030005400c2c2180c0000040c05016a80405e0446c0c65a411911300c0d2180d032 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 905872895 1250 905871645 905871647
    0x51216260f060a0b04181103010614131509140103020a080a090f050a2915010c031101060f050a08010506011d0423070f110d110a021c050115050604050603040201 71
    0x7401613008101a00c1e808500081c4c16900c074440d001c0220282d400500031521400752111241c0002e0049d000401d09101c401208640408041d001d400e000c4203481074465960284000c00f00c03005450040040c4c10328a05126000c040c03210346050010038070301181b0701460707100c008014060140488a803070351916668800d10410b500d000c20303c00d8104082d02d0703000c41c103841c1c0740e003c1c0d030080c1555888079110b60381e02605d950942c0c0c480e00e228265500200106098610044030218985038085040c8140c007055040407001c24850200a01000418804603038200300030020158082d034052400341c1e0519003001501d0741e2043d0591501c03030072040030541415450b80041c0140c400403008002c8451420320005508602e2041140200e45d070b43c641542016915108582041004015625561001d480700e00c82921401f420500609039400796481d2280310b900042e0742e001e00390201071402d003944204030305005080c401c074410001c07052801c00e100c614010101d0064001c41c81201d12401c3d02000180540e = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 905874145 1250 905872895 905872909
    0xf0605130b0a0917010606050a113c012705010b061c2003060f030106030503040e0103031709151e090601080d0e0916051216260f06 58
    0x242080d141c030580c4505100d18010640341051083e00f10085602410b001354920600c81e103000e03913003259540c40c6446882032080d564848105034605943c41b032881360800d00c1d0700e80b02c4003100800d4515000182c10b01e180d800c1c807002c4c0c2031035103014840e079142c05440d555090040072064600070418000c0d031060328103420054010408454241d40008000594410300400d01003a1050304858a03410002c1400c80b81090000302c541d201c82e00d00203c804c1000ca0114038003d0040f03500841c00800102d107043d00d03aa903085c10340e0000d50000c0000c2041c00014010160040214000481d0040e0396426500c1c200c00100e5540107052005103910440c400847d24405101e03140c00400168150350750f88074180940d0883d5660001d1240500303078001c05901c8190184a0b82000340300b600003d01d045016180c214040c42e44908004140044c42410000c0251080000005c10b1140c3c103103445c0314409070034181d006132452080703081c02c43d1140b0b4101c1c4420b201c040744810840e04014900e48083c0283c1d07469020942c9 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 905875395 1250 905874145 905874149
    0x70e0a09110304023313050a03050d0f170123030a0c05010e0f01050f0a030e16050406060905060d200f0702040b0a030210030b1c031115010f060513 65
    0x445400d140d01c002807100c2500081d40124820b03100e0b0003c102204000007070340c841202000c420100f099280150703102894024068100460b41c3e000c051030f0341e800c0090302101003540119081e0b080345203041252a0040040c00c41a0301504084440d54246414050203c0050003007400d0fa140071580011000c081c01030300c0c1201f0601070700b180c0b60078245007001d40401d1000c1c826070380042c00f03000d00e000141c109400111240c0b001078682c641005040300f1455082d8100d2a5030104046d543e03265444061410881c44111120b151341d103010140c01c00301030100b95070b00e0b41c2004091020032a4200301a4603550104d4008802e0040001910001c07660114401c0c490003048655200000c10304001c0c20103450014000d0601c02c41d0b0400c100760605044c0b00c0c5c0000b080c40041d50004c0c400d1090981c1c2d9001c1c2e00304030380545e0024010500100030040d49005840c1d01141500002c1e112028203140040400221000090035400c480d000c2d0700d440408009098540110340c2003000c00700340341008400f003112101c0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 905876645 1250 905875395 905875409
    0x1e090305070c0e090609010608030a0e0d060903051b07030809061b100c170606090904030c061812030e030915070c0b0901080109091e0f02040f0507020c0103060e070e0a 74
    0x180ca64410f4698040c1005030742d02c0226003d444042800d10005208101c200d61055000d0340c01d140c0c90403406c1c1d825803000180590804203514041740000c4e850311544010510946445031105d848140a6510b000b02aa08051036840303e40140b010840031005d03554a590704803840c1d5520003071040c0c070051a010074940c000503481810b06021561615801c00c130380c05240c40c0c2c1c40a070090780c0351409440042041e104260800d40411140103203040c008055540180a820010108129035441c00c0403038080468608003800310b00003810070450b9400400111455500c0c1c2445050040310310705482c1c0c45440c000ca8440c0c8840e18403c40101b91314810307162240d0f00030310400815584d071022034003650300c07401103680040c8001c070005c1741c101c15501c140311b07805400c1000c1200c034450512620301c603901e40d410151041e014070034001c001641c5502480b80313101040342e0041074504010300060300e40f0080d06c0406041c1401d051043c0214101ea11751194040520714240d41c00c8080d040c08141c00120030b0300030300 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 905877895 1250 905876645 905876663
    0xf070c06030c030e060f07030c0912050a0b06030a0b0609090a02041109030c060a090306020d0b130902030c06090f150c06041b06032306060d150906091e09030507 71
    0x14401c0c1c055200c80305111403501c3c103208035030345040100e40302e40003219504040b03041c52000c41c0c0c02c584030354011102c407105410059060707a03e420310450f407484415001c03074165012440c841c040140d01000281c101d581503000f00782c0742c0310a6503007070703580c0c00020000e60007950308800049200c40b0801507800e4103500904108a1b00000300301d00380a030b038040414180613102d1030003840c545080c4802280c001c01e60b17540e030341800d00d030440c0e884034040e500101d0445019a11107415540c241d5407610740510f040c03c0304000144618082c811300d82040c10350545584500710501000c4003e45400c2d8503010f4800080300c4404543c164485001d85901450b00315014501c50320041004002d40042080341504010b0f00054880ba0303588c81c110701b540e00c50031032043c00400424901d20b207000e50030a1741c0c0c0c00002c01031549003007255000d01041102c0c000c69400a55243c1800100041500c5108003000b90203100000d20100100d005442c816072404000030640680e20070b0560140f6201d6003c0d211b140781e000c4881 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 905879145 1250 905877895 905877899
    0x140a12111e070b011406120a1416030b031b130204270b090c04030308040f2901080111030f1005040609020703080a0606140906040f080105041e0302120f070c 69
    0x180a5a4000920403110050f10390000b04070200c81c11104221104000c10b145c1c40e103280c4429441402034080c140c0d000d103d480d15000803a5a003082c0320b281c0f2401000140c840e003054a0300c00201075420444c03105010380c200c2d010282e55042c5400302644240e100740c440ca60b0b5180074460b28002403103154044001343d80020a014243c1442e4598149148060881800810300d42c8040101c800c509984c1030008510404c01000000d0158040a07407150042c2d0300c01d20310783e201341c0b910b000c4441d4564003a441070500100040c1d0400741f40128a0141000d4002048401010640700b40036110181207201a4000703540000c90192400d141000a400b01a2051001950303414070140690880c000850100346c02e840024840c40451207800e0807507216039030300c980340040480c14040315072140d5800b94225004110210700300c0c601c00064402402290000a1580752606201c4559007241480e451007114010208000c00d500041541437500244d05159982014101d540d0543c42840700040403c0700b40540 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 905880395 1250 905879145 905879197
    0x30d150503160b0301050d02041d070f170d08060d05030a08100e060a0b030a0b0409050c0a1a030105100c021e09090d1704030c02030616140a1211 64
    0x8104454050301114842030b0200e81480c10556603000c0d1200000d0b06000400c0359190641d400042c40d40064000518208010240d0941441604004a1582c801c55042290420001041c0d004244032650f0511007045040066117860607416240200401c1d200460354aa071043c052400c081d40c0101141e640d0106510080c1100d4000c45071001070351284500054016005c203078040c4030709002090000392609101c1c0c2c40100350000303410800f01c20380d205011000341c0c440d4030a941440d070051004114484042c006c10201080642040c00c1d01d1204c00148030415134240150b90640d0310458070070f040701c258a4002c4840440884c0007035840960792010304a0160000c5010441c01000d5505840954459143d40c2d03a4150700141b0200050b120320035007055150b200700d103a8003c1d100746442c0020703450640000e443c1c840b050f100301c06000f10501d072802d059a0040f008240040042c21900e00b040340540d00a40940c5940100014041d01d88000d000003560000403101c206c0000d0701d0428004c03940c464 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 905881645 1250 905880395 905880431
    0xe0702070819020d02040509031b1e011119020c0409060b010201151a09060408010c0809061005010e060903070308130f0b0c121c0c2f031605030d 64
    0x42191954050514482e9100a08020900406802500038011500e0b0b82d400e02c002400000c2050480780400c0c40980c0400c141407a40e140d14100c0e100040281d0a0360f80b0045008400142401d43c180e0716061720190501c010780700352038071000c5088662046101e800b03401e03401e00e800c180c0c205074800d25148820b07080060941c04581c1e580c000380d008000d0001207140400300c5030f0085c001d0100c0c102c00c43c207540460010b140c000701000c060191140e414a561a540542910000113450011072442c00170008804030401500e54000100c903092506507143c01d001901c5040c5203c07a0a000741e0000510742c034070707850422401c00159403042c01550386462244461641901e0790160105d0f0850310400040c011140c00305440c1c0000c1c9a134040c1c40c080141138a4801c0700d50211040c4c18120500814008001503603101301094080c260721240130381c0080498001585c498a040c4038101e4007401940c0810110020079600c2c900105110100300400904000b440c0d1f0141c09410300126040011981d0f260103070107 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 905882895 1250 905881645 905881649
    0x602030a050601020a020604090c05070530030105060304030e0103020c1e070501080124090e090a030311032e0e01180516050a0f03060510110c03071202190e070207 72
    0x25100300060380342c140049844800107003000e9840340d03080c0014041696180d12007a031040003414841e18054031691a1030510280d550b0040380f00404075030a0f1440750214040c591199500d0000d68555070500c4006000c0d8000944080c0030000612214a0340c0c0c0d004e80c0c110380c0c07450440070895944500601c0412480d10003d0020300780b60159540014195019000450680d02d03803c01050100c03440422100340343d4440300d402c0c010001f07656000105940601d81e0a40520191030250101d01c1845c10041c3c1607840b81288801440d008004000c0c5000102000d900880441d001030564606060180c8001c1710701600203040308a85000002080266100d101c0e000820354403080c000d5030b5945011040390f464610211010800411020150502c51380e0040d0120213541030010f010b5840c0c80200d007a0f81c5002050001003880c2006070004040c0402a0101c40b0714100c00400b180c07810b004c4000051280c0c14070084c0951040d849107000d440d01d40d1048c1c03024145c1918516154030700914020740d1042030f8 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 905884145 1250 905882895 905882911
    0x1302070609120201090503030105100c0f14060106090303020a0308040309170c1906020d11210309100510143d03060f0e18070621020a08131e060203 65
    0x41c00d0b400072158010f000c0d418000f9044800b8606580ca0729040c84500c1c40002607181c104503003103628000248210103810801d03400394011403100141e8418080c0b41c06e0040e0041820b05c12036202c2000044e5000801000e001d41c5860b181009850342e1400f40c5100e02142c11510104520344014200350100041015202c202101e050140202a54181c00ca0421038050000181c100702006604580035101003d040c008150442c0c00000c030030346840c480c446010207405002c0b0000130134081915810484c40d5403003000c00360108400c3c10000c0040518011511580c00310a1b001c01c41c4106582d03492a00d1403550302c02c60901d0341d1303640790b900784590100051413114180944042000f00c40030300c28400d200650301d4900e1a240c1d40340c100441c0110740d01d0020801c601e001a000b00b6040301d01018045d94001b066130780c039041c1c0a0200360000382c1100011005811200d84148800c1e000302e903100b00c102e500b00f038116107030f1042c0b00064103181c00080c0d51b200c0109080320b01d9194140400003982e008503c42c07070b00c0b = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 905885395 1250 905884145 905884163
    0xc0c2102070e0c040302090411181f08100c030e0304030c180c080f0a0b0a171e33040305030103210f0503130b01030c03060e1c030b1302070609 63
    0x250008440b000c9800d852090101d1014003003400142081035251750803d002d804c060200880103000140008940c00d83d050b802503079072040c002c1c2040c5002e078800c103650384002002181c0d42010042943d400c5203105042c2429250200c80250b5030280d0320824481c500c49003501c0c3d4891300d070f0501c49040000d81c4503031681c44170002d0402c04061107500c5180483c80b010758805200b9110014505a035003001382c45503410940d101106030642c0d172440d0202005102d50100807807401040c100680c1099161444805565443d03110456030302d10104003003e80058100756403954a50581c1548030303030700503100d03c4a205100c0c1c0d8140000e00d900003010758101c038800c0c00c3c1c01d1140c80e1110740c915034103c1505042004a07034a4004491101e0041c4080d6078400c484506220102038241c862802004080e0f100303460702483d401040c018080e4601448a03c2c1c038651000f0001641d02c20b440c0c070546511403049408150750f500e61140c0a030b40da031b2040e00c82050304200c04e545030031007414808004e0502d004202d61603c0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 905886645 1250 905885395 905885399
    0x60310170304030f030c110612011418061203130b13060306060f08060f1302071a0c0a03110405060705100e0105070c060207080f120115210c0c210207 66
    0x280000807201580e5201e00c4d40180940241e40035070304001440000c5031590340365103445150b520760802501e280986a020110b055252041d00342d20b03503074041c440701c0c000d0850301402c5010b07031003070451141c1020059404421110507540694118040d0141060070000e02c008001507240701c0303501600319070181014083d062542e8010a408071059803040342c01040e207000355011594001d502881d444540a0a42c1c2d00070300114000540280c03a00400384410751f80420890180a54106080502500280100c5160401101b10303a00d502881010a00b0941c685500745d0480328400191002001c0140015490f8407680c60095150350200c20340c0c1850919040790f40d42d07142e1701401040e004801c40e464135164010035440b0795019600c044030540d01404200b00d006240198031000700818200c800c44501554100313619241214110313000c01c6c04005040c1078001c0c4200792440101d880702000b900c0000c01688066050340d51042c12080500b584107080155880c90000c403d26550480b1f4079825034401503 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 905887895 1250 905886645 905886689
    0x403080117150601030c230a1206050a3308040615240c0c030c0e0702030f090904020f0d080d1401080c0f0d1407030201140a081f05060310 61
    0x80e01c031031410b04070701c804940840c4065000e64003800041c45146400c0003060584403241044040203049400d50800010301900c909500c40c01310109404004000d100d140d01e060b002602215003401045054030b19102c07040000089842681207290313940844c50b030600c1c0040d002402c0050708883c141c2e0060705204216604c407546905031001da901024840038410000f102e690269240000003501784641d0b140c4520124400e41c409100a52141c0388505403942040c201401e00394002d45010f096510601c4108180180f241c2520007901c8180d0300d0512554540c00010214500e412116800c808000302c250103011000004043e026440c45091100d0010344605044000c1c00344102500c541141c00c064100707107003003d080390300e03090002c00c00007407146c00341c40d103100c1c007082030b42400001c0c2d204c25810000c658200742400c1c0c10022041085080000085010300034210080c080d00d11004103012004520038401240d2000d00000341002d902d84c82c0c441c401c3c1e9000c15089c0101c40240d903400300102810 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 905889145 1250 905887895 905887903
    0x10e074b05040b1206010b0a0c0c0e07090b03070207050d060605040212060108010f050904080a02010e1c080c03040f060509120c060402040b0307180e2b2c090a140403080117 76
    0x9111394020132050f86003005020700c7d40c01c10b590602c00c000800701c0e80760118030f5110761603002d44650744030282c25042c076107000740c0407600b2544030348644c0307209000300020a41c01040500449006a07100301d180d40321403504400429440d04015440303440400c415901000c81d0354080c1c40303408281c0fa1440d099817686101e6071140060700c203480e803005190000500041c42c01c5d015150110070b900002c40c104a80c003413610b00b404000d08a154040504030003051840d40d000030216081b0544505562a6040c01e0702c800303600c4450300d080a0511a1944041a05c07480204000c202c46420200c00b00c5e2561005806a600d84070141e5046e4465414202030ac403040c90049100b504031000842c0e2040c4128030342c000c0c0c3c0064864403030440f03d02e0083c0901d588100d40c041016000003074070300c4200884071920a501504c201a800d000c0ca00304c000300b00301558107401007003a10700c480744d044505010540c2c4a0740a07002801c002d0b0720002d01c0d825001e081c03100b05904444103d040e00c000311410b0f00c2c0e8046641101d0742d5 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 905890395 1250 905889145 905889169
    0x70b0901021c05011412070e0115020706031107080a020a020310020706060e06031e01060810290a05040b040902062a03120106030e0c04050117010e074b05040b 70
    0x480103c4075075074203c1c0c46c10604038a000c0d100c201c280c2d030072560f90b0034601540e460241c0c00590b80781c020751614940d00c0e505120a00280600f4102005449074a0001040c940107801d03000f0640c03c1c0006440308410b008108110704168014200e5000341c004002000c041c1d0400f03070080b509031b03081110210340322100d8031f083e92043c00080c00030315650504100c0b030541c40032540103000e400d558410300803410031001d0008441c3c0c0c008003000414003d4401c2620080c00036030303026003030010301c89a10240c0c881d0384001958040310310032078002c120891414005001404400c1e0000e40c040400100d2908401b250310040085852a0b50071129001307a855801d5200d200d0405a204c1269140300103020460182d8002c20141c092007080340c1c10203c4640c04039048480a03003054a008001c0c440112420109018000714801c135803000e000c040707240c40380b0140c481494800004801d0750880b00d00b50000d030303100c0004e81c60b206620200c04400701e00f14840c1e4080591401818000c9081010100309030401240820b1 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 905891645 1250 905890395 905890409
    0x14190f1412150402180408071203150e18030c0708070602070f03080f0415030b040c0507020d1103011e1e02180d050f0a0302010b0906040519050a02070b0901021c0501 73
    0x20700c01e203214412000100e0010303c200d038000740703040c0852083c010f25907089200703601c922802ca64440b1a07003000760201ea80344284d0000c00d410284400341d500c0d500444241181d4a842985100741c1740d42c003004241100c4482903040350b03c008203c2e81010100003c46030221014001521a01a240c000498655049000743d1800318448403040000480680040c01c0912045030340314242904c0e01c00016802c1c4070320780d208000a84a0307500d20000e2a1600c02d5298816190400300e00d0400c5690202c3c071070450104020700f0000c41c03c0384846040d1400c0d004164000000d4a5915024500d0100e100090048503940303022000d41d0706403000740452a2088035011011507101124840340f1008200c420f40c1150011929402030090000c4100e10410040c05800d01c2600082450000c4406103c004c443c010b0845100b14201410f03c614650b106200c000982071250380803c8582e12402040701900c2680780041404072214104a04201d040d4094111a68a040c19440c01c40c028100032040d0340c020302400c6 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 905892895 1250 905891645 905891653
    0xe0306041203060b180907110c0f03070302090103031701060c0f08031f09060303030b101b0830090a3f050301080f0a03020714190f1412 60
    0x401207107480056a050464614003c00e81607101c9914083c2604003100342c200c007642c410141c9420f0314060005e41c0e803200f854500502d0711690403d0103503031001881c19003800740c0745d584680005130310b0034010b44000d542c001d0f00c050425650ba250041a500300303102044d0b81540c0043c00440d00900c5940801c001a0b04404200d150032501e407100c0395260300181041031041c0780040843e0660b0a100b020b48000c1c150703107100155440c0395003005815a260800414440c0b03204200c1d022106070082c11450744e4000040d0007200407540340c50a42101d200b01c245890319090f801c000902120491146c00070301030214004030b0040d03151110034594a900d0810000d000c420364401d00700750240f50020501c5c41d0f0b00780c07011001c0c1d400e480040e50081003c2070303d5140001907001005000043d02040781803410440d00300140456441c070f450081d00c2d04114010580d0010801c1e00450407039031000948003541d480d00c84104009640c580c001c02800d480ca00c100012010343c407040e503845243c1100125226200c900c058 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 905894145 1250 905892895 905892901
    0x160e04080a03140c0c010b0a030c09020f0d021602010f05120403030b01020703060207060f0c180302041d0f0f0f0304080c040b180a1e0207080909090327100e0306 71
    0xc08015041003000004259a520a000e243c050b043d0020b070044661410325642d80b20159055801e6559610b2820700841c0e00d070104200081600429038200c48041000585405190810803c0c911801001020071070010a0307080c02c0c691440c40c40545680b00740c0707030ba146031641c0c603c0690780c0d80250707545044003214032000100420300907000000d070200c0c14410b486403181c80c0d5039108202d0f0040c80341079512640d11815411000b15030311940c0b40c42c02050400071201581101b001e0b01c03076040c500009015a455000d40708048000c420381014013149082594026018401c002d940c80340c511040d41c030548100141d1490003a404070803034099030b90780c401915181c181c131810b000c0941035980c007940e000002500541e0030b42412080b01b45c001c01800b080131490304001c0c43e8214841c21318106003445144100100d2000882071412950718042c26a110309090b0b5401d00b505040d4064500020041a5400381c030000c000b1a09400d5012a0000c03250f880c1c2c680e507009000c507003034800a01700c15010f5000d607000c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 905895395 1250 905894145 905894153
    0xc0601051c062406021506010201020c03041e05040501081b01050a0c03080c12040c17160905100b0301090608150f0403050c0307053c1e10050f09160e04 67
    0x16084070301d91000b0101000d50a9038904904002c1d41c084c0006070011b0f854000003140210740d05030842001d00c001c1d401c1680704203a0fa52a442584030300c484c00c2d088614241c0c030850408000d64000c1600038000c0190b50780d02e0603030729181d0b4500c6240f541030300e81c83c4410200c11360080e42034402071500c07940e4950000405a4040e10001d001504000d202e1030280f12280c0b04ca00305058080c4114440e41200301b1031483d107401094140144000c4000c40e40110f0044012130048201c804200c620740e0002156035143c03040f0a034000507580d080171070400c400100116460109402c07210403601c80c44c00b2651030300046002013403007a0b000e8907001100d80789080810301282c80b0b000500f4000c1c80c100d0540f4a41070f059600c991810244081001014440303107015a42419600b0040081400900204103141000c20324540c0b20443d00c00a261000c06440c40080d03541403c00c0030080280d521102042030341000e0680c00005038003141d40d00e4052084e13049150110380300e03840c0d817411160340d00300e0b1002070303203550703407 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 905896645 1250 905895395 905895401
    0x15051309110607050a05190201080903090d0308072c0a1d070309141b0a05011e3005010906080312060d06090f0b061f05030a0b0102070f0603020c0601051c06 69
    0x83c0c130180715485000c004180107002c07040c000c0401007003005080700e081c8005440050f0007081d10000b0340080c440a07030f5546400915400065040c94074003555580c2e24810389040c80c9004003030754489243c19240c8640c0b003d004d802011300b40c08603444441265a1160f110034400604915a403070384081000c0f07441c0500a0b04480ba0552090803040004103001c4651842c0c040800e150303104c1150364142d40701850403c203d91001408080c030701066040b010360044800d01400440309820481b00007111364026480000c00251035440c09120035540710500500e6024240c02e0280e0414646010000a44440000f044906000c4000e800c807000381e86038001c0200e20b494895058400c03d8642c094000010310110220340554440c210000580c10010b084c01074020203480c0110210000c01e40510441341c2090581e9800300c0e0404000c104491100c0040f4205a07050748401c004960001c000b090180d0560003034844d0b08842c808a48240c0e071b030b40d030801241d4803040002c40211a82c040c40c00c008070306560 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 905897895 1250 905896645 905896657
    0x90a03050f0c0111030a0b09070503240f040c1d0f030607051e030405061902040501020a0b090709110409180b0a09021f0f08161704060b04150513091106 67
    0x800004142c00840782c0c016255104030358480803165104038640b25807230003900c8070760801200e00e456811843c2c0841c420146d0314180d4645135540c040a0840c06859486e0700800e030300c1800140060000c0768415101500a0344080400c3c0318000d026424029981000b0340c4240603140000c1c01044642c0300c0810607181503015800c0350100700130b8515004080a190310046001d24422001170840c0e20781344010380400a80c2c0c134012710003103004000400c0145c3c2d00017841040340c1e170441100405c5884007130205190000036803100102d40d0070300c2401c0f418550100302600c00c4400c00001400614001400724100c00700580005000070842c20126204039001ea000c2c1a0311803025081000c5401b041c5000340b04410010f0403440021030b035a90305105107500c404195001204070107a2040000b0b82d80c00034000e0281083da00700002174420010f8203100c0160800b08032440080c000308041610b240f14a0703040f41050040b2030044018040581242e5490b11880a50b2504803004940300ca1008080240030792042c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 905899145 1250 905897895 905897917
    0xf060f0d09050d050a020105071805040c0e0306010602010902010f0906170916091505030c06030103020603100f3f061505060f030f060a0311010c0f080706050f090a03050f 75
    0x25801d14070000303204028922a10003030382c84040e203810040c04000e003514130040c01201008440c0886a40003c274264460307040e1031044034041220015030004842c03800f94140e200d039241c0b00d14400003404503010741c80803c286000717990340e50400805550945e01e0741c04e42e1081e080000c00d110760001d9020392120030701b90044071400a8070100c0d198801e000364242d580b5007105004698800d9003c400380100f004600081c20107402402080c0c00000c00100280014400039004900010020b5011209103508030301500007501180c803056218500b10055011075401200011544079245180c2c101160394100c132040d00b5014810400d211344d80e4034014040804a070750042e814003e0100f03c41e41c8110145c0480f88050300c0c05500d9160400c905020410003502c80e5008440510081c0040307141c0c1c0c00c00b207503000c034282020040120546444483c3c04104017000c3e0081c0c501280380c00400c202d41e00850700400c44122110071039203031003c210740c85566880005000c10400c004003110000d444028050702c2a42c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 905900395 1250 905899145 905899151
    0xc020f0a0804121104020a02070e0a0603020d080d1103010f03060b0f091f0b0c0c041103040510020c150117060108010c0e21060106020a03020d18170c03100e0c0f060f0d 74
    0x2444c01203030603604041102070140e0003010f0140711009a039036891381d02c80c0341c207003041c0042d03440c54010443c84e601910340507144600003d481411400540c1042c00314800350112103540390395503582440c1004050000703c0314241082030001c0c4524141407400c4604000030501c0809841e144002101200c0303007443c4000c10120701200050000c00403000d850b408031032034041c0c03c0c2400c00400700411103281160101c5030480074018030001c1480050341d00181300c1691001607880404d4200c0390701d010401c6100c020441c03600000801d0f4094000460400019000b00701c403802d988480d209802e884025a1090000306540a41c00044c503100f06e15098035401c0300054030a401c82110340c0b90034030f1003d802c1180941c1c000c49220b030415504010000022206180c80060000362040f80348515480c0d21584480380300c0c00010f0552154140a84400880010b045402840485080b400600480030001500703005001d00710003182070280c080080907100034807451800514840a00e0142c000c2d21403905550340e = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 905901645 1250 905900395 905900423
    0x1905010f0524040e0d0f0810030c0b07050a330b010516030c050d0c020a0e15130f05040311010e060603060a051b07080d0501060e01021209150d0c020f0a080412 70
    0x8001c0c0400d1741256425511864034200301e200107884804050100707a03003ca241d190400c0880c0b00080d8640544884a180d01d42e01c05440c18803500e4a0580b01d00038180c0300644c1d2500001034550300942e00b40d1a421072540c3d5009039440782040032541c007208581e01142040091840a211440050001910a04101c11482c007151180c41c41d080490000b8808603401c1070840d020740c60000c110b08010401c042801c440c07131900f0000c4000b01d11104001c140101418807803001c9048c1d141d003010020302c50070401082546400d0034000c0030030a540003024025441c205815032040004551180301d41405001441c1c2da072280c0c01141c006220060141c54550500d046c17031040b4001e400000c0c9506401901115107a200c851b4068007100c006a03c814203121604005250a03600412140c15003070082003040e45440c103e40100d10088450003070310403105000151403916a03d1580501d40c0c1e0641c40d401c44817440362504606503596100f80e005801d440c4144020010700a02500804100b40b00380c0400062403 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 905902895 1250 905901645 905901671
    0xe06060c010203010312110a1101360603060f03050c090c280f031e0908040504020a030207050c030307080403110a0e070c020f030c01051c060302031905010f052404 72
    0x82c20070382080315100c4010b40700306e40c0b0036405041000c03180b150102900340080c1a686007100c0c15201590f0b1414014020014100c000c00c003c5c51040754205104801c100d00c0140c210182040d116000c0c0c0d0020900d428400700b40500c03800c44600940c0e50010090220341e21040c20082c0140380203149519809017000b11841c4003000c02c910501050300014000d0404100c0240a0004d18000d40603108040c6007500d851102e041e4006014082c0c0e4900400140a22490411080c00d100e41c0d0021504140001b907040c4507075030300d54001d0212a004070f040c0c600c0c881d0014105503d0784a00c01010f80b29050a01041c40410f040c1e481c064400c0000030085080c80f07075112561710000c0000c0383c02502056940400806505011a0748112081e003103020301a2143c0440000c2d06034080e440c4400400032407030310682d2001500781e0110303001e10740040442d18544a1500503480703d089440003201c155081a0800c3c40d0114540942e50003003000d1040c081c0a9201004a5030030704060407540e5504c60f4035881d40744148 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 905904145 1250 905902895 905902897
    0x6140f130b0d0e0318010e010908010e0a02040f200c01090f080d1a0112020d09050715090806060a060518090103061d0f0c010e061306030c0f0c0203070e06060c0102 72
    0x104141e000440d214a0b90302c0c108021100407100e00c015641040002c10314038003094422543c03006090030900c0e01e4100707003c0122140703025500003050940c41c01008100b48400040c280f900c25100726014000018510584001e88921074030070000385912000c4c800e6295402c0c2c015002c00b002040c00042d40160607210360200003008078056544071000280103445800a000d6100380240c1014010525014240002e00890300308440a03090341c0c0c0131406080f00300854006405507a00201150585516048103c1456551480c1600071403806900011030140c08901288241d20080c40ca0541c0b42c070b0700c281a54070758481d01307100701e1320340744181d01c00c0e920358980f6a824084e50080e00000341c094820103035048801c0480840607004c2c0c2c411000040908800200210341903420318110195002103004100d2900480d01641100306004402140f075039415808510701c1000d6564002e01d60411b0101a03441503909500690950441c00c0140464070319080c0494001e88007902c2d1a00e8802d070810301600b2 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 905905395 1250 905904145 905904149
    0x334020d170f040f0e100e0a090f05030c060f01080a02240c0a02010f02070302060403061503140102090301150312030c11030406080402090705030618060d0f0f17030106140f13 77
    0x100c624049018008040000e01010142c08440e541d4105c0d4200301030544070300e0340325201c0c040309416084d0008142d00a20b03084036510580c400841030b41e241c11882c1c1180c0720f82020094414520800d8005043c0d03803440c4c80024102c0301c560b80500303080901d41c1c00b44551051507014003041c00b56003138000072a100107400242003041159016105040b00351000400154580d00140701315030002000707001595132502100d00310b0303a00860024155054110380c00d0030400c0750b440602686095480003030002d4064000b45018541203000300032110040b8403055554100740005850064001c200c1c1034400d0081e400001c034680c41d41040310f4160001c510403440c41d48503401110000b100401807104604040600c0380d0082400d04106065203040c4010420548004041c1c5c5803414060000c1030341380c2c44144802d245180c1110b060a035644060a04801e0249050000c0b0f4411340700010381384180c0241400d49068070459991404404c031105001c5120b60000c0240500c15081080582110414102c900300 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 905906645 1250 905905395 905905417
    0x905040c0515190e0a050d170a091403190209100b1c0b03060c0f0f120a02040e070e0a170c09010321030b060301050907050c0f0334020d17 61
    0xa520028200903540d941c90750007001083c0444244d410307925640d035013224400d45500b0313100c0450848940c00d00c01071b4994400743e150b00d500c10010b50f01080c0c42c0d20004d52010780d14034002e00b4240c5181801459511201c505076a0b1002c900442190014a800d403280c07a00000180c881075006512a49104400d40c000300b20000020440c4048148551907802544c40700708040f4040c10080ca40b01070500b00922514542c0d420b09180012110000903829050795940c0303039000c2c443c800d1442c1104401c00254094013820036001040300008603100e1007034108002c6008040c00c9501c40380d180c141c5224252666440b07138407840c05400f10301c2c4002d441d10b24081e07000b1401085503540d8111800e24a010840181107001c04160030550510340c01d0b290041180e044801c241c40a2001c1c1d40c07030050803203042c001c0a8180a007401460540001031800002510100f11400720003410f071a0501c41c000440c04819101c02e4000050740c140307802515120030400e60503030007405105030403491010881000c0d0700030043c010b = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 905907895 1250 905906645 905906647
    0xf06090f05121c150504020f0d020415030506030a20060717070311071a03150d0c0602060601030e0709090602090604030f1509080318190308061201090c0905040c0515 73
    0x2c00307034400d1001d8030483c3c42d0004804000c000f140c485540c160494034000c0c80c2c0a580c0005140c0d0300100c40e54100c90743c241c1c59540464455880341c1c000c002065481528000003030400d400301d01c33640f43c041541464554403a004030240c020059452400c01d8044007003940c050414041c1c0320106e0f1240c0a5608109074401460303503030302254078001d4401d130880036030744500364007021051040d491304d442040c2501c030030b0b00d031015140ea94003405441400440900550132061801800c03040048501006055511640950300316594080044040780e0f03041c039042d140343c1d2060000700041241d613400100e102c1d010b00805841c040740403005c500380e40e1059108481d28101340050000307110349106c0307581050700f040005100034441510f40d0100ca01014151588148064581c003a070b40c441001403150492255070342a041d102a801c0140110200315041805400b0300441c0c1000c50b4410720a8100140c0d00c035060f076030150f046c000b0100080400500c2202c1d0360710440c4d4040303000e5560568603100e0103d072100c62 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 905909145 1250 905907895 905907907
    0x30c210204030516061b0204090c06050c151314010609060308040608010b090d02190503060c0a0813020d0b0c04030c15031a10110106091506020d0203070f06090f0512 73
    0xd503103403010589078501e40120192060061075880f1498002d81c8501c41c1c500c0306d000186000050042070009401050401450800a05540c001d409071089560610594104103151100207002000c200d511944011411007000001085a05505910048035000040003034413441c03840200c4002c0c0d003058884100105040126691140c0c03801e0240070a0204e03035060030110000318112140842c0000c2c03191210b0800d440c1404c415000c444000e0000034100c40c464101091014519481409001c00142904d40091403081c1c03803100e101007155025003100c421340001e4581c0c038040f18016200b05000d40302004000041440c4000c500c01400f4110301d8444510a810f402504458a142641c20140e04400041481d983d40401d400301c9030b141824401989072403403240a004001c240c00611000340b410342c0005c0300c0000001028243e4a06408031913500d106e40d002aa035078002d402c001022854480d0341e44001907070765000a40c1040c032540c5904841205a5079903414000304901c180c1011801050b0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 905910395 1250 905909145 905909153
    0x6090302091003020f041e09140c010825020307061a0901090b0a031403090316032603010614040512210c1b191503110a02060403030c21020403 63
    0xc03075a041444030301406011031030743d8045050030b440d41060714070956650040c094807a02200c070005110101010800c00d00c00c1d03d1510b540078080160b020301d81d9208403107401d205940250043c0b8041c0c0000c0040524240c40750240c10481c50001c00d03580218003040c010300002403003c0c02000d010500c10380c14540003401881c18450041b805901c00030300707a820070b034044109403200725103207065a40029200c45103141403c5d403186503200d241201c540500c101600c0040d104c01113000e0205807403160001071400c50f050101c1d4858060150500c403003600302007004110301c60192148003050314101c5030302c0d07007015030b1f401c0060707c0d41e0601030000459401c80884100089060200410300071440d10149041c00710b00590350b682d400c0240c07480c400c4e041c210351803c640c0f41e644082800031800c000300707003c3e04280c556550444004101c0c0c3c40f40042070509040800034100e96041d1804a40c107a4002c0001d6625500d04402030000c1410f00801d1200740411440032030214610100c011546039000f40c0d03034516510b0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 905911645 1250 905910395 905910409
    0x30b060103060302010509010c110a120c08060705030a09020310020309060708070912060504020409140d0f0206061f110319120501062705030601090504150908091e040606090302 78
    0xa28101841c1240a00050b82c00c0000c0c0d8141c0324083c60b183c210342109150181c03102002c6542c0300c1c0c2c007103401c84000861201d0110b041d00054070440740c842400da40e5840c8642c2c0e03098255100000700c1d005100003809551558800d032045400242114000d81c150409001282d1055600d10640c0c1c102c10100320096422182654101c1c100345003520509280880c0e10041d0104160000d249544500c0443c041d941c882e04003034170302a0010039241c51510031048a90f40c030962200d81501141045c403000300b100c0d00101d181c0348a6800035040039000c80d0b1000851400148014800080c8a50034003800715405041010341400081c03040c1000190004da02c001d000c2d5105651510040c074100401848129800307543c0ca0500c6112010058160440c071a40c50410740c8540c03c083c0d09480f414000140042d010b07007065000e94000c0d0603421500c00003601200c01c0e13502c5007001614480302044200341034141150140d845094406030170300604c1c0705500060039148154001c4002425a45082c000d628000c0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 905912895 1250 905911645 905911651
    0x7060c050c0f0d080a0c02010204090e0319030603050a021216140a05062809150503012607151701080d020706050c0c1504030b180f01020c060a020310030f050601030b 73
    0x4014000b00070340b514001c0c010203001317105400031a180c2c04041d801354001d4040d50f019040425003400592a443c0040b548d940100ca5014540100c10740801580d9000cad01c03500080d03d4000f8007501094070a5028051a52010160b49907244210014090400c05818416001d4542118618207030880c41d401c01040c140e468005505c00c1108000360440c0c41c99401103101801f040f840c1541045c40484000d80d40c005403a030082a40622000009004a5000000750306944441c0f100d01c03e00030110601546c080b003210900f0005501180040c00803203486c090075020741d40b1a1070300302009100c0c1d03810314003a031000381c0c08a0100d9102c100c207840c42c240c0511501004c0c0010b450150700b008004800c03241e40d414590303a528000c500d90a801044c0c450581c086801031034000c1d05290207130601e112056a501004500d1220314026981148120324040c021038504080410003002c258948208200080d4130180011224a181140c00000540c0410242003028001d20203009158954200410460303402 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 905914145 1250 905912895 905912923
    0x3030206071b1707020312090406060903050a02090a0605040c020a06050c12011202040f0204081608030301120219090e030c1005010605030a0903091e0503010f1808070807060c050c 79
    0x104080c03100c00051281d55101d40c580000d00300c0707001c4283e20b031402c52500c50403030040c2d01805610030140c0c008400030010022400b0503501040b0b00d907520001101c1c020001d000042c000c2c0c01c14010400545082a006504005e50b400c000403150380e500005000c8802e88440400560440308607041403010b248034040c0c0c06000401c0d650b1401c5a001c05070311440070140140d0a0941c04207003502d05540303503584400040f140d42181150307507549804009a54010052501206162a840200d130101d404400e8a0480d11603401404000003683d003003020381100042c0028408030b0024001660103c1c030701400c950050311070055641c5882250420f410110465041400700f0704000c010807540c2d92000840e64403c0c0c00060000b4904664501140c1d1511191b1010440108040c0803286850040142008450b8110000c021041401282c54181c440d5940781e9032030301070820003000c00305141c030b801880524070a802d258a021295510081101d160f0b0014000017880130610181c004d1003042180040100 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 905915395 1250 905914145 905914157
    0x60807230402030f2202180f130b070e03010b04050a0b0a09051003020f040213151112032a030c030f06120d030218060f190813120e0d0605010303020607 67
    0x20404401070a00c001a05040c4020018045044079481c4203090b0552113034000c04000760000701c40407000c8844019217400318a00220760104003031243c4814270902c080d522505001056580d80c0303050390b2040c0c1c07030a04213803d0354a82c804841d8036a11881118401d1905150001301d100d40390050240204036174102d5500d5a1801c8c0c24003e0314190700b11494100c0b581101c1d0040003000c80070115010340100e007030720464405030031408242e00389002c052041042141c0d0340d00c4101101c0d69444c664406503ca040c4001400400c040b83e2484055100100300e082154a03c0c458402055121a8558003c031110204140c020090001400d40701030840d802c403404580391f1001240c103180039616a04181d900005060340054a561049504110300001d2030004040a40398541400062425440764100202c1d00310307003102e0300b81f05a00484c0114098003040346102140c1a141d0f60b00850740510010b2001032190109409001e6500c5040c61a1030901c40c0c8404500c65145250191030540058424010b20030 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 905916645 1250 905915395 905915401
    0x120406080c070506041b030b0a0516050a080c03100f09050403090509041e060b0307060305040501050117070e0c0d09031106010605090f0d020f0d05150115080c0a0306080723040203 79
    0x8000503005401c07a410010a001b48211040c400d503210207140c4c40140050307004410024440290391005200d440304a409181e542c081180071140c622900d50840c0110300041d000c50081c40070f4202071540280c1150300d421807075031942e103c049899502e41c0318030304042e142d204100c20140e1004000000700800d540c650781c241080d90740c50340c49409560810300110844561700c0d09200e040d07000380495410240554826035105c80c40200036010454041d0b882d90b080400010f100c0054146500002c810080580304072402e00301480700b1201d01621500a01f00107000e031441051441c0302c3d100000d0310a44038400c0901c440808141450016032001081c00130501c131590003a21103040244041000300c9a240b50b40d00345100141c1410b50010003641c1100300340700c084081100c0001c03070b40d1102160901e40a81c6aa03030390080074007a070803ca18034002a034640e021840d81485400034001d207000504010a80725207450740c951034180b59502100d1803402c80c0307904e1401c40382d40c0d040d0507040708001e40d401e518502e = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 905917895 1250 905916645 905916653
    0x3011b120b060d061a07110d1104060b0714060c1803120703050318030901021203130209280203040f11032401050f1e090711120406080c07 61
    0x1015115042090100c0000404400a000e9210303180703080c402000b058581404504040003403040340a0b010001900000501901e0642c0080e2013110394060605402044220b00f8005a650b21a20803034003070341d1208210302c0a6946001e0000500a68411a9110401c50030180b41000300032950481d00d0300a00c081c010348403021400c545101c0c03216003819501417202c1011034034003041c058500b80e101101040590030954070400030340c046c1564940d4061541d2001c9060f03502c2e0310940d500b0a000da804a0072240c0001410380185504c220843c180840c184070b0703500800d8074001c0c12501a901c0c000c401e031480d0a1640e403040c0401004558440843c114a000c1c0d4a16048181d00280038081910300001c40c4000e41c0c003005000c0c1d140c0062040f0303118000b01d8025920601400b030040c103204039038521040c00b480c2050614800c5850816082d60041040441401103604020384148104401303840c000190381d07000c04c2364001030784414079100e5a8629081c1e00074801f50021b010444140000c0003190045 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 905919145 1250 905917895 905917931
    0x30307020307110d2012010510260c011b0803190c1103070206030c0c0f010c0e060708031303020705060c070816030b07110a12050c010606030509151f03140c0301 71
    0x5d84121071059640100c880c0003c0c402c42c88901c0040f250360900c3c00f0491825100c1c0c0f848011140340c0704083c00d1009005007004010b5802e6203d0400d140d100343e000200540c03098504032510804402c50300001a03164031a4a03040e4011a1001204c2110085070948440140f0a61950011600e0b001c00c000c1000d10002d078482c4a424001380c415500840400c0500c4400001c40e092509107000304e803246071403100c149019142480050b03001c10031190440074641048400c0382c0382207900c144480c1c03469642141040341480b484a042d02107115420340030402e0344580008001c603c12600040400700d1500704028036116129030b008881900111081000a40040035a0b8010344203040072000324400b01809840c10001d4040506802451010038000f560448010007145000700d0003840440d407181c50a800740c84d8241c4583c03681c0d030b21003145540f041c1d0400194a8020fa001410624007451103560368410251745d030400c0c3c4040c480e00ca0510301040082199600000081d4000d1201008841e01c02c190703 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 905920395 1250 905919145 905919173
    0x402010e0a062c0d03020d08090718091b090617150601121401150807020106050f1201090b040606080601060c1e1e030203030a0e01020909060105070212030307020307110d 75
    0x20301c01c0703d4010710607070503d03064581905001c064a00c1d00098814140250b640e000412090040703001040414032408001c907030304096400124040702e070040030306000401000400f0081c1d661400c0100e0801c040403c60b41c510380240301c801e2000c5000d9041508043c49030761080174041440e0311a095020310030116008140d446802420708c0d00c2c00300c02c4401c0d80381c040c04a50320704080040c500d00010030040b0200100c044100c1c83c0780c1e2600303040d07520880141c0c03c03a20340303005440e0701603407240a480700c900c1e1107150b58204004100c000310760107031903580d246102901a03504442d200d44030070040c4914001000481e00600b11403428501216903900c50708040112502d4502c0051404c650040600951014103a14005240c041091002c100d0400035101c1d0815241596a541840035444509505000303032a424a00144054526101e06c801074407664400034080382c101d902c01540c502040781c20300145100300110740203107a9810b4a4500600c000c00c03005030311403003410305c10f230b00c40041001c005600f10 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 905921645 1250 905920395 905920427
    0x20c1507031a100e03030d05070c120806030a060c050c061801230a0f06080d090311012f070f0e090723040c1e09140901031214070f08030402010e0a06 66
    0x51005031310703001c0f909500c01c002503866418140018019a542d03c042a102c2d4180180c1c0300c4100c0c400045800c40b90702c0c0e0152070007645507000c0019840030070f803103034401d0001d5006820900d2030500c0d0681030341c0c20120202c500505070020794800c464014030078059000c1c00d001350f0b00c40c1c1e528aa0544031203580000c024040c141d0070381e80e4100f40c070a45842a408a40a0400e0808441c4c8840c408803009246094500088950200905041000354040c141401e00d10000b0515518100030540c1c6228021b1003c1e030b807980052080795000290004940701d15000307800040d55112051600000d40f03850501079520050a2074074010400d0000107a0b05500c12a0711360484001c103a50402150131500800c8400700c0d0340742e03100414440450550440203210441e0520344c00e0a810055075000c0100782a8244400740c0448400600d005025110b50180b01d524924a0203180c1000240e4880f418203e10380041100c8040000091006542e0000b1189940c2041180d0b0241c0460500800402800d00820400 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 905922895 1250 905921645 905921657
    0x6020304180b060324011103070204151d01171c11010902041a030c15030402011b06050406020306040b100e0d03091706011503050114010e04020c1507031a10 69
    0x103050100150401050300c4401800d2070340b40d04000f4081d00d1400012800e88113445d035800c05a0403a94020b40c642500308402402442c1844000c0c0c0030f020140c00d4008030fa0401c0980c211001c110f1900201e0011420383d0f901d00f5541c03880d070508440552041a818014269903ca004810455801d4038000c4c2108043e03407809000c00c0d104444000d01418080d04003e6125003001c840c600d0882d0015008081c90303008400f100d010381c4446061001d10503000400031104801000020059401204902d0100031940c40b0b2170801c40540d101c20341292801e4400f120030940000c2803009a02e414000d440300c00350215942c80e01d80c0d0340f104014100030b0071a2452401940c40a130070606042c000e082c481e00500400b01f801e0680c54059141c2500c5800c03d000321260300b204442564501c910a104460513200180c2a01140b0b1003003000541d440104220007684c4507800304440030f603100c0b09000c4091540c41f140a03a04407820304480240c15036248083e06695031480e0a00400c490b40c030031404018402241c1001 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 905924145 1250 905922895 905922929
    0x607140309030a05030c0d1704170c01050403051b0303091b060409090614100b1218010c020a0506010510080c0c010213030506060f0a0501120e03160309090608010606020304 76
    0x45045010308441c09600d4000c100d000c00901001100600240d80800140c0300c56141d4040d05407164440b40d010b0301f400c0e80c031000000d40064099101c01406800c3c00b9003807803c2c4034a0365031140c252101120708900250002c1418594998024008011444e00402850851078105d54982d542c1700e0b50071194140c100340750212422612244201d9000e0030303102106110451181c100040501018a011420840d40a00086429404210720829580c00c50403480c0782c160309912014007a10041d0032316000000b07803039401010340024880e82c50164000c0d00070303155005050a00c2c504180050780907030702415441e075080c0042135002011b658401003c030141078607120040001d50090145500e80e0100040340140030051104c0090344611a1208683d0740c210301200006028041c0c1080c41500d01042d40030180c510307070302e40035003014000c0071040085a0600d011000e4844403018110b5081d00400d480360401d125204050180101508142001b0b0240600d0f00500030342d01c3c459840b855290780081454 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 905925395 1250 905924145 905924183
    0x14060d0f020d240203090c03030306030d03050a060e041506050f3303090609010608030708030c0d09061d1203040c062d0915080426090306010e071b020607 68
    0x41407035204650540c1e0304021030b00b03e40d428000d520a0340c0c07040883c410140511650302d00003049078401c01c1c002c2d01500c001c502020f015409424081c1017114150340701c3c80c0201e541404000c2d01c81c0305070302480c3d03900c2e8400392800e80380c0110303401030700194080c0e0341c80c01c091000c80e00d40d0b00d281d000300c00098250304941385c6151154105442c4a400f114250342000041c411305030000101117009420350b00081003916a21125540e5a200f51030380204915018000205540e51400280c005c184a00303030040340710140c2d42d94035021140145a001003102d46445600b01500c0104040f900b10b60640f03414502d541015120300b5451642449032008002028000e040c0c052001c0da80862501c410300c904e400b107000c0c203000240c0317010128000d02c200c050346403141c16045441521000d008642205031000101c0c0c44200c00003695801080c0c51641e0601001000d483d034074100100ca0007001d900701d82506500b0031003801003040b984c6150145080031820a507101596403641200d00155210000701d50407402802 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 905926645 1250 905925395 905925413
    0x507050306120a1703010512060f070e130f02130e06090a05060d060c1d03010203100b0d091b26030f09120a1220030d0b0303130914060d0f020d 63
    0x1400804c8051001c0c0c880c403095145002650507550100c800d540b030810608c1c555075440c1c2040b10502c05440050300441e0b1000d020748045007200501802c80000015142c076003105485003c64010109580043d08003000c0e05d83d44245c00242c40c9032000c80740300c1e003040000120241d00150000c40103541d18000705415039201c0041e481d000d41d001c00d06210b40146200098403100f003509111302c0503c0245001c1c0390924043c4210b034801d154500c0315030203180c00d00185009a8021500c0b104010fa524a0140045000701c00303030048102070000c60300c181c0390400c0702c2d52170205001c0c015410300d840554076400301c00d600881916100000400100d0300d988070300c400926002e55901c000446030140403121410320107041d905180400140d1288800d01044003040d038505401c46001440a0b0400d0103030800a00685d040004480c5d4028120384c00c1607402c0c01c1204a40d070255100c401d0144d40c03004191969070103088002c3d400001190350b01c030b441a95440c3c0d51644d100911009100c2e500745003c2c1010001491 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 905927895 1250 905926645 905926663
    0x912130e130b040807051005040206182701090c020f0312100e04050309010f0216210606060513051005030612010603061a01090905072309040519050703050705030612 73
    0x61601c42d0b8906041c204444030b5802810140c0703007401500741d00007504500d405010300850b400f030103661800703003120214810079602c41080b0741d00c81d00c0c100c18401c034559902c4800d52552601d0208022a524102c010f1044441112048056401000d08620002404020340364502c10020003d070165840111900e013221558000910b5000d06400384004d00c0800000340208242c2a00d480c2e03a0000554800e0b41d640368101442007503440358030700c2802640111210500480a101c500103480d1640b40e80e103c0c140d41d606c0c0c2102c1c002035404034104420400d09188080101810f480912004000c000000c1091100034456801941c41c500030700d00c424030940c0043c00441e04034000301303d42420316602a4200c0c040c4610035001407154100810402000d1280c0c40c00780342981c580150802004001c40001000544028500c4009005980464441c0d00501e031203040c14840a1620907040050b500484101400c084101031402040003945a00041102d800000440355600440380c1010f0301c03881d0110103 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 905929145 1250 905927895 905927903
    0x140706031d071e1d0a0507090503070501030906021917010b0c060609250509150316030c0c0f0f0b07020f0d03200d05010515072001030b10080912130e13 67
    0xc4013080c80500d00d4000841c05228601010b1010f91541d07035040b107c0e03c0070b0380151581608200300401c0b0541c005e601002080d4401c4101600308241500e0004803481403c8109001c52402210b030440002e0280d0480c0c0507000c038484140c2800c60645030146d4030100200803501030703150f040100340400c00c481240000100400000c071224102550000e1890708002d85150040240c0c1c034030034408a90302070690380f06000c085101c6555420500c1e00300e0142500303000d13010900a05840c43c0303002c10070241c4840006800380c5200f5580d4182460403a032803000050400d011034100c4a00352015450204100309141c1c414500840c079480700c0c90743c2c1c1540006440410b0800780c80020f1103907481c03265420060480b1000c8030340e9803c1119000040056219607540101080396070b2240c0340e00182c403180c0701c04030303110306140001301800c001000c64110107248080c800815404410040c100300304000300050070400c4103400341000d01c1a0469184418940030750324821b01024002860b040b41d00d6104002c0e1504 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 905930395 1250 905929145 905929169
    0x50c090306070e041d03071e080406030c0f090e2707080a02041a01020a0b0c040b07110f0102010c090e041403070c08011514040216140706031d071e 65
    0x10090182c070607030f40f0408441c051402d00044204040c0c90388043c8122400c10806540703002172580c0c0300d0302030062442e1945042c01c0003102003c0400c1d0f824000e0005003050b41c0300040d0740142c2c0328020b00a00464500c0f9070401030500001e101c112802c104540d000700071025220b4081000c070300000a0b0010121503d0b020384206100024481c02c00030f40340003404c0c000d85041060102c042ca00c10725104000c04068056444100e507140040c107503c80c507681c0b103600c032001613082c1529448061025801002c003946c80d80000c0451140c240340c8080c00456402c03090000b0440c15401250107408410349100d540103411600c4005014031000302c400741c001d8030084040e81c0c2c3e107480c14500601072100034010200c0355031804120b525180b06a071070b080c1c140c030a1000b00c0314400c40c4a0301088081c0d0700c0216040c41d65107400d10800000b40d06000316200410059002d0441f441c102240202100c0309a115041d05010078015491034240100c1c0000a580c04d003141403011031081c20009581040039484001c401c1c1c0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 905931645 1250 905930395 905930401
    0xa030f03111b150705120318010f020a03051018022503050316020d090b2104110f0306040206120405190b0403080106020d0e09130f0f0209061c06050c090306 69
    0x2803005500c0482c0c0201d88a100300010012905800c1c00f414500030f00b190f0001c852240c114032031101455104502c0d001c841c495540444200342928240115110444e070003080807940250540541d41e13200d40743c405124013180c9802c0244000340c6214004104981d0f000860842c0400c150713070043da0943e1000c07407031050104c0510b0001c020fa44100c43c409102a005031500540c82d1002c00d5201d003004c0195180b20400d4184903260704075034003010000640e288900c260907450020510124400da018100c56048110800c051002d140c8206c01158072a4015004100c0140d0b00d40781980c0c4003c0c0c0702d204a100e55622440c1c4186821600c000c100c00c004c0462003810100040301f01c4140c0700da44030f45d89101c02660383d501b041c0d0b0350302a00c0c034106020400b40882480d61781403105490f540207070300094a5510340c19549550007020782c0140140c030b03100e000071551425810500a007940121058408007541c800024039031840824441009200c00c0c0c0340c101090701d1200c841c0c1584c400c00c10050560b41607003 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 905932895 1250 905931645 905931673
    0xf030c030402150c060412030e1c020d0302040302030a060f11030a02090a14061603140d0b04060f0e0135010b030c01050f0f030a020f19020105150a030f0311 69
    0x240044404921820903c010b01c0310550891090314418400c41d00204803644950f91814003400200220000b019692444424034410030008264000f4180c503110520000070701c00207081104600408041c14010001040141c50000d05001803940088000480031186060b41e405400003003400b40e01d0030341c04400e00a1031682a801400c00d0f031401c50b405900c0c140c0d00d41414081c0b4094143c3d059100805100c17080c0c0c146440c00a400e4607505ca40342c02440c0404088440d29117030094501401200e68980000c210b50406220358805010440492139010b0b01d0060745503210b401c140074000b0300e0602042c0e469210342020011900c1102c01814007074501614041180c0200301115034148a40724281481c0c645500403801c8034040c0b00c0d4880e4a600e040c4025a90b000c95500141c0003085040e402c201516106034100003601c004121a0320041e404210984020300b9100301030304a002c440c144c17540540441e541c100305c01d012070743e0102d048a8600c3d09130a05172a20798007078401b900540a8840803200301 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 905934145 1250 905932895 905932897
    0x2503240b03010e060406030c0e070c05060702030c01050a1a2e270b1b0718051b0a0210090f06060305012009090a200c0d1b020f01140f030c 61
    0x6030303031070482c03d0080765610401c1105032282c0380b00c00751400c07203040c00610580d010161959440030340c41c101564000f40d140c0d100d515042040f6016070058101281584941c1400c1c0502034012b0707010038090015a075a110a8403110034044411407003100410040c40822110071031740f181003880a00454069000e202020301850030b084409071081010030b1918147c501c4a00c0102c00755040c45c12081d0608045041c0791001804101c000d856900c1000ea0000300c03c50020b0403014800760079030020030700d0f0403c1003000034920350f0f031521a81200001e01101c9031b482d60020351542c4103005241c003c6441c40d41e0381080e100c00b08030140050000c504180300401072120540004000340005250308004800c4d10000300858015003c105511070101e01c0072402c040d2681e08680031003031000d5105507010303c0000e06806140c3c460304803204150880300d01d0075095a04601010302e01501d14801000000071030303000802c050060220309050040e61a491b071118030090045e2400303503042c40842035a9052401d0074541c3c0d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 905935251 1106 905934145 905934149
    0x60303040506040801090b06030d0e011d03030304030c03121109041a18060f010929160b01050312090310020c1203010e0603062503240b0301 62
    0x1040e0b440724003c0004049030b40000448183d80e01d00180b0001c0018040f038400e4000030812108036400c0407104058040c03d01e00034a5194a4551002407040d1018a0503010b00c4088104400c01d5048a000115903000e0341f00c5004005520351510309032224469150203100d010701052225040941180709200116401100d64040703000107e82d5001620384604018401c8005000c002e05101c002000503c0c02860072182c01414848641444600381100383c54040d500e41070340030340c0416403042d2183c81503824400100c5030020f05111107541c00c03e001c1e481c401d00840e480c01a84044210840c3c418820141c040c001e11404006108000d40113016001014014592881007460790400114080c0034814800d440c01d0034110241480c140008002c02d00c958007042d0b6a86410104403c0d483c040c20345442c0204850b00811410b5500d810b40c16030040c008001031001013103500b45c401c080d41c1 = true := by decide +kernel

theorem cover : BRFrame.Cov 905755395 905935251 := by
  have h0 := BRFrame.cov_init 905755395
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905755395 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905755395 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905755395 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905755395 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905755395 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905755395 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905755395 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905755395 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905755395 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905755395 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905755395 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905755395 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905755395 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905755395 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905755395 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905755395 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905755395 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905755395 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905755395 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905755395 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905755395 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905755395 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905755395 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905755395 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905755395 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905755395 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905755395 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905755395 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905755395 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905755395 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905755395 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905755395 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905755395 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905755395 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905755395 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905755395 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905755395 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905755395 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905755395 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905755395 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905755395 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905755395 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905755395 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905755395 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905755395 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905755395 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905755395 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905755395 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905755395 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905755395 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905755395 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905755395 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905755395 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905755395 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905755395 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905755395 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905755395 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905755395 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905755395 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905755395 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905755395 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905755395 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905755395 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905755395 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905755395 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905755395 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905755395 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905755395 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905755395 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905755395 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905755395 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905755395 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905755395 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905755395 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905755395 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905755395 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905755395 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905755395 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905755395 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905755395 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905755395 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905755395 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905755395 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905755395 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905755395 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905755395 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905755395 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905755395 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905755395 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905755395 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905755395 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905755395 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905755395 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905755395 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905755395 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905755395 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905755395 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905755395 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905755395 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905755395 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905755395 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905755395 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905755395 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905755395 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905755395 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905755395 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905755395 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905755395 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905755395 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905755395 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905755395 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905755395 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905755395 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905755395 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905755395 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905755395 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905755395 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905755395 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905755395 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905755395 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905755395 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905755395 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905755395 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905755395 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905755395 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905755395 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905755395 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905755395 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905755395 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905755395 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905755395 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905755395 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905755395 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905755395 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905755395 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905755395 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905755395 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905755395 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905755395 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905755395 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905755395 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905755395 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905755395 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905755395 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 905755395 ≤ n) (h2 : n < 905935251) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
