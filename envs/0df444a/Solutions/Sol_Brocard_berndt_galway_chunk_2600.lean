-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2600
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:11:25.796497+00:00
-- url     : https://prove2.me/submissions/3347e083-4f42-4754-8cc4-e9d596081280

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 467446043 ≤ n < 467625899 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 467447293 1250 467446043 467446051
    0x60303160302120a110c3c091612050c030a05041109010e1008010b0915030703170712020a03121a0a0305030a02062508131a010e220b 59
    0x129051403c800401c510960b010041d01400502519080c08550300c05000200183c0400c17030b002d42c0c4886c040030700c000d2455242d9451006101e140d002c03000740100701c222040c03208100180140e02d14a001034861060902c014000c1000411503d00c46441d84a60320441d40101004802c0b141981c0e01c8002000041c03001900c1a01c1070307200d1070300010a03980c03941d1480d800380800c4c200307074800c0c0e003801101240c00a456400042580e410200c0c007003240d0311122001c40e03200030010f15012816000c0d0b00031034188145a0006016aa0000c000c4419020030300c0c02855079510800030002c1d0107803080001c03622278501102c014000703120040385c01e0044180e90807084401c10003081a0100f40310980c0050a50300041e481120590404149000c0c07031038040c00810380c0072401c0410034182c5c8200c04c000f90b13420740c0700c100320b4018016001c2c0031401c4041726411a04150b94409000b10b80b200c1040000b0414400900c140040a0512800543c118804c042c01ca44103a0401c1c044041828817030b92380100c030610042c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 467448543 1250 467447293 467447297
    0xb01050a0509014b020c01020a02191706040203100b0f090406060b070b060a05090603060a0f060e040305120601020106050139080d0e030a0f03150312090602150603031603 75
    0xc2c0c048103680000700400b0401855141a000216103041665040300001c559840554101d206c0152840e600826481c0c2c401d0b5045501e01e8180b032108100301d5210300e068000004c1c0b41041c6d50000b40800001a040740a54000c038226034889280788901815595025126a00804e000c1030354281c90030002d0720107400034030030040441c000342c55034030700da02c240c201910a03141d1101c0c1d2400d1200781d08109410741c0103845c0130341d103c1182d8903054010075510b580c0a06010080c0d03546001c040070350b19055210801a010001c105140d600306030500030b16603040000350426810f13407100454100c0d80144143c01c216601a150341c4071800d07522800969503102e0b4600380864640c045a0800d40500366a440104948101e15540c0c898141d203408a007210101e270100f5000c2e5104100c074001d016004400b401c02e04801e0324002c514040400544048068103030f0009140303d0440b9200d4007002e410050720000d036010b540c04c0f10101c02e000340c005550340c80d00b5900690190003c01075a6007400b00070f404000420300034 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 467449793 1250 467448543 467448587
    0x7180507110d05040e0a0902061213050d0806131a040e030d060902071a0606090409050a0b040303020d0c020a1a100308030f0f0108012c10060801050a0b01050a050901 73
    0x2060142e040ca0b0155804100051002400b4014412880c0843d60040000b0508100030081d9a012400c0c601c10306008400414240380021000d400c030034409905e030782d844001c0d11860444103202504075041500d49912032483c0d0451041015881c1c0300d4421509100b00c0c03000c100420b50001c0c00001c04000029281901040140d006141c400b8004c00004100452006075540301500302900c50140400c2602c202e0b20416003441160f9542005895400c0300031500002c0d800c0f4645890b52030040c00100c01002403001c1000c0006042e0503502174810ac018540c000d00502ca992142240c40e05160034005003201440304100d000d170301d01c03080c003242c0c000c90107419900c449407681c89901c036980003124010302c060165010000c0d41d061081401d40140162002405044104c03c03101c0e54115604103008915200402c2c480361f400030411801100b0f03944108208012511421b560f8082c0400302e030180d102c1801c04401286d00c0d445030f0b00700c0c0c0c001c4800e40e651509041407100116034201084009400c10406 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 467451043 1250 467449793 467449817
    0x509060f030f090d1805011b0f0b04030809120417070b0313060c03020f120924040515040206040b0a0c390b0702060906160c030c050307180507 63
    0x140003140036440e03460038800c10f07181141e80c00c3c0c0303490880340e24101040207800e04c04100b000411480c0c0140e071800d09042440c00301c4540e0a0300351586400016040c04412030010052109201d28640501d000b0b0b5100c480315915460710556642500c2c0c02c1e07122094080000300081500410406c40541800c0c01341e0710260742d03500080009030000e9030102031346c1c0440618801041a00d11031841041040c1c1029418142c6200c083c40e854094103410310a040d09100010709141c6007404180042c051507011001c0d00c00c00344a1010b161841182c007140c035481100d40036900c1c0100e040c5410b10071940240001d10b000d04011400500b40c10004000043c0103c12800c0303000a035002005000094030303504000c0c0c4490390102400c1841c2080c0b00400040d80700c50006111956401e8200c2d5403180d01030320440d0f519070400002c11943c0c0b1405240100900801e10001e0030098160300010807a80603061000341e5076101c804042d1541c8503031095060818803041c8203c8120740b243c01680d03004215081c2036881503d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 467452293 1250 467451043 467451067
    0x60207050a05060a0c08010f030204090203010f1505041a030a1203090c0b12060901031104240306020a0f0206060906010c0f05010903050301081603050d032007080a030506031c050906 80
    0x1105500c02c9680760042c80c200714080074280304690441034649810813803940340c00064016882c0e0b90001030b0003241c603500c1c0300d41551400d400141d00000154800c1189010520b65110103803914010940310b28100740c1007004041198050303034041c09004000e0701119006666a00f140c0c04107030001028580c0f5900310750003003444610004024011021026a503c426080007031a000b03008220a00c16805d0600500104d0113003844110000026280081c40c0710004496400c500080c805802d100b4200d0080801000410307000362407820103e40b5000c00c04200c00d201682c07213410403218141c000c02c544001a1403988079509200b0a140134200781e242107040da441d4282900ea1100080d40070950000c010000da4004104503200c44140c0c41e8604841404c2d03a03078554440b641c1901d034508140d201d4240324413400100800a0000c1c418440030b566540462804600c1c54201c2464000032900d048c0000c2d15904000c10794104900c83c503e075240380c03580489810b50f02c40e0010000550401c20038011030484903 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 467453543 1250 467452293 467452303
    0x20f012609010504060501050108100501031a0303040909024204180606180b12070e0a0f05240702011119030801050f19090209190902072006070b0406020705 69
    0x9081c00303002141c203203000d0400c0416104103038800c604120346c0a00b000071198000f44403c040e100f0928021400d02204000140614075030f0220a07450b020004000a040000e6849a41001d1003030b1203440401074000c0b81c071f107508030707020b90402c003200034001c084819001102c1d840b21321a000d803070071a800d03e502d404240003100840ca1614400b0740d9107402c284141d40c0c1103a00c251841c1d440d8075000d1251030821001000c10300429010300c17444082400400c0e54030f07002c1c20041200c500090841010146d40c0c11369225070341220b02c030701c0f8024010131301c420030b88180d110340c0050070990b11088240707050140e80c0111413014201054004501980c9400c01417100e52080340d40d540d078003a50382d1003d9941064200005034040009143c070400300002118030b0f800800a0300301c03c9900b0b40000580320002e50700031401d4176200010f0182d01c0182040701080d000c1c55030380030304500c500810140380c1c09218000d45031820784184007080e5200500744461000500c0c50207031154054843c8601604020a40ea0b402e4600 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 467454793 1250 467453543 467453551
    0x807140d0f02090406090218060c07030b090325210c02120307051014010e041106040609180608060c1e040f2c01050f040905061f080a020f0126 63
    0x55500018401450b04e8103010341e0014010f5510118035042180b44d6a4242c02e80355818140994004035040c4500700c0240180d800075a001035009415242000d89a03849510284010020604205000148000c1188212400da5100508000b503030a45502e9000782000641d80c0800c0144e506000390041c0c480c030049620740e00780b8034000c40c1c94145914215081040f01c0a103000118074104030751007070304001c0681c1030454810002110b610740721810181007070f0424021042d04100000303000180f0580c448604000c075454002c12001d83d14500c01c03001e00380d540c40d1044410561003000450a20b292400003000550300030000001513542c00ca04098040e0000d0707200803011078510f10200000d0541010801c803100c1c03030100c90f039000c0e203640c080000150010b00032107019224038000c0c0481520ba076802140382075001003c03901f81d80303444400b690080d4246403030400710340300c9150f000640150001c0e81070821940181041c0754107400c480119080030140c1040342c1c810b508810560f04402901c0462401 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 467456043 1250 467454793 467454821
    0x20103020d0f09060b0f180103170408030703090302040c08071e0c2009010b1201030f060902030604060b01020d030915020a091a03220305190306051e09090d0807140d 73
    0x412505c20400c072a003001008058090903046543d03c115003081300710b05040d40d40c801180b0b107402c5150880c100f498061508000300a1000203010014140c003c2103106c1100d208807814000b00040c00b4084a8a4000742c440c840422420404192548031115550004403020303d0071007400c14068903020a84140c40c4040d01198000150901d07180c10164421405003d09041d05031404d43c5101c44140001070521001e843c00e4041c065540c02c100701600f1402c02c00ea00103040303074407070704250900c4002800c2d000d203014090303c41d0b40c1515a40c0c5000303008461106402801400e80ba110441d00320010f580020b1101c0104145001d0114100045521805150019894203912450710010300c600e510103507001c2c1d0042e52103840520340042e5000040350801c15006811034892541e00c0425800351046030852903001460b401c00044451889801038560041220342c4901911040004e9844240c4102001c0c001200000007607039490051a0001882c2e04e001c03419840d05200b204a0022544000c0d00000 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 467457293 1250 467456043 467456051
    0x506070e24120a0b0d030c061e020d0c2f0a0803010305070e010503070b0a0e191706061f08040309030b010e0106020d0905060414030312070203030619060903020103020d0f0906 77
    0x2403520749034207002d500001d0f680e020041000c0342000580401d404000060801c18041020003c0141c0360700b05482c03c000c060701e0840361807080d901c4034000e50050444112420b150032007001010b40308201900100c411045200480000085508905810a00c0b41403e03031044410070400203240c00002c0d402140507901402e001402d16641c400030b0241070303100c58400da1003041c0a00c9003507905002c0380c6103001207040c0011503004810206542110035400c0031548001044005108600030b940f1111000b5144143c440d20340c1c4580030400300c00d50b19002d95003040d01c540348111030b041c0500460b9800c00c1c001e040141400c0c0e0f0721703554200e40d91001d8008800f0009680c0c010403056404212140c261000c0c0d081074461281804040380090141e4440c0208501310340c404000940c0b014412160b04031584020300b11385142c8450065900e51054601600400411080f10300035070000b1880c4042e40c0030b03552a0755131589903800440c081c0d0068880004015034800851140c2001d0b441900240c2e03125500200e = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 467458543 1250 467457293 467457307
    0x3060d06180f1b05030d080a0b0d11150f070f14010608070f080105040551010e010308040306050c1b0a0c091815180b040b0604090506070e24 62
    0x40d5241007002d45020340f2004164003444981d4001c500740d100309001d0b1500d070006644259521000c1c1030482e5086030016890b018070401d1000d141000c6401510030b0310060343c03494402030792480c1d0b4410a6110003072150280404000111591036440b18a40980c6500c5012f110b4102da00342152550343c044040d43e44929410000d074841038007698018641c250007000b151415865207503c41d001d00c070381e20f2000d140501c0030390f05000303407054160650031030200e800d1418058102e614000ba130030440181e000b510400700008210342c441002c64162607205050700d040501c0c56881030003070903000d4404a6107000c1401291a00e80a044000a000745801d000b4000101d032400c1c56980041241c01c0421603a0400d240ca1103452401e10345403040300c1d80100c480e1031100324204044000d0841c0d4000007009e080b0341074a50240312104042501841c00b407400c0c403019468107801c1008840c003040d00203060f500044000ba1420780150304120180901800d0210603606400f61900244149421090142c0c4081440 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 467459793 1250 467458543 467458553
    0x30b01080606040b0f0906150d020a030203090f0705030d1d090f060907030203061c050708011e0e06061e040b0301020d020c19020102030f0307032702040e1203060d06180f 75
    0x1010000034141c818001050000b4049041503100801c11802383c407114580e0484120000f04868071110200811512280305c0c0e4402030103903100303441d120414030510300501d5140343c0208428045074801030080104c280080010b85030b0410040200d07d00650301e41d080d11803911100740840c03103040c0c20107081c0c290b440d2103820081080c4c00900303460200351045c070800056403162403103a80303000840040018114032507c3c5c894500302058014030741950801003040114410140075a208000c190700c03e02c0701c10140e030100c964403281100e101e540303e41102c10400602c115850150b03418040504081554000400800d0a80c0c0c0a1114154815400a10032142c6c4809010051110f10583d00c2c6004003030041d00002e56a018020780c0d4000d400b400400b086001e1b0003680010010b10040340380c030f1244809508001c41c60070b04510164080e0342010500c2c00041d401007503000d5042c0e001e0910710309645809040c8245101c10342c2086030340d29511001c4080007071100f041955030500c91a102d28040c2054641 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 467461043 1250 467459793 467459801
    0xa0e01050117100501200304030303050402030708010c0509010e0102031b0606011b0b0a0b010c140a14150a020a0903020402391009031e02061b04030f1407030b0108060604 75
    0xb20350758074101c005221034815110f00c56001c6030000d1a148146160b84142054203000d442104145480006000420150103400c002c0c4268000c50079929940d81d25a001350986180086030340000c0c104101107a410342c01004040c0d503040041c41101e050140da80e040685e410310401808001c1d43c0014200422503038030140c0d0081444620742008a20035207a902d0b0032000c0c0f00a40f288071010f841e41c0240007a039203e40c1040c00f1194122000102d40ca2007100fa25840f00550b144c251030065800e10a504030210000790510f8622408011480c00d0350381c200d020f0002e41185040c0b83c1000b001420000c00740e515400600114078011580300c20001d43c0809028130424000c0c0c0041056a422404410100000c07800c00a003445050002c190810186800c549405441c12145200301050304c807400c8042d400651a03200740c1d003180d512215528850b49400081c00f9a21000303043c407003413218040c0054410708000e810701003200c0407200026240c0d6100d44000100b6040500594840c000300412407070b090003 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 467462293 1250 467461043 467461067
    0x21010f1b050913021e030c0304021503010e150a0803040f14030109030c0f0503070611030f070e0a090905010209100f030c1803060e0709150e16051e07020a0e010501 72
    0x10300c02c1c90507107407201103a01c40b40140000604a079022030340c4001640003440e00012505000c12103545d83c900241003d2041d08241c80c20f07800748180034a420801400401241c2c1a5030b0072a034074002950b940400b01c81c484000c148101c2e00601103c1001900301c904102030000b5040e0901405100c2d818a00c1600c031048402034544c0c420303818031000001180d0000c014a92482d04400342000c41c4030981015481c3d032007038400c0200036a1a00c1413501400380700a0203540030b03d12176003c0c2000341d290b00e18210b41c05054503040c10382c07002851204020b001a294801d45043d48110005400d0900107030020724200004864040410101800941031540c5072154070070342e10490411081a14601240c6021071403d40001001d00d5079038554040d40d20340400c408401001040020300080d1030a9040e2078400b00c2510550b203811803114049022414a1009402841c40c25610301e0b040c00200c40307141b10030051a103d0640105000c011075400744c3c581503000805020940d1200007154540030004000101c080 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 467463543 1250 467462293 467462297
    0x14030c06031b0c1c030501090e120a0315080a080705160608040609080c01052a0306090708070c0c0b0a0807021603020108150402160302010c170621010f1b 68
    0xc10044000c01c4a07648030002d5140c05001d40d1a000c001503031501d40700300305862511895a6003c036400595050308072a06a61040c802170003000c04120350300342e8507951960405a0030f0000e02800300814400d90100d00341403504014125101d0380e49881c00c0c00c020707070300c6002d82d04806c5c002248414000c0803c0f0940e0b40440a62035081000d1418034001d00e0360001820080c025515422520140301c415020b9400484810b0020016814000719210031160300484510080307070035124101d51000306c10141d0348144400341019005580b40e000c2202c85482c000d0884041c01801c030000d00c046031074803e0f84405444102d072050b5231480c0d0550054220302c4000c001d201194003074441044c042044090a41c100c950a003800a900c0d125000940645040321f47d40b19001071010440d0784840b50400245009907000e50006c020b00c41c42507000716038244980d141410070401d4900810341a08148004181c1e4042843e122000030000b0380c400381c25a0340720405501100d484000130078402c40100001c2404903034078 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 467464793 1250 467463543 467463547
    0x150512030a0c081b060f070219030c1b0b03040303020705011d0a0201030f020903010f02090f030303010e0c07020f100203090306060916080a02070606080a0606060c0b040807030e030714030c06 84
    0x7628010145590614000c081034000f00350442c1c243c040e400c01c2078600035104161240c03454440262a5914400c0780ca01e40103100312203020916084030840c01c445250160f072400070545880d03c960006505148148480103030405001540074202d9011314000e034400e81e8096550f0340642050f03030075501d055001c00d0440071a200601002c40300060b20741c480b50b50a00b0081144c5c41158260307402400b5401d07109403d9401d02110182c0b501c45940240320100d0202c8882000320b083c80d0a2640da40424003079241c0002e0310b45c4c04140d41c5601d000c05052003900c000c5c5042d06803108203001c02d800d901c01c01004000350348082080b43d0589000e10083d68056810f860703400703003450049581c40f810081940704409000a050204003040560f4040781c00554100f041401010740d0740d008140d880c04080c0c401d0b14080d00c0c269010a040b4030a285a00c1e480c0d0f00519005066200c0b40c41f601c4440c0e209800841c00d02815107000d00103620240540001401c60055028200405400341801e002c10740140138415941 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 467466043 1250 467464793 467464807
    0x4030809060618150306130302010f05010e24030106060c060f140a0903020c030f0307120207030f0204021606060b0c07061e0f12050c0a1103190e040f15051203 70
    0x340182c0a2410a08120030700c3c03413900d0301e0380f03190302c6240340d40002c41c0c05000e480104440141c440c440d180d8001c0c131942c020410724404120050031140e003800380040c00c80c84040803501d01021a1301d44100d030060510302440c0d204021000030300b118440e60014001ca0040580a014040c2620400444107610a01032004081288451f611540001e20102080e65174100d84004d16108000020341c210002d02180c01070030303084200c07682d00e802103078049170300c4900c41d180004c540e440855170408a90740000058410b01c029401c0101035080303017035605100340460000300d0105805020b0107000300349944602d43c1d03c50328041c20700d00b00b001541091081c4440401504211541d900b49003105050b40c1c500780d00b101e04644805c943c0c3c54111101000407605010900c482915010f008000c00c100d80d8580d03c000384000e0f0340403510380c0110720403402c440905e101c040d4030181c0907200d1840d060f40010000250344034250781180803079a003002d0403143e84070640b4052001d81014210040919681c400079414815 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 467467293 1250 467466043 467466049
    0x40f180c02063106020304060b0a080c010c0809041b08012909010302120403030608071409072001060906090c051314010203121e0a1506080612010212040308090606 72
    0x1a0854105038001c14005011840c51802241040380f0f086900741c0c50b01d83e500b4040c003e50070540e07045e43d03c00e03d000e80c4e0759042d2a080780000115843c02d009440402c285034015100d04c0c1101c0c00980d201a42048031886541e40c1d8800c0c80d880881e03003d034003100f2882001d0000c10815050f0818041180380b0143c035881c0c40382c01c1d28884444a40d42c0c111b2592110510012000b03030080140070900c0e1541c3d0024003040542641140b0140c944080031501070641e01c580420301c14078000c0080e601f1010340408540300901c43c001040411100001c49210405130a004030f08591480d0b1003810100d940d080e00b8056440a03000301801c2d9030f040d241c040d080c00014070b4962001c138030901c220103100065070441201c9074024016a00001400400c03e84680303020325002102c03480480c001807164003c0800111054880e02c91601140401244000c941d8200041a50303260805042c0640c40461002842900f00090006045003800f0442c61040d505192402521090001d020351410742c05c017000f0899691 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 467468543 1250 467467293 467467303
    0x103020d4224170a020607150b1c030f020a0503160317151002101406040c0c0503090d0302070e0126030c1b040b030f011a090103021804080f040f180c02 67
    0x261003003100c01103815112429904d0300380e01c003800a401c42004200e847c10312818000d22048440c40070f80c00e12500c6400e0007007000703e04c5185c2c0c038072140034118610301c4040b03440b403901200c1c44a41e03030044a83d0b06466898103403454228070714202046200d58031001c105540200010040001154011228180074a03210302e0440c0c501e007014010f401580d2a4040c4520801c0b0354410b2020f401c00802180c4070080100400c40700c200d4190740207a04141c0c1d000507040c4148401130324550448090f42c00c00840004004180010003020b0b811807003000000309040b489503c1d82c500802142080c0d40c404100105210548102400c1070740540d042400111007550021a035081c3d01c80501c3c801031101800c03a40090004d11404c042d55826115a16034484082c0703056000054038407039415100300d0a03c020040241c80780742400700039003203450b4007002003420002c1240355401510541165041c29540c110305000781d0407560001d58068401c030b400f00072000b040c001c1d00200047c1020107102e2404111f1000c0d43c1c0b4 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 467469793 1250 467468543 467468549
    0x2060306010c150c02030714030a1e0903051e010c050c06011e03050f0601180902060f0702030102070f0c14040501032102031b10140103020d4224 64
    0x200016066500030800303586091044070740d0681080240042204c1d00958a800401d0121100711001c10904071442001003074a0101c40f032507850a5401e180c403080180f070300240344500010702041c5400400050341c1407101c8204c074a850400c0c030107903200c11b4a0417825a24908201d0086c010100003051540002160050554441580561102042c0400080209901e90002c0c00600421183c480e80600210f9a28102d40001d0044c4041c841d03d01b908001715489900c2c006d61107002000881440e4640c00041c044403400200014200003107038503030781100c00400b0400c66624100442c248801851900901298030f0240c0f0304100320341c115950020690400a40c41c4960384c3c2c103224160b00070348204101e841c082c8903031035503c3d070150740c5003481c80d0744240c0a40303107408880c01c20715011085a41d60510504880d0010144405d43c61243c84511541d00440034054881200070310409180f11007044940007074a590500c00000c0440c0050242205c030450303890078908000b511610010702c0a408800e0507 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 467471043 1250 467469793 467469797
    0x15180901050f1327080a02070603050903160c0e040b0414060f0105010e0f060d0204050a1a040e0a020403120c02090901050103020f060a021c0c051203040506010909020414180f06040206030601 84
    0x4030784814100c411305641c200c980a4080300c40131040020001c00d640503016a035031796000c41d2119030300d42100346c042c0c07001207441c8030780340e80144000c20803110b07890002d40c0700134080c84840c80e100f40c40f44010088100c0032a0107840c022070300c6042c8010401459000001c0c0120000a02054104401485841d1406120b200d042194a00c1c1401d05952000c07594010b80740020403060313481c1501c40410010303400620400c0e03c0354800340300010b900e20072071071305a40d43700d080100280752504215890b81041405091034810503400c1c00b000c40000c1c002c0511100403541525900c8a003911481040030001e0002c1c403403a00b5074189001000140c0316041c05102001c802c5030801d0f120303083d41c6022403802401c09d071090382100f6038541d040352722a0071440207419a800344064500080c007640c1554040d01c402d41307004005912900c0100321040700340e1700a2030810f10013080800c503608400308000301150b094810b00f07401a4a00e6120301250307070030468940301c4845e102c040c18441c5080d4000400b035010041007641 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 467472293 1250 467471043 467471051
    0xc030103060515030607080a0c17040b18010e0313061b060b030a0516080607021f05060109050d06290a0b0f040e04111008010e1515180901050f13 64
    0x80c0448a0411030054658050200c5c2ca1600e00380f403004000140988510003528540a00c0d072044c98400c001e00c0d032088489944481715038031740d541d6400c04810020072408a044000d61a10200c43d002c0c000e641c881e268410003961035001c00c218110328118550301110070300c030751040c05180414281d100030749150b030440f000207803809090303000c02d040480071640181a405500010780120080001e490241c510300012036940b40d5420500341e942c3c80c51110780146440c042e0b503840e40c400c2c84c69000b040d800320040c580b0480071399490001c60300348440d066048840b1a1249403c0d40c201080e9824000001c80c03400c4d20340301d40700c251710206502501e103000e40007900000241814600e034812003264010701c201c540b00303c07162509050240481c1030610b580c5201302035990b214000340c2d124401082c180e42c4140d04a04090315400d842c8100420a100c10a130003005010910140b1440f100241060200d00c202008918560808001d03c07508160042e511662a84200300525100c04a901e0841e40c11460001 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 467473543 1250 467472293 467472301
    0x60a021c0203090d050f010507180e070207030b0106080a2d050606210702010c0302030f0c1308030f2115120f011a1906020d0309080d020a11070e0c0301030605 70
    0x2d0443c400c1c10708850308034111911500400c20001600c0c0001400c0000030401038449030070840700311144003903540200c1000201807242404805c6050b4106442e030040320000e079625a10580103c41c240c0c040004030705401c003041101d10b0b6034001c80d841000c80107644040c0180d0000355400105118011542250b1b0341c8001400039198541102c506c02c0089401142d046004c080480b071100c411039183d00107500303003e10104124041c1c000e8a0080c841d6082c0254140d65031020000260400301800e90464000b882c0041d68160510090406c44458000716550f8000503240c04100c9070722a482d003030003030262010000041c101c2d07000c1c214058002c135080484c1140b03140c03c0500e4580180601c0c0c04a518006100301ca40d8041d1070740d4156850b05840b4010100464000100b5078040c0340b1502001d80c005003a10711782903100b940a100c40900c03400340d040c10704c03040c03851100c202d801503074501c80031480441c4048030144040044600409500c01408132a10300400282014001032000910854440000c1 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 467474793 1250 467473543 467473547
    0x1e010b0a050702063001030c0303030902010309140d1803050709110d0e0a0605061815061611033d1e0b09070906170703090c0b0315060a021c 62
    0x580c0740c0e0f500100382503210038141031140c5c0d04c500c40450341081c0f92182128240500065621241200d8014042509003451614264003038442000708a04043e40d0340c140d000018580c08090035443e091000a00b0910214000582400726010807075130405241202000044c00011300041a505000c20104185106000312840390148440f0030701c8150502d01003007045403000401c1d40b02ca40c02402c0034881030b241c910500503202819080a5080c0b1000740c0002ea00020007140c154a107100942480d141c40080c42c000c2c0e1070301c0c024a00032500c4035030700d0728902c2e9249020031480e241c541005580400750000b81d4510340300b51242c80100001c1e0454480381403012583c5600c20302c503804d0b5290b5160510760304401103074020801c1d4125075108610300000700703c0940c4210f0101058424030744071800a0080048010502d035402000c0c0c1d010907480300c041c003000802d03c180200040001d50419512800d00402a910030889010858043c64091280038002680002c140b070b610301d620203601240442d40041 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 467476043 1250 467474793 467474797
    0x14040f020a0806160e04331a0306030105390706061401030c02010c090902090307050d0311191e0515010f1403070303052b0c0c05061e010b0a05 63
    0xc42c80840c0100410411103c5201002842140d01170b0356042c21000c12504100407036003242000d0503e83c441c4005542141c1000a2034920078802c10310304440242e84040400c0780a055907080b01c1000c0000c07007844264102402050381142c0e88440f000814410400d46101141c1e541e03a100c3c001c19141c8280b10720705001481110769a5070404800c0c440305840d0310350454014100030590f40028542039868903010310611500110b007100759110201d0614010800001e50040302c003440e07040c00340800014040d40c5619104200d5486a140c0d00070354a8080c071910f013003540300c0c00f80b8203644004886034000200c840c20014101c0365519241c004503869070134001d01d13010001c1411070300e1901e444000b1400d85a1200254211400c50750541030a0012805154441d19940303c01801700d070341400003400c900d105008101c200541c2140d90709080c0202603501040e1104001c454000c0f6076403113035a4050140500003550706c55041e64440d54240501c0031040f0001c2014415241c07019030204004205522642c1 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 467477293 1250 467476043 467476049
    0xb1803030109091505040302100e1c020d18120f050c03010608061b0c070902210103030e18090619110301080706030506030a0f080307140c0c040f14040f020a 69
    0x1084a4a941e100d403007003001090703000810b440310440050320422003540c41c01a1845140d06074080d0115070203c240d11400380034102c0c002803082c043c0711445c3c00d01d507150148107007441c5210ba005200700e01a080780a0688040140340490728910740d4024020812003203064071007583c0c0241407400344000b5080c1a4101b60b0516004c5a02d942030844c0000c1c1700400081c03030350140e1038036590802020050740c0000014480c400024440d600052800c00168442c0d9010780b600786d04d112113500210303c83c002080035900090700300310041a032a504800c2c181c181103544000c0c0b5074594400c0001c500b02031601d0b0ba034502006222105c0e42d01c002d0203901d032461298000b0700010f0f856950142d241e586840607251224118010440064038103c0000c1d49484c000840c08030054201c0344401500d21191240d010581c002411001400780900d81d20744070b9115640100290340c4014090300d6105030706810071054a50041c1e5001d007050404551008000e490100d8a42140d03004081d000740585034400725404000e680c3c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 467478543 1250 467477293 467477341
    0x20d080909042d21050705071502010b060f1b03040503010f0207020909011817040f0308070308070206060a050904020f09090304240915020703210909060806040b 71
    0xc0070300041004681c4198800140060444000c1c01c3c10342c02d4036000c540c8094043c2c030745510780756503074900303d60541c200d0342815152621500e0454151561450301540350701102c4652000c480a40c4450350a10801000602c1100c11a10b0400700c0e04280ea00d038042d030b041d070b8ad51124074140a440d12a108100b03c134010320025009014583c15540840d0094100d20740907400350242e40001040c00318180f18680f18402c514041c60344902d0940c54000c100d4812841c550421502008082102c2c0d0030340f6940401548a21000c070781ea60386600d001450150701070920b2041d98401c03010307c5140c1d0384c0c4044d16001d0754815942d16020360395900010f0702840c80c01018a820554050900000100210050040c1d4001c002d2850b221040039080c0800c1da008011010b00040356441300344413481c1a090440d50016041c41214907264484d21811026404580043c00d00a503054081e1146900a110680148200700040118511317000802e070301c0d81d02c003c00040c12010030704000341407800c02c041820302504c188 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 467479793 1250 467478543 467478559
    0x3260a0506010c061e1109030304030f0606031b06020f01050f160c0209041a010605040b0f09030a0212100e030c0304060e0a17010c030515010e100e0306250219020d0809 74
    0x661036050081d621100600840e1b007000c0584d428569400100d4a60000203002180b401b451070312188805403402e03504071100ce80311030002011884101d10004541d001021491226280c84006460242036950f1002540d041004104190240844183d07210004450050200e07402c0d180455070220070090084d4403038a00c20600040c084602c00b00040c101c655052230701c4a0b6200c1da02903d41d07004038865410489010480019003020640152000d610060201c41340154541d001501361a50201241d22030340c00001681a444001e01a919040e5442c40c013842c902101b1259150b00d80c46a0302400d010b02a8204147d03020341c880501c0c01c0d00900ca0000a00303030104803034a0407800b0f03001c00e1880400090401021031801300001c6210030703541c0030507110385080319003480500c4585001703094030740107011801213141000d0700c051000320b09c02c5072201e105034100c3e400d001e8a220342040031210141103602c0f40c0c034841c03007010320080d8800d229601116107100c0d1340003a01e13164045200e842001500010a = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 467481043 1250 467479793 467479811
    0x30e03030706020f210903040b0d0b0301180204052406031f03030f020105070516240f0e0708030703020307081c0f090201030c03150e040515040c0303260a0506010c06 73
    0x808001303032120012017504e03500150b00780ca004040010f025100099103820030001001400c56250041440d1880c0000225010050a0000303007160900605d201c280480c84000400b103281622585a0101a0140003214924107200030340d0b400c05c071145254002c4000001107280e4119000d00c101480b89840f00d4104126224a402440c248805808038050b41c2080b0208010302d01502c00d442c80c0a403840340f4540005000d40700c8407842c0c02c5180001c81240d81c16000712062407141e024020010240f410045400da1005035010700c0c0c002c4541c001001c40c0c009120050020340c0c003004959019030003240a685410706109030303003050f1005042c0240c1d13452602490704440c0006420641059000362810001d02009400135425595801c0f014820700d03240d03640510210180070400d94009020300d08407452900004010369030600b042d58242c0c0d410210310010810550301c201000000c50240040140e40302e0b1861240f43c52450144c41c0100c8070742c841c2d0001d8202e03445010040c0010307812170f00038000d0304a = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 467482293 1250 467481043 467481067
    0x911070606172e0222120b09030901020d05031b03010f09180c15030f0e07050a090207030c03080414100509010b010203071a04080d0c17090a050a030e0303070602 71
    0x10004103030010600402409071850706a58044003114203044140040c100140e074032410082d03004085d000b0182100021002d0800c41100d150005001005036810081d21107003081001c1900051558806501c2080030700942d0341e0100b12070061141034205a078903926072400014006003145001031704242c000c00005550000c140041088584140701000340800c070517080d0003240c82052011f40565100081007080c0044500c100071108450324002401a40c000410f00990710201d104009580c01003d043c8043d01d41031481100a20480c1e40442c50710549a4010380f140d10076010107005e1103506c0c1e0005050008a049983d1012841000d6902d042c1241003007000419003640c41e04519032801e02d840040b03500000031a054150407061241c04650310004000c04050020809c030303024541408203403080d50842c001e403140c502d040d8590300e00d5200060842601201d00508180a1743c0c410f016130b0340821008544aa035082d0185011610311900c0f0300402c0c654860000b00910b0644005141d6503940 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 467483543 1250 467482293 467482319
    0x7061109040606030921020304050d0602040e01060504030b04120c0516091a06073003021815030402040b010302130f0302090903040e0703050a09020a080a031e0203040911070606 78
    0x8081181c04222607912140101c003251802c401c01400071031803c400c1c080e00d80d40a8003001c09542039104592a05880f9004039100308801c1710215003203500480c0a011901321760f0401405401c0520b40141010310790b45401c5540132021700090125426114076041c0d280c4075440310502180c05c40c00304d42c1409a0b110f0a460021564420000d03c28501241c0344881401140f404002d0040140754134180034080d00c40851001c1d030050100c01a4102c0e5442c50501d000c40d20909130b8400140d203006803030384d003440300700b04002c0d0700c1000342807081806c0d28070f1000c235450398030a881d00a030701680c00040984020005038001d20440001c03101e690080305000070045034403d40c80083d6442514249101e4031441e10380c9a5a000381c2c02002c00c0340d0020b000150555100c2d40c80107600900310301c03002c5030b00c110716000718034126a80d4000b00341d0750b00050014424940c21500b130440c0400301304c5103400d0004071004000d4890040d070240450b46074a41c0d00880c290a101003d440e0000e40040c010003005966501f078641c02 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 467484793 1250 467483543 467483557
    0x11070506070318050102030a0c02060c0a0c030b011404110409020715050903131d0402011d060a0e120705031b0f03031902060a0b03060f19050c13080303010b0f070503070611 76
    0x80f070391070710081595440482036615080c10307615440100030081d0308100c0d00b600005c051301094840e480071034010421051288004500505001c9059414030710f030030425061410f0038a02450402c01482d031103c44c150111012541c075a1001a1244240d103015016040382d0948030107094100001e001c01c010000c00207100c1411b070b140719140540e81e141408000d20440c0111410000d0450002601650050780044c1d41c3c011541420f8074090380c0000000c0e5690484105a00060308a6404c64054240f08110484c00b5200705d00901d21343d8036100020780c0d02d0040403800c80d650351481a10281c280c94600d5048642d01d00241a21b45458071800400031120710018024011301c61180401d45200003445042584030000e07000d40701503a50b1a44a4100701d0001e08024141e41a1068114100c0c2061041c40e002c5c08016100c0d564446d55840c000e81d51211a03004440325070410001080b55184d42c9081714258424038802071744403070172810580e00314060b020019140c5804c1188425030641000c00920030 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 467486043 1250 467484793 467484827
    0xf1e0117071406040306020f0d0c0c0b0601110703060b040209041112010e01120f11030307030c0b0a14181e0a0b01121208060307120b04022707110705060703 69
    0x10441c2d44080c01c0e40030580a500998010004101c144003180480d0018403807245215545440c0c890a64a0131046074045e01300c2e02d00203030b070a20504040281591161350441d10920303208120070460701e0126100c009610000305820703540c1d8060190ad80300d980654403045070003801041050058204c2404036407080590580700d14503407001040b207089054090313040e1151140403404160341c661b07072200d40300c00e1000f00781e4038000103030101c03450740d03a082004140c1c1c90710956800904907098500860503020192403080c8403414040301d41d00707422403c01303101e6102641103560031003a0200410682005076420b50900e0480d280c0561b200000c07400116050203500c20130354817030540c2c0c3e04d89240034002c00c126402090304c0081e40c80d030300b40d06100354041c4d5003140c0d008041d00c15141e580e0322580b80c07155030b8150842d441140007013000194030301032a00f00e80b040442c5000448141c0c2254040b0000b40d0003d080701c046c081254840042c0000070002400645805000c0d01e54070441c50602601e00d09070800c51140b = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 467487293 1250 467486043 467486053
    0xa0b091606020d18170a06060504050610031e110315010309020f0103150f06030e240105010c0309030b1003110a03050303060625080c06100506030f1e0117 68
    0x1890049544010003120402e6000d0001c10f0901801140d031162010343d40502c1e000c0c02c00c00407035042d205400b240c0007100c81000a01c900302c140c0ca49002690710740d5000e1445075140008208090711524840c0304c90503014540002c482d18a00c103410141084202100791030b500d4403241c5410440c00300d000354003490380240c8000c1b900010a0046050310a240710094210840010000c0c055000740c100e4000301c1c0c10f45404490840c1c44440c81da585c0061a40030000081c0c036440c01140700e0206011290268030380301c9a6001c000c0000d0303040c64102406104050401c4a0740b50247c085c54450b4034184003455101004840c541401c4403d06030701c8085000960740380c1020501c4072030b50700d8800f4403901100e0340900914110703903c6408100442d00141040c038040401c51030402d41c00303d030074028442c09501c9164660307201c2240031010752a000c0c008100c6220101c010b10207101580c0c41f48151f950001c1c03c11000c9819555101e0924500c20095604e000c40390186000070801248955050181d108004200c803 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 467488543 1250 467487293 467487313
    0x10503120703050f1615021e07020922120c020f0121050a0e010e060a0b06030f0c030403050415110105070e28322b0c080a0b09 56
    0x1103a188100c41004012420401220078484004c5001d0b1040003940300c1e190740c1c81100d64030f070344000c1c0d0041400d8040c0f09600160342509512500f11035400c68031000e50765801c5c4516540890f0241e2030142a0740e400e05042c240902810068030787e8070103030541c4040d410b0140310410b2030280811402c2c52089204014107150b42405503c11110140f00c641880000c0c04030b4400804400014900134010154107a1101e4005c40844000d01402c08031324540c40003801d05103007075202e03182128429042c4a00c240d1041003401442400c031510b45801c5258030b580c1c29a40e45541c902a03615104607444004032030000201c10001a0f0040c01071626241c88000a00c0310b60344d100402c42c2d11000d0b458040398040204035001c19011700081c244007500000340c0b41852102c1d124130540c51000404003070022409059400090b42c03595030b0044110700101943e003035103560141c2041d800c8806101e68800c401301d1004104078140105041c0840c001d02d5203400f568420b0f1114100080c0070582115a4080d5104d803520031 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 467489793 1250 467488543 467488573
    0x20d12090b090913020118030c0515070803071223150f0d0308191401090b0306070c06020d110f0702030613030509190f1202040507140d11070614010503 67
    0x11000844000c0002000b60744112071104802c1e40310344240d041080c0034020900480030f00c7d01c2e1202950151001c5c1c04218540030801811203080300c00c001d00c0700c0302400110300041c00361003a40c0c3c0154090500b90095101c0c02240300c000d0000815118078079090002d20000d44c40c144524a008140b4503440c1114500c0c2d01080c0304140301c0201c4000c0d00980e480250001007885411240d0b00f0000c1514091003a03980360348002c040c0c0700f038003040e100c88400303540040052248604c60006800010f03000303000300740341422024000e00419840034091039000105601c4501440d030064030110f00c5407482c1074940001e071807520b50903000900304a00900c1184080b0304c0c1c40e1403c91294400c2581680d9482c90700034a1410301481c104d1000d0301d6480c080e5164408900e889a031910500681000c411070b01c0582e000e8010001954400341801c024410240000e0303081284010441d005504180004140d501d121405982c0c02d2043c654090071507850400d0144d28410384030b201904030348040b000c0725a00d9031103080c0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 467491043 1250 467489793 467489797
    0x30602070201200601090207031e020d1e0e06070f021230090d0503070605040506190b1f02030c01060e1503120d0504020411030a05091204031a0c07020d12090b 70
    0x90342c2c03104e0344802c00410643d54107400500c0c0c8548a4544410401c2ca04c00f0038000810103800d180000d0b800002520021641c04911500140201100845e81d00c0b1600303406800000ca48401c24003402c1c0000340a414400302c0407009200329400b5000103005420320460076150070594100a80d1100203400404481c002903075811886101191a01d01c2c02a000c4108070009a80c444221481d00060101901140a51040758442da018901030801841c0500c0e0f240815079031010707148030305803030a03401c41d8184d1204014544100025580d5911200c843e030750036443c60140100719156582030550100e801138900c2100383c043c100e40e01c06240c144802d0b000309519401d40b038203550744070300b4240490b090348901a0410b41d08640040c2002407140b044220146055104480d40c1071099210b03814080300100400003260982aa01e00e194141410360341c40503418000010144d001300242400716031a20316100c110f48400e41d0013009a101c03e4014507000e01901c5421141201043c24407a00041c0c822000c01 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 467492293 1250 467491043 467491097
    0x40f0c03081b21030f06010c05070e011805014b091a01050a03020306060f04060c02010f0201060503071206110a12180215210a0b03011506020303010e090a0606030602070201 76
    0xd00f0f0b030869072910300b003c80c080c0000f40321904110b141e802d2040460414400302001d0f01c10010f0302c40701e03503040caa2800c8110405040c030100440c500001044468042a0998480620959202d81c031100c20b045249800c0790040440c5001541d4080d02c940d0008012441011102c01781c6050290902c2c0d115100c910007100380000b40400d50412501000510a900541c2d22400040ca440e041090f40440d610441c2c100c0d400c103402144008120070107568101c0603401400c52148001d0000908280219032030303943d2445261600e144c40308045003040300780d170019035130701161100040e00e031003c405008224250038055940410b1030203038402242d540114034a43c0e1150040c082da030041002c41d81400c0c2c42d5204168403440c04d50704c242c00700d507200e0110100318003c8140d90800300e05020340b08201800c42c2d40800345818610743c50102040000e402000303590450b80e294040344c515035614042a424444100d2008203454500103011003000342680c045c0c00e0460003a6a1800c1030162a0403101c80226110 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 467493543 1250 467492293 467492353
    0x110303030f06060c161805090721020607201809030306060c01091524081b01110322150c06050a0207021e0301051b03040f0c03081b 58
    0x40c000a1a0f400e2200007403040035446400c803142e95501803840800041e141e0080c814601c109141a100710401e80a2070b40c001180201074040c60345400c030300c8031004031507080064845120300f00102c01d40d55510140c88001703400c04081d0554030480320540014508440201e4800d0556100010070f4400203d027192045851000071840c5864410410407181c000900c4804950340750a240400541200c442c44c05405407804080303100503070300001e80d442c1800106912502c80c2c48040401951600203400721500c214950301072010b800d001c0048400109031040d854891200150b00310075015140343c041c072454403610843d0441504c07100c000d5035000b802030701b40380082c4600c15040003082169008540011004500505e000e02c10742c041900e20f090b4503c02d1030b06241c44400d002c4641003c0c0141540040c90918068010a520b1100c11321400080e0001d8007100d40050310008000d4024420000346801ca82c030030b510707000096015104c4a400140901403805000c1c1e207141400480310700040b039071903d9 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 467494793 1250 467493543 467493571
    0x6030f0a051207140d02011d010c0e06030604020705071203121119020106080a051506030102030708040803061804061a06030c0406050d0b04020417060c0316110a08030703060311030303 81
    0x2414180b0b8098224080a6070414404400c4c201c0d5480e040004c1000ca0308075800115245241c5900001c080d150702c48101e94030790400303c081c8110307640000d900310200300484030b0316140c0c0c0f500700101d0003d00954038020700511417a0b5000c9802610400803015240c42950359a1290210440f40ea080d1261401500456403080c0320101e09098091100345102703480b0720000070540c0d41d1f1124946083e00d03140d026120380d0007446400e0440c283c0144010351000c8158001d51460611410040101d800240003902042010001c1507140d5207007200103d0f01180300e01031a040d82401d08100d4014802d4400c80b05603c2034880e03400d1840d051003800d503032007045820692402c0c41d1500350140c1d4241d019000030102c09684480c1e521003941c441c4064409003044c80e04a88640740000d0080703142850150a120082400b8000c1000348011100d030720a0f080b01c2403525045124180c0c1c0458503040500000426140e004400c200e101a89544050708984c019100d003009110620281a00c0b40300584441d4107042c54 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 467496043 1250 467494793 467494813
    0xc010c060e0c19030c09180201050a05040806040b1801110f09150a020d080a0204050a090b240c071a0703030c17010315050c13051003150306020306030f0a05 69
    0x554404140405001d06031010342c0010b0001801002d9030201c1601802605a81442489071403040d01000d00624103040003403419003002003d03400d40c8590020b0400c940002e41c440058802c0003030b64002c255400849180341000e28052481803411594009060700031000c0c0300001005001d500c80c0d01c0c82ca032034003624142d83c4143c008803aa0045083d40d0300085003c07031743c83c00128032034024080345660b03034081c251407000d41c000100580070103040800c0d074500500061240e590740e5034401d0100d40c1086000589040c85d90003240345902c044449000403a80b1303110340c00002840900070704c15864150f06035500c058070352090311000300a08c000c4000190302031210304c002034020b50180714000424203042c855140b8200486105102c2604216000d20714012003031503280c0316025194100b407082810034100f00310002d5991100c4601d110f9584102d00c8085184000d5029601010740300481c0b010300b02d560794813030034100060b60050700c80500a1040d8030b041281c49401141211800ba404000780100d503131 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 467497293 1250 467496043 467496053
    0x6010305060d0203120306010306121509031b0302010b041b0816020c030f0c0321070615080102130806070306050a0b0a1b1208010f060e06070f0602040b07140c010c 72
    0xa0a0035040b0b1a6981c010700569800c00c2115649014144030355030f645811800101518016070000010000c41d2885100003038544049284c80d082d10350000546101c5d17410125405240b040c0c1e0000350804035050401456411341080f150054295028012404007070201c200034502005190002203089011401110903814144090400c0e48112203040284500080c140b0305420705505807a40203407908110b6050900c40304108c82c003452101e82e070203081201c24514074820000c0091806941d1014903a4003040d840413030f406891880300071900e50031480c02103503040d460b60055140b14400d01c80002d042030b01c01d004110035103002612000b0112b02c3c02809110301c0d000304c0c5400003800908401c58000507401100325000d0790041d8101d4401d6001c0c8600a441c0ca48107812000c5400c0034001b0070b104e000c1e0011904024031009442d1107a40e80200d0074103184000c6101d5008018500004000a4030a1010003802d0218060000240001c0410321010307900e00095031030601080c00f203044200400c1c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 467498543 1250 467497293 467497301
    0x10c14150106110307200301060b03091002210907151d1509092d0103020117040323040f03030e01020706020f1f18050d17010515130312030501060e03010212060103 72
    0x14101840b80034030f0848a00001c0c20b4449d03c0c0c00c464003d5501000b00100000d04014114a00042190840c5481810300300d60003038114060804800000c1c2002141c07040d54100b140310010b1420780c43c4c01d6900100341c2c8000f004840010b01e64800d14944030f01042e094900010041c944060700402c44d407802c5000403c5c8003d02d50001d2050000e03601d01030301e1604051081c40440300900710307400e400140b50305510024201c0c540da41c00c1c40c40120610800c11000940044804200c801662842c013464402071001070064840c5801030044500c240400004242c0c10a005002c0d02c6002d030262101d6a0b1034650407aa2818000d80b04041940320b04e02400600490308817000c50b584260001040d03c525032441c2e03400c0071074940c104540c03075031103a01140041d80c1d00030340300417a071a05201e09a803103501d400002450079840da9002c8079061000609803000000d0000c00c10019030740040403a962100f0804064005d042c24498040404c121090b0241e40c1c1c034040c401c891580440d54a80c000641b14000114014 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 467499793 1250 467498543 467498573
    0x506062b1212020f04051e13050a02360d1a070504030210121104030f2904060b031002070308190e0102040305012a120209010c14150106110307 63
    0x700840d04411040b103401c1d80010301140d0484d40900d5962850101404880a683c0c5030440440f40c981750300000320341c0c40d41c02c2401c00d5204024003080d15182ca22540c0001e02c1592850402d01941c080c2403c132001c072403540100c103080d1852666424441c041b0a00500e13461641000380352071140c0341d0100c680c6c000041c6458010526250507410540c807540420361016010003c5000300b0908050034030051a0f5000e1840d00009444510b81007914591320501c0f0a040c40200a1014910742c240b619841803107104d40c80c42500202090601c1c0c1424208031004141101d0181d0180c018000a005101198002c0b50845581507640b0345a951360381e00c03180721b181c0806561414945d2224802c00c041078090001e003000e140030720000191a00314464444c191302410b9000000100003070001c400b440d4010a85510030300c04103a01687d9204201f0040391242d07042075000b44a0b11901528460006000a000841080380d0503041d08598071000c09480840700c0303e600ca56203074420400c0d01c00103901c10301c400100e = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 467501043 1250 467499793 467499797
    0x3030703051810020a0b070915082e150804020a060e030a08131e1a0a03090f060606080603161e030c090c14040f06051c05040506062b12 60
    0x50306820001901001c3c2e100c910800584c042c11301c400c1400880b002e4580c120301c0c0c070b04243d840346207000691034925408480075070501c60f0000018a05803100c101c810b2040d80389001c3c01c1d0308501c4005922080c000700b4042e500052044245140086004515481c05030350020080329016160080407201010418202e40c0c25004440d0004005202d21010300b078500e0700800c00d52507007400c250300c56412403003243c00c010aa40100c8410402d10401d00840c050101240c0700306540c0759074040042d4003502d500740d4000c151140b08039151003071200300d5206805507005a42e601c0c6080c1c6034001012342c0d59a540c0b03c620b4840400075010868001c4070000c80d01010441500710301c0450703907070300e030404c106100c1d41c400d482c82c075240d86270b074441954003c5041d06d004000d21f50340b5080c90b003030040840502d0401c2c0200424401e0008440c0d88030742a0b8116803440c0c0007614002d2040b032400b490120380780c0702c00340c0324640160340c0e000304920954025101c080c1c0071010100403c03518003082c0c45090004100e60a4941 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 467502293 1250 467501043 467501077
    0x71e180504051009080c150426040f140a120b0f090f03211006050412030e04050709090f090b160302040503120405010801140303090f010306081006030b0112020303070305 75
    0x3e400410340104910207028180d8140c4a800d2903d07220b00313000007010305401002040c0100320000b00345510150601485820b205100c030310880d811740c5a03100d59004030100c03004400e40000c0c0f54810000484007558143c48003040d5558803050f10f03540b401041c2e030003090603200302c0002d12245015406113622640c0c03407045411200642c91014110340c08031a4114000440300d45019285011411f810b0304104500800034040740f400d1001050b900950186020602204a41c1d105240c0710300401034151030001d108109a0510b908003501001c41441506020703402d0640c6035800705014400e8003940c54000e141c5076803c0c1c0c1c2d82d442002910202c551800c041c560701380400701d46030301c081000c810101c2003054010794940c140384c0050702d0110140e01c01034000201c1c0915010640307000c820380e140c864064501e107203644211070040c1e0180401e0381100c4000d04c1a00c1005060300960303040541103c0c005ca98065a50740c84003000410041d480c00081d425a10170408040000d01c18401003001c1c540c1990320341 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 467503543 1250 467502293 467502313
    0xb0d11060f07110906090906010e06060d1103090f0d0c0f020d05030c03030405061f0b090a15020a020f0f010206070c1104020301060c0506090a02010906030c0302040f08071e18050405 80
    0x74a854000050a0320782400700700201149040603c1c00f036801000c101c81000c074a1604450059440d001402942081070a1070086046601c1e0071083e20141e200500c0c0521896103010f031a204560012120300a06105080650921002c00b1503100b06034050780c0e4581202da100d94039030b040d04801c20402280c0060300e16540202241050000d4000001c0d070402039a074a040c6814030303901c1c00c03002501c50040c0413180d502210b15046480140b90850728510445901c6141040018052200c036030b01c880c01d10760248900d01e17034003940450b1841e189442169035004040e440700500c14000002a0f60310b0269100c4004112218080c1700d46078015031280c2c1c1c102e804421150040b130705a82003030748000003040f070600d0000c1c200003060280781d40c000011002001d00210b05e40008001c0e0548c1d100340800e240e5034801a2808610a4046401a2104103007a000b825590914660b98801900c940398030170705151200c241020003d0824805c4880031800d00d40822029200c40000704005002202c243c4242e010302 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 467504793 1250 467503543 467503567
    0x8070f2a05010e0102040510030b0d0618020306010905091002030f060d02030a0f0506011d160503060402270123070303230a15090b011d0411070b01180b0d1106 70
    0x10140205102d0000d44c1b52442c081c180801c1c07403002d0b4a0082890304202c1c24050903180c80030f0604e2202e0308030b140464071030075110b2403040020901f04041c0d01801010300128403407070706401950003420000c0c210703103140300410944d00c00c900050300d10001102440001c108280740c0101c40c14405400103060300c803100c82c0ca03540c1d10000702000b9411100b541180c4010058212a0220760740c9450103100115101d142c1442c0022810b1441c4d4465000d114002c8003044041c2c5503a0706444940d11156107114001807444542c0019500401e1001d0002d0745200c0d400755450b03594154111640c0304000c400b41401e80554064001c1d000c4005502c0c40d508145408071b81028403143c80034003071a50b403500001d4017090307000010800050758000c2c103415810038109040e5640c0c40000d041d03070140c08444200a0f00c400100240180c150200b908a0000d00403071440c0c20b00074115600c5049820b21800d2540040703c4504a0043d500a40308155200c2c10100030100440c1815807032803030601c8010150352904040d0004 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 467506043 1250 467504793 467504801
    0xc09140105040e040506090d090509070c060e162105060103030c05010207060507200609030405010c06110415020c0f060f07150c03060513050c190e0402120708070f2a0501 75
    0x31707a080d0b4014001d0000c00b25081c01200d20580080c60252049418440401d0700d00300041c1a0710100180c202c8041c080c0b106c29440b00c030002400e003041c0c07032440114200c0141c0d03095240c01403074108450000381e0f2146040d50303500c940038150301102905c00743c3c1c61600c0c1980c000402100c155001c0d5020030040e40042d00b24400c4600c075845a8940c15a4100301044010325041c2613040e5041c80d03401034007400354810000044d582120801d1a02000700740003032400401404040810a11220002c100440d990450890307019250000da0b08079072150302c100c020821a114980000741e0012801c104d101e1203030003000014081203028540042c1c44000d05c028079400c4544c0036a010300041c0d0398240600c20b603d010030300a607114003103900601040c10480c511800a00c01c0350a001654048141762070b03c1c881c001c103400c400f9648000c10440d25100c0710501c40b14450000c80c0e01c5800142c0d03800c0000c07040790041503811704030002652018044000d03061080c501011149404c515845040c040400180090103 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 467507293 1250 467506043 467506051
    0xf01080a0905100507180b0d0b01110604030509311d1b032e1808180418050606040203060102070e0406060905071409060904021b010c0e040c09140105040e 68
    0x1c00003c1c28078001c20000e1550307021b041c007100d400c10540020030403060a013040d203000b85803c1400150200301e81c40142c0d0f01c1c5038008802000ca01420080205068000c00940014907040d142c1c0c04040003003110300d0301c1a19116449080c0400540e000040c502030940c0100344c41c4c0545040a041000141020785c0340440d07000b050082c1d445030002c800c00500b030038041d000f041c0214000b954002820000a44c0150454080515043e5a16480003040007990f40807a600e00b6005141c1550307600c0d40684001503010080981e501030713814004101c01c0041e40020380c15056420401510650312030408110280d40094205411882a014046092000c00320b449005030303c1a040000c803240b8181408094620090940050081291001103014070741030807188410011a61076070b450184400080003401a10780d100400b6820094241141d07005501a8100c08950307241e0000c030302110750820080d21003200008001072994502000f001204c011174180c007040504000e41442d0b00c6003ea461204001c803 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 467508543 1250 467507293 467507323
    0x2181212030c0c010e0f0c0303040302011e020114090714060a1b0501020f04060818070608041b0e0a0b010909151202030102040902070f0b0106080112081b0304060306091107020f01080a0905 83
    0x80c000c0e8410680410808040318008e5015608041c6540c0003c0c0005058103803104d80401c0a00388040003910039406066814000741144038981440100542d55000c140a228801e00e15108801e10f10b03c2c00702c0c00d641455026595100300d450000c1c0522080b00d83e4003104813110341d001c2c4032080a40d40034502400107080640e071500e15a01d000c8a8640d43e0800205818580d608500b20500c403442d84042901e5215420890701401480c6600800e10134800590000c46000c810320300b40702c04040c04ea00590804a0260f0750800c3c07080d2101d02e40c074200d81400c00d07504c0c00710200b942c0c100300d6510000f0b04014850b00045c0014200741d0f40f11014026a4440081111082860280a000c00071310b00034160151405141890301c07503050892901d1041180e04d8050061071000c0340b1881d0a0742101d403c40300c80d0886005494440303036103040140281c11940a4940f840d401c194141201c01030001c01c0d91070243d0024420042c1c003803500015156403030094a940b5407151216070210210303800300f00c03400b146603800c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 467509793 1250 467508543 467508553
    0xb0f12010209090105060c0a0201440f0603060105010c030c0b010603060e0a0902060306010c02040b0307061206170d0c020d0b0f07090b2110080f0102181212030c0c010e 74
    0x1034800c008800750141c05c410712032001806203040c40c1e0b000160700001170364217090490301c0c003038104802c6030150452989900703d82240d598850480b103075411184100c42903d00c2c40d17041034941e1190710790801c03001c0780c1003a0150301c550010055580319491340380034140242082e00072119291034480c9071100c26004100401c2c1c9403035080003a2407407000705030f60041650a08014400f410390000380d65110142150b41004000300700d000c2550340d140e002d8064014000c0441d800305540b058058144695105810300b61403401d0000142c04914490300ba0803a080e00025001c4c40e840c0f01c1055030b0300800c0b0b05e8148c0e00095030302c401c200080e98220071140a5409070a441c1441d1a10f000014440c25158110101c0c41e0828800800079110401d01000e0500655007000410303502c204800416440035404115584200350842081c09810760003014a00c04050f10151241e1041c0c00744510030108011789082c0764403071300144c0d10844160000d190010000352080386461340321001d079402c0d9860000036010b07580103 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 467511043 1250 467509793 467509807
    0xf080c0906131401200a11151207030b010f0512040c0803040f0504050c0a170c0d02070807020a08030f1c29040b1c020103020f071a0108100501030804090b0f120102 72
    0x1800860466890100115020741c2c181017468030b40300f4004000701003a14245d0048450b40e60780c59420004507050414a88030000042c010103014030582318840802d240c4034001e0060b500c20810034005400316203075103242041000403c01240b400500070f440b40c1611190100308401700b03000500040c4042c0c03495524203400c040c2004106c49010308030441d00c6104110468540341c00218070111160100081c3c040303661490b500100900c150030403080ca0380d200140340820011008080c0a60600981d000c900035600c5030035036540ca00c10115101402c04d014840300c140203100780819044000480740200781456141809034640e1401c00d00c010940c0000c17103044405013081d128146174414100c5400c07101d105051440030b001e1040c0000a410190009070801d5055600e00031a41200e500445900f058070342a0802c015a110a000e103044c5402000040c800319221405400c0c166030304508580d1500740390030003c100502003d41100c0e004480e00010a80700d58845850215180d0f41c81300140c1ea81031 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 467512293 1250 467511043 467511047
    0x21608130e0601080c07060906110d0609054006020304060c0e010e12030f12010602061f12020d0611090f0d0f03050a05040b04060c0b070f080c0906131401 68
    0x9007908480302880082041120680c2d12004103504041002c00143d81d0b882a81001009888840006040241401d6506668a02440c024100507003400400c210041d154000d94094810999192110901d4202100404568030080c120001d01c241811303170106294501c404010000320707030103039103641d0f02004210074000c090085000c8000e03a490301c000c09802030310000e0b00c0c80201030a0b582c01010170381c4401444400400803550701c3e4550201d15500c5074180c1c0c0912528220901480c00180208408a07000e00104808030028507061801e07548003904000d0341c9a82c04040c03e40c05ea03844120320b170620002c1f401a11800f000b00500c040c0c280d644120460612119000140071705010f0f05541000f240032549054a44040d00e070f040c40c00c590b07644403a8004071414011504582020040002c00050440c1c0100c845000070340f090550070140e56803100c4c152017481c1401c40f01c8003c40c80c441d0002c3c0900041c00001d20302504020809810000540140c86450304140c020b036101d8004ca4030013450960f = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 467513543 1250 467512293 467512327
    0x70c06030f0506090403140c0c0a0308042d030206030601140d0510062102090a03080d020405030c062502040e07091409030403081801020a0f05100f11040302090a021608 74
    0x10340e06468552250405e560010b06a260200601e05101e00204a605441500380003126400500800300b800258481c10082a20f80c400c3c03150030300e20321250515120084d29980c90500c884007291072449034600c1c0d6001d212556100601450400440300041e5004c4039514000e0301c061645c0d8000040c2038500110010404100c075000a4144549510000b03200b220007452038800003450300000d83c41b40040c4000c40c0c58141281c100810f201d074041440e0019100d1580903008907042203045940c80702130b5800344816071044c0741c0200b00c00c44441856645500039101c0103000c2602c0170f000020000006120780742031180316000706420035119150746202c0310300a0070498026010001a51402d481c542d41c0d80d2652045841c07500784401d4075200140c1c80c0c2c3c020300404000a402103946065a03115140a90325003200e40ca14660304c074a0300921070350180c4a0301c1140324480f5a50585c030701d0716086408000e911003009001015440d002c020f8055800010421103d265100f46080e90703c440c419440b800100e = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 467514793 1250 467513543 467513551
    0x90501061712090f0a150206070507080d020313060203010b07061d15100801140f1509150609060d0504050f060403090b030a0f2d090b0f0606070c06030f05 68
    0x400a06054111000008603a5811401d10b02c50300781c0e626031001000c0740701240291002d5a00040003403000950756801480217090103010f0342510441d0340c5081003078445001d44480030740803550501600c1d103d94540d500841c0c101030800d407082c4012041c0d0340c070101070717034000d8115503c03049000c00c5040c02c00010b07008a003210241002e418040c0002e20b19090f035501c8556034441192400e48010230401172000c44481c000d0000c0c02c00034480c8540c80f589a050308042034a80d031110350340e07020010b1071a10b410010407408400060580e405515000300c210021841d05001c658066001c21480b411646d0700f40080042440c000d20124280c90582007260400844d0048090590001e000304000264020420700650381d10f41c44003501c80e282d6411010091403034500030143d05141450b401d040e41c9980c1c18001e01000801c0e280200000b019140b202034072403801c0010941d083c4140841d900c84d200d502807951048019000604ac640c03d622110078400e07560340802c1c0800d644200240c142c45c0076020ba40d1780 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 467516043 1250 467514793 467514809
    0x6020319030b0913020d0f0503040515090114030a0204081c021509190611070515090307170702180f010e0109050402011d2706040609110a030e010b040c0309050106 72
    0x50b0384020340205825903002400c0400c40014180e0301d80441d91400f40041400c0c0c0c121510201c6030030645042e40d07807640b0030700400b40310702c00e04041010031032400e808a070003203107040c0e4401e5442002050104a640c1014120501598007448041740d201c00400040303090f0860741010910342060480c0c003900f840b080d8440c103204180d680040001ca03a200090b40002d00200130803c02c0140102e0802c007004201c0030344011403009001800000348100054401c4c001103a04440c1d90040d2200d0150036501d116205001f010b806041404040010500d0098901d0170300291804410b41608120444800e80c11185d00d040a075540c80103100c61410381012601501e9146001c0026003003d0b00040c103111100700c02c01024203d0003200700758a4455220040303061009407020062001d00d03140c1042131704421207280b40a94507144001a00401c540501c850261000000918180f144070045016140220902501e9922a042040701d86c0710707841221001400fa82c0c000034190300e180b40a6094031055400490 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 467517293 1250 467516043 467516051
    0xa020616050c030a0f120f0b130b010210050603030f07081806041212120f06030b0a0504110616120c0501140106023c010e190f0201050d150602031903 66
    0xa401c21000040758101180c41c140450b1101d03217144102c40c0c0e051a5001071000c40d061042e02c511400454002400e500400c1320034070111004060840225054420b410b40180d1001c030034030752010116400035030030050180a6911701082011515401e500030701c0704a03502c1c2d0000a041c0c98001044072160980401110f64602c0c0a140c205800301201c4002c2c40903141e03100100b5160202802542c0007000810610011f01c1000c4054140d40000c0c84175100c1540c4031142c0c207000031002c1c11540324461199a0010406c03d080d802d4000b03106913904812803012589004043e80d1000c10711104058003079100554824840344402e260050940d2002c0c0201c10200400c00010301000d0307004078010003030312074031050307001c01c80711034092400588513800814100b101800d0690040c8034040d0485001e0284c910100d41d02c409012804000344800e803e400b811040d10310724054015032254000300400490610003103408a66440100c2426100e43e201c0340c0564000584040303076220710f00700300e1109805410700f00 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 467518543 1250 467517293 467517307
    0x306101a070c0306110705010e160906150c03050c15060109050301020a080106050f04030f200303070c09091a1003050d0207141320030a11030c0a120605060a02061605 73
    0xc9428140f0302009010503282c40107804d00341840300c1903030038140e081402807000307420300010103442e851a00c00d0307403070380b01d0680310080344a80040c001c0c2e800b1540c000442c4404600c507080c0458251050180450402a00b04110000346204000828000a83c2c62107403025080400024000d00404d5102c50b003c0c0e4014400c0c29522504180000d044032140d0600315903424900c5403440700c501c900c0e04020020496114481c0c24080c4c0078081c0c040c800f80c50310711588504081c60415030790b03000d840d03001010307903c04150a02a0310525003203604c800e4803501e21081c02d040c04150040e0015405c41c0d0013040700140e0340c0100180301d0b0807c91034100003a5800900341d81400c1402e502c10584503403100c17502407160002011649001c1e603020711002c680c00c0c0300b00b1904c4600c4180080b1290b0050385c4501e140360410880d0019408114226030192031080c03400f6182010b64482500c8010b459400c03155100c0d6980400541500c42400902601c081c40d800340455240200c0b01401561100c10000c0c10814188512 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 467519793 1250 467518543 467518553
    0x30304030e0111070e060306060604120f031e02010506010f0504140105030c0708030f01590a0c1101050103020a1a19031b08040c140604050306101a07 66
    0x4940064040c07811400c04508240180da400c01d54150046191082d0030b400100101e50420300c5000c1c1008074241d83c0035490710800c01c03050340198004d4040c01030020781080005110b0040102c2d0092180c24088103400c00204400d03003402c0c00c09032410150f5112000c00c00710390fa11035a03404103c841400c0007420141010702801180304501e00c0c8a06010001010401d001c2d00c0030203944089521a032240e5032407400000442940600781f05144102801c1101c5a01203241c460040c860329680eaa0b02428142d41090700071030f5005a42c2410b00701000e40181d0380b54180c2d4a8100c107228141d4404089400e00306040028203030003880308030b4140b6914000041c00141e550380707201c008484400c038080b044054070440030442881150545034007807204010322620240c058010080368800c5070310740300c241c140e03c12095840b040300303c030001d1814210b840144044038003640c0100a402000e01500e00b800d4454010903c0c022064400720001c100c1c04504005031700a003a1140300c40e020700250709080c65010381d03407 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 467521043 1250 467519793 467519797
    0x503010f1406041a06040816091a1e030105040302010501050f0402040b0706050c0d05040c06110102160312060b0417160612021608030f09100e0c0402030411131509050903 75
    0x10340700c1c5851300310190001c9007590b40b0880c102d41c010a01e95445650741c2031196a1140d05950410f1900402000200b18015104141c051900408040141251807003001081108481e81200c20720328041c01e864907460900c1014030942c420303000041c5a50520040282100355601d020788030344d00400060240306800d4050b00e840c0396000d500800d03103172160304175544e15000341c80710b04240c10302d05170800007070292900d00d0f402211495181c0c41c03140c0904d165194203038401c121900006940c03120541000034450202c1101514070303001c00190190f00c4005c1d40c48241d015501001e009401c0c030b8201c0711411001e0060130380d4075040c000c3c04a90580780040c0a030100c441a0005800b00e41e0104204043c3c45171084000025a4044111696840d0201d10206042c40560340d86005105140341c0304500462442000d50007085e410040c00c2c45400e550410000e580002d00072a045400401403d40d10307182c1452145d00c8040d1082c0c0890f501180c2c02500e40000350560100e14078070308040500c07111400c0801 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 467522293 1250 467521043 467521051
    0x30702030715030914010c031a0f010806030106080d02010218010302120c0f1201080f060106110c04050a0b0613090507020a11040f0b100207050f09100e09010b06040605040503010f14 80
    0x302000844022075402d030000c0c4074071800600707175291038101d116024034190b00c030b0030010307003561010447c0034846420102502c1c5090400c542144048100b8042d0358010081c095200c100280003083c899161080d02e0b0501c510540264003503900800d4100300c500800b5404204c080c070a18045041a41125195500100142a01d01c4016001615007800c0d20400102d0310410070001048825507560240d00c0d64504142d4104085401010004114581b1400c000103104500c0342c024880613042c14108401054080c00d607000096603001055a00e40310b900243c00640c0c0c0502c6c9110b02c86280220940c01c2d01c40051a910440d000b9090220020fa1807083d09034016209560019031294034140c0341004004040260b03030702441500501407260342c000341001c1a690700740c1b8105014030400b4148911010207444020f62807080c40030074000b420b01c0031328080d444202d000c0040384131181310b000b08800d588940c0003000012070026080c4514203090045034105a60414101302d182e0b2544d89010440d80b01070 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 467523543 1250 467522293 467522309
    0x40f3e07080304020301092f3c0409030e1c05071e030605011203020d02010605011b080c060c090f06040b09010f231207020a0f0813030803090601030c0e0705030412140d0c020f0307020307 82
    0x400004a03040300440c0f49e02800000d4810031855480b414050400200c80c0002da105443d0142c0c1601c04440a5007c1e49401d03510000504400c0d00708500c080d2146202010b55191985914000000c00c0303040c040e02e0300810780c0340c901e043c0c82c00040c2002400c02c80840b85450075603040400c108000d9038090b801864000c0c000e0300c2d902800324240340c000002d110b000200703081c80c0b1030380d0144844070601708014030701c6800850f03070b6200101107001401220b024510680c04240c50502410801c0d5005e004003241380000c5203860020303d00c00f98540c0003800990078104040310804114201d031840080c4120307030880d100d0b0000742084050313603540404203070515000900062021981c012241070b90400d2102071580300000f0394036480d20400381540d41c00240b1064400079584e003800501d42c20391352030a5001e410f0701d0751070526541d160b8444484103e02000098208a402d540c80741c1309180b16000b82140021049011807080c000840080c5009400c59200c42103400401c46131006070b0f8000782c89000ca030340d25 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 467524793 1250 467523543 467523619
    0x315040f020414150f0301060b0403110604030c031a1b03040f03021c030e1501031e020a05060304060507090b090102031206040f3e07080304020301092f 67
    0x107407011801514880f02820420b5440d41c0501c2564a6002000b0100100c02c1c1e814020010400301010309071059840345400a030000c01052012482405d2014503c51000c4c0402c2d00e010f98a0b0380b0300040c1035a41d07205642c0f210008001c16281040d403001142c01194030b60b054080000a81400062444082c00081c441c04540e80d48108050007802015048802c460b29880e16a07a00c201c094040c00c4c0c0310510b102c507405209003148941c0300c849421811389411920810304000d10000c40e441c42d4060040c203981c42003030107100185594440005602c21846042d000c121814102d1020704034000580211040f424144000d2030303030b6640003050760640003040e041c21009131282c80c08240180000e1404842c0d0b681803019144091016030f0603981c0240132104440707480c0e40b83d00d9210340c00e80e400d002d80c0078484108022000228004c03402561300240004e00000328030885640710300f10795280c4a101c034a804004141d000f20702c100c0c4100302400030401d44d044051403516150742d80103000030407a401600d10b10 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 467526043 1250 467524793 467524823
    0xd03030f0507050c06090f03031306020d02070c0510080f0601031d0303070c03090806010b0d0507022a040e1507080702070e070314090a0201020c100509040501150e031504 75
    0x82900324404411040c2030030400c500745000010003d6000b0880320186200742808181e00c50400182e0800304410f00002e1800d544450307604610840d8442e00980300e040d020b00c52060411010701c010410a4810079804001514183c24081150038060200c402d0211400401590414081182e60300c242e0900c1c0c00501d00e00c400306400004800800ba1901c588800300c00c200c030381034000d0b5406030400e020340c545041965803240710607600c0304240210714030504244103105c08005a0781102e9003207403035801510100c80c017848404a401071500076074181d51400700301c9440181010312031358a17052103281c09024980386043c5101140d40019000c2001c0046000000e140d8034400c1c84840b0190092402c035004d18149401c1c010013429241202d518101d60507030210b514107000140c80c0c3c0c0002d5040c0c0140414030f000c101040317134200040c42101d09000c0108071301d00152381c0d213200e414040d0509209081c9004100d03040106000148800d0703074003d81c003100204401956030300300c2c150710640c001805522080 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 467527293 1250 467526043 467526047
    0x5010f0216140a1a0306092503020a12150f082a04110a110c0607020306040b0a020d0c050301090c2f010f02041410140a0509030a0b01030f061b0e0d03 66
    0x1d6198450100300b840c1e00c1c104100013000000460182004640c04803207603c030600c49007080310400da181301e0303502072050300b001d046400398003e00002c1d5290300f8080c034100114880442640d5011120034030f180704080090000788602c01c403000141901100504580c03c51000080d42282061512448012000480e041039a90b94200e41010003403000e606031146a00d00d0040e20601c00d43e000c140c1e107400780c1c10020040341004011340e07241c06c1e0024010102900c0e2500c6502c443c800143c64620010f03020440c0e42d510301018040e21911318481ea640c1503a0358504400d034000c841c00516046c081184402411a4440182d0425102c80103116414650462803048090040800300340c003103c1d250020800145401c08408142c130803101c03e8681100c9a0040c1004079032440070f40f11504880f46060284412044c8210050204108044c04841806684c0c1d00c920944007026481149d0140045d03040301c0801116000d600c140b451080d09100340091078903005000ca0790344240e141d00801c2c10310041401d040c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 467528543 1250 467527293 467527309
    0x108030a141c090b18191509050d05180319080a2a02010f1404140d0510021c020403051207061d0622050a12090b0c060105010f021614 59
    0x980400341044124084d02e4000070710139040741d500340c1c24402400840c0c007050380800e0103410f50b011140b0a0400405507902c0030002c0b240c04e40400b650645d12044030000a0040100c0c403101e80268964036200e00703a10502c6406030f0f9140303541c6e5000340c000c00505007002050540030031000e0752044032280c851480d29001ca40440c02014850780b801c10300700684907001380200c499240c0c50300030381c0c0f02042003000b04d6050782e1540302510b01400e281000c000c00c2200840801c0e004054410040c50700303050b14040d840302840c0c000c05090418550342d0019081c0005140c04020060201d1004015800d040ca10b0700c8842e00c981b00c170300c2040695000010301504000d0711380d1151580b0310300c01c444180303405c0c01031040603030f43c0d48111041c60446202d1141c0800c101c2c00402d501900075070100c0107003003149443d650f50714402016007058041c0130751200003041c03003040380b409860815001002480c42d5807400c3c00040095041d40400c0c0c0035034205108100b8a2030f10f60103540300303444c05855060222828100496100 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 467529793 1250 467528543 467528587
    0x1e0c05030304030c1b030606051305061f020109061118030601060507060c050f0c0f1002040b0d022803090b06101706010207050a0303120605040e060103110103060e010611060108030a14 81
    0x10113010302c01004200d400e078080708c1a10b06c192008a204c2001d40c00303e208484040e50750310f50050304443c40726070440305400480960152071002007440c104036034502050710302401c0180d405c0900414036015100b500309922054010880060046504d0030001428600c54107401a1500d902c456540300741900a500f2211201224220141ea51610040144c0c98402c00188a810342c00355105400c1c0001d154020341d4143c0f5000d4050500e4291060986c0c3c00940c0810380800c00303418004500001c13070b42081c0f2050700c410303095207010403500b100b4580ba00301054003c00084c0f0a80260600e44003003584050748848117000103410b561180c4807880141c1c6000515404150320149131800401003580c0000196812a003080301489115121001c0009507a41c440e9824030741e41c040001000825020340b0341d200c00980c18100040d0680c2c84034134000440c1400d17000078010650031030f020311101108024603401080300c90095410088500750040c18034500c5450482c0f40b203004210701344c1955035550003040c8 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 467531043 1250 467529793 467529833
    0x12050a0f081e01090c020f010b1507021c08030411091003030813020303030108070906090209010206070c1103030f0c0f070f1401030225020114040f06030203041506061e0c05030304030c 81
    0x2c00c0d07035a140e411000e008140082030041c09040c80d0210100c0d0140103080100400501c0340b0794881098944640c150000f200070b99200c60515200d4a00c0501c00510720011405004a1540e07894942010361b480000d019500340103446030400c0106440f0a8034444003985e6140c94800810384406001e82d2000712000030103940344c00300000008003400001410011561050010b1003030607614180f2808070301138084038601581024001440507803107513000d440312920490100b41e07208200c3c00420325642200c1012280c40b0000911020608402c10401442002c9403004014250034000300300b2031082d8900c04c610500c00800f14101050380290181e40c14500c900c218841100a1001c400362008041003003a0302207150400f030045007409a81c2101c040e151500d80c2d5100042c0360090840c002e51005100ba6000c102211200c3d01c48181030040c403000300043d81d2225055a00039030303a58214065060900240115410b075400040c001009595002da00350411841800d1981064007814034440c1252070 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 467532293 1250 467531043 467531101
    0x10021902092e06031d0706030209060c0a0503040f0519090e0a200114030c030609060a03050f0607030501050a0608010512070305120c0d05120a0b061e0712050a0f08 72
    0xc04a03145202840c100d840d165001d100c11400321107405d100c030b14a8650010b00e90032502c0f081c032003940a0780040521440142416180400300a499414014619070880302d580002400b086500145050140907180c112003058a40f810001d144001c458144a07540e42d15454891180c050401480411840354000d4002d848544a003269002907840107102e5901182100c241d0b004038819100940388a0502c0c9905a803441e2076a100300311442e44009c22090b40082002004400038100380003035103880741854000c20203814080390240a90b04140c0041d402a04540010000c10741e1285002c0e04503036042c0c8001180d00e1031b01081ca401d11070242c00291007845a0300503e442c000f40c1e00f004207407400780b980c1601c0203a4401031084405100309100780e141050b665003c2940c1c00002c0d405200d148400400e01e52424580499822201d01181c0c516a01540c0101c0c001b070900030340d02ca442011315003e140140c90598164809803000d0708101e903580401400d04001841083c0400030340c4030348510070303070200c0c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 467533543 1250 467532293 467532361
    0x9100e0d0506180606011b08040f08030d0b15040b18150d0506040c0e01181e030302070e130f050703021c060b0306060337111002190209 60
    0x15520a02a14400f074000c12800c0c48209410000c11228001c6405030b4411802995118100358800c3e0710f910144c1d00403404100020316910441c115000500c00b0001640c0c44803820b8000c003085a0b031140b0041c0c0200d540040e6444404485400c0741c0c00c0d00c442c2046240c80d10301155030a0030591489a003617404c50000d48840c1c0d0420059005000002c0090700103001c180d55081c248000e940d0401114030100386a43d81080f000d600982005050300d050304001c6559075a02c41807000149a045da03612120300002106000b89075061107076101038820359071a4075580c100300c0307880020800400809441b5152020b416420010184400c80007180c00030050488031b00b082200300714082e5001c0d0304441c110318002c1600d8403800c010502c24410000240545075440d0056200070b040c0c40d103044102d0007480030a1100707128150300900d0b102c460707015400914400718400c0900c030a90814030111021b650085003038225030304181010f01c000580c19254030b109034a480b02080d035061004035a04542468141d100307 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 467534793 1250 467533543 467533553
    0x7060203090601170304050112020c01060e070f030603080a0c03120509030d05060d0507091a090c030f010f0e01291b060106050909060f1c12090e060609100e0d 70
    0xa18010340544050b42c680c1d9030381d40089076955020300c86040b419081880104001d43c0101d00c22000c44403400c10151178100240c0003142100c101e90048031441030f00c0300c180f001381350b400384481311014102c1c00c04108490441d181d4000380e0050114800800160f4070b10582014404c01b030002c0307180710085082c030640c1000420541c8a0f0459200440294603020029040d440c0080e5280361154001c4080e050603428140e200b0040c15802d460b5011007806c0e0b0302a0301e000d86a0800c810711658502d054507807030341000032403480d0707038001a84441841c09100c002070110821000489045985e030000e9040742c0d100d0400825041c1030325504030200100d000c90030803503800c0980b087c0c4410f0000300d0103407803a0340e80f5103030180e4041c05000328013908411a0b60008445061000f1250035450006100398652442004000d2030079990b00011904400c515042d095460381048910b8060b0824424102c0350745031075800300e5428028030050500c01e00c5480c000c590818002d4a004000642c06001c0f421041e00718208 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 467536043 1250 467534793 467534797
    0xe0613092711014a0108041124041404090c182706140709140607080f0d0501150f03150801060f03020117070c0f031e0306030201020f121b0111070602 66
    0x294075070041e15a1130601c80c21a80018014034401616030821584645d01c54403500e01c008130341186c200308200781120a84c46007594000e04608032120442ea00e078142685980e410f00b901ea1464082c90424190307200180c000003400081d01e00b0525803003000c407070383c11050010308800c14031070034952295400c0b4190020305401c00b540040c094481840f070030b86040d8a070582002e0465000002940320701e01400381d0000b1104003034a46500074801401c290054685150036480210502c254190000b80c80348005e020380a802c1c0100380003041d480d414403014001400d403140c44201d250425070743d281c00030001d0110700c0c00107020b405000001c00803641c560181c182c2001250000386e0100e800380c40d842103400d0f0807000c800c2c46203546a4402e9040407041c0c0e503500f640048407104605006c07050300c00c04282d030484e140103c1030307140903074011541c42d18600029040c02c10500b120043d03030b0480c101c42d407241c1302c8240842d80c401e0a070309407001100000c0703074105005006041580d140e132400002c2c40710600500c4d0f00 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 467537293 1250 467536043 467536127
    0x31308070c0905090c01020a0c0b0711040203010f032001080402060a03022218051302190308030c030a0b060316181e080c06040f0909030e061309271101 67
    0x10817552064020300059036070f0440410b000305428103000090006525807409004110311503500b0500c0c0034028400036090340c109810034000000d00207420407d10107441d0750041c2c50b40508008100240542000070304018000344041c1c000c250000b03110072420b00ca90f04070365414008800030040034984004544542d601c40c450744000007102c01c40804554034a101c2c0c140200c0e041c4800000140c200d5003406481c066612030403920030850100000410031440c000c41c41031400d0b85481d40c0d2450002c2d03500f400c4444441205005401c28802c209162108407004441881c040c24401b06003912810384009154071a0003121600404000300c4542490380b240c11801da4001c4030a490002d8410030501c030b50b6000f00c0c81090350782840900108000d01c41d0b070740b05a040c0c03400b1345080003102030307036501080442e440554507040e4010503040403c004c0030103100e007054070040306e280e07030f0520007c80303200d1446054a0030002c0c10038813a90112080682c0640c1080c0d02540f00d050001142c902c20741411071140e040d01d0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 467538543 1250 467537293 467537311
    0xa0504050a0c0210060e040f0503070c0b040f0f050105180319060e06090105070504271d0c0603070903201002070f080601030803180c0a080102220b031308070c0905 72
    0x404c50101e540050040780f00fa103650001e49512a40d641c1c030352904035407420034143d46070302042041c40c0109105541d41806011448519681e843c03400c10f0f042c494000b50b13402a040c6203006442401141c0e0702100f116981041401030890985401000030f00b000354110074601c41c51030070407451003000078980040800320b10000540e0815520050620300780c903001c4440360001101000140a480348001c1c0b400c5d503420708800c10303500319480c01c80c1c50400c0b00c070403e0401c841d14604803440301151604002c56600000291016411800d0001010344940134034000100205400c1c01d00d0b4004801c107802e101f50f010001001080a1200018065182c9086000e4026920728003200420b11450000c4c44038102e0394400c982c0e034074541e203e540761a401400450050b2540c0241200406141c0d02e4880410190040750001a0340d9042004e824111400032002c4a001e2035041030104031040c0d48509070780c2d000109105110302c000d52440c1400c0e06e48184200104100c900c030b407001c507640c00240e000c00d2180d0fa00c6 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 467539793 1250 467538543 467538553
    0xa0306150309060b041b0f0207080601030b010510020c030c0d030201150e0f07030912200a06150807080a060509120403080405040623040c02030409060e070f0c0b0601030b0a0504050a0c02 82
    0x2c513041c0001d80b01c5010016601c1c90200e8000245240303d200c0070130781140c0b43d10680700d44541707844000d800d000080c0d00513136072402c0c40303401400b0038a8029814030380421a400181114041b050120303844001c19680c680c8100c0c0e1280a02040c50300039007152001d6542a45201e920307507203411005480c940260f034041c1200d811980012243c50103403058038011900403840a5410035004011074500380198201040410800b01c29003004100700031000503a03100e44804036030219030070340252445800e644010210f81c00032100300010f80003c0340146403d81c2003c40481d0b160340700ca580929106000d100440400c0c0001000410302c2942d502610545004940620005035100c01c1c004184031120000344102c940080480401e2030558080140c040303c80c010340c3d04046c0c1c2c400b103500850740164007000e41340c40f0200410500301d5220b070014420740305a0912101707055180d01d91106440c3c0080c5100c0c107242c1c1e200700034500c990700c0d401110700810b0010414070091030580035010281c119004980058821 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 467541043 1250 467539793 467539811
    0x14190201060e010602060f06040227040f110405090a140108070305010b1e1318060b1f1d0a0512030a08010b1801120908070c060f0206010b0406050a030615030906 71
    0xc00642e54100c6440303500510355a1242c80190445401c0544507641c4554208145c540c0c4412000d000290400c10150100d0000d201c074003880240e40751090701c0d490a41c0741486600014260000f95000c3c0c0b1401e1320121143c2d55488002802400c10480400c1104500310002178440f0b00041ca0034140c80c0700e8002404294485024081c0d14400e040e9824044890303119098000e04020000325110042c096000c40d00b4984038010b200c402c840e0b54802d8030465160b1408450b2414429407900300300f80b04211a0a06182030000100849060708510040141203440082ca594500011401402c4028128007400135000315695607076001140380e2001c940940d00000346c0c0d50b03614080d52401c01400c0342c0184c079100c0b54001181c2c1c40030004508020203580700c41141c08200c081d00601516803081401c0c251441c10304030040e0039412502414801c541c082e1005001d200703501000d96048900c241049501d510340014140d01403c402e4020041c004001e40644003480d071700d90802d03141c0c80e025100c02c10a60348 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 467542293 1250 467541043 467541059
    0x41d0a0302010f0606080a18021012050f0402061c061d04050c030703080409111308030a02061609120f050114061005070503041a04030804080303160302120402101419020106 76
    0x1006200307031000319106c1070020f04203070703015000f801c804103014505441480d525800600c43d82d060300c0c0b014001400300d2841640441c15440742c960800700b4000404011b260990002c0c03141e1056a1901618508e00380170000d418620b5003110f4098040700307160640031400000031010f450403ca4080e2010b100c0c1c0302010750142008200395098a41103640c20f482c2a041440d02000790003c2460720309000020080352105104c0c01021001401c8200c01a503561520020007c6c504100601000405141800c08001c04c42d00582081c0c110713130704809419009c13040d504050262072403d800241c0301e9400d06070901c1c0360007075410b011380c41050203c400c1d20f0100e10901c412120750060314401410b42e0320400081c403001134207411520350081d085008600e419200e42d6407110316005170348140010b6001001b4000300040c010911920025649000c46c02c050301d00701074104050000e0006070080d40a10320305030116200f14120751043c010840400d0783d6008860740d48014172a060140700041d4a4488049485c03c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 467543543 1250 467542293 467542301
    0x50105040f0c050d0b420312042102010c0206031006081308042d06210b0607120e1905181b0a03180303050f0903030601050a0e041d0a0302010f 63
    0x242d0081c4880035030b40c0c1c074400e896281403aa2030307400c440301c40c06d004280640143c2001e1a00314141d045448102d903001142450f24041c59040c040c554181d090100384180c41009014002c00c1040c170441e4240740c0ea582c00182c440d10b0005a011750051400401c100b025103081501e482114070396560b419030742c0c1d01c1199884042d1400c600c020901c0c2e40420041100c600300c1400e100301104e501d0b4009501011102c81e190813844958404008140a0080d400032500050110401d5143c2d407003040c03000400910002e410741c80303010300040c000281400c620032010311508031107101a0b130181c00e48484a45400c2d106440745218814584661642a50011580c03145218580665400900318403030359540342002c401070b04881c20741010103543da083e490030403104103032034040c031806501c0000d9241826201c6010700200100110301c264010000d020031070340d110044482081c1030303141800301e104c0c1000009002d4038402041d4070f40440044a0b00154007800b10b40d44400d144660000c11400314440034038001d031 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 467544793 1250 467543543 467543569
    0x120906070203090918190c0e0402060d0f060f170f030a050a110f011b110f10020703030b0402070c180606140c102a080103020f0d02030a050105040f0c05 67
    0x1a0828003490086003080404c43d5046a030320700c0030441c2500d013501e0103881d0030041c070b484060a40c46c0d00c010342c06100144111002600d00110b0324400b505c1c042e0007040c40d5200310f6101c4550682c0c0d402e2100f07008001944040064120f1103080c04090b9540d086d01c0f6160141041200d40e24040c1001507202c050b800421989240c3d07444c3c0f5a9801c0180c01402956071110f401c10364000d900402e60b44484070300c020b124000c001840200300b0b42a442c460500100013050206090703625070301074110440c01030b6000171106070701e2080c520096500c000354501140504440040d16170014004240383c1c08000c00681000d041e6699099004c0322415600c00e150162507007485410003007254041c07145450403040c0004c09280090204803543c0d01102c00b4284219404000e440355800203261640ca0203440e015400c0d080e21520340342020495045800140165506207620382c1b24004201d801030440d02c09004050256401c00001c001d40e24150030a1164000c0b49481140c48052240300401c80f450403140301103003 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 467546043 1250 467544793 467544797
    0x3090102121c0504031101111b0a0b0103110a030f080702031203040c050d0602220e011208030105060a140a020610050414070e040608010608250b0d0213030c0b12090607 74
    0x88000b58120400040c10042c0003a400c11010400da04001c020900400b0700710000c6102031903880704607030110107619070b45010301718080c1c0001c510342022919803d2641c2c15a0f800640003442c10100200007480c14105a000a03c283d5441c001102071100410282203030034000c1c0d003a00e20440b004c450000440c032041724000c2c556403d40100748020b00f0088900715891784696001460002d0400140403e000c0c003480104009190302001d01041d943c8210f0a40145441d01511000d4112030344e5001035408140545400f416010900348030542c4950542c4a5420640155680e00ea120b00c10094551004640007010003401c0d01c00040c840c182407241d036203410804800c2d8006500c5201003150301d2036214100c0f640c005c0e2100b0020400c940207204810013412070038000c00041100c1089020601038460103580c00e0010460100f2461031540100c912010460900595410305401c00c2042d0b008107400c0584143c8503241c020030400400802012541598079568101c3d644605c2c2060351442d04880c5000 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 467547293 1250 467546043 467546077
    0x18180309102a060207020117060a031b1a0a020609030405220608070602010b150c070302091305010203010e061f0e0139030f02070e0c07050f0601080309010212 70
    0x14202e21502d80b4603a000b11011a05000380c0203401030641c48641000e0a0300c459500142807021580c01201c503240800045000c9100b9113000000504d0869181c0320203008500c0122242810781032029032007002d08940ca0460840c0c1c002c9091503402504401f0302c2d10058801c0344041100c8030380c00000d480c04c50300020310f508909128000d03210301d503800c03184400390025252400850104020300004001d04615400000c0103501c2c003040050351083c1c014402e100040821400d8454600070900c80203aa8054a00251540380c1c040c642c01806258000a004c0d07501c00301c00841d83d0307240c1a04450182200b1195905544603186001e8800403a80c090780c40440d02d000000200c0c0c0d40507423019400802c4c80c1901c0c0740380895050751800c2c0d00c10b002a0a07040000640084000c164100e00c5a40b0b0841c4a40f004060351030034000c0d45650301001078079506001201041650801c4020082c9140c43c4400d04152242944d6440b220b50b9281c1101c40c06c14003501901010300c811140440650f000d10000c192004 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 467548543 1250 467547293 467547319
    0xc05070311010e12010f200a08062b0c050108090c19180204030c0e0f01060c210206010e010b16060b0103060b030408070b011202030c10090518180309 66
    0x4107240e00304070481414401c201c00f0a0303800c1e81e13074194140f0300001c000c1300108000e80413165000480d000440000301700490303080320895680031003055800300f40481c2403200080e1500300c0021000b030019a06001506c00b20b022500d052242d8482c210403d0348902d010201980d140c4006440c0300310100d40c40308040e0b000210740781151816146105541c03220068501e802138480c070fa00e820760590f0050341d41030240c001408000700802c428030364008007605c0e660b8040c40d0501d031910781c640c0001131040d40100030b5013421110a001d03455054030f143c003c2000c0418012902404041d4076400c0c240b150301c00315498070000013074200d0302c0e00448802400d00e804480c1441025603400307000300601100d007810540e6506001c10b6514007440114000c50181c000241c881c0400d18090b00c11150580103090903481da03c81b004010b03200041d6200c9404002c42c0e4a214a0050400880d00c890745548102d50146441000c42503182d01071050602074800c0c0c1c4403802050391300e400380d2075491003104011504488022412 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 467549793 1250 467548543 467548553
    0x10f020a0b3c01080304230f0a0e0402090a0501060c0803130b090a05010c1e030209030c090a0e010b0a05030a02150d05010f080f010903140c030c0604030302040f060c050703 76
    0x41c80d484580c0028081030412204000c80c0c0002080750007020709001003107455003204484140714010b040c6180110310382030a20b030300d20308070000c0300f082620b01118440052240d50399006025502c4003015217440c103800eaa584108082400c00c0c0d505a000e061500c0100d043c001c22401218181c8070a41c036030380f44180765aa9140880c0e0700081007030803040001041e00d00083c0c1070904003801110410020080e04446090031401c40c5c030240d00041c240001e0b101841c5e100100c000144c0c40907180c50800580741d210250100703007001d10b655600d5a00084800030095000c005612010b548800000208044446030040c4403c081c5180a600d40c194061000000146488900016a01e2042d0215400c00810b0100782c000c2c1c0ea42a0062420320308420414025500c0400250043c10181c030028001303e00c1d04d89020786500305900c00c04282040008a00100d01e02c1007048905144a600071280707240b409040c0200290864000c0034504a1404030000341d0313500c07a4034500b0101750020084e0050910b13550b030b0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 467551043 1250 467549793 467549813
    0x110a1206150f1e020a0b0108060f06040b060d050a3e030408160c03060e03120406020c1204030c14120d03050a060302030a0b040311010618050402031f0204050f010f020a 74
    0x6650400c20968030210702001d0f01c0103c0703800d070600d6800070909600705280c003141942d01600820070550200c0e0810030ba607442c10300ca00380c001e081039900040004a081c0400c00c103100f41d02031309242031b05060038803207041c42c01d912442400c14012080299001038141c2e10000c01c0540c5088034810603070050940720704000c0c0000b140c00603c180c40b401c1c40e0035108a50202408500801a03844000070b030410030038046540102c400311031401001c0c0d46810b8241c8a00c5407005030250016200650104000303185c8c0c142003100500f000c08240d4542d403141d60743e26000305001c00c180510f66050340c200404007018200b9001403005c00c032818003c2e1510345504081100182002481021069201c40c00080581c030144000ca403024054288482d443c50a41806400300918510140c40d903071428208005414140081c001910301111002c1303a5500c86000280c901880e681018860002342c0540d06041415540201308540055420030004181e00700151900704d0105544000f43c1c221540542c001500300304 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 467552293 1250 467551043 467551067
    0x30a020919030803010806060904021f021015050a080115030f050111030a020702040614011202030c040801020a0203040f05061804020c0109051204080c10170a0609110a120615 77
    0x21001c60242620411410605510607146080000010700503003806011582c1d00c0b0720207840003002400d082d408105002000c0c41194070407071a21411340500780c420300480d03000c4201c184050001311990036034032950300203501c250352260301c00080020701120123004041400742514040410507107582c03031740004802c1c01030b000c407125503075224607235010a0030304051805501030400050711031050b0320601040f039009800143d0061502203100d00c80d40c7c0d00507030026103035500038005038680d20f5810010345c2e14040d5401850480d40042282d2060950020180080b118a21072500322180e550b02409003610540c10245002c081a800032006420329400601c0004c1090000150a0415485442c14502007441e8150b030b03603400080c2000b078a202002a8a00454200e0300d070401c0c1161a070020300040c407d580510341d400c03074481c0014146a01688200010184500b0902030b00840502440e80355004411280202d5801c940714510394059114070001c2e1802403408107401107010308141ca00c145420 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 467553543 1250 467552293 467552299
    0xa06060504060f0e0603040803010e310f050d080601091406040506072a0f05031c08061903050a15021303030e131e05070f0207030618050a1101180b030a0209 69
    0x41e134641c0c41c5490340740c000c600ca24040c0c1111070f20707541000510301e201207002d0300d95444013a511160b650b000c5105c41209220301c800851540c0c0c941880d180c200c144a4004201910034024111800c081d02d810000c0144502e0013640c400100980701c0303101c0e05041103000703001c540002040c00288900e0901a0041c40480c0c010301c40b01c09c0c140e00707c11501d014000c10013038117003501c4140201041a81007500c01c650240004401520309068046051480012100d140404100b45100451019201c80c1c03e21040b07642c500b401ca02c0803640304e0a0040e40d50400300021207540710340c1c010a40004907a8801c0d1000d0300003280c01c1490b02440c40c0c6040303440c00c507d603204503880030309540880005000752107020004c0c0003051044640003401c82658007101c100078001c4050242840701026010303400708085082d254860000520342950491700c5401c1c000340c5600501c01d00c16902e0301020711521034007404051109a0329101202030701c0010b20030590280c406c99441103024004900030200390f4016002030513000d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 467554793 1250 467553543 467553557
    0x305060c0921010b1e03030304022e03270b040201030f0204090f06050307140a1208040905240f0a03060e0109020d0f0c0b031014030a06230a06060504060f 68
    0x40400c90404141000b490349039699180d0041a19080019108125076200b0440d20094420100480e44902c0000c1000384140306d07014907030880785c60400c1c171045003c5d01d030103281480c14001c80015000706105060700140c0119030009000c6c0c0c07a40c00001c0322529500044d901260380782c50b40150060b044580200d04419000e21002c2070780ba2851064070303202c0d1220503001c11203d00d4401458142a6035800c04062f40004141d0b40300252242000c1c0c40840329107406050488101e8280311200b80150f0300180f1040d424041444054200ba0354902e54030241c40716801c0e1070b1440c103810400b16039110010103800000032401040855600d6010451166450001240d1002c0d11350019030b100e01082d9088660380c942e0403004041c01003032803650f400750072040e4040c1e04d07505040f0003095803214a80f14085040c0700040d5124415102800071001d4681e00190520240416149124110400c42c0038450038405405c0004c040b00030310f00035001118480d0321414a0700e400c100c0c08403220411005030710240220 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 467556043 1250 467554793 467554819
    0x60e0603091c090302010924110a02090c0c0c0d110f010306080d05030712020a1d043c02030f0f040206041508060a1d161101091203050c03010305060c09 67
    0x42c01c0115044125aa603507807800c2d040d0704c00500306101c1e54002d01c1580c140040e040c0d906440144a00b04024210f0070250940c141c1081480d1810301e0300c0c00000e400c0070152062008403621080500b04071040701c0141c0d03581ca40b08a00707005885c4021500a00054a5038021410314200840310154107003040c540492003075110201c0070319203800060a000054000410030003c154032600380203003011690010743c500460541d00900c18124100d900ca0780b00420740103c1143e6466600c040700d03410006255107468000c2110f203108110541a8900d00740305041910100b0030114801c0780c0c8568411140b800054030303461442c00c1e402d1002041242c00003c1080b02241c2d54240c2d020390440c8140650390b41c0c040386000820301c900d6204d180d1100308110800c03000041c0b0a40041d100c00c1e40106c40c2c1100911031540c0050840d52460040d500003519441c0caa46c400901900b01042070300c1621a403401d020f50746540e46e20f00c0f1184424800a0050703003000780412000031601005288080006045080c1020 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 467557293 1250 467556043 467556073
    0x603090f060f0702070806090a0b0c0c0f0f07061b141207062a1d03030409060b030405070b07051b03100c0206061206090c04090c0f030327060e060309 66
    0x2801d542e0304000c0c1d8140303030411104550401000003d00581409824141000c0d400555a2240d00078000d01030317502180000c80035419402074a03101000300703080700c40c0f00d5650701c0d001c0d4480101c0148503200e030181e1071010032128010b03200000001c81d580c000c0d42c80030b08141c86113025040b411504508074011003480c1e006c060b4043c1c01030303c1860700800000902424003c4080c00304610f00c3c171020301010399200d482e02010740043c98030a045c01d5001004e10a50004000282035100e1030304200a0300d8035010300440c030041d1440242d4403a030321030000c44100d1910350019240a009004009120b80d00030b1420700d21a149034105200480000b50403114800c0d100d174408015600b07034542c8200160f000e0000c0001a29125507480c007038061140241174241416806540c40300c181015440c01036843c1d20044041059441e6020001c09030300748a01070f42d540301e280c000c002620b80f8000380300c6400c08414520340c201c400c1c4102412905c0b651070b904417a6461905011803504020040040f50143c0944060880 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 467558543 1250 467557293 467557303
    0x20f090d1b0603060608040b06150c070906050307051c030e0406180b0108040804091802090403030605090903040503070e041b0308090102010c0305060307061103071e060c0507050c0603090f 83
    0x14814407200c0d91034402029103110844a950159080501344001000410340001406400a401a204d0002c1c0e903039074004103800c11071812620694940000700400b010790003069590961328100d9007070004680c0c50003015907880060048540c0088000f1440b071903142e450b900c049409210342800340340c40000400090498050b41e10450a000700711845d5540d01c8024031600c44801c40900f8800d030306052030303202d10900e0700445c02030302c41f034a07501c4141ea82d08100b604480a500e40d030082160f01d00703240c1490014080c0440348500c5015000d010f011907504c46c0c012040d038003511805001031524a18080301401c0c8480c010344140ca0003052409003443ca42d502c00d90860295003e240603507601c1c031825000908451003819408101481e01c070502c4456034000c0703501000c541140c541070600d011294582d90451044080050904020070b00c0e242070081c08108442c00b8038098001000b50401132241a2020f100e0004003d05940183c1804000f41ca010000781da0008000c00884501a02d141d280503e01 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 467559793 1250 467558543 467558569
    0x2031905070c0c051009051002010f090f030f02071206050606090607030305060f040905060610110601030b090d09080319020c061602090a09020a030f02180f040c08010e0709020f09 79
    0xc2d800e0507206040c07000301e15901009020540e030f401c4035080e65007402000c0704206d0080130700c03c002d41144e0324842071003504000c40c00d21070200100a030203040e1030100d410700304560046011900c44410841c0e094004030b50340c1c0c12590607180f80b164090310380c3d4501e4010300c0001c040640c006000c0c002d031780b140d803a800007400c016442920005983c1c1082c01c100b020b0701d100401340c58400c5040c04d043c0000107201103182900200142c45044441c20300c00815100b81c1d101400c803501d1846201d0001091084100400740a101c815050b641c9907000c2c650f04403501c500c6401149280e80c4100a600d0001c19a40844000107180e881541d002214500000350641d100d820700e61044140344403000e06610300030740c0c0a42c000c1560081045050380c9540820000311013448090300b02e40c19800d8203000d64869984000050f108000d14000c0703460940603001e5400c8095030140c840024070707600401d400205108180300000d00381c0041c5001803030b02484034085c0d03004103028111144203005445098035000000e400b5 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 467561043 1250 467559793 467559797
    0x12032d04080a06050105030c030a030813170d1404030f080403140a090807080a0c0e130b10030b06190b070602070c06081f030b07201507030c0806130203190507 70
    0x344040e6030400da0150b44c41a00850310980200c0c1401c000780e94000391007d131050b0305040200441c0d0710229114684c007500240a4411990400139a00c00044d180050480300d1180c00100600812a00008070110003100c00a003c02c071141ca030002c17528080d54078181c4c4035119141980c01c0d81c4c103030304031201c07140c00c000c00740408900300ca041441041c405010010140280600400d600c920075100c950035210944a111129100e500c0400c0300c01202e20a52142c0a0304a0310001d07035420010300c0c0b0701081140f0311040e6941140c900104c2c0300c500c0c0080035910980200e400010b403140c10b11448413a65031028204481f80b80d420004600000c004e482c800000b03282c51749904d010303482d0a0820b600c03d548141c0a0328050307070800501340002500c0304200c45d0000342c0e924083c40452400a00142461454448541c8521404990088203080c50240521425160350284030b01d41e211181501c0c0f000040d14120b034420702c104590f40c4040c00c140c0c061a130244a0f864000f00c5064002d120200b1500c0950794000 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 467562293 1250 467561043 467561053
    0xd0f0e0f010c0249051305090f0c030c16050106050a0e010b0301060e0a1e06030b0a03031e02010207020909030a141812013812032d0408 60
    0xc4040c0203100784450464203002410000388450314644101c03049202d0342c0703140c0d581e541c9011101841000855880b07030100c503801800b04200c050151140d0030102c410031103001c8521000c01c1c83d003041751102d130203080c21140910701512041c054803515007004002c02d102103070511036940300504900084054a001d40c00001c0c4950920090040c0982107400034440100b100c00100820f040450481341103442d245050001101200700180310746130113030300c000c1d5180701c0890079518011400e119482107a40300e480c104080c004800034030400494910020740405d03a0001c0c02c2d0700358602c85801c0d01c01442da910005141240e90f5000403400a000e403103600d03641c0d001123803443c035141d0415480c001400c5140b0f011414450070455a060740a20245032602501583c141d80503804402d4001e0900d0050001c2e0315800c510184002c101e1a03d803010f40200214400a100403090401e040400c42d2081c035072000d1494441420300d088a81d50000100c0e1141a00c0424503001c528640d5003d0300142503c44040c1c1 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 467563543 1250 467562293 467562313
    0xc030a0f05130f090b010c023a0308160306061d060409050103200405061e0d0606060201021e0405090103081803030f09130e0d120b06160b0c0703080c0d0f0e 69
    0x10040310203540c5c865040c80b051903614005030340c494061040040070340450301c12014414844003c49426030031010402e10821491b00101074202d41103d02c03412702c030305da8000d4410484404400303856151250a0200b5840c5000300f103034500c01000d00c0a030400140c5591714282c0d1319402c000403281c0980c01560300340100007003810300c049418140007550008540501c41e0341455000038034004214203074500d103000b200b400f0b5182a00d4811041c80ba072a00103000700810366840074081d011398008844000414101c0d807094800c985543c040d9025514081c06203030075a0b08680e2041c0041d8440300384481c0640c000145031089540c1000100391103c0c101110310340b80c12215041c81158102c1910055940f41001b624140c0858002252041c07070a580c505004040110385041c2c4c010400007210f01e800540001f0380303030709090300030068140c40f5105182054855031425040261400b882a0003400100c0100208406644030760103400402004040042e1001c9410150350465014403100001ca4000d540d01d0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 467564793 1250 467563543 467563559
    0x1092d151e090803040b07030315091b021204090e0f0607030b121c030b01032304050d020d090b070311030304061a06090d02090403020a0210050408010b060c030a0f05130f 75
    0x412001c0c1c060b08003084054140900e00b41c5a010354002c0c004508404151401858402c0d00094041c18102c21132650701612010010081c010748080034000000340c01c2c0d455505480011311000310f0400c1c4881504107401c203000e11014201d0700c2810310b054410100c840e0b4012100b4440580100b00c9500c00080c00e174030100034046c283d15101c21001441d0000e00c0c0d0104080c4084911642900d0146000114191440010380c001c010200c4441d69210031b514401c4d0030480c5401107640200e001c2c0044132118496020708a90760140102140009600c0d01010420012402c0180c18223900c0390820040204c0c8405000c0e207540c104880c1600c83c030381c4500905c0c43c03803520350060140551080d80c856291803019004551081d0b20408002d0040e14080f0004050600c2440004259903005001e10808241900000d1444c0c005010b45502946003900e01229850310004840301120690040c50901c0000364041e56076014001c10402071113020444209403828071000701c0c0107000018120b80e0814200343c28 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 467566043 1250 467564793 467564837
    0x1060e040501090c050d1e092006090a29030c0d110a020a1e0501020304080304030e010305070843090905130209090a021005070302060601092d15 64
    0x8000c0f054502001e0f8010385034000100c0c3c01104c00d90701c011440c003c0c030b064020315188844500c0f032a00313407800110200f040f06a05501ea0184e40d0703405520700c0c0000b6101000034610039000b10310b5100000f0002040007070200c51030b02c108003040460544600c1c04804e040c005540c030403903454071101000030300c8003094011807040d490000c0446849908001142002035034825040d0b030080c065802020103814825420403811340b5055100e4025900da06040c6031010035a00b00395000c40124518804a4550307500c207200d090b211b03031750517940d1040d5911080070340c807030440f18070848400e210304001c1441030301a034402980201501051144050f4110184002c10080c2160002c1010038104001e01c6103c2030000d006071803003601154500e9003900d400705441c0c903040380800d0094020100d41c100082558008000e020a940a50261001c0780c1d5603000440d1208290300030f40c503803001d2010000341400c002d1a45000910081d1084104a45d00c0b40d54000072409600c890300005022054680303000051001 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 467567293 1250 467566043 467566049
    0x30b090703051006140702030714130b030a1e0204141801020913022b0506100305090d080a0b0904050115060906020c09070e0d05070501030509030c03090d030e030601060e040501 78
    0x58100700a0070580c0390f4070603040c02486907108202103e90202850750090040700c41c4294000c0c21120396583d1241070b0040400c444800034402c00183c0200c0805c0c00aa01a8070b4200300010043c04c00c011b2540c1da805420b0b0300c0c08039070440380c0707031000e00380c0f0016101d41c800c03503d0150310401600c035030340f812052030650410390f003121702070301c0e401803000100e00e444081107110115088000561200c2d00058400ca1316880120550b0480a00f0801c8500c02c0403580d104c070b805904281c90500c0720101c441c40903400e43d40c00b515500b05540c000d00710241040d205150080e045141c21002207071074282000080c400d04410340b0300b507465940d645002d17090600001d00001c0284101d06089c2046450a81c02a458482c0c102c0030a01800103400003440c003034420540011132410082c01414210880e0804541c0c521440c000c803408207181c00c0111f000c0c0040042a502e201d11004010351a003d1a0740501c005480b0302d401c100c040c06140c0f82001c80c659000e0100c14041c185980e18440e204001104000a58406034 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 467568543 1250 467567293 467567297
    0x50105060f060c0a1401020f0d060302010f0305070807031a0604031401051303080103031206150e0f04110412210f0e010c0c090b010c0501022214240705070303030b0907 74
    0x5041144440841e2070051390f41c1140b04680c8940b45109041c1c060f00c1046a400a003044c0002d895407100642c0c2d0081042d28001c1e41c810f8059402500180c1c1190b50a54020000c03441000000c0e01a600c00e800841c44056945103202c0d80445480c00300d4032640094008403000010405c8004011344244106076001300f00407004001d00d071558070094030080c4180405410030500d2030004000490a4010800401e01034440c594054202d241c010300d407030200c1c10100d11803003032414111440c1c03500f8081c2a521084600405240c81d2619050800b0342da0342c42022100f20060300b001c154403425441100040514549820300326200c4194000e0030661840083da052089009541020138200e260300c405559480c13078005890002500181d80800810718018400d6000085a807440c01400f4030f11031200d444a1904030703000d6254417161044404076003480307401c0301c00180350701c01c2c0001a80d01002e452040d1055180380502035190213080c000c0076001a80842d440d0210305201b410f000816507440140c074 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 467569793 1250 467568543 467568547
    0x210020c1906090506070c0f032a180b04090b04030c020a15051b0a170c01060b030c0d0b13180b06030a11120c0a09050a050702030421030306050409050105060f06 71
    0x10300071025038014580201d0021030406d0810041416a802800c40c030070310b5401c060750302d02d040080380040603618680d6a03040c9008140b410300c2c040d0083c040e51483e0704141040301d0740018070402052a8502103901503101d80c400d401140b01c2c03d4069010b90701aa4510000e0001030060145d80032103a4044611011400d650f6a1041e6100c01a04d40201d83c1200c1a4a000080d80c0c1042c07a090880360050145440882c05440d00409000240480c0303901000034032606682d07014054003400b0848d43c9a0340c17460100a125103001a607401349204000040c022500c1404908620044a04560620840d0728207003c41000380030801c101980d02a00880007082d03081c1c03c0d40c0e20300407842060300003d0300903100421805801c10050020320b00740030340034115902c66a51050840040d010940c1c9001d801d6151030081038503903201104850944a150180c40742d444600d50b540d86034900c1d04101a030802d03603600b101041641c3c8034007a00d00740c1c1d4020320010402e418a1010401076208040d1454420501 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 467571043 1250 467569793 467569799
    0x10e0a080f09060405041805061608010504150e040804060806090727090207080306090714030f070309060212070917100e030912061e010f05040203040201020a0210020c19 75
    0x11800480c0c0768907441d400361645860b0b1100128810b4011030b08031035070003030910172140350002d00c0c0000100090f0049003200c141e42c50b1300407a4140548425061400140550014802c50030290000d0101c030446030740c03484005a0b1402c0c1c50512900c1950111904000003d080049940c030007200c9822203401c540d00c0303901d4142010f01900210640182e542c8003149040303000f650400c20109407000b442962025562901c1038601041c181d032003240e209108003030b0f106c04540d045203d001000c0350044103c580f54a141c4401090350002100284200101519048418005665130015049694440003000780d0b0341001d840150000d00103402141e40146a4003256078026800640444e0180f07260328009103d03134050948074110b1160014803a00011840b645007400c0400090540c8902d041900da40398189030301d00941c080744000e01c140c841c8141d0200041c8400c6c50240d00450f0814414011580001c4955001c2901d400c00d980030340e401341e00100b0b0b00005a00b418200d403581424038514171030340303241 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 467572293 1250 467571043 467571053
    0xc0203120604090c031209170c030a020d0f051e011a010504090903020c06071406160906030c12090b1005040b0616032d030b0f0307050909160b0a02010e0a 68
    0x20003000c181c0300b00c0e00c80d0094014420241400000381d80c100030404500d00b01c201d0064080e141034401c5d091941d840035203020381c40c94081814401d508005000d401844c0b074540030030503c101d00700e00a071141052807501c000026010000c2d25210f54103148a08503c400c1c0130803050858100b07500c400320602c400480380000e0b07a8408225002e80340032013400a882001c6040c101e2820181d005095086100004c2c900140000928194050700b540c0301210300c5a43c0300c0010101c8501d00301510008281c012340148042400303504080c0000c1400d00d400c20142c18456030420230b4803a00c010030f5030302d013180764140003000d010303500c0f5440600700c10b55090103d148a50081641c5e84250b0080c4600368001c450010205132094907140903205955540344940400e2510403a611040c0058000129203001804046030802003d50400301c4d01c0100074110a1346000c040c802054002403181606019048a0441542c28103038000d0180c04c1c076405064403114581e00203800c481c0d17165264032281e4401100c00d03000803 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 467573543 1250 467572293 467572327
    0x1121a060a03171c0b120a0f080706140a0e0c0319150603020a06020f100605030c04050a022205100206010b03070c0c0b0409240b04050f030703060c0908010c0203 71
    0x2076210f50056900954040404007a000d4070581040d031400000c00746485806980101000b20030031120600500b0080101542e14078040e0ba00a00000e080414000410048005000224040ca00105107900399028104500200711004215565580e030711042c4694100041c10390480240c0040400040803400403c000c3c1120f9802007815291480c0321089a80c1c50308882c00031580a020b000c001621001d0103911122003c42d4400c5520403001484207100c4c0ca170081204a50028000c2d2114000d0744044c00080c00000301200d007501c1d000c2005800c00e03038480040000d080d12020000d170703449080c001040b426000020204045620050051180d2841003003102e03001641d90401c1c0001d00307414549500e03002c81c940d002c581c40040100700010810220340224400c1e0000b44000342000f000a03007001d0b82c40559000340050000180720500c01350415824042e6003200003012500318a41c0d80c0da403a4144d9aa154200d0700054541004009042e000d0040c8840c10342c1c14006141464004c4441401003 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 467574793 1250 467573543 467573549
    0x1120206090f0904051f02031e070e060c030703031b0509090709050a090209011b0305040501030213030b0403020a0b0c07030f0806130c020615040b0f151201121a060a 73
    0x360400040714042959500e0261907554409042c540c000c0ca002d041c1030b034946c800420414824840c02c3c1c154585115107108481c0300d14106000300008480c200001c050301140106100144810780384200026a11700b0050510500c0d0000150340d06c01c01490010261003011031900e03d04c0c4090000c2d20011500242039500c21402551800001d41d100042101e501c011036200302c0d0803194031280443d0031062030300102581e142c01c1e2140800650410400740b001d66800401800080041c8414440b944c1300e90010034098103801845040e05443e40c481c40c1296100b0345040b00542d000c1e038807050801210340b000e01e9015161148250420016403006417034408030101c51400c000c0c01700d00141055a808900e0302003203280a10410840481400c0a55100c01c280ca401180b03130340c03004049255103440c0c060000000c0c4050302564000721107400b8494141c4400d500a070800c01c0a11201c20b1290529429600900e684071915200601500f018004071103000203018410a0350020000240c0715258544d0072 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 467576043 1250 467574793 467574799
    0x160f0e0402060921071a1204030e0111100203330103110d0c020706120c021c020109020d0303060603050c0a1d1201091406010915030305070c0f030605041a011202 71
    0x5030b515410005600050078441c00303164440c0c00044a011403030002000006ea4554021610540c0001051b40546025011660100703608550004000034403407003e40f80c924606052416480a21500080c1041102e0b109035919a42c040304029031110b01c10205ca40300e07080f541b80084901141c2006902040c940240e4505042d00c0d0401c281aa0104004a902e224011036013088584604d040080d2074034020702c030b16400688061b98136002c2104502c46c0780310100c81c43c0c004203882071403180c40e01d8020303814803912400d5560354080d00015031200f03081da0500b0b43c440c1c0d4002400e1824075001604490014240c80e50050040c0036038039445801c50380106071a0f41903030f1007180f0320814034001094181c8401c400d18895080451860070490021070b4062402c00c44815542d19070b80702d0480344100c1e9100e01150005550781501040401e008000a08455000301c4800c2596921035840402900b03040c0d00880b200d42e17460081106020020000b0b0703600c0b8000490000305035140c040114a18074408034040d00c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 467577293 1250 467576043 467576047
    0xd05270a031403130305060402030c060c0a020409080d0509030309010e011811041d0a02010e0d0507120804080102040f090e0105010308040b130f080c0310090201050d09060f0e160f0e040206 83
    0x40c07148802c0042c0d5401342496400c82080544921b0420340318041603d00f24068811480c0380c035003031b01d040740a4407204110400100350070403c0381c007003001405110200703481c03203a0100080107000d059402200d200340f0090000f5656030400200844c03c5541e11070b0401d046034540130020031403454000c540920690459501e8000c18004000a801091403510811981c80c10300000d6000c05404141580b0f568000d8035541e484110007403c3c0030740c0e4040c060008091343c01c0094140907140c1d4610f2515503a900440c2c0c101c1c185a103038030055089a1281d0480e03a8010101c1c07008101c0a1030b140202513400c0d24503c0244040c2d4990b5803118410700032800344022102001c04c1c81c90540078900b010b100102200d01c0c3c2000c840fa61045c129464101e200000d5010380281079007a0038103006400344d103e071641e060b03450314a409585c425500080118040880f1070548444140c0a544014050711800015032009440310301220f041c05c04a040c101c0d0702c40110f80d01c40d6441000f01840801010f17a0040d01510010703 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 467578543 1250 467577293 467577323
    0x170313060f0323090106120c030201260406051005041406010503060d150212011208040b090f03160806090d082d07050c0c060405030a060e0f0d05270a03 67
    0x3602910310100c21000941e0141e100900d2a02030009281c002c0c204a002040100c0c1c80e4840b0280d01c491f40c100241c24054450020070055120f1448150006100c01c00140051540b107407060010300c0581d0240d48181d126414882200d0502d03094a0040404403410000c00d071001c081c80050345001002c0303a050202c04400120503880c1c801c0c0b0100c04546c0302500c41020030b4000c1c003480003508040c240c444071402030030001c00c401440d0008010181c0d081010076080501c1c10310a18803582c0900c141e01e812641180c0302c2d100546040090790600c40c0210300c2c0100c40d0f03081c83c00c41850010010301380c0c0c0c00c6510078902c0c1c82c42950020500c40d0010815102180b6502c00304082200c21440850a680c2c10100311081240b0700b135100c3d01030000460751030155108010042d0401134540223a0042c1c0e40d150700f01d2240c01001400d1588450000d04082c003d07201301d844841401410700c0c601c070001d1000b155000805400c12401150354044140e0082103103c141905070340842c243c5502800f0080120144c02400 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 467579793 1250 467578543 467578547
    0x4020903101d011e11040303050414010c1e1406152e05031803030f1503070801021b010b120a0807050f101a030a030e0d0c08060f01170313060f 63
    0x410703001d4400c44001d02c181c0001a518030041c03108000d50040d11885c120002c03001540302400c03136084941580c4c4107400c060030300c468000c0000b501d2480a043c00280301c038200015022920000d41c12201020718543c941d071605046114000906c1414001c1d00150208079040343c0760b640b80e541e00d0f842a00c8a5196440c401181c030450f6034040c20741c05110011101181000b5031080085120300c000c01c036038441c801030440f0802e40c1ca02041d226104220039060005407440450920034848010041c11140c04030b90310383e0103608a0b44006040aa40706448500604254090007012040d0b401640c50705480035112840039100c1c1c08001c4001e0500c04002817081c28000200b29108041600324280e44003038518208100084c407441c2c80340c0d00b01c003031503101604a038900800c45150702505a101c103448014220100701e05451030030422944032007008408070b030081007046124032490075004031500b40d50410030310705849540b0074ad003102e02c1e51040000b600b2545100e4014011a0814140341004101410342 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 467581043 1250 467579793 467579831
    0xa02010e030c0106061101050f0601030b0609040509010f11070c03110a080d050405090c090109031e2306090607021b041113031704030c12051608060601030b0402090310 74
    0xc40050391001041581a2100c19400340b02210600c1d250301c40810305184403a03080c1c40c81103400d001b0320100c0c0e5000840035402500018521640109258541080c890010b41120420348020425070341d502903040420020f4071522800c1c210015201b4100107042d9100b101060480c04020030000860007007820544075541560042c0c21180c05958a005c80210001d00301d410074441c241c807680001e004507002610b0a0201c420404040e90b03420b0000d815905d0b01404140e40034000030304074542072009404121480035403d40c20306c00615017031003031200064007864500007601008031340c1c20201c1070242482e0000352032420700b1210f4080b0f25005100704000344c01040300442d1210500000910344580c04200c000d01c4042c0c0b03124000d2411480803500158107140a280801030250380e020f00148030840003421114942445181100d0205101c03c581c0071084140ba4002903040d800700b014401c0d55078160250b00c2202030141d40460601e030740000025512500041e0b01000c20740e68104000c000484900 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 467582293 1250 467581043 467581061
    0x50c0714060c034512160e06030d09061715090108011401090c050403230a1202010509031c0e21070204050615040e0c0403020d080702011214010b0a0201 67
    0x1040c1c82c1c42c0c24040c041c20342c080300071040c441303c002c4050030981d039440350400c041c21220090061030000d15101000f0320822a01c1001440d241e445981140a00780d5070070b582042c090210750003418200e08000b0141490828404100780c148003c580303090000660001140075030050360010004c0c00d0b00d84810f500702010f04007124a4000c0c0003000089201901500b000000e140300040c4103000340c1e0307101c50b40400c86c0c0c0c00c0c3c004140003660070001080072444c0c070404548a0140252045080d40c0e0201c40d1034640310181030b04a4030680305404581c0104d4080c440d0039485410349000d58680006401c20401c00d440e0145405880c030b6640d000311141c0c100c04c01001c420a40c03001e12407030180d0101c50312070b03204d50014003040b0b00c25400c1400044031030401d841d00300381b40b014002e002c0d42003900b00f0104e681c072544000d10003000c210043c8400030151340d0340704820300000d0049000039501c03c80b40c00010070780c0c0440d040059005040c00e0441040404515002e411540c1041400740c99900302c1004901405600c1 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 467583543 1250 467582293 467582317
    0x10030207060204030f0311062401110114062b03030207030c0b070305100503070506071e05030d02040627230a080106050a150f08070915030e0d050c071406 68
    0x100f00401002a642d803600788090194461780c10500751000d0540d5620b100319045100b0070858408041d549895100c0c00081440c141401801054107043c51400c45201000604200e541001400068181018084021b0041e0f216101140a44109620601e4175003031004007010350008224041c144a4404035a420b58441c0803402c1c0383c102004000d000e84010f803245c000a0ba100080018285400503400d021104080c2141c0d0030000355403140070055415025a003841c01c0c020095200081d8103100500d19954003510041c0c580741060001807100d525074207058111030400c0c041c41041c49054a4500444040b98440700c0744010064034058030040142101d0b4000f04400002301d010201900701c2410703508113031410903420340d941d11401c41c4c030301c948502d90000c04c6034a41100304151003404015446412400c08901460341d0752004043d140c8810701c0d10000998034100d0702803242d003d100141c04859503140441c03c10104090a5848030814814045041c01519441800d42c0300c80c41a01c100860310 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 467584793 1250 467583543 467583547
    0x21506090606120a1517070b0f131d0a091a070201110a09080606060406080c0315060a11010c050c0d0e03070305070b03040507061b0209130209130302120414100302070602 75
    0x7414540300a0041d07945110800711200c100446c2086440b2203211960041e10010300c900c078540b00c09041c1c0e80d408402c00500310f00080055144044009101100500d820058030064041003804000c1200024129039003890401c2d01c2c00c404a0a1420740780c40320b84810f403903e1525103c0340d0007030340145a050b1108a0381100412581c88054001c9201002c8440e10001d580c0d40c0d658440402c00b45104900520001ca00da207000f20b440c1c0d10008028551040810911a40f40082140090502d0700300b010408002190030b0159210303002c0c00e00170201408100e04145080c8a0f840f0310184c0c807031744030001c0d80d410001035101422031564200485030003140c0180c1510f500e01d460b80c280c21002c0d03104481c10f0743d4900c03842c000020103d10640c0c250041680c4407100daa80c080c46503080008012026107180c41c100e2400c00401d01503605ca54005010b481c0d040003a801c081105d150281c20301c00010501004080c00340810800c1c281603202c030040c200811035542035402e0842d8016130003030181d0100608810300c0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 467586043 1250 467584793 467584801
    0x40e0619170c0319020315060619020307060501140f010e010203090105130f030309030308070807020d0f05071406060111010b0a030f0309080708010b0a05031c03020a11100209040c02150609060612 86
    0x100802c401d004d01c0c005d4041d1021340484401c1016003600a68401d6040b0408020b14840842e6034925818000c95078416240303040c060703490302425500300303030000203030b444800b8045103030740c54094400e040002e401c0c205401940140c4001070f499004054401b41800f1000900081502001403190041c01018610540864803400c0041c100c1005000c00c9010075100340200d107200c1e010f9103419101c1c0c440c66000704504181c8503022284103100000c0c41040c00400d2040d00005060410510342c030361520b4004020600e40b401c0014202010f82800d50007591600c46a42c010761a080780301030a0b82d0300903220302d003560303014901111400d48940c00107400e4010b640000c0398220701034004070b901c000c08543d040c00702c0791500109030b1a54600161400c01c45685605d8002442c000d8020341706070201030a103040c01c1109100b0050400650040f43d41086a00080f58611444c1a218446000f112880203003100000800000310400020380103074496500b01c1c0c0010003d9962004440c80c1d101c0e5401e0740d24503810 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 467587293 1250 467586043 467586073
    0x50604090f110a05091015090801091401062702032a07170301081c110706080108010f0b0303070b1504021602010801060206090717120f040e0619170c03 67
    0x8100b0000c2c80c41000d40c080f00050074034104400307501409082e00e00700210b40c500308682c0740e02d1207621a01400d102045200003244502842840e0045000704000c030740c0480310300d40250845010360420491500348030500c5000111501c00d030341084800030001681e9486000d4426a00200d041006000094212840440e9043e50010300042d51141c4001d6801e2400e0b01020301040c04240200c0900d54000d05021107030001c0100c2462040700c40c0d007004454012030728140c60070400143c0100020503114401000b0f0200244640c11280d600c241342001a0301e1840c000a0b21707032041d010042d000704030401c00308481c00104007462400c854028000c42d902c0480b841c01c3c5624440c6104144d02040802000081181c00400e407a072107107070202c000c0c044850611624600300104640f00c44454414a80d8441c0804648c00007824000c0469620315280c500c1e009403004484001010240140711004125055585034801402903804501000305981e903c944040d00d0800c0441c003ea502d032094900c01a8124 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 467588543 1250 467587293 467587313
    0x70e01111c05071505063d02070315060f05130f02032514091e06040b19030c0f080613050c0a0f0305040b0609040f06050906061809070306050604090f 66
    0x15100d030b400302c500a1344c1c0740c9500085841c1250241d0700a2070030814482d1841410100718442c0d01204042500101410580341d0044602c1040b2405a4054041801403020030700c0240c4824041000c00e0001a04190070b8184e804843c0c4500c40c001c480312600740790400c10b2900030403410482d03904115102e180617900490070940e280c0c000703c400c419222940d02d0715480340d904070031290340c101d400d0f13454401b1403004c0c411420401c20000300282840368128103940e0b02e02005000800f03880d00000d07100c110b00c82d040888001d0780d10b440c41c10725191107940c4034000d4101c41c1000720344056082008550303940101041220318480c070413501032480c010030094050034400c00380041d1309242e0307180364400803142c80550440d0000d54001e410302c8510300024084c0d190801c002030740a0301c284140003080c049551114180c94094680c1d06950b00550100021410690610750b52284212041c0107241040d42c1000d88030f0761280005080c0c90344a000107105500c45411000c8042c0e03001e001c000c400d580e1400d00c840c5007 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 467589793 1250 467588543 467588557
    0x30c090906010e01081801090807050d03050105011b0303052206050103030f03060506090904080c0d023a0809120a1701050a05010f0e030a0c0b0309010f0203070e01111c05 75
    0x30045000440c40d5944128444009200103844a9100307440c0c2c605800c48081e03481a0300c240c10341d214542800010012005003c400c0e100d5001042401d51160000e4241c600c16000a0304001003150b01c1c5043e0404203402078401c940500b00018903407941030002c05da080c003006144038990094402c41003003085540c0858101e0340641d0360908401403c110407020b6400c684192640700c8424061854103141c660702064100340b244074030720b10b0280d801c0d02603418040180076050258100c0e8442104081c50707044038107000c07054000200c09400e0708980e0110410303031900c00a001c1140101c0001c00b4000200000051001c00c50129500c90640d01401845026401c2204161344100000050b050404844a100f502e4050f1100f011b4510401000c45404d132000d810181d03d8402d401e9801d01086d00c070a12400542031804145550740f4000078101d0a440d84419004d128501c10001c0214480d030249511001c04801d280407818903404c8110641380c1014203030808118141c00079101807441e00302c0000c0c160 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 467591043 1250 467589793 467589799
    0x612030507060f0209030a060b061209060108010b10050346060b07080703080406200307080906040308070c050a0b0a0203040311010c0207090905010e0a03030507020f011803051b03030c09 82
    0x8003da4007200c400aa002d089a01900355021754131010008400d030b003140341159000340109090000700110f1850b01402600c060059801103001444901c0c4280200800d501050b1070503034400322011750081040c400206a0408080e8a41c140b0108100c092155901803504101301c0c162007500100d11020b07954800c181440e0701d80b41c0140000e600181c04141c61110b90030860303981c2001c04c9906d040c5e07054007006100b15441c0c1d90795200c204603440550031007214206031078105500ca1a00e040054904c0c0800761015050394401b02c10040002c1c0c0c0403000301e611510740c0c90440003240c00342ca042841c10042ca00e00614050240d010041c540c0e00b55130246100da4020383c1e0f10f140c030034405c404803400c0752400d060030340040e00814410b210160441d00424003181c4503200000308044200070160400208090440000784c8803003d01030150350400c800d0300013840c004020400c0e030100d51070a01250007104801400d0110100e00d04100740380d09041c2442c800061802d41e07a9911b00760549112541c000c0400300e02c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 467592293 1250 467591043 467591051
    0x1030b0d0c090b0a08070603020a09090e06011511100b0d020402180102120f031f09050702070f051504030b04031b0b0a1103190b280f09020328061203050706 69
    0xf092414210640c12030303010102505010303007410f000720b020303600684410090202492001440704424032840940703c031303008050400c550400f4000c102c43c042440c0134408200144040c0d06c494100810340c0d985038018600002042e0404a000c0703410100d940702d01030350003840032503084209107402c0000c48088100340d094602d007440d1071400a02e9801900c084580750718080c400202d0141b40d030798130b0090f2240504002c00a05580b012424140c0f213080b140140107801c038000810000300304103c000003400341103c40d84801c00421313848603a0b502a503c07000d04840c4030540401c041c1805140c06619102c0c2c1d40d045400c03001071508280490035800d55406890600e410740c100c601e01e00030fa0a5a004100c00c4000e40d850b01080c1030854003800300703d40810761024002d0008448641403051002e191041c0c1e1003400320b06071501c1403802000e4496032256046600400c2008401a5074103030b90026440461101b010140b0709105d100000c003102e030001000380b94840b1003d002c9c56007100280c4821881600180 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 467593543 1250 467592293 467592311
    0x418020a050117040b1902181906140d0e030c07030311160312030608010516030e0604051f020f070b04050c030a050c01050a030b0310061e030f060b01030b0d0c09 71
    0x551103c09003203a611640c01e0280401e002070034861030541c20281c4000606000140e11410301d0890f44015002c03440301c07500c1403400c0c1d02030415078020b0200401c0700d07071206404c0380341c84400f0300b00c4109080715a042d00070000e624141040c059000710f904102e0300003103e4542c040003a4881c0d0310149400700790042081082110586803000441d0100030240d40d45c40041d071440d41c0e030384d41c140c1e240300c003414802c3c107884500100e20701c807003403040c644035500c94201c5110300301201c170010301103c01c03202c254003e40c0c001c041000003060001542e601c500300d8007c082507685e5203217490f0303000078014071040f00400036001030414203100b850004240280e00075800e80e08281c61490800d40c2c1d8001a000c0204a9001280e44000c158001c1c0050070440c003250602294002014000900307142203503001c0c8000704d40e00c00701400455207051440308408540d60070345d4100d0342552a1a0701c4200b003040014403d5840f00c91440250b4465040302c1d0210001031710051040d0072501e0690240146805103040c4649000c01c14 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 467594793 1250 467593543 467593547
    0x30506090c0c0d111504110a0603090803060f011103040609171b090c040e040f0506100e0c07020607060f0f0c03020a050906090111030301080f0d050702011215050418020a0501 77
    0x90324181d031682c00910600b4800501500c12070004210b4000d64000c0031004440480c0581c1c11318402c62150001000c400c60a10410164a4081e0481000c05107840d4031000000c0d02c0c0c0003181e030046011130304038010304201001221151945040301d1000d000102d80064140d400801c0c410507104103110a003100101c40f0381503aa940c1407102400d100140d02074080040382440b111840d040400c4a50b101e15041c2c9070742c42d2140c0c00e142640c044510751104802e1509000d014004150080001840b1001d2580340066508020801810204c003c500020b200c20448d1703916812259082d50000c0c090054800344c030b2034000182203029045114500f0000c100c44414440d108441c0d43d0951030312214103045005041c0b140d2a0085810030f418400c0952000300d040804002450017003904a0082070f1802003a07040780e040c0b41d14072541030f0134008188400d10060381c0103640111000b80100b000941c03440183c0c03203d482d60340258807a0743c01514040050a01c0c0d03c8032889600403c3c02540d01c91807040d036070001 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 467596043 1250 467594793 467594797
    0x11a07030c020d0c05040606081e1e131403090f010302090d150908030c0307021c0509040f2004080601050315040215120a0b1c020303040b1605030a030506090c 70
    0x802400510100003800041c58840e610f29141030080d01c241c08a16111000b05044030065040203000c41c000d0301c2003002000c14542e41d40d103042060904800942411103c0c2c4900860b13401e4421580518900021a101626041e2422043d000001880c1805001421548070340c01040a06d0050040d884003440c01d501a0007103525010029042200002c6607031a44440351404c66440c54a42d9114030035040810ba80c40040c5004207590f90700300b5528244440082e28198040e4a1400410424070313800703640540100658055440c1901c010410300f4004500c0d200600f401462404c00e19000707001d520580e05010050020b1341c0101c002c4849a9884008165440b800085045900e80c828000a401030410004224401d0b0010556504240c009590107060340c004882070518955561a000c816140030181864805421449e281075561960040713503c92059004180085400050642c5984085c2d0350b4002c00703039080b20540780c60301c4281b20004c010b4a41030f204280306506003400f00d0403208010003 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 467597293 1250 467596043 467596057
    0x6010f0608160801090e030717042c0105010f020a02040507120c08061c03050412031e03050f04030f0c0812040b0115090504050604021b01050f070c020306040609022106011a 76
    0x65030031041e8070301228100908804003803240d040c041440004001292140c1240642c03044000003601c8900782942802520303165809803c0c03100a4bc00041e00810481201078155102881c1c2802ca5001107881a4a4850f0511000350050314000411034159031009005841022140062102180d01c02045400394030588040c1d911060811058800b0042d000c4070700b00c0f5a12a01300b6a08059880c18100c82d1542e4124054000c121804484081c807410084070800303004503030404010a040c51420305050800040c002420b00140c41000d6140d680118010f9004031380c4100080d946006540401103051800c2c2c6007152035900714030011444840000c540c91105040d503a03440341c0245003604100c0a0080680040c0d0065400c03c801e00c001d81214644c0b0b0800c1008000109141c100661186590381c001403000080020f250340800043e5404103030389401035040400491425070b54000110041c9803011700c00c450051514414241c2513000c510a8102d074685503008001c40c11003c00a00d9030300c5001 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 467598543 1250 467597293 467597297
    0x7021c0e01090b1308030c010501090c0306120b060a0504020c03090f041e05190f022205011709031b061b0307171003021c060605180403120b0306010f060816 69
    0x40050003010f040310041d0501032032a00c44602c0c825681c002060071a0711803a04401e03940d45410042c0071820072401188414030540c0303820400350345071800c6100c0303115105600801c11030329400419015030b40c40031514040e02d4000c1c021503030b5906010340c6a0742c3e64092100b4074002c5041c818100141d207010b00c1101c415440b151801c0c80c0c1a802c290202000701030040661440d03052000310b60380440d4803403080c04031040c0007a00050340c404034100740c0c80c0381044201304c0100207031407501c0034401644d00114890306009001c551940a840780d8040d030b41140180d038030700c1c105008039049020500e90001002e90049007045002c409034000070262035440d02c011030700500441d142400c0c1c0240302c1460b5120303542c804480c05c0b0400030152a81d0020700c2c1900000e0444021200700320f402020702c86680314650040804480300700031102041c0180948282c0200054184080300c0440401c1c000e072a0485c00480800800f50b44403580c44031000f60b003a01d181d009045c0000d14403000541200005a10426032404903 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 467599793 1250 467598543 467598557
    0x3061b020c0913050a1101030f15090914010c09050901080604080906030619080106060f020304120212030418140a02070b0406240305010c11120405040c090e07021c0e01 74
    0x100c000d2001c1200050f082c201c518030319640c0c0c0340100f001070000400541c852040c24a10410050005080c1d0342d8510261280626001004000c440b915421070708580d610071000c00c510b285404c001c2c07101c420f490141615542003403043e40e00e1030f9020300c106041c0c84e402c84480103140d03242c1070529902c61b402c440040004c90b0400c00c0c1e040c90b140070300103158085c0004159148604110b21070250300c0101c0e6112004680d10f41c1c1c8148074981e08011407030408400c9100640c2070074945040c850026050610107030207024440b40028200c1c4050040300e0180200002c0c1821815200441000070106507042503500b100c550041034004005000710742e049a00715100c1101031310b41d92512401802c01c11040309454145010000508031950540001180103c00001d4500000b102c05000c41f01800a1008150418401008510162015102034139803d9600003440c0751901c000b5070303401c50180c00c8219005013031001c01640545c00549c00c1050f8030642c40285207023148020544110030b102032080c1c04501c40c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 467601043 1250 467599793 467599813
    0xd0e190303020f04080d0c0c120321060b03040302070501021005330d03091d01120311010b0607200f1309110406030f030f020303070e06030901060b03070903061b02 72
    0x4a034025220a68184225034509039a5a02c0d17149401110f0701d1107004110101c00010a00954402c100700a05079201f00360384815080c0da0040401c210b06528102c40c03464490030003106080385d400707032000e4469800c00c19035034103260801a41d034206034481c1d240107100b00b0004241d1107606009043c003a142000c0c20441c9800d2074030004800d5a400e01c54685041030521041d041e9a4444601c0410a406601c65512041c03c1c00000e8200408090f12238600c850b0480c01040905080c0e041079084a41510341000000301c030300d0760385015280141a59500075008034a290501121301c03000034085038207010304800701c1c07104000e001420007545c0071568000940404507041544541250030401c0c0b08000d45103003155404001411a130840c0c0056401d1074110450703001f0150042400614031f40507000840c2540f0b81032000801034880b00060600401e030200215880398403d420480140500c540040d4a0340303456000201803030b06601c01644d9490400c007003400070007022030030980000e18070303800f41490410b = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 467602293 1250 467601043 467601047
    0x51c03060e010504091a01090e0c06040302210c03060a1b03111602030a0c090c0224040f1a0103030201022a0d080403110312040b06030d080402011818020d0e1903 71
    0x602c1080980d0351b004855501030103100e0848290b4042c140180c800203178401071300011172400d51104180c9c0d0140d5000c02040c000345e616035003907500f0200a28600609240c0b114032013414161001d01c0950144036000c240040036410742c00c804c042ca100c210072a1580c03903e58000b2015244540b802e042606402c110000c200e03010540c41464807800501114400501030340c50038402c440c6540469080d695903044002d0107a4144820307020158451240400015800740000c1c1d80c1c0e00180c40200b8615444078032104004894040b441e0081030300003102c21175a521704019000c0e60000302810b402d0503120303069802c0517a0040702c40307903041c840d5001055640041d0009440744e0301c010304190701b80000f10100d903155040400c010321a1310040c5040d42102d00305880c040b804e4080c041c20491294004400c440c4026078000030056211b0f07024a006085035070f0403180948000d0240d004020310040c0030000380e03d40c09841d001002c258450130340c1002442c001198254441a07000d0030240c811781c0c03070488680030038 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 467603543 1250 467602293 467602301
    0xf1509020f0c070b0c010509210a0c120905030c030d1403060604030507090b0301051008030a0c21020106081203040c06030207050c0a0e070908030f25050a051c03060e010504 76
    0x200c1811141c03442c04003941e81491a0010651000b010070600203a5206800302c28000c0c1c907002003500000f01104803c01458261001c6011510884e00d4004a1510300c800d20400c64512201d4000b03150706114a80f070900104084054000c980c000c1c801e40420440c603003400120608220401c0d6503d03860484100201c102c154005401aa80000240408404240107000d04002888000b074005001e018a90505095034801000c826654000760001c0192410100440f00103824901c0d01514500c424a13041505d1030405001512400082c203000d80fa66405510517030503101e0702c03c00c854511440101000562104940c0102000c40c2c094007000701a0003900a001060300c5081525a16210640071425024255109100c0c2034a40414481d8081e00110700c0b6000e021924095885c114660741000010310404100d460b428106645c1d0100ca0b20242003014515580a01510041c484a0810700d6640307403101410f40104070110313404c601c003600070320511084407900f220301c0d00242e1900080000034 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 467604793 1250 467603543 467603557
    0x190f1407020d0b0f010f08030a0e100309080f0d0b09130308070207030203061005100e0901060c0204020708030c040614090a030b041a0f070212030606091c080a050d0f150902 76
    0x4000c0441a00010f004000060301c01d20302400700c3c884070740c984810940444241e5202c0344050300100800c0080c02d500c60301d01c40d089130003501c00c2d4400e862192001c41c000c060020010342040c40104c0d07803030311003040b900090606042c5907000381325403480c2904100c10a5006e95000e00c001c0f03200551100041e0144025591005190054842d11581c0e83c01003802c001e022944501010011a003d21042c40c0c040410078601070700380b811051480d05031011075403030700042c0100824051620b03004001c559881d011142002c0d44940301c581c076810521459400764005004020105107a0440e110f18483d41a00341c0d003145030000d06840380f061441d228800100005401541e15202e02e0450005020603100031500030054041014010703e071078072000b0700303054401280c10380b00c4c0c1c800c1007882116a40d440c1980d182c00f104540c004481c40c804118001001e09401d00100030384008140400030580202c0030b4900c00302e02410500c484030505240d50211400b01e80e20701d83c203d100c0e00090103036840940c098091 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 467606043 1250 467604793 467604799
    0xb130b06070b040602070210081911070501060801050603190b19090204020a020721230a0b04050c01090e06010c06050a0e1501030212070b03010b0c03040504020f190f140702 76
    0x740c5102500d92200000003250f0550b01c59400050074011402e000c5400154000145841c0d90517080c504040e410461490540105040e158440448034202e8003084400c2d20740e00ca0001c003c40c0e1303900ea0340d46010702011246588207016030400641c0209900740441c0070f050380092001c0860b0b4071302601d46910103086c681c540300a40d5550140f1700680340e501c0188144030311034005010f85454280305000e40d20380b0b44050b001c4401d0141d0300c035000808010221011001c5002905c02e04140e0a007900c0c50512444000f405100b00001800b0500a0200ea607004500c0d007a07a401200940324818568450710a980782400140e00d6074034600400c51070703030006410140d2084041010034070410100e14104c1d1100541e07240303640b00c0004004604e00700080e0801515240050007034507161003e8508a40014414000030743c0300050000d0102d5401d0080b5805004002c10864680c030500400c445076030006203451181c59055946445582e0241112055542031030780c4054100f040300303c60b120503030400c040c202e030 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 467607293 1250 467606043 467606047
    0xc0f02070315020717090f0f0307120215040303120c0c0b01091806020d0209090a0b0d02060a050f0a0f0f021501050d0c030f030c021305010f030204020f12190608010b130b06 76
    0x26090440d0540300b00c1714510f0151203400000400c10380e0f9070120140341c4a22000707801c00c12603032030110f00c0400304c60981c80340d41100c0740d00307002096101d14544220445298000340c08801c0507003040c5003070014928644104110540041c0c00c2d111000c03035001c085d001c483e01313200400105405030081181030b103410540c0c2d0707211142c03035503040280d0300506880203003541c02207010115030038101040ca6008a11070b9091203444a1503020800c03c0681c0d4801038018400041c1c036510142c094000c50b50740840340456160380300c44010300104070702290305500000650110441e041d20307200060818601c07c01e05804d2100341d18000030040c400c1041e11084500000003940040421504404010000e0003901c9001c134503d1584100547d10041003a580e02c11303803901c2c006005801a10380c0c1401504e0341641c0060342c2d010886807a031482e008004c009461240001c00708400b5a05403111481800c0400c0024441c2588500000b400d0b5051000c006170081100c044144d24124a40c204e40601000544414 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 467608543 1250 467607293 467607307
    0xb0c06270708251d0702030f0408060f09030715201207090806040b1617160207060e061909030f031106060108220204110c0f010c0f0207031502 63
    0x90705111140d4040d4900d41c00880a21410000300000302240303007180c50600c1d9140703003400c04500e40e41c122602c851400c40d001d40000f0300305a000300f0031190311054114806480c1e980e074030743c0160740c2c0e03000f141e4040c029009200445d2000d940082a207812a5000484d11440c2900300d24580044c00d020400b903804000030642c0381c00000c00e20f00240a081201d44126400f40340001014044400303603402841640e000e4820000884c1001076165040318016881c0000155040001c44040300c803d1b0056141c0718102092108a483c00748012413400140c1c0c003078446295450500b078850110101341c0603004642004000070019803141e052141241c1d3f42401d001013030f126100c00c00600800c001c2240480d0450720b8a400c11181003020170352221003440e000860b80b42140040c09100c141c04a038040510301c0c03d907907104640c0c9a0700502d0314119201d01c00c40c0c03203111203e0810b61364035064903200001c1d460a40c81a4809110306e281c02031203c5140c00904100345150340e0b0703c0e80b00b0f142034103450903503509100340 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 467609793 1250 467608543 467608621
    0xa1802370825020102040f050f0604141f0e010f091d06030109060e06040c1e03060207050109200108091507050c16090b0324160507080c0102130b0c06 66
    0x7050382d8802c0c1c1d900041e20b890402001556022050300114170407010703d402d08441d5580d00c1d0841341902c1010019140c0741e030300903022554000c881e83e0710b52148020445000d290f958400c0524988403400d0380c0b4000a1489071000742c8401c8120300402e8041082a03000e58217604005038080d41000e03000d40005a50030080e1980421541c02c1c148004460f046101484184100030803443d0213041204e01c0e450b400e00d0310b610b25400407005803000510a41c1c000c02c250381401000e6201049003900302c4c4072809181100c06250320000308d0001c6550106103801c02241a80d035001a1448036003800c2c1d81c2507605512603c03000e65150700040302e455140e2240204841110b8840201b8030000c0454000104052440070201130510742101c1101024000384680d1951890511a415030030040710808058089006001143c4511078014090301900c6d00041010140c0c0703055008021903e0311600850308691102e0880320688540e100c0350800750f02003004540107458001040840f13080076a02503490402001103 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 467611043 1250 467609793 467609851
    0xb180613020c031c0b13020f19020c1e190503070b07080408011505120319030f021e0301030507082406011b05070602010c090f12020a18023708 63
    0x2046080b43d840d145907030344c2c50a10406c1d542120207540810341c206148000040d009016a11405107054682d2041102c518001e112500003503d010b00a1007640700e42000412103d0701d200107503802400071074000602000b40b404800191074004018022103480c1a1552100f904030780002d54804004120024102e5000d1255401e0145d514524000031450142085409507440c1c82c4542c1c550820028103030103207200850110f207001c1a090005e6401c1305034000d080203025a40c0303008005101c501c0c0b1000540da6000c0594100da1185045034551500c40348502d40780e4205d4803000c009000e04007881c1642c44000e030f02c603da1204040c584010140b1b00507010b046004c0d0004020b8070103800103101400b04d56420300603203a0345074050804600d80c51030164101d00d054414424002c001c98440c08450440d030741c0000780e00c01010200403e640382030080d80344034000c2d8041d150f070342110385001d003202c004840b4808841e0301800c0d42d820030f6400342c902c85070243c50000000380030103a602c48501d40341d1401505501c1d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 467612293 1250 467611043 467611087
    0x301080109030e0631080d0c06060803040302061c020d02180a08010515190510090e010e010302180a0906022a06040b0c0f09040c030b180613020c03 65
    0x4036100805082c0900505000e072880f070301440040210002d00700340c0500000c40208988055501c03d0b0500844409040f81500300c0806402984161654503601200d156102402800d00704107940d911007541e5601d02c41c512000350084001d000795010004102c16219216400500162034079110002010803039000030350300c685580d01d0000d20180c3d07081115076800942600802082503080501b203880e060008000700e40d00c9691440c42c960202409001c01500401c0050040448040010006000300e580b9000e01c40c1d5001c2000c00000f03a40a440400710b040ba50068015401e20905020741959040004d1001b80260b0b122041000021400e1004007100c45001010614895a03c3c28000004a220140b000d0b203038410420700c00481c08400d900c0d500441070201c0700d0354616000c901080b6500444541329480b524004101800b190550400c4071614011100c0441580c614000314402c4003058401c0c940000d80010407400c0c0c0c1c0d001d603004000306249102100d06120500030b00380d84580d0342d11 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 467613543 1250 467612293 467612309
    0x209070c060b0301060303050d0908120c19030c05070201031d100e1009020303120603120307090e010603050403020a0303020a090b0f0d05070c03080708070c0506150312071a0601030b03030301 84
    0x225031030a0214500c80c41c01144000c034000d00c400d40ca1518010940e0250452008445a4840481303003005608011118060060400c00780d0030300d090b1900c1d01d041d8003d0781d200b150104034111599080e52003803050344290041e9031159800e10f40c1580044000700b1203514010510204a4080c025240b8208000a4100e100a40100b1807a904c1250035040c4a6501c3c101452203043c54000380050307402005980010a40441d49c1d1140d690310b4002919060a02100e10843c440010030300c1050303a40548404284c4100108150076666110710413811104212405001170b0486064200003d2113134000304440c40342454030802480d22140307c5103042c1c3c0840c40381410348400041051542c0d015004141e0300003a1401c1290408090b03840c090700841d0001c0c4001c00f000a080001114107004121034005541c2000c03c88035075107043e0411980c04504510003a22078454411007a000c00258400c483d100c0380d00806500040000247e24804160003900340c5051503207038412510503031800c00103036000300901 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 467614793 1250 467613543 467613557
    0x30c0b13060b040b0109090e0c060a0c02010801120201020a06090c08030f0d0e010506060d0903021f05060916090b091f020d09050a1a070501090206130e06040204060215090a020907 79
    0x81e150038021038002c000321500960a08021541c16a0400030a00890f13804032800710f4815424115141040191012540e11800201d84043c0345544401ca10000394402e89410031181d0301c903c03000c8450380315124000e0041e4090309200000800d560001584944130f00c958584160300c13018914110f420102000d0112200403071400f081107602d025070034030b90740008000c20660034940c000c03c00c24499426481070340c80e00d07205002c0030988200f050714418520480f141c1d004050610421000d00340940300c15100c1d03c20017010031070000610100d181c1030000c03a11118001882c04114200c160030401a096000c4510f001034010031190001c6021213560b03a0340034140d449100c200c0030344070361003542101d03011340e010315004c1c0030b40b02105134603440181d0105186a1144254984280501001c0c1d1000750404008901d0362030382e503040e03021070084c3c55200107840791566454052100301e00441c4640320041e803150302482001240b04511a404c03c111006651201e150b6401140c2d4501055a440d0001141 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 467616043 1250 467614793 467614831
    0x60806090d03050c1312082203050f060613090317041202120a0c020904290105010909050c090d050708030415030614010e090c0904090c030201020c0a0806070c030c0b 73
    0x4144106a40841c0602c44d01341809107904040f4118440e0740100d0032960b04c2410b440741400340c0101660610001c594002e140d03400040c1001c0286807a6100888647c0305058000354440808240b9501c200d0b005003203403640400c4054000050052000d042c0d0501400400b40d0040d0a4080903542c8201d005601d0011001c1c00b80700c0c000d1510030010f5040d180e08405000035024580c0c4071129403a5283c040756691600c0d150b03030621400c44440786503521251010f80e85100d00302921010310034100d9800342c954404450381c0e0501c503400e540040305e00c4102120108043e12440c680401c85002e050b0003142181c00d000d45a9403241d04d15413180d0003d0b0740390051501d41c8050541e0502400000e00580031940c0000b1105000180c120b2000d2142c0300d21034120f04000840166402c402d548440100500c00d1021205c942040d02c00c1d03995500050b80140143c0c03500d03c0309030074002c00a071304032209500244200d54511004648079103135060104c00704024000d6002c0410b92101c121070280c00e09260007004268 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 467617293 1250 467616043 467616047
    0x11030a08071d03070306141806043e0906041103010509091c0908010501050a050303030703050a2003010e0112080703080c30011e06080603030c0d09170111090d02010201060806090d 79
    0x21f8001c0c20181c2880c0e45200102c50088081959030700030364040002510301c1000395001142c019240d04c00d15105201c08001824212000c2d001900740006455100103903d402c018407095038024900f619140761b0800040001e418100344055001400005445c440c0080410752308600b0300c4464850001840107106002018080c41264010b28045407108101c5180402207070f26404002c040c042419620800903030f841e401904403824240306502d078540d1000c10300d01c4440281c1c1080c002c84240c0c00c2100000704d8160031650000320000c0e0001e5501c0c0c1890710b2030341c1c112603074400200500341541013442501000c6401c442010510780e10001601714103c148109180b60010581c04500014180007103906e008152405003030a480c0c0c18544080140c3c0d9a0b8082451885801150802d5106240c003040400e41d102d030100c01074900509900c40c443d4408000700e070076600050a404000c8204002c0404a85000e0383c04020040c41800040788007030f0750750f21841c10120708440341202c6030441241255910713 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 467618543 1250 467617293 467617331
    0x14040605130b0c07020d02030708101109010203070b0c0702060423030109120e061611100203040302060909180a050303070e030303040b06010503090a0606090c11030a08071d03070306 80
    0x205403041e62041d08503544484015420180c15054035a500103002d00641d03c42c0101d126107160050206c840803030355800284e654a90108060b00d00c00c1c94000d80050201044c4221418104164015801d10405031566001840003801c004140d07441017050b0801612268042c000901c1c1c001c03001e800d946001d404198480d00c030000141e01c01e034900808140000c10100801219603580c0c0392584940306260701140091040d44580148901301480e88800c10040b00540748a00500390340010459541c1c120590f0f990103a400001c0d4092418003140600e42012042c00b076008000a0414017201802142c003418418040300643d03080d00700200b040007594100c000c42d9102d20065004502c1c62400351a005c0d0a820045c10345810060000041140a00204911040b090300450100030680c0d0b241c00007001003002a42850100f1000510104000700120548031382e00711684490302030707580780ca40c04c5550080707034020703000e507500005041a40d03908c0c2001601c000d54401c10001030740207500c1003244030311 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 467619793 1250 467618543 467618551
    0x30303021b16031e0204050906060f09010e0f1b0a0c0c060c0213093905040603031d01090b0d050f01090507020709110d110307030509061311060c0114040605 69
    0x5039000d64051001d480c100c2200300203c3c1d8114130541280b21030320b010078040ea400d45030b001c1e42c09814030052024441005c42c0c101d0080f01d08989011101c44e103041400402c250034821602d100803140002502148625401ca40c002e0001c00710307200003414800d1201c1c01d908052403600000720001c3ca0102005035104241b00030b0a5103060802d5981c009900140a6005064140a00603222a800360402c21402210b80150f1440c0102e6041d000d000c08024a00c1d01f0b0b40740310814031034107000000800d8141032081b10260380e015a914045140710600600c207240c141c0c940c032810884c01200020b82c0c0103906003c0d007600c0c40001d10208590408203041e4140c44410382281002511304824803114940005680d02154003c650110381b00c0c618103c4402e42c0d014070755407034a8040c1488030002100c0200c0c1300851003842c40e61020410f9032200c0c103902d42c0e2070300308554101c02d0140d030300d1044010865008251829580c010a901c0c40c102d03588104500350b0701d4040503a0a00d40f42041800304100030b501860744c0c0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 467621043 1250 467619793 467619847
    0x9010914090304051c1518050d08040809010e0307031709010206220201180e01061101151401050912010230040302030412050f0f0303090c0a0f030b1e0103030302 71
    0x700f0303060030000b44143c2d90440548191510414603030041105070307210601c11050400040181c0300e110030b011200b42c1d080007000c840e980100050750304103074020741c0241d01550300a0080340c2007040d0140155441010f40c120180d0512130200004002000a401d115098403003103d103c4d1624071a1002a14182c0301034030402e10b2802843d01310807280d0f82540c0941007544c092074031220005171031900b55a4100640c2000020001c01d10010424a40203190386c02ca02c000c2c0402002445519080101046128007506400c494641a090090b620071006000721940090614449400c004519030880e808001819a0007140d016003050b40c41c0380707030000c10100d40203612420b00d070302d400e5038005e40f80d00c07450045040c040c00d9450624140b000800c00c07041001840d04c03c072607824441c0c0e10310b940d0302d40007168951850700c9284c0c0b078580c290a0100081c000c5800c0c1c0d030321000c481070471640e88206086005010000c5001ca102c0341095000300b03820058001c0d4003d440050fa41c0c0401410300c1105c4181d0101610 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 467622293 1250 467621043 467621047
    0xf060b04030f0308071101090605040b07030b130b1201060801150f0f0e0a140a0506120f0309120102071b030309060509030a0f0314070303050105040b090f13060b090109140903 77
    0x310340310b88546030146603d450702100503518200181c407203841c40d100a040300e619060001c1d0801025511290265019094041159981e00001c9040d2540f0302910f5400c107000c1e000c80c1048031305d2504421280c90006112641c600b000901c3e07207007101c0999100700026034486150703502c504030024003100901003414004000f9070515001c06060007251082c1090307400001c0014407001c0c1e2590084031212024920b22480d81088030420011382401d8807558491000c01c2c102840441c0005128540c03000b401024608003001c050030488040c500c00060700c01550200296400940c402529210890200c0210490b00342907040007031502c03000340c010303100b44a400c0096500c5603800040c02084181d101c0c1220a007882c01e460300320b808600b2100407850f040c001041c080304054064020905840040d101040200c03441003c1142e07400c015600103401d00a49000700351502c201c4400100c106018581c00308600603002d002c1a86010241c1c00f0740720300340e03455107803c90825415210540120080f00194 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 467623543 1250 467622293 467622299
    0x10e130f11090901031101050d020309030a02061f120c050312120601020601120f0303060305030a051b07030b01060503040503071217060a0b0f0a0e061602010f03021303020409060e0f010f060b04 85
    0x480f403e8044c0409085010805410000d50703100703804480943c0c5d000e50056440e0b0400c81881c07581d941100003a103025015490009404c5c0015a4007403071404280300c908500c8511303040002800e40c000000681c0c02410800010525840c01c000f2a00303403101000115588135840c40d00019902c030040e00050464015070010030403407400000741000a500200468042c0b80549400c0e8010314159100800d14040890b2003440f69802c9005046251250b5a200400b06019440d294481243e0f001c0103141243c01c0d001031002610400c060340d8001e11440482c0c0c9001003503120500c0740503294002c2c00c002010000700c10411703614030703401c99001101aa194003d103400c0c414050306c02e0040c24906500702c000451201d0095104101d034580c046d00180100e0303610614600d030b202e01c1450502c4103038041802140d04c2c2882521034422240d94120b11000c00c06a1421513003001f000d00072581061325280c1e260302040805400c1030024184070704080b000041c090601000c14801d403000d0354401c070520742c1c00348810 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 467624793 1250 467623543 467623549
    0x206071701051f0c0b0403020f12040b03010608060a080a05010203041416060807020703020d0b010e10081f021c061410051b0a050604060608070e1302040902010e130f1109 75
    0x41180a140684446085240f500c07044483c5290004003604282032036060200f0f041d00403824040c00d2080c02d0581c0c5080c0740044074800c20740f0030f0784110b0341302c80d108100400850344122a06a084140108a804150740e120200703840c00e030310200d0079201c503580001480200182401c50031142106000640007490a00300101d2800b4003601c20b003818051400c0005041901c244160b80195074000c0141c0b000003410304090810740d4090240c0341b201e54036400415062503440fa02481240c40c0c0400800c8800b6000c10203902400520360b1025507150203205e2158000d008034030580c2e0740e0021001c0000c11903d00584005028214040390740202d4001380880c44056210341125a01c0a07641000f80c41084c0d07a081c0c062400c444080090503500a600501003001502e030004811a5000b000b15480780e41c41e522080300c1c00200b41d420a03810000e001c014001808c242d04a000c04500505105455070b0080f40800d64520701e003075158619580e18448a903160b09180f05034000300d0144c8901508080d07001000c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 467625899 1106 467624793 467624809
    0x2806090912020109120c15020c0a050d080c09010804141903080726090c0603070c0201090b07020f1509060f0703201e070510020607170105 61
    0x101e465035881400341d4400a43c202010031741a5003450b8056a04000c43e2408852100c400000300e421504284060f160032802207020b03107c8020311785042030600c0c940e408208103015682c41030104651250041d02c03001032087c20102000e40740c0d42003002e400211400b007013542e8844c8a0145001d0720503404108036007407290700c4041094640680c155169806184034000b038036500c18110700381500d1240c145400211000590f0384c003400c55404248241d00c100c03420703008036034484010021035a006c2c05400007043d030100031a00300b4496a00062030714a10b000300c1407065200c082d500040b03051107404c071100c00d4401090260317100c0302840034080a400c54034080c0c01152440c50355401050200303226416000c08e12000e401d02c00d4200c0000b00e0b800b080140c12001505c103103480810701d601c5000480901a840380c0041c6103601d00844000e01408107103820b03407001c0300e429004128036113410386 = true := by decide +kernel

theorem cover : BRFrame.Cov 467446043 467625899 := by
  have h0 := BRFrame.cov_init 467446043
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467446043 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467446043 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467446043 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467446043 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467446043 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467446043 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467446043 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467446043 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467446043 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467446043 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467446043 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467446043 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467446043 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467446043 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467446043 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467446043 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467446043 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467446043 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467446043 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467446043 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467446043 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467446043 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467446043 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467446043 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467446043 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467446043 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467446043 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467446043 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467446043 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467446043 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467446043 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467446043 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467446043 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467446043 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467446043 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467446043 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467446043 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467446043 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467446043 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467446043 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467446043 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467446043 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467446043 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467446043 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467446043 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467446043 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467446043 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467446043 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467446043 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467446043 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467446043 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467446043 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467446043 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467446043 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467446043 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467446043 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467446043 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467446043 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467446043 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467446043 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467446043 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467446043 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467446043 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467446043 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467446043 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467446043 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467446043 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467446043 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467446043 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467446043 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467446043 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467446043 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467446043 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467446043 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467446043 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467446043 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467446043 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467446043 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467446043 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467446043 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467446043 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467446043 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467446043 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467446043 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467446043 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467446043 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467446043 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467446043 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467446043 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467446043 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467446043 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467446043 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467446043 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467446043 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467446043 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467446043 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467446043 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467446043 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467446043 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467446043 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467446043 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467446043 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467446043 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467446043 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467446043 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467446043 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467446043 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467446043 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467446043 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467446043 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467446043 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467446043 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467446043 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467446043 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467446043 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467446043 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467446043 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467446043 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467446043 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467446043 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467446043 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467446043 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467446043 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467446043 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467446043 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467446043 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467446043 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467446043 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467446043 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467446043 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467446043 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467446043 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467446043 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467446043 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467446043 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467446043 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467446043 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467446043 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467446043 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467446043 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467446043 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467446043 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467446043 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467446043 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 467446043 ≤ n) (h2 : n < 467625899) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
