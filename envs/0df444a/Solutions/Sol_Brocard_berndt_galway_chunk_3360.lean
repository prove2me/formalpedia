-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3360
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:26:17.668971+00:00
-- url     : https://prove2.me/submissions/a13f0825-3a5b-4ade-b531-6c73717c7acf

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 604136690 ≤ n < 604316546 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 604137940 1250 604136690 604136783
    0xf0d08060a060e0405040525030605011a0307030b010201230412170f0717041202010b0609060904180602040e0f0903070b010e073515010c0821010b040e070309 70
    0x100c1ca01c0704c103202c154140788c145c814400c01a06d40a0280101500806800c80c40c4940303000840303900000f8241030401d613550345100b24685c401d401c0460340c000304116004102607010380907000c0315011201075a04043e007481d07481c0c055100d010b5406a486096031074040380e840e4189103480815002c0c05820411803280340400c1c0401c000e0007818012882254002809103000c00080d09641c0c1409403103204480038003007921580c40c0d100842d014402c085900144650303000420000c100c7c046000500380502c0803402144e200a22100c441c0259241420382c0c941e0340e80d080800e0760300d205600c001010403040300f0040052500c8403945d40c1d00881a03040000e6901c04c2d40340c3e903040d15062403d449000c09148082841c2d0301c219841655045650303281c002035420041c0001030b0006218920082940c480001d05003503031035001491664810700c00038840240d580d02c5940250a40107401810040c0301c08101207030840307002c1c0c0310310460181d0182401d01040b5807500000c09000369100c01c0c99851a0701c3c2c11180c0c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 604139190 1250 604137940 604137973
    0xb06031315110a0305040b09070302010f030c110f031b0c06040b030a200d2307080702071503091109040b010611010b06030112110d03021c030204080f0d08060a060e04050405 76
    0x1c3c0c101081c0e41e0004451a1a0410b03411990001c0c01101d402d03080748a040c80540da21001502e1140d596040108200302c0c0030000300c50302c800d0b00403a1035090042082900c808107022009011240301e4031030800f1040e414600c1c06403103c00020720307103034004800c2104002c80c1078100e01031944141c0551000078040d58000380d400d180c0281941914101d200042c00300ca040440b8422880c440490400000c00c040c2c4146280e00050340c050240003d0060000010300da043c402c000010150414400c01c0e05a0300c2740b8200a0041c1400f03090441e40c5e01c0c0c000108405c20300f851200d40784520341004000025919118094544c40f000d420032900a5403950342210058807828001c60003404441002c0e400b2404504120300080f071040350a610400a454210021a50000d612030303040000c2006032461981880c0240c000b03100d0303544080024010703628241d10386032010a03002d04009464481081d0b5694100400000d92400d0043d040400c500c90380400c46424181e0195611034071032000c541c2004131400e07100 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 604140440 1250 604139190 604139197
    0x405010c14150105090c0f12041410050703061703090f030c15030402030601080c06040915090507030e10060605040b0d020d1107030e0a050907110709020301080c040b0603131511 78
    0x20ba40440e2120300400c20750420f884450b03403000c01d8481e03044c2481091a0000b50038810306c030f0315000040404010800380240020b004104c420344904590b44229000161b4014040c1118a400400d14050307001075400810780f622082c3c61902c50241d0b00e4000741e2070070007581c00600420305400d40b040f0201d10389a9121640420001484150900d0b280d14041c810146041e030160000f200343d40100901d041e40b80c444605840a4640380c6ca80072807041000d00b144620049071f58064a6194100302c1400801501540140014240cad00140e0340810344055455064031028030501000640412003001901d489002070140a030340080c01514143d0079a034580305a0b041804c8010781d007040015244209500106240c40240040c1d41c000ca40a107080001a08001d009141c0c3c0240b0030803450740b064020b410304c02e45000d0490100c0440d101d585500145544860010b5a00c4c05949017110400c90f03468a08103a070b1041111a00e8509031495564821350502800900c009035952201c03489820410214040c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 604141690 1250 604140440 604140463
    0x90c1e030204050f1009050d1a0a050402011e080118021905040509011e1512090309080c0301020309070501030908040902180411090307060e0d0b090a0203210405010c14 74
    0x982c50750b003010100305000391105031440c82602400030400c07030150005c04617400c940040700e0003001d8400c20705009055070560004070300c0c50141314003002410710090b4070460046000b0303a03800304641d01030703650b2000c4d0303c0211242001043e2030000400601020780522441c01d0328400016040412046969500d00d64640c082c0d000300d500030405100500784558900d004007420301000f506003904051850a00c000c0b4040c910341042c0384000c129405004034410f10f1441d4080c02e0400035007001c1c1c00c0003005c419050140c80b40502075514900028a414000c1d40d008516550240501074034010044d0000d10b01d100301145c00100a00001900140c03074030190001070300003a004001025141e081004449403080030003280340c0305010407036407134600169070020340e112070508101e1000b0800c009504000c40e40070080c0700785144410802d4082003c500ca003950342c801c0d000c4030490030300a40705245e5000c0d214056500d20b40244400c010b50340c0710761181164580104a02c1342005102d17042c40e420521b01100 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 604142940 1250 604141690 604141697
    0x17061e090c030303101a04120201050d0222150e18060d0807060606030513050a170f070501021c06060c0312060b1209100203060102030702011d040915050603060103020a090c1e 77
    0x3010459007662001512500641c4961b15103410b04000521072101c22000b00a07040000c081a4101641980e0303040381d0b080504640710f414070b040c1890580e264040e580c06024002c40b44201a01d1a0502800c408103503848020f00c103c50005010702d141900b200c00506103588a0900000000400d0394107004098035402040d0205500d4140a030141c15102c0240c00c00d014000300c420020702040c0d01080c58071000d90b0202c043c120100403404d080c0b000d030180f03418100c181071000403003200b0414158014210f040040050601d550034046904089030354520451001c40c03581d02030040040e1186200305400b00300a1000511540c803030b60120560b030403401ca608000348910060207100391040066000040c00844154950b140110000791607010381e0301c0c000c3c180445801507c1400c01d14030120354103184040c00030040b8a1241c00c0000c100a101804017025500d4540443d240382000b0900d0b6058030307009020342c02010310b8211440e00400380241042d007003002551010100d402c145210724941036060b603 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 604144190 1250 604142940 604142971
    0xa030803041a01121a070905040f09150b032e0c11061317070309090e0109031e022112040309061710050d050a0b010f17061e090c030303 60
    0x1c0c841501e80780e06801c0041e0625004030a080052006841007205d006403466049094441000595a000564000644c401d040007044029620b160307001c3c012550081c003005440d81c03800c1400c0e0040766807010702c0642541080c0d82c00030451014007881040c14a110604036201000740403080c00b12003040110000062585803408002c1c3c01c00c20825801141032070f10f2105071019070f0745e582c0300c58402205000540801041c1041854050b804080003007012040520000d603258513801c2c02405550780c00c402142541080340107110300d070a031000e150021070b00200f90310b507814039000305200340340601d52004130342c1001010021b0350842e442d41d0260b442a1140a025800c042c0081d10b404041384655045140d41c1c02049a01d15100300600110f45007615000b240c4005400d020b03040440c03940d00641019810310002503a00001c07110700c1d08840390f0048003001100340514240d00c82d441900e8100c0307210030015203102d410300500c6850f078011244400300c2c0e8a03c2071040c046030468004a5112419a0300c90 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 604145440 1250 604144190 604144223
    0x1009120305151807110a1406070c110d0f080a02060a1b0e090405010e1519020c030315030f0a0609110339040207200f0a030209060a03080304 62
    0x10300410707401101e0300c408004800300b1840410000c200c540c1000015840000228140500074a80300c450890028265028030b46141051340108403007048070501441207000003100356100310b51100394258031024200407502d4090421405095140d01a2904001c14581d0000100000000c048902994020301490b2800300c0c940411200300b5051414030040c1008a144400d50010340007002c100103ca9149040d00c660400500520b03082c0080300c40c40c81503030101490000d001035414812200f5440c050742500c03d107071410060740a844114580d95100b03001003012040305500108403514041d0403a40201d41038141503141030103030301c0183c0b40c0d190b0b201d039070300c0c00d006088101540342c07142600240414005c9661002c2e04942c43c9480c440d0440003020080341c0c1e10394030083c03c0c0940030018001c0d03444507050705041d440d182d04c000c01d2010040707100000002074141006c0044113010010709000c0c6940c9035800348203100c1c0d40200032070340c032049000c00400015142c5010b540224024a2009000d4140 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 604146690 1250 604145440 604145447
    0x1207030507140d090602070228050402040b190c020402220b0a02031c02040509070e0112051501030c090902030403110d090e0a09030c0f0b090114190e100912 69
    0x1034030707850811010320808402c0e41c1c00700d4122844203641d440002200d010170f0400300003c1c0640c5200960002507003116514034540511010070b00d030488511010055942c42c104412881980708140c0809814484140c40c14014800c0d4007810b03d81d0b0410300a254001d500140807a40550076092844080400c902041084104000054640c003100549450208c03100607640e0301595083c9914114a82c03003030303500620550150b030000c00c405081500c440c01c141201504c6802ca0b1041140040d41200c10a40c0d0702003240145070081c1c484643ea81e5003503510100440182085420340c0e02805010000011600c2e00c51000f148036502075036036054074602105004d41031075005600c80c020840e51140600a80380615109600290480d8001540d000603150a5480203c0200050017402078031040205000075000ba02d031003803a22000800400b000210401d190082c265103064814003c12080300e03200d180e0768802356400d10080112440070031031000c114143c411301913040f40c8884218540303040e0241c1 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 604147940 1250 604146690 604146701
    0xf060501090803040e1801061401080f040f110103111605070e041a060a05030102190207120305030412020f0d020a020a0b030402010e09072c0307050105043206120703 73
    0x91a04118142ca089640755036800f441c0291620145100042604941114250803000000360300a2000e20390b168800040c0c50002c40c565404188000c000441b010f0440d00d4242c42103a0109910010000307944070072040c4811401d5142c103040d9903e145035003041c8200c01503c620503940744041810340b040d06d081ea04003540d0360700541c1d59803011401e100c0050710f101d4110341e50000354400c10100b41c0c3e03040e00294414515a0000b41c15510002e101e01e4100700200403080e201805800b10349107244d8a02d5407006552381c9180141c0080e0003400440c0026154035200a100986441102e124001c002c404c14180188035445d080940d01c42e1610f20118140884100002c4c40d041c80490300794034040d00042c00300c2c1c0300380c4105031151303520000240c641070040420212702240c0e124060b0542848902c01514241c11034542c41c8a41700d20140001c8540c841c40c01ca505039410070150740c1001003840d040a07100030140a18070303003685001566401949030303600130f4500210060b40c07040d80341c11320103000f41c11600c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 604149190 1250 604147940 604147949
    0x1141305030d0f080109020d0b10261003080d3e0301060c0f0312051503010e0c06070f03210501090b10050415050405090901020304031b0b0a1113090f06 67
    0x1c00198490700c0d213801c0030600f81141c0c0790a00169035540d0080409000748454480c4030340c031200c03c00261000701d60021150011165030040c80c0000781c012003014409010496000005107203443d01400020350050180c040c003244087d000c641c42e400303111500041074030a42407210001800320784540b50056201e078600d810b2440b0030020b180d035041c43c9004000340041e0201400c20384002c0030072420144901c080c00c0762004c4408080002d414248000007080641d803881ca0303c69820b06e010040c801401180350011b002d4020b061030300e4041640d462401a2000900942c140b0031100e0b000900d17400708485209040d07103400c200161940c10040040100c1e403140f106a80100301c403034899040c0507007003030440e425928202e145850041e0810401c45662242d604003030b400009500521841030340540155014500c20b0321174030b07024218511031040d15440120098604003070000170504c2c0c440703075500c0207a80d2031508018030306c0c000d01c0300784448020710f0030f61007000c4166031401040d50043c454842e180260 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 604150440 1250 604149190 604149197
    0x1090201170114010c05150c0c01060608060d11030703061820010206010b18031c0f02030304110409031205041101020c0f0a2112020718020906030708040201141305030d 74
    0x650610083d4550403410310700302814040007405038420301c1700400c00e014403054100400b1000340f414144480f640d40040c44c0d085800d40c200a00424074078018900305108143c040c2407800507814948440034101c80391f500c104d806000d01100400800e101d409050194519034010007140041440c04040c0b000740b680b02d000c81101d0a80e0726a80d2aa40071441904440d44040c4143d19560030198082e21318039010b0103650b05110300520002d4141c1580d00082c000c0d15035442d0703c2c0b031503078510b60140d80f03901c0200d0b0010082c220881c8028001c0c0740c154807800419005c1d240029503108520050b0046900a0794203a44004403101f0706113440d070b410800e0100c000f6040c1c9904030302116078bc0205007140340b1405000503e05e015028000c400760b802d0506842941c100000c90316683c0d00c2c100182d01d0303500c01d00403540c000d00000c1080c0c08800701d90003120b070f039550064501455651080011540312074040c10481c10400100303441c440008080010304a113045c440d04c410820b40c80d0204040c542510b9481c0345003030 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 604151690 1250 604150440 604150487
    0x1208030613020301150e062106030d45090e0601050f03031c0905030703170609041e06240603060816120311010c0f02010e0c0618061201030501090201 66
    0x1340840c84034014150410780c01c10303024642d80800058054010102c6004082c02036018848d41e90f80c1c4600080d020b02c405074103460150341c4c00c43c01141d00c0c171000d1190f1800350140840604050682e0107000c01d0140d90010341d1b0b0300c10050400080c2d07120441d0743c000c0e0001500d4075502000000180581801082c00303c541109000300100407903242d000b44401280005915008034100204a42080e55001d0740304080e13981d140d0003440c0241a0400c80d004400d5111030040003c0e68a0a03c9816680950b400440c14038107140d000342610700240c00c40354102d6510b616045c0c91100c0121a407100410900c904002c07510450401100a0456186622242465000304900c000080103043c482096034285000200b01c100e041c10706035800d04a0a0000085601c4c25000141855121161029880eaa58001c0c0007200659000e5580d4038946461207038003000030000014100702500440301c0c200700190009042c11102ca020240f982000d83c004d844c0c2d65194050b81c8119070380024600c2041d41e140341e40200 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 604152940 1250 604151690 604151699
    0x3050108071a070804060c0c0e0f0c0307051e0a031107080906090a08030705010b010e06090307260102161b0e0a0b0d0203030d060e0a0903020616091208030613020301 73
    0x680388400d1040c00e562110b0302c600300c0a001032400840ba811900030504956a607a2108014040e0740e100106554610512030301054541c148007056005050b02e8840110503281c03100310a1040d40068020f0080c8007040104e4021f03070700034545035040c149026484a854075011800074080d150310300103640c084d003010050200010354040650300081c8081c0c80642d2902d020700701180a120b0349800903030080c03101103107140410405411204806400782d9030446624608400c1c02440d00510341c4196164110030014001640d5449030140100c41007000302c0721608440002780c0c02c81c1e0010b04006188107190b510b280c00d02000608850315507800c210401c1c0d080340f60001c1c040c1c94203801f03084e981c2c3c003c0e11041d4454a0340d84400241e1029a001810b0f26038074030546400e44010311851040702d811603001c50005106070011710890b03460a4040d0054050303a0342d00910420407030b64400081040c0088650082610340d0074402c40700d80360744a814299500d050520802120407410380300b00d550745004100611 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 604154190 1250 604152940 604152943
    0x12111213031104020f0d0f0b0618010f1e08040b280216060509031803190f1703240a060906030504020d050d0504060e0901050d1e3003050108 62
    0x10460b50000100300541407403a00041c00303441550081d03030204401180740c0d0030042d1039902003818480b9542c0f0400600e40348009104a03070150140150b1403544210304414654021102c04024035400e24101d0684003031101a0010111403c0740e280001d09503408100412881600d542c0d0065143c03031100071007200399907008109259101c0c5110550b5004604c00d0311000305071522003045503008400f404540380c010f1120f0340ea500b0200d061100e0818000540c14182008600f003610140c003a4000c1001601070707140c001c2d2040411008950a04c440700d00c00d80f000c00088059401140303000c481000f0480012581d4204044110103248545241171041180c9504902c080702120050f042c0803440769141c1c0005a0240c41c3d50304081c10314000c141c4200800341e03210006005440c40b58884501d891008018003001d48400d004035504410052030190100301142070014407203132900e400462135080e40d5984a552090141a0350402043e050044007512a01850b02e101840c6071504005942c50b001071113 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 604155440 1250 604154190 604154227
    0x2010c020f0a1e08040e0103080703020d1701140312030403050301030c0807060210181221110301350703020a0e090c010503060301090204050f060405010b07030914010c121112 77
    0x281c3c101280755801c0810400b64a080c0c07001030400300d201644d03070340e07603410603450a03808518120014000c4e03889112103c9e0040300f101c18401440003107a1101e0b801c20354600301c499402021301c1e40c1403103007010140d040c0c00c0286c01544214840d40d103031381d129451498414036a82103604000c0042d006040140407843d400103460f0f84180c02c40e84041080d0710b00c172070000710091640501414203109409282621908034001607112414140d45404103084c08001d1401c0f03400c1820410040c40741003004201103502818001440301c00001100030341c016001103481c40007880104000300c3c2c1c004070b10401c15850200c05000c0104401c541000c070781e2400c411425100c00001c0c00c000e040c408088085920b1b520258002e50080c0e030f0140c020022800e240740c031100c0184d811100c00340b00d00d003440000b1a0100d031030b406a074800b9072b00d6161083e980d0305001d540c220b0150740000031410090b0f4404c4980c041200c030190a501c5020310384480d40c4110508110740d08100d4410880c8001c40743c100806044070030300c0d1039403 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 604156690 1250 604155440 604155473
    0x203010b0d05030d1a030f0109050705030d0210020a030b061305010e011e0311040902070b0f0702210306151810090812070219180e010605090105090a1b02010c020f0a 73
    0xd4110a984c1706480c00c40c04e011000c5415202d0040c001a044c0015405000f01c10301540403030301a00d640e03404040d50b03501c607200c00700c3c010303004103d0109009100b50040d1081c0c07030071818040741040b008008122079070001c0844140071510780c0c1c0304106070358204107114070480c401e10b080c511480d03540020310131060000ea091701c10507a0796080500e0b248001c006682c00f0b001c0001d419592603030a81010a03452034156180301a55296101185030385000140c491203824641e000c1030417143d908441a103007a0001440d0f20341044080c802c00040d241040000d100e41c050850b400260403041c20180404560512204000e210590000b03000d484000507081d04916603644000e640e0314810f00c04900a2000e90b5440e10820b0b02e80040800e2aa00000d00c01c10503404842c1c0402265a2100c00b89080c0c981911400ea000206d0f1001070240d400d10303406891f030051004001107001c41c080c00c501314001e410401900c3c0142d40d14902d810710a0f505026003407030001840e0040c18600d515803203a181c40e001e030100 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 604157940 1250 604156690 604156717
    0x82b020102181c140f160518070e0607060903020d0921060f020a091509030b0708060127060e06070503030c07152d020307080610090504180203010b0d0503 68
    0xda0340200640f0603500444540d00400124954140d10303051641c0b800150300340500390040e010520b000ca14400810785c102d0390000c01c000c41070140c00c100341e081c040c07020300088104801c004042d5115110340c00140400340c030802c400038001e01a410001d007442c1c071141c00e200400c0190a01004500302001c1e207610040c114030907151501020b8a003540080a04030900701c00b0500110300e9408045c3c01c041400c013128444082c0511002c5000c0044541051901004000942c10804120305500c9900f81e95404441030510062200c850717819901036804003440c1150320758040000f4451907030300121094000000f543d0403410103007541e4440c0e4507408020202c50041e803000c20264140050341307031684941e84c807414080001707035030520b810f2049030110340131203119103c82008600308103924800c030303442180c080d9291461a1544c008112030100c0c04108d190030001140d0011405950313504c52803d40c100c100500071080603061040c1800e4401d00b0544e02d02c01d107280c0d0031041c0031075004022622a11846070 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 604159190 1250 604157940 604157959
    0x50405090115080c120d09030f111e010e0103060b03060603250801080c010e0306042604090b0a0f0b0a11031b0102090301150b0405040e07082b02010218 67
    0x41c01810b0035078511040c04644400090b00a0f804159040b03c04002c1e651840a000c010100c941d484000316030900000d90580810030220b140110310419151040c1c01954140010341c00003042e80b091a000c4450400030908920607540e0842501c12080800b07003010320589152411981c83c0d800000c110b80d010305000030004a0400b02004070400d00c0101810198103924101001814441d003400340200381c4c4601e100e400b21541c0a540c10f40700d0385030001c0003001c00c3d40d15503842c21800f0006068940b8525088002070001000e41d0016101a00c3d1010001910900c0c50b000c205040d08160302c0078000b1011079505202c01101b5800b116515407250404a8104504e40708032443c1d8441c5958280c42c0012241404102c18010b40040c54555011030017030080d000c0c8040140d01c0c41c10640314000c5102810041000103040c1500a40003850034030040d0345055558400c06170500e14100340000401e070b001c14000700000b9000e101098001c0492000710300305080c04820b1349088840300c0c09030348140d0415 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 604160440 1250 604159190 604159201
    0xe070512030a140409020a0908010606081501050714010e0a050601091506080c040e0103240c12180609030c0b0108010b1003020d020919080706020a0506072012040f0b070c050405 78
    0xf0200c60007410f03c0d942c1155540913844001b01042901d000384411942425030000b43d26204402c010b024500d2481032130b2103600c1c600015103855000318001c503030030b905072083d02001c42c0e020b02c10b80307403c000090043c1c4600b80720f82c6450342c1071806c140c000812141c9403000c00c0510b01100103410050307450508000034503440b02801c4991500543d4022044008901c001200300a9141e00306454101d0082d40d4040d0b00103042c1d491000c0d20803600c0c1c1e070b4002441c82800880502901d421030641036071900c14003510080e25448400c01e40d004508180d000c0b0725186090002c00c02c00c0c84e0351500501c65140204a940d41a40000c0d9011014072141700c100f64000c07070301140d40c501d00d9044440110004090b005090403c51080224409a00c640440e0b8004d005000035981e0000c900a01003a6100028000795030710920241c0701041d40c010500040354112111400b54803042101072207510719084080e8480f0b107005020180e100e81d41c7c100c49100f0780148810f4000400c03050104080d20401c840200350b543c1c60 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 604161690 1250 604160440 604160477
    0x60f091815160f0c0b1f06030b010804080d0905010905060603120a080c03071205070804060f0207050705060309010603080a0203030a0609090201020a0b04030e1309020405060613030807030917010e070512030a 91
    0x4c10068401d140c41420300961412001b0340507194a9210807074400ca0740d0f101d4058080ba01c40c008103502142998000900140c01900144001040a0000900454a030301d0745821184062002c45465000e8414081c240c9003c1109002e4000c021318914a00001e0700b00c0240180381c040c1c12400c0c5075070040049540710740030740d91100341e500c4110801c000e140380c144001003200500782c60a07200d09107000b808100b88402e60080f50003441d0040c0042c04024900814080c1c960f00080400d801035503600f401100041c4054010301e1010785130f90003103490b0705000184004440c1954001c115803441c0116840050f60041026610750341c03c07030840340d000c2d5944e09080e103010706083d0704a90b2054040707440d060081c2581d442001c50302c2c0250303010441740e03590b036080c42014458031140401d1280d1090040001901c0e2030300900805d03204c4d203090719180d0f568005140c440112100302c01020317516415200c01d00072003041000010070045428003198400d0800742030b101d1103050305950422007601000601d130100c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 604162940 1250 604161690 604161707
    0xa08011e03150e19050115081c1b0210050d0f0533150408010f020406050f0f0403020a320112020c0f030a08010806090a0317060f091815160f 62
    0xd1315000b820540489203007040c002c0102c104120300010590001240d000b00c0000c548032800d003d82e074404c252107207580c019a80440c2c008480151300000301540801a00c404210703d542e0081e41c0c690a80b58812840c5100c25078440e030800c3c0c14940e203000100412010503482581c8100c5a25004542410b20324030f2503916480f14510107600111000013006003400c404005004407881c60008000486003070a80070160b10443c407030b200026200b44170750110450100003d2000c4200761031403e2500d552980858030b10502c41c2d00c8084141c2c0601c0402c8040c5520740030210034810010481040c2038000340000c6c0c003c00b0000262482036a01150130503642f80f0802c40d19001c03800c0b40044070b0715071100101c0246950400d020392150f501504010074a0000001240f20701c09030706483c0c040920780900c5240000c003000a1005a204500c40d040708100d40302c00790f24031301840c1c0f00d4200f0010040b071460024904020300a612010130103c004200f0b0710b150000d00341400d0113807803a06900031b00120300c00302c51484 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 604164190 1250 604162940 604162963
    0xa060c02030706050f073302034b0403090b3a050103150b010207060c0602070602040509070f020f0a020904060209180c070201080708130b0a110a08011e03150e 70
    0x4281d010440f44a03550b9890200d08047c0300750b4509407102ca243d0524007680026a6440a5464801072082079007245a203801007858514080e59101c0888000030403040c1504083c20702451000b806110a15034462017a50240c4400010a440c1591103000c20140b00d078460650f030032079180b01c03101440e200e020010300f0503114900c0c04280902e50b141d0600c40142d44201d4048125949000f55a042c154008900312040755802d8468000304c3c001521010b01030350250350221303155a420000880c1c203684015095004000d555220318103889507000181c541140000c5a0700650f110340348080041c0c0d2445107595000e035000002588918059002c558100128402c07d088000c4110421802c1c9203901d01603d00c1d14000d0340d4402568844500c1621080801e0307600e0710440810b002c43c0404222280c2c40d2680208400d080000c032800d034041c1018464004030f0380b03480041d128500400c060321440e000c6001503409451490025403031039a403e4203c4001c002c3d1840103e0b1a0144c0014601050003200210f5 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 604165440 1250 604164190 604164203
    0x1210c090c0315090c080f07020106030606030b070201050a02030105060702061e122d0a1505090115020f0303060604060c03050403021c060e0a0308060d05101a0a060c02030706050f07 80
    0x7003121000140c0903103c4100c10b285083c0b050748000a044041c3c3c01000d01041e15500c450109403a8401d11002e003c20080c24841550f481c0c240c008002640c0d8403404e001140100941d003032508010b90000d01352803010b00a944041c0c010310042c01f050303a81500b1034103942e5040340d020b50789440903c05c00481c1c0003c2c000414103004080b6035260807100c07064100d8441c4100c07011003148001140d12684459800303124902c40103400303e000841d800381e90b0b8480320a14005000b160325581d40c45c40040d4600c5000d0300b11179500c80d015803000c80c3c2d00da0104070100107100024099410b501d4400081042401181b069400f0009940c090b607003030601841c112000b964020703000e42c84c880b0400240c40001c28901c1811566945840e11030b031403107080828203000c1ca543c165a43c40c203540b2924104042903003076403005e40b00360180c1c00401d00e2021051051010f0b61078000b00034a02820030500f00210f0398900d40c050001d016049081000695021880307400b1b0302c0342c50400e0391721030701454904c82842c0103106006000 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 604166690 1250 604165440 604165451
    0x70905031e1e032208102301080c040f05040b0402010c1e03051201051915050c061806060a030f0303180f0b0901060f05090c1e07240501210c09 63
    0xb6040c040010501c0110410564002c4414040c00d026002c409100d15042070b00162014641a042c50b0820602607051200c0121003210783c038620394059400307030701081c102d41c00241c12990a05040c0100700003410704034000c000919050321030800600c00104020b040045501903c401c01c203411070003d584001e401c3c00000c684c040ca142c00740c05544000c80440001040200009662400002c44803040f040581501810740c5000d00b100e007078550801e081011b01c0030a209018410b201000100d106001c0310000e258032038002042395080c40c5000d026036019102480302031000c01c80c0c094076800580d5240c41c3c0041c64401d41c0024400020340d8500040c01c1211286482003071107a074050440c05051040000c000540d0b0364071040e100380c0214450103400082950001c2c0400d0317170b14005054400303030443c004100b1240380b2003c450954407000d07040703030031240e840001e4051179440c2d105940700c001402c1d4100722a50604078520084030309a1721000c4032903441c10080e000c000c9118007000c018040d0b440705100 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 604167940 1250 604166690 604166743
    0x3102030a210914100c080c0d1710120f050c0d061b030506210118080a1202090105160302120a030b1c110918070b07020405070905031e 59
    0x1208201c219034000080c004070b00412510b6080c981c07192401030040c5135444120750740c18190b85003400f154040c4d80c6603200b0700207a00a40300900060700400d00c175075944540d8005a14040b00b02700800341c0146950a02c190050203c0b1982c41c1d1052044e03a005450b00001813a1032400710b01d0491603221040d0800b1255805030200003182c0c002038844d00c080d003ea40304846240c0421000c070740e4101c56a5030300030910b5400100100c081c40090b03007411180000841d1544c4c03400949501043e69560440341ca8100040310801c0e540e00071034401030b00c2910982980303480105d1000034600d004403c1c17017a810450b030b0300311503007054002c10041105201100038651104a0803c000d402071410b89141c43c01001814a050000780310083c0c50042039901a1071545041e4044041c08010b40004000d8000c0e1021080c4c02244104200103d00c02020784415050341c03045544140800d84034040c0210003800fa40340c5007846103139004508410341204900028a018408050f1146030242c882151007030420405d030583c030f = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 604169190 1250 604167940 604167983
    0x2a0b0c03191107030f0e061605030c01060303021f090f1401022a010c0207050a0b031305010608160e060a15050d05040f1101020607050a081023093102030a 68
    0x49058045d0325944101081c264043d560402c142c501e140d4041810001d00c05401c80d003007014200307140101c0c00c89081254049034282120b540360800c0c1c0140e0301c0444601841c070300c002098400003070445414468140c4503502c001d102c1d50f406000600070761040741c104e403005c1d10942c19079425a060811481010031344525001c0f8901c03580f0040030155003000004040c00c1d0000602c80b044800c041c10400c1c02a1401c0244605900045d0540c44d0303210000361503001003517003400341c81c01030400100a00300d81030444000c201c4034035460b40400e441c0700586080100c0e564801b10f001d022504900300c00340d200810f0301c0741101c1900c922115100e08600e00410b1100b4410b00010b0b0749506481050803500e2281c0100041e6941c010403120301e80021420020301407401e105041381c1da04034000031b40b4280c1160702c0d54884440182503900307014000026072138402e028603000034903d8010913041031241400c440045580c3e449040c1940402c0d400c02c090940307008544040145913509074200103100180642c66001a = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 604170440 1250 604169190 604169197
    0x160312090615060203040b090906030f03040308030f01050d0f060509030d2306060f0301090c090b04081c0504060c02010305041110020607030c09050d0b1e072a0b0c031911 75
    0x2041480c0060000f140d002d00001c00c980c250b4401708a1142000c0c0601c082010282c1d0050400f0707058041d146c451420480308001520103544a10030654032880e00401c1e04900c40016448180300d81c2c3c0d0003801c0004254180d07144a80d598108002003030954506101510394401e0111411001e454100500017580e40d40d98610449040000f00443c10303207c00c01004254001c03601805410903040004212580159000400c8110300d41006440c840c0e89014a440e680c106500c41c0c3c020360081e0141481d441c1088142c0703030401c070160410340d0405050a40043c80b40e400300d00700905055407140807a090241d4511548442c01c0c00901460b4421290305c0002d44400044c1c0742d500101c0d04114445402501400d03601c07061750707005003c0954442e01501d40f15185000a45100c1d154880c1454142170b04c071540d8a5107110b401c0e04d0700e508504410008802641c1202c00302d5140c205560720254600090076135001907042400c0d1440b09032651582c21101c00700c8020390f222032802500c4c00e041c04183d0300c40760300070b07 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 604171690 1250 604170440 604170461
    0xc090f06022103011409070c0206070c06170f1f09060906150806030c1509370f0b28090609082d010b0a0e091e031603120906 55
    0x86001c80c511220400540420f005e9002d08415a0040103024105070007001ea05c030a4a203004124002503030086034203540000c0080d07502034068002030080c141c001000294000800540c8803043c9000c2d610a614000043c081d40440750729a0501581264048040070203098494130400841d81d40300007050003412180b00d024810314042c03145d989203a0151009900c5000013074050030380c0641000030481c110159002c000b005200a220826243d11040002c0e80b6141034011001e015142c0c0303207481c640d1407501065588001448003020300c000c19036a001c0808880c000c9500342d45038200d011016015004c241c5449400c00030506010742c800d60300900c0303072048821540351103410503241d100d01526900640070403030055501a4082c80f0417040c998a6141c1103402d000002020800700b00041d502e200d05500100b5549001424040d037000140051040480590700300c02c0e00a90503640540c8a004e070003049841c840414680006042c0140003408a540c0c042c4010001140145010030080222000c03 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 604172940 1250 604171690 604171723
    0x190b0a020c010c0c0302040b01030f050a0b030c04110711211b0d0506041101050c070b0c01181703060103140a0207060c02010e07030609061401030f052e0c090f0602 72
    0x700000594081d81e56003080c80e07004054210b11034259024403000e48404440c03e8101541c8065042c0d0b0344096202d81030040e40d00c03801c0070510b01c0500040500c7c10440c101d007144501c0c6400d082191304414141103079480e9030f100d4901410240d1000c001950f41510340c044c0407030526200c2d0700c500020f5020508810115001d90801102a01d580a01101c0030b01c0c046c0050580e40703c0804100402da194114140302101490000e1600d040302503498108480d0b540190303070700342000c51045408502070152640c1164204446110702c50951260701c02c000d0080072484405200102144c616403082d0403880e900c1c3c18820b00c3d40c030142400c10103c4007e6022820a984462809514125461060040c100c070648004014005d01d42152954401040300c54000ca0f025a6144001c0402035981c0039080c0c001c5000701c9050340b2013169030030b041d820312011480c40100403441005000f494011004000b6640e0000f020028240350804030a640107803c0d500103241240001400144150f40010300c007601c800e08a0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 604174190 1250 604172940 604172953
    0x6070c0e0c0304030f11010b0316050f04020702030d0f02030c0715080907030b060f06070209090106180b010c0305070212010e03040501140c0c041e1e0b09070c0809190b0a02 76
    0x1c081c0342850009640090010780d005032260f400724030400e444115a48640c0c000107029004030006898070f2803070000c0782c1590250003070811191030000100007030b43e102680d055103044003d03400a43c07a0700701006001c080c000c00c80e0403086901c0c070030029200002c01c0303078041318040e9444400c0e200720404a0302c01d500000d504000000c10007140400c500c0c0c100d0780d21580f10040c1c1d80710042082070b04030114801e0360b00300c032003849000050307500c4031302580c05403811200028103e801c1241105c841c50003403116032245801c00d0300c8094241d03400400111441d4062401c2d9071182024400242d8201051454081315030a00d03048cc101c028020000700102d4600741c030780c005400294a1010380c00c0c081d900c07024031907800601c03104a19040c150440c8111603682d480c0c9c01c10140611024070101d900c100104500948001081c1c0c000035014800d423000c4241c00c807506030081c40c00080080c422040803400034080f03440443c0501281e00d500945105040c0c0184107805280c0e00c031a503030a41904000000030041c840c10 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 604175440 1250 604174190 604174201
    0xf19030b01080f0c070c0b0d05060604060215060103020d0221060d17130314010207110d0f032d02060405060601030605061617030a0c08060102073206070c0e 69
    0xd1080400c91031040c0c6a080c495030b5507040b0000841002003624076038600070451a07002407100700f41e480c09000350340a595202c07031221903203604a0300002c009902880080200f48800381e00090005142c5404d0401c0c90b0b801e80c2d030040120701a00544c0350300d921302c900211b4151190640c0859a0129490340040b00401d030303685104102c280d02da25140501440c407103400c0610030b038800b40d00625a540203c140c4a00e05940c1c4d0340c6406203000801580e00482e50b0101d94901003044540c403a02c407a4908a40e00b8000c0a6651210442a031030041d00074184803900c42180c1c40c1240d40800b030104040b01c1050f0040c0301801000185d2500340c02c440440b0b41c1d018603c0000c40c81d41c020722034142030300d00c060221820301d440c042e08c6040fa001542010b644207845100401c202c1017000300103510400d070b418008120a0300da01030180485030701402090554204c2107090002c00c0115082c95030792401c98260020a83e60035135605400052140100e421000c006242014801c56185000869a0000c20b03001c1030f5452 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 604176690 1250 604175440 604175447
    0x6090326070f2114040909050a0c0303020d080109060b1b070e16080a0903020619060e070923010f0c0804080303010306050603060702011109010815030604121812080313080f19 77
    0x135a510720390021801e1001b401003c8a42e0b00c13400c17500744204102e40825480d9100d01d5440c03041c50b031080b80181e101d940300c080d80907840484070b4014082e800d0107001690410b180c051190144d50074682005401d002c859000321030400255004112601017200c107810035101c0c04460010702c00d0f00d031001c21a85000309162403070034840c41c180381e50141d0242c25251030748081100c9180c001180c2044580d110100403401204c2109901e00404080e02c400034090320780848568015403030021030b4110b0402480101c80350340c000304039103980c0c4028078240f844c800c170310320b060316aa0049800a011610001c0000300c20403981d50b00540c000c00b0304038200e400c2c42c0d83d0560100c0c2030700c040e08618004240140441502d80d400303141c51903002041040c140034408a0540442d2400e2802c4030161610761000996041c943c1e00180340c64102e0541c81c0d4010350440c14040c03684c0c2903d42125000344101000000a012121826071452180d0303407001815641d565040e4a41131a40c12295001c11001c4200d1103080e1041e00 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 604177940 1250 604176690 604176707
    0x2041e0e03090d082a0105161e0e04111c1d0a0b04140f1005011721120103030507171c0c030209151306090326070f21 52
    0xc0052068005280d96604c802054000d90324003e280030502c000f4074a040f00798111401c440000d0710000444e403408041802040503800c0d01c14051000202c10644405521040001c400307040d8184610804074001c0807400030624605105002c1c0d101103104820889103041d40042005101c00a0045d204145101000301582c0305106030558003a4410400150211100390b900074040d0583c009441450580203007003213201001c5541c2c541144520140708010b52041c42c0c00b5003081018000c6110600d904c440d0b88100840c0700312402040d481c0d8007100b560a403002c079002d0b55550380d4001c2c883e5a407483c1c060b080c0d03002407030300300d900a00741100840c04124180c2560303092078240d2904801c0f606007140900003802d50301d050100b016003c00403001103803901c18801c40c2c8001d810540680d9400e030780156030301d0182240c015404018420340c0400100d4480340a945003181185280d5021003400d0700c0c0c0c1e0b01a40310741c81000340b00e10710f10460380b0305010f041a50b00c810702c070b04210301000040301040c08544442 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 604179190 1250 604177940 604177957
    0x1b0a0c0b10081902010e040509031b0f12030a020910050c07080316060207020102010905030f04050a1a1b0a021f030507110714010e04151a03150f060702041e0e03 71
    0x501002142070015502d003ea4900c860044c1000c07420f9603020004141951411208080c96601c00502c50342602c011911403401085000060110350040104094480850500e4801005004004100350808550440c0c0e40060000c1516861072500400138100f60042440140740703000744400000c0c0c1d00f0b004800c5401ca110038020000e003032803070740d0703107100094210582c1a81190b5803a406c00000030002c01c004c5c440016940306050f100ea1800c0200007892440e500010452460401888000c0c403540081d11a0551080e464440340c44000e44141e2904c01c080001960140700380b4229184004202021240b00c0c0599405000759601d040041d02d08030114818007070070381c0c010340080150250640c40518071050501d803e511550303454002406403941c98030340384440805040c04000d0003020201c0c00e981c140384010564154a0007031800c0c0a04904200440d000e040041021001c1d6990f60003203400c42c1c1d034000d000b04403040e81d611302203100f43c1d04030661844051502e0708404404000000351010304 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 604180440 1250 604179190 604179193
    0x111206040b0a090f03270e18010218010302090d0c12020109172e0f06050901050102070308040b070804083009060f0a050f070803060a0902041d1b0a0c0b1008 69
    0x140c0b110385d41180c0102100e240101c03051101c11070841d0600c4628800030041a0341e02140b2014100b141200c00001e0402003000110381c410840081207003400c4e410b401d0191001d003001078860706030300080780f0780350410003005020103040c000c00305200d101d0b6401c0b50a500e00070313a1654000d03500c40544e40003814994104080c40e80c03001225554000b44131131048040000c41d03428012044030740d03501400355017255a1051006072034070b03418003041c100003800a00400092004082040c6542c5501c891842235014500006034002810400c1c8100320301241d0007031805100310341c2016098800b9201c1d2041d041d03800b07100900240d41448407400caa1081d6070305410010003103441e148816041041c10343c8043c000c041403050074420120f1006181c809040744601a618056591074484200303d10b121980c1c001e594010702c140001c2c0120032174000c00c89405842d41c80400c6032a1140f4000100348125002480c0d520100050124949a800500c4004c807a00c1101440c10541710080110140021405411a075 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 604181690 1250 604180440 604180463
    0x103200609040c1b0804090e0610170a080313020306010603020315010c06150b0301090b03011e020c01240503070509090c1e040504030e01080a0c05030112111206040b0a09 75
    0xd142079400076030000000c0c02d211010500352446041c1d400e03100d44d010703074101c400490304100f495000e004454240e040d5401410b15807402255900c04d00d1568080c408034a1001d504020608204000c0080101e0b002803400d41c8a01e48003900d5002c00303803d050200c0c0030740140800003907c40c1c000c2c001e0368011340350704590307003404c00c0d003403004442e07000c1d030010f05071070441d12540303164003d281c08090380c805003808144007550303076060044210a44000c03a0059010342e01d003041d00e00426251444071221003034030b0350001d81c1c0ca4110003160ba0241c50102050b4840300721400c600170b8800418038001c8100d4400390240c5060542c1ca4003000140c3e001103900e5409500007182d084824a41000c00303001c852000c411000f1000008804034007180c5046404902060789090101059078010940d580c5c0061100000c1c4074141041000501500040c4219440c100542406104102040008d5101000007801d400c1c42c1903003000020381e541005072816110001c030000411003422050040b1062183c005010307201 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 604182940 1250 604181690 604181707
    0x40e0105040c06050706060521060709030f08031f141311030f04050a06180605011203170c041205010603020901062c06090415172823030301032006 65
    0x304d0b0743c801d03813044564603034030500403d45a4401c185d4403503105440300d08020020002c1d425600c3d0400140442052001c06a130420011701c02e1002c0110312030f409101d55449445070030130080c500c1e0b02120100c0c1c041c0e100d00c00204801e0001c1e6100c420741e0800711420800412001d144004807200c810483d107820204000148100d42c8240407039070031609c51000c50f13440100fa901c030030049070343d0b044481800000c7c0c441000180440790003010b02408081400003402d050fa44e4010304005d09070682071a480440900160b103000209056500600100004d681c400c002450050b00900c001d0004030301c24042d203400030074003501c19026806904120380c0c00c420302da40e101c00000e00034001d044c0507a500250800140e820340c0c40314020b80502540460704960035904020f90206022803c015028481c0d0100d16800700044402170181084401119082170318841c6041c40564070700d80484001c0b00e42030402904044a030700100541c1200e001d14000d540384283d0340705115410311030b180c1e140c2e8031941c18080b00c1c0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 604184190 1250 604182940 604182947
    0xb06130c0e06280c02031005010806040b07020c1230120402041e020304060f020a05091c0503030103030f0206060a0f05090a060e1320180c071a0105040e0105040c06 72
    0x15015981041d0b2890700f441c038004030701010003454000360080d00914114241006070b4228519050340c1444190f047c42a40c070b43d2407000510140143d400d850200e0b4049009226541a43d00e010b0b1465000c10005000640c0c0e4002c9a018198104c0f40c960014410503d01c441c14001e9000444245140100005200501c010701801c1079034060b940e10601c0d0b1105198a0b006440c018010300b001d81c680c94a41001070403504060458140c40340108085082107600a0440d500c8100c110f40ca0350355280c1b0109032118402503c1c50092442c4400400401459000010030000f003e00d98200d909568a81c002e00862034203500c01d0714030854000000740243e2409001c16a03002c0030742c5c44c000403a6595141c1d0444203100c01e0300c600100301c0350920542c0078000170b5071100044403429201407920000c0000802c0104c001c000312034044100b01800f04580030321040485a410381c000c0d1040808510b903861f00c901c0e01c40e003882980d10075864107101c40c01d41c0e201070188512540e044510204220700e07200045c3c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 604185440 1250 604184190 604184197
    0x10501350d030603050d090e160c29010f08100209121e0c0402130608040f061b1b03140a050f1815180103020a12090b06130c0e06 57
    0x64005030304261000303840c0c400c000114500c8030559010502502e1418020706145400d001c01c800c01251301c106000c010141c001d09500411840c0d0006000d201528085940181c000c6000381050a00844c40e20050000c0b0b845080030450340c03052201903682c4a81598680000e80311300000744d00038044c903994000c80c2d54041d101101d0040d00800c0000b90710303120182021014007070039003001e12991801022890400100c0b44401c002c0d9811807410341d665000c100c8104451180b0030811100b000002c0410007100c8880c6241540b1010a002c40314034000d501880d840940203050005803a0240491521029400c18040340c1d0140c91b1140381442e84082d1804c0f542c080c0e000c0205201c801c122503240f46a11500500c0003024107100010540c030030800b00f011400381c500003d00311070424003801542c24442e25040e14509024240142d45441c0c8800554903000951000c0382d080f0320380203000b0700740800490340704c0c401c05c401c55000c00855103250441d0216100a82d903000040c800101e090201e05140004 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 604186690 1250 604185440 604185509
    0x19120f060b0603090d02010e010e1b03070f1403060f0c03043201060906050f0a060f120c020a020306101413020c03040b0d060e1303030f0b100302070c08010501 70
    0x2040a902100108042d580300b41c42590b11a400507181076009642803192590301c650800c0284011940302d81540d40c0c2e00d080024155010201480500150740c0c1009210300400e80114821070306a030302c03c980c40119200701c503194000d00501000403036440e00350f841c1d10310440386030901070b0558940d901c52840c06840d45034090810007242046504544110420340408a028000481c15508103910b10044da03103240d1106018050742d1035404141d560368281201503400e540b8190b140c000c960242200c1c481d00f40104032481e5440c1c001550340187e408100c108030342d0b0084e81151820f40790241c81003007114051154550030141c4001d0b5160303070b20700b0442854000c40d0390741000d8140bd070501c0c0d4403411a807181c1e001c07003004032002030141c2e071a4544d402054021f0a002c00d2100c01407821280c480c18030400d184000301010f90b101080701f4a50099800000310200160215610101044020780254802d04003611007074200280083c08960500645050310800004140b0100007002007680d0410740828 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 604187940 1250 604186690 604186703
    0xc1403071e030e060c011a0a0509160207150509180c0d0207081b0f33190903020102090a081207030e06070506160f0e01081803041a03040219120f 64
    0x4400a00b50783d1a0054144d84060100001c1c6002e0b40c1f1108240d203902c14007540d4081e5050030300c00c10041d9501040c182e03003d40203003a281004101610200c0c2041581d412590340040c1519052071200d40c000d0180145910503110711250813410700460166160882c1e0f030b07013600a01000301848010040d0007510707269114424190074140c02d03c2a00c6445000000103090b60362014624201021040000c440003e410750048100c1100e210002207240008840c0b50703603507103800c60100e908454098656404001c0d41c0300100807004444c03074000c2c0030750b00c0380c1506032041300a428042410030010804800c0c01407900c01030317441c0103407a0360140e450840d1191b196070b020f0424030980000c6903040c040c0174800d40341c41d01008003502d440100600000340003000c107020010340900781481660865078150304414405801000c00911444591030340c8216000128415072500d216092410014090350240e417080b00d0940c0c0e1203210007440d00d5414110310500c80c2540c0d4000398600401d402107440807000c2d00911 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 604189190 1250 604187940 604187957
    0x80c010603060e0609070e040305030a0c09080f0105070f021609090807050d0509010815030615150a030608010f0c0210020c0114040b060a1e230a060c1403071e03 71
    0x2c6070351007100c4841d102c0c07030f425402c03990400c0b000000a20009014004640b009140c41c10981c40c010468000241090503641d03407407000024540c01140b03610020005601202d0011441281c4503010f00015102e82004c5414242c100ca80680003150075118084444071800b550ba00c1c0c24150006003488071340030340f080d040810040001c64000e200d100c00c08025900c0d03807507888c1d585000040c0b000138020054044000140c407250b90980c2d01142e0f10340c0184c40e44804200103a6805c00254804444150b000101d00c0d001070054051505600100215000c141c000c2007c900e40e0345c504400d803102c0840007801608225991058000785a000d824a450198000140d1400480c2240c190342030550781a030740c44048004100c1e140c07500c0041540a000c0041d281c10303918403410744000a64056000350310000340500c0c544600ca449006107500554001002d00503c0c03170b92003001030407841e45000180e981c280300d01030070808110008100d40c1c45036071003a240300061b04040c1c010035228001d280214200720303440 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 604190440 1250 604189190 604189193
    0xe0601020d051303060c08040c05010302040b0f03060f030610170111040621063503041a070f03091a0a02100f020904060e0603010e010e03070305070c0b0f070b070516080c010603 78
    0x40c441c00006c01c445498180250510f030510603003020040d403220341014010001404058500015611209514103a4584903103d00700003400a199103441075401d88901d000f00074106001b22501011180003044449150681c9080c1c1c03420303a424880e8011080008120411032984655610070032311a8110302130615004040b41d80e0242c0f60343c2d0b03101500c0340c080c1e81100f101082c81c010480c10310003000c80c480b15a0b080d80d042081d031240624400c80c0c0c0f84440c85210441042d03104400c07a6001075005d0106000c0180514020304841175600403215083c40c0e00001c0e805003522401242e00800194000b04030080501106a0182c0030904c5511211502400f49204545a078040c0001404038246e9100d2186403000c103040c01c680e541c3d54007040982c100140740d600c0060110407145480c2c1c041c6050f41d40c414030760401d4403403070101c0d03440104c0c150000600c40a00d01208000351980d103105515040380743e203e0803003c1b01c1034003070080412400c40404904000141d945030091012043c01c0c1c0001c500c0582c1da = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 604191690 1250 604190440 604190453
    0x509060117090c01080705120703020a0c0c2c0709050f130216061104031a090a02030604060f05070807020d03050406150803130501031103010e090307120e0a0e0601020d051303 77
    0xa5500d01450f40c0804420703241503030081d03425940043c107458000c0c2081190343d84160400c102606000c2410360000c1c00c0e11300d09100c0c0290011040e0040d0800000d61750f58400b29254900400301810480308204410440c0041126198010090355841300d5145080004000364061070140250740010000c1e111440403180d4009030280888444885105071900d04194080c2d40303110000400000c8200420300c0000c0698050400b2558110703040b0304aa030f01c21803c02e02d040005803011750706100308000c0104210741d0b500304c9032016250480900c403588903202c050720040b005a50000242c6c100791030100d01c1c203110354889540280694400328074201c120080b4145e50380b00341c108243c00c0d0070025070000d00d01342c00084080108000e280401c50064030340611501e50106005003140303c0c4801c00401e9295004000355001240c1201d03001010401d8000043d0005407511115806080388100c00107103400d4110a9034403424040c1c024081403c0011401c5990364484020b020201ca0741d50404004100ea = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 604192940 1250 604191690 604191737
    0x503061f0527150406020d1209050610031106040e01140f09070c0209011703031603020f040b04031101020c13090201140d090506130c030305032211040c02010209030705090601 77
    0xb80c044400010590142c03e10150001d038203411902c00904120401110b07a000801459480c450b02e000700e00d080d0b215402501802c003506e030250042c481c020a100d00c107a60210802c00710b0344241050440c540c03007034082c030495004921074404002502030040040900d45070351081e44580040c50711a1644a400000e0366031001516074500048582502004505203032180038050700c0013045009080780d040001a0b560310004080c2c0440d003000103c04002d40e0301a80641300c50200c11200740f502e82c1c1d268020b00066030005d11041c1c8035201400c030440e80d103500101e101041c3c0c200103403c50382107054001041c40038000406049041101164420a81021240103400c18440c40c042c0428500742504001e0314104001e40145080e00390444a80300149208140c1c03002c0f243d25041c40c2d505c80c0d9030203d00700c1406075000d6040041d14562108041005080000c14924401c126800c010450100000728200d000d803252803a0180d12561090106140104c4c2d100d03403000d014035040540d09102080701400a0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 604194190 1250 604192940 604192987
    0x70c1205040513060807031205040806071e0320030c0c0a08031807271404050a020102011104060e1903050307030302040501020c0d050d0f050d0c0c060506010503061f05 74
    0x3100031605020501e010000d8005121400500344106030030100b050344c6500703461000406440c84003c0714440745020700207031402410804107480003860f10280c082e00c0c8100390161040c0884048410000315400380c4200204050341040710341d021b0311003045c02c2200741d0000e80a0949001d00b804405000d1004100086000d88540001a224100712400c1800c5021070164041c05070805241030180350100103007004500c481d1f0100041402c00f1820281c02000380c0c140700c0900142c400104001d00000080c0145010700c00c0c2d00070810500c038030b1a10506401640201d100040205000308001c1ca003c1c40207041131000c00c00c007840c00c0ca03620390b2028030390f03440080100c01090300840d04102d95a01841155400e40d420349200f0b162500d0350f0744580c0c0310711800300c80b0014003c1c2550030000380e51003141510012298000d04104030255088054010b0341d10140071030b5440e04110010348603510900c1500d02924014100303d50442407819a80303000110030090008200c2c052026030b201d480e84800081188 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 604195440 1250 604194190 604194197
    0x1202040f030c0e010906031703100f031208090705011b050319120b0301020a050f0a0201110d090605010b0421240b03010b0409331406011101180b070c12 67
    0x110300d002100d03c21400140d2100020919050081020528200102d100c1012101d0202e03540d555200391581e40c403025130049040705442d003002108000161002d802107280640320601c255403503143d03543d0341d50070031302a69001036400d030081c144080c0b82040c0401920f1050040d6420040e800040003030303840c0544d540d80b00080f200d228884070903079188295159020b080e00294548452074902030a90b10401500c0041542c0004150031245e100307602480300322409201540d55007007000400400b5040e10300b41a28140c0c0707098000556503804008840403100f44280c2007a02c8640e1145c2c250410100880958602070b52800343c4414404130800c103a9000c0341c044000903507990b45800e01d0300715502c060b40540074600d458880800700c0c59040e8184400e055200c074041d0950440c605411121440d003d550300441c0c1054500b02c1c5110054503190b01c922000c1c0c1c1c50250075410a421386081e80c45d23982544600e500182d00c00004208080900c96000d42a42070201c02034586903100341d0440341710307462013000 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 604196690 1250 604195440 604195463
    0x31110031122060302090105160503130e0a1422031101020d0212060f1813050609060105090709030c21080c100b0a0812071407080f060c03161202040f03 67
    0x1450b20302c0c501e01000c2d0802d4035045080c002d001002804900ca801200200a4040c1c8204000c124042048440181400d00c20080301507a440b00d0284902c8280c0d2049240e5040c00f0340020100800ca41c480e22821441c200b0482c0ca105100707400303c0d843d00a0500f942000f9440007002c044d900d00340000e0401846107580103958980880e4102100000646018865080d0346060200c0307960b40d03110540c005110030521812500c070405417000d0b101c030380e00c0010100d00404040103407201c800700f01d4a0427208280c51b20390542d640d11400301d81000d840c0c0401003641b40300d480280a500b40e0744007140c8040c0001940d90b1407024803502c4481054000510300c0c540c96118183c941d00f082c0d0640510b421003101981c442e02400e0030452030580300e5161095141d0381c03190229180f0b040c01310002c0211448005002520b072a15200e9030320030380320010202d684000b44240300c0421881300d250400c40f445256004201c0c1102521094100d0700e10300102402039031150240400316444804000000c01180700e558003a40 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 604197940 1250 604196690 604196737
    0x20c0a0f26043519050f0f0607030207050106050d0b1b13050415050d0b012c010e1008030c1f02070506011503061a03070210060311100311 61
    0xa664450620158550034441081070001610051141c000511075101c07200c01c0c0350f1210694100760100d1908140302d07568031061310105400881380400e000d2419070f98401c10f4400301542d55541403000e0b070070542c021400680428407a50140021520030b8001207001d565902c0000e50300b0800340000c0d07607080441c1042c002e107042c00c0001c0c000e42a034116081402c0c980b4510b45841411030620596000740d441e0700c031500f2800407042c00030000e0140107015441c0584035007018508070b1000d0149030030142c49a60201010756010066440b0486003042c00e01d100c1c0c2c2400d00e480b00c2001c001e82201c007446406040803886d47c0040c00030b4242010610000d180303482d02102504403401c0140240741d40d02c2e00c1000300300003188020a901d815200281411051882010000c400400343d6510191842600c1c602c4040480c081400450040000b0340c02c0341c10700b80e070f020312603030440e007281c40300412941c84000e4019180c100640420011401d41c20005113400a410f00d00c4520350102d42c01404400d1600034001 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 604199190 1250 604197940 604197983
    0x1c080705101e051504090305090405011203090e040f0f060b12010203100b040302030703060209150a020312010504050f0a0f020d090501060302030d020f2116030801030b1f0306020c0a0f 81
    0x201019950349082c401418043c0449900d9180c07042d1280c002c5445206d02d10615018a0407565492006081004150303918400221504480c540450004083c1c45001407403144130b003642070007160041c1d5501315070030090f41d4a00111840078001c6503400d07120017290030a6a1051258400b80b03901c00c001507520702e8000e812000c00c0e20144c1000900600610007400561800a00d138415a940031100581d185807442c0011349a19000024035210300300026041c410541c040068200340032030b44055a001c0e6241c1c2d0800c0148c400817030300920079560b5040054200003094010b1122004000d000603c0c060b0400c50520641e1404413041e1242e0707454036001c0007142001c20411001544a1019020442007210015110060724003451011094000c21104900003081220107811034203020303480030040352901400c909003d120070b82c0d01d061148002100081c8402e40c401c1c0403030f580001004128216900c20000707410a07071031a0002d11640380c0c0340d000109946881d281080c001da42c4c0700350b403021544109 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 604200440 1250 604199190 604199231
    0x40309091d3a0f0f0f0507030e0a12051501060f1e30060911040603050414012a261f06051b03091c08070510 48
    0x121000c041e52600d01100000440c030701e61280504020712120340b580014031544460300704081051811a118036240440d00107440d03010746022500c445030038000305481035504006055880e400319104000d1140028440c408070140301600a2100c040b5546544441e210608088411100380e80030340c44c84002e080550400e5170041125207003005084144900041c24a80d101050400b072007281c40050030814058104103115086501d400560641c10918210144586500c1030f00200d103465070109000456001d481c003402c203003884041ca0145002001c500070000144141c1e031500f8850201c80c0780c0d007000c1c018100180c0b1200201241e951503845d000030341c204010007480c140b10507020a400354070b44196103591024000014120760b42e071000700c2c1d2094814001400001d100c501000400c40f550440043c0801044181d40319520310b440d1700342a581d034842e01c241f02d0390003c1800c040c0d00f0009141240b41e281d1030710512441d07040041c607a88480c80d007010740444500c480c0d1651b0602c00b01d09100c6100 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 604201690 1250 604200440 604200461
    0x602010b09010b040506070c03020d0c14032b02190503040612060513020d090605013005100507020307060207032102090d12090e010e0906010803040608010b1b01020304030909 77
    0x1211070b5450309400c0340a6224038490180624004200c030002d008103a43d20703030020b54000c0d1103031101d81140d250070714038080c580c040c10310b06440180400449003030000c2d149264000307905d1420008500d000200000e000d17000030040441c4a0301e00220504072a0f042c1003407040384111300031070702c650403c000a0801180070383c07601441480c2620412a95550ba580e40214000760a001a9101c4810b503180d07002e0400c101002d82041e00784400018105080360850a80030082d1213a40e115583e1100102048102c440c0080c140350300080001900040703d5000540000850041b20301e061255540c40c01030341c000090940c0820707003040c03899011141c40d2040c074400c8500c9140441c03400c04040e00040b032150443c0f10241021040c9609406514001c007250800b801080041c00f00c91360b503c20b0700d5014100c013203a003040c044c0611800090385035070000903102624000c5d240e0380c441c0c0c4c2c2000c010080da0b410001d04040039140c00d5080703481260081c80154040d80c0240c0c0c92404050401c102e0f84281d403506142c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 604202940 1250 604201690 604201699
    0x902030723090c160602070b15010906050f0301030204150305060a060509070c080a030c030b21010b09070c08030a020f0d020d060b030c07060f0f18060b090408092809060602010b 78
    0x800082d654150f04588081c8441c02c4c030198519628284100280200d41005112401c04424030080414448078a0002d43d0241c1c0e90a07034003503d540086405d8001d0054414440310113000500c014501504111860980b00c2241e042460340c03525014036005050340e20341e40f90340d601d4000b0710690402810b000d038000740604008450a045613100705c124494109220101079803003e96540082c4a0b07000980c2c0c202000b00601e401c102e2030700202e07400704d020b103422650740d610300083c8442d14107203103a43c1482800d0b2900d890800301d505890b1802e96031700051042d8895a82040105040c0246a010b0440d401c208180140c41d00c503107441308001c03103071144c00502e0201c90900400c804130000c0012a25150b5011802151004120701600080d100c11316544282030b003499007840c00c0e254411080362507140204418881188903400380b20b0345e04010b07030340034209030300804c844440d50414503000c8080f41c00810817900d441503c40b9100701028070030b03041418480e8841c182004502c3d0b0902408282d00000c0383c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 604204190 1250 604202940 604202959
    0x40b070206040819030b03250f03050304061202091f081e060103020c030403020d080307140a080402010c02010c02120618030408030306011b120302120711060f09010902030723 77
    0x201c621050b4044c1c001c130001c11008040c85103901c1842a00008400c040290450300740c0c4036480b503280c1112004894045541c0c44081002030510344a00d0700784101d82d0404061403503d030504400320707540844000c202c150107270200300040740c680791614805146815002d80f140b40d40108040100f0382c80002c1c0803161031211508907903102c580074070242a0001c02c2400d006036280010b120701d43c25030041d0360019501c0309081e0040020700010b079006600c01c0300309681da6101000308032a85080c1380110000040019041c2c0c0000700194014600140054014103001c80c0840702a400a004081c08607015206900000180610707050951100d40011a51601031420141402081c90303503070000800403410007084980c101d803201074480052800d140c1180c15000c00303440100740500658004002c030029030192200003a0301a01c90180141c5e14107812000c1c280e281c8a11044240084000d8908a030556803201d072100140c0d03003007110390014007542c11515204244002da00341e1101e84195003601407070510 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 604205440 1250 604204190 604204193
    0x9010e03072d211710090c0207050d0501020405030c1c151407020a0201080606040303020a12050c16150e090f06030c030a03030915090506040f03020c040203042604140d29040b07020604 81
    0x14454001b81d501e004000101403441031030403031400155902194009861034400720a101d419002481a82e1040e0115403088020b18148083d841c1079954800850704036101e00c100168810050000543e4515000b01c0c5181c0340103e47c0041c0d05003943c024001d0380c0420110421540c204042c00d5109604a031200d00b40392958401a444041c00717103000b840c2928070464400d5860280342642e10801d2400100c80500301c4449210050680500a01d90700300400094695040d1085054000034540a4101c145944822142d0188000302400039640f41c02100c14036019a2010424102c2c442e0103654040b1b8001641d040c9201e00c04480703651030012505001d007820124400040041c0c00c10340c002d04404050300b03d810120b007800030300940283d0003400002130000b407101040540c0c2250401c0c10a66003480c541c141d03807010302d20450bc40c06410381203682c1c03902a43e01c2c111803a002800d000341658000c04100c0003441e5401c1154410304002d0700748003070521043c02074070002d03268001a00c2c0010482420107 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 604206690 1250 604205440 604205461
    0xa17060909031c09140703110a0b0a0e0414070f0e030105100608040501200d14070207050f01020718060e07090509060609180103030809010e03072d2117 67
    0x184000203181d0340d03d900306001411a00d034424281c00344c2000401840000340034000307031541220b10054900810f4000d201045140c107030145012140348030009840c080d034000d0300391002900d850b0001e5004c0da50b00300306c8506a40364142c140c0b160215031782d42d19401ca540300300034104d0000c1039031281c0a81c6c5000104440103444a014900392911418802080d40c2e0310b143c03440c003501c01c00b0941040c0c3c02c0078070030f501010485040a0640740c0c040000c10f1200030840707549500c000400315149001a409600100714505100d482c7d00d1401c0d0040c41039440040d1a828103034030203510480410100342d0741c1e40c020400040440c002c150001c507589400c4041d9480c040c0010322061000d001c46228000c006000f0007642d0303844441a4004500b880d1003c00e075070752420b02401c40714003280e0251080d4248041c402c4883c0000c800c03220410b9120b00c9000c080d07910740b1441000010001c1e11007070707001040d004c590089207441c280810044051180000c81000d07045004020200c2c8000d030a562040344001c2c01075a420307 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 604207940 1250 604206690 604206697
    0x5061215071b0f0f060b030309031b04060906080f070b041a0d0207020904030f020c030109030203030a05180f010b040b0d0807020d052107062007031409060a1706090903 74
    0x205150001c2d21126200000c2071150a41c40024000004078600508010703071308240740c09a0380103550420a0780016014980c992040d00c1440f640f5420560714003d03890002c0054585d401806040003518a40704c075005404c0703500c6500a15990352041400c40700c1210100400000b501030692040d0800307107810308242c0c02c900302040418100340b02081c20792120500c0c1c3e050b9007410380c0051800c0345c02d003440c2c10b002c0c0c048192058180c0050181c000e084a10b070030140079070000d03503a00d40d00540c0345644108081008010252001c0c00f01a400780c0140004042000b0241400d20340a0002070b42155190401003200d0380c13000c095024013050b07551000032843c004140c58002c0d070147c0341154109010700d4039904042403003080c6c1c1070040750640e5007401e0040000242c0901d40c8070300c00c10089840341c080340c403858049a4100d4041504100302e07100000c0d204e1001c4000d411092140c4504100220b000110039030000c50507000010126500d002c0b940b0b091000d03080e003190f000d40390440740341440e444a984a10 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 604209190 1250 604207940 604207951
    0x112170a030f0c0518060f070f0f0609031214010e040f02041514130908032e230a21020f09010b030f07110c010815040c0305061215 58
    0x1400494041403080c001e40200354103100035141003103c06404000503006800503d049180040f030349209100070704022084500c03000074080c503503007080f18607603503540e003100c50002c11503880c1c44070344541002510b10b0140819440c07094a42c603604462a481405c00ca604034206144114940b8004005014035800e000d80c200790031045d9003810224034000b0a006d4866807114090300c0f100f1403000915010500c4080702c0482044a1040041d12032a141d0025078000082c090301c000003c0000c65610b00d002c0c1c5a5441c0f510f207014103000440e400401e44503000ca916880402d100159154100031006e03038103290260030100711012000d06041c900c1e80070168040d513007a0a00075030112340d00d605640e9442c0e5014584100200041c5156071201c12035809504240c07012151041100c0110302914000d400c402440c00c008001000d403107449800444905a01628684003000f111580c0f244c40d407200d0107035010540061301c0101d6581011010701a510440c000c90039a0f942001c811000c0e003021020301d85401c030 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 604210440 1250 604209190 604209233
    0xc06090d08070c0521040f0503030f180a0b04030807020a0602191202011d0a1202191e05100501030309080a0312020a0918050a15050907200a060b090112 67
    0x30034186806440e000c02458402002e582603220703e02200070420040084c1d07881d000b8488400e81c0e03143e09041c0d0303a0103406104c41101c103050001c0d40382541035402070b207200140100337107400041daa50741c800415072041d01300341c58940c00011080d09504008001c44002c100601c010003c0c0e62a052800c030a041d403032080208112410f1341c0001c190b51003500851003600750120780d0707600305200000480e035804005c50111400040c20070070f9020300d8000300d4990384000c490407401382d07104529903407401d490380184007041c00310f41000c00341808100100f00c031140000b060f450020b45541181405030100001d80d04ca2041c03903002d8042d070b400080e400003d035050321b010101c0258486140000c00e17101c1c1a9681c0009604a281c4480100c0705007840d04683c0c0100850142040188602ca4a20080f202c103800b466401c110950041414140b2403c040c9500c10003123260821120f444d400d0041c01c141600b0001da8089450351207074261868029a607c2c0102102c0c69100c0454115035a04c0c0782d004e006200e0100003 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 604211690 1250 604210440 604210457
    0x703050a0806030309030d0503060909030a08151c03050318190b0604090206072010051605010f15090b030f0a02091815190e0322030602040b0c06090d0807 68
    0x2ca49003002900c140785d1004003901d5840c100c03081e00901c035030011501d20303200761100c2d0003190740c110f8040110380310300728981c3e507c4900e039035040040c82d10a16004622034000e07540740070300e15800c0f2442014800303861080d61100d0b600c0c100425071444910030300c0c851480030780040380540c50f1700c01c4008010b401c2d0f41c0d102e408000d450b03a503100040d008103402080030307411400003d00b00381046000240701060201400040c5882e08011b414002046200f81818001c144100600a9410b940b0066001c00f24401c50010905807020300d0300784203646250280401104003080c0500201020f800340c100050001e0700204610b01088200564503400c0d5200079000d46402c01c081080224145d8032440b125000a04031740500e24140e6000d002d8010840d8480d1040d88024a402c1c0244620700172001035074030b028000c500700143c4441e013440b810f03a0038040d007600c01400e0320004001a07680c0007510060010411250b100d01c4c00384505818030710002d1280f80b081d0802c08440b00b410360001001500410705142580c103 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 604212940 1250 604211690 604211701
    0x20f091005210a03170f010f12080c0706110d14070b31020f030607020703030e0a0909050102030103052e180506040f23030d0906060506040e1b0703050a08 68
    0x200b400520600c18490181c4242e03c000d158219550400865119101501c030380da4032070070014055001c0c0140340014403480390030030400c8025804420003e000d100500e00e0000c213144541d2030302c0c18547c850008980c0100f00c00c10705031418404480e0380d01c1e290809000800296003446218400d242c001000503401501013441c4c1864006035000c00740d105030744c90300811200041000e0001012404070300c1201130040c0c482c6182030104460740600c405400402109081d070f5400c0c0e900d05007880482ba0400e5052a00199926482c0039160b441400ba80006a895055017011414074000242c0000300c3d00c01100800240005154480c04c440000a40001e20440c0d160b000011414000c0300584144960b00a10003800b50600303154500621410b00c2031940b051180440c265030100400d407030316a420a00450009007035540021003201d228220008056031031f41c000031559080341d0003800c2d815038000100040c0403110bc1c1d829150101098240e8240003541d50000c00d03034414440701408102c0d442d0081078 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 604214190 1250 604212940 604212979
    0x302010b0303030c03040611040302221806050f07090308070b1b0706290307060c05120307080108210a050d060801050a0b1302040303020a0b1009020313020f091005 72
    0x2a0030038000c0980303550f420300c01d40301c0101d0f8105440c180c41c7d4500d85540f40d84070307039079840844044940c0506800480d002c0d0301c80b00c42240c58030b90b51401910740c42e00300d6081e1800e92500141583c46c803c40000559080090740309042c640010041c1041c006c100b4801e0011903042416180005d80c130650503080b50340c8440701e0120780030100c011140e0030000400c01004204a40d0806254954114030030b205440c0c1c4048581c4007141d030029074a801d0342005800740802481045200401c5004504030346468100f9080c1c2c4105601c100c0350303400082c01680040c05140b405000312007100038030b0860b040403110048280030003440791800d40000c1c02400216081d007091990800300080c0400300003005245049598a0003400f107002905108042c0500d02c4401d4240703610030384081d00e0f059402040304401a070740b840d000c540c003d0040a5024603407240003034805c48600003140700d018482c03030b07000314081d42c0d00c14440c0c07a43c20b01038000d110b140900104080040e200104104a03002212410808108546201d = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 604215440 1250 604214190 604214201
    0xa0e0c0d02130b07051501030b0c0c010204080f010c020d0801030b0f250e040c051305040216052a010305090606060a03020403020a2d030b130c240906030c0c020d030201 74
    0x1a61402c504000200d1211100160000368010070649440503243e044807080c513002404002c1c818001c0b02d0204d02e4030b5411801401580b42140001441c1c203450301c0d00d40e03240c01545440019140c0d16400d8201405905100000d4080d1071030a28004950555440109882c1d0041070039003000315070030002d00c10070011001205494044407880949000c01c1c10002d140c072140b0704009000310b05212488211038468400c403042c0b043c070f00e00c0e0124085d00348400c1001035400004014082c0281407c00700c0807660074800300d0320440001d10300c103040301020500313164584941420319060514000800c1000180030900b01c0d070000d800c9803030640e64810340205030000d0055401c044d402c2008418040341c5400d20740003180d01240020034102580e42da01031122407800c001d0000520f1910031602007104020000b903a04020b501c19010748190540b00c20815400f100c124084001032011b202800c1c1d0f9a5410920101c00381145280500003003c6545001d0500b8500040090003690300d0f10072042070500c00e5014 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 604216690 1250 604215440 604215457
    0x200d1118040504170304060606082d0411060f07021e06090d020a080714030106081f2309061902090d080d092f0303090108060127120c050a0e0c0d02 65
    0xc00b170310303400c0900f481e80c0244114044c0f10003055100020440b401450740340040100040c03030b043c00303c50309400101c42900d80003070005c49180321200006521603543c0809400d542c80100d00706c0b52100780074010481c1c109001c40f0048a103241186101c2d00b540c80d4002141c601000645100000100760300c0803d00c0300c0c059501c5085140106103000c01c0d60b03a80d0344007034404180d0450091182c140c580c504176403220060b403e030311019009011640c4203074017030740c009948642d00310310285001c00796072101c10000760f0200c44207a0700350404403c01540141e445125413a006442000314203082d00c0401040760402c907a6005401d91501180d913480440082c3c0014100c02e51004400c8100030074031030702c10941c2100542401d1a400030102c02141c0d0704002050300c02c10481695400c000c4d486080042d14200d840108103120a5000210780042c40e0300942c40d0b100500c0d04283c1000c184020b41021001324030150406403207000b480c041004544034411620b900302c060650b041ea40d8000300c0c0b001400070302c5403c10 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 604217940 1250 604216690 604216733
    0x40327090513021212031602010f0606030609050f04051f021c151d060108070c021e0117090607080702030c0a0b071e08011503200d1118040504 63
    0x1c011855000e2407559011070300c02c0d500300003481080e104103900d0703401c0300541c5e0110200500005410040c13103103050076016218000047e94010140191003036800f66004a404281c0324038003089072258500c0741907480b082210421030141010340d507444c0c0329503191011108101c5100e1039160909407a60444803400038203401c10f0000f43c40480726002030060701041c1008100d5003003001804000c400044030800d6410b021080b02d507901d002c01501d458801500302c00170440004403200058648040068a02d4100c0d2403698074000e5082c001050752440000517103412145070103001241400180590308a501c1d81415541951060400c81c03441c010010303c0c110728892900000c0038480900083c0d400749040b96105054090b103800c000c0021254544003900148001004024203001c54019450420007443d0200300c082803000c1003e4650440007691402900000741030790b806030980300320900d044102940c0c40c240f840602440054007001003c981c0031300e86400c009820001d81d0042044030404d03520 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 604219190 1250 604217940 604217951
    0x3030e030d0524010c0b0a050403111b15070f0b04031b0605011a190818030a080a0f061206110409021206010210110a0c1109091f020304032709 63
    0xd040d0303040003042c604a4840d00092140b081548217030404a01c0c160403034111011910340100e89001000010415420414030422807410803074148001c070024458034400c85401c6803c2c108000065072540d0118600300000c0104c480050a20a4901e0030642c01400a02c0b4030395803401c0c01d4480c807401e0381c4200700071440c2c03400c40401c0089039481181620402d58104c0c2c000c02c084140503181d4401c090820103200741c50040d01c15101e1280030450b0f444500140c2c01303564001c2d101c128038510341200074050085501314081044994961207012649000342c17106016003841d1540040b000c2c0c03401200501001e0700c40e0240f46541044e03500310380007000f4006d021543c50305680c0c0c80b82200002030312158014010b080c03c40301200140c2c05200807006072031103200d250501d071000a8500e500d961004442401094041a155582d5002030510400100024042e0590f0306841a01540301801c0301d81f03101441801800702095000d01154040082003005640800d8200d4802c20041c00d244d02c201c88050409 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 604220440 1250 604219190 604219201
    0x80906130303090e060d1e05010b03061311090709061b0203062e03030e010f020106090e0304060f02010e0303061c05010c050c0c1507020d0215030106051e130303030e030d05 76
    0x80b0030466001c80d940598640321740d000c100b010312404a014000f880512181404580580300440700a8403070000000c00038502c10100b410034900300d40300410400e01408030001c0c4941015500410341003100c40f04014a00140b000c0d20104490040004018041710780400007400c28a440360016001003ca03001031074007135803d0803180b99039550900052004c1101d030b9074440c0c0c02000141a41d6141e100d202119120100454030a00c1c0343c076200086641b107020004101d642d42c802c3c4092421a40c01642e42d860800b03002401030b8105021100841e89004d54060400034040156500300f1021140088403900d41145002010f00742d040c06811546021180c4500941140c01403020100320400d03241d041d00000b040140001100304007165942d410000c020051400d1240c24078086e100610700c013980340c1c4030b01c401006078000742c014002190001544122103030168403000d80c0c0b072040914013460465142403000c903d101d9480010300f4140c0364924030703820500c1807081e1502c00d480c00d00200f1140c0f030305 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 604221690 1250 604220440 604220447
    0x3010e1b0327031e0a050403021203040306230103020616080d0501030c090b030a060b03030c06042a1214030409090c170102090d12090513090c05061303080906130303 73
    0x4007400b6120110440428002880011040d101e10540344e09034541000fa10b11107075082a0301a011500402008000110069882001d00c400403c62100115183e50447c41d080f812a034010094000d5000c40c03008000f00c80083d00403090650307074182c58241e02d80c0f6101541e41400b40e601c0300d00038000c3d00d000c030350825111465801315048074010a007441c1c281b5a20070102003161003083c0d400d90560002034041c0e0114085400030031407000080c2c1141d207802116004d0904100e8141e03003c40301c03801c20119038605926044d040352441c3d1030300200541c3c0c05180010202c1c4200005000034041c0f45c4104103803070b1401d0203000341e40041c032070103200f0301001c0d401e45804020385c0c071a4000d03106407020910f10b92010307042c14070a6800e83c1c4000307001c0301031940d00e40d01d5480840720001c800b0001c00c02409404602900c0d0101a0f040000e0806000f04a03105180307440c0d49075800c41d0308024020301d0103210b0100075002d00542d20040f00d8000d007019540c1d16102020a2041c4519241c15105141009000040503031 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 604222940 1250 604221690 604221721
    0x102301060f08010b18041805030309032706030114040609060b30040807050703151b080c03061201060503070b070c0603020c031207260a110304020603010e1b03 70
    0x80d5039034810b0b607a00c5401c01019809944c507038014803d2008145100c50030140e201c2800d20b0144000415082440c2c2d030346c94a954030031240600d180c0c00c00314160145849002070610507803145000d4030044800c08021615034001446540750b4503100007500d04991b06d80307501c2017020b0002d0303480510003c1d444402c025080d91202141c100303549103000350111004281d240c20085040100c02c013850030346070f42c0c60381072050304450010b03180b60203100c80020018130f0b20650106800c041c6031021900d49040841d07503980451388580038081c008540d04000340441440200c980c002021a03400d91019140c2010500500094201d80c0d014411100046045902803000c1c1012030f100b280180c41240d2248022030590103094280714090f40107104d120720f01d44000781c0f0300703502c20031a06d0400d40214040303040c0d1101c03451f00e10038107071240c0103072007440086800d600825220151344d03600b242c0385040c160702180807440305200e001ca21000c9000843c00041490004524402035040180e440b030034140c80d0b40041c01c9 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 604224190 1250 604222940 604222967
    0x212d06070915020a0b01030f1502120124020709020c1e0f010e0d0e060703110607030e0709020a090e0702070b0c0304050a060c48031505040510230106 66
    0x1000084180c00c4a4800956107042c95072017080d041459296035228244030600e140200c0c1e50240559018442c4200e81c0f01508580101d002c24450552402000f05440c2020322183c02408800000c20101c4640004e1a0000c43c0c000e5400140d42e24135814480c0c1c1017110348441180d50f051407155840d641b050000f00c41d0b414180cc40300800030350034004103035030b0780310782420b451004500401c04c108094a481030203820450b00a0030320801c04241100543e0815100b1219140405d680301c0890400c0e20b000c002800c0500340c481c20451a290040340081c120081da44102c1e04441c00520004800c03900c2480303480000c110401c00e503910340d084001c00c55100c0d081030081d030340602181500000c0c41841816103545007508080400c7d2a0400d01d007030f03198101c09883d0304651101468240000500c08481074262040544070103031181c03401c626003990100280700094100c0d03400c10061201281001c42c14140d02c2002e1500007030125004010f0410103400c103080554280c2440c000061403540044403e500c41 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 604225440 1250 604224190 604224209
    0x303021b0a06150501080c07031205090303090616120b06130b07060b030712060c20010f140114090703090f08030406050702060408180310020f0405212d060709 70
    0x4021046800b0f000c00f0407803140350700151710040840d4103140034000600d00240030b4500300c241d4130085004141034440a03640c0c400194000030070000d40060070311440e90882c642004418580741c2c500c00003082d0000c500c850000040e82da401a141503a01d0604840320511565000c020940d41c0e11541542c07a001404140c0c3c82c00c0c14201303d8512850080f8925080e0750a0785d114040704e1280d9200d000040400c00000818040001405140c405d0322020340040100c4c80000400c05241c221064001c1c0c4485401d001900100c410040c021003101010011410609850020302aa1040c008801400c1454405800c000ca0030305a403081c0007001000b18403c1d0301440b814403454a80840c201da846c1400c58014210b1501406141c980e03074502001e07080d40c188010304407540944051108070484c1d100e0850281e00440010302000a82082d2600d60241c1e078405009005203000d101e8420b0311401d034095480b0411a20340d01315001c02098410403404d82c0c0e82f0f0011030b00145003a000107414084076000d9000304 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 604226690 1250 604225440 604225451
    0x5071521050402180903030411060d14070e01020c0303030403140417010c2a02060d0605120705040b1f050901050403080a0f080c0403110d050c0d050a1e0b130303021b0a06 75
    0x504d07540443e150150090070015031a5503141e441d0740304016464203c4c2544840c0c1005a201c00c041d96019981414554111890b40c50910074005003800c2e04900c242da041d500201d0405541e80c0c0c012003035a50203038040c00d2003846d0303000f041a250b8680c03280da0400020164607031401c1c402110150f010a800442c00d844c1c15001041c04400b2070825900308450038868030703607440400014100000a00280c650007100890819203030000140521990072945c0000e5014510406c82d034546070003030303a40842e030649240151800300040c03040c019026043c48410302000148040c40d5910034411100111f230042d0f1080c0c5c44460b000701c0240350119071802c80700001c4004001c1458404240112000c60781d101e4000000340d00e1900500100501e144030513911070180d440c4559150316001078000203140f01e000034080402d800d1400b00a03140d0215005031410040b0710215000480c60303950344d83c00030a1003884640070551440c00704d02074400d402d1107420720003074040340300541e407000190700841d1442181d06001 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 604227940 1250 604226690 604226719
    0xd0309030b0a1b181d09010506010c020105030c2203030804050d02011109190509010e100b0a1b0f12050a080108010b010c03140918012105071521050402 67
    0x40d41c6603044445034000031450090320b03c50044c0c060740c40450504204403c2150b0703401c0d24030070b07241c031014104601689160800094840a200d0540e0000090a0816403160f0381c2d00000c206010041c51001c0b10540010300c22046c0220203001503401d011a01e4182ea442d03164600100b0050b001d84003200c2b0351180700f001c00300c400c0c018026031440201c0d001d40103003040f0360f040800c0005c6011404084499030020000328154484603031160103400c3c1144005000d04100d10090304000d8240c1c844010628180714400c4a1076000160000e442814031140e064101ca50820441e540f01000d0700a02607000245d0714040642c01c00040e00c01e144a903160811079a81e00c41a45080c0c82000c2007540c000b50382441400c4c000b0380a01c1445031502c1c04c02d070a05007000d44460100e491805041c400203022400309004111644840705030b10495149440c0b140000419980c500380e4034a0203000c0d5800c01c03c040044410742e18440d50346500d02d255005096146891071502c0c4100405c01079030180d0280c80c1d00046480c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 604229190 1250 604227940 604227961
    0x201050a050f270106030f14031812010e01150f08030415081f0909151806020f090301020d0504030216060801060e04020417060a2f0d0204050d0309030b 67
    0x340302d01c21401000c1c40076911480d90449480251a4580a00414480400041d1030921030000036601c10810700c161200345040c50f1003d00e5020002000c01e5000704626540c0804900e1103400d1000c00743d41c1c81d030708075040341c02ca40d0141118803450000d40d860f01601c04a04c19200700503004035202002c178088016281d085045d142d1082d0700071140700588903103444038902d01c034154a41d44420282d03003c005401c5200306608042c4076590005181d02d48556113038003441000440305185010701e41c000c002c10f0b54412224000700320f0700720b406480b456011407514a00c015100484134020001402107641e000d40000c40d40060105442c103500520482506c0d0800e4040c0982002c142e80b22600c50280583c40d16400f1a517540c1030f6002d854202e5024800010503003920402002e80104460103081e40345070a4080030b040301e6091a0001e0150041d0b04000300d80d50b03488a414920410016800342e4031036100411002074403441e0302c4503820401c407000100c03d02d0790080f800c07002d5900c5150036045d503446003030500 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 604230440 1250 604229190 604229201
    0x21080f090a0512070521030115030203090d0c0c09020408011b0509130e0a0602040305010c021c090302011b080708180603070f050705070b04140a0f0605160f060c0309030201050a 78
    0x4002d584820b014a840b00d10900180c00c60622450448908400940da0300d56114440514054800380c080010322005000e03660140d4025640d160860540c6080c4405c0c95840c080400312a062009105a10b018000b055803004060840c070300c000d542d03d6990310106402000c0f54401150001143c0d4a00d0706a01e125400321101a44000d2038958039105410b9540000c00c1c0a20a030585846520a101d00240d0a400503000841c000d2000180c2d414900d00081e0804441d54201d501420980c909841c000d40c10410301810307290207281c40100c9011490000743c81c1d20b4503c00c043d0035110041281e000304400034000300841c144608000c00c0104000e01031143c180401d030f86e0200071030505e803040d00c90944100003420420f40900102c50034260b80700ca21521301d038030035013128980814100d121f03d0f181c02e103071103601c00030161204c081c0705903464208002c1ca280941c0042d42c07503003182a102002804444000035507040e4221404201d030f4028442c0c054000c0042c048101c025500308800960041c1251140 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 604231690 1250 604230440 604230443
    0x27030a0228081b0f010924050f07061b0c1502031509150307050d0c05040c02030c0708010f110310050918070806040314130b0721080f090a 61
    0x2921000240003050207600032030030000500054907540040d141c0742c20822862460300d900d0108031401840310502c0300410841820a041c08641c400811034040f0f42030a5503d00001c0319518848860055811540f91040f20503020301708202281403401d0110310381c4956900401c0c034541241c060048007056032140c03140540500b4000020ba2600c4031120150011980519400d4244d0403180304070001403854107058a901e02040d4000c22228100c2c101080400701410084034083d80010180d91440c11001050040da800b407501d0b07001601000e40200180c40b1039442c820181e0b000380707850f8550035008116010303804450600304860220340340001401c9a014100107007001218609143c1030204045c0b019005546051042e61844070504090241c00301a1401402800300f90038182401403801c03226400c07800d02810100304100d070441545e4455001c8514003921310340ca5103101c2c07c04804400b14821224000d5122000743e403032007640310340350320710401c2c4103c4400d0745500d50500455850051341c10 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 604232940 1250 604231690 604231699
    0x21040914040c1e181d031201030f0807080301180b2704080904020a050d0b03010203010602190203072d1e14040902040608030703080703110d050a1127030a02 69
    0x1801d01c60fa01c510314491005181c00c001e80300d01103039120780c3d04003155902001442c209590b0048003d0400c01c0c01a081c058190400040d800c042a00f0b0704d0700c50008040c80000d181c1d92209020000300940ba0741613034030107504031202d192250b81d543c201c42180701a504207080046c0c0340500c01d4640c0e24101007155251041921a0503c210907003009030544000507001380c41c0c4500070300c031482d655901c90000b0b0541c0442907a81d680c0395140d410001064461440c0014030a074014801485066400a1407803003160440c031400c202e0f0601800805d042c60b40c685c0210348101c0003a02c0400c14031501403604c0c4040764001d00702c0100b10743e4a06988000030400c0010030401754000d10200040c030f914081002000b40001c00015078503850b81d000504440c0981d201c0c142a40010641d0001d05800c000d400c2e5002159003014042251004859000c80c450014621000c65a600c00308603144400e0f4424409180c0c0241d81965800c6003000801d4403c9040002c0351400300c4240c1d10751b009040c0070442144030f65010740b = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 604234190 1250 604232940 604232963
    0x1804050709090b09100308130906090e120c030f03190f0506010806010f020303010605130506041d100303051c141f091a0f030f01090602070b010b030702060c0c2104091404 75
    0x160b0303005065101c0c0c044a440b2a0520300b01082271740c40d5100d5030000b0482060000b8007607030740345100c40c14600c0700f0f185800701d41c07810b0000c2449002c01200300c422030110543e03126030f0307940c81c405504201400c4054810b82c09290900b2010000766942c0194002c4100741c88079180c9649110044174503203c0c49100c0f00c0141c000340700403c4503a020b0400791442148182c2c07100400ba40300c00103e080c03a0425402103a02000c11007a2509544034a88000d400840c4526284400c0c1e0854070054424464040d1181844c40e9414401000410b1070b40940655440d082070000d29041c036500c10200c0c0704881e44050f100342e210b0003001514003218440c00c0b61050280d004a44a4403003c020085503011000c0b1040d05402505600e09c0c0f4080700303201e82c601442c0704090050b143c42c2141029811400c0c16080203c959800304140056550006a080ea0101c89121079a54483e0030703480d440d08020b80b604040403074541d49600100310040e40400390003624030a10041160b4004005020641e402c1a60081c288003082c0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 604235440 1250 604234190 604234193
    0x6050c0307090b0711103506010212090f041b030f0e0d023004080a1a19150513090203060603070b0a0f03290306011401141804050709090b091003 64
    0x400b25007805006d41000400e5000704035010003c0b2404054803003100d0100001c03400c0165403140300680194080c030090166801c6481003c055101c2c00c0c0e100f0348141c1c1810701040407544c50750400940038159120301012400240e00240c017810391100000c450a0420104950f028000101807003c0302807035000b8101010241601c0d20b07108100340c00e405822042d0b074007040c050503c40c4028001080b0b40c0d0002c0c02000080e0510054603070009042100707501c000c0051045002101e4214800c00c080d600c0006401001c00092140b88100c95103c9904070395030301c2c5c002e00e86950b2944001c06060081c0c0c141c031480e503240e000301510760600d4020f62040007403d000f9031441c0d6101e44103403c0c05a08505002030b04504114030301c00700c081c124240c0d1134407020f83c021907400d9080a010703450042011070b5141101c0040f00002a24600c004404500c98040100d21b1440b07002200c600c40c2c050034009041000036060600000f0040c4800c3d02400d1406410001080b04034246010000e21418181400c00d802038110f = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 604236690 1250 604235440 604235449
    0x120b0f0f01030209030102281205040b1611060a150519120602041d0103050d020c010e040903090509010e011a07020616030314100f0b07020f040902060706050c0307090b0711 76
    0x90084e45030199424003c810103124035042c0703e0b4580c09084240154000c3e6400e0084c02083c4542c40d41c0070560400090000080702002c041d60004402d8201984e04280748400305c0307144001c40064000c40c4035078014845d203682070341c3c410452001210b484060282d00c070028824140e0f00d0702002030f58132982c6c0030304010035540b002c050400544985000b51a00d0380c0c1c1d4609940700c1a060007848038556140327004004107e0704010625060b40107001411050203c130002800003c0721440190059456440003c20184180322800c05071000405000310b0b541c407410000c1c043c44090161149003003240d90380d251541105400d803004d250b17008011610300b0052040c1042001c01c0104102c0501d40c4915100e00f1404801e06541e100e003048480e034041182c505140c2406141c9290b0094040c03102c100408030268075803034038a991040c026039000c02c44509500c0440c16a104803c0b019100d589040103000e5040b0038000114020a982c4d0707295844c15444d20000c08603407080540080952140840d4030515003803 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 604237940 1250 604236690 604236697
    0xf10090f081917070b0103051f15140120011a0117010308160218061f05161e24020a0806090601110a0c08060f070203070605060d0602040303120b0f0f010302 69
    0x9007044413820090940c3c1c903840f80740c0d4280c008071441e4003e80c1f1041c684400c4a4000d0702c17140f0880703034140a509101c0c114030880502c3c0380260031050003a40030804069000740c0984010200c01074002c1e1070b80c66100f024500809071309203070130034000740542e07030301e801b9881a4501408a10030b040868072603407843e40d611b41a40d01542c100d002248080450102580d00c05091074100c0404030841c40841c07404204000e0318842d40c1034882c60050640f050f0007004da40c0281590002c0000418101c540c01c45130410309413071041150601e034111121b40803941007201100b02c542c803406018407102c0c1400310340120f0700146e0081e0004503002a08410000d445031400e107030b543c7d80088041c1440c24036440d18426807030034100401070640b80401240c40420081e0003c0040b01e81c42500c500d010204c5040250009482c0d204140c400380c080d0f511100418500d65680002094003070340710800315542d03540c0313140143c581410030700c404d60f84500c2c3c91441c03e041d083c001300031403031044000c02280440c003031200190020741 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 604239190 1250 604237940 604237973
    0x1005030705090a0302090c220602031c0b030d020a17030c0304082206110709110708030a1b030c020c090c09042714071e050904020f10090f0819 63
    0x11100e400040076880701b20505014003c09602c0940d40c90030000346404501084076101c0d540c0c40500c10400901d03034040180c0703400d48205880f061700040385d450700b00c01529034414600d525001f00312600d9110798000a2406489100c0c2c2e1103e0390480940151a00c2e13170004079800c0800c2081000010001101140103020080c0340400700e81c2c9032488031580700c840c201190000130100b28200c0c0306811002c01004240001d00d50a0814400b010540c0a545102e004030600103141c40c0012001c2a00c4403065000394072004201140703601150700030900100507002d040080f00250156034090302c064180321800c81c0c85418282d41c0c1b02e180490071310501001f41201ca990803007582007072140c04440c1004024112803680529651050a0401048a418240ca40c1e001c0d000b406130303110307070340520000e02c6001e802210400c65509402d559140003080307000d142e214099a0000301d004d004903402e03800031142801e90780c10010941d0502c0d20f850040d0b45e0b86028212480c1181c6000001c6000643d81454080051 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 604240440 1250 604239190 604239199
    0xe1602030c01060801050604060b090604030212120a0e210a08030a110f2206080a02031801090510060807030309090f0e0d02030c010507031a010f03180c14100503070509 74
    0x1040c100045421128a41c01203000d1765110fa090080a2501e801a00d01404483c1e155a02d0145030000240f0948624030000b80100c21445260341c0c550814054581c10210305000c580d40c403008400c00504c03408010f07480520400040d100c0340b03c020000c51700011103120380340040c0030078034181c3c4503841541c00003094036060503260140c510003c08520054a802000e505401c0e071140b0343c0c050054400c1d03c20303e05107080d00203008800c0201c190310004254004070030540050b580e850b05800d0b10b0309150b224805072001d41c00c0010100801c00005030001035035640303403003c00207252110001c40c0c90f030107144006000030b030700301c00c0600c0700b007810758043e131360f6a45121000618000514402070410769820540c8002d43c0010500188401081c0a010380c48032441c60104101c01c0c1101070035001e0701040948504010000c21184a1680603a000204006400540c10781c651018a88211403540c20b005003036100142d10700e40c0c04103003444403089a003c0035540b507890440d5150007080b1001d80101a050742e02 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 604241690 1250 604240440 604240447
    0x51005030106030302070e1602060114030a06240f1401050c0a0212070303090605070807060b03070f0b0405150a0503010e090a1506060e030c0a180e0303101503060e160203 75
    0x56900340b05503001940b00340c001d808213501d4420020040c103001001c800700341d0307054103503046810741c0481e1490540e41c944524103480c01005001c285801451040185075030300c0c3c01290400c0c1b036940c550070700c49900304444040003d034071000f2004e080401c41c45920b40c3c06030440c02001041d801180a480c1503101541181c400042d5600040c8410100022039403040e00050710600074140d101303541c50082e0903a410401e02e05200703a51950807510410202406440e554a59500103a0f000d210301401007100150048070181c0398052080b03240d205108481c403078881c26402074109075407a800e8451110071525400d040d42c0c640410000e06c140000c084056078052518102d0005407071000914901c201807000050030360800d03101502900398002c540b07110707902050440da45581c03601410301c10b86850302d03400350140401c00c0c1d0038405040c90070280d4907280070120410601520080d25001100d00d007050050b00c507059140240c0c12100c590040041360940b403000a02010707640080405228801d10480c0d15 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 604242940 1250 604241690 604241699
    0xf0b030102191107080c04020706021b1f1e050403051210150c0f080d0b0604091a060c07060e06090d03090e06031b1c021008040201080c040602100510 66
    0x1c80e030015510464040100c10595051980b0500800500d050500103080050030b10b030850f82da902940c00680c0c429500002c49404000700b54042d9008544003c81001e26a1800e949042e1280c05151101510460040c040064504903000e00c6c0001308640020380d141c2e403000428040a82001002601840010042600b418980740540c41c850b081c03004030425107508200e40c42454420389464001040540d00308040030502e0100b8914400d94480707071003030340c0b0000307210700601410003480c0241e0301c00b4010074001045002600329420304500300002562005141e8100000d40c00744044c141c08581c401d41050280a00800b041c804511006141a060900d00000a1011059103500f100041d071030400c00c00440c007912a1980e0000400c60140c090031a4581c01c0300913038810111694030501050006108a8000c0e05001c020603801a011180082c00190301804070131060314101d0004070303007500065040041c81d050304c040d00c1650703026115201c01c1081440107060050703c070b5021003800440025 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 604244190 1250 604242940 604242943
    0x60117010c0c020f1f0315091406100e030a0c08120406120207020301110f090a14030c01081e040b100906030215090a0f0909020f0a0f120f06051510020f100f0b03 71
    0x4011030255800300381d00b42d6911f00100c00e0440c95201c5403060f0b05081d903480c03071088510a4070b41e2202d030580f0b00010303441d6842c0301200c0895a10525a400d400b444260100380b045060f0410705440c42c540440c2c0c0b55081c9100c00c034009118074416040003541e0030300c1590122403160002d114250009002040d150380c000490b04540d408420b00707092840b800a0720780520b040c120f145400070004804030b00e04511082c40400c2c0c9800b14031008904020800e40001c0341c01c0030100d01e00350740784d11400c03801d0350910b0503145c80c50b4401015181003202008a00e00052243d40b18061102540d90141ca000b04103040030740c000425421a160039030b804418040003048058170060604000d20805001059484003030040c0422131460030f00d028059491240148200d40c0c84405a00c01c42e8008038200c2041409424101c4c03001405180c010f00107410f06050003201c0c4980745030454180400c948505030940c1c0045c1c10381e0340e06d2006851030200d0304002d9038205420300315072144c00d054100120100c0d01203851000039 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 604245440 1250 604244190 604244239
    0x9010b1c0507030c0f080c180a08010504050a0302060112020315060607050a0b011a070c0b07080712170a090b07050307050c0105041226010311061b060117010c0c020f 73
    0x200d0001c0e84d0b49802c140c095034041d00c191881801070400180a040c05100d40c030551041c00d20300040180607200d104110345400915030010001ca07802041103050a1a002c2d85030b50400c1c1c01600148074480000c10300c00104400c020380a6401001850f40041407480070005003c001c01e80d0f5032184061200c0070216200307000c1c06842520039440e003c0e42c1c0d814090b1026030500e2500020b22484c1c42401640001169000b00c1015071b801d4040d0b0649840251030280d84a110790746004062402e0600104041a08001c080f06184040c10403500d040d0796105410088a01e40040600340e0320180f0045148ac038028001150003170000d14050340350070200d04e0414291a01035030100c038183c0c103001000f4005580303c000300e00c20b243c0e201900991500d00b0010a6502032041c080a054402094030b00c0079141d0b68481200c694010b5451201d824040e10405a901c1d102c091151502c458401d081009140314184100301c9904034035180d44030703410a2902800b000010010801d5000b0b4810f0004030b4558401e0400c4 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 604246690 1250 604245440 604245451
    0xf030f091b090509010204050f0402090a0b12101d041b09060f080d05121f03020d030804060c32130f031703071d0d140a0303061409010b1c05 62
    0x601e0501850102c46030100d86004140303451a0b4070522040c00140e07a11448000c00b00d00458000d80c64001c44000201098100e1744031002c900c1000540030b00c00c24000e82c501c1d20400004100c0c80701d896031484641614042c0c0300d041880340d00d040e00000d00082c5e00d608007890f5907413841c100725049500c0d450084100c40e040d4019520000c0706032001c109050303003080700080640051a2582c24801c01c40710704200c1c0300d07000e0203001c0710454000c24414001d42c415855002917400a20f5605502d0907400c020b03221620580e81652001d0400558042440c0115806041c2c2e5107212880600c030071004083d04001c1e8507a03500502c4034003041098558840c0d024400001800522080b2079100b46586050700340e01d107501c4001c00d80300c4800d0003007020032604107581c610440b020b046011000b403910300000b104807000090080c5031800c007042d0516420b40020b08185140d210742c40070001c00d62140d01c20303034645599038030003540500d911006001505502d0041c003544061400e840d203100201540000a40d02d04440 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 604247940 1250 604246690 604246733
    0x5041a09070509030f1c050d020c16031b0e0a0b0315090f100515120a06050708180a02031b0307090911040c1b20030105010308031006050a0f030f09 65
    0x8034910113140074429403254010f00030003000e64804200d41c2000f041450040001442004a01c0e0300012485404031f410300310003070b4190303000c0d5030307a417841c2402c2c0c040580015140c1e402c1040c000c1002c403840c043c0300310a0703c030704c524584211b80e110260240680781644900e40c150286200c0e1705000c0c0a1944010b0250804c80081c00018080c6030366146030641c44105030351128100b100344a401c284540450754020000ea80000700b465201c0031480ca0881d9030f510007400907250004000e8110707400030800307002e1036810121000e00c1c0030711601e0079a030b00042c50001e03615400c54200f680300041b00701321103502c0a40103000d58039120f076038141d5803080750031042c0d05962170000022100410700e07051281c030307569503e1800e06210480d0360044107820080480340c01481039100c401180303040000328644025000c0c004001340180e40e1a890107098030340080c2c039504a00b442000020441c00c2c06101910f100c0d60840d41d0f2000828001d402c114050803d00a00164081d0b03601080c0021404010108076010321102 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 604249190 1250 604247940 604247947
    0x210604140a060501080c0a0806010c080c0a0c06120903051624020a02162103030e030a050706060e010b0a05033105070806070e010c052b12051005041a090705 69
    0x2525040c0024480c0b40386d40420011100e01c0c0307800120315a041502841c010580528924150400d440f40e81d410103100e02c542c011b01410821080050001d440c2556500a2100d404d03200210540d00301c0c1c0c00c02804500c00303200041701e80d801c400c010034030380f0b000b0b0303440000d541d410001440042c07981d0000c0510b09a0000780001c42a60104603891011200c0c000c1c08511520700081400402815451079107400d151000b014141031082c1c01040708200004144c03540d8190055000c8c15580c45041d0032906a42000c0340080c0c001e00341ca25960486940300c50355890300002c54001c5800c0e40c40203240c0144820601c014000000c030905100d006098403040c003041880d12401d1162a100081d840034546074403800400018907030041e00c15040c1d29080c2490681d10106140aa080048142c030349013941041c01c41076a902803800111310381d4502c460300c1e0f41c0441607101086c84240e450489a0b05455210000e00300302600f001d0f80320300441d540b0748504041c10005480003560420040c1d40c0c400010f03a010 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 604250440 1250 604249190 604249199
    0xc07120809070e040b06090a0902100905120a050c0907050d0f0506040506040b010e040209060910020a030809010216030c0203010209030a031e0801050d02060a11070f03110402210604140a06 83
    0x204000009031400f500029104d04e000d030382e110b1044500500881c05803034043d001c141440307910b8016500c804c0d801800035905503c688801041e03400c2d1803051074400c10420380c0490843e0307400f0404c1000306c1e030003401804200d0710b008180b1007664005090501002002c20200d003210429111342005801400c1000c1030a04140040205444c005445c0030320652810300203458503a00f0044050b0300c10710a8130056225017103140002c206000b0460300c95000201c04510345589030f80400c800e14094800c4c0c4928441da100e82030054200c1c000c0c00021410b40d0420761100012900880745032140a10050000d403070a007000012905103050321070124089600010201d286c100004002820300702ca80c903054140d98508000251a1075441001900070348000032407a002520680d031103041c078140d1101300c4400039910280e40c041c040d03a078402912450441c09020380c80385030a0003190f200000142802c495400e041084070a44180030b0034140e40039640d14642e140445039059070521a507550350f4000f0744c0724a030 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 604251690 1250 604250440 604250443
    0x7090c11010e070528090b101b030e060715050402120d0509130207080c03120a060303080708222405070504150e09240a0506120c07120809 61
    0x400310860564140400c01181060019030602103038030403503a04840c200b17480340100c20038a0203112090103c11001c000b25240b24250403038a9140420f550841504ca4038940440360190400d95013080c1090302e14040b004a4411150100c15460003030215103020f546660340c001120031500151920354841040106514020014110034410900a0100c1d03070280f8600509502c5800c1e1550310401ca418041481c241543d4181c66400d03038000c41c043d540d090003042280c0d42c1d0b00702061202c1800e0301100050290580c5000d004112645074441351000c3d1030f40f80041d1180f03000140030003030041c03940f01c90301c45c400e900e07c2000042c07501030040d281e4006110030307071911065003003540160624140400c2c0088907034031070101c42c11111306c040c10720b88120f021039044491205005e01d40758052100028400e040122902480e44c6061030030146c4006040c880900480160354800c40f41d100c1e00603c00001e03e21100c0846035030103600000c0c8545003250691302d4000c200943d00f41140001d00050400101000 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 604252940 1250 604251690 604251707
    0xc030c0102010c12090c031a0f0a15050f1201050709081002030126070f03080c0c1e04020c0c0a0e010303091a0406050a030209040608010203060a1d040b071107090c 72
    0x202072009020303034556035801909030884466070f800e81c0c96960940300d081c402100c844401a540c05600000a26403000c1c10740c0d007404040c0d514180c06250318002c64201c1c4120b104180084401d1040035181501c1d201c10030001084491005d500024840004401c3c140203100f2248078455a85404080c5c03030a00004600d001100c04d40180d0f0903104000600507540911480d181800c03621001e440340c0d8602010050070125176902180390030104041c003004220119002c3c152a0709070380210740c0c00d407991f01c2c02c00284e000c04e441031042041b0000e440e80c240341043e0300109410f85a880c1190f400c02c2001c00820312a9195a000d508003101110060081642c041d42030401481d00511061f43e241c1c4030074000210344600c0c0725050500c03400160039403446019805403681d901c001001040910b548407502d81c081e40c8101e03189441094522000703d0040344031160f1201d10700100b5003243c0c5070703a619030f42d06a20810240c800024408840100100c49104000c4100035041c1e038240413804441016000d4840308 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 604254190 1250 604252940 604252963
    0x12160629040509060c090a0e19110310090510120f11120613030909051303030c1407021207080f07060e060c03071209081504170702060703030b04110a020c03 69
    0xb8200401c3c06007103107000039500d80003d02c0b090b40507696040203000514003040f40c4c0c4040c0c5528060000c0081d4194284612445614591014842c401d2212481d11182c40119643c5400304070255041c0200e081950000c0e030f114190022101006441c0c01303039800c4081c0300d814101d845c03814040581c3d04010740400c0212010409898601c02c450009850540354440100300c2595000004807690038941f0400300070005101100d0b0400c21810f2005900c0400c22015034280c000c00d05008040c04e28620500c02c20b4034820840d0f440c1414071400d40c2c20095084104080300e0824403c2080100766090148440ea4110070302ca0020650a494444094414400c60843c00d20641c41401130b0b04003118080115862964080e0014108544680c403c0c2c0d14200550041c0503184103024031104110031449040b0b00407402401814540d00005c0d00082c0b0314410701c1002034005200b400650000f0713000c1e42100040401c000e201042c210002c41c9401d41039008200340800503030041d0b41110840c1401d0162a8411 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 604255440 1250 604254190 604254199
    0x1090f060f140a0509030d050108030703080f0606040611070f06090306050901060311040b011116030b06100c03142b0c0305060f011d03010204080c13060812160629 72
    0x1152001c50b007005031840180003188954503580012004003041c412280721503004903080099517121100e4594a401044084011881a4010848460010840e144202801460340745000c0c286081266000e2104110603072038428941c1c0446c01d10302c1011071a01410113643e60040f180c0c070318104081610300203000c81100364501142440454900c07000c40e02c20907400c0d1800300340702e842440121000d1881d0a50084a400f56100180301e00c014888280d007121b0050458241507201d04d010801000548107210700400c0f0b81c1848500005d0140b604051482d1240700504d0801001e0f0b00c00d001500030600d850300c0010207105695030444030900c1100e4a03045136107000c01103413400c10b0105c0d022200199006050107c1e00540070542c0d03842d50300342c1100500c05002552965980d4050039690f07050a0501d0344a0104c403400f40703030700d00c0c030303a01c1000112440400202007000740700509004981c4420b03d1200c0c071820180307005020a0327040c0514011403c407903000c032102d9001e070498103446505e801d54881c401c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 604256690 1250 604255440 604255451
    0x1c030204030f0b09030d09060f0c0e030303010314163209190216060605090105030a05030a200a0b090106060504180203060d02120c0a090c0f030b1201090f060f 70
    0x1c01c022040b0800c01c81d0388021500e0302e5441d54032905145005004110b40303580c0c2000c20b81d00070484550848541205040c0083c0b002c84007524003582c0da042e6050340c142e0940e00600041000c11070401444e01112400020703140c01480f894034400b030980c0c1c6600900c1c2485103800440041036407580b20100c50320500f507402000d41c200d180008940401c080d2007400711240d50001ca41131450240c0c1280c0c15600c43d200c08610a44142c0f520030050155072107810310a80c90100001801d040c08161001c140e41c1c400d0165140000111050b40c048a1200d6014000702240c0c80342c3e68070400c204000d988003805480802d00e1403034020003143c02d43d842c1d80c0083d410403070140400c000f160f0b03200c1d0201a900e44d42090158603940c40f20003180c0c9041c4000d03006540207050f516442500e44012a0030084c030f403000c1d03031903190720b5883d40003100685030b8402500000030440080284401e1103540140011a001081c00c50088801c558041c250f401156040da801d40c40d844800042044500c00e603203000d03280d824207122 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 604257940 1250 604256690 604256693
    0x20907110d0807020a02190b12060f0d1505040f12050c010b01052b0b0a030f0507050f0f010f0c021201060509100503060118090501050f011806240210020c1c03020403 73
    0x12503604444001f1300400085900f103624441c7d02c81148080d24044a803291503d919030380040c640c04007520614090400d101c050b100d981031441c01d450145030007125100880d1458038105c0b009120081007034401030036004007000050300410700c122060184d13942c3d0366200d0404e154546d0868a910078418103011081089001c0e0504124140d184440e1441d00d400740100380e900381354003a00e407501805501c0001c5400200410034a02d14109410b40100700b260b10181d12042070008110104a02c02d90048507410700c860150f100b0a07041191400c186002486100d20303501041000445071050320741030b5114001400f95050030200613612105040c0c2080ca064580800310351540c40600440541c800740c903011041444860b000001c913330b03900000800043c981070a582010315802e0045103d02c0d848030802c144c80e202c0c140242e000703a40034080ca1415201c21102070400340d130480c004940030f50040703900c4041e401900d88054107085940c0006440079104464206040403012500c1d4024184140001d10 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 604259190 1250 604257940 604257943
    0x20904110d5001020417150109021812030903060a0b12060f043804060b040b100807030e010e0c0306091b040c0903080c01270f020906010507020907110d080702 70
    0x18982082558040d909031807002403076003e0301c40c80d01b080300c41d00700a004444442c035000038402c100b140602da41c580c3d00d9803a009808282d2150030f014040f404800b030140011840c101c140082c40d04241000c8178500300c565004281031440485103a0755265841490001d24103065030a01c090b0038180f00908614607090002111468020380094a0242c9038003882028034400500f84a180580d21084080303c0241c02d001030309400700700e0b003c88000e400e12404040e04e0a2034060311f030441400070700d15451128102130494039803000900d070b00109601c91010303007440c50080c8070389a25000d80e43c000d405900e90b00b2040c140b030000044c08100c5641d002d1041800e404074404943c4500140440300072511414010048600440c540c002918801c3d00041d00000c1940542c08260302c010f4210710004040280314042d1401056940c0203002d98052a10744001071400d008065032215050500d00c0c02c0a0660b0080f543c0c00500310703070500120300070020007445c48504002128800c05286045051442c0c90003000303 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 604260440 1250 604259190 604259303
    0x50402040b16030e120f010b0904020f131104090f060605190e06040b1c05180a020603040c0902040b0307111606050c1f021b06040f020904110d 63
    0xc00c2c104240600282018810064422210401452102e0342d0304180702c03980d02d40000c00500c980c00d6182015190203410a080c40d2481540c00a0140a009102006201c8412582c074110b00402d9550411b0200c000d050030080c001611010100145501580620300c080301d540e60000c00500c042072001200405003008001c03804c5e0400c1c9481ca038241421303408591280615004910110000f191031030281c1540c4040606641e00900c0c2403003d901c5d1545030070220300f0401e00180460f0012210800513041550080d0b403c94410060304003026603030061f250403a0025044110446c0c40001030040e5107600c0007074200151060340c01b8007810070b0610b009554400d114400d11080c4140812034810210f020302410407641c003454030300c000c50442001e003100294442c0038448059000c010f0100c0e48001d001818903c030b6540080d040040744403030f4080101540d4024802c030346e85181030207000e203561130b80b12000c1411882128081d80c0c0341e03028000702400e0f0f03001c80704500103550001520000d1411020f0b00 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 604261690 1250 604260440 604260457
    0x15070e1905062a010518011503080f1605030d020a020d0e130b01110a05281a1009020a0c0309051e0405090307021504060305010f0807090209040b13090b01050402040b 73
    0xe9007032660140440c501c1052248010f0b10644d440c03d8108a00164520641900c03520110000c0100d00c2c3c50030804e01100509000240004405001c4010403a960310010015130140b403401204038440307035583c50b20303560010310036034503854004c0fa08242c0f050b0100031144000529050403108800704a011a82c8106455280103600c0e4031003842d40b15030303401405007440d5002e42da0166054008241083d075510300c42130b0b072555140007000089080032002c01400a010b16480b03845403042c041402460112108054a81c100004290382c00245000303040c4001c22003181a03840700c0040e801b084c20054112001e5602a6000f800305000c17502c40742c0f041d020040d01d8600b04441c00100d503100c81281c1445c0d4081c014000703400903031840b103080542d21104054000c4880a58040c0050b03a01c136500c09600c03003010f214007500f030f0f888004280502c03001c0da00607000316200a4000a0500c3c0c54070300049258941c41c1403200e9043e40c400340c0b41d051014210350703203000d80801d4030f09502d4070b46414545511403050810 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 604262940 1250 604261690 604261717
    0x1050604120303050a11180f03160e04210906030605040204141e0a09021b240a110424020706020a1401020408030f0c060a060303090b0c15070e190506 66
    0x9103c5c0c0d01e0a0740f100e4005184103000a8031040034006080c0600b0343c19801c203100b400030840110045c50005000da044d1100c1010040380c95140801c90040e40d10701400031039904c0301c8822101800c41408c00d405001c4605699024812031500102404030cc00d280c001902850040000f4826890307040c010000245050b60301c10030000cc0500e11a43e0040c90400305d0381e0050b100600090000f0f8545c0203029034001c400d55600c0d0030341d2031401d0303955548154421044c41c0c001c85020500c1d42e02402c0070087d8080124180414424005a54103a0700da01039009607658902c032400004e10400c865540031000d2115000a045e070300d0a01d500a965081c4424000b06a043c10700410800e111003034060b03600030044034040740d44074404130300b1041c0d2540014400c601c2900c2101c0000d04012114080d940441390151100b2410342e00380010134200b9407003d0419100340c441c094051020000c0d0b601c505110348140c0da950400c030360301d8004001084030054076080010b021340c4428404c2d55951812500715110790310 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 604264190 1250 604262940 604262951
    0x51e0f241e010e0411120604090b010e070c060c0f0f0c050c060c0c060304050102070318050901260604050610060206220c0f06080618070f0e040b0910090501050604120303 75
    0x1203914001c0143d00c0350b0400d003000718a031101c543c21009405800c00404480c5050364414052104594803000d000d450003c0c00d000420a111060b8002900580304d803038540310000941c0c4440c4252088250a100003c101040c80907240c0d81c050380c045101d0405250032001000300340c8405942c1d24401c220300c3e220302000129941c400d001001481c2c20300c10b024101d2170701e074a000d04025001f034004203020f03004261031203104041c0c480b01e00010320a0390300003414456130380d0800461140031402c080515a81c503140803a5401410b50410036a40300b184140010000303840c1c1220f440340d45d522950320100644d070090003442000080d0780e0411f1450340c0f01250082e04c030002c2d818001c0e0100f0b4181d104079042440d0b6400400c40c0c603440f0125a124100644550240c60940d01c036051039074004440000000b00078660700001140310b40c2da0304040150062010804030314860000b10900c000f51040c010080c1441d400700041036050040310300408084a22f02e040034609401003944030503080c0c0003000c00d983c98 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 604265440 1250 604264190 604264249
    0xc01120507020f0708031e0a0206070e0a03050f07081606090311030111040b0c070e010b16080c0706020c0406090b1c17040b1b011806051e0f24 63
    0x20440c05820f05142000c9525155454445a07101e5001c1284003400441000300c03041d180102c075044590000099004103100e54a2803011942038180c0f0350f078207902c0014403200001162040040500e02c10940e00600b4070707a0b1600301034a182001001404040c1070500400300921600a5050720031240c0180e104030480303e001d0002401007034100381c0c0e8030f904540402c2c08a62741100070080e08405241c2011a038410b43c4032450000d01c40c009100b41060700320f04001c044d000b003944610f81301e100d604ca41c2110f030401e01c1002c500e6090900c0c0d81c012100581c4032038420141c2c0d2a003802200b00801e01e024040188401c8540806e01410900507002c2c548448003040c00c0c10440008461850410416002c54880f0b480302c030b0524590780403680320443c0c0c1b02080e000c1010710f4018400c100c0c0004e180f40741032814611560310700000d000010406048505e00c0004d03403000d512103030083e5104140300d010708c0410380340510516000780b84405009026802504206500d5150781c1003003080b91400107966104038144 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 604266690 1250 604265440 604265443
    0x403031112030f011a070b0601052803090b0114010f1815260106080105010e06130e04052803030f090c08060a0f0b0d060b0a0306020f0307110c0112050702 68
    0x1c000451000980042085260041c685900e41030301c06005078600004840b1440745254000c062014080c1801c52010881c258020340040c0a00c56001c1a0380500c034404900c0b40305141245220900840c0d211440b0b001003022030554140134142d02c101c2c0000c10001350000804212101440303005108144440d40c1c0d943d04454060300003040320801c0c0212043d82d10070300078401e0341c11920441c20080540a526414880301c01c41c14140c52403aa01c50019a2030301c4d0044034a5520307041c0b160f4000104021036681e110008040001500c540010111a82001d02d00240703011603105d034a80070300072500100e040324028040a0350b6003d406140c04a10f0300c1c034100200b00105541c0c00000c0400300201070000307855601080203031007110300c1c0c2c0307080003220707403440c6003105a80d1001e107a20350000c2c04000301400110035a0100b0100540502003001907902c0f952544100d03804104c0134003034a80b021042096030755000d03c50101d485844805800c41a0412002134034152480c0340401ea0030b80c51f9000030300f40350310 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 604267940 1250 604266690 604266703
    0x7080d051b070807021002030c061b070b010b0a0908120d0506041803020c030c0316030602030c0903120405090c0a2c1009051c1a280b040f1104030311 66
    0x40214060742d40c92149040c1c80d041d84224000c038021800340c0708a04480e800482502c04c0d0480c840c0242401e642c0344004035001103221040608060014400c44020800d8001c042d0b0280c0203011005685646010024010380c080f54064040c0390b002800300305081d0300840c16074080310b941100209a6403900400107011f00701110b41d070045019094038041c28140e0009034884000c0040d0300f5560503410f90b505150f22007a0342e104806004520b0780003000002d49075402554003140018a44c1c0c00c15030400c002a0510b5186c01360b0408030324001c2018411071519024007504101c074107101d03614040414038050304d5440105d00800141054124000160505014021030b00d44000e100c904440b008020142c81110980540c0e401a049441800814005921890300c40c0d40c0103120f400d90344045603c3c030b00321002c00800072080500c002149454440301d10103a004040d007406004039101a541c000d01c0100c9910300d15401c00c15082ca09140760120036003045405507078041c5054a5440034019a8914000 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 604269190 1250 604267940 604267981
    0xf050c010f0f0218040e0c0603040c120c030c0905010e010b071713081209030a0b0406150905070e01020109020a0918020d05061009050603030412031205040506160507080d05 76
    0x504000c40c2c80c0d1450701c654014656612400c0b141d41289801e101804101e0340301d40e419100f6a40468080341503450560003840d8040d20070344000101c20303114513000c040f15049100407a040b03000741e5400d004024903c07080308060034142c81d00304519031400110041e0b41d0011f10400070521000107111040c0001040202021003100f0360b0b40d540c07180f40c4000c00302505120f02c200d80c0c582c00b40415614030b90303024130212942c040000700141007003440d94131940d00340ca6001c2c10444a0f160b890b07600031411401da00c000c0300280400000003d82d0720307010501905401c0300e0303000103045900d020351341ca0050780c951480109580701e0360800900d102d000b148401484d03485400c00386d400962000e441082250008400c0c0c46420b041d130040003a00e9403040e5010a945003a604d031a410380050000303128400c40040414611806441e000102d1640c20301410704446060398280c0d020f030810820000004986414020200500d241844c80d1034200d0300d482583c2c0c007031084044190390701c66002c0b540c00c0c0f40400b10035400d103 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 604270440 1250 604269190 604269221
    0x130b04140a12050307020706080103020d0201030203190905151806040b0910020301091d0a0c03060b0607060e07030b09030f0d020c070302131b0801030803040303091707050105180d0f050c01 83
    0x6580b118000e040742e041201c044006204009010030103d02c110480b40c100c980c0501210500c02c1581d0065020f274200074814441c000d0074050f800e441800364003e002c0341d140a880030300440c000800d89910310140c014051000b80b410300200d5003010400103012580940c100c2c101207283d8a4201050b82070003c8412650000d50020001013403111b40c0d80d10400d00b140c010007404440c1c10511440c07640b81c0040e400050403960891904002046040d00807800c8404d000b480c0624088050799024101d810901c154640d55110440034003c00c040c0c8240150040c085000640c100100848181080d102d1581d051a1068010440717002641042000b0b00c0610380c02428448014101e4078540000c1c9604a0290f04107031101c042d1131041801000c0721810382e600320ba0340c3c51035659651030030f4001c0c000c0388004030b03461100710581c000701c0030b000e10207091325030310481c004a05424541c0e000801c482c4001c422004d10382041c46c440010700d4106101c010b0114280c200251100585165103004100d400b5050010 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 604271690 1250 604270440 604270463
    0xd03050907170601090c0f1b03300506150702010e0301151e09021303020409020a0504050c0d0f020f0301030f03021023090c010206011802040b0c0c0108130b04140a 72
    0xc002c400309140781a101075440030003500c40080022920506a00780d88408291380c01410a83d0811401e40f0b800c0301e60107820101c41e10100c10000e04520140300c100f042041a035006120803405d083d0003901e4020b4011030b40300b4500c10302011850070600c150b550080c14011500c0300082c1c203817405e40050921a888241c494501640d0f002d80300410303940341810015004081c040898010013070301c02e0b68904040c0c000c5460b50181503600b44801006800381c160b9200358103407000100380d903560181070711801440016984550200c1c8034074040d039003035442c00d01c006c0f40140b03c01c088414803042981d044a13004000c51401400d503080903400c0c84c65002c0c40784420b03420204661501c601e0300511038a1455100b034004c0d807981d1000486070329901c0021046005030048001080802d80ca03002c001c0d8100c004a100503d00360fa952842b03101a0b000d01403081a0790041031480c5a55030f00840500d03030141f4103440703c40301c40c0001c2c0e4aa10803110010001440703031407460003480c9204820003102100c2c585c08020740b1103 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 604272940 1250 604271690 604271729
    0x16120b0403112e0b090c071b0806040201230301030212030d09030f12091a06010c1709150702100e210c0406120f260c0a0209070507030203120c0913021312050d03050907 74
    0x842b09811280cd034003140d07044c2900440c07402c0b030b01030680c000550718500c85e0450f400c5500301b1041108000d07101d002c620007800044e1014010344204d0580a100e610303004941c103410700d0301420300d14050380c20800300c2e446c1a08800129074651890699000d045400480030765440300182e9004940007000313030565440025409854a00c603000b850a0a82219402c015400d8241310f01e125208405000b904909003030003140704140a0451815040802003002808483c0e00d06604680d401100007650146d101c0d4940c100c042c2440d00c18103000c1c0120400038440b8000719125070300307041070698000b000400c0740c1d0311909000c08070548940da0b1070b010001135035507030030840e118550f1040d108070180c5c40f503020080803a031600e001e00f0032a5440c9600d074007e1420101700c4816003800709030050072001c40750402c2010b41043d0343c4980010000c540361281c01a2500071204140a6014031908141c440244102c1041701003580003c0c1d042c03401c20103207000300b400e03556960a2414880c06501400c48a4054642d2a1 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 604274190 1250 604272940 604272943
    0x20c0a0b18060c071e05010b15030a05070504051f022d1c0c0609020d06050106021e1b040504020f030f0a030216120b0403112e0b090c071b08 62
    0x9035001c07a00454245880310034428140c0e00c1a00c2d4020140840011451510303a410303121101d204c0d00501c00000c040d11060f0205888002c007011384140c00400004000101e052807007865080041480c05500742030401010501031b150700c0031030354201104d030b210920f14180308001008003000c1c1d100e02d001803024180b900882454000d10641c84a010307198070044509080303002c50000e064a59a1000c2d084c05903110300d002030403107007401d03600640300602000c0464050f025040c001c0c040c540c001d0007002c00c03068074039480c001a40300c251241e130001c100e00f01c0341946003400682c1d0b0308402c41d4001065241c910001e600000c669003482c3d0140503041782000c001c5004204045502c0c040d400703503488201c04050441411503180202c80b0130540e5480e1540c041560134111070351292081c20580c0507200100394041c5400c0f000184c0444d10040342082c1400d00d549940030300078000c6219003e00440c0064000154941c00060a0b04145600400e00d1070900181240340c150340b101019010542c10345601016 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 604275440 1250 604274190 604274221
    0x2060c0d0e10020901110d140a110a110a17060403030e0f1b040b040204180b01020f030c0105070e06070b24060705010c1704210c200108010f050112020c0a0b 69
    0x141c04100c401b0381d002007034030011641d64661b40081e5194100303100c4000146070b460700564102010840b0000a21380310100400c544030640b070003004181492a4202c007004004180b81d0026100d040da0962030328034148001444941041d1306003400304084030107102c658540074180d04502040e20900346440c60107101c10300a0303510302d03c0c140d4091140d16001414003090b80700d648140c0d0f41905189001243d0942e45034081d5154540510541c3e85030078009407814515040040000c0440c0d542e1410711078055007100350310710b8444003912154100300c055281c01d540b036032000742544080c1282d114901d00f0142455060a030030400103000e16107034446e07814054000e0010b42d40400100c2c500c2a018039100405019480c400e40c2e0103500b00720079a4401400844034041d05c00c004060100902c011000184500100d0000d081c0342c404c50b0180349015400100950010391004070592000c501c24851668404154000800b11010242c0d9808000307c0311441e04004540123030002c100101880000b00e01c02480c03 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 604276690 1250 604275440 604275457
    0x7031b02010e03240702211e0301030b0702190203210c0a0503090a051203190e04020307020a02030114090705091306060f080d0906080708130203061503070f030302060c0d0e1002 78
    0x44d41d4403a03a9080c0180d98851202d08010306409065024401380c01044c001440304c0c3c105c0400c440341090300482403010a0b0005e81003184c02407403034070800040300c1d410008100848142da020486401d030325004251629054030100e07040503030000c0c1e0443c8442d0074100719002c1c0c8240c4000c580045010303007011a1aa007002480c2031150704080400189490403d40e041c0f5441c074401c015615260744841032640162030713040d0100c14801c2403043c9000c00d95451005e544504540e070050051040720340304140c21034007400041480321100c4002c2c00385100700041e1903800e0780d90a0f04c0f0b20039192580c0418203c6841a0b0750004c004074204000480c101500e04008030484a00e030b42140c803141080c2205507030f40121405100300068000001961b0320b4403900026801c600132400003070b0b012080d600805d050540884030110100041d000016403824100b2641008044005028501e507081d950300035101c41025056188010f4080788007140e8042e03a40c0554008400c0340304555220b03011403402c03000f94002416 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 604277940 1250 604276690 604276753
    0x2060c0f070506040b12071e111e060610030e0109030f020f0a050316021c0305211506071e0f061103191e02120609010b07031b02010e03 60
    0x1c00142d507040034800d41e0241d034800c2440901b091000200d90307a0701d9000506c29002c00400250080015000a01c45001c81c5c10655400780d030124908235aa2600804418071000440411020440e42901203841a004201200c00d00240400c50b030045028084c036100020543d46021180d104240d0441a00c440c0c42a80d80c01f034a00005581c1c0180e51229080381c005000c0342c10401880e950582c110303a81601a40c40140350324245440e10840c00b0004038503950440200d02d000513040010403800010164204d200b13103800c64107180501900401c0440d030130b681401228003240170030070401c0110b020f400400c480e256aa034400044d041804800e4a1500251802031401078000d40c01d140010841c1d00c60402e134504a88141c0e111b03c03c0400819004900c0440c00039107402e40490740d0180e00007031585140c0d0758a41102030500200308205100c040e48840060082044001c2c0044d4001c80c0025030800030b1350406d010f445050005071345030291652055494091445103030354880d07001c01c044401d41d03070010 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 604279190 1250 604277940 604277953
    0x30507110c0d12120e2404030c0f02062206090b0405030309040906180f030e090f070c03020f030d09140f060703090503120118050f1e0c1b030706050c031509040f02060c0f 75
    0x1246001b00078029035007e400200020441c5c0c0100e0343d42c8202e0110213201500c118030f040802007d5482c441030b040311a0030010000e0324100700d02648980c19801134903039001b88074030749840c1c100041e0b600d03c10794190a000e181c40d000d1982c03d10480b68440d401c3c40e5060710210303080d00940d01c0d2415600c1c00c1590220003003801541d003603031035040c5104114803e10407032400801a848402007600e265080300e030304504510071442c0015100c001480909042094520045942686407506c020758076440304145445502405024102e14000075800e6041600c40c10b0001d045045802c100d0b046100d1868054500b04003040005260744075030190a14145c3e400c0c84c100900d4880651490081d20182da50340b0480d0701d020342c5500e43c5101707480380b00d03004960351000c0c514104c0b030a12003815140184c0160035072900b001c40c40070140070803800741640c48401c850f80c04e1b00c1c600e84081001541c540701402d10740181c1200c2c00180811440c045070220040d00141215158400c43e681155500d4080807000761a00411 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 604280440 1250 604279190 604279243
    0xa170106060c120e0f040608011d032d090405070c02040b0d0201091509120305030136020d09050138152107030507110c0d12120e 57
    0xc1210b0103245501c510100110040340c42d040380c3c035460190b10180d00c12802810359015580d03900c600c00080c000400041400100c800c41e5144183c0f400010b50f0b02034208002008101a2048030703112038148034207180c0113102e40c1e0700328946e00380201480385410514080038018002d4020180e192281d1007100c05000d2840c00d6018400010082c04000b0f000c196943d40a0108100440ca904808000c41c9444007005590388082c5030020b0700c1c40815004038100100610400300b5040f0600e1121a81c4804220103503011140c003940581c0e4071800054142e4081850150560b1980282142540040090000107101090b40e06000c041d010b13412003407042465040f03501c00b440855603002083c0100140303180594803462203c50340c8040000070a88002c00c1447d1001e0802d82c46403805a5507560313002551380780000d400b900325041070418004642c0300d1030080c0341036600e4102c03003c081c6503c400c00c01d5000c0480c90080d01c016080560a194a07410040c1c42005480000b0f52180c42048200c05403103c030140 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 604281690 1250 604280440 604280447
    0x2d0d02010f0c020a0c0308090112020304060c0216060903030507060617010b1e0a090207022227050a0f080d1d061e0112031b050c030606030c180c090a17010606 70
    0x40c42c0107105c2810300200304042405d20002c0c01d00360313030181000108040105e2548007240d00c00c0303074211440c55652100644c103a50410000700c0002d01e05250011381414200c0150600780180f20050803c4000210981000702070781082d4000c20310000580c3c001403c00100f90b01070585448528090036001c604848003804051240100900141240104908005061020f9400740b40c05a0700050454203407080e200640d02c1d40c5240200da03290006580c0da602030742400302d0840e007800140e0341410b1484040030400c0810034180701a8045030030605080e0901d40900c1a001d15805e5031003080c5000600d030b892074004520542c040b0007400c2994400d940314440c0d00c10b001002c3c003070300300345030601740c0180030304001d26280455840c02420442c2880c0400c010a031108070340320301e0403a169000340081c003007941030800c0b01c650071200890103404446418008203044114541c0412401042800030070700c110001c40443d070340104003600c0f418085895480c0e1105a544403d070007003030382d845d0410004a4610 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 604282940 1250 604281690 604281703
    0x602010e0d02011512060e030a120b06090105040902070c0e090a032c1002071e05040b1e01121e0615020111093028052d0d02010f0c02 59
    0x540c090845051418054141005e50010000316842d44d629114019036050070400381400f0081035a41a901401035100e001c1918076030440039000c0c1206004045503680c0042c03e40b01030f1420b0800040c3c44040c0e0b4101100241480e500025001c1c0d108000d0002103d00481c0c40940f141c020344804242c80c01030010180c929090280c6800c030542480762069003803a00310094112801184100e8032030b99140c150a180ea600d684040220080011500b04104d06040c05100303008582116130660000011042d400310030080c244843c104a040c9203800145940390313010f05c0c03620602280702c98201f007010300b02d0002014903005054940b00c02816008829105010381580001900310442c2000c0e201c605101e4032890382a069011410340426a078588807a2021945010540d14010000c0010900a40d0920f25101e10b0503010051b0240454010030400a130851401c91160603004089480910082c07041c042c1220100560003091600c100c03841c0d054000101c01c1c40e03114000c00a85620200c02c0e6940e16 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 604284190 1250 604282940 604282961
    0x180b0c241503160906060f05030f0f0606070c1706091b1e04051003060515061206030f0f010209011b0f03080c0d0e0102070b0705070c0b0c01150602010e0d0201 70
    0x8002000107101c00c10034040c01000d654025080f210181c1031420342101040854001100865071280e0802c0415400b900c4845000214207103c1d1a501b890110320000b014000d18001021140c140455019291f60088804840d00461809070300c0707859508440b10021440d4800c94584107400205a58102c0490079000c0000b000302d400724210101424004d04150312080140301a90001c0d2030810703902c86004061048020b481c1e0f2030b005c03034150300e0034208480018081685a45860000d100380d51200e808880c088982c56402000a0752981c2c006894001d100c0050304d410300445074281240d0310150098406018241c1b190709004240300b038101c40c6155040000b400c002108240c83c00841d0180070019000701d6050aa50710f003d01c0b10f8110340685a42c007030500307171581d0300080740001d00040407542d0760014030b149485864401075480d001003e2001d400341e01070403040011842e031a10401d40c4844400b40134404070402995440350040e00810505048103e81d005100b20389424030302c1031140c0071011 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 604285440 1250 604284190 604284253
    0x1b061b030108150603070e0c0d0e0106050303070204090f17040e07031803030e1501060c0302071205070b0f0418060e060108070f11150411120309090c070201180b0c 72
    0xf0700d06070b0a25103003450151403076405000b21400800c0c2c265810080074811561464080e5646100808240442389520003044960b49081c40620441da808001c441c0402d4045078085142e1071281409041156807070340080c03603c01a1152408281d0149002d031086891200d14585540e035140010707016241c4a00708550718170501100c0400084c000c0e84206092001c1e90216080d02806001c6d121040100781c010202040a201d08903040640c10000744016044607001071030303016030707940d9855542d8065000e0a0811135021804074030400403001034900900308a1202c0841203c0c01d0359220003417086003d11401c041c0310304000354003940901a0240140040d61703e58142840c0d500c02101c00e01c02c2100000f0550260500188204540348940380c0101d0160480031920b42c580020407200c04440c2c0e031016869041406551141e41c2e81e42c041540c0044d40410150385e030201c510040394145000074000000340d1030104081484c01180014084c2c84582e0360031584864142004010000c48244140c1e200b03 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 604286690 1250 604285440 604285453
    0x1006060e0a12080a030207050102090d0b190603080301121502030106030c030e010c120b0a1e0503070501090b030c0f09100804120e030307020f0411031e060402040b0307030c051b061b030108 83
    0x505105c2e40c0241641c43c01040014100300700a00041c02694111006075025820f0106203c06484001d042400400b034101e802c02034140346984421913800305115000305410300400c40c0050215042154002c86140c100440d41d03980c595001070020001d01076480b000a103401c0d0041c40704201442040d5408000b500c80e280601240d0503800050304003804107641040c80e590000880309080c0c00e1042521084180118900d81048103062414156030301c05410801e1603581000341c00d0511003120740090700c40e50070f20b03134500b9914810728251080b02074507504178004008007980c459210100500482c490343c0c240d24003074403118085400c0d10303072000d425601d900104423007030061420303080c1d190b01c500c0003400c041010b50250f404450305800403107540d54060710304c010040780104170603a0b45a00140840c2e0841c00c05092580261090200a012030149070707444020380c2d101801003003500e28004482c2c00d0b407444d084612040070b8036003505407040c0301155246407020140710300d0502903e041c3d55044e0b008107007 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 604287940 1250 604286690 604286707
    0xd14010609261c030f14061903020105030a0b010306050a030605040507080f120c0c0a0e090606100c1410110a021e0a03261e1510111006060e0a1208 65
    0x3c64a00071210101490355400c80c0d40d00b14186130040783e8140f612603041c03464030b01d40f1400f405212068809034135401c0d03500d0350701400182c0e0420207030b98121000300400200d009803030780160b008004c030750019944040b0782d1030000204405504001c0c0704520900640b0b0303c0035900c0c2032840d0b0310b580440344c440d0603410040940e44004084006003c448544c1011100181d82c0100455030806a5400000740425444100a03100d03108010b103a41054042d00d44800511030141c004181030b10310140101070180302d10342c04110003030030080304402011060042207802e1042400815035805501d0a00250003400412000214400b280b41400007101000c1c0c42d1003803a03560304580a036108540300824242d90507a40c90b003d022035034514824040d40751460b00c80a4401465096100024501c9a0103141034101d85406d8807242c0f000c040d00302c01401e01c03030b02c124004500c0905224504c0704022045180000010f03034268084583d044003841990015405912880340e9015844503c02c0500001b80c10800001c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 604289190 1250 604287940 604287973
    0x925080702060c0a09090e010c17100905070324090b030c06040306051b0c012c0d050c0a0503070b0f01240509010504050303181905010c080d1401060926 67
    0x1620011445d05254441c0c0310741c02e00003182c214a20118141c0c1d954240240096082181d580c2090f0703264003014041d18040c207509c0301c420a28000d6a10301510383c0041002c0e00d0194101c1030f074140d0701c4034a1203000d00c0c40500d004c41c4000d0610801603102d040442d011080d007004902a0a844e0707001d0855458a03007180c45580180001501c00c03040c1c020110510b0003086107403405031018809403000828040c080121181445202100803010401603004050f00f001002a19000d00b903082d090a07030712000c4140c041410020000006041404000b45a03803c10509036040d500c50514502da80e020f1340d8980c048022035940c01c403410319044804840c000d035110300a0015060751441403402e140340a4890700400d045800043c028104071010f032966a1075450621100e5202109075902c0b100c240d4a441c00083c0414555040900aa02c001400c00380080d0700f90030200340c200d400001c100c3c45503941d000080c0203100e140300d100c60080000d00c2a92000c14014400791018071504014075502c50f074482d210 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 604290440 1250 604289190 604289197
    0xc0633030a0b09071a0c07050f01021515040908030f0109051003110d170c0c040c0c081606060608090c01030b0a151e051b0703081e090925080702060c 66
    0xc80f4030f4403c640001564a107a10f80411414115104543c1c44004035490346d49000b80c641c000c00d10880307501f1082e05550340d0004500d084070648507a074501c203448184800c40f1403ca4469942c7e00316091400300d1040c0301c0218000c2d4002d841c00c580000c1d0340c0e80e031203407030504559041e00c03403000c0811010810808100f104d00c8507034a1440007403c00304d14401655800d401c070a40083e0300307020031202041e076040111013400401140d601c2550180f26120096100514406c00c0c044c2c007c0c01400c0100d1010819500000380980d0a0380c400300820850ba1141c0d00134010f0002240c08814502c00c65004000d83e5100340540c0700d8000d80036010204650030329003034100d04200c088204007000004048491641e008492400c020b5041e82c0382d003541e594420b103181e41000c082038280445688404c00401c00100b910044584d491141882c05a4074110701a800d0a60701c2003542082d07100324007500b4440a10500d40c4040c1180e159540180403409003030340280c038015400c44905c07002d83c0202c00001d903144400c0b00103 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 604291690 1250 604290440 604290451
    0xe13020405060d0507110d0906050d020c07031b1d06040906090507030b01050f041a010e030f06281b1101020706050907151d060f0c0633030a0b 63
    0x5400c1680351008076190b9003000025000c16030301c0c1d80611213025044200d03a0700002c2c101003d850a60250b48000e00048039900c5003c007000400603a0300c401c4078003603040c0c41d00140c0c144140d40c8201d9507814100c1c641e00711001821243e4501c48400034032407003104070b50208180c6003e10242d00e965004c04002c01406020400e5481c4c039101c0320700c880054024020030015501c1050035070001d505007000d0150540c0c1107841640901d00d08234021a0f070520402d45007082c40000d02e0302c1c0360f04240000109013880e801c0c40e00035110744110780511400880360700381c080b02c6000421807191100070542e405426280d025900f400803106403000c80715200e01ca11526112642d070700001515104c1d0307580d1211308030b801c00c41d00400702e0341040005000d034500d41d0034200b0750154a850314440d031900701d00207290085030101205224000014100312402001800d560248203088141c42c102e00c0d04052500811900714868011414207808042c00c5c00127803100d401c103240c00540200700c0c100c82941c60848580c4046d02 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 604292940 1250 604291690 604291729
    0x70c080703050d0540120207080d02010e16140907031803081603140705070c0e010909020f0303042306040f0303170108010b0f06070c0f0609030201021c0e 68
    0x1108151201e1800358600803117a243c9103092124942584058040d070407548402c0006004010b0704a0089013041e007680c25030880d00f400400601c070300003a444d001050303002d000580201d003c003004070740d0107501600b0241c007454250340c04143c4510103c12440035034001d00600b141c2d03103010715490b410f00c6108140e0103002414009550780144940400b10114a00118006270b9203404100c01741c03d81801c0e00074000f105050600c1074000300441d540b00030030003d05410030410007150140500000c02c18a400404640c00c1c1a035044d616110303100050300e07400909030b008548040c0300c0d40480c1400404c43d0104c501202c10f400030314541d1884907000001840003160300c9036040c071002c1025010080280c005501c45d880d100111480d110041c821001d05a010b0b0045901d480e2505a564844002c10b980f4400c044420940c0c0c0c1d0014500841d074060740350000c0074160164000424150340290144040c0d9000340c00b22280b0901622146040400f802c40e4440000c00c1c01d2031411803801e0008445405200d80c82 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 604294190 1250 604292940 604292947
    0xc06030a0e160f0303090f0e071124040506070f050a030b0a09050906010e0c0703020a0b04020d0b01031b0e010f09020f0f0307030b0a06111513140703030201060608070c08070305 78
    0x4140801c854000d40000c2c4140c3c2c00380c00c0404c20140c0100003034008040c0b400d00c04444502d42042c801354544001c00550030b2207840102c6e032001103418010004000740c0519454595141c04070791240341b42084408843c184920000300b0f80d05401007400d05251078043d5225460154001c0c0101c1c050040600c4443c1c000403410701c04120100940a15032086d000c910040045d5890014040a800400b42890744a030000b00142c6003c01d034046090342c00543c1150a60305552224804100d03441c00d005030150080700c0e604004000c101011004580c500040340c54001260340b0783c41003080b800d200384190800c413070a1030410000042035402400e01c43d2080c11882d401c2141c19550042d040d4411120040000d41d92141302e07429140c080d00000191140c0d2401d07a00b90f64804407481e0340d414042482c0e000060b0080c0005002d94600c1607045c0029902041c41d201c1040103040b0690340e11801c0c00b045002d54208600400c40504c500c2105108d80d0300c90780c60030160b82a0f41c40701c2809078040c11081d0100001003 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 604295440 1250 604294190 604294213
    0x3021201090b062101060b0904151805070905040c091401020d020604021c140a0201021009030503070e0f1c060e16350a26040902090a0e0c0a020705030c06030a0e 71
    0xe20680c0000d00030114081d41d281030560030000ac880790380c040200000f0500d2400d102c600408941d07043c00044480001540e92a03050040e1585082d030361103294000d02f010312101d1070980c041100f00c12500340310000c203082c0b100340c00160f0b02c690244140300b0050f80203c0001f4054a400d00c0300720f2801c024400c2100c10004141ca4210b0220a1049a030404d948152002c42c21960b0400045c4070006480000300500602036400401e18400036041800304015060780054a964200300d40c903400c200100b42104600010010001010ba401410342e0810f00d04010b5107101e2b0004100c81400201c400803c80740e441c1882c41c000382401c9007c401c6541031900c000707040c01000740c00407402c0b1901c00d190000d2148012a00d415101d17402160681e00010080200625031440c4600540d800d8801520000d6207800b40781c40420068440ca44c480e08800c0881c07400c0c0640e15245a0060079080030030750a80e424140c039001415070301d40e02a400540c00c8003041000440c40004c680c40308507074078074030701c184c3c0e0380749645 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 604296690 1250 604295440 604295443
    0xd1d120f09060a0908070e160c02010306080303010f0f0b040501141b06010e0103060515030d030c0201020f070308100b09060306041a090910061403030703030e1f050103021201090b0621 81
    0x50351581c3e010810080003030011000030407080c0000d044588801110f46046103004014040210700e00c03040c045c0c440c40190071a8043e4100070060808801103c1e103d48e95141012010829840380c001c02d11105240802c9400d00502201c00381c42c41a101d80c40c042c100c1c07015406841e480076041000304280f800d0342e18191401800307403c3c000c1c8400f821102555065052003000ca440c041d10075100100f5190b41c40b03840384c4011503c94a540a0790400103161003801000780c1c064811460702a5005400141100405400c04211800703000c03058030640780252103642c0451648a0356000640c01101407001908a250907003087c01c01092120303081c070010000c0404a440c8000c141c0741c0711990740080380720003403941451156000500c40760303031440f40002c80c03540401c3e224840c0c03e03006020540c9409034040348800800507003603080703c0e0707010009442d00c0740002000280000e0200b2840b0342c0720f001c1d81d1500e10405010b5001d00d10382203810708000c1d4441804121411100500066401e4203405400418031030 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 604297940 1250 604296690 604296697
    0x111302030a06170f0705010e1810080c0d030c020607060b0907020a060c0912061d03190f080f18010f0e03031b0705070e130c0b0d1d120f0906 62
    0x81c000c01040b0203080552240781c10042e403550307403416800b03001003203035040000494801710381084c244400c1078038161000c903103502100031804203c501c8030300500019401c0c4482c850f0803520194181c50354070322117204018040001c09006070002d410000031001614080c1d000380902d5126510000341c0c3c1211f54045107202c2d0088402d0400b60b00404240c1041c0700d114050f140e15045d451525000381030030300b0100c0280350300d8280c0151141e07a443c0514003140c2018448010404000c104481c1c070b4100d50ba00302c05400c11103504020001e248a00210b072518060702c1c14500480c11907000e010955142181d855416844c101c103075900f0b41d2a0300f00440c0001e12441442403450546015540c0c9180040b400741d500b42d46441020880d0900708000f8000c200c01080c08000e0300d200e44000d0720141c031400c50414071454580303800341200c1d900b0240080c0121a0400904070280000c00610460524001040140043d500c584500b50804854000c100c2519001488885640b10b1000e0425100c0000b00d5211741 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 604299190 1250 604297940 604297951
    0xc01022406190816140d0803060d0f0c06020d02010b0d1515060507110a06080624030703050f06030106030c0909030909020c0304060206010e25051e2a0303010311130203 74
    0x400c204c200c00300111140704040d011380604c2d4040c01c0b1150260000c180029280c12001e4031621000c80465040d41e90b0038041340200e5045280524149410701b070411241c00c00d846020051700c510900580d20b00e0060040c0c07100010000c0941c0e001c4d15403a108d1001e0a440c11041b690744654030380c150300180c450703014080041c0c401d6544580e00c2d009a4a000200340d408680403d2050944210400040b07a0081c1071591220050b2850b210a40d074840c82c140c070402101c044541d0034280401003006050b0b150f441a4403800040c154080c8580300d0b0028182202c4c00784c0000703040341030305d0101804085055000b80700650310030325000d42d1040c0d03134a1544c022030b00088041c0d0ba0036080005c081001039810000701d4003520100c1080c032460700b41000402c01c038500c80904001c600111410315442139024409030b400000403920b4011040c503c0b2440c41c599079101d14421749204400088a641004940041d0304190340302d0300082d442e5034299110818508221102954400c1015400da040440030303002031802003 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 604300440 1250 604299190 604299193
    0x1a09060d05060a0203010602010608031c02070f0b16080f15121f150506131503060902031602061609090b0a0503031b2a040b130903020f0c010224061908 67
    0x21b5050650090a42d4110780c000041c0e40e02c144071038601c0106980c0d2816810740500c2c00165550554900303084050b1340c9030f4001d0308448030b0308100704103150307018003604114540e07a0f03d080d400d44e06c00c00280d80202083e10480a02c81e0142c2202d01d80d800e0000450703003c075044c0d008841c0410501e84101c042c1116100c1401c0c3d03643c0c4c80c2c400d111101170020307200c8030207010215640c0c0e08000451600144031042803180ca10006a204034400b0490700a0b80202c001d8a11040c0a40d62480d0102150003201c007800325510040c4550030001c3d240604035000d01d941c1600030717650040558074084071440a4913410540590202c81050000391980c0c0c1000203105243e0194005a505140500000c0c100540805004590480d05101c110303010788070140131071140011900050201c0000d80414101680b2040e407400140c50055040e050640020b404002d00c0012800c89a9002e10b0318012611a015030600c3da500301000344100c0e03070030030404048550000028045c40e00c5000303400f0450b404404035502c0355015 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 604301690 1250 604300440 604300447
    0x61f090503060c03010b0706020f040302042f040602030a0305100e040f03020c1c080705120c0307060501050402090906011110050c0309010c0c0b0105060702010309150e0f011a09060d05060a02 84
    0x2420180200c0f50302c0300064400034107540c075040c101102c81c45411001407070140c0c0041c00c80c40400ea0202918040d54014008021612801c4111000c161400450b000180c0b00100b0700c540510502003200d044d00c01c241d0240d81048145a010f602400d030103007a00a0380b203c40c41c4003185000c070724194903100d83d00990b20f00650803000d00b40682030070350707901e590340c000c101c0f11a1403812100407102c81c031409640f094030b8a9554a807818000d0030129800910186201c0000b550031841000202500d1141d000e0002008245d9a4500f000103d1040e81d80b0705401c003110f03c0000d00ca942c001d405200c804130362501a541390301e440e94040802c44404a07001e0340e4443c804411301604c2c400900c0b900f200c076030507030030300d0a1112030585449182c944c0500c1198401c010000340c1c801164842c4c0c1000703240d668014050b690111310700202d107002e001c011800c1d905600c00da01c0d88174600307041406101c144001c10708141840303000c03200500070842c000802d41500140b2441ca8000015000c0240520562954000589 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 604302940 1250 604301690 604301699
    0x5040501140a050c0a1115040501060609060302130e101203170705091f030e1c17130305032d01031403310506070f06050a0203041a061f09 61
    0x1801c000c09440c07029507900c1c3c03070100610112000c044032184216400c0070102003000d94065450640c0070004c0118800c0420b007400100101508024240c80498a5810016494050480481c0105c000300301c26283d4070340c0c6c00c004080f410700445410101d5074103c6505540c81e0b40890b81100d608442c00c80000d0000d06270580c20301950f21261342c2202c00361400c241381c0350300b42b000504400c40324600d003600346141c032018140c62b038040d5000114041d10307941a40c51480742d42c0c1c41c041d0341340c0a10042e9800720f0011034510881155111401d4030401c560307c00b1030014400703510120762a4200401c1142d04c0000304004000b42c0301c403c01c1e080006003c0202c0b0099541c10b620300001d240900040f01c696680c000d0040c0e5140320546130054a44400b801002c00c009001042e007680c107070109178889a000180051100c0038421031000c2030740000e01501d814005500c07000c0500b0304030310048034041c04000c06a0f0201e031031400003440058120a0050860042c00d0b6031481c11821104034480c3d100c0410300302c060400 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 604304190 1250 604302940 604302971
    0xc020307090b0306060f01110f070f050f180a02070606080d170601020307060e0a14030307030501050d031e1106131b030c0509100b2b0608030d09020301060905040501 73
    0xe01508000780103000044496020030f99a040c082d004900c10290400c0280469120300044245c000c9128116003581803059a6251160003d000300c200c0c49940da5000310325401c03d01d07080030501e41e000d04940e00f4400c0551001000e41009081401503940800c50304012880900410002e42905406031800742c4202c18060308100103420800d0208500d5820403400b0307a00030098075026500301001084048a1410071030038005411002044c140000210ba41c844030b001001d180b190780d46403030130071123a6200c0007007002080060800600040790f1045000d060750920304028051800c504ac9890501c214071032050401504480c0d032070540c4403013100c00742440150348101c070058250405401200d4107540711840c28003010b015146c060021580850846940001078800400b4402c0a203515980110720800e6010070070001d44c840c0020700000c140720180c0720300c20070003210540b03802140303031044500802000d0b1540074030582e490b55990340002140501401558070481c458000010351021190105 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 604305440 1250 604304190 604304203
    0x30f021b0c090705041a0403020306070306030219080607050d180506090705060c060106051b0d0f080f071d03010f1103060415030506010302060f040815191116020a03050a030c0203 79
    0x640b150755004280030941e41c022084170180c5656001c283c41c20107041c0141c5c0014801c40e84001c0d058456401085003655244d40010143c0e8402c0f604c15913082c074250103100300c182c41401284800c0e0400c10125020311700034030040220008500012402d0380070074a1207500c3c036910b08000d0310140c01500400400700410310103000902000c445980c105690a4500e507500e41d8140120010f1000c0080c49032120242038030001c60a01c005000c68001580240000b00011040e0b20703d403022416420224020384040706950f8030a400d66079400d200c07030401d03502c0c01c030140400509c420b81555843c1c5d0514000105406492020088000d8003130340ca0500000740011141c40e1078043d0702e11400c1844c280300145d00440c205046940403034030162a12041103c40d80940b00300d5000406910401501c00181c04880d0081407094000300007003030040007035641c550144c400780c1d41a80b00030401000b4001010341140011107503540080c00720b40f145510380c0c1e0744c0c030300d4041d50100980c0802ca14000000451030104043c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 604306690 1250 604305440 604305463
    0xb01020a050c0904110901080c09010611030a140f040f050a080c090c030c040e0a050601030b0402030114210f06101e260102031501021b0d030c03030f021b 68
    0x402249103241c940c50b8a0b8405902a24801d105110200c0c041c40b12410b41501c021000420600442d69189000c9a441d440d04481d00e001e48125000060030a016641903d90030011901651400c070402d5822038604018610007071030305805101c502100c4120402404c0038281da0f0000c201c91a040104001c1c4a59295225041c0d9030701000194206448000e0603075000a20f489503e034403500e40182241035030040d600803c00c8015104100b0241d06056001240912002c4e2402c00100011b81c05007c01d1384824061b080a00400d17201c2c205850420241d501e9070090082005c1031070304180c0054074140144801c5e000c0255004109100c03001c3c0c40c0c180b40341b00501c80f502c103582402c941c2810321809100e00303200740c000198040806450848207a101210000400c0008658900c2c243d04038200c034540c0b1084040c0103100d194020f48441c420980c0082100b840108600c03c1d0b06103564040310018050304013207003010380766010740e80e60601c0c50018060304000344035800e004001c4800d02d5858030403070450 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 604307940 1250 604306690 604306693
    0x13031110020909011203270506071a0f060915011202120711010905060a020a181806050a0e0606070212010e0312070527030c060f0721081306090b040302100b0102 71
    0xc0c02800650480c0700742c00b2032101e00500c400003103e000c2107807c012a80f039020a030009400102002044402500383c0d082d079040b44042d0348a03450f00010f90314202c1d82200c0b02030b081150034000c05d6004107424841800c00710145801c46001c0b60040049003640c102030f01203c41020388105014260703030071010f10270701108110001c219003c1d481c1c07181c6135035413000f801030916154001131654050f03100b19071070428508600c8030182d0540c1d4131f03013114060039041002d034030b03540345005004204c0f844d20003240c01c1280d42036103800460761900130400100e41d20040c8c0c104ea014040c0c2d56102051842809900a0444514040c5d80c41c0c40c500c02100c5048000100b42908101c42007021150425008104007401d8030100c1e925840f01409202082c40e0050311996075134042d502040e00409090441c0c01403e49610a102017040c1c0e1295000c1b0000e0700090784ea030f090100c7d09403400118501c52594014800c04d00404010804121545400704054401d90381600103801680000e00712002c10f02404a441c0028070 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 604309190 1250 604307940 604307969
    0xb0a200a06060b3f060a0504020703020d120c08010302190317040905070c03020a1106040f0e0109060501030605010903060b0d0c0605070308150105121008030307051810081303111002090901 83
    0x4800180782c044582c9000308030599013020502d55100c01d407001d0040c00000c0c000319a40c600e98180070b5030368080400c5036000a032240748010b8020700315000b280c102c14007a4075003852a9085508106815022003030312004030444100c00030214040320000d1450050a400c440da8a40c209a00d21040d00d400400203010b1041e4008542e0009500150008411350441160311808400d5030005209110742c2e4011006200b5810001c56180842c44115040b9541c03010104111560b407070054042d58854807030180801c0340883c1c2000460300e81c0d0480104c1140c018000c0142504d9640c1d040504240ba4100c03070001000030402a0426800c2800c0781c1e00729003141030b24541442003000003801840b50307640290b04c00c2400c50124040d00552280c107009810810252512483c0c00c4000404a4101ea041070b00304101c46407140c0454100883c04070342e05042d03940c0d2218203907a146243c40f420040c401c02141000120641c03619030000a0115490b21540c4080c0569141e8140c010050030300810707001003242202d1070 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 604310440 1250 604309190 604309267
    0x60103060f0504050402010c0203010f0605090f040803060607060f020301030309060806151b0330160c0303020901050903061801142203090b0c030a03060b0a200a06060b 74
    0x407403800c41110b000b20340110702c03a0780da480100d4101031901d1b0b00030340542c02d09062080840c82d0750402d00035503000b9691300ca090340e90110923009020054501508220f82080424101e041c81070041c40039a01446020446030100d079100d000f04d030702c01d90080e000600c0280341482441d40c401d280710b0300460111409140364a85405180591040f040b103d00c4880c083c04107000d080f8003d100340c1d2111400420601000c4003140501d40d40950b6419041c11b21008000001e0030b400d00c10070800340101440d680d6a241c0340c40741d80e0300381c00940c00303500c500741401000c0c004200b00d0b07941007041c01d1050201100310100d1141c10f40c040c41c25a03000e041c2400c00c060042c0104004403480c4419007608011307d0501d03101040c81410305030740c40107564000361006c0c100028008600c1100200610030821143e0382044610f50b18090381d0404e008194440c400510141c5a01c014103a82034041c000001491068403111201541e6050442d9255400b040c01c652010840444807203509030600d0010a140702001c6661841 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 604311690 1250 604310440 604310459
    0x1b1201180b01020c10030902040f0b01020f0304030507140109090e1b0301020a051c060509090c03070e150405180f24070516081215210723150703020606010306 70
    0x400130181d0150491789980781001d44a40c1004000f140c010b01308000b0302e5140304403400504089507045004d482a0343c4102d5480000208940469800c640503100c160305101c01000c601c8016140c0070704000e140ca00204075552a4480c000441d04d182c801007245112072418113410888a01d00c0714400e91043c0300040805412074222003904042110901a180030510000c1c02008142c00443d04006c400b010400840400128212542000c6044449250383c0c0c08080000c1d1800310307403003040c2c54030355549451a03040c140c200c260440e007170305406003c1500480005290981c0c0c0d91452507158041d000c001205802c22306d07040340e07805221a10100324644040003405a102e41d0b0500359522030040311440522003071409a5065400c40e2a00c66501c1c10490100f54040680f84011403043c00202d42002e000d40442e020821a0125900500a0030345060364805040e1481100ca100c2c00032055078041942d940c241d0030030500d4960f003009c20340350f200030f04000b85030440040803a81414079251052000d68070 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 604312940 1250 604311690 604311703
    0x414040308100602100518061f050307061413030524160c030c0317010f0503060f091207111309051002070f022b05061e1006081b1201180b0102 63
    0x144d442e00851b054480004a80c10201503201c10b0f59075000e41410f02204a01c0803c1c00ca5500c0300c400300d00c02e007040d212410180c5483d2103106060105007129480e20741e800102000d130180d841003040b000c01d001d503692103403400c003202c0100c0c402000c40c007071701c1a06560500c0929181c00070082e000c2c0c001ca650341004003400c8900011000340070300c6640c5e84050b080500c41c0c0c074544921044078898201c075507540c42240d1049000780c01030f00d1190094030700060402c1c00c0c1c00340c0d80303128205070740042c8103c101ca280b07101102d91045070b003910004c910100c1d10006848160f4042040801c00200056815403800e000c6d00780840d2501c0d12801d00d00400600011030509261030340001d40450302502030000e55030f4031141c0c48020b40d10540c4991403440815060220102d5141e2080010707070352102900045840c500100d960881d04001c3d80c00d1030303190034404207210314425640191410748070740000d0b01c0380075410352540058944100404291005201c004002c550402d41d0100e0791078140244070400700080e450300c0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 604314190 1250 604312940 604312963
    0x60415032d080a020706091d01051306080609031801021c0f051b0f16050d06020702010201020906070b040c0b0c0a120302090a0314011103060a0b180414040308100602 73
    0xc541400714280c821850036000030580c09000356581d0014100065100c01c1244200c00102d04510030000340e00c0001000045221611203290115070309010400c52906c4404203c441c0d110340d201804114160204880b80c000c00c4110001c40e1101c6040c9840b4541c26280d005590442d04030f003d50754401c130303601024030300c10a481d41050441248100d408403100c2c000c06040121041c1e039020313489200080428012000c94080c2c003914825441c088070008002134901c40c8a0704960034050140114210780c0c040d0403442d10503c005803a0400410020b20300b90040b00d801c0d030306480400144002c02c404605080000c0c0343e0881e0fa14140104001001d458414100300540341d002008d1a03a0b9255121ba03044a160103802020785100d140c49042070030041411095000540d881c0c104085005040c40007078170310030f42000b02001e076050300b0504100110340100c1c00f4080102800b0f00c40701d00a5586000d1050180d07403000361185503141c076040003000d018004c0d25200078421541c009201a540c00b269400411 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 604315440 1250 604314190 604314233
    0x9090703051e03191e1e030f090204150f0806060f01051305060408010903021207020f10030b09190b010305040206030a0c0903080309060f0114030a021c05070b0306041503 75
    0x14051000a801c40c031850b81c1a201c50202100001c81c0241c102d4080c082c124a130603080501e1000050042d0b4920000c80b540031032007a2021000106c091182c2c01004c1c60fa5140c01e00030440000d281d01240a0b25500e060700064806524810f001090000310088014000318000b81701a041120208401031a10b400303840c1040000503031003040700b61100f980c80044c98081c02d941e5544e60f03510001c50081400d11412001405404401d4503081600e80c1603568080d001041000110041401c01c1601c03040342810009250f118194800e1076075803414068071807000c11100d0018030850700d481c00200d44600c07040c98107040c645402e003c09620742e107013603a601c4915003c0004800d03011400c150f07007942060340010712400b400800c1100c8a032001c50314902070085202c856280c1d0341c0f110018100c05920913000ba41541c052a90340c409841c0055010390b0f00c4442c00200144940c2756221941000201e410010032905c00005028050500d4414018605100c04a09807480d0440d0b41d02e8444200c00f00805c01103 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 604316546 1106 604315440 604315483
    0x1e03010b180a06060c05060a052215050105030a030c11060705160311120a11060d0c0807140903030d0207170d051603091a0c0c030c010b0909070305 65
    0x503646c080c0c00b1388401c0c0d4a6800c03000092500801c0c030034245e038011a004815030207a5a102d901a4040c1c4100511808400740d402c0684506130302c25802903004482c0200820391203458000c010340d0060301c1c0102010b1001c00555207014512000e842ca001d0550040010400700340d600c0d00b101d100722407101248110004105c15400d820036850015000b83d03825200140e040f99404c00110401401d0908088040d40d203441182d00305219180459840810300400d1608841c00440c6101042800791030004594040386c1c4034090315a801c004560040b4411041000940040450103180c911813501c898103d20058007812007614110704580440c0c7e07c1443c61441703409040d070001e030403440c0302c641c07011703603000c0101c20b010010400405c01206100c103a0800c031003400106404031181d000841c801640c5001c01c004941c0c064544001944110801c20001e400402d02040c10a41105280707507 = true := by decide +kernel

theorem cover : BRFrame.Cov 604136690 604316546 := by
  have h0 := BRFrame.cov_init 604136690
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604136690 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604136690 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604136690 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604136690 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604136690 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604136690 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604136690 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604136690 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604136690 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604136690 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604136690 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604136690 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604136690 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604136690 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604136690 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604136690 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604136690 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604136690 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604136690 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604136690 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604136690 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604136690 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604136690 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604136690 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604136690 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604136690 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604136690 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604136690 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604136690 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604136690 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604136690 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604136690 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604136690 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604136690 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604136690 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604136690 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604136690 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604136690 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604136690 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604136690 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604136690 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604136690 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604136690 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604136690 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604136690 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604136690 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604136690 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604136690 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604136690 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604136690 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604136690 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604136690 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604136690 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604136690 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604136690 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604136690 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604136690 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604136690 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604136690 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604136690 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604136690 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604136690 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604136690 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604136690 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604136690 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604136690 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604136690 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604136690 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604136690 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604136690 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604136690 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604136690 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604136690 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604136690 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604136690 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604136690 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604136690 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604136690 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604136690 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604136690 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604136690 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604136690 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604136690 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604136690 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604136690 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604136690 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604136690 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604136690 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604136690 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604136690 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604136690 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604136690 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604136690 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604136690 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604136690 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604136690 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604136690 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604136690 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604136690 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604136690 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604136690 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604136690 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604136690 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604136690 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604136690 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604136690 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604136690 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604136690 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604136690 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604136690 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604136690 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604136690 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604136690 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604136690 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604136690 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604136690 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604136690 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604136690 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604136690 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604136690 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604136690 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604136690 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604136690 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604136690 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604136690 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604136690 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604136690 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604136690 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604136690 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604136690 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604136690 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604136690 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604136690 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604136690 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604136690 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604136690 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604136690 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604136690 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604136690 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604136690 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604136690 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604136690 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604136690 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604136690 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 604136690 ≤ n) (h2 : n < 604316546) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
