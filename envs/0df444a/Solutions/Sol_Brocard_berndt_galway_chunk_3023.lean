-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3023
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:26:26.935235+00:00
-- url     : https://prove2.me/submissions/cf6325bf-3021-45fe-881a-ee3764246139

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 543525179 ≤ n < 543705035 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 543526429 1250 543525179 543525187
    0x70314011410051306020a06110a1409041104031109010e07021203100e1003141b090a06030f080a02070b0903031e1e03011404060f090504031202030a090204050609060a0b0f0f03010605 81
    0x10200e043d04c10744008500034403000c020400f41d880d0048039424160010bc0002030301c1c3d000450101d8020103620514040ca141c022078000200040305034407403111001910441841d9990345c80c060390b01e060994180b005a00140402e0184020640c00345034881c00c0b07402e422040d40e83c0c40021140003041580c4040a0090140381070060000195544105080c1e80c401002a13544108119444e000d0702c480180c81a00c0d61400315025828035000301c8061900040740111514140c40c0c0940395030b00518000300036002d68680000c40091102c10384500381c0018000e58038000940c030314001a801c2c6c41c110403224a4060140c1c3e4545000e1090107015444144034450749e0354140300602100030131140d0440d01c07487c10440c0c02c0c40070007010100b013400c4816888010031a0b4440b46819074444070707005190000140f0110400081e441d0581084200c20b000380e4081249407a400148500000e08640700798000341060410000d0200200040008403072100803503040501030618610310358030030b91085001401c00703d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 543527679 1250 543526429 543526433
    0xd0c09050702151003030315170f0c0301050103080405040f060305010c030605041d370c03121107050105070501091b051005130e1e09010203070314011410051306020a 73
    0x2c40402260f2031003814185440c03100345000020500000301059212007250864142002c10400500142d201c90741c2c0303440c08252415070304c04000001c3c40300c034031030300c0403c2c80395080c117200f00d505907500042000d24042c02d00d402e02c0051700c07042a409090b40d80e10480000401c10038401e9078040d285c0c654002c5405850b0070100010f440310051120080c2d0340011038000c1b944800200300c50442c0028113003010900002090a020b10029209595560401c11022040140d1881c0c074000b070f0307485a83c1c0c03002c22810100c000c42d1018001440d40031650b100440600041d8000c0c006465900c0c4070f8000441c500000d50f40c0c440d13100495481c8040041549031003031105c0d01c0c05000010000e051440e00034140441c461341c0801c41d850074420307400800d684401041889200c84a414140300f2034045601c840d04086131030718001c0d4001c44200780024581103580202d0741a484145040f0780c050b500042e904410030040003a48141e401500007405010080c0b20301e85043c1c503040c0002400d664014060340b5000e4 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 543528929 1250 543527679 543527683
    0x10801060501030e100e070305030a08010f06050712052b021206030d02060103020d080903010e060702010c0203070206030f33010f05091011070810020306120c01021002090d0c09050702 81
    0x290440c82c141420700103400d082d218001441070342031102403400714a900e4135040c0300d410300307810b80c201030100d00001070902107158007c440346048030941103a600381150380e400212101e0107141001410055100e100610542c4104007401490710041d409009481d0494080d581350300f0101d01c200303080303038000c181c840450710700c24010742d4010416070142490a815482c002d440d4441400000d2060402c0760400090002150550f0051a400360080051070410340c001c0d96030380d1084403824010b40c01c0658a00b0340510100580340c22603130241801d4210307141c82d071200c502c6100080c4445e15881411901220210417a040101c2c8940c4848500b02402000c0000421088405210405018040004004548501010380e0030702c031082c84c0041100c807000c154a0f05000c43da41c003445070391003818a031a1021701250b008500681d811030310000c0b64040b1540340c076220030301c100c2410b025030466000c20350f98850315001411110700003061190500c0701603403a000d42c24903c3d0002c01e10541d5560412400d9501 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 543530179 1250 543528929 543528941
    0xf03050f1603080d0b130e01050c0a17060f04090803040c05180a180b0a0c111b01050c0a06090602030402011b0203120f1306020604200108010b090d05070608010801 72
    0x1450050920401d00c00e0076400815101c0c40010503080000800510035240c9900003103540c0002444011805000001c5201402d247d820807921540b0341804111080c41601c101e403034190107500d030f42c1c507042810980c42944e014010070440e000b2038003060104a03a682d80c03050050f02441481499200c0c01c00f82005130789a0b18541009025060b500341c4404118041384803d5445a16200041812203c0400031100d107030711240024110b4001505004400300ca942100b61001050f650b801c81c9810090f0620390345410480b03e00c07544a50311440560294818030040000000030350440e91884141c0d91141c0403500303c5442580c1c480d84c04802e002c215a1f000342c10301d00710035000301c1d01982540c50b034001988618559595801c580b02c0095600391088c14801034504408018007100081659510b010b9202c0d031342150101c5040740d09803c400f202c55402100440070f807406070364030020350f03080501c4800294001000c0690110b214458000011401c04c098000f4005554030341500b940750002d41420b483c6 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 543531429 1250 543530179 543530203
    0xa0c08070903030e0607020d150c0314040c05150f0d020a0e03010b0a06050a110f030405040c18031b0b030a0c1b0201080c030a02070b0103080307120c0e090c130f0305 73
    0x40c80210400c00321350300c81d507858290341044a08035654074035032000034803814107c4070050100c001503101c0440080d01c0e60010469181c2038030240148081000115840c00d82140d0050181e4030f0032310203010f00d040c0242c040300d100502c030754560314000c0c140c2e00488850b04812046540c16400080c0c0036201540708180c203d844500fa0000d21021011000180d504502c50084004000300451080c2100c0d100e0b2020104032140b150986901e0520200034940b26400f038007907640a58100018860900d101d43c8143d002e100c1542c08030030007a4155074a04840c05980c2029420403110100080f8211440100075401111003210000742052180340c0545074440380c03c0580002d0207040e04210250b40c110861661100d01c48501c2c82e03a075900e081c0b01e48020b008a0340e001d0494140300001004202c1000b0080d40109202e440f1000380503001c210100030727903c51802c0b00340014411102d0100c01d0501d11212030f000400546a203090401460707140400240b10303440f00d4040840c1da00f080003404001e02004503519 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 543532679 1250 543531429 543531437
    0x1312080703020706090608070807051c0f06050a03020a03080a03110301060e0108010e0c180d24180305160201030905010e160801020c03040501050d02070f08071a0402130207060b090a0c0807 83
    0xd14020020306000c7c0300606d0501030200d5000051100e6214004550a00c829811402000610307002400c0080c040710b07045180052030418081402e142c280c1d0701c00110790780141042405401c50f42d9441382d0b500302640c00070a00d521040341040030004130001e580078100f907035651203030480150001071001e071046e40100e50054142007400880c0c6010000c480040729040b0040d051400319038042200a84c46d140d01034800440c4101b100c828000440041d510001c00400c00d2150084111508900d041c0c0b032600200400c00800c4000c003031401c03104003400ea180c0141000100c0c0d0002d910b07203900f13662008140c141e864105c00426000840748900340400307883c5a9000314100502b007220a80e89200c4c88c0205030600c400400c1c0580c0c049100d4044883c055403102d034200504015150180080d00080030484020100c4000789980e075006050184c842c2e80c00501c4440c504d00c845901c0c1000b5805410180d40701900c0b0801401030b034480e05e1660b8000c0781c0d1a14001006c40c62507100500030720018018200708 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 543533929 1250 543532679 543532697
    0x40218040309120201090509040b010807170703120314010803091201060f0b0721020105061f081803130305060403081f0e191b020d0c0f081312080703020706 69
    0x12aa111942e00240da0484510881160701c03400140e0308680c0350f6010301d901550b800700700001c101264821a04032048038086130440d070b48407400c442440840404004040d804580104007003686944401c03c0e20540b8140068003407401d009448402009810005c01c0358400600c10a450529500c50510703240010000c006942c1400031030300c00c114a030302c03a640c090000481d01c8d00500910f0050f030350324408070301045480c02c0031490020f4082c0c002201c00c2845001c00d080400e00d010540310040b41d0900d9541c0c0c4184d0341340e86440c1d9000c0384000090007984544010701c803814111400843d004091400b4000408503840d1502e0021b02c4600c0042407a299001030040c02d071510402c4088480644040200e05045543c5a401e2030700f54207002c0120585041c2040003000341401d804401c00c45501455080d81c80d1906038407400d03a80c6c0b146071000105208418401c0c40c0c081503506014010080492107a60700140e40c45203504000c0c100741c04240c83c800000228a03041603010000000201541c0c1048154 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 543535179 1250 543533929 543533933
    0xa21020c010c090515090f0f031608010506010e0406030803070f11030c06100503030f0307030b0301140c120106080112030c08040f1d0a050705030f0403020109022d03010504020d150906060e04021804 87
    0x10300c0c0300c25621074041c070030b401c140440994003030252b400d46500000c804402d16903103141d014068003065910601240c1003000c0741e6540d05140c060300c000c0c0e98000040303a2031a11108001c171400646030003000c0c100300d040058203191020a100500c032035200f020041109050a02140d4140342d4903070320032480783e8420040400c0c00c2d0000130940307a2005180c2000113180c0c0c1c0002c04240940007000d4011401c8070b20004110124007804042c10a008985030f02901aa0301c9110680306c0035820302840036003000d80080000000c3c464240c00c00a5481000d18a061135a9003182031074202c003030340180b44c00c502d48540301d907c8550029801a84011300903403e104d5030400d0000500144006000b40b03c900c07828000250505000350042c4160302d138060141d80c00520190030000c0092251100440c1c80b142c40d450b5407009182c140102d0f405107030018614104400940d07103580083c1000528a9112a10784500c40c000c5841032061600030301008000031610b203090b204100410701501d6583c03a201c1882418000 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 543536429 1250 543535179 543535189
    0x5040c0806130609360c05060a03020f030a05012108070b06040902030703050610060e0901171903051c02030f040b1e0a020712050a21020c010c09051509 67
    0x20300440242c1d0854910710a01401d80064245a000001030b0741c03c02001c0819540c00005400c060b082d560940441603a51140060003a050b400018040000d0700f4070034041841d11800501024400f410f00601d820032502c04000c29402c11540d00d00d402d5550700040000818215540300031015400700c005c0144050f644001c8207000303044001d000c00d4100c0700001d4082c2c603590712402c1240d400904650095607a80340142c0c0e10301c002c031054021190715007400500c2c5402031003224566000140004040c2c2e01b400301061142c0450001848544a404030322403217420f40445100b0b08178000e03600c00703568000580d0001e10100a101e00012039600c10000c000e81440d1801809400551080140d446a290b5641000e410000341511068800401c42440050401a4020710381180b0456040404090329401690036009070100c3d02c0100d042c60107091001841600405114010810014141841c1191050860356645114004260b5034001803189207442019141202d008002003403520b04104045a = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 543537679 1250 543536429 543536431
    0x305010e120a0207090b010c050a060606031506020703110f18070807170a091401060f0519033c050d02060a021305011103040e10030605060f0a12020a0302060307090f05040c08 77
    0x50350b486d649117001412603200e202c100d400030707422604031500c0d0615802c28500030105d510401d00402c0c642225450b00e18000405503040359402e0b0080c0622500c0e5440d0140c1803c0600216640204d20003101a101c2da030b0844240803a040074110b14080e45001000900b00c2c1078090038480030712001500394410785141020650b032210092071f010a90b603001c0e28140c000a074078032404a1041d402d001000c203140850141c2d02003100d0048a99000f00300360300300760b004a54214003000d8044e1048021000e0042c4045004000c600c601c52030380c04203400c041e00320340340002c003501c000c403902e4100032030340ca075855410403000303801c0849001d086150031010100e003d14041184183c906210b03001c0408501d01038144256801800c00c1c0a40e444240b80c641c0550380d10100a0008503045803615020a006003084842a508080d020308070300300b41810300c010305030350031202e8200701d81c0244008804001071f25118095402401346031260b03420b15040141440007070440f50003190007245051010230b0072562084101e = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 543538929 1250 543537679 543537689
    0x60c020c1018030c060f0201140c090904050a0803190c090521010219050c060c04030809120a170c010e0a0c0b0a0917100c05090d0b090a0203070305010e120a0207 71
    0x405400d0040b101101c541c1051644094400086410002105a04507074034803d644201c0d802040000c00d08582075401e00c100390781c51181150144485030003818014029074105000e102103d520306016555036070158000c80b622148103030541488605a201c82c01207a260007958100003013542c0c1010080354000c20303400c001c00c0840002c01c030080102c0e08c0c21760488186016004144207040010b080c094003541c0720907400d5905208541c0002e2520900c40241c40a8a91112420785440044010020400107e40340741c44d2501859100400003040c00c05030703008040540b4031054035002c0d1b0010b03480c215224061159102d80010001500156140300a00251000600c0c44c64440e084000704490441071904030300e2220103404680507c80e43c00044100f4182c105031006d06c2440c081c1041220180161951580c0041400d02200c00041005c0c0705180e100c03141200b241c50b1100150000380c5054050791095403141d664802d00b1300141d00038070825000412a1208510300840090001e50b11101d03407080c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 543540179 1250 543538929 543538937
    0x91106030a0f05010b13060906020c15041805040507050d0512030a0603050723010c1e05120d020417010507050a2d02010c020f010b010e0d02130203090a060c020c10 72
    0x2560011003507006990007105038208000568440c004121035500a03d5025080403041b000060f10030700c16409141900c1d4250301505489a5210510554103000e140000840342d0501000c50030440ca605100102460400040395500301820728030f040c1582c0c0d4102501601c6548602c0c40418000a415080000030170801d43c3c0d2a030303c00c0c403611b00030725258100034440e014003103000445025820105000e00071400c410003550305500e00641b003040605c84000c1c4001c003209250040d48009030002c0e00e01078094011f070b809115041c001d107041c03907000c070034002c010990200f02800700c0090800d44420100551000300840d0520380700c0a007050240c0034080040000c0003a42c1004402c0701900100010b2421148103052088001c001e80a0295480b0031801886110080090410140a04c1040c100181c691105010b844024004c40903a4558203030f17044102e1701041e8121840c24401144115841800761a0004052034105c060380c44904200c0215072109442040544d03c224144050605030b0074 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 543541429 1250 543540179 543540181
    0x20d02031215090403110c01030b010f110f1903080a050c091e0402070b09010e0606010f030e190b19050c0f0c0c041b0e0d080d0b12060901091509110603 67
    0x2d0110410740b500300585412580950030b110415421038180c01c00c0403040000da981c80d2422000440c2150b011000c49800901d022411140244c02000082d103a0306044040d5103082d5000b0722031502e8010458214410b400900c000d01c810b15911040740390300b100074007505100c4d034204907a10000b035008181d5070511440c95001960b204212030303555581c1c20180a8020764071880c850908640a6108035403075801d95081c1446a200c041c0045902c1d40320320300503140e205040310040421801805030403100d070420710490104403000042900c60068203803003400e0001007464211a900e419521120402d205207084c070302404201c412800070740340142100b0900d41d0b107840c2c1c5c071410285071100169085411a01d4682c81c0c0c0e68002601403107102c4440c0d552203096014003e00309200e81d2040100c00070f012b0380c0c000c9c040348039100e00035080896000001441a400041d00c602d400e8180002510502c065a5603480c2500400000a580078940042540100901001381e10f40c0440c403e124099240300d0b410000c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 543542679 1250 543541429 543541441
    0xe0a060e1b0f0d0c080a1a01120c02070f03142b05031302091504110a020c100207050a0807080d0509090f10090c020a050f031303080703140c0c01030c020d020312 71
    0x2030583e881200d04281c00e20041030b141c0405054101e003610308490b11818140000c0c8944506071814840b81d0307040c2e4070201180039210280004003d40c1ea03035542180940d1400050424a00800c07030042c50042c070028080c0d0790140100d0340382c460741c070508050024084204080345d0003000c10811001c140c0e41001950307076481100c80c840c1403020380c074006d6203c00c1d6001400200c901c041c010a0b60300005440c108080b15040c4c01c980c1c164040d581e501c07801603118101012903406c3c4401344550025550045594140c2c80d113000507410500780d0400207041c1d1000714201720004042110403a840c1c094200746107402d0070340020840601c0010180703e4060344002c080746042c1c04180c0d81070004e01000d00200210050303a60000d4a400038904c01783d8140c416410100241800071084070031000241c9044c041e0740307155640300d4a05800c11442641848241d50024000ca90903000030401c210056000d09200858980050300720356026064004550040b510000700035000422a005e900749108401030568444c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 543543929 1250 543542679 543542707
    0x2d030609160e04330507050f0d180204050f09010515010804060513050712020f040605030703030804060207021309120c03050a0309051204060207051201020c0304050d1a010e0a060e1b 80
    0x213103e1140385100220130a40808244400c00d1040f02c01c03250041c002c40e00c9542040307643d401001c601810100c3c0070051004c103540c0030350000040050003080342d030400700c40f07400290031140202c1e21401010005d808100d50322000f8420180d000100583c5038100b80c403401c1c0000c20300200100000c101e00e5582000c07900141e0400902030f006d0790b200c01250320058654160340b803c2424040102c0c010617078010b40c403009280c40e019034400c1e54009070040241c00e2840c8c504440303e1002400a40d142642001807002585400004405040d5a480c000ca10b0054500d00501800c0c2201048400c002080504000003a44072044030b01c01d0420340741c040703008022408d2090601c8400b0003456140040080d002480b95004920141120021680e41b00d58802c0c0c2000d540c01d0740305888841145800c204000c1c82030303180c80c0d00b114580c5070161070841100c9912881c00b20400200781c0041956000c0701042001070202402188003810404800e00e446060035050100108041d041c024030090b030116100c0c480c0010 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 543545179 1250 543543929 543543953
    0x209040519050f0c040e030f0717040306060509060102010507021e100615090803041d100806070207050405090a030e060c0f100605011b0305182d030609160e04 70
    0x1d2a48061200c2480e01e010343d41c8500d0050004840d00407041c04e4000380c0342920800b6020244100613505d044514480c450071503103d040206d400b60301c0035640303181d603a6005c1c000d04083d5105650014804c2c0c10803080016008005240700e04581c144001c02c2801540403030f010002c40d80c3d034000c400040c6a40300c00f0b01c0c2450721303003840a42c10902e0700200154503082640c000340360220981381d03024a10b483e0b030320b041d07120700c114003507598035408010185200f030305810030140c0d000d4104e640784d6810701c0c1c43c3d21515060600030350756140181d01c1600c09000750714080c40340c030360480c0d83c04004040b031402030780d0040c12802400709081c1c414400402c1caa003070044c00307024403081b020214050b1000e06c4001221140244043d0080b2400590000e2951100c40d1601c0c2529510076015241d6a051021000740300c48a8580600801c5d04200c0c1c0041c1400c20b404078020190079000780990000425420300c0c181880e0020080916210f43e104123078541c00701e0081491042652186000c0710304943c0e0740d007416074079406 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 543546429 1250 543545179 543545203
    0x40b1c1118041e0207060b090906010e0601210509010b0604080c370602150f0a0b12070815091b010f0903120801091a0618040b06070318060302041202090405 69
    0x110841144401110350017024684d1088004200b00c5604000340700042004a0341d800039603001e45d0050010981306180c00d54494814504021091052100c44400680c0085a01c05a5444000703102044000b030055101e104000d40d1550300305464910010395030702e502600306000302d510002e080080096240d90084031803407000c9841c0c10620521040b014030040d481505d0050162001c02041d40e02944000d03030051511050134a49a01c8130001640240321241c079095110703c240300180310690307041c0980320040041c0c0001d8000c2d1000c45800400e030100060050f8595041030409010580380c4034480c0f010f03042c0031300e060240d01d4a074500c19a950301084d00023400d40780c07000c0059900150300c500310030b059440300001070191840540c4003880a086008400ea40301e00e0500200d4080c1c80c030300030080714808004201082200c6080d01180c0700c0d902c01c0c0400d8001400607140f003400410080c1c00c603001072045145c1185840d2510190a6246a0500c0000d10441800c0d011500b440f0040101c107031085 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 543547679 1250 543546429 543546461
    0xa03020403020d05060402031203070e0f03031306050301051e0d030e2107060e0609031b033c1f0216140f010b0d080d050405070803040b1c111804 64
    0x24502d01300707203994003411a4202c0c442d01c646445540402252020350b8019280307502e404140c0a69402000b1515141e05102d0790144000d000003018141c2180101c4010700341901e603142d8035414030052006040074018001440c0d0010803a184003500d400c904003140c2034043c58030aa00b0104003002031242e0f0708503130342c3c42552207000c140d0205a4501154440440302d03c0d03120a450b400040050180390f0040b4542c4682c19080361a02d040c40e09000d400f006180640203003680c0c2070301444004003440502003803c1c01c00468442944404801c107030180b44000200610062602c0404002d400188500e80010419026000300d08180e406017540c0000031501e900811a10f9102a000080380d6140074580a007032081d82408152aa0303414000701c0324511a400030212031500650000c00d1000d8040500101c44034410500d0008a104091011b8405480926121691040c0300700c04601501416000c01000c50b240600c611185d01a803000c54146030a80750409800c098240009002094a039142484007 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 543548929 1250 543547679 543547699
    0x302100201020d0501050405060d02041d01240b03010f15050910020a06050f2703090d14120306101d1302040306052412160e19200a0302040302 63
    0x5901034002c0c2202c00603c07a410800783e80d803003040105407842543d03229049a80d401000f07000d410b1130b03000074001d0801d0203a5070403003940c0e400782d05007100d10300c200c00ba00702c62400011021048407489004010820081e00301d0035541080c0d404211039070b02c2d100d015003400c0340b00c29540000d40207005841c0c039050001d0091a0405a10202a464114207241200d400f4900340c0050b807043c49130b142d41402020f114512001850114014520603400d0703140111041c4401e000040007581d5145002d50300b01d00c564802403120605c80022441d001d60b0a581c90345000080c810455035483d031442e03000c0e5401c950315280403d4403151400d000740c40100480da9401c44030303140040820782d001d50014022288a0b2a08003c1e40d035516200203010b164078070650048680c000e02c4509646030040c04c18804026401c10b0b6049410344040e00b01400c51240d02000b2924049800c00120034504e01c01041c000c0c129000c103028441c07940a100102049042900171800d03800f06142c2c003c0d920950541d009141c1c0078008030301c8 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 543550179 1250 543548929 543548959
    0x504060212100803190309022707020705031c0c0501060b040f05031b190f03030e04060e060312030912030c120105010c15020d0207051c1d06040312090302 68
    0x3039441040c08070781c00c00d4000d002c9840050200c00000455805401450410165400208003882400d01e00c01c00c05d5110000080076039038002e81c0310104010610380c0d40d811070048150714114000200105d056402a0404010f00c6c0c4001c5101d03c2003540c9041890442e012642e03060302c0c1e009000d48040c3c259072034080c0114000901c3d40041040d107010044000d01d80c0d81d5002015551840022009d80208540d03c01071481d05106000c020140c0318155038203803d5031030b04281091030009a1080d80040c9080303500f1180e5003014490034014082200590015140c00f8006c01d560303d4008a111030060b030b00200240b0b10034410702060100482405045176207080007990741c1525082134141c0c9072608960400054550300400078200c905078803401c041070030461000008002e4100241e10307081c07160200001d40028200b804404003050010741103100c07108005400070305a00e40000c0c242c0046842d003c2442859503404143d80499921606550a0b42c91001003103c8034952540002c0d004408807941c00700c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 543551429 1250 543550179 543550181
    0x405010c0206010803181905060711090c07081902030d090507090e0616180b04030b0411030102040b1b010e07060503040317072a0219240e1012050406 66
    0x408a280c0d0308035005030f43c81d404000c1c0c981c8541002c290100980c0606c508060805014201034150550418800325076030b8000f103102d5a202200c1156a068242200726003480e1548034030f50461503155503241001d51550361440188034610344a034140d028041c070444214800c204995000764031b16001e1010701d4a0f491720b03030b50b00c5446000b0410181d0810041c080306450015080b446103001c40c0c0940e40e40d1030060003d03150140c110140500c11074496901054101d01003004000951280b58840391a00d00350030040004440200e00920907401000200503412105090300c80d0210211481d0800e8600600c000780108181440b406403070042080000302550028082c0d84100d0203529000c1821010100b403180c240c400321402c0000c50b24249480c8001c103144000d042c100513111480d4201d402480d00083c140449514508442d212206030600403511000712609540403448a00006100200005060580c00d203100314003800c0882c4125100f684506003420429424440811140c01c0c00e0030064 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 543552679 1250 543551429 543551441
    0xc05040204060314061f0f020f0105070f1106040206040611010605030601060216080c10030c0314040c08100506090103060c050717090907050c0717010b03100b040c180b21040501 78
    0x1015600380741e00000c455082556907a0600c0c00d0f0400c21400143c150107090ba4401e62030340402c3d04512480d000542d85209c00d2103950700912881c1c461a054484400000f04095089003c4e2010390708503c090000684441040e01c080c0c403103608214400c8518a166103004014660006900d4450100001161900850b0902e040303a54140852096510b0f66038481c0c1d2107100c2e0500580201090080c07280882c4a584518040b00c000c0c60042680d1004110314047c080d019942600c1c2c124030210f042152a800b00071400880c000150309014a01c0d02100080c04490140710260000f6115880650840d00c40c1e81114074490b88910721440e2002005400c1d50280c000d125036600520185020030b000e107004e01c09455251107004003d201013400d01c610300b10300091944c01c56245640300e10b2406500e81c1d0a114100b40000700c0000090300050308020001900c1002c0f140c4414420300540c00d0f10320704000d80c8103005940c2d245003515520300260303004001c491800501e01008600401c02d202c104034044d0004 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 543553929 1250 543552679 543552701
    0xe0103090602130e1e0c030402061b16060f0801120c080307081c0b06090d23030304050c060a140a0207090207050c01020606030d020c1c06090503030a050c1e070c050402040603 77
    0x1c54140d07417140180d05070904094100c03042c0c1940040007419000780f030320045a04c1840609150b003800300d2130558000b400d00110100c10190030416961040b000b0f0910340c00009c20480c43c0040d40080c0e1048040d054003018051054040d0321070b0300c0202848040480400207128601c1165515941410800d0707680c0c100c00100c074440c400e081010709016440e8000e55400076002041c5600d8145000c04120f58610108070840303001e442443c180071100c2d8059030300d01c2880e00312805140d591402e4501a4105120205143d2040c003080c07140f44100c41e80b09501c03588a203681d05400e0ba403808080d0044e403400150b0f40c071080c0741e10b00000d0a2030800401188801c00346800fa000c80c0e00700cac4c69541c10592134540e20307c00c540050f07101032000c1d03205107022184880905031400c59005621040e8464006440c0700c040269610b5100100740704030180703d0310419a018500800360382c107000c00c503030701842006c56501c8031800ca600042900c205000072900c0350001031000400441d511581c1d0720025018120314020 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 543555179 1250 543553929 543553949
    0x16080f0705060a0e0d0f05010509280b04080c0304120f15050408090607030504090c09080d09080d031e0603030e030706140a0503070203130602070512011a010e010309060213 76
    0x1042c0c20044151081e480a40d00c400d07500d00311036414010401d41c44181501c0d4040b041c00800c0c0402c000380b044078014141007014008a0301d10141101c90440d0260a4180c0404000d0f6244c0100741c0103540c054210382d11010007075a40a031009030030300e1340c050750304084526220008038030304000c520007004604522032004004881c0c00d001c8080c00b1100201c8001d80205000c00c00110035161140c01080c0782e902ca810800d0416450300d4451007221200c8007128007150100c2030503c061502000104040c15941c44c0c1039480d9410080c02c1c82d100c1040107111014143c64481e00d80301ca10006500c035801200a0800b080007650b00c0c2070041c44440c1550440340640658900412a0740c81900c00f0810500030351552490038201031021605540020140000c41c041407000803440c031110581078008015036030050664070b0421040004850400d00f85041680c90004a000304e080109100f0b01d500c8401d0a283d0803a48c0300600513800b034289498020402d5100003141c41411140c40c031010241e444e1803007 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 543556429 1250 543555179 543555193
    0x150f07320607090302060d06180e01050c0c0d030504060b130507030507031512020f09330306150102030c071d01050d03050706150e0109140c0a0e010c020316080f 71
    0xc10380c0350a02a10580c0000d2039900c014000740c10403038024403408601c030b40001040c43c2d07039000e181110b02008200041e5a0340316403041c00510307424042d00307401a0360300c00002d16100540c0c24166481041301d10381002d154840002400313016150703104000740f200140003214030003001c110719801020100d80403008070b441c0c0000700381030510a01c110003490440780d8036203244604102c3e035200c00ea010240100d0380544100c0c1c0400d000e441d201c110074015810748190762040b00e0920000703c080d45c124800034501803003103048440c040d98005080760300004445095000c2e0718007880100d0951042c595403c03600e00c5110b40001d11005441c1d4844000d081940310340d011a41c0311010440340c100081c1c8003500040007403000d440403a48079888405190100c0504105065131000b04182041c0d0036804003c20310303500c1c01000b007070a5404603d283c0c071007005901d541c038081303e180014200303e6a00b10280d040201800400341151001c1100d640c0056000f8400b4001554805645903140010012803081d8002d0f86 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 543557679 1250 543556429 543556523
    0x80c01090c0608012706080a260909010506090d02040e0f01060b070c0e2a030603060f04080301090b0f031506010f090e13030513180e030306150f07 65
    0x310a03513043c2c2c0c610310882c0e6219043c101901d241e030f900c400010f0308520340d00c02c40000c4100d410041c00e0101031103600500b54050300440c0101d0081f841014140020030100607072203942d41c900c0b0b10345064540880366151112580c02c042000d8209850001750043c0c81c040304003014120006202c00504d001d003000380402625181c0c50242402410750052a0b0581d5210911529060121083d84040701c603550142521000b0035560a240d8114500b0040480000030300440e0b05007803111590003c012164001c5038109035031303a00300c039220500c2600c000c16610802d1140a54400c4c000c00d1081c8030041c01c6822407000441d42200c20710003a1142808078144001c50700742d80303000e0800c45040f10040100e90110340d850680038454900300c2c10045007000000c0110a040d00040c0e0b88500141c451045541d00a04507511a1412140390744449a51544103000300000b0740c0d51070190a908404144c001612058203199a280d030340928076000703011003000121110800e0040d6200700401c2c26034004880740d0708400c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 543558929 1250 543557679 543557687
    0x120706230d23152b260a03020d111602011202071b0f1a0306150712090e01170304050d0809030d02010b032b0e1f081b040803030103061503080c01090c06 67
    0x14007908103110351404400b6011920426202e41d40d040400c030145c0c401c1e83c07600c010001300d40c414184503010a5001c00c0d100d4001c9034038400c5030b10140c4401800c91030002c8480d403554401d10240b070001e042100000769205202515012f03101115841084a400380381e034015070860490306c2d409520008a4514400903052648851b8400608904044203146444034003d021401c04010101a06198100400c80018060002030645a14256501c4003801c0c2081100301c403124041c0d10080008040c49840e01708114084101c074215581207400f400110560b00d403551850140c54400da030b00d0300640314010790181e010b400044c44401d044041d04e80c0c0c02d10201a1070703100c103281404654461440340320146641e000d07091104c00c012000300280030b003802400f03543d5540d062100060000038402401c1c4401c6400184891040d80e000c401c4184c20241004801c1f55030740414032000e042180c840e00341101c880b0310340541c58040e54000b40034903a00c0810445803400f030810981e04440805540c040003554901c2 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 543560179 1250 543558929 543558979
    0x31707050304030c061a0d060c1409060f0915120709060302070c051e040f0b0a0902030408091309211d0108070518120706230d2315 58
    0xc143c0712200607440c1c03503d6440082c0384500513550855280706d5445040d03a41c41d44c0341c1c6102d921811021460b40080d130001020708100e4042000c4980081c020611030303a0340c410550314020350301003101d41c0360140d01c8002240c2c83d840c0665000c40c130200180010300c3c004030100b90f51003105942c542038a11551054110100d1080100280a94a43e106c0034030080c80c2241804c500390340e11a81c11010403c0110020701106d100701d9601e0606551032140035081e06066421000604d50981c0450a514058071900701c0340c403507601d1840c842c0d07055001d0980c1d0134255620405040d908404c42d008145403c00e03074020755480036000300c008a40140b001d60149260301d51010101107069403090f0141d180c128090f20103422640181c4818192100490700f251140c0c4503031180001d00c0300007415118500781c1c0242456050300510000108130a0b441d01c51000904100ca241d608010000220440180c1c107280812416500c2504148407040500c920700e2045003201007004011111890b117046040144125844 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 543561429 1250 543560179 543560183
    0x10204080d0915030e0a0b0a27020d030e011b05032505120306060918010915080c01120906020d050a0b04180b100503060103030804060605090103020108060427031707050304 76
    0x4000f25246000c9071281d04804000070400088403030484d45a40c1d03d110710481258151543c41da1500202046142e40300c2801c800400c0c20440300d68040315070007155100d40d03405001340608c0401980303000c1c2c592040071840010701c28141d080744a00414071f019522644a042185190701d49228400108040346060f400c849900c48001d0082d104450160710300c0d504000c03d0b45500000a0184090a480b010828995070b80e400c4010f001d20340c14904000101c45100b8105200000f1407641481040c40004100034100824208a50145040d04042025000c45a4010a480d00200c1c20b4041e1509680149018000000062048030107178010703c011603c011160214141390b20003a240801c10540c5c0854111165a4204500d00c0c3c580001c82e00c3c1c030000b030b841240000d07510310821090014600c40c01010f0701044600a030366516640000704904006010b03079106a50742c0307443c0c03440040c01110310440c07180022a0208184032a080240c40044c031540345406080c010303400502c10b03078032610859214907 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 543562679 1250 543561429 543561449
    0x309290411010905030d03091a040510020904111b0c03061b09030109020603070504170604020604030201030b01200a03110f0604030507050c090a020d0e060c09010c0c0f08010204080d09 81
    0x50384644501d40029560072640d410b0010212000c03440761000d010b6a1111402900c01098904040c50b118140c403285824031b68480141034180000100c000c507a80000d0f440221002da01d54082000140043c50652030b000c2d1a40c100090f00164000c0c0d8401050040d00c800064404484610082c1a2110412160118580c4039030140d20031303081404025200c0c001d000390001962111030340c04100a540156012004580042400c021800e011200d041d4015a9580502402d042660126240c6e0065001c002c0c1455150790668046920420300c0d01e041d1520f50749080400b0440c0351103170780c030380f40901c000b0740c002004081c0d03000da00600043e049030a0f8400c00010001507407581c0b8203c41743d0300728040c101c8542c01780030804031490380c07545100c0740104a404001a520b8400c1c040103c1283c20844002c0c40c5a00488100000d00700c4150513030f070019030700f82405242244a458140c0260a843c0c00091000000e080041503604055010b131080d10400000c40c0c018890340d91043e41c0c01c0d85140701e40c40a031 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 543563929 1250 543562679 543562681
    0x1d070314040320030d14220203030d05060402090a0e0604150e060d02061920010e060712090602030a0b0307081c0309110607030e0a0504060614030702030712030929 72
    0x90854855031810801a80f002e90782080c541c5222481541c0300c40844144500d805414481103005610980d00840a41c06009006031385a41c080390312400355074110041641c0c3c0d840090310640b02c035012035280e40002000785900c41c2d20303050a1180c174501564064061450001c4000c5242c1000d640d41084d1210b58080c40e880d80d40d19000c00200041d102030490700b2040c1445901440d00341c0388807203150140700b81ca80041010003c0030004855001500c5591103a04100020f0754020740480e18503001459031030128030307825030101100c02410a00307100900b402d10000800254054941c040d8501d0036080702a500959962810319035a900c624032005990411011080140c901036801344805512800701c039a84012000c00042080c1c02145099002c154012800c03020340c40c051035641c000e020304450400c8214107144000704070003c42d001c00c07146182c0000c0400c80c260b00030401d84c0c40a541c441c1060a03518810300e0010f01800d8288000c8440c02640a030b500801040340070120509074080ca000422 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 543565179 1250 543563929 543563957
    0x10504051902090c0d0222030203060c040308031b0c160518010e010e07022107020a060906020d0507110901180f0203060f100e03030c15010b03070203040e040c1d0703140403 76
    0x910b9108100c20174145a081044140482c5000210b201010b54540d00180e190b01c0c50045c5410000b00030044110124100824000160078070140c1e80c2101d45450000e0b030401004011305480d21565084170124465588943e0a0b42140501c0e0f105a0f481521074100c0c5001002c0082145e1600303028200b04440d0440060004c581c1216886038050020b1040700d00c405003080c032036030350350307440803010640d146000403144207508103200c0803401025685050b4608901e411002034030740c0000c08070a410804000380c00018410745034400000c80c48020882d05035035a54443c1d030240f41110f540441d400310b061000450a0654a1082d28030451010704100b1404d02144200081c02c000a1a01030a005c3c000c41c00070410f40b41007004d0081d000b03e0200824050f0002407403c880c6180507449407e44610400c2044070166021056904a40440c0780c0c1d41c4140d2038510300300101400a070051000943c200a074405071110140d1243c3c0280310f21340b401c01c0341c80c485040e200c01c41c150031500900400c4444a010f20 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 543566429 1250 543565179 543565201
    0xf0513060b0f07060b1801091d1b0103020d050703021b06160e130f0b030115080705010c05030c030a0c03030e0d0c08090d02030a0609033507110d0201050405190209 72
    0x1110b01d204000002d181170000c030018072000c003201d105000c0382d101c0743c005004036030a0340300300f403d00c41e50000c3d8001e1040701c106269030740b0307031fa10305070f01c04412034442d035100c0940d02a8040d1500005000760174002c9160005004000f50803102072050613000c0045c0e086d41480000c01c0b0309001b01c42c1d01c44040d0388501680740030340b0110124020076070043d20700d01c1061110300091056048019500d90045982e02c0315108041c291085a84240410381001c0f0003084502d4001a030b2804030340c401e080461401d05981403407400c50007286a0751046000003d144454150301c142c0d0b41000c6803080d1010000c500e0306104007031307030b40c9015064803011400140801c404141c07850082d2440d284024210b0b41e00c501307203500ac07a0a2280c2e244080304e1140d25452540109500300192000411085024210040c090729003001c01c030848010465a841d840f2002c5448507215203901c0302282c1544085030003101039124000c1c0209011981512039008404550f00c1d00d641a03810741d808242c000704010003a460303548000d6 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 543567679 1250 543566429 543566437
    0xb0c0304020d0609050d0e0307050604090c0302120c0405031002090306060d05160f09060e091e0a0b1f0905010501090e150d050a0c050303070803070807020c0a0f0513060b0f 76
    0x1036400b85048040c80d000070000d0082d001d645202d800070300b8000080d82005001404c860140783e129811800080c80b4545944060794101d030403005011920300d500c40c2084c0c0082c42000040600f54064008004517044484010022203038140d086800300ca40840d1440304030b000780d0807030a40c1900407a010412501d804000c650b0014021001e8030300d4031029001c00c0c1508415640310200d9854404010403924480344241c000500c0302d1a02c040f202e02c0c0c5826a19203582c2103480d00c4008aa0310802c40d801d19008100780150241e00c081d05044505001e5208000ea003100103000741d0340a02031001003002c0c001c0b409900c2c1201c038184c440001d02e600300080e44844100040c944c4600301c02d0004618080d503944003544d41e00ea802000a0700c000c031654200800b0110b510b802141c004d80c41001402c0000d8101400c4950000c40d48c40c00040c01e8681c100224106209205240d51042c411040800c1c110a04521101155001c40f402000140380303038606000d851591140c181c48040902c003224540300040010 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 543568929 1250 543567679 543567683
    0xc110904030917010f0f020415080c070605040f060b01020c03062e091d01050f0402040905101406041d1c120222140a03080a020f0307050a0b010b04030b0c0304 70
    0x10706801e42c40f190020101c0b007100e482c02d031280e074542a170080191254400e18070f0030000b120003585002d090a004d4081040d4555080b0200a80c03080080e84541803041500d100903480242070019081c00d003803011f006100d8460503101680b8011480c0c20540c0000780c204c3d6007207400381c080c00c05a07884403400e004000714078007418000d090100558100c003101458400c0946107101000070000c1303580448501104040400410583c07504007800101800303400220341c0035504480101e10301c0080e288c9203080c0f041003c10b58a8a90400d048031032040803505503184501d4068030f04102040c900c800e82001da43c2c03c01081e1555800408603011950881003852580307240c2e07400e0041503a44480c212104903840540701901c40d06018050140492008846000404001031661000380f4160005400001144402091024000b8560446c103000348020061000000c0550f81c40d0101400e0050300c0341d10700c22041fa000500d41c00089103007000f290a840949030170400c1d08803180e40e100104e5180f50301c007400c1 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 543570179 1250 543568929 543568937
    0x9030304091d010e1911011707031a03120706090318030c03030801050108090c0f010327060e150703051302060d0b04050c180108040c0306060803190c11090403 70
    0x41511220382c020005804121100200ca480442c100c1508440b5080382006454000b1640d0341004104030302003051041e005030808996403407410058400141201c0d2a9940480683c00c21a1642d017540c0316011801b0203400c001182515101055207405054140d681415410b105e00b0004c15180e911810301e981c1f21307040000729841002223041c031400c2c0c141d200300c41040703110105004240d802170510b401040c0a080086080c10504007c0340c5901a5900183c0101203050a1644580c401d4000b034510a0700c411a8008841c0014061400100c0c801001d03540390381449030f0b01081c20f000059a2803e8034100c0c1b240e1110361100d14007140986406000e54509505500d03091015036601c60007801342d40305405002a0355010007042c0310540340000d05400011409020a1802c04c02da44a8111259424038100c02c1d40e50741c078600980c0b41005a0405820705181420100d400b0900200615040218025100d50019003010131140003ca0410013001a4603c0150504508004010a40003442824 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 543571429 1250 543570179 543570187
    0x10f0c0903030c02040f061e0e010e06090a063506010f050d06090203011109040506010905011e1808070f09050606090d0203151609050a031a060a090e0c0405010b1e090303 75
    0x4007000507117090b5001111234010104007c6c0090b18940c000701c0080030711700f2a05c2429850301c1921201110001d11003405004060b000810b1104181d0144005d85078144003031184442c0302c0c00c400c00b403904011259540000790910a42c80c9840003031040c3c1221000c6000820355820700d024050780604115040322050b844200440041c0d80a00803d0034800c1207448243d1030360fa8610401007915000745c0021305201260b0814082a60700c1980078104950141d180001150341d000e084881c0d94041c014403e42e011600b01c046034201010030b40380221010400466485a00c17a44454221070707055850030b501080400c8407908508005002515103400202654809551000c41308400c110031120101e02040561110100c40e8108160300c014040c11307200c6110703050865807811010b0100550f904a28a400781c0002e2080d515007034910083d00c0c01450911001d541044070715a105400e49003139100380c3c10300e000800c1000c050b01c2174440d107030314808003071081c0691040341411645c0450307402e94050000304 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 543572679 1250 543571429 543571451
    0x1812080c0708031204111f1d030a050105012402030403030e060904020d0903080a0c0e152205091b07110609030a050f0c010302120c0a09091a03010f0c0903030c0204 72
    0x1c0041c00008070341c540c2c840205d25051409010f90700641220a11032212005c03100d41d403040c6c068108090010f2800d000d02550001802494413900200078075601d84a110300003010410190041070480d42c00b5284044090a00078140c00d58044941d0312000580c0240010800710384900310762040750394082c2009140c84000b81c0450166070045454080007070325801d4000c10980e1040075581c0c0302e12220405c01c003a45164070000c0103411f215144034030070b4160401d800307503c8001030300302c914a509250032034444013034001034803e0013449885180d10810b220400034800600440c6420b00228008003072601c0e10005070385508102c804442e20740d410207000d00505101e91010808002c445001c0d0000b030050354030140710b0b145040700e103420460406006020358401100d50000560b0020301d0555121340f180e41386101110760310f00a070300144990b8101144260b815100e0111909603480036002032000000c90300c0f404080c1d940484076600042c807101c0c02000403038030868040106074401880070403100004 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 543573929 1250 543572679 543572683
    0xc020a12140c1c020106051302031005030f0a030e010203030610030203130c060201094101090b040b01050910061d13050903031f050109090c050702100f1812080c0708 73
    0x114001c08076641c00f100d40d6500040215810300e04100e183c1c03009000380c80c00c5c040071621140d0702e4020108515000b001203801081a9450100900f00280455008078018486540d4900d40c1002c01d030701250340c07a6036985683d40f001c821248920005030100c000c1e804220000c600070340c4000c180c0041104076140c0e0700d00082d03400b91100010714040d4000704160400e4101110010345040346080d0141515036100300b14070602c0b100c4090103007403990720340c0403048001e4124050012090020a805441d40401c030805c507000b4180c1d816218280c803000000e540c0c2119080e9010043d002e903002144040c0c0003c0c00e014403010b881004240e0162011030716040d1000c5c0c00701641c00c2560800040d403c080104111002070740a00a0801c5034003d5001003545401e0000e04000001c0c000c0d40c000c140c071400100b01c0c20740100c0c200c685266000e8002c409203c404840200650b100340804000140d1180700f0004010442c02d0201c152004c0c1c000b00c4042002d955103501a81d8481c144504950140c0c1000180ca00f100b = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 543575179 1250 543573929 543573937
    0x201120e07180c051809040510060b0d050601030506010c060c1701090c1b0c09050a090b27280201031e230408090f060c0d0201020706050105040c020a1214 68
    0x115021014945500c05205007510030083c03061007000001e000c1d05110382d1000c010511030f410261400c0c6856181d90810f2410614410900d040040c1000c00001d120880e80d0020300f00c120480004101e01d0312000011825500e06580483c00903d9851166000c9104c07684042d020240b1420403d0040d09010140b2000340d03c240c0c01021144d80e01c2c05800070840c1c000c54540c41e4102c40140c80101d4160a95481c001103415001c1d031044c050340c680003c5c015054541c030690440c0d820108001a500d000c9580500d8184407554166036030201d00c11519001c1d0000800d01203020504a10085c502caa00e0711648112003402805c2e410142c44501d40d50702c540740d0340180011040fa1200225004400e01c2c40c074000b0114500003910b178031080e2420400401c04903015652064000ca4250302a550208001050350040480484d12802913115001c40d01e5015401810000e11442050002d81ea0312000c02c4111490342180c41d0160300080c868000040114410a2001c0f1300790401c0240c01c4680c43c112101600 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 543576429 1250 543575179 543575189
    0x1d010c02010b15040f0611160905060301060e0c070b04021c2102031e092209170f04060809150403050702131b030e0a15020310090204120201120e07 65
    0x154840040300750703043c08540d0100c2c25980400c0e4600e441e2034000402c20040f0b0700d100303038000c02c4040360030480c0c1c00c2d400340703c01204c004c001c090f43d40c0c0d034a88448854004000982d480c521a600c7d003980024040c038030244c0c46119800344100c26041100c0d0b45c40704441c05400401c1240d10818031076528582041140d5020710341170090090340310305261125111301d5551a044100e055520034820b600c0c4214212061400c104405615941c88405480c0400d400001c01903420811688900c0c0c0d000d1005c44650044600e01e0180f10703440c52100c2c4000c085100e501c40c0341724600761010108402c2c001c507070103040b5164012140404854030103c42c440201c850b03220645081300020b2002901d40150315041008910044525404000c1c105d4420008000c07a02c01c1c5131346005140e2103203140c0902c141d007800013665698018508050841000383c3c018020f6000301c0ba01d5031042400711020808419510a542c01e407032180d4000740003000703607400642d900aa22924105415141e8440344075060f000c0c0b0130748000700 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 543577679 1250 543576429 543576431
    0xd0611070b150319050c04090501020a0306050618010503130602030901020d0c031418070b0325080408030f061309230a0512071133070201121d010c0201 67
    0x4003a440c09032152040941038000121441116901664020603246031115107026180030b1030081385880b40c10654180c0e41c10750b005241c10700780028400103400807c8140701941c0c081156603103820800010f40680711682190300c0c0303507000c03003070311540204003c45e0030804030340c1401c0110075141c0d9004280d91003182c07010001d0b50045901924150f0900500c8a110481d050034420303500c0e516142881c1080040c1020030b144010142c0d00048076080c403c1070094000c18980390383c0da180000302c251244048c1030050954071461403c60703020038841c0b51550b005030f5018210600e951140080300b02008006040f15900290044c8003552070350040c0300b0307080004d12408042c840350305042c100c4209015141c140000c10307044403c2078030002c3c001280c02c4c4290403410b1034040d1501134604010391307040c0100030310541040b080700407003503403c456600240ba0020324500d00480101d1810106d07005004100c070090100700c1082d0719081429440d08031030286804082e455000c0d1082d00a05400c1d203e440c00050007503 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 543578929 1250 543577679 543577687
    0x150d031206050402030108030715020f070b06030d0201021e0a020c0402041d01090b03190819020708120a05090d050f070b040f0b181315180c0903051b0d0611 69
    0x4000380780504001800225411030541d890510740326101c2c852507000411000310ba0003603014040082c0c0c10381d2101003041c07031407944481c6240340a901088003a00c01520030300c144059034030400e1050085859500d02c145c046d9016216951520f0b403103400c000800d0342540911002890f55898500c0170304024000300000130140614103a2101c010941a00459991420051681001c0e2000910542481507801442168602504000450b40954503929a2103030420b810068001c0d80040c20034103541310902a42c010440d4030900130014030540c042403020030000d2050700c1c9140b41c143d40d8596000e01400075101e80d591110703001420b080060304052000000410b0601c40100f04c030b0380c0c501c05001100300c030900c1c000221804a1500340d0981f0120310803895119002e4000c1c201d9041402104800d45944c4140703600c2e4001203207800d840200741c602c05844c100c00481c51a00c1760425104580d003000250041c4004c07089a07074603800b600c0b40200d4001141d0f140c2c03440016030f64032480c0c4d14840717803416098907 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 543580179 1250 543578929 543578957
    0x9041112030405150d0506120d050702010c17031902030411011215090203010f050111070509060a15050a08090105070c060e12180f0d0309090b0406080102160203070f0b0d05150d03 79
    0x1286e4010384890b001c2c1c01c4180008040510000c1d407400e070b08599003001a103d078200d100480e52019003150080c94040c01109140d404103180c800780d1b003c0e098130028515840d400c0344503001240400c850241c00340b4001032041c101c0d940118048020698154004640c2003036008a040c200e84455000240c56580000104004046c42d10b0300c82c081e003001d192030740c426510402c50b2565416140642c40c42409000c01141d01d40e51481c0f61000106000081c91000400e030030700292103034109060510115918000003464040c040c45507510031701c49519840d80321744154845100a06000c20020018400c2c04008102a503078000a0103600703544c400324600c00ac0500b414440040e41c04c0b4074080c007441d501c0000d840003a402403060b81c00c1e22045c0b0310018421106c4000a4044d11203a40034581035480015040141c02d040740b14807244500070f4040750402d913501d07020000c08929504c241c1e41c00174014000c45400c8103c03600015004a8138800040c000c000010001e00440c181c0d00040303020800c0c41c01d4503c0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 543581429 1250 543580179 543580181
    0x80705190c0504020a1d18070c0605160203160804090e031909241404060e0a050105032e0b040f08010f0c0c120207030618060b09041112030405150d 65
    0x2001e00b105480650600d98041e9010308014280300c503000c407805960b40c0000003604c0f420100c480030391242c0740c0e88109060052028101c401c000c1400e49292741410001101c8a104440744406200b06074015443d0082c000001c0c00b5069a01004030350042d810040024000748a00a5070076050be04005035980301c50710300142c80d20003c82407009043c41b01980c02007040070444140e00030b80d094112040c0c000311001c000d0440e24000070030281e402815020802203070300c56200c01e0034030311424241d403542c0c0066141c0b4010350f40780c0022202d4404205003103060810b10003002c803c09246185405101c4491030700d500071450700340c015410400300141c0283c810820b2100901460718103207001402040702e001c6115000786000004030018107a08031021410514500c200091402950007400c200243c0c0b400303141070380d5400d10604050351203900300000c4044624154018030702071a03100d4045000c00071290300344800b0004031114200103000a000c00100f54443d60401e0454014040480c1d96818a5243e0300d0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 543582679 1250 543581429 543581453
    0xf090e0c0406080c0d0303060324150e15031f05070810030803160e0409150c020313090b0130320a020702041b09060809060a050408070519 61
    0x80c07199040020400c0010004138045020b604107580b40032a03040c040c10150050070880d40024040c2201603108a0030b4229141414003408000a06100c00e15507841007180c0445503004031a52052a9804102000c000302041d48000748007034159255501804030003152205c0700c0d002c02c42c520381c44004106d03000358032a0728240e0000a415803142c8040c03d42d15046a1400010244e18941c2d01c41d04078100c025025440f0300005401c014030a01002c0c0640c580f24002c01d0142c07000c00c1c401c5080604080c0c1c51800401034480c40d40601d8a461200c42c9010514400360403031100740360602c8844420705111150491001075510f182a48842052400040000c01c0b91440b2500f2822040440c030f0200d00d000708020504079110b134408200050307031164244a8000d100300b000003544030b450100c0b1140d84904903002030300607070040d44803001100d40e6a4000c8e2105501255000c0701c90300324034009004a5155032203290040d00407820386003000d41e150740703c0346005000c104440e407071412410f841082003002d40d449 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 543583929 1250 543582679 543582703
    0x180603010b1e0a0903080f1b0c10020708060604090201030e151f03030f031d0304030311070e071403090705041802030c01020f0729070c0f0503010204061205100f090e 73
    0x100b85400d02901c07001300400781c2800000c009001c000346501c2c04040203015a252025404a40062400d80910140d0350f11841c5074400d01420200e00120921800451004100d60126002e0030003503881c4030400c8014810380104905043d9980761160f0b025904004500800c0d5800701411864181092000d008040c1c1020300c54440089030424070000b9031050855141000ba82400f01e111013591800c0c903080f840d80ca01019592201040000074903910800c40d038041c03440ba5041e5400e498448185001c5e910007141c2c1344000c2818002001c5002076024011075100701c0303401c181d4000a8555000905441030200c604040c00311180b032740780035854140904020a18240024020042aa0003146e1100c80902c20b50203c00d0b02c090741a6090f060100e1030200d1034910046090395001ea924000212100a00038210b40368452000841c02e41414030840b005c1c0d8155407140e0a100809075080c001420004000e000240a10000094a9170031500303500060000c0d0900420a0b801403030070185841220460 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 543585179 1250 543583929 543583987
    0x50f0703051005010b1803070b03091506030105040b04120909060605190c03271a04150809280c08030a120605061803160311150703090b180603010b 65
    0x1040175000c090202d071880116001045000c0344003800080c140510740c3d02046850700008100300c0c0d200d0000c0380888519000d00d45610302602d909060500700d41c01120004d0809040f0310118000c549107440c0b408080f0820329211600c980c40344c0d039110a903180d17035007c3c50101d040402c0090394800c5400c0951540ca0052510303415490490724001c03d04031410200e40007880420340c401030100010f5900070040c00480c0c0d04144030548410f80030740c45921520032645000085800d180602d4072600d4a00d010321a0344000300a004440c8461011003820008214005100b01c010040003c110107201001080c05101454440f0042c03180a002c14212982e0118100d01c0c2c04800d10240d6245001d40752188604203001300c2588104011034070700f006113042a9915105040c00004008901c1517281c60803070155504a81c0040790610403600340241007004003c51100c1d01c05024825806011300190700c07940000004090700e590104540b9030081c3c220103801c0388001543e00b610712555030701c8030301c1800b4120 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 543586429 1250 543585179 543585181
    0x402040e010c0c11180408030411010207060206040b0a06031a0109050601030204030507032909010e1209010215091204091a010c0b010b18092508161b050f0703051005 73
    0x500030000f419088004108500010f664001e0351504103d2880a880c000702049403402d141c200701e84a07800446007114a0b8490100c07040c00e40d440840d00034111407e1b50010a13050300e56a948a54040c0014660041c00c0e0f45c440340003002c174071054008a60310910f15640007241d41130107040c1c01039400007006c003418035004210030400142c002421004803504030345140701c520101da03415412038a0450400007151500010f1004514041d4840710040c40c09400702c8441090281042e4640d02811100c13902582000c203103030b20000300760b05145034000782000230346508202140141c5440d41090b0001280e55560350b444000d080c3c00001000e80000090a00320008151556040c029950500844924080102d0f501c407400101c840b05030710601c0c00400042040c64455000d03905072844010300729652034140200034034940281c459134020665074940d54096032011000395806149654417a804403c10350480c40454010b200f540f113a021030300040e04081d8958101680340c000030500e40003d442c5400 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 543587679 1250 543586429 543586451
    0x7060b01081b1605010219180501081003060c03290906240c120403060c030f06030b150102030c01020a03060f06020706081308073302040503030d090c090e060402040e01 74
    0x5640500081d0f6842d0303d07043c125483c11601a0080400c80a5450820141c1140c0035400070441041000d45104100f40c2940d80c5004680c2807100740c2d60a030740311100780c006001140003034126188800032401d01040c0e81441201c100340e05030304540d0520070986814075080961604044d0307560408802c0b5024400c02f0504181e001c0704040c01b900300c903210640004c00c000309410920a604800c02c205041507203ca0b502d0800345c0c003405041c8501c800103860038a1a01d109940361081e002583e0700104000c500f59240c04201d080c00c4034003400541075102c140601541c03044240020040400300d80c1e00800d80e98034080441110320300c070b0741001c015504800e200703101c1b040e48603680350391041200c00c0702018001e0508150307405108098028009521402c3da080302c00b1004501d40002c1d02c00c241d400e480710700302c1c20b455a04178055405200c2e03058200700f100c1e0003650403d820102440d4094203954801d15030b1200c0304411a090340b1511403140c3c00150030081136103460703c609500304201c40000c0c020f203c011 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 543588929 1250 543587679 543587731
    0x70e06040207051c050a0801210308100b180414041509020a0503030a230408101508030703030605030c01110a23012c010b03030a0c110607060b0108 65
    0x519050046a000c680041406010071161000307000e6410301400903465110001c169174441c0c07400102081128000043d42e000c840341084c40c05009102070702c1e20024603a8120b41490000e0214040c0c02403441c07001c9030380e601d00301c001c00d030200c04883e0123080d05025509000641e400c503c1e401c0030154280e002c01000c1a07241d034110000f00381c084400266904d0900c001440c1903c81d810603078140c4408500c2070310094000b1031001840074214100010355801004840051040340258950360700210313040300fa4104240c115008000d2038640c1200c12581300c00100d440e540181c0b2003500042d4403564100142d04050001e940040400c0c6401e0047c0307507071400b44640c4c642c507900b070003006020b581c1c0c5031029054010000e1258250804020701c070030412621051000c00b418144440b0040c4075022000c000841403043d065800400350245003485030110056441c0500c2900580ea81d400d00c0d05044c1b000d644150041414a218200018094a070301e0001804150f0041000c0d80601d00707000350b40b0018000e = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 543590179 1250 543588929 543588931
    0x6090e0f12040e0c19030506120d020a11060403120206010e2202130f02040611061311011409040204062706020705130f1b3c0c0f080408010e070e 64
    0x500711070060f1901d418002011034401c21900020030703a42c40000701c0300b10307070b1580115006260480f10346900302e140107802611101e0368581440541e00c92043e4100258803c10094003402009103802c0c102076480d100e0b0704a501403004400d0043e00200e0041c841e8035404040590050380005031802a44070014a01400c2440f104001c1d00ca0320100c641544024142d03000421020310030750741551035950710440501004d0800102441e107005031000200f600e5a200b8a40e4012904014044a0715241038010b690700390344c0e850210391054080002001a4a4078002000100842c2d5610f492082456269444051503000d0842803040d105004004c09980001c000c015102d0803100d0550b00001c0c284e60200401c140100000e01c0381c01e000c80d40c103812180200da0030b10290103485501882d503402070429024000c01e0900581c02004544000d801000850140c81100180c2002d5200c82c1e01c3e5120f0441241c950304c8104c50740c403800601800b0a0200303003e81d088268a4100510103d8280308d1945c0c4ca0541c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 543591429 1250 543590179 543590189
    0xb01090605030408160c0f05090903040302041d070b0d0606051606050c120408030703050708071b0f1401060303120603022409062107090605030f071206090e0f1204 72
    0x1070201c0801c0a0140d594202c809441210481002c3c000903072405142e500410712401104150700007000a0905040c407241d4400e2174458040c41c07401c0e0079607080100a00d842440303c1540c01c403840c3c0078080b9090412021002d4003000e410140c4940c4038004001c15960365403c141c0410505202e80200480c3e41d1b01800c0b0020f9101d00045000c3d41c0780302e00c030030740d81c0110b401d0304c020035088506100074400c0003001527018a12030f81e028000b40e40c580d0b03130036100c1d00001e407201d8000038070328001403295600e412441c1116070302c5415142c0301000181c48580c804514020281840d940d162020001c054204072040450305446a041c0140d40ca1a00007400303540346400d1041b100c2d402ea84200450422103001c8800703500006190a403909614519104c522641c800994001a018000b1500c464000e9587c0002c840b081d80d0388a1455a650a80c0e20b0803040161040c001d0000c50a540740444a85004e00d1740a000c580c040050040a5100241d21f44001c81c12448019042180c40f50300001c504001ca50a1355 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 543592679 1250 543591429 543591437
    0x20904141f14010609050904061d070308030114060304170f190206070915051b160f060305130807020d020a080f0d02100b030607110a06050406020403060b120606191809050607030b010906 82
    0x11740b41030346070f000b50031207002082b42311300420070b02008229149000d0350681e50301c80c040c24440084241405550310054401074030f66550814660b60302c00c4900c0050194107290800f6605140c400d10108030500c0002c0740032070241e0032020070064040d40c80700f20303500109510701280300001d1180da006002441030741e02c0034490b0400b445036501a07040401807081041c1b031080c015180c443da0f030481805030414502909000a0510000c500c211144619140280303400c54105032404231160f0801c050a64410012a00310100c0d80c4001030342402440700c88158641c0d4000b4012041c5030480083c20403140c5c035903150070203141c1207101240e81c900203503040d801b42d801d04240404111800e41c4601c0e0012808006001c01e040c20100000c010a40c8c01400490344244414440c101d4000308000140d0942114040594003403000a2090310b01044002c0310b4014081110f5019500c031406806a103072101105400152604480410020100400d0358011801c0c90100402e01081d0f0000344800c5c0c0c03500c02c0b18104 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 543593929 1250 543592679 543592691
    0x180a081b1504050705011115010501031a132c0a1b090608030a1d03060403030f0b0301050c0c0c1c12051615110403020904141f1401060905090406 64
    0x188000c20404042541148034404035240900e44240e503a13041e13020b0280040e0400b040315581540000d0400c00039a121a9a8800780e0f00300001100100381200a24131405c0c02c4a01c0481c00c2d4903444402c1d92860f141c07100c041f803018545088000c0c8500030014045500c8900c40c2010380f4904040b914072070b584c0e4808403000f504a8034080044000a8542000400c603151400024100718000001e11268801e52601841001105c02008950090b40c0426800d82c11203c0042d00080c881c2c5c0c03102c0b03400c0c0035105000503140d140c1004242144d0701110124041312000950b0b81403890b0420400c1c68400c400c9503541d28640e418888440f0f01000b02c28002d125a4400701211501e50046050328660741180c1e240d1059180f05c0c2c2001071042e4031003012246032a290210749110130704244c00b141c00742d03070f00540462700c41e48499a401c868900c007115014090700035841c21201d0545058003502d0003034404040466a003d0003011240c03044d10682c40b800611900c100c0410032521003050052348139810581c00205 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 543595179 1250 543593929 543593977
    0x20040311041a03070626160804021908071a0304020d03030c031b0c02011d0307030f1104060b040f0f05010f08040f021c0507050d0c0302060a05090612180a08 69
    0x2104118a800d034140168403002c100103500c1180700940d1b0405c0c2c0345400d07642d0301c0c00d030303141040210035682c2800d00010001c408400c18051401140c0007840501060141c1441c1a40c0e401c4216880d0406002d60b04149010810026062100d511100140e0841d40c40c6050960000d01e5800c05000e0043c113158941410000b0b441c029030095809608881909600c0d0180741c1d4010a40c01f2102c5049011400c480e12071941d0708540751035400c0c02100a4000c244490440d103030130601d41740c403240442b1640398502070b04020707440d0741c00b5090007400b203041565280d90030032010b641340346070035005564583c00c0309008220913a0700c980c540c08000510f00b0320300000d03240c0e070030038104401105001a400503040b4018000302c0c15003881c8401d8090241042c1e5400c0c0d038950303082100382a15454054100c01c1040c0080c005072420714006c03c0843c074181401c9242c80a06004a1070540080d2200c0e03e03240c0c508c5040003107009001d4480c1e0000000d4601901120003140c0d02c2c4035a03401a80c02c03828038a03c9001d01e00803 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 543596429 1250 543595179 543595211
    0x30c03090513050601020118030206010b0d1e20030615030a090c081c020f030d05181002090f010e1e120f01020d0608060717060f10032004031104 64
    0xd0310340500b25000b03012001449801904098802c203005600e841e0f41c49050383d00d60440303c07201a90503400303800a41d103005080c2e100380c0c04c09094204815039680d0b40c0303600c840e5200d070100c03441d824182e00070070302450740000268403884c3c00b1414078024808000f080740ca0b590702c1e0001c200c0420413a898039241e40751300d200305004014000e03000381182e03054140422550800105904401c0000641900b200030b01c9200f241c4404407090b038043c4030b500c1402041c6070f000c1c2a40207158055501c1101a48c01440014020325100000081c141015030014140b112800d100c1d0410750100c9080c0ac20a1469040c140821485403440b82d24954070348400c1d007081203030380c4c80d0722070761443d0043e0310112348001000303d103054001e40c0010404102c45203411400500c1c100e011038014414081d40e201c0c01c0c00076107200c0320010000001490070340c0c041c4882900b00003941e5134100e034003400d44c1240d030009080400e024440444403040c40da40082442c05101c100300003011284115a596402d4a0100321301550360702c105 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 543597679 1250 543596429 543596447
    0x801060c03140a170907080604081605070f0614090607030e030c060703030204150c1505060d08160c090501080307020f03010f091a0f0709120c050a06030b0a080118030c03 75
    0x180b1080c0c000100341c54034942c84a458201c01e80f10000084854860060b0305a07140e40314402c16aa03138101100013004070f02d40401030240854100c50300e01500050b943d4060505405810441e42512022001d02c0b810b544002c40c1001c1002450035140f6040980300028258022900020b040201010b82406551003d102c80c0407050009020141c07201f52503c0c0c050080e41040c003890000034800e004180c0700911461810034004d4015220701e86003907445184074050b0000500c2903030010090b600d90390015002800a09840440d102005102e180c0c9150074a0544107541c045581b05040900605c000540030088820711507045034902181414000440d0150100d40e000c034214030f1030f140710722051040e40440070030b00b60701500d003500c12580e88192500d2410801e9810754002881540244202805400f0010b4174900822030f4041d0a03a585001803020401500130000090301c5180359212801c4c51012000500203410080c40880881a8803aa441869080207810002050039900c28180100d0200e = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 543598929 1250 543597679 543597707
    0x1030b0d0f051e0102041e1d220f1505012d08060108150109200c011b03151a070b1012210518060a050f21060d030801060c03 55
    0xf1480420f4102141d0007900305210300460501c0e0844049211007030401c448040d501705070b8082c40f5442050850b0700301c0300701c0200107800350050710310340c400120780f0780600494103840380740c40c010500c8080c0303845906481e0008562a003e424200140074136119240c1840c0018201407140a44044205107010350b0074040d400130043c1e0003040d00210342201c0c041140c80101d40781690607a60782e681c800d040e02c1220060a562500310b03440100c540007a841000003030a04105200012410014040780340d500310700010f00700f02c08240c2e07500c201c4c005040b0540045004120b40f54040081d0303d07007445425400e1040940c000e00340d0010b0340c0040c80d5107010b000e40780d010b0400940c7c1d0261100b824900300280c480c401603661000608060716400c024403441c100d913521a00d004444030800624010b205c42c90b000814454140101800152801d03a02100030b001d07040605041140082400c2000fa819007202819550003040421000b40202c0e40040398181150301c0351030711205800246c00c0c03c41c0d40c18651640e03 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 543600179 1250 543598929 543598963
    0x52e0518041a04060602150105010e0a05061b01110f0715060b03040c03031805180a02041a0310150503160c0606030b0708070201270c2103030b01030b0d0f05 69
    0x7045141c40181c100d8100010000d40f0100055900c40c141070340e0315040e01c014000784034034440c0180b006510600304000c0c008000b03882503102a48581c0042d0054024400c0303009400c502500ca0044071800b401140150104100711601d00849d000481400e17100c1c0180180800c40741700000c0b51400c00307903402031000703150740100d450300ca04203440c24942030007240c031007600019520342c11904684100c100c207c0031204010013a124a01155207030f1202c101d402425600203039400e0000040c3c02803c04007443c40c1030f1383c0800300342c4d507446e000fa4480707419041500521a02208040090015501b2904880d004021443d0501e00001355450843c0ca110b4040e0008042c203003090000001c110060300210300031091600d8920207aa60034504a0803903500500000b990003400b410400d035503c0f500c55903d00540103400c0314041e291500d11030b06615002c0e0302d030b43d10243d00c40024001030503414401d00c074610300246801c0c441d10301e40100154081144c40d8000c1d002502d40c0c46640c003000310810444104100440c1c0d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 543601429 1250 543600179 543600191
    0x41802180909160801110a030905010e030f070605010b0a05041e080d0e0102060f07051806040f031419170307211d01050c04060e030708100501052e051804 68
    0x184a40740c0341d1083d580100090682404610541c0c1801001c002c492150641c5040401940b0120003420311001c040d1029540e031400003032081014001031088400c52120607588807200c0c0b5280c1d0880c1c1050784031309000031003404070000c8154080d00f1181100c202241c0ca080305c80c081c2e0134169880f17003260b00000451007000808003196411856940000000343c003541c4855880c101c0c011302041d02190740000081c010043e481d402c0c0100d05850031000d0b80681002d0030103440c2e01e548110910250820307100c0000c54900c04401c0c4804009800ca803114083d00600001c00681c0c0c8d03032850309a100820b859890020000448441c032030b540001040c00440003141152065102d031800900c0c10420018a900700401d000c0e52074003050003018000c00b54200d4076480c040c83c00320110384210800c12040c5e4103000d12080040d00200400c4600c0308034400180001d59549400e00300103890240741580c08002d24142001c1c0401c5e4202140140c1c03c000c642030459446110000c055548004000803c0d4020700e018 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 543602679 1250 543601429 543601441
    0x905031903051603140402040510030b0a0e0f0f03090402070602160c06020f1501030f020d020604140307051f030b040b1e030c0f15070602040e07050706060b0418021809 74
    0x14000c14050701c052112903c901c5030410303040b419500b0310305803015200c07030880c007040c0103040591141c1d030301101c04d5084402c043d489070f8800d881c0780d50948100b4400d070384540c80c00940707150038409100340540000c0280416070183d42e03601d0b202d004410500348115070214a030700a000c0319404852004003a0240444442c0707040c038042e0b808072054001c20340140306614003a15481700000c0c00003425210044410802da01c1c6079900406414a12030480e0085016050b030230041e01c07101e015102600d926030960000a540f2001d040c074000c2c1136800349203d480b081d0b08035441209181e4070190351101c2c91070042600310030403011034003400c0c8840e41150003103240450640d040741040c400c0310441604506591988030345204108204060505c1182d1221f440e41c100c00d09426184001d0001a22a00c401b600302a607501c0f80c19041e4500300c07080c501066000403541e0401020b881050041c001e10b001030342c200350038102c94040020804202c00d40c01540011101b821720302a50310801c40c20002800700441d0b01d080 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 543603929 1250 543602679 543602681
    0xb1303090e011217181516051005090703031e02011b1d0a03020a21060504032006012603071e020108090303040201020c040f3c1e0905031903 62
    0xd07081541d03200d88240700b10a040c0034040840f03584071030741d00740c0300000c803190705c10007000b0740f400010100051010443d074843d081010070f0380c14455000b00085d2804401c3d00400809640c3c0c01418944242c00146051000070340111050142180c041460f00751441d0b01d403000d87c01800041c1c2500d00c80891020702c002c4090b0301050307084100007000188680000c0358000c1c448500b14034000294054249903042c0b0240749000c2168102001d007906c00002d480c1243c03518000c070741c01580c05400090320000030014040c0c0f0303440000d0300900d01c5002090558900303401614a2a0100001c240303512075072000304880c2c0d6080041d1404103811200c0e0035909050030841406100249004a011508031f90004158200c04070549100c0c1d901a00505030900f0820108001460580e01e600913240d9240200c0016035104c0e0500081c154407041706542e4400412040e01c4094600305222040078204401e180c0714045418140b14000c580b08070200f0a15068500281180103003503400340b0782d40c00851001d5060760702d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 543605179 1250 543603929 543603959
    0xd080304022b0830100b03090c09130f0b0103031e08010e0601110115050108090d140a11160303030e0f0a08030603210301030201090b0406020c12030c010204030305180d0b1303090e01 80
    0x4200a180b40643d95401e9110901040314040400d03008503030500b038103081510516910a5244502d04bc9108040c2e0b18180c41c41603220060781c0c182a140014820540c00038074140302e15140c0d2034521190f0001d0600113083d02014007550180d0581e9101003825039015509001c1c41400c61002405260700c042021803000540d8401c0c50300149a00c40814101030001c02c1039286138080703613107144d0800c1d459003440f52654401e4040d0420080010800f101511003446809035801d28200100312507843c40c00c005003039505681d50200c5035008072081c0c0010f840c0008900700b04603400b8001c07e8980e503645000904048403601225103856048105094501c0000d0007141624802d0b290b40510b03a490f0200400b160166000d0440560b0000d40359030341600d00314a94a811481d98400c0720f00c0c0c081003401c40c50998100d03030300c12400325001007100807001c091502002020b1303c040e1501c0c4c64421680d151030300b086102030242d0140c0a004140c000a051042c40003034003502408007541501d581d50b544035111151 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 543606429 1250 543605179 543605191
    0x2030610080903030c0f040906090c02010506090c04062307030903051002040b040e091e0c130c050412030c05060403350109020c0a020d080304022b0830 67
    0x89000311999918012105180500c00050040d4210b0352440b86440040d48244000c900d1000d0500c400540c0e45640d0090501920b10407401003624000814007a00f91900503001500c42e07a12441006840703100001520110380f07461405204400c00c840d505011085001065035003604001598801d058000e54000c0480707100c0c404841102503004041c3c0203e0155004080c44940c0402c000c226820020000c1900a480041610a8881a2040504072100e204910b0107107410030041040b46142c03000c030412091000c45000d02c41648441030082c0385101701e01424101c409216140014544100011220242c0c000100e0f616410142005002d02c1e0841051052400407905800d0780ca085180c0e01411558013466491501c0e4289501c0720081e40002045850600c1505441c0c000360751850201900c070b030b004004035030740c03424a401032200440841180d9603d203040d04080010800415141c3c040d000d0708484921703121400000c030000d40d0180091190000f1101e121030f24403a500d0b580381540140 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 543607679 1250 543606429 543606439
    0x9060546020f04330e0f0301050f060307060302070b220f1a131122050c071a0403121d0d030b0103150302130c09080f030903010506010306180b04021b01020306 70
    0x40034a0704c610442ca44465654450301c81d01400748002140200c4602609a8000384142045484500400d0131680203c40c414044c48142007403201c01e003001c1c450030001d00107070703e004d5180482c9522000851000a881890002894504528512200004900429446003050f031400009003400c18070007650490170300030700045030085100c08a001d0214411180c0c891207a5002048081c1080340c0850714a5040b0700300000c51016500080300307032181902c9218101c5499469880ca070815484050b1442512200351b95034200f4400400e030400c1c0f105d02070290130040803a21041040340003054450210160020303220b415030703403a600754040e0084040914203030381c10441e0211a10001c1d150300503602c006900070703484405038903c900c0700b90001d490800081c146004115034030202146000001d61a503d401d4002044814040c0b4080c01616000582484c0521085090418050424100f2044660f201d80d8403000c840311510b658040d00c0300790911043c0788802e2a501d000141c080c0d4012140c06100b5 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 543608929 1250 543607679 543607709
    0x70512040b3d170c0907050903010f0e190c0b0d020702090a021b03040518060a1212020f1606030b03100f0209040b060a140d180609060546020f04 64
    0x6070403c10900d024982407100401c040c5141805004c030145000d000d0008001c0104a000030580b024000c0303007100c0e51640300001d10038031f22000e0b050030480d889240075208495107400801147c1c1160101e0190b441903c0134070358403190009070200910031108000c0d0040082010031043c604217501505800c004800403d0581040600d52078803889a03020742036003e42c9005142100d07000c0c40900c0c9903c080007130000d10b00c95440383c0c00401700e40158034003103480380000b04004101560612414503100c4041c00200710980e019010035030203041a001c0c2c5020103944401950460b03030304010840e000c01825000300801640510172402942c40320605034001c13810032611940d542007800858071b900c82da56542e0468150b400060594075480301030580101615022005c0050301e40c1c0c2c41c1c1400003480359500084102080c5040015078100414402032080752491900604422200c0315022940c4c44002d180402003101111071210f034012070b000051880070600e03c4000200c0c1c4010416124004d103101c0e90 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 543610179 1250 543608929 543608939
    0x180105040b010f020d0f0507050a051e01020a09050112140a0507030c0804050703020d0807120c0b0601110601060f030e011d070e070c0828020d08070512040b3d 70
    0x20311040f41010401a4040300d03c0c22441c5120360b8241c0604038052030120301d0102c1c00d85a40d403400440c14001c2c1c0c2c2681000408900741c0180440c40310001020800940c03c140600002501802003881050305000d03114031080940440d80e4006060088509801501c908100c9004001008112030a9010a00d40440c40381c8060003004040d00c101d40c004000d100302e074110b41c24801d17410310140023100c8614052014100184282e20f80103001c1040340c1e180c441031440e03030401111500024041c241170043c9000c00307200c205004904207054a1450401e020407030f043c80c008400804040440e641194030b4140417155490b5016694411017140324201d070303401611048200000d260503590840401c1c0401d18210000c2d11400240c62030b0145d02144486416440315160705050901d018140127070810b0b40c0d0710507184c1c0c0180c41c0c3c2d9000466841d040d4217001c444a4068a104009800600840e10440006880d0300040000c00751a142e03040d810b020700e01c0201d0840401c0d420446814294401c0e031100810 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 543611429 1250 543610179 543610187
    0x2090916090911190803070303050426120c0c1906051e0106030902030a0602042408070c1b0305191109061302030406060308031003060e0a02090601081005180105040b01 74
    0x8099801410720a00c80702004100114820303940211340316801a6000020401814400780c80124000c0e1004540384c581858100c00d145000c22480c10581846600f1200042c1c00708242c0d0b00126229140d02803548480c00a41400c3c040c00d003070503125109900406150440d981d0300203200e584100401c0c401612480450484003415100b684001c075610303030040141502c6034210b620041d00103401e5070b41c071070100c1e26003c060380d00039004004040243d03080c220403002c1002d136a89032120035160004150822080085c03514104060180c05401200d00c600040980c8581c030f20000c50b400402c5501801c03940c0110703406d0b551071140c01d60b0414105a07681a00d0300b085501d0600c901d000a00d128007900140e40c2110081d00040c0003907a0b840e07541d035404400560b0410086000380b81407440105e07041e03e903250000560b44035245910b90354010b540303e100103803280c40020742c100d102402c2404280e96240e00f0781e49004240d910072a4082c4a031620003c11034050418141a2603054500780001149440151 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 543612679 1250 543611429 543611441
    0x914030118020105030703060e07030b012d0c080f070b06120703030f051c090804140f060304020d030c061b110a0b01270f050f070908100b06070209091609 68
    0xd030190700c8100100561080d401140d1100b15420005043c035142d1004544c51903046502c607020039914240c1028540c0c12560a103074901d00380d08800740302c4040c00c0c110700e402e0020764460f106101184403a18200004c0c442901c000b4116223140d076403204e40c02c1c2000d2941602c10b5071114060400400c100c200494082181802d5a402d0703204c140f0010940c20003140e50394880ca6000050342c494040402c0500100d004020744a17001302159916941440c110518503c540f42c170061081e00c55404041454443c0c80c02d4a0780250121082b1980717003098203040d10084c0020341c3c010103007443d020603007594000180c0b4640f060360756551521041000ca0207400e81d01d90030428040c6c01440440d004103d500200c00480d241200e5406121105201017890041500d004441514555444204000f401c200344002c40b5400007462070a03140152805d1b0b200e585402d012000c2d141d0680e104c1c40b90002640b19a0200c4200c0d91740542000914502564083d841d2850320100d40040b9810100004070030500e030040c5 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 543613929 1250 543612679 543612701
    0x110a030503040501051c050411040e012c070e1e15130902031f0e0f07050109090e1509030702030c0906030312040f05010c051803010c0c0605040f0c0609140301 70
    0x942c50242842c0c010b544981007526000e034110041c005265885550f0b0048901441c41407030001142034034002000140c031001e0b036800100c3c0e032400d440720310811403142d041e084402221484a41d44405100042c1c14941d00340c0121100a031442c06114280300a0a12080f016510110b0444a48c4034181c1c0034560746482e451099000c400300ca0150000ca549a0100240e18802011102c902c4c02400407401a030b0311000300d404000d43c0d101c40d0145c0303030132060001c0c00c196071f0010045c000d40ea042600180c80503560340618951075584181390704007081c0c1040214140c8803142c092200c0d91500305c4d40380741d0700da1220404134082d00440d60078180c103040019001c0e0141c03100a02035402d2560840d888402c00500500030f03a0100a54540c00010920a20550001200701d5540340c3e5601e810003440307106400c0600d039481c02070703150801e80100a5800700c034429440703500002c0800e4585450034410145680d9490150014103150000600c0a400411034011a28205010032512005000b01400c80300001c0340b03 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 543615179 1250 543613929 543613933
    0xc100c0807030209030c1c052401031401021c290f0d0804051306030b01060c1a090c150c07060306050d0206030712020d1406060304030225030519110a0305 68
    0x1c110340c540a5005015036502c00380031140165039500002e101000ba440d00d8907500004e00c130b442024000c0c2400500c0300c0181103800c4400c50850005040240c010500c0061b10030300d03103444441c60602c401c4d01122030281c4205030030700540340a4009400281003c0040503814407194010540b203003a01442c0038020310000b450088900a10022300061102e02d031011144580d041002103502e41d12099050b803213450503000024010708500d480948c800041e0070034018810040100c3e00010010192041d4a00743c1981d50211900e420200f14604080e001644c1d41c0100d00e002444403203007800c5d01825110f446d0b44200c481050703540b0020f8003220014059241c006007a0703e5054094204807009540007011440c28420704807420700400201e03000b500c1c540b9004c1c0d444035144520380e00e800300c4054000d002140d0b030714a1801c1699001c2d58039048c01140c10141e002e440401e40c2c07036038543e048150003150440706070340c030888400d03c1c00c40f03038188070034001c5070b440d0502d0300c6620b00b0f07042024000050f6644180 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 543616429 1250 543615179 543615181
    0x5091201151e03080d06030c0812030a0207020109050d031e0507021c0201050f0310090c08190e030912031e09010801060513090e01020a021218010809030706110c100c08 74
    0x445050a485618050514103042d420003c001828100180705848112400181190a502d030400804001e03510001d195484440f03411141c0c0190012030f0382010840d6001692840140700503240b00089501c020380c0040b5203035803138080c5074001d2042d1030b4a0f407501e00151100307081040151450b00881c1c2010350480e0003c002500c503044406010b60656005040103800c00513100601844c030360048810510514104101300300d0394030607010b03e00d21007074039007458002c070b241521840401e406014458070503261502110300300c01c08140100c4903042c10180c101030582da0381c101c60b01e03625400008042c00c030b080807072003030000d0034010f40a448454005a5035002c0c5646400c9003100d07160070a090500d110541c0d1440000d01c1c1043c0c0c89000b6105003035a00142c4c4810340c804004c0e0410601110100d1003880030403040c00076038114041d0030704043c004d0030700201540f50222018651300404c0002401285400d418544e103162007409410002145412510798650305070316042900c0300000481b0100b0304c120 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 543617679 1250 543616429 543616439
    0x20604050f0d05070b040c05040203010b1801021f1a031b0a0803030f041b1805040204150503060115051201121b060e040b0f041406041503020f010c0219060509120115 73
    0xb038401768000303000e41903d2425944400008040380c0c001e1f40300c44007010380010781e0600d0341a4a410411403c10900180c110120052150484c41d441174010440266550010415640c1684c291444d42d160280c100e900003400052100c3c482c0400f040310b103200e00c2d419a03002031000320020440780304041c00c19000c01c0645036a036030031448a6181e561744000900d1000003041c80a0a00c2d034018500121060219031410140144000c460185400505031210400c06114503100041e140c1d04403001d130045800701e05005181141c1a000c0c81403000b610400d44c0b000041d00d030b04100941f000941c001d5a15044400c0c0903d41040102034500c1640c0105108040e140039615040d803042d402913102400d142401d148175030001c0e0407aa01c212807981120b9000090210324207051146010344d404400080085904540003d00d00c1202c0305c0d0158100140100101e045481d00c0303040050724061b940d5810103898441c00e001c0c1c00ea8018500450007284042c0c0c2c48a5803050500403500301d21580c90041030050300340 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 543618929 1250 543617679 543617693
    0xc24150f092a0c151407020102030402010e060c0c0613090c0513062d0201050f090f03120601030615111006030f0b18030a08010801140106021b031c020604050f0d0507 73
    0x382c0b041c80c080c0141601110b0104448003425980c40e2401e01001a000e01c103580c400c00041c0024202da021a03106000b00300060340c01000180c5d8507102150f42d1515443da2f091031501d8113901260b4150000b0300410030190300c6051400403800d413003026409005003401544201c0d0300b0700070005490b004a0400d0400c1160034000c020406071652100000e289032050003c2e603a0440c0303054050000140e42d244104841f64040c103800c0c541101e4800040c0204020b5031b005a9603900500310302c0c2251300e603460042260303130b030290780081d0041a48000d40510a03030406409400501d1780140084039015004031440d40c008548600b6081d45d6001c0400302d000169034a80303191201004060444540e0365080c503c440400030030203040ca580b01555610301070b6041a06880c2942c3e083c2d40e200092105100043c05116004202500d54203031088400780a0000b900009103090401c01042480d840d40d5020450b829a000c1000e920645c0a0001c84500000c001c0c5c0340340c1c0d1590600344610000da401c3c0301d1900040e0340 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 543620179 1250 543618929 543619001
    0xb090a0905011103071806020f0318040e1516170f0403020c030105150a080d05090907030b132307120c1205070503250c24150f09 57
    0x100000a0300250a0310f21880700d5106855100c00b0510034200340d00c40e555484103490103019944050704154a002d106d140d520b0194140c06903070b9250080748008070b901c40340e001507114010041166003400240c089954101c2e0150381c1c501103640d41504400c8103c0c09070012030301100d40900c40865980e164008480144000b910450460050003c800c8272503a003402110300030030b0401140d1407954840003c02514160540c02035290341c014985601100f81c20100751440000c0545000120369210017084004010001c052540640c0c452280c000008203584004c0b07161100d01d031241642007107007940c459403450480b42d9500150070401440d12072011074002c2c0018101034207101c284845003810240503158100e90907000240040200b000200303030b0040459a01c088031755004071100500c20021310f040b5803080d028041240300e1403144a01d00f0f200c801100901c04c40482000166042070310094400640e124000c1c02d141c0000c0c02046064140c411500c000340260781c040088200c03100c4002d85108 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 543621429 1250 543620179 543620183
    0x9140d030e030a021806010917031614100b0a05011e21050112050610140d020a0b0d150b120109110c060a0f06060905090a0504050c04020711130b090a09 67
    0x98280f0540060303c40381200c00050303200c001e81108500c0e0120005007003c10503801084074180b00d21580250440210454860f441c0c00064800c1d4141282041c1c0282c00d84011104a903101b800c01002c100442c0c1d42c07003004110002c48062142e43c0d03980300111440c804101e11003100303d0600351018004c500608414800495030078140000c4003124514400302d5101740e01c446030513280c00c0b00040410900340b00495200c01c1c50310100a54a04124803419a8450075000c0c0d80600341d4054a001550368149100004001ca00b4503980d07608007a9280c003024003008c10414540d0100c592020882c0141da4095600403a001c40301080543c6c40c3c0102800030b04241c040403403030850100503400c03840c1e4040c451140315900703c01c1d02103078103c840f401c200102c620780c2c1d001c10108003401c0c4040c0000e42e9104000d9800c0000503001144541701c0381020350419520300705003a4003074070004174032013044208402c0e06658042100c4001e100c1103078200041c02d44000980269202036440c3c0022803205190380440c618078 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 543622679 1250 543621429 543621433
    0x300f03140c030f07231305090907060507022e0f0f0203120c04120302060411040c050316020f1b091501270306060f05090703090201020c1c0503030703020a09140d030e03 74
    0xaa00c02100a80c42d11181003180c5c03010b40011410340314426404050000e110680c1c1c4041c891401c2c09505480301c110b1302910041110000b419819035585050481c00d10749000c200c4000b800d14034051080c558402c0d000348022075a003842c01c0071000c3c00b44000c03260003107880d000380d807810381400e001814146008090580ca188148400b080351000c045034014114401c3e0000e01c42418241003001200f80c18101041c440c504180c0e0b0780c074507240d01070281e03a01700115801001100c04085800d13800e005119038104000e1241c00c2455000040004030360141540076030700b0300c580b92581c04030301c40c2d1200b0780344c54280801c0200c030000300300000e590703014007449510344880700d082c82d140e44d42d500c00d0701e406902c94601c01c0400001404185030110b40740d07800c58400e08040112851b140e00203900c1e04100c0c611248600f8500c0c203c0e031049841002034903501c2e1361041c00c0d00d039030389440c200140007904280c0c0ca44000407801600481c00d020790030340b40319189134020f0034811002c22a507011034244400c403a02c15058 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 543623929 1250 543622679 543622697
    0x309110d0c0801020a0f0801080102190c0201030914100b120d050906040f1202040e0a1a0912030c0c070501180b0714030a02010b01030e0a02010c300f03140c030f07 72
    0x30b1000e1000d0540c1e9207050740d0342042142c1c50400200b49005c107070040c009507441003241e640180200320800703440c040c1c6810140d04400d0340f40010782c001d01c40410080c000c41401c05102d00280800300d00e115007040003407000c106841c40789060001c2ca2030240c680300281d51245190903d80c6d400391003c2c0c14840c00080000d440c143d11501400d02448244d07106610b0206c08280e02d00861a19008019001142d080100380b442d0031611400d68070904c001d48a5000414100412400c0c007050100a030040c0c0762641507607803400e100704004000c0d0312403440e0386280e018150f07000c1000d41c403400702030314032000c4140084c00080c241040303501550301c030350300403140f1760514003004032806d80620140c0341c070303c40940000607401c141d54005001d540a4181d030355a10340000000200503a0440920340c00290001004820015122800d045603080d000018039141d002405402c1100d03030000452030b0301c00c401e54003807001071107490340c5918008041c0e520501c0700c801800001d03105116994581d900030a9440d0900790 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 543625179 1250 543623929 543623939
    0x90609130b060a02060919030f0e030111070803100e0906010e070504050d050606010f0201050121141f060f03020132031003110f03030702010c03051309020a0e010309110d0c 76
    0x603070350041443d0009604101c0c10820014810310154156a400d03262410149640340da00804d03140384140448148181480b01400c5a10b0951104003080c1241d2005030f0b84507040d050444541e0012241e500324101920700100e126040880d00601620966004010503403c2007590b4411110003000d003410000c05120010705a66103c00b01c240f0300c0d00980203230840c0d050000c00181400c21008182e4196030618004011100b60000a5198007400c6c00c82c1807951105031902400a14a5101814682c460401042041c40c040c41d032001c24980e8190307041001c195100c0381081c1105032480041d000c03410342040c0b07130501e00310482c0750700c00500e4504403040521078402108035076800c02e582d0701c06a041c10b05002d008100c940d1041048a2104030f80c25074000c80144002070340ea10520070001c1c100003800303c0030010180640b0680345020668183e1310003041d01d0311020f10003500a155480c000822400c0601a994040e00c41d004420f600804100512a845002e10513040b81250f01212070603040c0c0c0300052 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 543626429 1250 543625179 543625189
    0x705030409060602063402100e06090d0206010803040608180703060519180212100204060c03031a010e30030c0708070b180105041203180902090609130b 67
    0x2001c0c060a00c800110203040881c000d20340b50b0028003001503032540942d88140211030041b01c0c1841c0c000c400f44000c0a200c03142d4100e080140422001c4a410b04148010360020300c08103005107c0c0da240c00845500641c0741e102240c0d5100700f0700c83e04006400403c82480b8884c464001240e10200185100b041d425450311024075040c2d642d841541c817079566000744610050b00a0110191142c0c20500b0321082010100e089511404241e000303100b181c810b8444040e09006201e11414012124001c544540d55030b07002500906000340c0c11400203160003125201444415400d0800603410b039600c1072901140c2c0144824203560340343c4c40c84c00d5040304080c0085208000884000c2d00c1901c0003668961070700c403030894070780041074014003025084804280400d21201d4240c6400d65454210482c00c0c00a1100503031790b9208a4108105586400440314245a003203090869043d9070340030040c0000395a10360702412030041c0002c0e40c0d0711440c2000008094078142c43c8610441d8201b400005003100744a001403 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 543627679 1250 543626429 543626437
    0x7020d080d0504060b100e09090703020d150609051312020705041802030d111b1c03020a05070e060a03060519140a05091c081008070902090a05030309090c0d02070503 73
    0x10aa072500c2c0c008110410103203004814400d10155032007078642c0c5000c1c0002e4a44d01c4410b1009000c0c955540000710140b808001e4a0000c42d00600349600c0c105550074808149542c0b020050300703540c00c1c003c0004600d01c0a209040c440d02c0e100101c050030750310540d01e041d00103040080382d1085110700c48000c2031903034907840740952070043c0c8030454200018134410301d41041140c0644030309200150100e0240018017203008071840b0b158844208002090000081ca03c1c2c2446952000000c03560340c01ea420142c0024401c00e51a006500f2940503a0741e0700a040c2014004881e81130f0001540036041002a03040c0d0000c1d900f00c01c1510044407011250088202100c00283c00c0c100701c9207400042c01403850051103041d030442c00607000751240c07a01407210304480ca0b070180340e40300800c0300742800a600300c040402c1c0c000c0a400c8003002d498455940d5548a000794002703656091181d600b8040c0012030345800030440346c1030000541414455520f011052101d40c00c407002c96403260b5000c01c88100060010700c024 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 543628929 1250 543627679 543627697
    0x1416080301060c050c0d020904080d060f030b0f15030705060d0608102003040b012c0f070306050f090a112203150b180c0f0414010f05180607020d08 65
    0x4120080d1941022440c0a229462542c002c0c2078090303007000503032140408230390b0060b0030010165840030700c11402c50040030707607510000c072926409801008100400c3e01c05402200080504041912450000c491034a614518168183d000030400c00c007600303259000d44540c0c0c40a290000340750f41d94500560411008410b5100b815503284104007051028144103044840c12000643c00c51a0603075504206a1040c0900401c0f524070041101403440000d81c180c108001442ca6020203003080d2800800ea503c0544600001c64104640850039080803c0646000e00c8014040c03180d03903da1560900c0208a40c003a030143c80b007010800103100030390304400401500e03134400c240c4c0401c038990b0501150000e4600d0300f10141c641003010020f85035680f1254240e01e007003100c0680c001a22044c400000e03e21511f40b00c100154004200010322821420350f40c1000c59080c0c823801d8034401181011543c1e449030130420344601c144284040064100640a030647c98409410407000080c151141c94042d0445646 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 543630179 1250 543628929 543628937
    0x91005040c170f06040f06090203031602130216060b120316170a050d0c12060902030114010e090a110409050c0316090614030a1b050301060f0e01141608030106 70
    0x20009420441c00d501d10310700000c40940301200f12020034644508001e08003402d1104a0249401030104a80c04400210790040403a42d80d41061040510788040c4044c09901c0307941c20782900001641c0a00071112081c40c04241e0140702c0940381d460342d0003400c000c840c85810040312103100d03440c001c00308014000c446168011640340d400d203203004104035000016145819805004840005401000340c40200a0402c2c0105051403900000c407000030f82000703445086820144001a0502c59900450590340071081d05544100b0080040d99810016001140c0040c1c0d4100054a0014241d105c079481c80050030882e440c2c1540e0740c4c1924240c030400d039400500d61000100303200c0780010010b54900450280e041a100c0d1600d0700a000d00340c0b0344c11a40a802400d000400251200c060343d100158000c0000002400140020001482900240180070100d10407810100060340a0940c2800c455030580d5080d400c1000000c40d400c050308500ca04082c003c24034201680011180d1005d940606681d43d1 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 543631429 1250 543630179 543630203
    0x7020d05150108010603080901030c1101050c220f180204090c030605010e0d0206041809050f030703260a0f0209030601061d060304080412050a060203010e070806120c010809100504 79
    0x114071501e88206070300200f0a40c2c54001d003000011804801d8800041090a00041911283d142609d81c4158906500708030b5190004000925080704003402114000340d02116548000040c20103040400c1e000c1d42801500b40c3d1010803041d00440d000241400c0c0c0120054205590303000108151604000703110302103a03c0d001c2c00d20031940d105480c0626440c003210100180c0303100b500802c1c41403085018210130580c0c03803840468600b040384c11180c130560340103040769080c15041055545a41048a00300c001440841401c00a83d509807004440490030f54035010b9103481d0300040a004021950090001a4082c0817080181e80c1c24003c050082c141034949019003030514000b04100d014264019101320b40600602000c030740e580c01a50709a5503400400b43c074009247c102075150896080c002441e0a00003c000301d501c0d0380b0070440c14020b10301c81e1600d2085880f0142004205821000b294007240c4c403003c10000250f1054060941200850060300d5002c884401d0104c01d0700d0080710309031851042c5203 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 543632679 1250 543631429 543631453
    0x20c240114010305070e280b180105250f080c01050601081e011202190603140a020f07060f0b04022d2104062a0f020304050112090807020d05 62
    0x12004850402007443d0401c55450310f0b8601400c00c03011070480c140101401d400e007540e100c110819102c2180d408941141c041c82c0e881000c00a150b00400c11084400317000c81c070280c4107500032415a000703804004e65a4080711482041c034241082d41d00f400340c2e074800e24410140c01081041004108070345213000089407a1805c000050312101003e49560002d519004a0614480512954034151111054080340b0b10131107000013260581d40c100081603006c0040b070005032898140d4083e0512500d040b01c9481c295035048185070403809100f1449860304410804400083c0340303036220319104180410006030300300d100d101240480e0000103204410120307e000413402800c24181d12211114606015031801c07902d080403100490300bc04a40303508445030404079080100070307085030740340300c40100008807924034000243c00440780344400e030310100d580e044d48000ca0310710200490702aa0810303182c3c13117880140301501d8002000100000c0d20301040901c50240103039560051013503424082c030020452030040b5 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 543633929 1250 543632679 543632699
    0x702030409050718142107050301051008010b0a05011d0111070603020406030b0f1005070f020303070b0411030f030910092c0a06030f08030c070b09031b12030a020c2401 74
    0x41e01316600d1170320b603006140e085030346100c89074030110f1045906510100307482c840c90346803666039001241c0c19400c16040009a091940c0c50390101e0388020004c2c4450030140303091001900050003198002002c03c500c201c8101c0300300400320940c0d4010b250001c180e0504a60b00c0f130030850740d0740140d030002e034000504015880d81402075002c540f004640007402602d4400000315a032040340b508030140003021039501c040c044000e24402500d034000e415680c0d91074682c5401001d240040b9400c444682c005615013299080000d82141c40c413081c2d800035441c201c945002c00840507040d504003001c00c4000507020660040c080b01a81c01408800d0030903410b01c440c0c4101070612100141960303e098540071040000c2000c05040d1215103400032140355684d00c1e42d0000c14840d1003103c0018002c1641c0509011088000100915055015900c1c03170080c011104001919840100100405610284041221000f569005140c104a41002c440c0c0d80e0751443c030500815214002c081c0100c0049000420500e944 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 543635179 1250 543633929 543633977
    0x30e0a03120f02010b06071704030f050106050111162612040e070c1212110c07080d02011514061e0703030f1806090203011508060915160807020304090507 68
    0xb50780000c5c4003c48903100400d80758001c9840280400d1001480c4016000420003107801440d00410a002d8902403401c0c00c5020b00010704c949800104098110039281c4004590440e29803102d58a100040740340807428172920b00c892901040c25004240381c40049001005600030701ca00078414151164a8551000c1840d44000c1110080c000415109030000c1c0721420008500310b100c1c00d01002d040203d08007480200300a882001d100580011a440c074000c1c0001c1e004d044078901400c84148610701042242030300c29140d1000a100041203043c005005100041080d2070030191201d820021618002c0103030255909114214075000101c000a065140c01707481c0d0150145030b030600602c4042040c2203043c120005000d403032260f5426200c0e0841d5400c0d04143c004103c0303102001102038036101819100c0c0801d44002401384510031003501d006010386041c612905907010760005080600c44203a07411400117100d0401c50008000103e0b11159610070a40180000d6403071444480216013030301441c00c4 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 543636429 1250 543635179 543635207
    0xa0c020304050d061107060e0102090a170d031a0315040c06050a050d02092806200601050904110919050714030105060703110d081b0a050313030e0a0312 67
    0x1007004144510b807104644060401d07400300c0006100100102d083d502c0d8000c2020040000d410001401c1c0301803015006010740100807541e440c101651144940160b0001050010f26600a07200072400315000b030f44100680d2040b00700780b00c0c1c004501c4002a0a141500020b00b6025400d0820301061010302e5a040c0050552800c00c0c500d03042940030054240c0c0522440340380c0498000900e1340d1180c590640014004910064420004529036035004583c0000c2c0942d80c005090501404c0100303a0310000f0080101c0880045c00c00b903402c042c103000700c0c1c060040c015200825485009159901c41300303821031003950000c0c0c02900510384900c06400b83c403009070021040100400f1b4500c000c94001c411a411110201c4e8003e540300345620f001d58440301004015603d0703016070742c13903035803040e4001c1c1c00c143c414040c03202e20803441904614003003040d00a06040d14000b982c148005401c40703900f0ba150030f4000d406400c0103804007040c0c10000340040e00a0300200d408020f80440040c0e101d03040340030411005 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 543637679 1250 543636429 543636433
    0xf110313080106030b09060717131b090b0118060c14070821090a063b240a03050a0e1f0e07030506061915022506080f0c210a0c02 57
    0x230510000c010003d0750f5900c0b07086040c180c4c0740f01141c491000000070450b16903104002c1c4c0c0e4560748107a034a801c480914482c0041c844d091140b0b0100c81d600c6038a00c0c4203001d4a0854a8903101d040c0f035401c80300d03208400c40c11138400f00041d9003000a80000c11101c0010a0518020f08180070b00d0744040b21800d031010a000403c030018883c880d81b40d41c0e031400e0082540d8003460303d01020311401c00c00076100d44080b00c06508d0240903842078882c66510700505004100252946c1081310740700e580d1820203c00050210342a40024043c20085510a41002da000014407001140b4000285003241c00d10445214a07400854400031311582050b10f8001d4454200000d0040c05a16143d80c4403681c403202c004143c0742c0b06131006200031486d002900c00100241c5810b01c4801d20000c4201030207565030342c0903a551011a051921110f6403201114401000c0e500c0b40e039642701c00c2d511400c09003513504501a0100401c03900500100d5000b00f407015942120030703488645048a41450040340c401c5032100c154840445d = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 543638929 1250 543637679 543637681
    0x9090902030c150906070b040209010f080d05070f2406051e01030207260a1112090f0307050907030204170106030b04021207050924030705010f110313080106030b0906 73
    0x581c0d00031038980940c0c48141d841035011203001c0c405a62038030450758001c1e070201c00404d0791010f010b1003208042c800e520070b41340340440d80d88031a00d81d40ea9005521404506078400300e02d0201c440d00c134801030083e2510030005501d402019589080340900c182130a01600340d809644c003a00381c09140907c0d401000c0030384181180050181340301003114010a4214141900015460200720b19024649402206002104d400600001c183c0c04198001c80d410400100c445106d0048001c6c081003608080501000a03490100d0310780a0008a45110303c120f47e05020f0041d00003030304e072210700b0a544035040c2980c0060b500d030b0501545840c5022084040016030b0b14120007070000620500060b9006a0105c41c140c40145907914040d1900e011900000c3d08101c520b01842350525041e26514251640d507005030424144100c01c0c180da48089208203400030300c0d0206601c0310315005003244840507041e0340aa07460a00341f00c04c6003030f043c0b4256000003841ea5460a04009108162142c5038002d1042c0000e425a = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 543640179 1250 543638929 543638933
    0xa0516020607031e060e010501200d0e01051c0c110a020603061c0c0801020d0605240f040905040521030c03061c060903020d1121030a060b0409020406090909 69
    0x3440d840104400b007815960354001007501501c1035901001060700005010031600d90182c2c0c00c0b08002886440e001c0b885903921031029020000003605130b0855030000340041109008220341181410b52540e041c058200b18525a00c88104034120722300c040c03181c0200d280c40440900600f0710011000c020074940002e100d880040c0c3e601070882c2c0d00440c080b00c0301c01d80000e0344145076200c1000b001e402010000ea42c1c1c800036051006401070300c0000590601000017030f039200c0500482c41280403944080d14815180130704940e00c0100545005000b0800c03180c105030300d84004208a440c140c03001d0300d00f03910a030019a080c690a01c803112901d0038000c01c060441c1800e00455201380005010107100f951070042410b0150000304030403403070580181040c8210850f904001e902e8440c6012460000b584841c20031218500000f100c000858510301420721001c5030100c09006074001411400c0b9550700c84900047c50710b612000780011f45540313900180d48502e4044003502c200103550055407220b04002c02000 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 543641429 1250 543640179 543640183
    0x30a170603030c06010e0405010b0303030a060603110a050a030c03180b10091b030b1f120605010207080c04020702030c0d05072d12031202040909030e0301052205070504050c030a051602 81
    0x81191b14040000f0b031070f9180c0e45400c90240c421803c2c3c80d40c1610010040198200041d0000012200d454804115056400741c210b201413081ca002e81011410410492901911990160040021610b0005a5840180d015501074600b0600c00c1d10016800000d11014002c490510002003c03584820001c60140c4c110741c410100301c4000e5a4141641c594101d6160340703074814240200031207050032110415840202030450308005280951051a1150215185d400010307000180c464400050290003e810f02300006941b10340001c0307800d0702a680d103603106034a881c1200c2e043c4500c520050302c842c03406c1003000030160f0103040c00501c2c83c034032044c810b011406c01d404c084015030380c200c000c8400d0291141000c0c0c1c1e03403034410903460390b65610000d80042c0c40122070b4051000d0902c1703075850849400c107180405081e00c01c199081c02e5046d41e10500350300c21150701c042c83c2228a00c00d90a90341c240c0c1e600d5000408503102103440d415220340000130050491794070300c41c0d2a84118007c2c40c004140b410008025 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 543642679 1250 543641429 543641431
    0x2d011b0302122101090204031416210501060e07080708060d020409030e090a020d060503070f15170f0109060b030403020a061a040218030c09040f0f0212030a170603030c06 75
    0x4042c603000041c1e14650f40d1420320100d0041411210907a42559641d00100020b60080c4000c0c1d5450500070848031840e04042601030079402400104108142099081d82588a00c1e40075007a20840940100000a400303016200051080303007218401031810000c060805c5074014005d00c10800d4007002c01920f0b03590304004160907901941c0020b0304d08540d28080c4c030f4140911040e00ea00031810303400c1121603841034000f840e00d82000364052000a42d17990901d683d540940c0544022040081818809604222071813681f4095078a8904210000805910380d801c0c4140c3e28420224880c1300184112940c43c01130030018000d80a100740385140545009464842d807040040c106510f80076400384140b03045021529031400148111740d100fa03001e2059001c134402c404401e01900800680003a185800442648079035006140c40b141c0c00702a5840c0d0341d00d414480001c9a0200800c0300c071800d41d940820142140c881591203101605104030240c3c14402002045c00d4030907401000070440034000800c01c2 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 543643929 1250 543642679 543642703
    0x180801061404110a0f05181e030d05040605030406020f0403021903050706110d03410604110d020309030403060905010b090c0c0a060513050607120c090303050304112d011b0302 77
    0x2440c0c43d4441f119050401e403c80465065000a401c1e510140c04001c103420031505079811000c03200c1041c031210045e0b800d030180d8820303003001c504207000182c0400e111b900100744201c40403040c0707841c1030345135800182e5041c150304486111076140c076400d00801c03004002d002e01618680c00e050b4412a600e840d80c0340e0317884407480316008040c0c507502a10a00302160100040700001c48041e5904040b0040400c88801d59030440107609925a602040d07031800d0600c1655201000400c40c2031401c0d4045008201030b602c040c3c280b4032140300070400000802d0543c45142000c0d4810700004c00c0d1142884200010002e0182038151500c0d03040000026480700010060780c45a440300001c00c03142d80b8007015441c4c5240300a406400c90040307904100001c0c0d8002d0382e44211010341c5a04000340c1c141c484003256051001e0200401041e010004100421040c0b540385c5030042c0d000300203464100c584e480212a054805034a45440010703500c11403801d43c1c010340c010768400c5502266002010441c1c40c029075468000c080 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 543645179 1250 543643929 543643937
    0x7081815011811030a02090301060f15050a140a0914042703121103010f0b070203070314010b10031a010806130c14030907051206070f180801061404110a0f 68
    0x1d04a00000e05400c070782e81d0426441d250544030b24000c24144003079803000003148d22a520300003010030300341d649101c510142e4031488d0a100b921002d0850548040e0301c008421020300c008000034444140714180102003620700c0b03903030300280c05140503103841e080e080031140300d4412400c0c10900707405e94400324041e0301920281d40c80b100b0340781c0240c1029240c000e0720320100d0302072501700480203d20300407010045040307e440018241020350340b21109501030240c607030b00a5254015205c1040415a035011400b00c0140f004000121002000c001030400c0d110b040450020039101e0340a030500642c50710504204510170f0034088071a191100002e4805022002203030a21503540c41c9141d80d1600c41e0b1101c0448101c441b40440d528141030002d555035041038800e10340b1826480c10304840b90103000c1940e41c020103041c0c0350000c0302c400405040c0d420b00c4a02011501d4010310783c2000548003400d000f580014641326405020203000c030801d01058844810303c00c141c0000800601c08101d42c004401c001560700ba1030 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 543646429 1250 543645179 543645209
    0x91109030c10033b0a0506130c15020d092c0403140301030516060309020d03030c120911190503030706020f07140d030c0914090402040906050708181501 67
    0x103060b4018200d41303074224004a0f41e6003010760242c0504600e0201002c0c200c0c00c0f06014500e0130666942c8604500c0024815049040840d00049000c0a55541d0521810f18690f6107516036085010080403d000309d0016400b000f0074107040c54006070650041c0442c4020200fa000c03410290b40c01c018660448100145205400181403502c108001402c07400b032660015941d50350703400d155641d0102d41c030300e5001000c56000d000441c00d01178441c4c0680e0710b9010303044032000c0001e52000d40c0101a090944801c0c400041e02040d0355800034440c6004d0035210300c01c3d40e445141c0000a0101041400d8035065002c01c040600707014507900001038540c41d542c005c43c0075070f50b01c0e80b00d0380d80c0000d4003902800030060042e010140885140204804404001607030b01005101180401103c000040703205068004249903010746641c248030801d10343c003a0000c3c0c00130032007540a555500880b00101c82c1030b0001222801403082c08205844030703488250304500105540c0050581042e40110180300ea611458083c079 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 543647679 1250 543646429 543646459
    0x6050114064f090c1205070918090b06271302100f020606040b060306010e0d0b070c03090602070807060c021206040b011a0304050d050c03040f03030504091109030c 72
    0x6540040c006460240588401c450700c0350b024590007a410710070b29000001500410100001e2056080386043e6a5a407444006900c0e4280300400d0050010010800445004503150803081d904601c0c0c8a8419400180702c4600e0401c0324504002030506403240c00791500100e080542503880d02d000c00b41541ca8000384c0c0c2c03610040011201390a0000170b40201240100c22040c6401c082d0740d2071a044141c003078610f1a52030b43d0800c011100010402e40c0c0c000c0d02480450010351040315007509083c00030b010b18001d1505912151198041203e040000460b400450000c0660100701c0100402035070000304052800c060302d030f036119411070040e031080203039110070902950f40304914100c44400370b50545466050500701944010f000b4081c01d059003075019a01010055058122442142c00c24060015208a072001b120705901c02e88000b01144803c0c00042001180180c555004502c640c6407540d80394a1301c0f801030f054030004210010407880038030205c2c2880d1000320f051041c80208a5407192418284c0d = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 543648929 1250 543647679 543647737
    0x2103060f010903050a1a07080402030721020d050d030606080910110708030708010509070e0a03060b060c1209040516020a030e131410121a1b070b040605011406 70
    0x9980701031300a1107543d90003000e101c620318a601daa40450100d11031302c1da49800007914280800d0744d0094040d03200410411511100303810f2204509a00740b0707500c0e811440c6400282c6640701c0c08106a450341c101150070700d122074040c850a4020300c12400c0c0380c0b8861400c040c5070354403004e07410300d5540c0f002d07210300060350718607585000c64130459405856517403603041481c40100151800d010340e40c0034043c0c00001c50740c80d9004444c0a0042e060003001240741030304580d5068060401514040c0d0000300074021040c1c00b050610450340c1c0a4501d40416440e403850b9010001a544060701e41d4000f040303120340b141c10480c0d0228010070380030781600f00b01e0382e0758039003902045510620507000401d161a00e018407000440c00e944181c000c00f0709401c1190580d4541501498442d18410010148186034450b00c24000b030014655a02011540c0840103900366030494201c0b542c0144021169078240504000404c1030b94481c0e1400340811048400c14136002c4004105c0707510851040c0c40908000d121100901424 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 543650179 1250 543648929 543648947
    0x5060d15020325020115060813032a0f06060515070605070c0c060c02130c020729030f180c100c05010b040e07170c21010e16082103060f01 61
    0x18901c9443c207000c00184002e000344115024404002c07150800050a50712034640a0301030284900c048041200b1171f5002d852206210b640490340404840800e01c0921b858806034035002d01654031030559640b03500e400c0c012124950001c9115001590709030080364180c1d010740d01c12039170100000620317840d081c0b001c0c2d13250381c000800206844c280e80c2c07004c5121a4070803001030300c1c01c2c800e6681e0404444e07082a0315007980d000d074070200010307805640d0400046482640c4500c3c00c00d0900d4880c030364643e89801c404021752040381c14510901902d014000300040007400c8039030008812011780030b600e10791030010310484c400b04203003010000c2007070484081c00401c0d80010a2044018010061020000700300750b02d4242d1880381418110116083e07940c41d03800450b007803169600003001c048944074840b8600e8107044980c0c501c1c580d199600c000302144c0d040200f06556583c0c3c220140105c8440c9490740151808110b0030f14448130b80ea0300c0350700c101c4030010344082d2034000e00102c504003a10081440101c0d40069 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 543651429 1250 543650179 543650221
    0x5010806030a024c20120901080c1201061404080610030209100608040201080c1b010504060c1107170f0d0c020a06110312070203090307061205060d150203 68
    0x320007900a040d40d43c80c000079504410442d0883d5082c110203260121340c5040120401c0d50814614014404548034410860a020792041d00e01d40545840e150310f454403545261a00300803800041c91030556803c0f42e00e00d54454504070300702d0300c1c0c03118000028414000c188914824084150400c04d00112200c090758040d040f444111980c600d030001c0648030304282480164068186400412482c8c60192442d00549046031199080754031280d00450701050300900890002c03509202c441d0300b0411146031a00b03500c6240300081036034182400c00d00c0071513242c1e0b0360240c18003110341c140d01d2441d640840c144046940d82c0f00c10007103594444440500f8a250304400d0000c60180c0038100c48035540002403d403845001351036407510503440d0041070341c168150b0030906416074428803610480d000d540411960114141c4103981c00c1078407000200b46030440540101d80483d04003500708c5055446881203e50016017180c0c0c83c004401e480e1078456070103444500041d8119000400118450007002910079501 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 543652679 1250 543651429 543651439
    0x7121b02031e010608030c151e0403120906020a03050702060108011e05090f03040303170609060d06090501060e0106020a20060306010f0c080a210b01021207060b030303100609080703050705010806030a02 89
    0x10490300c6042d41c5582d403101e0b41e4448c2001403004125019103010140003103550326444180f59850b01d031002e403080c0c00030f40c0401d00095110300c41200001c03c240090541c0400b951004100b5090100c40a400c100e0160003071840390385081d2540c1c0030f60942c0303031108640d196111000201501c03014841414000c4c0250b80714882d10001500004040d880280c0100600d840d04c840a1240c48031004c0054401064410070790045410f02214042155644000003980c414800014060341e200e03111000782c41c003644058050303004040003400707015140315000e0351801d002d1000c0c001070700e0b0a400140c140c0806801c2a041282003a09004150301550304016403034bc1112803652181c00c001e800405003e010a407192500c4a00720456100c040280200f68913801c0580242403240c609040701d11140c1c01c40301e0241c03000d079119900326200741c07070900055002e20b2076034120306d8200c2d0070058041e0004c0002c0d80014190703400040d080011840208031481030311400d180245454580c84c000030300e844203403540130b9484 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 543653929 1250 543652679 543652687
    0x32702060d0606092603040b090409050601141806031507170a020304110303091302090402040e010915050909070e07090e090a021f051c020c0307121b02031e01060803 73
    0x141d08a0205821140050401411481200c0d03440307400d517010780c40510590784180418421030540f80054119080c002e0b00010742600191a86413500304282c0c442e4103800c542c43c1c0c6255080c1040c440d030509140103521408080c0c20007002103a40c40c0309000402c5407020b0300c04081658a4452468950b0514081d06403070868104171190400940c8183d40444000610452044060602009807401300500030a461250045000483c4c0a94030818489501a9007007001003012000c0244c880c0c06000902c00c001500418040f0040000159410243c4100080c3c41048400c0c940010020151602c4000585554550100688641c031260b000581202590010800c44110018010720814021140200700081003107a03110710380785842d80c840006204010880d01d043c0c480d0b0004c01030310710425006150401081945045410007801118400354038002c1d00c00c011b40c010a501030044420340e04040dc0c0316640e000aa8808441180302c070b50085607014040003032001c0d40010000c2441c001503d5903 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 543655179 1250 543653929 543653939
    0x91b04050f030f0604110a05090906071d040906090c050301020301050607030e0102160806040b0c04080706030207080c0d0801080111040e0f1b221202010e131e050115032702060d06 79
    0x1b24885100d201401000344100004e00c81c50303d030955500070f0341c210010b0000da88800c0400c40d0380c080d220f03201c00e84e44c1c28842c00400d842d8580b48110800d0758062100001c442c0342500e070480185c8490360001e4030aa0050005019565818048449255060400c01d001c1140313840141d00301400c9001e024900f810403000010684004581d084c4030381c0c4950541030903540c17182c1c1c00c09807074011381c004c01906034401282800424000e40c002d041041c003454485003445c103151200340c5842d500c0756601001514031001008031a109020b0b42d4545050b401e4020304003410120100810200204820039010803000460a05a40303104e48820752036660308940d940301580180d1001a0900b03000348500c4854080c0c0c0065203414040c0d0144a280c0d050751982d01841c0e542d000c00c500c8010f43c0b002c490006a5642c19107260484801c14060820311883c0c0100715585080007c00300003400d0080c040c20700d400c0901038201051550003204c1c507111501005080154a80003040c40c80c081c0c848150020f62904c0d0340030603 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 543656429 1250 543655179 543655193
    0x6090606030614070305040b1506040e0a06081504050a0f080c0105070e030c01020a12081f030501090605280507200f011d03042303010f0b091b04050f030f0604 70
    0x80c2840381d0242810041d1101300b001c8084690484000e0301d20b4038400f0215031807021941c028182e8000044c29641000e8a449503c490058165001c07450076507684401c0158203401c2c040c16902104000c4555094030701507ca142d02e5140c0500001e00124164800c041001041002e031090344107100c000708003516000b800034107400030f186c007200d20070311905500001740c0d84000740d83c001c40f40d48401e0025034603007918029160070300040c100000c1e03005951740005928800c004014005c6000f070001048a400b1802c00c48100c1d140a0300d4490840144d00b4428412000d95120b01c0545801c1d10700001d450f926038030704540d100340c440c29a0180c0f51502481c06840100080c14030448420900200309400302c035100288001c4641703004e20140d40050108001d003151001c1103040e001c0d8084096800e11102c000080c0c00c6a03940030b8400c000c1540c5660010513070500c3c2801d15403000c040515441084c84d00c41c10513846000c3c5200f220300c2814140134444854409020070207900c480c001c00c42c0d0341030409150560b = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 543657679 1250 543656429 543656441
    0x30705010c1d01050403021c02031203040c0b0a1d060c0a0809040c0f0c0308060a150203180108010518041506081c080601091e2d052407060906060306 66
    0x10019200b0480304101c054210601801440140c49141c9403d140d035003400440c5148103031208944250b1049840035890a00107280784c880b0300b0394419a24030305031401b402c40380c02d281c0000c148041c05200c0303010301035005804101408210700b080140745140c080000c001d4416000060b003a030080700036003001c00c0070f280b020f040340017021581802103840294084550f20b23410288500007030180d94850002c240503410303498006401504023291141c64070003117110401c400c610580164800284406909001610600d0110092a00031070039403401000841c0300d0404c445180080c0e044801040400031410700342c1c580700040b284140609030341c40580f10b80ba07401d03215080e03689209000141008602c903040f01c0d03108240503111005040d080140c03581000c2710006000a24918106004ca10540e08480c1d801ca4900d5503901014010f1801c0d003040c036200130b143d1010b80209041403602c80b2081441490103034020040b13403100e880743c0090400380080c1102203805800503251950200520246030002 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 543658929 1250 543657679 543657701
    0x15110a03060b0307050426012306030604020907031a09040c081b091302030a051b0315090a2d08070605241201020702090a0b0a0b040b090603100803070501 68
    0xc10600340d50b0010740155100403107500c40042c1003003206105191524401050241200402e0624400c006400500310f540c4990034a01103560303035050791880444841119400142607000c3c010600b090340c04642405000750a0074141078940c060040c10000301e41103900107000041108107a814542040e01d0100100e00603446503000702100c41c054a162a0a41042c0d040060140381546d47d98a0b100e26070052000e0040380d050180428607400314004115460680305450441801c2d090204205450445600040003448006204100002801103503e414054001100c00b0040040000d0101040e50400e02007030b4240e036145001c0c06100c45180544081e500c0fa8000304010b0f104c034000c0e16260f903028400005030030000c445c100402d040098501d40023002880025041082c41d9000644004003100d40111190b0340b10f00418080c0713000c0a6650042210441080c5401d041c41c604103410311500c41c9180c00340ca400070110f0741c0711070003030703010f0005000c030005403500d49480340b030228040c020350250 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 543660179 1250 543658929 543658931
    0x3090f120306090f2211131d0a02030c0d0219090203040303050705042d210605150612070c02090109020a02010c02010605011b080f0c0d0f020c0108011215110a03 71
    0x1510511601894901031900c143e841d07181d4071040c503450f000003001d540701203c0c12050000006e503691a5004c0c10604000b8898010030140e0030f4503104515500c2d2221941d207182d00594414016860102c1c10100105050340c417500810038070300100e1070096241c2c8500d1b4411440b00c00c0002c444e8040d0b0701542c0509d2280d5024015504c075030307100f01d500d0301450084801104085480d00350030700119113032111100000d4a074200c5650346500c1d20702e50402414a003d0300000050442041080512440e41c0c0003070803900c200740c000c4202000c1081e501070400400103200312400030902050044001c1100c281d401440725001d9a102c81d0408080e41069612901640c00c205003d1992030041c00703990705594061b5100d80c2141c0e00201950304040303816409455100003004409107580303101c4020106c203030780e00c8014003132440b0120004002c161040010011504000101902603030b000d10040c0c111000340d035604040e00d501e82050420b54319504205040c140c81c02c084103414405a0014203200e031083d4070 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 543661429 1250 543660179 543660181
    0x9020a1725050918160303170c030c1608130905060108040b0714040308070c06020709050c040b2a010c02070501030203010f0b0703110d030902130e060c03090f12030609 74
    0xd03000e076042018030040a422626220244001d007041000c03a944000740b11900c40951a408450b24200324041781c81d0524041640e1092041c544c103c2c102940031101003110080e20b1406200c028028000944507081450b800144c681c6080e240b8400000c460307400800c801d40e111100302a404076a01148160400d40707003000000380c003641c000d00d46180b1030764100e03074242100d5407043c400f200d00383c42c1000e41c110080c2c42403001101040008002d000c509100c0c4400504050620074040e2030a10f60740d010710651420b007020400403c003888140c60441e400040b4490300c0300a102022281d40c000e100318800010306484607609015015040107148600d039800303580c40181c4490046060b444240140d075009103103013400308010780b910402410110300134501800c1031190700e40204d040c4903042d51344200090b00c3d606440150301e03140003040400b1480b038108003e4040d04070407881c0c8414006251103441d000200001b80c3e02c04081c000c4000300011030082d504401c50301000d028194005a400314060400b102c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 543662679 1250 543661429 543661453
    0x3030f0114011b08130308071a091f050709051e010f020c1f1e090501030b0406060c1704050310060315200f04090e0109060b040c14070609020a17 64
    0x108243c0302003500300e150203000860907101c005141e031184019210340030045800102042216000e0503046101c0c1c00804103a0001e00c0843e145510050300600c00c43d00300e041e10503e10308ad0b0002080c00d40c458104081420f59504c001501c1003000c640c0710315003000c00240000d00003901c0022040c0c14003400d807070b41c2600d1058078400b02d94413184442015004248143c0e0b0002040c030700401c14401090b9491320f01d003400001110094901c4242c9204000b040c00300038140810342e0140204181864142e03401c12225241c1000188400c41154010300610044c01e007903541d01110b042190040c1078050103c40181002d089024024400d5110503145a94005a1048003204c0c1d4000e404401044100500481040090240560b48404030319812150f040100152000050042007040b4030101d000180000d902c0c1400c40640c1d6060120300d12840c81c1441058103c7d070049500d50440300c0d1410302c20780300d8079245011802044002d030081d41c007440e07403000004c804400714001a015002c00041c0d9685680c12 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 543663929 1250 543662679 543662687
    0x40f0b0406080d1209061116060e0607120e070f1d130206030106050c24160f081902041211011b170c0102160503130806010807030f031103030f011401 66
    0x500441c00059202401c0b010889120b40054a00c6030054030009800d00740300c05c250419902ca208017520140006200c1020309c00303a4030803c81c0e141044405400075162070000101401e250218404125941ea0710729000001d0801020014041c1c10404111703081d111540320040142c00c48e4240d000b00388100c001060b28540f4000418103d40c0030700454116400c060099030f540c0c1059000886501c103450044090b010100130090798044c80c095094600d003043c1400b009198004c401000500c00c414103c002c03240ea11540e1581e000c107505903034074a0241c14401040c00b900c035907402013862450104503901440300d260407500110100362165014461012401000c0e031040c1071000c5d000101c10f180ca040e000348050024004442c0f0100010701c5e1071341000e0b030802a1a010301c0700b81c03003e81c00440c00751403040d0398003c00b0001d8120200200301f2503242c6400e5a41d6940c039400010807400c24451700904042c0200d04a244400080090301c0d2285050f10400075042001d00c90600307102c480c110f040b41c041d401 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 543665179 1250 543663929 543663943
    0x4050f122703030403060b0d0b0a02030a1a0916020304170309010e1e040902010c05010f0509010b0402070507050d0201020114010b090109060c030503070c15020a0522050607150605040f0b040608 85
    0x2c0c2c05981031074030315250031000340080800617810140b510415000166000d981c00c0c400c4082980050701c904004600c80105e40140c160340114985d07000c400d4251f42d5443c03143c0c540c488256140040102c106001c00c905502a940c001c8044182002400010301c0021010700a860b90a0b039940d15684604000c000303502d035402400385000054081680c4940c00c10b500b2007241c0340d00604101c4808006603480c1821921680c654070a0300e5580c0040c003000003001c1c0150b04002c1811941941000c82ca52030300e5803149202d03c40c261003500007588440469000703411154401541044204640da902da0381c40b4003592000d101c003030014810003004a160ba00661200c04100d130190380e018111703910039100ba1b95001c04404151046004040d490140342c149000800c2110080e55074140c4a001a00c5044240b6201c2c00c1c1c0412403005030001445039849140943d850103811800c0300411584030702545c0028007030f5420075600182044404c0215600c59040161080400c0e58200515542c40881c240c5810b4 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 543666429 1250 543665179 543665257
    0x616060b0105041503020c070b12040c17030909060d0606060801060f0212120402031002030106020309040e0d0215070512180f0c0a060309020f04090309080706090b0d0504050f12 78
    0x8007a000d050707044d6119501178580050000100d480e22a2141042c8003250880d8007044148445841003008000c00b0107180c1b0300401300988902c180c40b80c0d4590407520fa024481e403641c0580007900c0055095500d098003040340581100741003014507101e0b00028a182000d004800200e211180c051360181d200241ca45c290400c500e4070b180c20100f111555038801100038200340da06101e1200540f241a09500c000d60080010b0f40085580700303444018032080d6900c47c6080c2e4201d80144000303e502c00d40200304555507a0b0a410702c00c03015a507140041d1054051404142d45001000003004050b07280d0032000c00200f459001200d01c020b00d1461500d41e039840a415841d0814040e0f41f0400402d8025007120440c02d1000b061101014500c4011900700d505518055000070401001000308000c180320903070103070240746400101c003030404500c100c3cdda00c69040010710240d590000502400f10a00005000340c5855054803a2221a100c42e640c00d500b001454100d0681c88a2a0a0800402c40d04103c2800 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 543667679 1250 543666429 543666449
    0x503030f220f020607061a150903070504091e0f1505070c080f04031a010f0518010b071502031608060307080c090406020c030a0201020a0305010608010302090a0e0c0616060b010504 79
    0x1507959452810500980c0310803a0009801d11007007001480c0d6010b00c01d0750a003000d1160b07801681100c104907415180d628500e0071143c01b000144056240480e600d4240d13901928041503440091a04004120442680d601030314140c60490301040400440b289030703d400b07030070035030007032207245c09000c01303d5600f41d400c04045460341e4800e20005d85000040c00c25407503a20780c1642455a20b0315011403d01d040702a81081412550062010408200c18400900015550810b5030060036000d218111010702415250710310110380002001207088680c000451030340c8066450741885400801c09081c584005008185e2140014460b41400240c101c101d42c0c20200821a0b0b0700002d061052194002d40103480f520f408004144a030380d0100010710600c4019800165106213600c03006003203c4044c0c0085c010406d00100400250742c64003c86508001315480001d104460322800511b00f15100710b225030028008100303003c00b2860465070701c140c0c2d409080240b0072401040011109807141d400360700401 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 543668929 1250 543667679 543667741
    0x1080c0d0504021914030d11070b030c090d03020102030a0528020c070e0f01061e08180f0d030f14250e130f0e010b01090b0715090503030f 61
    0x250300d0304269003050003d8641c0c50503a02c8032042d2000030300b290700081d010440d441079840480c02e0410100c200d40b010f600c4c14030a10000c0c07107107140d181c3e030341391003084401000840420140191402220702c5680000d01d01c0780d4503101841c0280c040c0d001190001103591400001494911400002c1848042c00081034240c641e070000c81c50009400401038901c1e03c0c407942c03d021546261313908455001d207402011040c860f40c50004010200f4038840b0600030b0000c1020341100086411021300b030340114000b01e245030041c0d450b03101e491500035280c034441a6403044400c3c03407051540550044000c075062003018841c02c0c0c0d0109054111500990311a81c80c44140e144010a481e280030050101d003405180100c2d500c401c5c030000909000d4030b50581c820013a5100307a92103000c003003842141382025880b030003442a802200b0000c2c1400c00f981c401c41d0040400080e01108001000410b400300c00d025107803c11001011382052070743c9400841d00300703204009000104801054130300c1c5501c041c00c0705900022074 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 543670179 1250 543668929 543668947
    0x90b150a0513030605100503060a180f29090c090c1218010615350907050603010305030d0e030310030609240b04060b09130b011b080a0e01080c 63
    0x14590000200b04284a100c0314048000f8909001e00d90041c81070410304100c10381031904050600304050304009503145020000c0480743c4600354102030380c0340c00c218807079020401400c24903034114000e001c1c0d224190302c60103d40100c100e0a69100d000c0c502d45000c0b00d9210750190240201c131102038a41d044041014044c8028500965000507800000c9080c0b010f44082240c1195080d62255005440c90b540011000e202c01d9600c00524a1400305074440100c0e25529041003a00c003c808204c0300100b0003485002482c90380741040035070003c0c44040c04040d03881d80c0da4104075403a50031005180c20043e04080c220a80c1d24400029a8050300090304103a400d2071550b6101e01c020b20040324102c5103441800c40e106010015824801c0340c40340c046401085103c0e9440400080312001d401040c5002d80c01d002c010801d0300c3e40c42142d4000c900f0543c002a541ca000d0f00181c4030000150000101d44cd8a1661001081143d20141489018517241c1400b00203040d001035500c0f1104a62000ca008018088804 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 543671429 1250 543670179 543670187
    0x1060f110c060c010915020d050a02030114091015020a21020601170111160b01050105030702370f031818020d240602070b030603071a04050603070306090b150a 70
    0x20108400354000202c20340c61769541c00c441c0380d081b030020301080e602140c004c4166149004096004002140c21480d660400c00b440d011000c0b07594005000b48658800a0b049409031701d4000c000d0b01c0b010208082001008074029075841c81e1440c11111441c0f10301c003d11a00c2408480811001c1e816006840d151303081040c03440e0b40f00202020034005640342c1c0501da50100c01d400040c4000c144070310414071035840c241011400d01c44181e01890400204108000000d50f000c103100140f4040801c50142ca00028600c03a0407038058180b00c00150b1041c0641e80c0308000c0143c0c140b01c50f0714400d8035101c921491180d0b5200700c2c11424411a034400103c1e40300781c2d0340d90f4071030f0740205851a10813000254005958090100c400014864441c00c00200b10080c0105901001070304001c00c56240601c0c954603001e40402d0300c07060184203000f14a00014001c484002000013510b004d00703005028a070703da1411100c000c010b0035151280081c82490a0040800f07410483c0d5514019900b170040c092a0240c6aa4121 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 543672679 1250 543671429 543671437
    0x3040303081816060305060f03070f052715011106040b011a12010b1c0605060706021c05070f08010e061513050d111c0c060323090601060f110c06 64
    0x1440c010305066030010007140034a58044e110580c4c0004092901e402841000402101c01078466880030300d00b007210402a60301c150a845066410408040b00703440c5e82e9200444801d1081c01c4c0f50751070010080e02000c40281890700c240f00366a140e03a401c00d600400394440740700341c501034031f4049098010700c003640107400c01c81c42c041d2070084400d25040c0000d01051410a081e000107484260005045620806071440303240319504440080100600d1301c40045c10512500200402c041d8000ca0039041e0401080c0161410802c0c685061205150200c401813054070000c907a0400b0661500000c135501d01101141131040101400710074114080b0703003d00d65550080781e0700510f4200030820100e1180c039041c0241c80c1c0903100c0c2034800c1e103c00c0d2400400c03d81c00455900c00741118905c5810f040824244101d0808403002401c000078144200d082000c020788829480c0c1003003191240c14407031080310018a03035040744c02d1a0385198080c032649000312443e0a21405405440d44250750a04151070004014 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 543673929 1250 543672679 543672721
    0x203270c0d1406041a010b270103110403150f050f37050901060b0a02030f0a09031a040302010e030f1b100908041a040f09050406090501110a110304030308 68
    0x340c2c1c01090a526502e0214115022115a00102010070300550a1020b803405442000420b60400749a100c6100352000320076294803844c4420a0384c003a140e40203030300c0b46404100ca03015103580c031741e00c909050f50020180c0105a501a01c1c04009640780d008910450b4090307000c0040d0038425441c0c190030203172121035015801e444039103c0196510365032041a120328084c50201c03004269071410b0f47d00107003118516803010054241c00c00030510354690102c22510181c3c0d030060744540383c00c04480221490314881c3c1004108040c10046951b01688912500707104034801d50083c00074054900b030450712805580c00b1085820380034880c1241b19120b041d0111402c11b03d4200f2940036041d4501c245054827011081900c1656000800f070043c80c6034200155982034038880c50310300e02481c106d024010b80c15103110b01048140c1e900d0101c2c0401886403c4039001c99003010003072040c41d8800040c409240e00602605003c65140c030442e130350305031000c021354041780e4154071441d0b0b07a81c0d1040340c003040c015008841 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 543675179 1250 543673929 543673943
    0xd0201050d0b040f020a020c1809151005030106090b03060709060e1005090301020a090312080f190905150114010c020d03050c0f1b0907080f070e0d0212010203270c0d 73
    0x3031460b1400c036078170103031400e840582e005002e002100341c1800b008019030360340e95282115007070801201c2c2c807002032141070060007804070f0f00b4190f44005c1d28102c500c000b42c200a82c50b500b0900d00107000702c0c1c1074104500c40041281600c041b61500b180540b0309152610594010440c0007080301c17028903220b00c9a01b82074115080c1a8a05224400000d003207a12519181011070b10754602031081c0884181030208100d000d0411041300c0c00c0c64000c207054140010440c54260f0f181c0d40f00081c48141c0c07a041016150b5008044603045c0584110750340010000340a484900700c0c217041c50040540c416400d03481102d0f00500b90f0152803009803400c4030303241c0c0401d204058a101d09840d0b6180c600b02000410181d840401e1040d280720384d25010007003802c9018101a0401c901c02c400e109440340c0313120036943c1107200f9081c440c1200043e003010403000415104042c0d40081c1c401450356280b10190011481080c00c90f40c24852006c0003034a180701215002c1008103994840000c8002d5818080011840c4074001c1c3c0c5 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 543676429 1250 543675179 543675191
    0xc15030f190b0312030108060f01030f080901090b071a06101b030203160c1401050901050d05040c0f03030e0310061206110f03040812100501020c010c0204140c0c0c0d0201050d0b04 79
    0x3c03d1605010301100d035040d8000000402c1920741c180240d90b000510840844465451901c035401c01c000d01001c09018001e0010b00c0c1982a806048848001c0c0312448546407140054204440d0101015020030311014200700041d03a0340c40c005030003400070600c544465600f052440d07814a00c00d2031402d0200c065200400544c846d54080f1407900c07000c58802c3d4100d0000e40d0030a9408144014440f001506008003409401c203140c5c4c0103001e40764411502280010140e441b030074003041602d41c552041c46001c1030110040280359001c624011500401d804840e070311a03034110440d00310303240c61280c50078499511601c600006c44c5a045080d6034400098030307500340214540d512075150f2080d2400c9074100383c0000c021400f5610b00c4200349c2d1201028480c000983c0c90b110000c0d4584500d4100d45d410410900c0301c000442d80c690340b1141000f400800c103115585060502a00140c0c0b058145500d00e10649014044a281558626031030940c10f031b403841e013400c000111007005060800800c950054450b4 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 543677679 1250 543676429 543676451
    0xa0b0d020421060b04091a15060d02040608011a1218030d09052104090b030f0f070e13030905061b0a1112010603050714120f0c15030f19 60
    0x6246080b01c88040c2429003040c0304614102080f108201402c501036130420503010045046100c00e440802044440a42950345a61320000042d07016072006502040100324024600203650140040e500c0711386035407465907240d6404180010184c0c41c00c110b26107081020369004075004203410303000340d0041d00444030400e81900c00e60071a00021100000301e60f03140d01010920404111142443c1e00482c806240941917804129440c480d6005443c0056150706107950603850410ac0150708108220558101503415604640c541e5400d124210003a580d9902150f4000546072030400c0c1103034946c0700c04c4403840c070304024804580c005900824102c1c0c0d00490003901181c040c0200341a8510071030110403c1c100500c06c1100a010064030541281e00d008820710001e000001d06505884001030443d00359040d003000140080c03040b0700040c045001e800e0710310742c0a6030001060801c41c0f108880c0400300f400a140220024002101e5010702c10f0310f2000410140305511041090700714802002140c2480aa = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 543678929 1250 543677679 543677699
    0xa1202191502032502101d04020d0c090602030c0d0f0c080703211103010509060a03021801060f080915190e0f0d0201020a14031005040612021e0a0b0d0204 68
    0xd003007002580001900071100c1c00a4202d900540c48414210700402086801040b8030301449501030007440a600e1080c81290b20b000b00001700c5000080041d035035242035010b0400906100181400840c8840c840400c465002000340e0345040c800ca802810003e03400d107411285800080700c0d8105011341c004018001c0380c0c0380c00003000b40c24040d890b242013460104030701030701021842242e00700c0c1920349245408001d9091040340d04490088422450769103400e4000303050281513920080d40314200204501c50340c60b1104c00113040700e4071600d0b107803010807843c0026030702a2022182e8192075080503000010b120140380b8402e070040030344100c000703882e40b110280303400b2a440c0301031604c40c951011420680e4404204030760001d0340d0300392009609204c18280c000e08025480d82540d070304114080000b420801d495007500c1c000700300c0140140003256441204007c0900301420a0b0302800c0c0c1c290b40101c1c40381d20341c1c1c02c80c9803800c80604010081480d10407180d03020703000754000380d0301581c00704800135500d614 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 543680179 1250 543678929 543678959
    0x8180a17010902011404150302092808010605180703090f120215010f031703090c0d0609060e0a050601050103020d0f060608060108010f12020f0102030d1a0307050a120219 75
    0x140c0d800002d00844074000900708090780d0110a4408004102c244800c402e001498900d203506400c0140c0c6401d41c0d100007a00500b528207030f030685280040b55000c82030041e01c00d0300d82211405002003240c07584510034808154041d222407000d81c040100404c9030039101740d002500c8a1b0141848200d40b00d000d60b40c500101860020407001030b841100d03014003100350210210300400000958060321450b42e41c17000b8081c0451441c20784038548c044005004504280001510a00001e05070000e000341494420010301e0540010f440e05494090b094601e180000f41c00580160040000c0500340e00c2d010044010754000740c0b600450030780b01c003d42d00c058035041c003800380945195160f5880354a4088001000540160702c0303030b0f509500ba6031081041c07000040114142c1d039010341d40c640b40001204010303880c44c8204d2881e0711810f442c00034100303c800b502c4610054540022002d03902050750f103500308040454180540c9003050081c000200040ca000000550340010448010000c990741e69658100c01b03071 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 543681429 1250 543680179 543680219
    0x30601050d05010801050106110a47160f090e070909140403080f011208311401050a1205131202160504050f240a030c05090a060308180a 60
    0x3d1102d0041c000160446003501272414a0402800f202d00f007901c0300d0380461841002c05010014141585803040c60740c08405010300904202860590300445540c0103818044440000e41000c10181c01811842489e90904e40c10300303556407800407418100c400c4644040038121800b44980203a0000341d48049000301140182c00c0c500e40c4125103001e0070081c10854009001c21138410b009001400290050303d0540d04042d00180c010740c403100c1426403a641400440080d1a0500030000031030201c80341002c4050584d402e6241c441545d0803106d0054510f130080449010200e120380c1240904071400c0e40c0b00c2c0d83c0c0318000456908110442c0d40b120712601d1060550b030801a04000c114140d103084408a140040070162020801450a99018001c200e0040c10341032440c40c0052010212011100c851034002e00d0090440107000d5481c90003060002c0b19114590040300b0403400222024000c0c4501d9084a030058500ca02c4c10f007000650200a01c0d40c0c040c090b90040e00d4980110b0300b84000d03444002081 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 543682679 1250 543681429 543681431
    0x60d0e1f0902031903020c0901030b100f0b04060e0301020f030702030301170601030807020105030403181401080c0c0c1302040b0a030506031b01140c0c030303040c15020a03020d05030601050d05010801 88
    0x350064400c0032005440e4505110541807007007990050f100000c0d85100c00300402180032108805103012030034406421411030703102c45000d00200902090403030250080140c80011101c0641d5000c524000d8002e51080d56404102800204403150140000340c00c0300800134001450302e555046130003801c0e0416114100140e20120050010f02000031030358440001d408000d01c031a614607610071a880c8220300b07009040040100200d0201400f034240a60301440010100010644a0044188a41c40503d8907400241490007180c08002c45204483d09a03140e075000d40800b07185002801010b202424001a10503820003000a610f200c2f0b43c040d041203c8544e501107040e040007000c05140241003640500d0050700703c00701d82c0bd00da80214400041150b1507080a40311108200c06500781010b050030741c0e0701130100004210401c00350102c10070075078403100340041580ba60f0b079a0807a0340340044100140941d2141c95044800c074000c4001e19072000051402a25100000140505854080c2c0c44801c06e6 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 543683929 1250 543682679 543682693
    0xd020301030b01150e0f101206030506091504020f0607020d080d060611010c17090304180c090e070806010507080405040e0a020f0d0b0c07020f15090306280b060d0e 72
    0x402949048004c0840052030505494241c0000250301150754807456072213007560284082c0b109003d13050640c481140c0d4801042481e03500c0c01c0c11a260481102c00c0c0580d800b52030300600040c0e1020191a00950700a00201040800c00041c04050341c010a0b00b60390024a5000000000c0d0307128000700001d42c081f071401f050307803880d02c2805080120518001c0d00340c0c0e41000720354400d05510588100320088100b0984001da1100184642944603941091007120000c2c55018104213040e040040c600c0308554603c0c4c0380e50341d90142546114070550300c10002407030100210322258400c401401c501c5c0e0152007031600d0195640005012070b881c4541c4c1c501382e40c00c0000c0220540c9414242c40b5401c03a02960909540c420710340d50141001c00003800650140300c04102c10702551600e030340d02c0850250191401c1010f00c4c02c1000b0208942200840324400d00c55140042e216500c1d40d80e18014640005600b030003144510f04111001e0141c0010702d68000001b440314a440310078500541c0007400803107005d0240 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 543685179 1250 543683929 543683939
    0x1c020a030f030204081005151302040e010506030f01090903050409050906041b0f051905030a08030114010c0f081b100903080a0204050307031b1d07080906100501140d020301030b01 79
    0x44032070000e030303004240761050104102d001d01c045010300203070060702c0001619942c1c01c034200800d4080d1490090700300e805600e25074111401c0d503006005407680b90010014607a83c440c1000301c0c5200440c1d403101881c05c1c907001000100310540002581510904140d03041986803030110040341c1c0205d403079814660020007840180038080c0c0c00305412032034006451443c0d5007005802141c2da8020320605000e1910046295400d880050803a000b4020007020b45176460110f00f0046456002805564901000c1203001c0e170301503001e09000d28210b80d0002c1c0c030320b2075103002e40c0701c1c2c01d0350b60060711072548460540c2c003181546110a000d2202c1141e246800000d8040e8603040041ca0000f009041e503294600c10401401240d50015095045942c0660039070006981c00000300d061407050b50201030381c2c85200d803030042c0029010f1b401d0b40c03080103c0c0d1740b002034070350343c0e0030145036034500540f110305099504440c20712107944210580d0080c501915815441c1c200b000941038100e81c4264001c0e5003c00c5004010b0007 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 543686429 1250 543685179 543685187
    0x20922060b0f0102010b0f06090607050d050a020d0305060f010c0f0605040308100905130b1b2a0d0e060c010b0d20010923040f0903020a0618110d03021c020a03 70
    0xb9400c400384000c0013696501c9000c1075608403590a0107220791004961000e40f83d84032400c455003540d015040c0c0b146001a11405480d82d000303404c50030007500495040305d0744584a44251803180c00c0081a005031062102c005480d039110030700080d160410f111030904d021401c0f90007000e004605c03d6469050b1441c01003030f902c1918415800c00709813103003082c0c24081c2c40300076062880d501a07017041c0c0840e2140c485551000e0b280d494124540ca5000000c11174002c00b250711404090003001c0c40d40303e150840030344500c0319200d2680d1200003004c603a00c2540601d10341003003c050605505a40000180020002e0000341c01001e400340c01c07200c16000c228142c0400b108442c00d42c40d120300a09080d60058102a085041490034100012404c94400c0302d012031665190020755100b4000007003044038403000e0500945800c030b81801034820f40e0600603406202c04c00445411616900584260620040c540030402e101e00110b60507811842400000041801856940032a089898000707100c1050300d490050 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 543687679 1250 543686429 543686449
    0x7050d0203100806130c080109080301030605060a0819030306141014130b0702041107021503090115030305120108120a0305090a0606080f0111070f0f0f0b070201020d2403020922060b 80
    0x1f0403603410108041c0000c0d62003015681920750022010800795500f1011079041e440c035a11004551081040340004684500304880040340642d0301481265180c00400005000301135807103030055841d10007000810700c10b9031050800f0103030300005880e00d02e1003120458000c01a4000c400740e008002400320861070a4454843c1301364000d6529414518941c0001d982d040400c00500d20001700000056402582980040e480c10601e90082c0d9089403603050041494012a50941d001100f010002c910010001500d2a20400318483c1c01c2c5031085403182100a41400ba0000c56184181d07440709001422034010b403000703004031800506442015810907030a55010307a40c0d0035100041000602c0c00f0450020040c02c0441d00083c51113054443c41c5841514904000006009800c0e0f140601004a6043d0001c240742480340c00c051000c100c449041202201c0e0b03820860090402000b410401414804116a0300124081501c0700103880b0000b440903c420140c02295015901c9030320304070f01c1c03030038440d00 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 543688929 1250 543687679 543687689
    0xa1e08151501050c030c06040b0402030c010e060d091e1a22023f0c0603060d0311030f0c03040e0f06030a20030106080a02120607050d0203100806130c 66
    0xa8507401c02500c09008071a010011504020f000507403000c07200c408004071205c0e4001c03401241c00318a000c1c00c00600e59942914103d200b80158540982550f105036058a00d003100204000e1920403281400c10003811203403800c1b42d030800701d405940c40401681c506040b203503010340050380000140880c205600740c401020403603003003140d0520050000d07289003d00744170380e4142c40b600913a900c0c0786807210b00031400000340c003500d4600d1400c1810340020440007485465040d003c684500c0240f4080280318007080707035100c2d041040c1c16082c50200b84100c28080b41200145c09a80c50122814940b07030860380304200050440d8400182040400210107061341d01240d6000762011074180b100c000381d1200e0141c84050300001e401500c114069110032090385040c03c00400811566654004154441640c01002d0b486004040c02001e190746020401c1403060046035101e608e00240300b60b48200940016080a401e000404404107002d40c040007124001c00036a403d138282800c440c0381481e2100c3c2d9681003 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 543690179 1250 543688929 543688963
    0x301140106020a02060706090803130b0601020102070f080d0e071e060f051b0118060603120e03060f100302041d120903070b09040b040203131203140c090a1e08 70
    0x400440b076000c0741404000e5030456100b40d17944c2803400c00c1c4000c3c00d2508409000d0000020904c0840c0c0031040c0320040343c41c4240c8800034541d8903480168200c3c099101c018000031082c002980c001110080180011481d5030350001d2901940745141e49001c82c01d42182c0041e6136802103d075211089e41110300010041d500d400c0200da0b2544100421500500e440d68441540107031060701c60300f0085d00030446404141069140440103030030328101908981c070064030300c684003801c2d04820034840d1754805071b804400380040000f038584c2001c4440c60300e03006092480c240c041c9100480107a03528003d80600e4103181000301d0744182144c443c1402e0900d803c0001c40f510404101c12036854401140f0942261105444181ca401d10340f004600589612480e261748244004100082140f0032034001d15468000c0f180c8480c0081544004d40865000203804000b4860381d00000303aa0401407001030400f1400070300b600703140c55034131000c0d86482c48500401c0a0801800b40082c0180303601041038482113013480745 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 543691429 1250 543690179 543690181
    0x10608010b1005070302070e07020d0305060f2404050612092b050d060f0303032c0a11010309060e0105180106030b070305040807120f121401142d030114 67
    0x700107080d419800c02003600b807207404551311003898002e210f90801011601200405461b10703000094030340d01000701400c0405e00e0400419003d0070040c1c1c6d49003070a0741c003416030750354044201d51808041050300710344022280100000b29041c6c5404020704028580d0b030700c0459541c100f031a001401c20318202054200441c2d10074a1541802040c00e03400720102060410301e5272041804080c4016142c0707500815850a01e04c1000030801d40e15074005a440d8420403c50020141045030150402801c14411441341c2c0c0140344400214198010b0704d01d180170141800107010540395112001d441c8010301c04062a5075880410071204004254aa0321440b1500204004d07030641e51a0918540040c0002c4c04041d0745070002010006250120b50800303803c20481032401ea0913500050040c030703c104c0d010b0005008140c0c004150005809520b0410784e10200100c400c0c1c0c2805905c6010400840109500c45100a05143d034558a14022414071440e455844981000c010a05003520510304152400640c004 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 543692679 1250 543691429 543691451
    0x103020705060610030b1f090e01030c05011409210105151305130b010b030a1a010f0c03030209040e0328020a170706050f0a1d0304061110051801060801 67
    0x800c1c05548100f00700d48981c0e00309010201200109200001540c01207148041d0f05078080e0f58107240321204151340e4031584095161520140182000e02c4018464940c8030800d00c02d66001c0c030804400380c15070748107190820703c0340c00c0010014004483c2004480d0100001038242400c20302460394480d07881098401d200030884041003003c80c4080040840d5992030300414251203a0552420115030082409841942c44010601c0c090b030040c0c13000441e00e03142c040710607065900100d0b10040100140c41b07910180c403039444103940f444200f9070101c0c10143c0c204149001c030741c2c81d4812080304501d014007d5864a004020401c4d603c50300c5004140c1c0407018202c8000810380c00035840000c0c2d94881000310748003001820021050080e000c1c01408903007080c1c20040c078160f4401e410f9104030860300c42408407044144070352603d00c24240600b112a0000c01c01403000b54018015032028a44003c1100c6010181000032001c44a082c1d80d09441030002001344640082c003401644003602d5844000c10040c0905 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 543693929 1250 543692679 543692683
    0x91202010213050d05030717040e0708060607062d060905060402090f10020f1e1603030905060711130203100e061f26060301110408060112020a08070605090f0103020705 74
    0x580f0680e882226042c1c0322108000c4180180c82c80c42d0f038410f030b60307892000411420b00843e80240c082c0c0c4140c4241d0400140560744220815801040007074080c074a0801d00f5221140580851081040750f5018001d010b501e50358030030052510a50034080004416050810607001d88601030011781c450760040c080e00c82e044da203841007044052021546600c40d801e00d41416420200c042d40181c40c0b0780200da80c802031056441e03482031905880c210545003c042402003441c085907480c00080e0010300800414489800e081004221003400f5610010200f078501f030000b4424501c906d2020399143e00031081c80b0102070241d030113070b01030b140440c1c0c030701c1031464000c01080c089107950714805401c0d50b01021201416005103c1146200c200b2400c0441c24401d2045148001d001501c1e014047e42c40c002e021ba0b1030300300250a40741950084006001c550b484e00f8a00007000400c1070381030760710190845000516107410000840102450707107602c3d0312402100c041001049140414a0505004105150005d400 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 543695179 1250 543693929 543693967
    0x120c140904090c0e090c10020607021b0d081804050c0a0c020405150d0605040b0705090109030b0702120a08090d0905130e161d0901090b0403030e010f020d0912020102 73
    0x1918000b0398805a400c0045000e05658081c980240b0034a051009800b40031683c000b01c5101940d5450401036415401c81c0d0b10b10003180c4050040c1c00000b070080c81d140103020348140403c0300800c192400503ea4030317840b0207613010341d40c445040b0b000e80d0700300151410a40030300c60388412400480b900341705e0100005481701510800081c41075903640300045591840a03030384604101c0c09088000154490700e0305a0043c40240c0b41075440c11000c3e00082c10162298003107440305901a95515081440c5554100c180d44020b0040800d500580201d0201000a00003801c401d6010342d54020080c00d045000d10b08005030a08170310704108200d94140020f8491055640c3d00803500c80300000d00d00c960b406c00030f003011000340103a080c180c104103000550807951004c490300031400b015802c800380c45d92080c2a08035440004004e01191010780080c0c0440c0c002d9004110310f410b00d00011540402c0412440b040768024185002600d07560403688080c882e15042d034111420450000718a0f040c0944071007201d4940b = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 543696429 1250 543695179 543695197
    0xb220501050901120b0c091918110c28020402070c030312110f07030207050406180509063105161715061908010203100e0a110d0c0c12120c14 62
    0xd0b00080d48003041e20b40380406070040d0000e032048d042c040d0321076400604000407170071510013060404600b0760076020050201c481c6000030000800403041d142242282c2040e05407290800180d6040300400035840e540020441c4034031440740304c1039845c2035150141a0104d85980225206e103030030103c00070410400708503681e91a40880250700c490b16441c0072454001307140c10440c2c015040450000320060000c800b0a07501001c2c030740c148050740c1c414140c10380d00d120072115100801a48a4901d1409a04c444094100301d021404071590300c00e00d40307441d0300c0d1000b10550982c2050145a08016004c0343e180c07000b100b50b600300040d080340303424100c520400001c0070707090070304c90304d0003541c85000b000d160b500402c0201400c1c0d00035500c87c5045045030392030404921642800704030001c00180252801d01c82c06440030100d02c1e82c1c9080c1031540c24620010801c40c21410240404d240d04100407403003403040340140c00f0580d0340d0048c00d210703101807400c02d65140045900600014002c245050300c60203050300c90500c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 543697679 1250 543696429 543696451
    0x9070e04020105090f030309130c1b08070206070206040e01030308010617090a02090c1e030601022503260c0f07060e01140a020111030903041a030103030c02040b220501050901120b 79
    0x1201000038254420000d40c0303a80215404103036507489c003040d04120340c0d0a101e9101c541d00c01d0440c03520482050402d0388002c0620300100403490040c078180c0c0c0a811a540060142c41c249616280c1c0a44002d401781c0058020074000001000201c3e800349a1708000c8944a510b100282020010150b030341e010140c000340710b1100706000a40603611a01900d409541a41306180c15280900c406003043c1d00644005006014641e081201000f583c0804044428400500c0309840c0c51501c0b800103503014100c241c4c06680c00c4030507e400440200015043c0101040d01a09070245410300b51860451607500c0003080c0720482c1c5d040c01c1e05030b0b005001f07504504000100e85545030840740c030807030040c4030302c070354844041d04003100f808000100000600195804d02044020030081c801c0511840e00007403000400182008030060010300306600064030000c006015043c0748007001081d0b0240c8212004a690415035400040140340740001f2024010001082c041041e102c5030740300d0010b007034401082015a0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 543698929 1250 543697679 543697699
    0xa0b0901030b12010f150e01030b0a0905031b0d030b03010c0f0305040503040f260102030c0f09010c061d0114071403100b071a060901060912020607060e0609070e0402010509 76
    0x358440e182800b040703c2103007008200721100020081d000700741840c015022000056004201a405582807a050360b03000613040b519551107491140c00342c0203081d0300301c4d081d000502005405650180c544020701c2084806042039000c8001d0003403c541c00040320500c640c0c145032801da040c64020007a0740d696080e518020642c0c2d40c81782000d03403070342c0301d540d00c562490f860545000a030f08400c0040217801ea1800082007141c3c58003c81711034241d00050303c071412105020441a9000311841008140340034040c1416102104140c9590003102c15107840415040c13400003140301a60820310072400c40000100000016051003500180100c05c0745140781140003001011030300c4200e43c1c080460003004130200180d9216103600e462000c048400360420030010712103010500c94034181c0c042034140c401c1d6540720410740f49040305080b14032680d42c0050b80c01010400508021a07124080c4004030100704000b4441e60801c85002da182c8840741d0720040c0750102f0300d003d100c010f07a405801c07104044d00458480d020 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 543700179 1250 543698929 543698951
    0xd18150c0e0312091315050111150c0d0e0a050a020d021203160201030e06041218050621100303080a020d0609051e06010f0915140406030213050a0b090103 68
    0x60342540d2505681c0c035100e883c0310084051141002060040c00079109440c048083c03000c144251241a40c0003c826105000c00b401a94890071082044500440c200d0f0110280650704010b00e1005468a198040d0000340206d8061124018880b102d44c000e4001c1905e1400c5032a22078540410200003882901008212004e40d42c0742460f4007540410141500d81e070f0f5100004e031269410071001c0c1240440c3c2000c0704000c0450002c106648603641041c082602a034501c0c2e01199040004c10101d00454014003010a0644910015007042c000700c025020301c07940110102405c5220042105200401d520b00500c00281d00034200d5801c800070000c0981c41d800d0700320014000c0d06854000042c194a404100501c035074408000701d07406011030482952944507900112641c003459804080801da218004001da43c0d001400e50401707403050725168055480703602401301540d12581c00000002e8010075034044280304188410001c4c64111044803199113004a0001d0798003400070b03c40c1c14103135201442c0744 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 543701429 1250 543700179 543700187
    0x141c09080705030a0201140c07031b03110a0b10090501061e0903120e0907110a110315100905060a06090e0a0906022106030d020c09040f05070303050d18150c 69
    0x16001c0d0700a043d2600d4080000c0020b00034404d00b0700d102424103048011520244500d02162030b81a0180e94282c0d00c003564142100b41851241811420011034080c40d00900009000e0f01c13600e203100d10900d441504142e400262044030b16004010b48600c1c110040008640000315003404007031408450400f02c80c030005c2a220581c0d0350340080c12182141c01250070343c40c2c5c0011043c00d003140031910407072261a401e10488a5a00c501c4d00701240c0d90202c0b00c440041185204244d00c0c0400007012100516044039601000b2402581d50000320101100b00703104820325409019807009040d81d5882103035103030980040035855644a980032403070500c008100b103116550008440381d60010320542daa800c0780ea6540d9003201c0c2d0145c04034040c3c0c0d046004951240303004650750400601c10707402040c1812038102004011341024004517080041e01402c4000240140720440003107002c0c2c0c07902621000900c1c43c5000ba103407107108690003070200d14880c2000445401030900c0c0c10101c201c000071001a030f40740070f903 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 543702679 1250 543701429 543701437
    0x61c031115010f030320061306020714010903020601090e0a08031519082e020a17100932060105130b180913020402181f141c0908 57
    0x200001d0111000851080f58841200c0103d038803d540e00043e680c9101209070801c1e0700d0744814540f9403c000082501c014000300d54201c028083ea00c01481c01c01c00d5035941918400c0016000d40a0b510b86501106154040c0091340c01043d06102c1402241608030314162619842c1000425400011021412a451040c00204410b60241850a40c405400c1c50804405014800e03003005100f526030f14000c0c08a92041010141d0507131841008c001841d51071840a50003500b0310604010b00001c005c034600c4c4c42210a14001c80c08840040302c0b803402d01d03c1100aa82c5040d0f80400700103626200450050306410070004544981e11441d5074a4480b8401200c081c460303500300e038042c00c0c07150b540401c04042c21030042125911004403c09594120000e03c004141c00326410604148040403540c054103080d0010a140042c0502c8020158084400541d4424071507950b14141d90101919895070394000f1501d034071703800c140c0034814200148204494100030350460480d00642d01e810621003004103040c10b803 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 543703929 1250 543702679 543702703
    0xd02030f07061d07050a0b0c060412170a0605130603020603071d06040b0c0d02010608030f0313170702030c01050f04050103110705060403110d0302090108040201030b0a17070e061c0311 81
    0xa1002ca640310f100300c5036240a01c0c06010301c40c4445540c001800c41400080702c040d107614002074011550303241c44d2a00c1242002c01361400307200c0b068541c00c2408010840252080800190015109052030144407610702114882c1104a20f040c90034800340c0c2d180f9094135030210075171130400040a06114104400c3c034000d000c03590404808903000c10014000b402501071808420122401c80031550030032400d803100c5226692641d081082445072440f031500c02141e00c05010b4451501d111010f0b611520190b41916480002401c086034607000c515080c00301c401130810910b0040d040447e40d06050003035111300d108640c14150b858418a8a0055550a8400351900701068403d18a080d09010380400a041555030850181e0003c422110740a4402d5849207541a0340300801903450303900650080c400a0710180d44820210300000e40c41d84c030b80c46405440070b550805868042e2410880c10041540a885a031040c00002c1000d050f400c1c4000c00c901e1455010301d800403907940c040b100c07603003040b000740c0e05 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 543705035 1106 543703929 543703961
    0xb09010e04020915030d0e041401030209010510140a0215010f3507181103220206070c0609050a12150e1207061a030d02030f0706 57
    0x103c0e0b030010007000b0b0f20020f1200d200c0041d20703017895154890000307601c1400c420058245802500101e0300c200080c5041c43d41503034000380642c3c02c140215030040d81c1104003802100e1046044031b0a240000d90101e80ea44080c00c0d0094890b40c0303200143d843c400d10240000b1300401e034015981d0440c4c40e0703c024030104260780951004c62204100c3c150000740c06c54100d00d1188801030080c44000c10b80003080035440d0522080750026550540300041d60b4610500400c013000c1e458800e01160080c00c60f03251100080e4610006a040c007403000060a0b8030901140454a140c100c0040400c0d074108030f640c107400603a1020701c08020005464000c001c0300051440c5000050b45401807001b100500301960400349000007001000d4000060565106848a0114107800c20700e200350101c0c0a026009004044207020000e0b5891003410304100310000005030b89000d1002c4e0b0f6000c600901c181c808 = true := by decide +kernel

theorem cover : BRFrame.Cov 543525179 543705035 := by
  have h0 := BRFrame.cov_init 543525179
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543525179 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543525179 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543525179 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543525179 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543525179 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543525179 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543525179 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543525179 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543525179 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543525179 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543525179 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543525179 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543525179 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543525179 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543525179 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543525179 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543525179 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543525179 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543525179 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543525179 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543525179 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543525179 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543525179 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543525179 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543525179 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543525179 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543525179 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543525179 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543525179 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543525179 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543525179 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543525179 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543525179 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543525179 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543525179 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543525179 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543525179 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543525179 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543525179 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543525179 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543525179 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543525179 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543525179 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543525179 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543525179 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543525179 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543525179 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543525179 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543525179 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543525179 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543525179 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543525179 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543525179 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543525179 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543525179 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543525179 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543525179 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543525179 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543525179 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543525179 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543525179 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543525179 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543525179 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543525179 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543525179 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543525179 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543525179 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543525179 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543525179 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543525179 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543525179 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543525179 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543525179 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543525179 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543525179 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543525179 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543525179 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543525179 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543525179 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543525179 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543525179 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543525179 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543525179 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543525179 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543525179 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543525179 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543525179 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543525179 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543525179 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543525179 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543525179 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543525179 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543525179 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543525179 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543525179 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543525179 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543525179 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543525179 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543525179 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543525179 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543525179 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543525179 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543525179 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543525179 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543525179 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543525179 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543525179 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543525179 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543525179 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543525179 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543525179 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543525179 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543525179 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543525179 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543525179 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543525179 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543525179 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543525179 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543525179 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543525179 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543525179 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543525179 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543525179 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543525179 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543525179 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543525179 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543525179 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543525179 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543525179 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543525179 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543525179 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543525179 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543525179 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543525179 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543525179 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543525179 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543525179 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543525179 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543525179 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543525179 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543525179 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543525179 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543525179 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543525179 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 543525179 ≤ n) (h2 : n < 543705035) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
