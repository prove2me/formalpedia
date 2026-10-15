-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4582
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:04:57.484985+00:00
-- url     : https://prove2.me/submissions/b99f99e4-78c9-4fd0-a8ea-eef9ddd4fd47

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 823920863 ≤ n < 824100719 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 823922113 1250 823920863 823920887
    0x2030a0801270b010c1e230601030305130302060a030f1d030f250501020304030f0203031e04081b0c01030e01090f0b13050312010e0702011b0e120703081b0607 70
    0x3076950030004540d81e20882c9400c1e900341c6c0001820b0088108031074079115689a081040ea120a0402011010168040c0802c4081c0b8031940c060010350b421a034044440e1350048a0090166125081c04070141e613034040100382605160701d000444142403e41c400a0714010a5001146001d20113500c220040c0482140c03000b01c05101c0c5a80c0e40c00c040d003900340c08500840c440c54102544401e10710100507056000714011030282e11140d48002140034126070364801114245000e50b50301000c02419403500500c242c04c148140302d6541408210f00120410034010303401001154401c03c0004280d582511628042c2c1c0301040080c46481a50b40751080800c941c42001400b0418100006034040e04030860403509582c040150ba555225140980500c2e030002c1c064001d0130424072003c180e110b8014410b030080d540400b0040443d070301c1502c2d030559014024603603645d0040c2c042d41500c0394508040c403030b21020b94860340f207240c1c4404c102f00140c00612108009140f10303920150912602c150840044411 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 823923363 1250 823922113 823922189
    0x180609020a09090b0d0804030b090115030510090303020d0e1e07060503061207030213090c051206150312120f0c0309100903020a08030708040302160f090b030f0a0302030a0801 77
    0x184845941c00b0a817015800c0e00041c1c44500301040100400c8481800d050013001484001d0114001c040d21112842d0118400141582d0080301c00b10a003480c5a0800d00c0c08074064100142000f010141f14070641ea440d114104c9140c0203200a003100c248020110380c01000d1400007002020700300380c07001d412440083c05203407082c034140d8410b04500b4001c0281030003465004d07001c60500003e95003a00701418081d44122610340c00c068010a00f03003820421420078401c420010107058a0359101804030b0f84640e0007007500f41c0140f605441e48407030744800a00000e070f070206100d4114074010401490484002c0c040c0c0301d002c001002801071602e8009070038500307501030240005c0c200109180a9142050f071042c0109034601c04020008140e4000d5800307803155019400b0b851104410400b40c0c44021300302e000e50003d080b4008802d00504410307502440070b623007026044404800a90505500e881801d40048005038000103406d00c10303d40c019940c078010702400c170313120366401c201c1540030244040903248401c0d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 823924613 1250 823923363 823923371
    0x11b0503190606020c0105161b150507030c03080a110f0403060f09080a0807180b0a081e070e010c0b2e05011d1807030518071d100f180609020a0909 65
    0xe0044101210702c235840340d008230401e090b08025001c81180a03414403910221420180070b0b10311490107002180d10300b030303403565501aa883e003d1760300351421400a411408a903548403266000480b4100050840780424640c803a03c030b0b465480c01c1c2c41540c4004403441161814100d2090000b20350030161982200c09040003c3d190b07540007070447c1d103541ca00716411a0bc00840c94005004400c2500401185060f90344410043e80c0d80c205004003441c0300b04081c05941c1d1441e0010300110310034500380d040c02005140c130b841c51403000e4480c003100314015207400c41c174200b107038501c0009072803444514400341d00d0203400f000c1080d01e0200040c2100750001820007d210007031403038942568441c4071b8151448504034000a00b800c29040c024000e0008441080b82c1003c04814000452800215074046030307442d50141d039038048881d2804009800240003001903a00081c0f010501586010340c0801600320740441000d500300310721143c410f0300c1059104450061040002c44569130380083c5000684541030b2000c1 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 823925863 1250 823924613 823924627
    0x306010303200a060204050405011d04140309060d0c030b10020303040b070507120f08010b16140c03060901141311010c0305131d01091407030c02011b0503190606020c0105 75
    0x1000001e03564600c0e9a0314003d035441441040020390280c0300343d406c240d804120b030703a884060b21181804004151030000b0703c0710700000c00080310441400a04105042581d080480c80310101d09140c00c14001860301c1ca40b60f04101c00141d41c141318100540e1400c94840d0783d015100c400c043d44030300c0040d00280c14000994001a440d40c041c1c070442d401c142c0c0c807610000c103d40240d00d0003803008039000c0b601030000740701800001d02c025842007030f00d1000d410015019022741c1159036200740001079041514442c010070301c1c581d9143d42c017801000d105540340ca0010580e8442c1c1c0018080c4a54005d0048034001c91949890307012847e940704100002c0c1d0213081500003450541420748090140c00c1c0d600c880d40301d40f031901040511440c00c5004150000440040e2281d03256220401983c00782d08103402c402c000d0500180c000381c4203422079441d000103030000040b15010f0000d2042048001100c200202d4800028000031101101840075122801c0000b001501d04105000352079001c2c090b1070504001d00800d9034 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 823927113 1250 823925863 823925897
    0xb0708030411150703030e0318040513060203010b0d0e060c030609040f120f080114030a03120204090911010e030106050915041506180b032703160303020d0b0109050306010303 77
    0x1140500c031000f03020b20095180d07080e180819a02c421000c0b00000e084ca02d101e25895400810b481680c07d04548011081c0b400c0800d101c01040000c1c1540305160020700108003242c0c061008601912a0b0018a55180d10a05515098454030010341580764032100070001c0400518094035081201290f0050040d165410032464086c100340026290401c006000941d090b0000301c1ea0840603005e40395082c07240c5c1d80d41071014520343c03e601d0140d010b400080030480045d200e180c4500303840c43c040100504140d22408014100e681d59a411150340107546079014243d038225002034117044045000740302450030306000c50148070024122140d2020360401d12502503442d6045070803d050b12182c1400140c0e5110300003440c222001500346131015168a000c07401a00d00000c0360b10840e0303103118440e00c030b40c801454a10400200100c07241c807808284098106400700e40407801c100c5020341d9016890b81c01211103001210f00f548240c0d81800100c40f010081502c01280150440b03405082801200000c0914 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 823928363 1250 823927113 823927133
    0x19051203071715090a0f0e0d050d0e1603060c050705070b03040b0c0903120f2115010903170a120218091f030b07020312040305040306050f0c0d0b010504050406060915090b07080304 79
    0x800500f40501e003040c0c5500c60b4410003400b00300c0c0c1c442c0c0091195020a01c0403543350552150b1000000044920034170105c0d0490f00300700300c059600d143c07692904042d0748a1a00300f0704240c1000e12050341c00002c0c841440f10465115030000c080b03040c010b04d450500700019554560450a50008440c049100806005000c00303580a490481824559090150880b400004000ca601910800080d40c80000c254410300a12040d258840308046035207000320f410302c5241e0002044842045860f400ca80a440c081d400900118010041e280078502021010002194030050040201d01261442c02080c03490b91401d41c0202d940198000703e0341d45038250100d046110f20460000c01e1424001880101360741722005104481c001d12003000540c490100c0010008800d51768207040ca0424424006004a290700c1380d0164541410003510b419501c0c404201503034100d87c8081c0c0070508081041004c0c41c18288011100b0003e440d08045160070001e01e021103000b030601c098444400400024100070307003014 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 823929613 1250 823928363 823928381
    0xa0b1c03030c21020301050301060902090a091a0a17060c090d0602070f05030c1c030c09180e0607030c0905060702060a0c080d06090203070e090919051203071715090a0f 74
    0x542201510000500001c5d600070b11505000b50320748600003c03240c28601c2903400c442c034018010605d40340b46c04218800b9024450500850041c43d821070025680c40380d40000041c000600554a221142d40c1e14070309100e4014003028809a04104200d125a6952012140940c0c881c2005032187d49506000b102c100f80c1da10014060b100002e030402a10800080341c142c4d000e100c071021a000110a80d00f20181c4041e0324a420104466400600c44445000c02d00c2140c00c00d215400a0a910f1349100359140c40003c1d07a001002c0380d13171a00b0304c2e030059500c806442d01501e801c1d00c0031442c2594030b03400b18041d40b241d00c0945c402c1140115141e020868014200e030942c40f40248144022611402c01c14006d6205480c040b003c1421180280700600b0540e00c2c8038440ca50990141c2074004d01079044400101403110100c5260040003a00710144071100c014500a0740c46036034010416558420540a803d0003400c182005000b086082441b07a03a082e07002c82e0301000031a00070a0300c41001001002610900b0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 823930863 1250 823929613 823929647
    0xc02100f09050307091b0e031b0f030d03052a031f080a08040929060a030f0e03040609300602070203100b041b0836060a0b1c03030c 58
    0x4e00003581c00b003580c2040780e51131007651030392214004000056680b40065820560140c100500c1801d00c002100c071603e00d04039020300281002410200002c1c2400103070403e084c0400e40c0c48040c407008031021003409082040034145117040d96810001c2c0d802c81d0200401c1040c2d48010b580320502c0002481480c000104245001c4403600314091505046a07041030040c100b0b07031032804a04041d40d03203242c150300801103d40c02d040c40316030703400c003043c404c4950000281d0000d1584601c992206941a4850f01e4140c4c65481c001d140c803182010401020654607500c40643c810580c0d0b520315401c03c4110440f03400c0b2004d464002d1f440311517440c104029010743c0001960501507101a41c0c4200220340002e8112035046504008a000800c1621f509003424010f03a00080c0c1c07000001080710003d40035222480c421240b80004000d4171702e200230801304140c114841c2c0b5800c01002e0010a420a004d50b81101c5411141c021180c1d0111442c80e900d0129004003600300b40d21508846800c0b809140e41e02e203151066 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 823932113 1250 823930863 823930873
    0xc0303090102040603050a06051e010315090212090105071b030c0b090c0315070e090402030a1718010201060302060f0d06081023070e22021b0c010c02100f090503 71
    0xc400c1a0303000b90040c1c418800030a05280014030310061520840c000e17070384018060042d6000c00d03c41a5654401000c101d07045c16074415480a80e0150801e46d080101b43d4000d01594850340d509515002d11070252484040e0380c10082803020f800e0300400000c4500700d0a40c4490251010341c1000c0f83d000400200140c521051001441020200803403c5030282800350112000241c0d0185240885c0d607080b01c00e00b000038031022644100c1d281551481d50450300090485035100e020ba2144891140c061020000c1c44000040c05000d04021a0721010004824002080030500d960045203003403003214400112441d00080400e00b011413944014080c00d40700040b110001c81d01c0702c00c08001d081c5050000f101c030034880c401c070101040c1c4480507841201310703682700740c4030058003014480ca0f503c03550310101407d4619880249400010702c083c0010a0656148207403c035114070f9180d0a203030310403202504024500002030056110f03c08020145051440d100c00003c0c51048101c50f44010b0340c1005625000b9 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 823933363 1250 823932113 823932121
    0x11030106080106020f06090c010e04091506030209092109040f050108031c02030115030903090305030a170a18022b06020406080106050703120c03110c0a0605071b0609080c0303 77
    0x1c4080304a050ba00b850b001c64551161038102190f403150212041c0c2401d80c000d2556802c00d52045001c8140002c004d48080360440700c0e583c0d125110848240820300c00399a840c02001545848011140c00c054100f02a0004440315180504242c11041c3c1c1d01d500c003440050900031640f29507000c00724024200404010031350315a021f0320f480f6884460b541700d50f5400c254420801300c1061003164102c403000c0a8000c8048c3c1c5089055002d080b105600760140a0102c1c00000460030620040c50081000d51f0341c0600d940041c0c05441130064098030444d801e51401c8518140a1465000c484400e50100c07101003110b00c8418902c034440c40004c1e40006080202a10306003003048903009401580c525403680c02c6582c0c1c0b124401c603010f01800001600298070000012001c4002c1d0b8800b401e1469170340790225070020100e5410307800d9400f43d015103000740c0c0850752403018030200d0306c5403a402c2811481c0400a61104000c1d46020b10100d50010348030300c0d517070740081081242040c112588000030006886c2c40e450 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 823934613 1250 823933363 823933367
    0x1110c011b200415050d0b09120a2d021b040f0e16050f030715050d110703030c0302341e050616050304080a02010e0304080102092103091311030106 65
    0x4100d86a0750042c0d0a01c0403800c82490304c008800c0603144041c01c4024010010f480f0309680302400b42045c0703a24016913140c42290440f642c003e00d4520550f0b104c84442c3e03a8511000c403401d00820700b1071aa244084510130003501d901103215043e001035072500c0c60b40340601e000000c000340700c0041d8020010f40344c4001101c5c1c003a000301303107040340b41c00b2182207480c116a508180301c001484454400e0b45074001010a001105c4024282c0715907010030302e055030515001c01d000000721000c106800f4641d07180410601d04142d03043c0600c0f10003460790f150550138581c61200700302455482035102210092644182c640ea4070480140541c4036030464034101ca546000002c91701007410038a8241d40d140540b8002500c000020f1516220f03450540d030345e01345140e50316250010f1a4001c0410002155254400b140207aa0204041c0000e040b0040005030b4600c010ae0400680e190384201003400030004410f92080c070350010041d0388000b40e06545110350424503010710b000030403800e851040d12000c0880081500c1c0d03 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 823935863 1250 823934613 823934663
    0x606080106140f0a1a0f120403050408010f0c091203050c12041a070807080c19140c0306041203020903070b1306110307020d030e061606050601090501110c011b 70
    0xc409444842d410100030007030141c00e8019006000d4850890400181001e0b9403400402461b0034070030146080070803881c0c01281010003520700307800250300400d081c0b007020001c3c4206405403a6180702000b14001042e030152005130341d0320440d480c0450808115042c94001c01c200c91b20a903011041d0b610551403c0101c01d8a90001c2c01070148080c40c564a6000100d000812a4217640e0440f828034101001e5a55900c1a03030300bd00c955901c1800b0304000c08540366601e40d05000c0341c2c0d01c02c41c0100c1c0d045007804c464034540110041035910941c408428400803805107815880060201d1502507591181c040100349461342079403000c00c0440e00003c0320700c024400300100d83c042d220696120b607185014141c20b0307540c034018480702075070084a240c0844000390107106840500c2c10f0280a41d41030195a24410f5204084903206441c4191a102042030541c0c0c0483e03001c025010909100301c0ca0110300e41256503981c6ca03261101c0c18400351032104a41194070003501240158400100001a8448a417030300580d = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 823937113 1250 823935863 823935899
    0x3061201020c011a0303120a1a031524012c12070e06090606270607060605041104060906080a2a140c03070b0a09021908070e04110d0606080106 63
    0x80044c41c3c2d0070301a5450080100c40c0741c031a18981d18000c075201c00b21544020147d8044042103185001c2c80c0032801c5d10188025141600c0d81200c88120340780c44407032401c5002440c00040f0b04900201c00000c07060380c0000c0801c0f102c6a21380300b8190781071b2074040c0c001940c00b684920350b503000e5010840d003610303000c0c005400c00c2038902c0080d54505548402040c0010044140c90171580054240310202c1c0b030310380e100300c00802d80c1e01f450b40c0103681810707a1003c10200c0d440a0b000b5640c0580701c1006101600b03040c00349000010554299074179103840c010008280c10a2801904100080034000ca0807420440c1c10180840c142009200f10014070420205000e05c600e075012800b00f100301c10381442000d0fa46050343c0e0380c1c407a924061407801c0c8103640c415096141c010300c1c144015070350341c0381c0d940542c64500b02c00403075080030154003104a00b046104e038034203a41030f884220039494810412000500c582c03594980c68506a5030501c5015251414002038049904000701c0340d0f10700200020004501d4404403c9 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 823938363 1250 823937113 823937141
    0xb0423210319140403020f040b04021c2f1602030601060305010603140702030f0702030a0b0408030907080a03230c0a0309050f030a08041a07060203040b010302120309030a0803061201020c01 83
    0x400b0406090030740751000514441812104203220800250400300300c800a031040003000055a0810503000500701d1700450703801c41c490840c0d6a00d20514694522a00a000c620b070252a1440146003095000c1c444103905c40e0086c543c004115181c1500126043c2c06070b1941c014242c1d846583c41302c00003002803200f4425030380068202844c000403e0b10310a2b82d1030040c83d50f44e020714500b42a20300404940d50028008a0309446412002008150001045405640b28042c1c4903071b01c2c04c003001c4c0c03a883e005180e0004900354010003110400260003440301c07170035115520100b14580c0e483c3e61161039103020300c1c42190300e2030166100c0c103800c0540c4100c2d58829200d0403100346d0740816844083c140c0c0c660101800824100d000c001c2030141c85145401140105403c4140c645000515602c071010f82e04103403411a81e13440328500600451800038088011064050021814590b442000036a500d190081c094a0841e000021a02e40e44420841d050180c402800965a80101007c0c40307009001d120180a0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 823939613 1250 823938363 823938397
    0x2061c05160e040c1709152409010609051c1a0711030702090a020f09060c0601030605310311010903020f24010b160209070806010305010b04232103 65
    0xc2c01c2c90700748078148401e0002d56558900c203202c441e0000414801a0004400f8416880030f42000011403110b9407050164013000500a042c2020200c14003c0903e0361520640180d8014000309900178821004c80d0801c984815442e0140c1084141000303c008001e40200455240310f0172007848025520b01031051691104012014500d0154883c0a88070f0002d45c08440007000c0f440d04e03001e540240054240c0c8680003440c058003403001072100d43c095050301e00c9541200c07004000340151480b440e9400103400c0c071a10011034440d0124005c0d440c440f08510044088210704800341407250342d8021005254500800c9a030780d99040103959501d00d00c91804a510401c0000c45000b41101c4203000760762030f590795560950b400c0c80c004ca0350701e410101440b034038041c08800550140c1c0c0c900488600506054445661500304100010160354058014103c001c0b4200000c01030041c40100e001c03c589884d0803220001441c0d800026450784803a0441441c9000c140c0c4800e02d0031270040000e0405020360302d4040 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 823940863 1250 823939613 823939637
    0x1a0402030c06030610110c06190906020c0109170a0c0b120603190b2a03071206180c1107030804081005010e0c070614010f05011d0d02061c0516 63
    0x401030384000c6030296003014040020501703160148444010070443d50003074608002a40d008100542c02c0542c04010110704e0082484400360071111082c0904210320281c0400c4402500290800f0010320420003040c81c8105100859607007400207900c515486a04010f065585551071181a0042d1400000c203112020108100340790004d44142049001d007203200c080300f0745403101d94108600a00d00003101d1440c1c007102c028100c101100703c0d440d84254441c54ac583c1801c5c0d000908244030a8511000103180134001c1c0016540c410303188592070314210b80441d04400307015040b11150b00300880740203d03204212012040041c0310001d03206136807500c021103054850300e03030f504800c1d15020f2141c40504251180030402e40501a07009044240c0a084081407281d21012041c1c0c003800709034448490561034103c1440650b82c0030705a4101c1d4100340c03450300e084140b50800102078180d0018003d2181c240040c0e8002c0401088003c0c85100c00c1450080006103040c3d450926048103075150341c400141c200b1495 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 823942113 1250 823940863 823940869
    0x90d0c181a0f01090e0406090b012c0c090303040b030919240219020706090605120112060b06070305030a20030f040c050a0f0f092f071a0402030c 64
    0x40300a040701c038110444161030420030701100d150441d0302e036410015074501c0418000494414103000d144500700000b813242e100e0a2103c242801a00480000e0700080d00708400b40c800400062244403000c09850b4054540d1041080544500132800d6050300010a0024500d0000405180315048000c103550721031400325019028201704200040086408012804d24542c8900c0c030000b0140c07421400510b8800f48808440c40c0b42c40f440c01c0c120050b8000602404035990000c10800286403a040c0035003895401d000b01e0a0300041401a40605420048600c00f8441907800090920300c0180246560f10b6942c20020196402121540c0c1ca03141881c04007100001c045400c09a454500420786045d038942c00300d80011110041c6c010364040740815000300301642c0d601803550082484000c40c0c2c0080c1d10b841c440c0c4001e00023651266000a1800306106214049200180c80240b04420010103008140e491000740340900030001e4426a04240484a407500c46016140a60f00803411100360380440420 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 823943363 1250 823942113 823942121
    0x7020606010c1203060909120f0216051e040c020706030c020304030c0909020f0301020406020a17180d500304063209010809060603031608090d0c18 65
    0x4290000b41e8119105000c1800d03400d503980f4110940c40c001c203005035200c840b0000d8a40081e820341d403030004000584459601701c0181c0c0b00d8503001d40045c00ca107400042c502007141030380b4810750f401032091100004204ac840002c0b84072042e4014400c1260900d08040250b4411650061601091800c144140886c0c000002da4046079400190074502904002c000c101401101078101d03000110750860301016902800504040c2c070050303005003115a0203003410981c001070041d00a04142007000140300080d10250160b440210554003043c0d40ac02520b041803401d002e00c0b8250701045a01800b0600d0215552003240c500600c080700e04540740450003407a09404603d5503076503544d33401000100071075030007810301200c1c1c5101c1302c0b513282c110605202151002c40d00c001941c91401000140700420b9030b04001c9194100380e110005101515090340440c6c0e4a1080140000c10007107150490b404110000040300d480d23003030242c5842c0000c07616241020000a06004915401000803c4111042c0e02841 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 823944613 1250 823943363 823943371
    0x2070f0b0916061e050c010b0a061107050105090d0f0201020312090718020a02210405030f0a03171302041814070303080109270335010905010608040b07111f05070206 73
    0xc26141e41c540308130020344440d40042000c9625540710704c01d01d40580e60300c00c009401005140c42c0c0c100c00180179050141001202d0300030038140707c818071211143d6210018881c0b0702692150003604911114001070b4998001c0d00141c4c100d0440300070401c00c43e07690100c0c0b4074044640a134004c01000000168401c04e07401844442d81c0180c1c0240e00c1031024410b02c05c0300f00555003030111294541a21500070a04080c03040361610401d0b40700c0d545240c01c1552014224490201a18071010503003005000305030003855023203000e4480e544444000d482400e91003081d001d0f5550000c2140000f03840b80600540b1741101d840103030041800300c000040c81015500808101c2c0000d80882440d094203292074980007881e00c8010344c2008aa09110700800340807048254054402c201c4a10b2540f403503003030f1800c00140507044000210305142c010040e0b01d8200d040241c00550102100c015992a03800c1121042e6545140303580c240300f50b010544012103000c000c84c00032540c4190502c9150b466200c00c0c1d907502d0043d1 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 823945863 1250 823944613 823944647
    0x3030f0e013e1f0b01020307060b011e0c030f030b01090509180d1809090c0303120e1b0901140306060d0c0e0103060b03060708060a0902070f0b091606 66
    0xb0300c040300c2c180e042800c40004503084160840404414401045a400d0006a08800c507448111800055184010305050300b60001605006800c0d00c000000e449010b0080c0042c64a612031419144681c080d043c00c0d0200c0e002402013075098159000010407401c015841680810400600c42050910901810b031408006131100c9141c0b500e49020702c010400d000707281281c204640059010344900601108000c05d20302e55407511324800714140d12452030000e038800d2541600e0141c40070001400c0c10301050490380c00d41094900c2000c00d0b5044405003407002e803130b94414094400300848000a540090340f06c0304050702d07910b94030b82c0c8494500f40c02c10701b403c0e8055415402000040e03074501c1d000045034802807040600404041e030340e00b4200c0f07250f1401c1e00200c4520f43c072191681400e0408101e800d030300843c40d240a0340b050501d000410401103581c05104038442d000203014081c002c40808150f11240c6c42892400c051a103204031946828800140442207407500c003002070900d1180c0000350140341c0c06 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 823947113 1250 823945863 823945877
    0x80108030a0509061207020601030302060f10050103090503070c0b0307110708070b03091005070c1709010e04020a0224040507080607080a1508031201091514090603190c03030f0e01 79
    0x8007200382c51a411070340249a00000400c40300d20204040038003107001d45000d400619040d411443c01030b0a21100418240401c040c40e400c100e085555800d121040b11300a003070015110040b42081400c0d440361082c0a04401c9c070342180040c04221900084d031080488d6692114501d809217a0306840e0b081b24418042c0030b9000322070500500754000029900b0a895404554144060324050000c0e0740301103d982012805010222040c80011008414261210003905280120800c0064000c0201720304140c0115800304401500600810800d040226a1084404607000300d224100841804031001c0710036001d00c220020703210100113161405000b40e038032005502e60f2010709850061110100c01d002c0042400ba0000300110188000e04440b51809170440d5150b0400e02d294044d5030034038201000c8064000801c00074004c004500a10b0f8110844601e95552200ba0002c0d291401d000e5140c402450b25203d0f0b8130400a2480c40002120700c00d44074450b4580000c0300c251004060040320344e02041c41 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 823948363 1250 823947113 823947127
    0x33e0c0618100c021507020118210c080f03030a0b0a0509041b0b0d0510140d08072a0603050c03040f0209040311030f18030c0604060f02010b030d030b1008010803 71
    0xc50910b00107112040c0c6825901107040d83c00040401030f204582110344000007a02406550340040908100b2900381071040700d080c0b810084845041002007070b0740850740c039004610300b00314410b81904010003030300d0300303ca034040c8122001c592a0380c401d903450301459141109219070381c206400c0c0e400031560005d00a42440d038482e03d4000f00100803840785200788101c1c40011407030400700000f8114101030f0540004039450700140e8100c480e059500b00b03106014000e01da010f8143c2d64074480040007503001203a60344990f014545440480428072a001c000000202000118040d18119004a5450780c0d0b09001d291140c0742e14081c1440240c40c042d00d9103990781c0e85440581040b048503074110344280341100c1030042d81450a0b0440d0064603401c03844840001c1c071481070f216084916403840c8402c9000d0f0039440c2070710740024490321440c0b25840510030202c01100200b8000c1d030040d4100580a000e035201042200e0700207005040c128030081c812200810943c04c850302c0307028003a05843d5040c00852400003 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 823949613 1250 823948363 823948369
    0xa0f080108060f18070530011401050f210d1419030c020a0c091d120909180a0b0f0c03100303110a020d0819020303040f033e0c0618 58
    0x2082d0703030708400c0c43c2c4240d04000410b51a42131007181c10340018440820728003070851007280d10044900c807c1000e82c1c14804030f901740d12656890181114021980a0300c40d242910110745621003c2d02040c0c812208807005588000c4d01240360140e00300c1035179a18015903070b004000c03e520f005500d001130304691444011003a00380a035100c440b012a55004403001020a980d400030b5640b80c07a040510159140d00c0c1c21800001643c4910788040c0a8030701606261440d40504a164010940110700c6400e140b004200c0d403103540500100c07415900b1081d104404030350300304603218660640352426800d80410000e000707061040c00b924003400c4800c80d541e07101407940c1c90485189003c000e8010081c0104604000141d54a8606507d05849816401d4881e055980c160022074a80800542550000c004000010f40441899101e0907414100540b5a09000900740d4105040448140c90a140481c0c0404100300c07130f00030f0b40304032800740c0125030100b034103c02800179602481c0941440750082002c14170141c0703 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 823950863 1250 823949613 823949641
    0x1205030a033e0c1b0f041e090c0302120d350406021603090e070201151a0f18040b0604050d080d020705030703080f0112020a03140c060a0f080108060f 66
    0x1400da91050802000700e1006003058107013000c455000e030465004030001d081c890103650b82c2800c221703410445a1408541541100910a0314102d4159654503480070072845402c480017442c1c0241c9511750b403003c001800d545d500701c1140c1c1400450706c0740d10382c85a48102d103819017040c16400d4821503c1040d404101c4038102c080640304896040d001c1c007500d114015180308411419000351340b0900032a1501c003c1c20360144018100707000711790601c4030380d2080c10b4400700f030300003100d210f100c4400d4030004034a0b003145c0c14007403422800304030400058843c0080b00382242000200400711020040d8488044c00c100d80303441148900340e005100026041c010a011401a04220b03855420251031f0034616941d490446d8428442100814240d90030b01038292a900c800c40c1c0900807007001d000045150390005002d490a03407200070b080145d05c074601d2402c100107100301c450200b000303000070303844610501000c0c102d442c0022050000520f0040001201100000e0a40c0103214840b0318040da80c5990840000039 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 823952113 1250 823950863 823950971
    0x1a13020d1b080d0c06060902030105030303130804090f09060c0c05120d1508030a020d03090f080f070b04060209040e03190e0604171f0903080105010e04061205030a03 73
    0x81c4984080090580024031107441ca650866036a007125605a2030702008951341078110a0417280f05000600c6103840003c22a5000400448403840c480c0c02894880e0f450710440c1c0040b50400e080a141003080c035243d412083e80c1500c07968050048003d031003000c80740400304150203030807a03000342603c19800d03283d02c0040500800000000c52140002c0040e041d02d0751055002d00e0540c0d200046c1100095030502000b135a000d0286000d100e80c000d9074032542c40c2458403030000f0742012800507451007032011690441c0c002d944d0101c003d1600f07140504050000b508514004c0d40507d09041c44908604008012074203100c0030121144540700384ac8000b281c1c90408400840e412100802003c50008861036a030304103611004000d1401d03210140012102d160640350812280d41400301c0500040d4201d03843ca410f43d082860000160501007000901030081c0b40e00540741d0076072456250003401408001028a4039894a09210780c0f004034990141d6100d0342c0c0d4a01c3c003500c0100c06484441c941c0b02c019030583c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 823953363 1250 823952113 823952153
    0x5030307021e0a1706100e01151d041a01120605090a15120b070216060f0305090304090e0303060a1406030a02030c0f0d090b0604020316080415091a13020d 68
    0x480ea44034000f0038844e40c0301103103280b21944254200042c020800f000038000c0e0041480c46059545003007004240840c108805105004103401171080030b09100c8044c10700d81c40010300c02c1c80341d800880d0b080c90703203030030000c801a0025a6500300b8001c40151402039501704c2b840580b0f4021582d03191241280200100742118400703003a5903038005091403804000307444481c0a21130a40c0e80741405407000c1c1c9440e140c0c001c010400500c00b00c0402405420412010b050085801d02144035681c00e02c0c100e007144540d030002c00e032552404080c0c6070b00e020008040d61046905907050307224a0340301ea41094690050b420070075800607040001901401d00344d0007554000c90004103da081030403906e0748040380d03045102c0c03404a581da922480c4080c410310b1116250008c070141c030300314590304065101c1188500502c1009060042d04800b24040002c200200940e0514503401000380201c540f4068110b003030704055609a002040f00400d0258450180002d01070780c0c010103810200c1e049543c0c8031950342100c28642e00c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 823954613 1250 823953363 823953379
    0xc2c09100b13150e0f060906040e01110f0c0c0910031502090a1706070e0a140a030602030a0b0307080106150c020609120105180307021c080c1504060605030307021e 72
    0x8000700035003c2c03003080c40c0094415107090b906080d8048000c010061503c01801000d200f07104041d110400510781006c02a60082185007070011114007415064903a140070450008003503401d030079044090404546040b05803214201000104850780c0fa040e0790386280340107800c0b010000036081141404821000145c05418107001c0c07c000f4480e400e69500000c0001c40040780691801c3c4240500e40e030042c140d00303040c0300500491020a07480c0310347e0b000c0c86446010080454001e6130300c00c640d940042d50702420955807481c2c00d0034010050604101c0f40307400703841485400304075404117010301b034169148003901c4450207a5010040340c240f40360203030a98000c20b0400030340c049520f91880c1ca0320700c0e409540002c50b02d800c080740d100b101ea4144a484440c02d800c18810040141d542c503c2d001428035080710009402c100904004200d0300c11805038607514882e00078205503603012a01c44900c1640034100801c00c055507030061648034890008000e42c0a042840744450001400088105101010f40880 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 823955863 1250 823954613 823954639
    0xd0803062e020715022a01020a06020f1209070605031902041815090902034206180906130c0512030714030702031c0c0c2c09100b 57
    0x640008210703048040140c2081c1d20500c800851507405009084442c401803801904114216901000c000c0425240301c01c813540e2803116a1003003084030f91740340e00110119030303d60848803408940e80c05180d0b1512100400d100007098140089034600407603440c4d8a501e4a19526207a200c442d0010a84120502c198280000714107982c051440014542c01e1070b0700000c0c041b007140ca03441c0900046500ca400c3d49420100b01000580300802e2144081c0c1c500d04034800211a0b540e030403203607405034140148840d00311491084004064401c0a0b004110a0700d40920240150a1078564904120383c0d2402c168010382c0442d1503c1d20300c8151001160080c0030182e01c00351100001241240514401106a4000303e40b910900c0400b150205880807610003d61400c5040ea010944a90110204c1e0801030100c6017001d1080340648241e01c000c1750320500c51680507031604621085092002a220111440711a20413088000f80300c440b4024008000248003540c4400300307210140c41c81103815034020305038034420 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 823957113 1250 823955863 823955929
    0x20c060106080105100e1c080c0c0f0a090e071205060a180309030f150507020f060a02041a160c0303030603050d020109051b01030f0c20010b06091e1002011a0d080306 73
    0x10051523842410840e99031402085050b14040450b04224400c00415210418683e18801004100d074505078020494800008610341040300e15441003900d56200d0050404000303020076860b100c0c9603100004c00140025131f8090038008801440180440e0a102c02800801e0000b8241c00341c0302e00c25000d0010007141c018624080d528142ca2032030150f405500c40900c0c1000900c00568800e100e1541141043d10b40001800e006201403514148040e0001d03203805003030074400d80e240003545c000008441c0d0590b00c0c50010010481880207503001c3c0951032001c4501841802845845e540007002000081000c084014000d40e030340b04441d05141d607400e20701c040c0702c21074050001c0e072002980f25040070009980c0280e00040e50b007401414180d14181407555541c0da20016546014000c0e5201c000c614035410b4880c07162401010f01c03550004c503001030480340302d0341500b014821040b400d010040000642c4240041c0c1c003a540e41c020410641400002c605007001c420104100c1514070550010082803681 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 823958363 1250 823957113 823957159
    0xc030d0c090603060b0f03150303070f122721062310082d0a1b0519050f010203040e040b100b0336030d020c060106080105100e 56
    0x40c150200300c258404104071505072003503d000304005603940749403024201003144a84002403c040144504402c49130960310f003081038496640c2d201100c0c1d0203806060a041c4c19008211466000140002c0d04122207504840c2c071a003210b800750f584005c485800c050000c626588040caa9070b080c0303d0031401c5500460608d000e0301e0582102034400c1400306d440c00685044507800201030264100110100b080304410006602d12088860f124100c50030841c890951018001f500b604401031040c030420300d0500461002c1070622981594140011a40e25401c0c401382d003901c54a020a111000782c0100900c1c00c0100300150003200510641e0301e400e80f00c00011078500402ea400341e03425400c2d00200042c010700c440d003070005801c07050089401c5261100508003d06a903c0c10002810102000030b00c42e40000261040c1c02c480401c1642c1e20b541d0021107500094103c10310208003441a1300c000111240141000d9043c0c07140036040d0442c24101e078109507402c2c100c040c5d0b5517401811340c80440706a8010004 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 823959613 1250 823958363 823958381
    0x3060311040f0b041d0706030903020a11010c02061b011a06040b090411030f0f10030b0c070f0c06030218120c0105071a010e04030315080d030e0f06100302090c0403080d020c030d 78
    0x350504100d178015861820005070030100030315107000900400b07e078001551400700c1c0d0b4081810b050800300e01d80120b40c0310b190104001d41101011643c0b00a8400c000e1080c120001464000c1003840c00c4c1503a03001480454042d081e4000c5000c203c20705c1231240303000040c030740000c002d800400c01c4404001d802c1603561044400c048194284820f201c201c00000600c6078011303207452071200440c2e0030361b298400b00b00800390849980d4180056110204800151920010760304407141845960782c8005c0600690701c00f031000c000400d40703902e000e04503203416220300841c00b844200600d0386007081801542c1d2540401020b44911944a2216105180b4051014043c120f181c80340310702810540f5000d81600e001c0c1c000042d602110b000103004000c800035101100400310b140c045141d00c5003d448500340039118050444c940102c008000e1004c88c0d150f01d420841e4829a0b8102065079485d120014034000c41c000204080303010001e21803118081d401505141410405a07840e040c800151041100c1002c4 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 823960863 1250 823959613 823959641
    0x6071e030b01021606030506090708040b061309120201050711070e0c1605011803090e04151109090c070308160f050f0909040c081b0904060c020703080c030309070603060311040f0b04 80
    0x42182e541051441c9c00e801c00010b003807804850403d03940f000040710b0000c0565004a4042c6030806d4401038035003040c1c0d1801c2e0402010441031140c0c0390002d028120844141010800c01240407280d40000202c40085803400c0300200d21580366088070f008182c1c403d41e540107410b0740c002c1490300454001e00c1030044c5440501c9070031075076080314680508044403076845544c00d00078134030801c030221705607074001040e01c20b8011002030302c1410049050624041d03100c40360f0f0440c01e40390030003400d071900b03100824600f03000307071a45a80742d41c2c0c5c0d00d21044d410301c403054203400140010454a00e1300740598040e2103c290300c40c28090410000d800070135031500c0c080742c00342c0f001c4020306010800d0309000c0c0003031a000940416030a078841041e00104070601c1002d00001c01c480e66600d02e884c0110b01c203112420243d9881403127283c2e42d0000c014159565041034440d06c41a0140b22000a000781c0a0b01c141e8084030750100c0c480c00009909404c006c01401c20300e42d041d0603242c54a9204000783c0d9584a2442144111 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 823962113 1250 823960863 823960871
    0x405031b060106030c050403020f01030f5f090a150c090e01080c010e120109080714011b030c030e03160507120b180a080d0603030206071e030b0102160603 68
    0x1201004096518601703008040c04000c120520141e111070701c80c007500213000c6c00c010074031784050201040209417075100c0d2040749001c0101c40310307a100035030104444125001d00c0046c030901841c6107018040d009900e8a4040c015200d000035010200c0c009940d8003801c0f0809545040754103490309144061121400c4180a07600c5409039a0950080161400340036603142c44499036041403071860b82da81010308080e0520643c402e003100fa99869aa0103e051607000000f07000c540c2c021318214942c2e4105020480310694100072484800105100703003681c181c4d1507803d09180e81344d00007044d001820028007581c00c00d41c8400d1400604c5208000030001070700022400b00481405060840c10080c4036040414501c40d90a140d001003100369044a421030f414004410518030b40c280d07854604446202c005040620201e85462480307196400310007100c0c00f82d025588169070b0b5800c212454602492801c04540c003098074246610310070751010360780d0107043c0115001180c140d40740c04c0c45d071100c41d40110b0010740c070307 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 823963363 1250 823962113 823962119
    0x14070b0a051f15050d0b031006210804140103090b0702031b0c0d300c11040b0102150601171911040305030a0503070504032f060705150405031b0601 65
    0x100c0d09000903040c0d061421150040c00c1400820078030702045100c0080141c085030800c0d0341c0215500c46c002c440001021900480055050348015040611810580250485402010030f440210306801d00c1c2d401090b044c50141000c03010740f50348003007001c3c141c101662411150001521810038601501c4150010f588404a054441160350203c45100156800c440c102d00c0c81a22044501e001181c0c0c4041e013225038840300c00003405004005005001e161540c0740e00007036125001030000380703400c2c000c03100342c1e0240c0c103c803090206031031010b446280140c0c019102c414000f500c6035600d0303800240524125800e42a1044c075600150b80584048440c1b4458040400341500c1a1244c100f00c148000451401c00f481c6844031070726409076200040500c6400400203d402d8480d0301102c01455011203010036440c0c0007480b109400002042c2031045402c901c0a10a1506e4200192009250720500500502c440c100c05483d0030034010700102c51500c02800300c60b1404003905044800c40d1744001c01440d0640c5 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 823964613 1250 823963363 823963381
    0x91b080c010302180609060f0f070c170c0d06020f071112010c080705030a060f031103060903042105030c060f0f16052215090e010b04140114070b0a05 66
    0x6140d24a03041c544104003074001850030b41390080c0215411268a500c485000300414420b114141c2d103440d10a00c001185044028030320060305115000d07000407840c40d0b0b01c9298484440a44084902c41a40300c6000d0248034900741c804200082c0c0300f21405808c11220b42d021a42c1600042801c6481030388115014441707003000c461140c044840c0f540203102d8003035024005000e503c000f51000d402c014000001400e80401a0032410040c040e005402d0303042a520700741034a00550201450344280244004210b10342400800d0394169403560103a5a1000c0c03041811101070500e07442e040381c4501062005000b01e84090080a00c80c0342101c198121910b84090001c01030742d0000e140d281041b290902c99000c2c50751102c1507071484544181040c1602d440501c803401030760400c2d84180780105000e800461419807100206046800c80e20401c2003690720744002403100c0c0030318020001605c40c4420542d020758800d03071590728a1760301201402c2c541640d9441e00554850201c41040190f0b8036a41407003607140e = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 823965863 1250 823964613 823964623
    0x6030b030613030807020f160303120b061603030f1d100e0a0f021f020f12030402031915050a0b10021c0e0a080f1006150807050706091b08 61
    0x45085001d00070900e041100d00d0002c424100b005020800744500080240c0d00812036202ea03a010302e401c449000302017000100341488640030803800120098819204c1488a00480d50110700c0180000d007007203803585000c4075007007800b20f00742e04058954081ca104103030f9921581c409030003007001040d005103403140030b03c0c03138800c550315120f12075031401b1250821050045400210154000c01d080342c02d28a034000a000340c01c440b10485000180300c6010650300390000b49100e540c0c500712080d203c2c02d03804103010390017500bc101c502035015009840c01c80c02110422101100d59480744c00307048003403600c105070b000494008a600c4051300d540c40d80d014a1510700306112001000452004291014001c14940191071401140c80141b061021144202c1c1c0e8400c0369110280c2061811100d5095061144950342c001181803042e0076454068081010101c680ca102d4070b030480e40d02c40c1c980c41c1d280c6101c112042e5000c65000d9400b20380e2100140b000807900c518203004010041c200064841c241000e4030304023 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 823967113 1250 823965863 823965881
    0x7030c240f090302040213031a04120c08070206031e0106020708010f06181e11042321160303050304020f04050907050d0f060c0906110303010e0c1c020a090603 70
    0x212112600e0201100d502c580b070b02c41565810340300035845603900402196900540c0e00010601c0d030060207a4100020600342451103640152202d510a00c0080e40c2078820204064003d000201c00f00000005030074200001c5401550074410b020610707024035000502940203030403460058008e413800b0080280300b406400d140040708541000b801d0310300034030403004e5110341d41e00d80121034491010281412207080f80c1e075805103040c1c20500601052104c00c490551081c0101c181040030310009002125110741c60440700306010b48500440a106180340a01c3c1186d102484a40c1c0300b45202030000c603a000c0c141c0c400071880b03510b401c1e4990415104002c5000889000a8003a510309002c00140410000703000b0100c8030b040d1228001c0c41164145240c1a407081040030f44160304055401e04120b51100c40d0204030b4040341d8402c030502540b1151292288001c1c810825110b24000c00b054600144900811075007007415542c0302000d5083d00107400381d8018401290218000c0002040904d800d0700a8800c0c3e = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 823968363 1250 823967113 823967117
    0x50a03030c140703030b030c060d060e0109091a04110604060512062b020d0602160201110a08120c09040c02030408010c030908120c0c100911010e150c07030c24 70
    0xc2c2c44500607060740c0b809010b0000c2c0c20591150340041c0251020b00c03030004400c2019061954130100e0f61000d4010f02628400d1201025500000003070416151041e038000070303402203d0300d45000c8020800608480c011308240d03201b03c084000c01019039030b5100148002e10340380c1c4840b5210000102050080e4a009007140d01030080c0c1c000205510701c120516242c40c0d07290f000703180d0000742c841c0041040c0b0011184000c141910029030702054200c48400701d107941b0f02c00d90702c44040034403440500d501c1d4691224002c084107014040c40c007000c039403858002c1d84101460051414001c01d1000941900c081072809009030b0000502806442020701550710700c0c400504003401220700c2c80c5d0342d41c0d5039803250368001c20305a00058040780701440c40508448000c0501c4040b518031044124007100204144401100c00b00b01c0c0d2400b01d425540900e458030001034004040d03031901e0001400509403075000c40e607a4003c81c0582040403000580f03000a01000c2e001c0c900d174a120481060305070000941e0300f0444001 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 823969613 1250 823968363 823968377
    0xd0902011d0907140408011d07060c1106090103141501081623041806060906030902130506040e0a030c021801030b071409060309011a1009030818030a050a03030c 71
    0x40326240d102c070300c603000281c91400c02120b00c081140c00d80c0501842c0c10080255003031070504100407821561034004003217088103443c01140d8487c415200b00040c40402040000001c894200906e0501d0103060741d280181008204901400040c10345441c0803222151103501140c2c0f9041156445000c4607840584c2d0441d003911201d074080041c100e07000c5180c000b04d550003043c240305e80c010066000d8a008010a208004018042c0e500840141441e030003841c0c001a8150b10008900e44680103646040707401402c500d11601c504130350305001e00350042c00ea6400c44d403a4640c0080d00081000a100c404d8025510348000d04003a104208114145510003a4070240c1507005001051102d6800d42d0400400d01b044402c54008a0b1001c419000e00c0340b000c7d61001020082040c03500d0706400040d5519125080e40c4c0c2c0c1c1c40b04010802841d10030421500d400201580710520015203080018001a24500b4080840e0380c007900c0000d01d02a4090404c540540101e41d0324010560140220705404000d41822030f = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 823970863 1250 823969613 823969667
    0x170406022505060406110f0c06040506031003211b05031603090b0403031205062b170a2106050d0327140a050301060f09050612030d090201 61
    0x25910400c81c59454024028614010784400601e00700d0002448042c110b01d46070760352464013801003c001034808580b8041c5484e5604004004117443c45601c400034207090620b400c2005208403908020800140804943c101001041c01144a1980d10074140780003901105101002081d24160304441003a01c4155108200016400300603195041034030301c41d04080340d48505044071445030b5640402d00c4c070310b4001004002d250b40040d902290160342c10003804207440b01804e110925040f0340d42032203d401c49034018001c0140031503241201c00d005003070001c0e03080001c0d12146aa607001c14182c3e408030388a011741c440c0d20070b5420381110203c5001c00c0104000b91600c404600e80c40070303400c80181001180724889200e140d00c03c80150303140004c101c002c0b040c2c5482d03c0300c5040d911214035040744604801c9000244501d4140640b0054600d00080441c0345850454100080c1001500c080c0c1c0c801c001c2c0c0d11400c08420304201809000c03051240c041015440c1d0300000d0b042d0074600410400940d03175a0410 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 823972113 1250 823970863 823970867
    0x10b0a0503030f120403090308030f16020a0b04030f030e120405010905011110090215070606031e2f091003020a05040204260f0a0f0203010c0302040602060c0a091a07170406 76
    0x24442825254400007485d6450785400c075901d401c00d420040c100b100c08010b002c062400881e0880c4110005000c0b8500c012100000340e03540c040f8072100a1050701d4003000a000248226055480d01805040104420022080050070840140308040b400c180100b0208459a403046061000384000c0c2004150b183c45054100e485210506001d18115200e1011004545801e03d41e0f00c2518280b02c1402d484890a10f8000c01601061006071000c0300c0c207400220303c0c141d440ca07002c030501da8840e010b81d2004c655842844d40803a0140400140d03880d01000404082e212005950721071046061031400c080c0c01c0d803041103009205a0082e6009071320504c401c0c041e0000002d8072504000308400340f003540b00203501a031842c10f15407450f08296405056480400c0000000e500385013039108400034091002c80300c80032400c030701680c41031000590045000c1507130780644100034a0b49024500d49901c074251070f8620305c01c00320850f407042c0600b003000050b808207101c0f04209051650401800e005d190034549400 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 823973363 1250 823972113 823972117
    0xb1e0109181a150f220b0703020f0c1003050903090303040b36041a0333101503022a1504050d031a0301090515090c0604060c061d010b0a0503030f 64
    0x190a80481d40002c0c1c000043c41001c516408460642c3c003445c101035243c555501041d04580f608501500c81c200c1450310407000424025040e45028107a2058440b4454045018240203800503001c2e02040002c0111030304c091008001a04901407541da440b4500e0403040034004518201100350010f02c01010104828003d40600d1490300300c5011170131020303250b0b914094030b45080344142e0510030000f903104042d80d18480c0030b145110403000820344540c01016040d88140131106454507034003447e4140004c40d80c1508100044610345001828031030301d14080003019240340710b9880c0c1401a01c008041030101004107464001d112030200b11b0324101982d40595803048118040289500c8408945e0042030108009284050090091000c4111402c0054076003050001d590700340000000020805080050007030505140a00b80f80e15140c58134004694082c0f09800844401e501ca6290004090200310140207001990f1b00001d01c83d40d02c1c0c8100019255541d1000b80650014050b400c040200101 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 823974613 1250 823973363 823973377
    0x1b0706090e0f091905011a0105090d0212161d0601030c0206010e070302071532060409020607050115290f0702030304050901030303020d0f0b1e0109181a15 68
    0x28000c0741e10344410410300d091642424802d00002c29142c030b050700307121741508403048a142d1151030340d980350000d000446003481920040743e007011001000c0e50050404091451503440704409071680c141e0303003a0b110300944100e03a008858000d412468006100030800b40c0d80e401c02d10900301003001881e9800c010303485200512610302c089400000240d81075010707404032740317007964001e10a13101c0c0040069064001c141c6481004d5018150b489030303000310351b442c0440f5490b0ba042d4151030003850343e0303080c20171010740507610089030000c07024482880015001d0123040702c86030501e84111149401d105442c100013030030f00a08061a0921030000041b182c49400b241d141c844000085070307543c11303d400480d203184903e40c405504441b010000009042c0d00d5401307442c860000c001d05019903107070b944550058808c00761a007940b00d41c201c407100d03886600d8401d400d94480018105161481e5669a0380f42140d5400c02081c050a616082c01003d010300d0803100c03550007841240c040741811543c81d46204280140c403 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 823975863 1250 823974613 823974631
    0x118110409080903030a030f05100605071104090b040501050405120324031617100515040b0414241008010302011409030303010b0403050c1503130303111b0706090e 72
    0x1040c4400e0000203012a2042d86000c0e007229510301b48090010000c2c00700e69440040103160201040328050019150000c4541d2582c4640c14011785032501d591990300e968a16070710690382d00406000520750301c00309110b540510000a070714505400d0060601e607461044050084080041050328001c5500d401d042c0800300c81d10114001259000c2840c04402207604c605600c0303244000030700d044e003414074240e0f1082c0900c15034015804207003443c015103100b60b804003621013820400076901d0809610960307020b00c004002103144803a009519800340030588201c100300140c450800d52402802108030320b500750581d905164221200350052911f032040c00001c5c10030403034180c00060781e004007040ea0f24903000101030340d40d80d580d00d0b41d10321403a500c103120446042c040c1c160104041d1401c3e00c102c2d818026003010041c5940d90700f178821a25000c1c8240200d00b41a03403401d5028801050b8806803140d06502c058040c010002c1104031450109a58001b00812075078600078400c0007185000d60390004481c0e = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 823977113 1250 823975863 823975871
    0xc0c020913060b121c020a03020c10030f110904060506030103081909150c120e0102060a0b0307080303040f1b24030902031f0b03010b0a05120309150a0201181104 71
    0x2a2900c1c00140c888210010380c040144c01d0b0700c132a003030000325405818010258a1080c0c1d01e121800903030304c1d40401e02c0c5c041d0150304000500c03116130800c0000b81400001c42c3c6000210300e640096044211100d4190a600c56003000c01c2410755800c0c0780c8118000b40070211100c81c255032542c0d40351422481881d1121b032001c44001000c184940c0100d4202029003031420b0402c0c000e155080c0c001f0204991504142ca50000c15041200c41900810300b0484145040c1d000d400319a079041ca103500034005003030705c02d50984039810b00001c400c01c1c14005180250300c14031508408000d1400c202000c40c00c41c0c100190302c40c2000d002000300d480d542c090143c5800c408400081103000c60714064000389021b11000c1d4160141c0c00803d00341c00041d03450400d40f88005c140801001c031f5203a00741422106005000e0350051001c1006111600d440f0b14640b1300a00c020301140d01d410310400109040441e5107518041d000f10102c0c600069075021300509203180c07900a1042c1c1004281d49032002d400d40c0b64108540219a2 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 823978363 1250 823977113 823977151
    0x60f050f0d0204180c03080903191e050321090c010516060b0a0b0a0c0c1a121906080706020c090403080402060d06170705030717030f030c040503010912030c0c0209 72
    0x80c400c04000d11604410030004c80e9a0b00c1c00e002c14142d00840c0990f11034010202c2b00b05c085080d0b4500d82c514160050000d580b40e2800160603140400c1612082e18944014010303580a042614968111603410765640d480b00d00340024602d19200c010054241440001d1006a9184100c0030b070800d0001d40140700441d9146149000c60300c5c040c026040200042e0001560191468000340101a803902c101d00c8080102e0352030180310318810079101200c9181004103d0756000354880c0442d15008400f03000c0004c6003103284d50318241201c85e02c0d80182c4450f0000344040000c65014030004180c84000e4402210920303260740d00403c1504002e000912402000c1400c03540540c69501a10240c0103081c4003501c02070305d50080c0f9680e07501a1103181c1c841d2241c4100070407105444c010824009942400070b50510668015006942c0c0004000d4100307002c090000190b2079a09001c0c000c80702d401840403180781c825004005003520508441001404444a03150300103031a00c82400b54403458043da01728181030 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 823979613 1250 823978363 823978391
    0x80c0d0b1303090b0a2a122706110f0c010504170312070e030d02030708030a021b03210106050901140a0201180501061418010302010804020f040f060f050f0d0204 71
    0x2200760031a002820380442e21040040d004260491020111303001104240d0094601040602c07a80d14024041e800c8061001801401500881d044040668483c0505400840384e0148d00f039080c2d00c04400100c0048202181040a101c1c1a422290f50b00240100502000000c1e00602c194032810b010503005c900c12503200c0b03d0034000d40d00088030390380c02c40f6454107060030000c01d01039032144164881d00030940c401d4201c600000c00c55103000c1d44002110700399640c005022009400c10419180c81c0e00c6982c604400c0a1010300007080440009141c44000c4004c1e40342c0d1141c041c0050700101c041c03041c100034940407a80c000100160406486c4005680c540ca0608120f0140602c0c02c1302451080c0a400d00380d04101040d00400291000242d09a8a0007c007200b000800c0007610542c0d07842c00645d200500242d4807425006900500184c0301c05212071010010030308030350200418401183d9075880c140007601842035104020701003100c0650700c1c4181080018104946144000d00ca01e80e561a070852000e = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 823980863 1250 823979613 823979627
    0x160806010f120c120f0903080c0310080706020a030906030b0603040b0a0204080a0f020312070c15052106090108121b0c0604120303150e010303050702040f05070207080c0d0b1303 78
    0xc10401014440000504805040844040c8076110401e0400c1100611780d0090b03c940800b590f0191f64400303894a8444421240d42e00281c0140c1802c08085004035140c801008608000c2610340c1c010710045545080042c41c0c1407440e044201098109180540d80703664580659801541002d001e4010351030b2030741902d009210301d40c4140103a00a00d03001d4418410040142445a0f000b134041d80c0141100e9100c40b680d5100f41080100081c11141d01030003412070b01c190003030b400041c0303040c018074050303450b5075843e00e03c01e0140001c40c0510b8810100440c60070071400041c0181000c00090120a5280c0304100090150245201400c500305650600a507020040c8040400b4081d1425070b485d61901ca103640a0320745110306a021030306100200715100d0700410317084111a4003c0100c02582d095513003c890503400b0180c10fa0f0b0007600e4a101b4160701d200c0748a05402100c0640003004000e21b000c15a504100200e50001c4c422811282948040b94003d000641d1040d210050344c42d00707102d180b405451013 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 823982113 1250 823980863 823980887
    0x11090a03021c06061502100b010c140316111002120a1107030c0305030a1704020303090103230a02130501030b031c1814120f0a150e190605160806010f 66
    0x10300c0c1070084c0003989120f43c419007110842d00703600391210344a420030038205941c10b4041250000d20131410100200302c6441c40b04007648984001c3d03d1610001e1340010340c603d03400b2181a12442c0750040e48001c54500a0340b100e001e8180d50001e4030b0910644500041c480c012110683c0c01c0c041684072242d4141010b01490001c1c690111a120b003650300c03801d0469507504900207800106209404003154040640f182520403640200190700e842507a03070044002c1d2032500d100c82c2098845e0104003031803038070010080344249ea00c2840140c039640807032010248000d00e80d000e01d051502c1c1c601040e03c02c1d100400c3e8a448521220b0444c0341300051080200e91230f2162144401c12410306e48000b240390403140c1031a00000d001201d20500e442c0d5010a040d03110360aa0341d021078070342d110402c1100014001740c2c142e014540e03054400141035640101042c02d1101e05108030441c00490000e407020070110340300311600000d000690118000e41d6100140840d9000742c0468144802c035121600003d201c2d540c0d00c080 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 823983363 1250 823982113 823982123
    0x20705010e010911031c2105070c2006030103060506030715020102040e010501050309030a110f070303081603020c060f061f0305040215130528031511090a03021c 71
    0x1e94000c01c583c902c111043d4015004041040c030300011116410001c0290b081e0700c01c002d208081e201d82081c1da0703114183c0c0c11901e040201140035441000e100d00400c1d1a0003005050030710307142c02078081c1c0b801690380003001c2c141919250784030201a641503944c0034100180d103840d102c00180ca04480c07a07000e140801003801217007280a6041d0082c00172544a029a0901030340c0707400040d10075001c106d8401080340e1080c040c210076144282c000c0860380c050801902d2800388030304802c5007084456001030300460205000c0c0500403200d6000100c0c01c0303d15140440c10a40c500e400c2c9600c8581c0500300d2110304421201203160350341c03603d103007003119001c0f000282c503a40801d000180146c001141c0c1a44500100b5000d50044817100d822a201c3d82c92007482d64039424100810030240421901d00700c0c585500c1804510810b01d0140c1c4414060360089015002e00c000181e00c0d40151a804070303081c95114014000504907841c0d0020240541c0c0c0d048034044010080c410194115800c48280070345 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 823984613 1250 823983363 823983371
    0xc0106030605042001080114060d140c1b030301030503070321021c0c0f051e0408060c041e030503030105090c13060908010e010b1509060f0409050610110a080d02070501 74
    0x820054801390306504031340d41031500b80d11915058015600c042d030074410070850a42000aa804614000c001086007242d0b40034005010340800114256114045640d400c45040001d04220300d01446219100e209018000a52a5604507a41c0d6503c9000e0140d0050072302801c46121504501c50240041e140000102c0c115221842203c40c10b440c4012003404442041c503200103d0303100c03446111041d00d25900382c0c446900d44a01511840c0780901d0b850802c0c2c035200014040410902c40500416020708104511035441e00d09045030700740924246110400381c46901182080010008001d0303904540c02204c2112195492449410041c85480d5400010318540031f00800d0b140c0c0c1102d2104141c44164008021013520011410700300e07134401e03104039404039828002a1440300090002c240c102400741c01141400d50740301c42e0082a400c039030400d80d5416150001c0003454181544415101c4000b450200410242c42c0001c80d151000b2010203801c1140003d401c1c500d8200540440f405076501c100200 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 823985863 1250 823984613 823984621
    0xf02150406020a0e09040308181905060411091618080109030804051e070905060d0c090603051c1704170d06030b06060c0318130606390204020c0106030605 68
    0x5009603c01d4410801040e07075103024116074188001c445218907496100c0ca503003a10303098080b00c80c400d0501810201481210210000101c46809504901c1e106000812103800c1c00d141c0004101d20042e030f41c030701404501040104103907540d00c0b881150b605a05140e00d444d5240b000800844d010340d00552500c0d8200100042010391001e0164030a1707004005580c0032148215690f02c6025000340c500555522155050200c4491070b03020b90b4006000401e40d4441101c0c654444e40c861141d588503d0466554000030006d0203400d04c41762415040045a15680e0803080390041c0c100300001c0c0f015440340d040b280c0020f0421030210b94000c0c0842d10022815224500ba06408000d4945030104031101180f400100c1d116080500545d030210080b0300286081161442c180c00030502a00c00d020342c40000c55401c001035804901c6680044c00e103581e10320074100c981c1e9448018038000e909001035094184680058020452400b000200c1d5040300c015944541b2602003501402c480e81026240924002c144 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 823987113 1250 823985863 823985873
    0x40b04060b04051009020c150c0307020705030a0209041209181a0301061401051c0c03090b0f0105100f020a2a0e0f0a02030901021e09030f0604120f021504 68
    0xa109510540041c00000c0c2418140030944006a0315000e48030a00b00b41444003a6140c3c02170300d040c0c80c03000c0848a41c072030f181c4036288460000f915804260300c0000207103d40c01d6418044c400240c20241d00070001c3d07840a130301041c43d04200030000f6108529114043c4074291003112400010300d15010040f4ad4241c0103100313040100030108191800c42584c005503042400c0602501080740c0c00d00180306243d18a103001980c080c3c0c015034008001d45405848554000345500c58044030100b5035400180c040740601d010000400050b003100703991403002004021175a9201d01310076070701041c0d1901d810040c0415006030301d814185140182174190342d05072440818210b480d0250b480043c00140c101a541c5c80c8540000010107541c6130150094190004640d03100c241c0085400c14125400145084d4482d01e0489141d56030b10b4408606103000100c0103010300e01001048800700c40540a400142019602e000c800f68440076200103024024040c100303281d009010b103003400b281d141d242030084c0c546440c1c1 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 823988363 1250 823987113 823987133
    0xf030a020f1c06080f0f0304060809120d0209040612050a0303020d020903030c01052d060f0a030b07020d2010050402010c0f030c0302070914130510020a050301031103010c2001060b0304 81
    0x2801495110301c0319950512840041c0000c00d166075040552310305400c03e1021100d03440020000c1d0940e12859407004010100031005000c80200c545006881d44a0002003006640e0280c4c41800300300590507214000c01c4021801c0145a030b414240169242c00c081b01100180c081c14262aa042c00040303500210f424040d04403520461000c40c03c24164070034100660b24030308580c490340c10201e06203000501c1504251074184224070005200c854841d96943d5140e19814080360b5240050304040b00d9680c40c90340140c440034a14a070940002c0303504031040d825035568400341003103c0d04d01d03483d100800c0569004402202800703801200c0202c5001850601600d02c80c10b000b41103006210b1800300181c81c0303285100b615062102840d00c00465151960300140e181c00c0b5100540e018011800621406411440108240021a1500c940720340c91428408403100e4034114203400b0381d06042c0d0b24010142e2040801542d810b1501c0c084100400900c5a40d00409103608400483d03440002400140402100 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 823989613 1250 823988363 823988369
    0x1241d2b0606080127050c0d03030b0f1e01030203180303010608090f01020a0801140316120c0815060d0503070204090303090605160905040222060e13020f030a020f1c06 74
    0x6030038002c199849034820f080790b5a4880c0700300d81030701542e810f0006070040b031440040e080c0104125041c02c0d2021001848082ca1944202c02080c0e40b44000e060310b0038103410000c1039510071104c01c40c12007003100c08480340c1081600c0b001e0415600100007444004220204001e07414034004603900e96131142e6015048180c1603e80310142d22841075001d14000c0c05000312250310001c0e903035a08259103048820300d105103806140c0d80c0d150148401c1207044a40d42c0d40183c000700020302d01d02c002d583c00d0382000c10700d144207034014801580249020382420b11240141a8000c2401d42e50054808400d0a025045015600c2c000354804d041400260506500d038001c45181030140340200555200e204a0880d0700300042da0b03e901140c140d0304c0030403c134a41a40035200918060880744040c10014568840008040d006000420420406c4c0d8505e414101100300120340c807554214589100c2940d02c08041c00001c150b000800e40001d41e900418a20f80c042d610750340b244951151014040c21841b50190450340 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 823990863 1250 823989613 823989623
    0x1020f0a0906080f0411010305060f1806180c09190b0c03041d0402010f0e011709030a031d100f0204180608010f0606170403030603051501241d2b 64
    0x10200d0440904044c105000b5a030049241d214040520700641c05400020071495028040d15a09410707134035041d20a0700d820099074901c80640c0351580c03c00855881032075100c24904038400422040b80302c02c0307040711044402102c2042c00c810880c40c0c1d4200200841c0c001034040400030039208126a0000054010341d081115640350000d4103080111940c0300c104e402030f00285006090a440038069002008038a006140c81d00860040391445070b514442a1503503111035000003102002c0703e90600c01d0781890250034940001d007980c41c01d4001da49526499a5030002c41d03454038201e40f603409943c1140c1c02010802c0a54150380b8610f10b00c3c0700280100d100b40901c6500f8501e01d0400d241031403160006458058586d1041d24144c114109480358000f0030407410f00d40e0320300010020600400c14025049481d0506c802198106a0051480c4841e13105036560310030480801800540c00c84038902c660342c81000d9040c2c140c1c0041c1c0c00906542d1005c0c050401000c800c8400b6011840074240d80d840da20300070 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 823992113 1250 823990863 823990877
    0x9031308010f0c0c051c1b0305041508062b060c02010207061a060a05031b0301030506071b120807020c04050108010b0a051e100507080310051c0b1801020f0a0906 71
    0x20403080e140741e944d90300014180d8000d440720031008119070500031050107040c1b8100d090020343d0184024070860444081d000f00e200414100b0060f00355028000a20405103424881c0e8140400450751b11281e260746181c54460000351000900c1e9030400c1e5100c815009403003070000038400c00b4080e000350300140068800304c1c1001c03404031b001449a1360801c039003c0081c10031898144125002c4410303400151a91030584160031640d9102c0c0c1e10040950701a50045010705498101101c000e043d509a20584021100d11000180c0220b20110481c0c00070400606008519941d101d0049082a450062140e401464180042100001544020000d61040e41c00c0458031792940c082114908450300f0754005d007101e036590000340d4142440c0340201c2041c542000c0b4140540365903a102641c00071640705043e0010104200602d240020303680c0a1103454020810205030562161030907844000e06603025581c0c0c0300710041319480e00354112103000855512940d15800708a00007804d076402071052200103598 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 823993363 1250 823992113 823992131
    0x3060c08090d0207050d2907120501120f08090307260c0a06030c020a0501050112110d1a060d02060c070e0f010b0909060f131d0d050403060509031308010f 68
    0x300003070b12540004160001c1c02082c3c5001c0402a14610707907202120303000307040c0040c1c042c0c107201e42c9040c0c5c0740030000c4d4803a200f0724035200400410b216100003400803654100001089000e440c007040066040d000082400c0400d4603041004480c03040105083c0c1510070741100080c40105000c5100d064441300300001c061030046101c00b55944440c0f0341c0240c1c041440c8204100060080d0700c0071002c0640e0b4010360b2240e0050351601400c494090f400b056001c805945004204084801211088082114407200032081920768007690001d0354180040e82400310045200c80c3c1c1c0300b45603006603540c01401255200c0500801548980e4a0b1090b4090700c80c1d190040380e001c40d070f10312249040c6c0f94084c07201030908001c0c0040000ca468007038000d60300141c03105000e000c5038640745207600c40b80d09816000300c0c00c210388505010076491011503082032600080a80008282d01c8001c440440c2e81101005c0751603101c1035440750662080c0c0340280841220110f0000c1c0042d8117410180011400302d20030088010 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 823994613 1250 823993363 823993381
    0x181507150b040b0307121703180d05030702030a0c06021303080909010e0912071106040b1206190306090203151006020c010203030412083c061f0c050f0703060c08 71
    0xc0c00f070380140e154004500501060301e0b8020f041440e00c1c003501c4160b400c49408014130009904c240d03890310450b03442500c6440000760070411038032102c0107807520500e1440c0415000b501c0b8020791301010304000182e040f079424403c0c95010780740b10802a4000d0118070766240342c01030043e4080000d0600408548000080315420001c65500c11200350000d400c628039014106c03101d590100808491403102c1c0c22211500341c6640700508007030030f005203419a552414405241180038000e00c0c1300e10510714000751881680750904104122a4085004141081944000313130071b100801612945600f001c1d41003001003112080b010341282d039940c00b178468600130300740120785a02c0100d901034920303408031a291407041e00c00c40d000c60740103030008050b040c5855055030511403001e20f000e0100805154810208031580c09060841d00700720201c0f80d034400325520a080c074883c0319810101c40d007400300e40c0c0460802e0200512420204889560075110241d0312860140d00900d02408040005441480012780c850 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 823995863 1250 823994613 823994621
    0x90a06140603070e09011428200d0207150516020105010303050f1b0a03051e1c0b01051c05011a0c06161b080c010e0a0305181507150b04 60
    0xc01c0030b00a02141e60600e6141c0b060448090002a000e42da560402c403654140d8440d0b550050302c4252000b00c0b00d940c00518604445a900c1454004919201d50351301d00100e001c211441c0f400304540019240c40d41c6600410090040c04005007034040d07042d0100f6030840d01a40414480c040c00401c0c0d007590f0100351404c0b404c9030b100f4000180821020403814540c0d105c148003030640081200f0740a0b4040000002030b50400644240450102e803002c11801110b00d52420403604181c01070903198206060a0307181ca104512400007201c0081d5034440040c550707442201180c00c4001040c0c003540c0c55241c2c9103080001070109100f11701d98040f81514a6030b0380c03c1680d04480b00c58a0403c02002d542d1a61011502e107807a440308102c0170302c0500e02e504101c1810351442e04001b5400707420050345803030700c2051040c00c0d5007012200038200c1c6c204281040009401c10107696090f041020103a08042e0b032540492030244540500800c800d00c0070817580300f0008816000c56081d21055410310501000e24140016a = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 823997113 1250 823995863 823995871
    0xc0c07170601030b06040207230d030903050f07030516030c03090b030402060d0c0318030804050601080c0307090e01020f0c161a0d05040228060e09070806091806090a0614 75
    0x5401920040022070030244c072032030300120018801031038200c0c50f9884280d421a096174102203184007811601c0c2540c800d00000b030142074030381000d000b1030001707640090081c440c0141c8a022010045048021b141c46803007074890b00c252044210054842c10304000d805200002c0e006c40001740c2a0301d02085988031201070300d00403540544071600f002c4100e0f034000050f140c1004c918040590761014500c0b825586a4222001406a11025041d042909095040440c160480203044d070108500400c192400110340c0d080b5103030420001004075400700304d0750191050355a040e0050b0008036109149010100e4003220449014002d16410b50b5103003000c0502c8042c4280c802000c00d003d2200e0801c080903900035991052000b8182a800c541c069070003804800c0d101401403e08400c0c0e40c05200454010a5004055504440d50300652403c40d40007002844010400c6004d902c4031404a0526104443c02d003000c1d11100041d00d005180c040405550381c0300a250940b00d6500340500e80b07004908d402c841c2409 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 823998363 1250 823997113 823997159
    0xd02030c16140d02042009040f0b01080c07060b0a03080c0c01020d0f0c0203070b0f0405090a020f2a0d0302030a1512030e130c08010e06031507080613050c0c07 70
    0x402c0c028a0400c1046074840206a80181d2902c81d00410440910420101e400000000c2c0f07407680d103400140001c0b00c401a246028003442c0503500d120700d0b0b0300620526842139404000310b940e00310b81e25102003e407100d50703021034120300f007454080200203880c400b8180d042819000c50f0062260300c0012a907a000c00030303d640c0450314152442e50014071503001031040a00240c21210015940c40c80880a90301800601003041e001280c180300620f0156092074001180c030900398144007030303400c44020610900641c08103d03402d410704503009828029040706884520400c0da8039622100350060060340c0110b030459030051820056980b0700e001c039603130310303080d0741001d1030810f91074059070343c141d03042e410848505a04c50040c140b03480d05051580a078040000060303a1783c1c090b551414111070401a80900000e03c2a04820300248541c0394140d0700325441031f0640340052180c0c6881c40840c0a2001582c441c0101c5801e0408001481c0d85103401002040180412a0a541e13a141c1c11182e1403aa00151948 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 823999613 1250 823998363 823998389
    0xf0201091106130e1317130b032e030507120305070b07050c030c07081b0d030f0519031a1203120402040605060c0c01170705091c050d02030c16 63
    0x76a424550060503040355520f082d42140c40c0c0381c4d0074124554408840c5000805030140d0500100f121000c410540030440444083c1006580305000d4692905405484071941001c80041c81c84220100b00072885568922100d52504094580d00590356181c0800c0c0d03000c3c800c0c818006118050340411005064255403518240403240c1d84031500d02c1005052142080810701213002d01d00814001404c69000c00d030001c2c6401450003510a0030f1101c8400709001a440c0105074101540301c0d1481c1008640c0c2c1490804e07492000641c06507800e0081d81a8198456081c040802c5541e81540c4030300000c1c4000720410403481c2d40e04040000200d11542088101c1d00705000308200800f08050130394001d0300c000c0002c504140c40300c0100d0001d81008241260640c04001c3c40321403940c0042c0701c0000704a02440d01907080c503000d5000740007403268600340341c0141c002810214000c81d50510501c150f99001060392012944044000e54a070400388404d03203940a04840588802070200da20021940c0c4600104 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 824000863 1250 823999613 823999643
    0x503031c020d06030507120c06030b150c150108010e1009080403031805060706020a0f0f1d01110a0b1e0114090c120a0507030e030403021302070f0507060509010f020109 74
    0x140a50407015082c03103041d842d648040001041072014101501401c810f544c100106800c04400c641e0300c0da4800800e242c5001a4554580c44110032030b80180050b14500359103142c80800145400c0c1607030760122448001000200d541c180640010007034007411800c64071a00d400c42e07015005c40d403180600400400d402c01c070800c000390007003000405014005400c9a489540ca0002c1600d0764400041100c0d1075600085507034038190800b1210140c0416450a50b41125048001401405602c03404070b0004104030325040c19a80f249011050300640c4034181c40c6280319030b190906450300203640000703103041000c4022820500b443da8031030407034540d507070408111171b8640c0a12440500141c44a0701422082000c03070071900403480034901134240404e0000d05460700300402011144a0700b840d6100341c004200400c05a52003920b4272004e110329440059030740440b45032455100e41c610400400398026050000f9807980c218000d443e038a24280c81d03805900b20300070000c900320303110b03100b0007001203400440b95 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 824002113 1250 824000863 824000917
    0x306060e0f0909070801020705060714070c030803060f0d06050106260a0518030705070303091d061201020417060609160503043801080115050604060c05030409050f0405010501050303 80
    0x40d07500580314400303844c60180c9079501c2509a0340025002e64140e80702605028005a20824082940c444c00d048070341050a0740e521030045100900c000b0f0007910003c40400c115690f144032050b64120024906c008014152074001d002c2e2409108500c04a90002d40c0090440d801c001580306c14122641081496a103800c079000080c84007a000c6458030018070355110358400d0800c000c1050350f004000510402e8030b140b500412005690b002142c02021400180b0704601000034030230b03008042103c4480803000d55481090090049074000c0301c281a00000d0300f9006100854100d0240901b0b0351b4800c841d60303850b20000700d18041c2165a500142c810000103000c6103000d00d81034245041041400081031101c0510419900358541040c042c21060f0010000c42d03600740b280e43c004081c20300c0c041803200c0c07500c80080c1060180e4442d50045c070000d14429410014240111405010128030410407420404616040100100c3c3e007180c4941c44c110001c00c3d5480e0010583c2e4009212400c0c4a900b41302d00000 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 824003363 1250 824002113 824002129
    0x6080f01021e0f0d020c0a0209010515090103050613091412040302010c030302031e012d0e0105060307050f0f070213060807060c0203010e0307050f0709151205100905030405010306060e0f 82
    0x10f030b141c4800901c803000d140a07a500040c030040299900a10725001c1c2d81c010000d182c030040e4810303889640c043c0481d2070401000c17401d403074029009007400260f41c0c0e038004c04a140700350303808146000c4070310301541e0a040194610f1601305040131002110030341b40c510f5039591207600c01d50101a021450703034854940068400e8006650044614025100c0c0261a041d40e686d42c3c0801e0300070b40c0f4071604d00d0141c1c1c0382c507040076840d1481004c2001c841310815272418055030421001070113600e0255038000000360080d409103040300c0a001ca00064540c3d5843c0c403414100030b5800c2950100d01c40d68015880005140d8039000c6c2001380c0d518200075200301ca00e00300d000d0b510710303400d00f408a800d552515002046039505001609203140564017406040c05a18081c0e824290186c01820001d450202c0c10b4521103035007540081a10041c0d42441881070032414001d00d0809080503da8025080c560200204100400034200311102a01d00b40300d8145c580d44240c900c00a00f602c21900550a41904c48503840c02281e = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 824004613 1250 824003363 824003377
    0x30c1b150e0c0d120e09010f05010305090a080c0a2306150414160e1801090525090305060702010e03090d060b0603101d07020a02010c0201200106080f01021e 69
    0x1044442e9020084007240e800054074030213803038281d41c0c4810495401e80040345241d03444000c94000003191f042203015502505140207060415903234000043c044a000c000b100c010030341001c20503481c3c0c41ca04003540d81d504000c01c02196451004100c0300b90544289040300040301600c000380c40c0a0b5110b05035001c03404403144800350b0140d1036000c5d200071007a0703180c1198001c483c1c02c1001c52580444080240107010520000c500500319110142c201c100780f0700e00d06040d10180000403941d501d40003c02c007000c0410f0400c1c0404030032206044801d640d040030440c2d0440f40f0030400c3da2300703958598130240d00f02e41280d5807071041034000f0030140c040c82c07400002156403144108400524181103801140d1250401c8502407044209200b040c800c01d04e040c040c09502240c0c21000b01d0b10f5180c1040004e46441207407100038140200c0c00803410031a8000e40707a094440105410100d80010307124443e138081c04301d621a480c2180510505110541810f0007140c60901d070131103c122944040a502805c0fa5000d10 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 824005863 1250 824004613 824004641
    0x2182502101a06040b09030601060e060301060e010e04020301061724061308030301080d17070504061209060e03280c0201080c1201030c050915091801020d0507030c1b15 74
    0x40b488407040c3d4070007002c1d001130000c40150030f4880c402101810303d8080180c00800900142e44944000c2e40d0ba080d04480c1503d4191821035028034241c0016030b904002985e00e16402800800041800d9034024042c60346002c000070140e4a03901c900c0b2103420b40d10502c1090194403101c0c02c006000c5c1c2d0800c517001305440304006228401302e603515a00305003590020b0300002240e4100090504889500c0320701e0040c0c8a20501d8111564100808041e0040c0b281d48074030814001001100d44010700307164071001c1816008001402641550040b69880764045400d41407000c03812105800096400e8580e0050008581c48600b101c6519400550301c4020052081c40e06410030090000d0382044030b0000c0e4002d51040c0340403107080f403c200c10400c4003100109002c003801016080270200340c2e10808056001a5440540f0f000e26440e01c3d80d10b40a40b05e80c0f2484481e003818001444440d40d0305a014002c44081940d41140050640d480030811031514007014201e80140700c0041409003e5a2081c2e8048002c1 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 824007113 1250 824005863 824005901
    0x17030702060403120809011a091f0e0703151a030408070501110d0e031614340501090b09090627011e030c090e01090218250210 56
    0x503a00203401544690800c942c544c11020181c40c0c90780e0009038507600441010003c1c405045118094285066090102d600c10000c080114400111091050020080210b40d11a0b490b0b142c9207852214481920014002031901e0f135889041e4055282d03000a580383d529840f800510b82c03071040411500054020f0301c44035010010580020800d125264400c050306084d680c4900c1292814012103135003081900840d0402c215018401000e400160300c115802502303000320052070070502d0315103660381d49640c003c4c00314400c45000c248819610501c1900e61400d1105102d502c2c2c4004680c4012b0034443d660b086032060106151603d08001c0313095000001502c0c5520b1812152841005440307144800b0b44c0c103501171401030050702d4104509039035003018201c01d24101482d5989907141c1056520900009955a005001c104102900a00b001c540c0051180b13000591450301c403501d940f42500c103095840c0901d207080c00e650356102c9424140c502c1c240c001c0d00d00c00036181060006003080884403900c7d0445 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 824008363 1250 824007113 824007127
    0x7050a0308070c08031314040513300309021017071b02060415020f12070f050c031c0906080708040b0702012a0801082d0705060703050702030618071703 67
    0x30006440e0108403a2070b100a007d02d0a415100d252541603000360003141031a0402c00c1e244c00504117072560b141c1c041490100c0c901100c5d2405425a20b01e1702040d0505915946e0500c0d40d54542c0043d48001e00031610003031055101c7c901a90b1326440d02c100001003000d0706000800c2d15010701800070420f001c401400600c03c503198000380599016030008034070b40c52400c204d00318a940c100f242d400c04800c204000c11241107119000302c154010b501005000940004c0c0038010808107004090300382c080a800c0350340f200345450260f402510a0f0795180f0029000f20340005209101c0c600b828007651182d1149017054495460300019140014041d500b50364980b000f04e800d28806038045100900c420128400e00094500000c0010406034803900156103e80c440a03100841841c1008040c07040292040c2e6a020040c401c0d410200340d0750146074009030105103041450303000700041014034400c8069803a20359a0800c00d401c80100303001814840da02c4600180104880720038400c804680700700c101c9042480d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 824009613 1250 824008363 824008379
    0x1a0906030a0c1211030d080f06040c020601050d050106080f0c03120a0507110f09151203030f06090709080a0b100504020c120a050d1a010305010e0c03070f090308121807050a0308070c 80
    0x2c074070200c1d5000a04200c108001510301d000e9803a00009c3c100e0f07050003501440c64009544841c10300039030b131040c226141c2440170048254414401000d501003a01c2003003100c031000315110500521124024000c80020250840c070490407549201440d071602e506011990302c5488031000f03e0b00711107401801c0c01403225555aa04503003148940415812450000004401d00c10986503021000b03806910a0040c0890910038a400940c403580c2a1208d00070396a810f2030440d1441d030703540c0c043c0f41240202c01003a000d0006030b0a0051240b001d001c1014030181e552800d01c8120b111b448070900d4240c0000c1210030050301c1c428000c0448840030f10300203003410000c0c51180d0840314020b841c03590591030116503002958041c0691401004001911502458100ca459009100007412042000403040c51180c040f40100c3d1a080515000280661102d160118410b40782c4c0d03082d03403070000740d5003989800121418002514810381c1c1000e0064056030340f440d52600c0c15900501001c59201e04480c602051100e = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 824010863 1250 824009613 824009623
    0xf11010e01050106030b1e040b151603020c0f06030f040c052206060f0c060207081209100516090b1305063402150a020109061a0906030a0c121103 64
    0x30250000400e5458110041c088949201030540213038240301084440640c41002c02011080c25180803c000000c0740001d500c240c2200f00d0410926804100c90300220f01d10141e00007258845d030201c5d003401d1400020008542180c42c450341c2d01010800004241481d41d1803820340080c4100e40c0c0204850b218800121100c904601029a0000c8070b8011800469107011301e900800c0141005209000046801460810383c1007000c0c6c035103500028900c08001e000750455148803c3c00c0c5041e0307024201442842c1d1070f003d803080c5030050329040401050304103e107000390100303031031043d04ca00340c036245000340701a166008408044000c0504140c00a4a91101700081200e01c400d0742e01202d0078580c1006402a055001c108290386001d010300041c0141c441403104015684041d054907126070700340e07a040b4058080391100809550800810b118802804c12403a034840c0c4007118a5503c80d910030080c580d43e03907200ea40140091056402c1002900b074034a50307240fa4140949003004000444c1800300f03180c5 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 824012113 1250 824010863 824010881
    0xd0303090f0c1e23011103090a0b0403050d030b060306010f02120a030615080103021e2103090126070e0607121d030309030d1206031b060228030f1101 66
    0x82180180b80d0307059109000c83d090054a9505555150320345014002d50702c0c141041c940606014505000c80700c07081d400c00542c0c6828000a100d42d50080e118101400182c205100c211003d100e481c3d0b0501c0340d103000340500e02e420b400107404c1c581190f50b00e9004482c00982820481d0641c0660025105a4541100140020100350310040344c3d241c40d101004036059a003024400801a0326401440160707245a1450204490060206e14585015000a034403410405520000f511001008030342081d01001038503415009803a55040b0a40c0003502040c48010070301e82e4048041c2c1e07800020b00090041c00510702d5101b002e841582044110b03650040044819044400407a00c3c0301603142150802040b44245081c0950295080030364941c04a80d6401b0144824000d01a190401c10b511221503440317a8021504003090041c8890801c9501286070010300501d00180142e00c0e507100f060140c04071843d4410202042c19803e0000c60700c0c2102c00e5070201c13684a0400100880340070503d84240115442 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 824013363 1250 824012113 824012129
    0x1d0604110a050121050403051c0e07061b0609032312010f0b031501030b101e0e0a090c03090812090c030d020d0315082a03010b0d0303090f0c 62
    0x10300000a040082440d400c0c2d01403410040c071100e9001ca29034000c01907440c001d01000000c54107841da07203401c0c2d41e1802108909026642c045280780764001e0560050700d251000d00c1d003075645007605c039041103501c2007002264000011803c007403400016110360205a02d01d00914004640c0c2d1b08180340d100e13108440f154107036141e43d80403038a103030960b00c810b45483c018004031231041111450f000c92010b00b400002c000403103080c0003004a0701c1c103074040d40141c60149002011845011803401c8050b00c1d14000e031092404075284003402400c00ca0140300b601d007202c0c0009024603155854a003c42d0013070b2000f403031a2000c0644402040300040c0720b5501410304800c0da0000300d112072414042d0689010040d040721031003036008031811a0226004500102d0225451401241108d00040402d80d03654a681c0500024850308442105080c48450310403d0305a0981d0141c0d41c42049804241c2a1002012060b0740300c00300a00400002c1c2c041c0d80110600e5200311050303003003400c039a01c4e200003400490380002c0c8 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 824014613 1250 824013363 824013383
    0x70b01030c09060603020301150c02010908190512090312250b09060906040c150c08040b030f1014040207030e090114040e0303040c0e040c03080412031d0d03031d0604 73
    0x41540302d207006840c041d041c02c1c42d04604661400c0f4549088084861112060050080721030066920841026002d000e418084404c10030110010746403840c3c40c158103440c2c40c040c403070280142082c944100c400e036032001002801e40707030901c0301c43e11510752141c880702c10307000c0d481b894014540704681080c4c200240504d80b413440514201c00d903603042400052103014650403490402c00011040400d58080d140707000303480c00e19100e01c3d4078140e403045c204087c01b920740741001c43c00144c100b111000031480340040340c0703000025407a4003141c80c03002500ca0246544801615011080720300b0142e0140885600920300301286000c06004107c01040c00e8001b02c03429008401945d01c0ba00345405001c450a03000707030096280d0b140548803040794000350f014000c61a2640c5002ca020300262030b07064000f0f59003101d03c0903a50fa50312408014542500b80085001c100350311201495034201050a4103440300142400c0b400542d203550440013004100c040c20402c100030100340c070b00d000c02081603134801c07032040c40e40704 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 824015863 1250 824014613 824014619
    0x1b050c0405060d0209150a0504020c0304050a060f021f020d0c03050916030503120408070b09070f05010c051c02030d06120b090607020a06051003120807080108120403110303070b01030c 81
    0x11041d20700c010182030040700c002030030741d0050716540546544141c00303006100c040c4188100007841c180c0b556120325031160011600c442d1240c4044010b00450f1021104500b427140d039071400781c5103040c0440d0300700007680101111141900e00400c0c0002302c43c002c000014a00102c1848042c03c99a07407046240c00a9510010014140801c02007180580d0246100303000d00c501d140d985aa503031249080714864000420302060800040505417804982d10000d00c4006260000300346543d201c992042c20702d07900494500040c0307075001c3c034621160f20390840040d1800e00780740300d4056581071007030f0008000c40c0700410004036034106511804002c0c09112900c2a141c03c081d00b00068500c401400d4850b494000c40180120a900000d080031025404503000c6541c0c0c0c1c9002501e60010010361000e000b1800307001005030850782c844a428818882a1564140c50340c0300d485d05581c40c4001103048801c81800c020070b1000ca10700b041c1d90b0b450305100408070f92421070a5a50400b54031001ea000700d03005070480400b4 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 824017113 1250 824015863 824015869
    0x1080402132c012c0c0402091504030825030e010c050f07080c0312120103020108130c030b1f0f05011808030414010f0201050c0405040b0418080a03060f080d08071b050c 74
    0x38440304c903481281d0141c0c030301c0c034800c0540b550300320b0303802c0342c800c65000640b0005034a4401c030f00c2110260501071035490380c0d5a4107240c200c1e64410708082c0740600c0c81043c9045071900310041200b0140d01982d400c03001e102c05070015941142d141c0000d581d82c1c030640b4600741a0007410050302d070107010400090202c40307248805161030410862640c01d04414140086403400c1c002c00440c90450ba02407808007050b032a2a040350030110110744001d01a520f03100e6000c002d003c04090400d0003400600a0b45162550480b009005400746000ea00002d40e8140009c1219610800029007607406100c0c00c202c5195588a040f4510340c41588100805c800d901d102c41e0296030407a004401461b220300007800381c0c1c50007040481080c400e9024051280e40d84401030b00c031540f2260b0200b000d10009102d405440d50b90303400c1003403044c2c1101200c18002030910b1000314114410268031400c0304c00d00c00c01096001c805910580301500001e01140801c04408a101a00485000c0900c0780c0fa000341c0c050040c1c0480b03032041c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 824018363 1250 824017113 824017151
    0xf100c0318050a2a12020f040e1c140d1b080f01050607031b0c03060e03040509040b1f060f02120315010309020f04090b011401080402132c01 62
    0x44025501c12001c1500481e00c00300c1c1988565600c49240e2014088400480c002005005000f8004200001c00401d491584c8400c0c003050328021141c940f01440c909082100791981c9004801c136942158003100110066400c030141000348500345946c1000d42c15000030700710707040034007807051054940304048101c222a445070031a5403210720b00102c1c2807038034044010141c01c06110300c0d0b004481c0096001d080c503100350300d8900c0101682c0c050046910031400c01401500e01ca000503104030b4036210703042080240003c112011214080d01880780742c0e0f5651a0340d050f40c00c0c02400d120748180384000000c0410329500000700500b0701070300c954030400c40048009103030a0460070303040328500e030802c1803007143d409001c4030f208448004d20300415022118404500080610343c43c07075401505041f039042c108540e00e10401d059640c0740c07080c000180b803a00300464101c0015200a50400744c140c3e02e1040600d680c1d005645641b0164401403c02c1e079031420180c1d252801c5004481c4145d550f07a10034481100041a = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 824019613 1250 824018363 824018381
    0x9130f06050301090b161817060601021c05340605060105090a05210316030e040b06032a0a030903030c140a050d0b04020301031209061b080a020f100c03 67
    0x20003003000244d00d54032900220006040e5101205440c52802035035441502e20043d610a031401c05507481d50f880040400701410103110402501030040041e4403940b00040d000003483c4540d240103920345000300b080c0c0d50b507070000ca4801c0c2003101c03204411101064141e03025118000b00c0a20030002400c40c1492021900041c0202c0d0411404100c15030b201d68a24072004261001101ca02e40000c14060040785c8100b00c0c055403010602021614100305003811450303411071030013a260141c0c0c0755804804c11045a40001000d54031801c1800032070080e04603060411520001c44103208005162005640c050703030080065100002d440b546c40740c08140e814020700c0407129541c141001500405082c18003580908045c03a4100329000c1071902401c2c0480e04540c40001000e081190f0f02e58407400c0c01880e54002018800c045680390f180000c0b1184508401c8801c003801c2c0c1036004124603a03640d210141c0d4841ca910504512900e41d800da0501000d0182a42002088030000742246032540c001c0c06580c0340c65 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 824020863 1250 824019613 824019619
    0xa14070512030c0d1a1005070c06110f01020310031e02090105010503131b03051513031d28120503070206030a0615020109030305060604050f09040809130f0605 70
    0x404610001240054012a4108000300c1c0725103035a215400038034580100e1401e0780c01507040044168884842c45840403035030360280e4865103140c0d08003009564512a1440003849002010400c1048a01c1001c881410242100503504075200c034039000c909a030020340303508401c8000a02c0800c10412000d0011220103181c0c0303410340d00d1940e5500090780c0000d0500c1858184080000010003049074801069811540140c10f420a80b03611003002590108a0108031920320a0740a03c03203200d40162030044c440d81c40b0445013100c6400e60f640840b80030a0f800900700028060611042070b85d9030750440d032420030010011214a001445941000800507540030700340d030ba01c00ca05e0740320201d1404002c0b181281c5e01030b80c540c3c0d52130716181402c0000302030f0b65000081244c0b85c4034175010341503810340110280074041d940600032a1110000c00026100b00c2c451590720103180b5032482c8050500d0386070b00b540280100302d4203081542d00d0011881d2041c0350b03400e01c2c0c1002e580713140040d21940b0f2881030340041e00040d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 824022113 1250 824020863 824020867
    0x14090a060605070f031107030b060436020112050705030603070e01081b0a172406090415140703021209060606120c04030210080610080f0a27080a14 65
    0x1007040a8030368810100c1c06010000640c60740814540295421405240c0031012038803000e0342e80c24021303c3d54000741c64091165050400130100c7c129918402c03d400070140c0f40500c01560244070b038007031052800707604a040c030080b5600300110b1001842a44e1140b034507602c88590300d1404104240c248512500109480349020f0014001e040300011110394000110001d01c07140503000c800524040c1c038641c4030f0700103484510805004c030400800d0a0069120b14500020a0344499500d0700c1d21001c12200c603900002c4e00000503011450b031410315140301c80429000120f0302201c1002040c060b00407900307440070940008402c042c01d041020303113580c00300008024220500b030400000b0780d0707403041641c0941048400780c04501c040a500c0308540c0159401000c2c102c440c0d0706003001a21100080355181d20642d8050060004a401001c3c0288203180305100b419465840c11149001044002140d4881c0c010001c0801207440440540640b454080e4507115140e40340200020121360003d4482d680c17403401 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 824023363 1250 824022113 824022119
    0x18060c0e040c02121605060106020102040f090b1f0e121c020c100324031b06080402090403050a0c02060d02030417180d06180b010e1503031206061314090a06 69
    0x101080d010b80f132030944104199600d006003950352001c403401c5409031a5000e81000010b01e40c1d0158000d0040b01d810000c50034055070707036036114401c561507468256049025183e00d400d810442d655050380b4203030035050554214040e44080350f244030f03c050300e0b50307825442580b90440d111400b004d14403500d08141700425004018030b000c03e6520403446a15000e0680303402950210309081032079041c0ba4541e540d4011405641c80c1440700000c0c402c008441d0943c800301e000403a605208403150b51003260090100d00b1152a15074044600303607c6156550100155414140d0050703840d400200300c80e088401c0090b031a414282020440b0700500204c4002240d020880140401c0910100b551103c008445260300354482d4200300000d401c4080784641c082161520110401502e4000241a030703103c800e1900c01551610510040074804400c02c6a156005020b000e40c102c0c41e50001c03c0c0d009401a001c50705203955100c20100601094200420354038420004026030300300091120740c0610031213010b00c141c40c6 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 824024613 1250 824023363 824023367
    0x1030506220c1806140f07120c0224070b101205010b09060d03120c030f0501090c0e15041211030303040305040306140f01172a0406090608060c070618060c0e040c 71
    0x8058548009607081c08901b5100c6014000203480c000c680155018115006100d0002d040f42c0c0c600e0b208900c140b0485440700c0d40c0d1850b6000c9615541d4060810514044040c1c4030140040402030560000322059080800c08210504500c400300d8400d400201d070b0364010504001c8003400c0200918080e4007001040c9021a031300c44204d1a15a1184100080c1540c52440c101c01420a0007410310400b410a0000203200b1001e80c082240030f010b680d58944100a4401080069401000e246080310020b0005101540391014803418251155100b12588100213011a013107810885080c0c02142000c982002401014020449182100d210041062808484055080106000b0b0f0600c280d25500b000c02c000500304501140e40344a030214145000002401c0f200080310b5802c00e0740261308080c0d0005a24419000b207000766075000010708115501c0c0391810651307401c0316406907076a40d00d0b000c096268031070742052655628010300012454030340d201000f41c002c55240b8501030044e40f0302912110055 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 824025863 1250 824024613 824024627
    0x271a09060904030c05120c0d0306260703020918070914040320070902030a060602030c0a0f020a0e04060501060908240924010e1303050901030506220c1806 68
    0x32004840c0c8011076202c1d410110390f40300c03c0d040000e01c284100c0c0b462161aa0004028114550141040740c0010003da54101c056451303e00c90245032015001000c000320b108200760a450f84040000c41d80815548e80024000d1030064a89941c840e1000e010303501040010b004500180600380014454201d4281c5800c0d000c00e40140302800b04080c440011408200d5044602e0000c83c00004403500c0c552103070302e288000d6000765a140240380c170780701000038070f20300100c20313a041c244c9100c0145c0040f1500d601d5015000d02e2004040341c0c05118070501003a4110700c044150b02403402050005074543c106040036143c91780c00c1d00300c2c00095004036000d003510064000314020030100a0602c000d25100c00300b01c1440c0c4071075a04108003034541c4141c110134000d40a9809030488071130120b00d40e9141c440d4100c00038480005800038000460800140b84603500903002140c0015002e0304800410003402418441d480320503415242c0c00307403540f01d031642055021000da1315020700003481841e070603d00700002c0c00c1e071 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 824027113 1250 824025863 824025871
    0x40c0212091306030f060b010e0a03030206041b08120a14090f040f0e0114040c06051624180615050a12080f0a020a0b070212030f0a06271a09 62
    0x10b1056840345a010300c0c4590000001150321140340107100006141100141202c040c01c0c6001400e1031103006c40500d40304100c00222501500a40070540341d41e01e44415103035000a00d8003144d0140f44000030706010800440d9094491001000e4076802007401c014031640309100415404030003071180c40c04590341da0b54512100c12045600240d0b040d9181c02e1100039201e42c520843e5a54a0070306040b54000c406403466208a1192a400303545a0300c6001c10b5803280201090340b4504400b40000600080414039088a6062a40e96106042410071b5503041541d20424001c43c4420f9040c55007402c0003914021481c105000e96541d15005090a012800c02c0c0040c2c46480c003102050705460082c4540c1c0ca00b142c9842042c441d03075a0b80c0342000c00000e50350300c41c403210031101100702d5070000d248544041010704001d00f010702060302c1c54031860801500c114028000310145580c03244e0001d014102101300c0041d062403e496026034400714008101200d40504000243d880005e00c68090717035a80c041000c2d80 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 824028363 1250 824027113 824027119
    0xd021501050a0b07150f020c07121101081e01090f1b0509130603020604030602040302091e0117100c090f0f12320a17070302060601080603010e06010e0105040c021209 73
    0x8400c910708000a0005441c84120421440c2c040391b8440f21200d42c0091055441c000100d802069030341303002180e103100144018042d059420140707c031320340c841d540443c0c02000e1948084809400c002070012001020790103211b51544d070744000c0785c80c42c1c1c00d40070303a6906c20b200c0401045882038410000d45184102c0d0380c2d440c4585c0c01070b030054000210907802100a150040d003900d45650712494444025800360205a2003400c1c41c000041340c000c2403107035210000100c441c0040c240c0e4030b440f0040003c81200480501c060050083d01161300703445c3d104521760920140e4400c3c50161809a501440260740d07046a445400380c0c0f5010300003044c00e0402000407540c060680c2440e80381c030481100488180b01c03c503040150a503110103c0a040000760000201d0103800210088860f03c0c0d0300301641d124419004025801680c00540700358041d004560340a0009000442c60383c0b4a0b03043c05040400980040544600280041c0007a007883c0c410300803010a00c0c0001c0030348000902d0403403004c0c015505070700d00c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 824029613 1250 824028363 824028367
    0x5090a03122604031e140f0a0e0d080d11042102010917060f152101060b07050c0d050111070c140102012d060f080606120303070f1d10020d021501050a0b 67
    0x100c0c1c0706d650f2098550100210880e200c1c0800580d00103250b0210002900180460510b2585440e21005051030a9071000610b0b02e8500d41e0500040544100001d400d11001d040c44002900c400a0303c000d459454412a8545100c400d840050000d2030550080e002c0c0d50380e040c0300064140703000106a600011050340d4180c90781e4682c0e280091645100c02103070740141182c0340f55802d501c1030140441a00260400130b010b813076120f0724500503600410001030056401017041844608100e44458101409500003103103649140c1e200007041d82c0401030440e5030a4400100b041514440f030508400400d00348000d00c8403480440e8000d503111048001107403019442c1081c000c000ca40d0381c0c85580240310210350140b26981e01c0c080c150310307000c0895040307000301a00c5d0301c3c03101c2d2400007004a86c403441094568030083c1c15600c4045405280043c0c000310b074499140580300041d5690b00c40780c0388454007a40140803ca00000c0c0090030030b100e42c0c030601101417401006104503551050000250b8a90490841d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 824030863 1250 824029613 824029667
    0xa0c03030510050604060807021b010c0312091e0201091d1f0503063115020d290319051e0123061206100605090a0312260403 55
    0x4200c0b40910f0384816403011002500056082e0480011445001582c09a82512800c0a440081361111510b10b600140003c00c982c000680940c1e144580603006503000a108240340d036404003941641c0ea81d400185084151071001c56034000d554902811507041c00d02801e4101c0c0940107c4004050300036895420203c000d4526540300101d0b00008000c02401c0700c0150130010070283d107020441d0700504006c2c424001d00030103103c420690100c03056004800300d000003180c81400000b500007003181c1c5040e9403108841d0100f50f0302c044c2c0036a40b40d03d045492041c0d031514813007010315000c10303510074840400040741002e000c070b040031a0040000d074900009500bd100414041742c010492070b03049402e10041c0500072111002400300182c0704400c10340344020142e510701180703a9648411611041e00400111060012501c99406800d68003c09400e880d049516559a000075a100c0d059036800503182d0307942d140c010321001103072080e5440c6040c01000681080d407001007000004c600590400b50400c4600 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 824032113 1250 824030863 824030881
    0x2040f0f030f12050c10020d05060d23030c0f06090c12070909020f12150a061818020d030c0209060a08210408010e03074b0206210a020a0c030305 64
    0x1583c5c0301a500040d251101d42002d00d910007904650562602140743c00005601d50509801e074103c402d4000c0380408690b4600c007206490313440092000d40c0d5a01007030201c1c130002c180410441641c0c01c1004003410303c51501d020840e2030000840582881441646040da1842c0b01c08600b0300c0c1074461510020825803e140086421180040c5099030414800350f580000d001000c150fa800c603c2024569040540b91401d000d02594140d0160900c5404e000f0345070f149100a0742e2204111022040c604110042d0076000510700c0710400e00103038086543c0c500c0395030440c500304006650111003210f081442c5800c040300c460f03880340640b4060b201144080b400701c07601c07803981e01030f81c00030f18014000b400140201a11141c40c1d4001d0a8200c0300904142ca4918440e0200c02c620020502c0d62659103c0e0109042d0101c2100c0c44207a8001880c0c0c3d48200c40c003400358070303030300c00405401c1404418510f11414907405aa86101c000740b200304581e04c1400070764006984828903203400f68040c5004140d41c1c03030300001 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 824033363 1250 824032113 824032117
    0x141207050a060b0a050d140c0901090914030a17190e060f0108011103040605070905090a0608160503120f0c100903020f060c040504020f0d0c030b01020607020a080a0507051006060302040f0f030f1205 87
    0xe04c0e03900a409d100000b030340021542110100901c21803811162140b00541e00c4d0b56400340c200303d6000b06121a0441307070a07000b10954507912061a540c5920340c0a428404202195241d0b240300d02181c000c90304000341b401d9020300860050001034002c006030928500c0c10304d000e00000e17100902054507a004118024444d0b00c000018103c01080740b8401e041400405e030050085103e280f5680c01a03d80030410308095582160803508080c010b400c4405041e204002258031824028000600070300964503290f0301040b1403202ca40c079850300002c01c0583c9040103803030544981d4000400e940302c0c008100000c0c0000707095808581c0f00ba0f07809611220580c90421443c010010081465480d0055a2041d82d9168112580c161000e07002d803409031f11501d02c200d80f100c0c1d440c10050640c140410020512501c90001010010b0143e01951000030004403010141d540315803084c00040d401140900021800001400080148210f140700c4586580e4410070a80c0340074001910030f00140030100349050040017 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 824034613 1250 824033363 824033383
    0x18060807051c02030105030d1403040204091401020c0105072706050912010207120305090a03090b0d1d0606030f010608070b0a030204050603180d0813141207050a060b0a050d14 77
    0x100078105140400140b4000b07400910440f8800d1141843d400a01401205040c07009110400c045156030340ba40c090001174419000b040718075a81441e00e1268424080c07000c1c08511000000101c5c160816402c01007110b501d41c550b04481e000e0401081c03020703503440c440c0c003c00c585081c100a41c03184518000141401d020304100d41c800d50000408400300610816813241942d0141c80c20007150701d400043e203546250a43d0020302081440f10113000200544e80a004015a100c4002c119180701008064103040d60301300c404910752100060000500d41800500e6040d440e46000b0001a032a040c402d0340e54112a105110031407100140c0c071950980303c2e404407400b606016208543da4240402d0b080c5070700300307142e10b100e05034025024031501c058440c0454a003d0b0b010b48900c640c002d044da480b081d8800c40a020384080503c9110003138406044075102a10007103001c0c50160007407402c03d040050503a1500050140b04503810300e8240890756a80d25070041c287e822a0010f5900c150007000f0310721b0105070007 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 824035863 1250 824034613 824034637
    0x50403200d030c110d1205150a030b13080a120f05161101060906120507050102030a05030c090f030d02030d201e0f18010e151b030d02070605010303020601061806080705 74
    0x74030a0179668201c14484000d1100c50402c0001d5a6001c60b0400150511040381f40d01c6280000b08001086226480f00e80101120304010800400c59850aa00f07610004100001c10140440300c0c038055171603ca8841d40290704541842103140441004220110720b464040070310410011160790382a0952012001d45840d0b08200001030b21001543e001d0752200782c04542c984590b646c00300d25944048261445896561101d9085440c1c3d14441c44c100d40000800b07c0d00700900500c8106103540420501c09260040d401465440d4000d6003100b00740c408018420004410142d00c2d80035510b280c108482000e00168070800c00c0c0c0030520b030f20705010301c6a41c0b5000740c4030340c0100e00000740e505110b00144920900762240d07480c01e1822014001c00200d500c501c0003004505000345d03207640d402c1c00d4102104820766400e480c03a2109200426040760030802e0f00383c07161541c3d0b000520405804100b214007400242c2404415400350034040c0c20040c20a0240004008000000c1400c090042c401d4603540f040c01 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 824037113 1250 824035863 824035873
    0x906020301081c05071509030e032e1103181504030509040c1d21160305070506190c020a05030a03110d0507020102030421080409050403200d030c11 65
    0xe200c190303070f140010318040842c066200a0041901e0084003203d11841d8003680c95458034884056002c000d02c6428020340510116062040c615a0144002c80c00703035180d0746200340b01c490081925440101c118901016003441d140c0c07a100c48111000075242c0c400450810412001c1c102d484c0700e81081d8900682c000000024418401015000006006030500070b0360200000101ca8804a41410100c0340f00752481d40314100c0a00b03035040c14980f10140c2c2410035140c80c9006400074034186004071a02054440141c0000c0c14020850284111001000b0440b007090908203000d0030f030031080050f144481c040c8850380200d4021501c50b01154001003000030140d0309505500e090103802e80001c4482105075018001181035258052400e443c0c01c03903010303030045040c1800c2481100314019900990300c0625406680c000c0000c2c0a41d0003000500300c0d01e4000300300e50030140343c05049682100004030340b10440382c0d207140149100080110340100c0314a00031480c481000780a4540751515081c00c0c83c54018 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 824038363 1250 824037113 824037119
    0x711041d01061d01050904030f094106030a05090c1512010801180201080a0e0a030507060b0402040605030a0b0a09020307030b0a0803090919020c0d0809060609090319030906020301 79
    0x410741c842c10407201c95243c00180745290f15a50b10b0032070b00034007400e503001e4101c4002c6030120740301d011004401021030410345150368484084050f01c40c01c040c0c01e00d824a40d0078100511068008000c1d07881c0e004a40c21901000031428000748082c007008020100f40e6a84a00180c800f40c0300b0030624146880280c140c0501c0c0c8000d810303035000e0754805a02c15076401903070000000c01c2c142c14450528a070034424940f20318640d6580c011a08c4040c0a070801216a482da0340d00ca21000080c44403039110b9200352103003640c0d1001031403c0c009868143c84218480d5205000401c4000e400c40126640b1080031000000c960b00f4050000d41c5007032243c1c0044142038404000c01a545405a04c10b05500d10b04840180f101c9a42e00c40c11350b80d07031083c4845950050701d118003140d5218802d0499401a10840c400503040030000c000307aa1402034254907550000700307940244803a4180600802d604a0130035541c0138010b24000c07056640c0c074404d408034182521212000d141e11140b081e4041175240790301c207506540d2965 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 824039613 1250 824038363 824038421
    0x6090602130905090c030c0607020a1a070507062a062d0609021e090a15080114060c211e03010317030f0a180209090d0f0905010203071104 61
    0x100c601404225a01d040c0205000210000303800b102e09170300030b000702210103100044c40859040724074201c0e000200f541002c11001038583ca0b00c4034040f24031805513241d140a0622626000c0030364014010310141e402030885544040346850140e070040000200d140049140c11402019030645164944518049016510b10444614148844400f0781070000740d0b190440b220403441171030301c50595844110901a0b11440c04009021003990040c501c500c82c6076a00c00c1440c0f0007500460907000a6075030301c01444034540c1003a030f80d00461415500241490141c2004039521907245480104542c002030004d10341034058021032b000d8402141c0b0001c0e185221815128030b541003030100312400030105521103040c042040680b0700c2070444403500c1041d500c5090541000f02140c200420100c40e03480d00c1e01c0e01503190303100100e0007007403441d00038000c00724a944000c01c00300d00c0d4101d401c02c0000d50f18042009030f0b800010344035aa42c202808209000880e03000400410301045080c402c100d038582d001235400 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 824040863 1250 824039613 824039647
    0xa0c050102120601030e030a020c0d020f0a09140709050d030c05120a0201020712020102030c03040f02040b150a020609030f0a140d060b040f05040203010b0a030e0f061501020f0f071206090602 84
    0x3c1c42a20b041c0b122003c8904084c1e2a40580d5500a006034841e003031191035450400c1d500b007861400680030400101d80b050104d124030906400c86441c007510354007101840810511400e6120655140c04001c070303420640061641d9030100c0010313041010809107042807040a10000341c00b0300900c181e052740d03071091401c064081d40004a099444015400c1610583c0b40113000700c9100303155584655117180c4d1941e039101c0c245803000344203a070402c0e0f80700c03070a007816214011030349508040e030b0f04929110890090001d140c280e00800c410728540040c07162007220740f09001a1001946141080113000841c00d20143d250700541c56105101401c000000a1412511001f071007a55014980b03e04015250002e100c04c0c0d10003803141e140b04950400c200c0c4025440790380404032968840042e240442002c05066180c0f802c180c907660301d01401850140c20715130b010030800707600b000464023505a4110070b041c92a100c142c0351140e446505100c00120003080850781c8400446507215000315102d0b203201403107080728 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 824042113 1250 824040863 824040871
    0x1f09381e0a060e06060a0219110f1206060f040b0d080403051b10030e150406020a120920011403070e09061e0f060f0711030d050a080c0a0c05010212 65
    0x50144030011407014603841c020741007620801d90101401d81c44d40d00601c2580c0c0c1c8410303444000c5002d1052040c0084070724200200c1c03101c0c018000e0700c0044114004202d01140d00e010305030710800000f008611605004275983c0d40c0044d0442d013404161400344049000b40c51000803269102c42103040420030003032140007500640f07000d20111200d0b0b00d1110382780800e540c469480240d1210044880c8019540301c0e070031541907101a281980d801d2502d050b00d040780c0c0c09054500301c0718541c0118103140d80075841210b840040003560310510080031aa200c030681508125440c07401c440303601f1200a0945d0181041843d141c18170000d0542c0c0b03242c4004010005051010a14801c00d484c0c1c010941c40e25158504500a410309188080c1e0b2071170305020005c981e1241ca60190304440c0a1194008448400010300482c501504141803441a040201400d0a080c19042000c0c0301d020f104030000c075540324510a80c00b40e1703452441a560710705070708180e0b66085840030050444d800013a01c0f11f402911400741c0350003 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 824043363 1250 824042113 824042161
    0x6190314060108160b0f09030303071e090303050d0509010b3a230c060a0201090c05060421050102090a03062301140f0d020d051f0938 59
    0x1a0b980f907541d1140c490f04038440020550814071428070090403210010030941a140d1a1145042c20401c04281103401c00c0302d490001c41d00320440f6001d070f0804103800c8800180070349040d003025419a540541540a90a1001c1041e696140066820002540030f000c1c1d9440081c01c0051042e403010105400c1c10851710441485441244007083c0c262440e451104000e6000c41414001480000c4500a07202c101d414a9214850307809207101d00c0d140e40700107210b903401d181e001242c01c0045003002c5018003c95400b84cc00384030200410440640c4000c40a0181039910504500340c9000d13050043c064010300003102c0d4000e011203400010806a54420389120020281c01d0681256284596818040910030540220b034114400700b420b207400e90070008a100014030b5812403040c1d68022500a201c407100450b13490340018030204105c0c164141a1a03030642440007482924003690ba521004665849450080948910b00ba4004420611000c1c5200d0350646440340d21310300380001c245900a81034407028 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 824044613 1250 824043363 824043373
    0x4210606060203040b090618090c0c071a0a0c17030a09021f0807030e0a0606090212010b0c0a0f03030e0a2603150d05031903020702180f040b06190314 66
    0x256490010050b00e084914202c0710501b4a0902c0c010710646078045024280128510f220b049a039959000007540201c0948994644800084469524000b0240c22603480b10b02072104d0781410b10001401c81e4004802840d00c0f04180c042c2d0f01d03051020002105c92001c00ca00040200702414042d40e00c0340405034002ca4401b940010305018122900c0411103048002561b100d00040f0518040c0d0425070050a110084520780000ca45850007126003d4011280701d6400060381d221140d0408141805000030304050751602d40700790344140c0d42c0c004080c00248052a03441014041c1800781d808480003014450550f9168501407030118511540c007410b0b40703040401e200d840c0d80405011810380780700781940e401c45065001c95038100320125540c400200c40c40c1c84108005c014882010032044d080101d43d0310702580303454442c410032034842050b81c0f80701301a660281c06c20290b0b0121140300d40d08550040b42c244070a07190780d07010469500114a211110002d0310b4000810028902c240b61500000c54049d91 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 824045863 1250 824044613 824044619
    0x8060105070309211b0303020d1107090b0a090912081f0b07060b030703030201050f0a020a0f08060f040c02100e030a1d030c150d0606110709020d0204210606 69
    0x5540d50003018005400a40d0205062244401510344c3c03000440244104807058401c41c0d5810780f05080207515030248441d2000c3c100201a0100503056088c0c0322800d041d00142c80f18440c00e47d80300c10611a10b0805500e6800450183e104c079542d84014111101f0180100707261404c21201c020746450015000490307a100140d51401d61740000315501c0705422160035014680102c090f1030303401100050754480c0d960382d00d41e81290b03030800169006501c030f070b000403905160140b034840f01d801d8000c00c0600c400d8010024a2400c0b44d120f000d03040c41d48100c0c01e00b1905030f1240c2010405240f05115038a030480c0c50304810588075178000600402082010380c040c0301035a9500d22041e05c0e4000c003148440810800c0010b10290701d442100816594800340c1103449a0b001e501c0052403103001c41c041e40010030710015a104080010f400b40c074010740f0090502a007940f4507030902a07550001441080701c2103502080d0840d40011540458004005905580c10366040036080702800310b82c1d600c8119000b600d042800 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 824047113 1250 824045863 824045867
    0x11211030118080306060405060705070e250f110102030703061e0b12040303020d090b04030f08012411100c02070e0403080406050a0213031407051915020f0f0c01080601 74
    0x2c0d00c42c00c2001c0c01d10862a140c0e81d80780c0c803c1c0d420142000381d0048050001040784d4540001800d2558090002003544515000242c90b042201801703c5944000f10202c00300c45015050000605110300e1500c4941035448480440e494402400d030b10215500010038405001d034075400510595a01c41511800c0d40c51244160610011521076010082e20500c0031010b60b4018240496006d0f02078107000d803130007040408000032036104030b030100c440e2034540b0280000e0540c031854110040c40c650500d150103505040c124201200852010149541d810a60001d168480d91f0300c030088029500884031406032080030b64001d8022840aa07006104000c4000341c14640388c10010301950f0540c558070341c00e0704c1310740f00c460292030b004265015094003004032095105010741000000d5015103021402c200c2c4002005043c00004e0b4441445207840d07d4140304520080c282403011208860501032240320243c0f01a0701340301500c40b0545041c007840782c0c2d20307414242c04242e030022200c0036a030780b0b5100e550340401 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 824048363 1250 824047113 824047121
    0x32a100e24060d1e0602040303090312083309090a020f0a150305070c05030705010606090503030702030303010b090a080f0703121418010306091503060e151302040b090112110301 78
    0x900396015103224010740210b504e0313011100d800140200e400036000313a551290402d9038010761086000848540d000c009024400307a1010028110f0300e048807107824240030700320392001c0043c600e1a400a270725581d0211002001d01c1e020f58030401803c40c24640c41c20504050304d9180180042e4043d2183c038864901c01c5c130740190401c043d10708080400203500280401100204001403c140601c00f082d03905402003101000504180d84c8284000b05105080100003000980c0a42c0600d010794000d025440060b41e002c01903c1c1514070f00d850035500c940419002a51b502c1a55204010328028150b072080b251780c01003580d600b52070154100740b900c2180c94804669a0303004a107244035105081c800c09010f61480c1101c04014081454017040c2d00b034613580d02e40202e81141e502900e4030300c0b00f1402003007001024010751081c4030408015004001a42c9000c80d88138500405264600d01c2102c000011540d85070b114646110b0080c100c0b0382a0b68441000c0025070035807030740588910503c040100b98520301401 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 824049613 1250 824048363 824048371
    0xf0201030e3909130b07120603061a030f071404060e01060504080c0f0a0e18010507030605030715080403110304030816060b0409030504090e03040e07051308032a100e24 74
    0x51445082902600c44c1c1d041c160002e424001000380305021014280703002d01070748d400765015410010780441c400d04101c01f41c0500400d80e6010341c01c03c40504808400c045400001c6620b240c900080751048880060014905900410489124100007242040d80007014000b902d1003c021640c94135124010416446400750803143c5c820b0121100340111b460038207080d5000081d1046c80344080ca1580c004a00350f6804440040008e0f40d04e460030001440d00f0080740c0700520044500007525505000e0003800d0100040003d418008241e0481421010405c11a0002c5800001c01e42d01e6400308205103440080c83c5409845a505090310107405103024850300e10900d03490f40b00c15203043d14000802000d01100900c8440034003041c400001c2192008050300d1194803640d071850359900082c1402ca200a40c02d800011040e841404003080d00084010f5041c807d40c0d0040c400480d45440b0744c034551401c41040e919200403400e20007104060140000c1c0100003006103810582207800e41c034080003042104503 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 824050863 1250 824049613 824049631
    0x804144902030c0d050102091011150c03160215070906030b040b090402010807090306050c09030724140f071a010602031c1d03040f091103040f0201030e3909 69
    0x80300c60f58510b0445110f60403188071307400241c1040c1240000858200355486402c000c202c880d0030340150b17800d00380030b0031400d00695101c0018071708100301d6030300e100e000040400780c00784c030008480b101c202d0081003407008403150344180d40d800313240000000740140320600c034280c0440d041c190011024034040c01000c402100242003298595030b01e0f001121028400b5150109000140700048007103560350180c20b1095403a10f030f40c1e40d82d814880e018186005010742c4071614914200c0c602203524142a0901d1407482d9061400820b071001010b0480c00e01d101c0c00351800000f080c005220003c10458500c0e561503d002c509404401d6aa03915050340c80344241c188440035504406010407580d00319a1100c030203086840913213402d020b5000740051a40c0c4c030a800c90309090411801c108058004c40c01801030081c1443d948604604040d600e0150300340340c5900c02418180c40703980501380c0517800c00104940803060356162802c0da01040004860010040c0301c0b44051f40b14400c80e140e00c0c20003092075400340400c6 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 824052113 1250 824050863 824050873
    0x5130503030f072303180703020d080708121501030605010806030d031a040c02031b15060105071511070308011a071209080115080c0d080414490203 65
    0x103040c00d52074084009005500384100a40302c10740c1d403205070404400240040d000591740f8100712030094240441010036104036846110705200507142c140350202c00c00d038090102c680718030f011b02d0300403914090200051072000a03a4204101d40d40300c42d8007901d1960080e2010070600361283c0044480190070cc0e00355425500806600403000d00c030303601c00030701d40b09803510440701184000c0014080e1802c4000585c0140c1c800305425004409001e90f0402718240c2d18000c24102c92070025008036032400820580c144040801d95009009046e00c0744c40c08c1c204c041e1820402003550045824440c0c004080540000d41c2480010682422510034410006101182a03080c0b10003a07541d615048903081180c01045106213002603507007003d00a8010b0001030301d072500b81360350404a2041c40d11014418480c802e070100d0346150003080901d0b0441f03042e103226080f810741c540114004500751080002c00e08048607008000e80800d501942c01d0140003050252090640b1651181c0704442e01d614200040d5242d044 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 824053363 1250 824052113 824052121
    0x140c06120402090a05150f0f0a090618380a0308190201020909060d05030f0f12060105091e19030f111e06030a0609090b040209011203020622080c030d0513050303 71
    0x450004e0300d800b00b030b0007017500d01c408c000c07080401c90055840e4081c80600703072125414012000801c680040c0d4180c43c040800005402c01e02452400f9242240036441000e1015000c0000e01c2d01c20643c0c0740400040c107004041d568924040c0800c0e8088136040321481c1094884040c002e00c107000320303900080020301100460b29010108503011a00010448051104004803020039091038050170f101c2c6400f02c01151200b0f0004400c5a01c104028501410403030b00700703c0c03200701d40d48980880c6100810048543c0d01c440f851300c08070307110744440c8641c0e08054030420000001c1102d200d1441c000d1512510002e01040001024011743c05c03e4132480c0ca50060030003100b1403c90030010041d40d030182c01418003090b665514075030b500881d10402d42c15681c0e200c4010400c07080d42000d040749801408004080c00c900313182c980f402521000c015200b01c503444940b030040540c410030b02802003040b40c0c006145560303d20b60300b650140d0b00d42c00f0034025841a4245400a11040e42c812100340013903421401451450f62 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 824054613 1250 824053363 824053369
    0x103030f020304031a070c05120403020301110c031815300721060e091005160e061b0114010e0709060f0809070f14010e1c140c06120402090a0515 64
    0x18004200c0410415815071f43c0d80410010807584005d800728805060340c45055005260940710040307a031030441641005034002c140c80020856240307407040c1200d400003a4074200061200c21001c0c05445c83d040010484c030707044402400d05c1c003003c82c05500c8104031800000210004c22501150802d020800300420400000ba95110b8440c0582849100040b000d0303c0b01200c071104401541c54903415440300450403641d48151084036003180308821010350041c01c01000400750b00500015a02407500802c1c9010102c030288421005204814000d00840464000c800c4d8015400d00c6500c0f041c1b00002e0120703840c1030040045800b036420030b07a22248080303407049007075900c00005050f025940c481c0140000d604203854031a40050181241c5e43c501030b8011800050200b003044410a10401c0d0a51041100344000c00004000315404104128919590440706040c0f624140c003083d04035100069031101549460716807440345101b2909040242ca42c800746402300c1d1811240201040b1007007803442c02d585 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 824055863 1250 824054613 824054663
    0x6040b090f0409110913020a1409070809072d0b070b0a0e0a020f180103080406112d03070c260105090c041503050304030c0504050c1602041806050f0103030f02030403 73
    0x8074100748030b11b071101140c1d020405800455110030010220303610810300030b2500c203000c603801804628040c2c00d1800c003200f059440751001d10030700e4a40d40406041c1c150a4090202c03c2019020103401ca000c0700d65954041300443c1d01c421401c0310035003c0304e80082c2d07405496101e1070124a20f900002c0c46002425400e202d1941c21030b0101d542d00540a14440840c1c0c03181d20344541c042c500c20310741192039500d000001741c01038558410034240c941000601e50700020200b10030140040b1844440d51080000c2010b550445c4a41c0768041d119040c05800030850180b01e1250483c8550700001c0f801d11401c001d03c0d1b1034200e600075612101e45809c4a01600010301c1d06801882108150084003143c0a50f03940d1034a240d64403c0d80308a07480c00c0c0c0b40504011901e440e2080540c49406201134900d0400c2e030b8030304102c000c004240000e02c25070303a440b0101061038110544007801b13940004200500c0c100344101240300c04091008500085414920140c418404405e490840350300c20740d076044100910071415088 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 824057113 1250 824055863 824055871
    0x5040c110c0f0f060d152304050a06080a0c06020601120308240409050f0d020a0b0a0513080409090c05120c06211810090b16030b06040b090f04091109 66
    0x2e0101c00f00295944042c01000004900c050005500840381b400e420068090b42c45020285010000c0c2d4001a030a040c0c42c0101d884110380024179559100c046d14000d192540081e4460301c9041054400c0103010580031041c0d450360f03002c44640ba03a07a084e18030b428a03e20708000b070004030002d01141880c0001180040c9003503412802c0c3e80b104885401041c02c4450f9928107840651117012206038030081440510081fa031341d4400b0380845009500c4807202071501401803100580d5850001d500c0502030185900c0d603641c041c01040d9980e64480390702005e40704811003035031500c0052400050074076120000410805001014101101900041006a4000440714540303d102030a1841504900e542060311450281074594200300000c240035113407030400710828041c0741c41c1120180100b1108649a0b0f1302030695030048480d488003400c220082c0141d40c000942195000c60045030051029000d0001d401041d180c49110b552684c0421003928000c0d0302c00750100300c81c10026507050500d54086540 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 824058363 1250 824057113 824057119
    0x60f0c01090501111216020c0108041703071e031e0b0102012a020607030209030601090b18040c060e0312030408030601110607030f0509010c02071e08030301090605040c110c0f 77
    0x19421507882d1a425201e80041945000100040b60083e510a001d203403900401c00840000c400403005030302030342e640041118035041c042404009010080c039042041d070b0340d9403104da029440c2c0c100120003400c40c001c404d904d4070030005600314140803103100c0d00c66a8a0910f442113400080c40f400701a500090216408450442d501c0740c00025426060b010700039406429900e134400d440c60002d000904110b000342130841014010040d4075000e60b4002902e5042d01c00084000805001410005186042c07035220741ea07010304004100014003605540d0318048840944404181e00d4000f000c150312001280300080000c0414030103d00400c04110140da400341060500c820300c074071170700c690502c0c08400300c0390000082e49800024a40c0400f034060150000f41750002400003001c440c002030b444074070b90f004500207042101c92100442a0009079a001410000207980d9256180c070408070141c8000d006042c012070802190700d1441e4492201610700880d05005040300c1c801c014108036600c0180d28070fa41d4 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 824059613 1250 824058363 824058371
    0x4110c0304030b2d04082d0c0c010f0c020f01210b01180e16020a0203070e04060c03110910030209041d0c010207030c0b0304030c0c08030a0e0a05030c12070906030b01030c080705060f0c01 82
    0x281c508204000e4211f0101001d081030b480d00d6001d140f407032800a02d15075207410001c0342c1001503c203c0e00000c8540c886941102c0303039a40310146000481e0115920317440c08894035407184407070940c0400c990040a451000b130307070388140d8094008180350100d440703440741044000c1c0703800008152882c4500112503442140c41030f901c00c032480e41c000030328045040e000520241fa03400f0900081084602c92a90040c590342424042d0400d50359a44401e800341d0503083d4007500034400340d0403400b032080c0c3c1102c01c5800300410401c40039440403000b600c52182a200c2121074490030604081c1076000080e40f00c11a039102011250660074800d00c103940380c101130b000310180b001c40441200002d0b4070804a101414445004640351101004001c00d48840510707141d02422a4441c00e101586011500184e030040907100290060750107064903181840b29408110a18070b0804080200300e492400b040c101c90060050803440382c0c03603048554449503a44030b400e07440202001181c40000c500da01408401140c000001 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 824060863 1250 824059613 824059657
    0x50d0b120703051b012f151801050a05100317040f0e070f09030c09021b01061706071818020714011b030908040504110c0304030b2d0408 60
    0x5458076905800445680e084102c055040b10f01d0b010310003481320824649104c09000000340007842150410411b410701004025900091104100b000320200d60b00122034210325101c0b01096800c4c0801605949035401c04010411f59002405020301840e0044280c400700c500c0e50340d613140604001e92044040040c24800007400141c4001000010700d00c802c0c5c040301519110100600440c24044042c0621a505009001180041d0000b0040c2d541c0b0420069603440020309041d070400c0c00e9480030070b8560134044080307503103c400303041000407440c00790445c0c000780c03610a070a42c2c64281d180c1400500d804200020801104101180c840480c48028014a07040d100d80710304900071514800e1503440e03910b0309005846a200c0111740e0780e03040140d2504024405041e03582c80450b204030b100380b5219640701e6090302c011108a004a644000c0a1b00840f640c490340e0745004401240c1c00c4428140c00800f40081013040e22414040e11096094807241e441c0581e036690324801d030b07034001882d81f81d81385416040700 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 824062113 1250 824060863 824060899
    0xa0503030405060105011704030801091d03130806070c0506041518140601050102030f0409090311031c150b2a0a03020a02030105071107030f021903060b12010c050d0b 73
    0x1940960700400c0070301070395810500007429007049601c28101070347c04401000042503202c96040c0c1503c118800c0400c009052840070303003c50356101c0c600301e1700e4000091199414080159a001150b0303084094400079a244003064941182d0440083c1054011200203400a90703000120302e1b0210820070001101d9004154040300c100420b4411180440050240c04080d401000250f005003001d10095180a4141c40d03520101c0c000c034400e44c200e45403a13112001c1058000c5104203261203410040703a40754201c02c188108084078030885a2980d62030504c0b030408415100d2411001d64030058001490111000f803901000014002c0302c03002d1901304152220040014001c0603003190080e80140a2003055004050031550003034010307030500c4039418007002c0b4504082030110499811185107a02c4418900204402c0112030011190210000601008001441c0e10011040d0f00c1038814000307003d00c3d030120b182221442104400441c1040c010162020103d402060381d4200152084006040000c02c0c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 824063363 1250 824062113 824062117
    0x3020903030708041d0a050c220b0703081f06090e0709030b07350c0a23030702010e0f120d0e06040506190606140d0b0d080c010b01030911060304050a0503 68
    0x102c252009641002c070301c000178400700c01d074002444403002c01403810310391685400b0b07110380b1b8a200100b0b6840300c04451158203600c12a0001c12801c070219944980c9454010441e03802150b07000100d03250080741c000b410000078a64415288a604c5180c40c9a05110250301d1584005140d4400c001200c48084005010001814021160350300c9240074108011151a140362401c6030f4220b202c050b6200619003010004080c54101e020b4503182c603990b9882c00c074210f9a580a2600451103155007810301010003440500442c410187c1da4002c00c0a074608890503502d43da07907410080007030390012240460f500740b104000c00814142480001e403d00c4c1d02010719080a008540035280340e0440e07010400340180048803080c2341075203102c0800100e0301704440905030500140894025440200340c140011056911519000100074a00d48500c40c0030301d4880017561080b489a100d5500b8042c512549501034012448020740c020340c550b128052540030300060ba04000c100b03840c01d200744610040420380901c0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 824064613 1250 824063363 824063369
    0x603120e1e2413050904020d0206070302030d0e060f010501050304051f2d0608060106080f13050a0c180c080c0a020703020d081905040302060901030b0406170a0516050d030302090303070804 83
    0xd0940c980601080741c008503120f680c0214040c0d40d02804120042c1d4800403120000341d412108683c4070005418200c0c0340d03024030b030041441240b178802d600760074007000105188950f9000d40200c0c0305a80300d000460722400306981c01400b644c8100518614000c0410061002c880200000981e005060744130810308078240c28054409610038000031900f40d040d000745005450600001e00301c551418900509000300101101001c054610100d015140e00c0803220008503080801c99036400960f04112024a55610440705a0640a040940c0b0995a030003194030410158039221210b581d04000050b85e54840d81e07021045014032a808401a9a2042c0284190303010300f120740c1c1c482000c0304001c041d10303203580e10400074004140410001a602c400448201c40428038002c9244000200407901519050f00b0070300100e901c0040012207400d00007100c121031030064040714460b000c80d241c5a01c034200140034050f0004014031071000442e00070780041042e000003408407444c01b845c0e03499495041c0c106030 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 824065863 1250 824064613 824064679
    0x30c0a03050d15061205040201090b040b0a0f02070503070323030301080604050c1801061809020c0307031b020a030201050f040e010f051f050d0b0a17010603120e1e 72
    0x1140030415900203100700c851543c0c1040c036656040e810490041c04117844c0501e103420f01900d038000541164800c2040900030407802e10390a86440e100c50f0074046a810910740103000404007a030b40780d5640d10000d00503081303c0e801740c017030428142075880b031039803140310b2004c0079503103038a0400301e1010800e080000394002d060041c040c00083c00c0c9450603e040030079000c046845041c0c1708608200c034580b040304041c11a00241084919900701170200c1c8494406039010854181c404954540401d07000f00013080064400d135a00380c2c1d1401480f910030b80300c0381c11400103500510030321014030040d401040240341001c00f40704c03074034102965031907030000c0300100b60800c00031400b50f40420499820300b0101e03151307050003400c016007120034440720040150040c039496400880d204c000032000c030b854081b001d07000b07024014040c1d00494030408c9241d01900d401e10003280c02e984060000d108040c41074071136280118000701082d428400082c1100c0c0012890f05600341d205601401e0100040607030f0325000c1010780a0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 824067113 1250 824065863 824065867
    0x1050d090816170f2a0106061d03010e070603020c070f12060501170a0602090f0301110c24060105090f06030f0a05070309050c280e0411010f050318030c0a0305 70
    0xb41c5042c4030b4604480c1d000303041c01007041c001d000d0070126120030354052072841d4880c0f0010840b4070056040ea280101d401d0b0046500e00803000c5401c550202e001c0079040814508001e980c182401071500301c035103840b441070850304942c0051041a120b030f0028841118144100d52600b901c61001c6c03030030888140d01c010052341540c29104104000390081c18018806c8811200e012545843d0558445c004100d000301801d50010b00094595121380540f241040050020040b00507040b07100151903000c0200304030113105000d11281065030001054400305034100c1380780155103c20b030054625030428440180c2c03103140784098441030744a00f40594410450455000007509121605c5400c841e805030421007050f00307201d505c401003000010001d0207408152001c030001028105030407600d484052000307814640c440000519840801c031864000d80c0540019644290b03050015102130300000d0b25000803134004c0c00003400b0703c88070400300040320881009891070100880107490a05100d010120045100 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 824068363 1250 824067113 824067157
    0x9060b100f0228031107080714030c03030906040e0415020a170601020712020d2d0c21020409030c050f070e133c06060603052401050d0908 61
    0x104100e084030302d5078031042c8641102d808290041d103c1c0d2401c180034003480311583c51217079100c5007088410000d0441005441c100c07900c5901a00e030349041c03200243d00c40c2c403450001d44001c1c0780110417039102c41d2009200310b140ca4030301920b64030811740007041960b0030840c0851082c141d002900080c104080c0716503c1c21070350301d034031001d800300303c9409044507045501400081c48400242c4000d12442501210100400da2403460105003030241441e808501404401d480790072103a1107022000454464400f1881c480d444001070160b4074941c0700740440b030001d05510781c0054209540140700c981d00074078192050390100d480d224a0300e14056924001907002101c20811024410300c15500304500401060200006d42c441c5111a040941c49460303e000341010000d50303200d10702001520f440090440840040c1e070f42440c1005119611415010038100f000042070400e443e0414551582401c083c0008044484011161f9130031151082c0e00c2c0e0384c0c2e03035280600410034403400b800d6244101d8000c0c22540035 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 824069613 1250 824068363 824068367
    0x908031314061b0c160b0306031c080705091212041403011b0f180e07080a050403021b03190605090106120c120804030f110a080312040609060b100f 65
    0xc00800c141a07000300c4244080070f9180b50192801c00070222001d5220324443c4c2e4400d0400e01000343d0030280300110000003405000301c001461141d4012070135503e8182089110800c04080d4894401c000f624620000c1c031500e000b10054041c0f240049c0460a01050004c403071481c00c1c0800741070203a002000b041c02c015080c60149140c070001415802030011114001c1d00303c000564104040050020414003105064416081012031075948211503044555580c20203007443d0041c2c84540010f044a400142e1200701402008e01896260b4010641034540305424205100600c809613803602500c80c1e00d81140741c0c50400304070401d020744d0300020b950030070101c1e060864070164421503188054250400114041c424100200e03003480c0e0004440701c00701e00d0171050341d02c00c54000509442203001d01000f03101415202502c01d185c161800da0123a911602500d650b8000c0f80180e24180d0a44400540040c0325500815a1944603c0c00807401d5500c000010f4030038515900000c00003400141c0300051300c0c0d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 824070863 1250 824069613 824069633
    0x60f09020f0409021804050c130c020c100804120504171f050708040f240504020f060f0f0c03070804031412280c050d0e09010b0c06060d0609080313 65
    0x70304116000c101c6041280d01068040102c07244040804095000190030302070140910740ea9104000e00100d686a260084c050042201c11105001480785945000c801e0400d40e1403250327103007080d494985444e03450356948410071400e548000100001030200250310300300300d20001414109200a01900c650503641c03105811885001c03c5101da05003070501c80296082076400340c0040d00700c0468008414035007089805541c0030440a0103c25503520b0140c0500c406030700280c0580d108544a150150005007001100d00902070407440c4103808200309559011000000d180944a500540741442259114540c03280c20503030090700e0804080c1c0050070107a10504c4204a420044404107040000d5103a42654400519641041e92215103c00706100c60207041c880c14030a0f8081e0440e04241003420000341507007406084580070b00c40407000410070021981c01d5644013556071005000350b68421081003054041c0003025545541d8a04000001c96a400c0c01140300c0da686100f6010724002d18602a01d041c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 824072113 1250 824070863 824070889
    0x209130b0a06121205071a040b07020a0809010f0207080604030801080d0305010803040e090c090a060503072408070c1401050105150703170703060b21181513060f0902 73
    0x2c1c03500b4828004071001c0940ca05503140c111402101e01e1188001c141d44030712807910080c0007100740c0003210342604180c0d804c4034411071040140c84903c0e02e0305581070341e0710084444001c1201c1c500b803001d200c44d54880c800c0424280304500c100c8054550b212807090805400766801c0e00007a484034018819910100180d8418100c246070803c159031604420319124019801503105605210010500401080003540d03a0580000c0549026040c246101c80042805200ea1402030040d000002030301000d03810b004c1820002546400e144c0c440542d02242e110f2001403421050290b005d0f4540c0101e032030050786264000440d000081e603941400108444114050801d00001c0d40800090380040d034420b83c2c0415140580c1e1000c48943c480507800e034094002034204a41d01540424503a000c1c001d4000780c40c640c07407491910324446860305074010003003060b9404016140d61091507042c0390840c00c3c0d800c00d5840408180140300c0c0300341584c4e8000548424400d07070301c40030f5200e0360f4200c1035191420070600d403 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 824073363 1250 824072113 824072131
    0xc09080706090b0d020405120d0e0102121204060219020307021c030f080606040503010e061b0702030303131a090609060601021c2006280203010f03020415030209130b 73
    0x640d9242030001444006140540000c2820100740340360f040302e03244c042d6000340000400a9105191010312a5940d400c1041500b0010f009210644130715400804e20729900e541e602500b0b85845101c0c400030405803c041c000b1507e403a400c002041009108860701c0d055094290b0103555501101d004108580c16000d01e20720707040c079120800b40000783c0c003c883d0050809050074102c0c9541c0d5000700151181c002e5038001074040d4240b5004150802001c03514610039a00002d0300b65003c0704641d103001041c010424000d40550040000c00e80c600000c2042604981c4a072f0001454100080c080c03824100d419110388155038008014882c41910500c29142d02500038401001e00140c0002160f0f2284000d01c9180700b4070070a525180b00489030307000c00710443c03d0707414101e69660500ba59440c28220a182c0b20400040620008460005031030089038100c0e01544440323900c1c03d05503000c00000b000d2055090000400c1c0302000001030701c601c450948030740e407245082c3e150020181030549039014010f1140034 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 824074613 1250 824073363 824073373
    0x60f1e0a1728020405130b0c0d1a030304120c031a0403020c1005190c061b0206010906050a27091103010b0916110a06020414010f0305070903141e010c0908 68
    0x200001d5848640a585901240c010035179496184c21803000b80c038002400340000700894100b0100740c3d031410081c290144004010030152603000c8255801c1703140b040c4559817540040000704a149510000b04c0c178544d008552400c2c032103540baa22449201c01c0540584c101c0700c0c20408200034180c051100200c01c94040e920003000e40c610b03102c020568406c1421603108081e00e00500d080640c40b41c40179550b81039204000f00029250038103401559100020140d0051141100204000186000d42401c40c0c1019201294950801c4072001c0c00200d400c41c25002c054030311000c0d6440380d6507070080c22201070040d102c01d60124004410b0509413184040e0050080d0402800d004080b0b180ca105032005c03907410b1404a00c0d282000051900703214140002030304060000c00c02003614030440c141c403000006c00362a421103040c500b02040e0107840c411a2204085080300804001007540007060460201903002a070b82c1101d012074030a0303880120281c0e4040540c0d511100200380079040001d0a000d13008204c0100 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 824075863 1250 824074613 824074663
    0xa05030c0a03080f0f0d0209121906200a09052b11150a03051501090b090f13091a090604050d0f0c0b1815060f1e0a17 52
    0x50201c404610006140c40f100140442c403a4520009442e080035550040d60382d112003140001d006074106208692181440e6900105c01c0500000e0380b5070320403a40e15080e100440e45807507100060040c503130b00400c50b284038410340c144c803c0080020f058084258a41c085031504000a100504054000402915050360408442c3c9074100280d250110f601030542c40d0a00c1200e00071503c00b005074040c07440c4001000c2180d403005074054000520880588400303c02c101d410300c004448105a80c4200c5204010030400401142805616490354a10180c19411503e12744550f14080b0b0f40703046000e4841105941c0c1021403554100d011503000039110740103000d54105502c03084e440c0c51040011100b44810b00704000c001a004480a81950f40c22003a07a040b42e1a00d10380d40c503410080034451480314062140e40240000b20080414080c0c880640000100b00740203081c00b50803283d2090381c041e09006400d0714000350b5107280e103203800f40c400000e07503409080d00d039030426150445141001082001c185c400d1 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 824077113 1250 824075863 824075869
    0x1523011b15050a18260c37020d021909020c0c06040311100e0306190e2a01140310030312020301080c011214090f0706080f0130110a05030c 61
    0x182012500507406580000b210401030305481c5100d0700b441c0c02141c0c0491240d1000101250b82407000c01000701d0640001100da0b008a801f8a4562000c1220002c1c200842c001d81030502070400300901c0a080c0c1c94502151604c00100098980d001c030380d150782c00040081000000380860f8024100558540c2d04040c2555640c03c1140c1549603072074010340d00c0403c1c40c9c80c1603100d0010340303d207a0805015111070b400c10b4070740003060f5081004000d130840c0c00c1042600480b40002441c40214070071000058540c524105802081e290403001141000000c025048d042040d040080d4021b20038106200c0c1000d1851034041e00a0030030700d08400240d031040c401040400c0b000715010400720800d207401c42540140210100042814451032841d1142ea0b50410100c84800a107485501100300c08468504d5074441c401c0342c0103402251200d8080c20550010401440c61a070282d149209858081c0500c2c8601c2124000300385203e50305442600c0b441168542d1400c00c004244003400098000d004281142404 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 824078363 1250 824077113 824077151
    0xf0c0626070509150c0102030103030818060a0507020f06100e0601091d040807120305071101020c07030b07020102070f0b10090c081b0408031b011523011b15050a 71
    0x30100b40306000480712250b035940700510b40b0032000c44c40a02d031503080010916000b90000d00048001c9113404000c81c13030450720104055040b0060340f0041483d55034050607000548400f81c100415407048281450a03202e051000030f10841d10a00280c40c024035050041d030b0403400191030345040c00030754842800070b0a500380b120811140382d00c503c8800c0d40c0301e07450041658401c43c2d0010305081c002983c40300045515402c164020302450343c50b10780c7c504c803075081c0501b00e00c2100c0b80c0e107000d5400f00d00200005070160701020341c00326050000505040301a122174141040c0c40300c040f13886601c0141000150303540c4401e00c0c0040c046440e010098000c01c40406040600007524040c1d058101070b009805080b10b043c1282d000d88890401e584d103a140d4510802000003003c60784e210154280381004000021200c00d100844518840c600c50003021490144401409000362604200c1e00342000070b60785503a081d04040807440f443e98141c8d003000c44412881240d201415403041203080141c1c8040038148124 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 824079613 1250 824078363 824078371
    0x705030c0d2d05090c0111191719080907061b061104121a07020c0118050619080603010b0f040c030f0f060303020622060c0c0f0c0626 59
    0x1000898018070381c04028842a60a15007030311041c0b0b41d00c08a01240c0e1504081d014101c1c020440c2c50030411000151100d00880c0c031280403641c400c4400340510700e0442002c000d07440c0145500c140c1810b2000a06056500400b05000041c444507030f03000c141540885017551100294010304900c1d400d00c5001401c481c03004180e4041c0500c1d0004c03080900c60300303510070b20500419900f800e070b840f562605844108d840c805d01c1600c8196100c843c0030704004803086014072540c4140d01400b4603086020042d611032002c2e2580e9242d440711154040390b99101c9c02c000302160b1544d403214002c1c0c0401320f10010480703407000300241e0283e41003d8554002d516490014014110304a60100d510386644800310010320742d0250003211241803800780c1590141a50082c81600e000380e0076503c1e01c0d034840504424200c50259a407000c1500840c0b48000326125601030f680750001490300e400c4d0b514036030f155403141803100301054034641d003c00b00412a40c0d400c90304041640c0440034424020f00a1000b1051003804020 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 824080863 1250 824079613 824079637
    0x203071e0905070e031c0212250516090f050105060a120203070507051501051005040608061c050102070c05040c0c020d02270f01030c0e09030a18051c0b0705030c 71
    0x440030844041c0601d01d6005001d00207402c84240701b01d031002c004c0d84000112019005030250220740ca00300402503080300c8036800404a181148402e42c1210050104607030b005842e1400780d0048440040c40340c0c41808020b00b1340140228221600c2c51502d0111141a845684218810003020303400300e42042e03034000350380050040140c50f6658110240d50074424240c2c01021801190707114404006110390080c1a280c058401810840154005440a2046d4052580455217600005003d440c2152002401c030000003c81d0070b543c01c066441a0a80c0c000c2d110807222030741d4840c13080c401c504181c403520710340030003a150007104800d19402007100901d080b0340c06805a51460802d161800600e84424004142802c40c1d07581c61410018881da0030000b07020840788051002d2000800c0400d103104640a001c207200034501c0c00450410546914681401c0c07810048000d050025080d80c40d0074503000c07026017070640303007290022a10b00f01000b601c00500c0401480310500901030301000c007609640c4000616 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 824082113 1250 824080863 824080871
    0x3050606010c14150405010e0d320f031e1608040f0506040b180106150827030a0201110711060f04150306050123310f030203071e09 58
    0xe030408010100702c241c0034980a2280308141e0002c044c200340d40c1403066005000802c030051f141c1c0025a00c849080000c240000c2480c02000c8010b0444c000600905ca505c004213003c429103561501c0301c0e5000017140890000c00403040101d44640310364545403a211010880460b4540a51940c55402815865170100aa20307800181002078807d8046604c035002000c845140c60140391508800004413507010400b030803080203192070701c01401110f00342d541103420080b8105415104403802000101802c8c04130288075031140c5c0f042d1440c1e80c0f5032400055030000e5039803400741e000c0103800c1d9003111a081e40080000c01c094008500903c01080d5074100484406982d1102c0024105c0180200d800c40501e0075041c441598200c0d8040c0d1003c400c0303440030b880c2d1800607140351002d007440d680c0440c0d6200d4084020068840100c6a120f100134074500300615a402d00410000100f00002e4143c0000c0d1506007124014000c1d45000c0060400818156828200e041000c0031144124966441211003031503d03 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 824083363 1250 824082113 824082137
    0x807120c020c13150b0703020c0d020301021603110d09051f02070e070e040506030d1202160b2a0316030f0b130605040e030c0a120215070201240305060601 68
    0x20900c01489980801031100c6a4508207000d150001d000201444c2c0d1007581c00c850010b100d45c6510261549550107401501c8180c2d18481840081080780c8001c0764155030803c220038003801c0d21055502840d0007a0303524000d42c0d8124140518260060a206083c011100b80402140d51240701301e00030a61500200142060501c00581c07506a50350420b4000440040c1003140007540407001c1803203184100c4042c4116201d6009150f11090004005800600e41d1744900d80c0102d415001840340c010310303000c5404403c0711601c48003910315041d00c404481c4680f084e00b6143c1011400b440e094048001811140303141819111801101c0c6c80328046810715442c0c049a038a180440d5000c58105040681000110f5082c04881c00041100d8010b40d03200c0c52406c402c481c032040000064892004402c40240b2100d04182c0b0386d0b51040854583c0c19046210b601c0600c0000038541480b640070751801d8001081c4010686c80301c10341c00804081c80b101200d14850f041004c02e000081c1d035604614282464404055 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 824084613 1250 824083363 824083367
    0x191502010905070605090406050a030317040c080708160e0601050403031d06040803070201030c0206060105070609020d240c05030601050406030e0109080a05090f0a1202150702042a0807120c 83
    0x850040e020707000b4010700400180c880c5c3c1090090280d11350440d01048020f8486080209594050101400250440d04000310411002540c203411030302400341800071568a4800a1070400c1d1a0401c02c0303250441c0100200340c0444912613800342c10035506c52800d500c0d21100081c054002d512015042000304202c41d103040e08040642054418007070700541d6500d460b040c1542d40c0340e004020403030010341340007171007000d46101080c1c0b02d0080f0360594505240c0002501c660019000308070099a2041040c5149000194041c2d41c1c40c601d0700840504500c201001032981c81150240010300c010310000300104050f80ea800401c8500f41d420038100092400000c003001401085040c2c8000c15091000034a100450b4000003d803044d000e084581801c458182d4044c0001848280f00e003040c0c418581224000501d44006c0c0300c030010300b119440d1814540306400180580c2c901980041600b00b1050402200d040c0e442040b010304541e82c1080801420600002010540810511104940d44a001c00c0c003081c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 824085863 1250 824084613 824084621
    0xe09060f0f091f030b010e071d1005090301020d06170604230c10090f080f0c12100504150b1e19030206043302060604110403080706091119150201 64
    0x25100700c07039040f0041d0b00e0b4540151068000c3c091099411161000500da90b4030a4403030329508841d1001308200d0402c1b1000b03000e210040c6101081c280101031010464688091000d00380c98030070b92201082080c0703030000d1000c03d03848490050b02c070750b00018104004070360860300b81801c884902c420200165200500d49091118899185900c0020540c50b00400d50b0b01c05d002909441c11140d003902e001d65200441e44e03030755200d403012015a40060107600400c0c50104c1e4441c00300008501966103040d203010080f4100c813030403a02128001000010f403054141607101e96840313100151150924a001c0d09044019407081070607443c8680e0303800c42e000c84502e481400e130300300840e80601030903181c90302c800e000005414070102206c003c6500604554040500d01d2122042d041c40e60003802c2750f1f86650301800094400c201d01b09071391800030007000000607200b030000d200b03aa000b000001203883c3d01c0c0c0b030101030929214103150301c41d000fa8860707070744401c8501c08144c046a0018040c280586541c3d0400d0b8050 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 824087113 1250 824085863 824085901
    0x60103031b0602091c0c050a1413110318191505090717061f0315021608041203090b2104021f08010e010603140a05090106080d0e09060f0f09 62
    0x500401d070038140315a038180c0c5111103038031030480345032559214018000040050300c030f000c07101c0303000312450720701d40c01c05500c1040000400318010a9080300be0005508940c0241c4495142e2252040340c18106002406400081d80300c50b020300d08240c1c1c50b5140c0d5940d040304510b00442e0320795218049151098200035100041982d20b08205074540205461905c3d9541113448100001c840c000030004000092096016250f016a40c0d036000b142615252000390008620f0a4580c8400110380004c030305400040c2c00241101e10b0b20050f0f00f001454003d0041480740c1c46a40070240500243d05840815888034030b22214142e1a001c281d51940000350038600b25518400c0440c6c180c914188d895544000d24a06035145d5503071540c030690f80c0300000c07005c85280c40c10f42d1110342400d0000c030346181e405411503074010452100105200c0d44407411230381450300d07180c41c03200401d41030004e408840c1081c209442d0700140465104052007200030110f04001d80c0b0744400d80c40750f41c0150004034003c9003500c0c54054 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 824088363 1250 824087113 824087119
    0x606021902040e010f0c050423010f08040c120602180907210207060908251e032c0a060311040302040203070909020a05090f040516050d0f0509060a0b03060103031b060209 75
    0x81000c1d0001b0240c095801805446c905c006a11608401181d0b0b000c00003010300810307035400b100c031000a241180c240901820449100307030b0025000840b00109504140b2850155800507546c01e400d0044900032004100740c035000d5040303c4100098a078000980000c525914448da00d19240c0c003001400082c4100c1c40018000b600c1e00d0040e0090080311000340203c1003406d69001010380103200803c011000818006101000342c2801c0c18600d03980700140700950744a4204052003d03c1111100030340c0f0b00052210030091809108400305241c042c1d0b100008240900341004400d0b0707003003200300c82c51069003c086c0c080e68000010561140c41a0701e644c0040c44140421500c401c40a60000d003654803060b1420f200320302c1c692a80d41d061609100c5d203070080200303420001140c8503905007a6119007240b000c5402c400d545111042ca0600540120b0b0b00c00e01050b4040d00c510700e0015601d00440c0c07501050300340a54007070b03001030001036040007103a4641420055080f006003118600b0b040640300d0004681c0d0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 824089613 1250 824088363 824088371
    0x53301210510050103150f0b09012001090605060a030c1a0f070308010f0e0c0a030b01030f142a0301060518151b01020f0f0d062105010606021902040e010f 68
    0x41030ba502c904451042d50000d82e4240415921041000d0300c4010f540134940110308528400c1080c120700174010554508181030500ca00e1041c115019200724000c02e5440540e51103c0012040180301d1107016400003040b500407014a0071a00c42c0204ca0340140035546c0e25960b8400c03070b80e8400c41c2d03c405036801c403c40401107590790261841d00a0020f4001e20485c0040c01341160046204860011028460740103192140d041542206c0e0460203400d03030403042410303d682c0e55144180e43e2100d009244a503821185612078509200a1003008200a4140108502d02d1201d50302045070503141141d04503061480c1c1b80f600c1e034959003040000000b058081551005c0000d44080d1042582009802d0b401c901c4014058080600d0744c0140c06e0344540d85c10700360b018904001c007001d456130308000350010401c034007000224030741ca0b40200122500001440100d0580c2c607084c40081010902884000d064240302901c11801100203034020100c809000a20a6440d42c0032441460000d510004021110f41c1082c0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 824090863 1250 824089613 824089621
    0x1003020702150c370c03051209010f03020a1701080d0912020607290f0114010e2808030a080412051e0702010203070b011e14130506060403080d0533012105 68
    0x4100c80c1c05c5440105c0322405142504102107000d4410b941a40206071642901c500800304220000c1d40504074040a1042c040000030120b1004603800d0f02170b09441c001003100c02117000300035081c03100da51b000c08032400810080400680740c0c207080d50321540c1d10086034000205071f0319954014a4003400012a8018a44200322040e11100511070486201c50386403410392400c8001100e010b07002010702900200c4099062002920b01c0e45d641c1c11900161800181c469201c05001c0c0c02e642c086d103024400039001c0420700090104201c150007050425040131441c00c8025880045c5941b40d0703a82403280e01d03a000c0b03415401d590003841103940f610760290340084070350b84070020f010406800c146a44d07095503401074080f4100c25560340440c0b1102d2300400350140059607007c645d000e008018540d40d0003000034480000040c40c60005001800102c03000030030356291814005140d1168039030712206800d2103414450700c00c00d0030b200700c8164200c2880d1694089015100b908101100032000134459842c0c00204 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 824092113 1250 824090863 824090873
    0x111914100e0a0b1f0612091401060510110d0f0c0b0717011706011205070f060e041506050a0c23030d0c140313111003020702150c37 58
    0x1501e81034403034075105000381c8510f42289002c4142000c13200c0840004c0704240078444c083c0c003c10358912141031012840d10120f5445001800e005c54641205d030303443d02414006840c0910115151a0207460b002c1d044401512600c1e90300e0240b0143c02d41070043c90141c01c0a01e81c82040380c1c2d110700f90400040700d010f080a02008040240b982004118985070600200d400007603042d20042040c9400010122a42071001200d2040c00149045901344500003001503040c61221a0000500007034417603805202642d0f0901050300c480d00c802800600e0005030900003550440140c40b440382c003a28060028405502d000710600b0041408201103420108901000d910b000000300b4050080440a0010702c644010580d0824a03101c3c011071f04010500000b80c003851203114141c0030718012114015815101c0c008940d406440d905080000303900011a84298101004c0d018101940c0d030301000c0c42c1c25140010700d0313100e820980c003103a11034481503a017001b04200f0040d4120009410a60921200010300e81 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 824093363 1250 824092113 824092123
    0x2150903090d0f030e04110915040e01170106060e060f030403032a030e1b061c0203010909031e0504060e0d06060905040201020f0111040303080414070306020406111914100e 76
    0x3c12400204450302861403030409002d003002d825980d2164a00344420482044807001110340d500d40075001c00d2000144600d41201c042d070003405450b000069400a4075051800d580c03403a0041c9003030000e441d002c5c181030389440d000c079810780c1d01800c4001e86945441c6400c41c06041c20740c210185a03aa130058500c000b4100700720b5600e00c071040e500c00300002d1580c07106443e01c0711280000c8909074888220304030024241b28005080c4190130440341d10b0462014984407040344c04c20780000042558942c00c0e001010b40002040600720f0441110f000c000604103c01406031155001d04003c0110080c5039440644030001940310259001d5000d200391034480d1000e01c020311045a090b40103114001c0320102d000018843c10b4400c16030128154503080c1542c0301510703001c1029104031040d0211480700d42090742c1c2845142c001e548a002d01503950b6141000003400c80002e840f0070207858109114001078200302020000d52036501039032401500050300c1100e404c00d89010211a5003c0c05d10102207000d00c0003080d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 824094613 1250 824093363 824093393
    0x40207021f030c0c0209010b07150e1b04200903010e010f0510050a0806010603090c080f06180c1e01091518090b0d02040e0708030f040f06050a02150903090d 69
    0x15041141500403070046413001d502c1107000e90040615001071100d018032030f00402038203000301c030051404c9800b0b0803500103c5040c1560807010f0380001011607441022801e02206446003141c081c001c0220505800c0c02203280401c0600d0031803000a400c6140e07407404c0d0804515a40040020810101d08416000c0580011540d002d4242182100484e040c6451100401a14090b40042002d6800d250054000707051a0400b550b560486074800034141078200005900344003080d02600c01420409006101036003044120030942d041414031000c9a02c803403041c0d4032051400a01246100303484001a00d848100781c00840500c000c03840451445508004101c60b1a6090b011041c10907549103808411103084042c0648d01c64120a2050054a000c0d0000041c205154040d56142582c0c0c2da525851540911040c09103200042000c0102401d24079084005140504003079180913030b26200251519158071440d8400c000d050040b4504180400940705100f0780070300302c52810a041e0414039038143d035800c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 824095863 1250 824094613 824094617
    0x201180608060f030304030c0e0406020403151d01021905090406170303011509050f0d0c1710150609060518063c040b1c0c0e150403031d040207021f 65
    0x8040f1046600f40003044400700ca420200d00d440c540d0420022803807410000d00f050b52803903028880803020612044401050b05204100001e55065480300030320719078541c22207902c0c641d10500c40d220500240d1000da80d40c4401c2031070701a5555125400045c0213000039040500700f500c90720b415158880c0e000000714103032a120403145101c66403042c01100c0e40c034843e014041d0442621424000f00341400500b00031070910034a620f101c103a0704c3e0101130642900c0340410030a140d02918008400c0e41152088203110901c080c2c4a00c00613085c00c0c0090240c0c0f0007407203600104100014041c900c10315200d00111505002800d642e559114041d070030310401c1450408074001d000701c0b003038a1902440310340c4d106100c4002e40050360605203004001130081e0003052641e00481c4003010b0340610421944101035144420346c490032007400c980c006100740207d051071000001c020400052010a80040c091481a010f01c0b02c840e01c40c02441d804103004e4004d10310001e4110700300100c003500501c481940a088680a5 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 824097113 1250 824095863 824095879
    0x61204030c030206091c0c0609240f0504051203090331140a140a0f0b03160f14030703091b170a150902150f0903010b010f050a0c020118060806 63
    0x400c175031500c40141c00306640366600d01c0200340411074007941034011101c0c040c4200041084803619030703183c4040c4400703440350009624081030740d800c0645d1061203100444003c0820107403a040d6140e55aa010340103442c002c0c450003000052200c4801c00c1116400107400e0b10b0002c08812200e0360044460400d191074400401e41c00004c50f61005091444d10522001801c2c007112034941728000c140e05500350340e1181c100b10b0304580403425204016401c002083d6880416589181407031005403049113020760324017084041100381001035448038803803034076043c0b2103040d960f17079102c421040d0000d056951008051707039100c1c0720b00d840182e138543c684c008450f280c5908104082642004d00d07102e1140280c0203117240754041a902011078607500000540340301810040280c1c2148103801e629803c0348484040e8041e0000d442c403201c3c1401c0c000c04200800a007003d1492071641ca034060100c0c01081035140130006081800d030190382c4140c00c90302c0102080e04028021319150100100441c6080380d0260140c01d00b = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 824098363 1250 824097113 824097121
    0x303020304060b040b03060610260405070b0a05030a15030605010b19080601140d0605040630110f18160e030307051e0705030115090b0405010b0306060702061204030c030206 76
    0x40c01507005c1c07400014080e15903544d4500401200400d101202410003400010322154010f00c0c020201000d00e03c0c8002e8a00380c83c051400038545805508180365040040c00702d400c07072030b800109aa40101008078003103420307040503141c041d00e624640c2c00548458206400018012035082c01440c90081510340000c42d0b54660b001980c0d6900d041d10f600c0d00082c080b0071114012a6950081c000000c5c404c0700c041400c03a6a200010705403400782d0061440c42d0080018098400e0301c40d503440c3c0c1400710304410240d40030b1064407070b07602c240c110b90071250281c501c0c072104114541d80c5540340c4481410009001d007042c24200214000c21003680c0103000443e1008040c00a249400000e560400d6032020060a051040c0b142a8419000007041048a031048820100d600d503000c0c041c915494198007200300c841464203040f241503409180c4071500885c5004014001429000101c2e60312100503150142e9440d090710225206214002c1c0c44018080000d0910007015401511400014000d030b003141c0003511 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 824099613 1250 824098363 824098369
    0x120314010b04120305041706010e090c010503060d1e0c050f011722050f010525020c10050918161404090c0c061d06010803071e0c030507030303020304060b 68
    0x2400c0c000c2080e114410300c0100001400000700c4030391140f181c5032481c01c10b41c1e14060802d1400c2c90a8060303c580d00400014889000100050385c1d000d2403a0000b82454800000086e10740c1c1b1000d823a05000317a0480300494180550180340c591001d01c6840c0100c0f400c50113080001564556009062158a03c801b034101550320440c0d004545c04d41c11221840b2940300c0c07801c0da103070541c503544400120401c0443d00101183c4248102d0700780d02041c00c004207581c5007101905c075402007680c6031050350000010301d414a00344c0c0081d44903900c1c0c0d030603604110200300c51441075420f400340c14030140d84805d1044069040341a8030441c0e500540c41e0070b0210810b0044c0304015a030708802c0c40c450010f24482031200f0031211035103403c52200e1803254100410b0310a640d843e0307038050754803565401d8012102d403940615a82c03020480130b801040100040c41c1400c0050340c0300c0d0044241c40d1040001540e10141400501c4640d125142c000c6a001c000c641903550340f8075000c0e001e500200c44c03c0d03071094038120006031541 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 824100719 1106 824099613 824099651
    0x20301200a0201060906060f120e070801090b090c0d06110403021c050706050913050a1d1b0a1508091e1605040212010e0c161203 57
    0x107101c5020107800d44041d5403004646500e44041040b05d00e61000403140211001d2610380003443c40c0d400d035880680400e940158980c01801e03c00076440405500c00988541703d00b5500c0b011390f49020095840301400350021303410200002c1410b000602941c8500701c0841404030a60420ba10307500401d03a5545002d540c0034040c02e028000740c080c04010040c00e40142107901e00140740c01400008149910413154107464103941700c4010441d5240c960304a4083d407010301c5844d54400e400d01e540d59680311200139109002d00141c0b006a04c050501d6a4030748240c6a02c00c000000284800c0d0085a11070401411031002e07005042d81c030a40c484040d4009405400020001e08060b030102c03005648a90481e4400340c8281e10403c00c0f01030030182c100200d41100c0c210b02000031203a880011910042c4140a0720f400c11202040c1550704001400c140c40f440c13490036230381c2048000808a50b6001038 = true := by decide +kernel

theorem cover : BRFrame.Cov 823920863 824100719 := by
  have h0 := BRFrame.cov_init 823920863
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823920863 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823920863 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823920863 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823920863 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823920863 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823920863 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823920863 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823920863 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823920863 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823920863 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823920863 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823920863 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823920863 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823920863 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823920863 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823920863 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823920863 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823920863 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823920863 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823920863 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823920863 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823920863 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823920863 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823920863 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823920863 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823920863 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823920863 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823920863 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823920863 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823920863 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823920863 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823920863 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823920863 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823920863 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823920863 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823920863 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823920863 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823920863 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823920863 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823920863 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823920863 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823920863 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823920863 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823920863 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823920863 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823920863 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823920863 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823920863 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823920863 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823920863 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823920863 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823920863 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823920863 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823920863 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823920863 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823920863 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823920863 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823920863 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823920863 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823920863 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823920863 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823920863 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823920863 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823920863 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823920863 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823920863 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823920863 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823920863 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823920863 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823920863 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823920863 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823920863 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823920863 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823920863 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823920863 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823920863 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823920863 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823920863 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823920863 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823920863 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823920863 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823920863 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823920863 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823920863 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823920863 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823920863 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823920863 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823920863 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823920863 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823920863 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823920863 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823920863 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823920863 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823920863 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823920863 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823920863 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823920863 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823920863 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823920863 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823920863 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823920863 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823920863 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823920863 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823920863 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823920863 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823920863 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823920863 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823920863 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823920863 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823920863 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823920863 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823920863 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823920863 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823920863 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823920863 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823920863 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823920863 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823920863 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823920863 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823920863 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823920863 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823920863 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823920863 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823920863 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823920863 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823920863 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823920863 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823920863 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823920863 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823920863 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823920863 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823920863 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823920863 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823920863 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823920863 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823920863 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823920863 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823920863 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823920863 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823920863 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823920863 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823920863 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823920863 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823920863 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 823920863 ≤ n) (h2 : n < 824100719) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
