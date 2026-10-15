-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4552
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:59:23.253192+00:00
-- url     : https://prove2.me/submissions/5e0c5ac6-0981-4fc4-a064-e41eabc9e612

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 818525179 ≤ n < 818705035 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 818526429 1250 818525179 818525221
    0x60e040b06040c090611011d010c020c09191e06030f110d08070212150109060501091d0402240304030e190302031b040f060806011805221a010608 64
    0x4200ba03c01100c2076403002072481142c86504259415084032403140307002d081d0001c4041d6a40c4895020b03d401443c0c150400711444280342c0a8540c1c40c2d072803c040c00302e2041d00b101c5032450001480703800d180c070300015449140c6d1680140c030007403124107071074410b482a22045c2d8000d44042200d4072100040c0320322070364540c01e500c4003268282c2034a0480d5640600030b0148071006481101810b03540700b10313a02c0c10f0010200070718040300100c00da580c480c009800203002500032507001480180010a989501251040810400f00c0c1800c0403541c0d140d0800c080f143c40d40c0203128090000c580c4040c0c0f400c1440c0d0207140214865280c400113003543e10148071040054412520841503400f41c10805600d0124560540d695007460b007a81080c40100444e010b80381d011a0554607510340750300091003040110354a4140c410700741152014820107161101910820384503600300034150074041c00c0302d0103408048036501e44030b481c210309900d0021102382081e410076030100f000b155000c4100f00b4004440225a0300d82c1c0c03 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 818527679 1250 818526429 818526431
    0xb011802030f15031615030c0801050d060209120d0507020f0906010c03030b151204060608160506031021410703050703060c0210020712080c0d060e040b0604 69
    0xc9040d0702d00311021903000e8441d50070400da6143d00019920103101001d03202c0900c0c1036410003550b03500580d1402d414816050400079150078900b6030114441d041d114101e42000f40020b4001c0d0580e21041d0080d80511035441c0d000c41500d07111070090105100e00c01c40e00c04d4139200c2c642c40b0740e018010700c1807141403558428450307240030381081056030304112101280d0b5054a000640c3c410301c400031440c44c41c040c0d410418801e2010909041c03c0701c000a4051290380300324070a10060340d5412155640740c030074414030040c2489005090115040400117541d0000030a020110346941d1a002108000800008500084150f01d400c1c01400020020300340484030b407460210414081a0350700f6810360920003440300d151004188412491350402203a0f0146030044291075040b503581c0f030904010040300603a00c025000d120700f03601c0880d20b9442070b1600140c1015409000c4001c0070401c81d20b1620080820745150001d000035102c61015228400107800142e40f0f0400a0405080040250b00010703c100d10031 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 818528929 1250 818527679 818527681
    0x306060f0b1b0717060919021f050f03040516050a060504090e120f04060201140705180310180314071208040f1e02090703050c040b1806070b01180203 66
    0x101c50703464101d440300d44160442c80c2400c07800c5030388a4100003403a44030b16405020140013001898020070098040c0002e102103800c2e019058104403004484400d001e50710854a040e900c00201106507a000603541520300140b03014400303280340e01c150700261015034041c0d01c081310ba42800c220821540f0050482102d00c41907803450404000c00c0c80c4124054551025120f46090308200420411a12015048080785450318048140b454050700a84039000056091140301c061b1411045032040c06041c0030742d250340ca043e05400070808441190310149805103da00c1001c2600c102d0b601c213850f5a08131030104050a041c0604004000488807540303900c114000700007040c0010807035105074042080d203003040c2404d603442c0d06040c040301c410150094801c0020042c48010f51445012014980b807084402e0b441584410070110304035001151403407041c900c100000c3c8112104680940b0102d123040900001c0929502d01140081c3c1192038111410440140184103a41c0503407841c000403c400c55045087d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 818530179 1250 818528929 818528939
    0x30c030f1506030b160e130b03030909041410020f0909090a0506010609170f1009080714010203010e07080f0f090a06020c030a0306120503030619170c03120703081b130f0306060f 78
    0x4211f810140f00c01d00155a52549911920b0510642d1203614000f0450101c628050920310541d40c2c0b0780000c600c041c0a03114246621200610a5451030b091004105040108070f0b0f091008a0401a0902080f0b101780a015000a80304122007800303844a6520306501514080038820342c0412070b081407000e070300010100f200c1010009404402a940f140c000b1030904002c0c105003441d4458500c014241c00b003a00ea4580c0c074080150000c50403105688501c40301d503503403a0002c0710086429280c41e51180c14220104002407031844c1c00719004840981a14400c00301a81ea07002280d015003032400c065000401e0581d0302d103806100b024010192801240318020590303070307020303100d2000a03c0140316010340040c0d580d2545091130441d0190151154600e221101c0030400c0340e030b6040c1042580d10900c1030303014056004076000c043e00d16481d85521040c075191602240419101a40c4a100502c10030601c41c110444100465900060403100b00c003030f40036415030500d0019241c940c0c1013800c14011140d07003080 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 818531429 1250 818530179 818530189
    0x70c031d0303070605270a0b0609040308060409080f1b0105060f061e1902060405010501140d030c05010b0301091b051906030507021c0203130906030c030f1506030b160e 74
    0xc40d071382c4004002002c0d40c5000b080c102880c2d4120a90003401c2105040801420000800034102401126418103a80c1e4500400404202c122001000646011301041860515420940910303124080c0c5a0412605400000700c0c0c0d000120078061050004004981c1c1070028403400e90024400d030f81e18081018100040ba440d8801c0e101d9012039401d4580c001d0780010040401d85045074100826042c413010071130f6000350740e00e00c290380903940d40d46040000611004901404541c2030380141c100c50108080344c80c06d0b074141d0300c6000c05644654031a20f1502560340c081c4540c81015101e010481031015419070100000000e640020b80a442400d4002d200c501d00d02403070320304403031107031402040c1903072880300403800c151aa030920351072004100008050709030044040c000c1c1001940320300c0e20035950f640b208400e4507154800608480d10700c1c2024404541c1920140240c41d002700c01031059184c00101e64002c0320420b90058420319a09000d00c0180c5004031800018406140b614400b20031608001031 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 818532679 1250 818531429 818531437
    0x1c0b04020703080f1503070306023106050a14070c0312080601080a0b010c0b0a050118020f030604021b06011d0606090102071809050312011d0112110612070c031d0303 73
    0x160301901034000503e506886910342c01041c10140c247c804056580c03038520042d400c5140c01c2014440030703a40301d00c01002c03090300000400607104002e031005490031000360398961040c2c040004000c0802e14204041e00d40e0700040c603c0c031b8400d0080803075052950400b00c503068140d2801404024a86041c480160381c004409a0010351481e0001411320340c803030050395880d01ca1100100000d1200c4100802d0305402e9008504a40b850040441c0315010503000c8800c910a207400c01d00b41c500c0500200b1403d00b415405007042403480700e4168522030004015034a040f109038490140075203240150798980c2869022035420030300a032140c0742001c5010340040e44441e46401449060b1044400d85004032403d44c02c68002641c02c02d00356561040d098590040540d402d00400c40018407940c03800c450b00b5040e01000b4103e480e000f40c8240200001c2e1740d6911031180c420401c90b8421024080428001c1c1c5550319680601840d48620100708040d28002d00003109452452841c4900c007074240e0515107001c0300b25 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 818533929 1250 818532679 818532691
    0x2061308120c090306100302011805090f0a090813150516021002031c091b031a0a090804180f0c050a080c07060e210301050a0303050a090b1c0b0402070308 68
    0x2010003503440003280c0c2c0440c040c03489425407501c10716040c090342c20542c19401c41a24001e81c0c0b807a40c0e1001c458024640044284140f46d000031508000446200742d1551058000b803103007001043c0400c941d1920002500314001c0d6420041c10a402044141c0b09459002d28070001401c00e103060202d01d0400c3c03441c200400d00080c0c0200081c0d842181564402d10840320080c03040b0111a18402403641d0000040400700c808485401801b0040c0c101c0d2514611a60300300ca42c0700700713510a540540520444010317005404000c1858503600d05400184a41c00644044c0110305c0081075a110840600e0007950302c80500c1c100c101380340203501014158001c00b03e40030089541040301d46c41e00e500c212070700c03640302e541e001074403042c58000741550f80340c000308101203603064050441005106032203001c0b845120a114855028083d1541007001a002e84007138030f8020000d0401a081381e80d03484120180e6400498281e01c005c1c001a4900c1d400314003441401070206041d90704604005c280d1750050503400740a020 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 818535179 1250 818533929 818533957
    0x15010b090f19090603030305010e060d20060406030f0507140a030902011209060b421903020d060b040312030504140d180e040c052b0507050102061308 66
    0xaa00441d0300c0303405a08081d0342c1c0d42c070030042000750340f0f01010340188514007040300000c0c00e000c00001c0600c01075407140d01840c801442100c404100f59a10303008100410410a0760285234507082e440e558030301d805400240300750b450100740c441e03c1d01c54950031a40018101c0080c0502c1e0b180d82d04824500e001500c107030742401d003000140b003201070005842c0700c6c00c461403c100740d03418006000200318507074000c0c092509060702c644030400000c050303042042885803444100301d0700a010b0000140c1404240f4580c4420601f103003403900001c05e0b0114225201d1000c54004650002032241410000c1d10607400104906194541440e066554140310740d014503542c01d040544800100d42440301034200608401c0c1142d04643c0c04e00342003031005d012501503081c1c3c4600c07606100400074641c0f031801c0d480f0740f0441c0d00c100b45102c4a0308000c01c200c1074400700200300e100398596180307030a40c1200c8010200d400c40d0084008040346407503d000280350030340003840d0801d402e9010400e0b80c0024032041c10b80380301c8240040 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 818536429 1250 818535179 818535199
    0xc030703050f160516051c02010633030f0f05070e040905060a2307090504051806130c120b0612030a080a0b010e061b0d02030c0a29040506070215010b09 67
    0x10003641d00c2417003100036140740a440240750351203002d92a4070504503075a8009000c016611241c0704449016811041e45649801601c6610541503d20415403164182000200d10070486001000c42d01504510440d039aa80c07400c2c015043d804c40e51034603000c03400b15810311051215654a980b100380c00303014102640d8031206070408690120f00010400828015550a03038a0600c0c5d00400c0580184110350040e49003801055103144008040f00c10a0744c074178018801c644804035180302a0300c070240240c8110300c070307148003081c1010702c0007818103118040c003098041800c001042054444c40d00142103001e0b4001c00c500c1360400c0c0c12501460740205030060002d0001081401030350080390202c811075010f0390010f06058080c14860001c00c4018041044410b800c41c1111305a035248607242010300564007800b01d2a00080400381041000902c0c00422000b07000803142d41c2070040d009440440d80394001c1c06c10003603450b50402c011030381c1c403500b940c01c00030175450f01c0d00001152040300c0680d8000d0103018 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 818537679 1250 818536429 818536447
    0x807170a090519051008101a09090421020c0414092e0203190c020d140f04080109080903060a0506010504050112180606050f010819150b030c030703050f1605 69
    0x68002030092502401807004021400001006d0140c2241c111101d0203000780c2c040f481c1c84071800680c400013040155a441e028502c4100704070380d08018011901040a9280030108100846d1040002c2d8800d03002098107503078440400094601107580080321882080030001042c03800034441000104280d60110460508600d02a07111001c0f40099105800007042c0140048042e035290704a00390044100075002130f64038101c1e12aa8002c089100013121900400c02c050a51401089014501d0079000d15196495440509448010a00381d031100303404900c40e881e80c01c007800140c3c0d000302c56000400507450460300181035070159010b59410072410056510481d80698080ca101c442d891226101d03074455481c000700584010b002d0140500d40e03010030101d4650003103900e0341c0601c0140004505000340600d030b480c020440c804c03c9184003c000440010829200c10095019100d04803029035641341424004c0c003680c20140c0000000c28034102084901400d0006c0070406604526140781d40d26640 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 818538929 1250 818537679 818537719
    0x90c030f0c071b050a08012009030309030634050a0c060605031f1b05030a0c020703080318070b040513050925030c0e070c03030e0312040807170a0905 66
    0x404401080d000421800c03100990f030003610704007120b030221480440584c07544036076401d90740c118000c841d0043c1000e40c51011050f600001c1c0a55007800740849040c00d000e000000d181c490243c80c68803c0401c00c810012086006140a84030350780321075000c0c1c0b11074121001c010700b03a204482c0c1c82400c110b40c050340c000400c2403540100c1d0040c00c0050482d125141c1034214588000070090404041602d172030031030109001d50600c08004c0c8031182e168142559503182c40d0402034807102d5680f0045005584021000401e034601542c0180303004013031710b25600d4900d0003591801c078194000781441c480500c0100300303544e10702030310290700c0c403a8190100f101c0d00e0703820b040b44c81c00495024070403060030707850501401030400c1a28042100c0c06100d442e04030b0341d80c4d124407800d14541650302d00b0010342040c0604021034001d0300315418507912603084031301d018040380300f8040d0b249041d00c040b207600200260300c901707100001007841c2e5843c504400440c40e05a04100c050202000c62050314024009000714000e00695 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 818540179 1250 818538929 818538937
    0x306020a031d030d0f06050a0b090d17131a0403060f110d0b0a050901080d110705030318011d0603150f280b0c030f0f1308010203090c090c030f0c 64
    0x7101c041d200108982c00d4156200e40107152418080303854204901e06100c02070142200702c50001d0054039640b0f08210b240107051344000030041d0403460f480110300c001803041c05441000ca1411003070940301c0e17884404010f04070605030b10101d0348032000200356189000c0c0c0c004450460381c5c0304000003440040390400d000079111044440140752400305d0b17440340408030b40d0800c502c401d40449500a06644031001c10880040a0091540071b50062a00d80b507540c2c011109000c1c0e00c142c1204541e00c85a4400c0002e141d503205914074407500760b100f215a2400d580200f02d401305011024241c21108040742c01280060000070940303500c280494140c000e02d81c5131103030001007404010300501710000c10f2003034400c201804e1100d05c8100c0980d110000400c1502c40090391591b840c250040c3d850700f0f107140201d0700c041c0c02408000314811000c025002000309420900c10040c1100000540c50349030040c8134500304082c4100041c041c548a1040180d9510713408103c81e40a01d514a6405180e22111111001402 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 818541429 1250 818540179 818540201
    0x10609030c05131b093006050c042103090801140619080615100801030f030509150a120b061c150e090303010e150f0f22150b130306020a03 61
    0x51a00c0f80610700d0b80d4010501820b80340a16002d42540c1b440d6015186139540c600c0c540760322425070b2081000041d40c1c5412668005d1170480070079081584915000880441440c5d204048000710400e09042582141c82d04c0c1c010050704000300704140c441140f00c4070f1101d005101520440d40300b16010744400941c000d0102034000c0d030048552900c0d11810048480c442401e0745407103000d0340b0286400892042c0001d81c182c1c1d40c0200308039461071244d5070076551a0800c2c40055440400300341105c407078805290142400481c41c2d0340322400000030508000c110b40100e00858040c91040000303620600310f07140ca03d101c003086020000b9214113000d81d41c404000840d001180140181c0d410312042c0036000000d141a40c41004600c460b0f40c5030304465101d101c0d01007026a4000360389002541c002c4c589403c4684030520051300c40080c4000440c0d03491030303601e10040c104915550366a40141241c0b160000c002c050150250703618030340381d49041c81c582400140d2100800c90780c1c00080341e11401e442500300d0341600c0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 818542679 1250 818541429 818541461
    0x1060f0b13050d200a030b0a020a0809010b0a0303111903051201060819050a2403030806060307230c031620060412080c0601030606060206010609030c0513 68
    0x180c450301000040d6011079a00d86070898181c9010440c1d1800050007000d2560180704400c04003001495104c900403c1640268800080d84001002ca00c110035614450318603584016518029000d02a24420026041e08a240e240c03461801d4141c458002c1c04080d01d8042c2050454003118001c0c8038039184401c650107080d43c1d4a681984101600000603202c4141c41b48090b1101d44c2e01c410041f50304490844500c289038901d00701c001100100c3e541711a401041c00300c0c0114102c400e20105003034203003001c030313846103044115041001419485246160000c4044a8552a50a007490020000951024504a44120002c03041d01c601300513806c640e10b00f0340c0c000c1601c3c1c49404265180340035400d050402d0b50009001044840824041a041c80c00318500500c1c035810305013840c00461585d4500007085401000400007002104000c004980c0210700c10100800c8450420600a007007410682c400700a0280d02d23f0140300151000800005031b60701a03c4210003000b00d0120b09010f8502405021141 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 818543929 1250 818542679 818542709
    0x417010f06121502030702100c03180c1d06090f100305072301030b0114030c09120102070521090103090c0e040507140f031009080c06090a1a010501081501020106 71
    0x50328030240c1c2d14000703500818a0f4400803418581540507840201c0e50240140c10800050044165541c0002c031b00030040c1c5000284460000036010444071011429100c03481c2301141041080d580c0e10600107100e01210b12290241071100120b40035001c00b03445185000c103541d000814614922102d000196040800c07107079655610700c0320450038224070044040340d02c49a81c0d08103195000e40902000f600043c5d4a542c4500c01d041d200000351341014210b0304ca00c240400c80d0003034075a1980103004c403500c0c0c2030000580e07421076454250300e00240c016912103406178440c001b82e402c0b403148096030954003080c2800321301044140380ca07205880580e08283c140000450030710051140c001030403020744a038421b0045c00e0348014420080d01d58020240079078164801603181065070981c3d00000380c580d2088030310f6814900c03030010070307402c102044910300f59a84c0702400e440705103c040c1c450b500c1b40a4102200203003550415000a04242009008039050f001e0b42e1a0700a450b4400d600040044c00b640c40c0300c0c108 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 818545179 1250 818543929 818543939
    0x10060c1a0a1b0c0204051003111e040c0504080106090606230d0e060a0b01210b030313121205070809010c0213180203120408031207031107080307180b0417010f06 71
    0x10b143c480000380c1c040d41c505000a028041c0d9072240d0001e8a4010300030351a02131401d4100266156410a2200e005040581c00c21440d00c650083d00b000d01240d881d01c6445a0406600030f0071200b440d0721212125042000400c0115003020b0b849013940d001d8601140b000c06021920b080500c611203001d0034680c41d101e50341c01c0c00580450018066a17505000b03100a81120004451032111000b40581d072119200b40980798444685c801c4042c40c2c0d018041d2070802e103641e680740303084210340d038410005a1a040c022104124034092100c2d0441041d09045050828a13111002d4601880a20606000c01d00071aa0b00f9076407a00d900c85a600d07041c1e10700380081e4082d00354a03400000044802c80c017074071584041d800000240c80c11b44d81611902002941072140c451200280300a01901c0746051659458200f4401003064008000b490701030404144d580c14454001000185801512707401181c0c0c90000f800226200400c503411117100e42d89200d100f1704000441c3c1e00606d10490b099882900d01071000170 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 818546429 1250 818545179 818545187
    0xc030a06090212010b1003020c070314061b04060210110723100203040b04030806150403050c0f01020c10051305060d0903020d051204150207081210060c1a0a1b 70
    0x700080c42612070100002503040b2aa00343d4030740b90310b529030115030000b0040c02e140c840e034050608804070318112805030b03a4a44403031890781702000200e02c0a4101c00304002e040c481c42540f10611503031151845190514114000f512910100c5611700866103d0412103001c2100100303507804150080140c0401c0800e804c00700c10040010050784135580111902902c12010b54400d0740c1c400d80d0041c0c071400d440c0d901d5070303000c031201900142455807000c201414118058213100c0680050340c4660010160b40e0950301c10010100140c9161504642c00741b8030b42c60b2640c88210703075038103116102d08029440d00d85e0505440c5614419400180d0449004220038040404a40040c0b500c07074020303000e0ba0030322254584111010701c0b80f0003081c041c5c04200d1010600040e1a445003082d4901490001410200503907a44652603001461842c011080002800014010707a030b2100c00625250400b0130002041e03a407016814401e240c41c1000305407600c1c00007206c1c134880e50008035801501d68070036035242e000f580000d0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 818547679 1250 818546429 818546441
    0x150f0213050a120308060d050f03070b100e0103080703031e020a210b0d030f0e1f0e060a090506070f0c030506010314030f040e0a091e020405100501080c0703020c030a06 74
    0x680314807004000003501a108458010b1040e4040d0340d20066540e071401402413802c0891411151442210610951003104ac0b004d060381600c81d40d1a0b0b0000d08003e480e580c0504c809411035a41401404c0041001801c42000c580020f60f060801241d4423484244c882041c03080348081217841c600008554150b0750b8040035404150003040744441083c0d4240000c4401c80f4140c0010580000c21500a0004240140e001d802140d131307245080c030000c129500215010b41003003a081d100d1100101d002c040c0d519040811050400340a8072441d081401d2502c00402031900c0d48680da010305000500b00c401d006441250410160f084017101e01010b40e2440c00541d03c0e9000d02c03003a1204405821400300d5800701004a6400c1c2c100d1540c042e050a040446054410501604849100c0c2e5640c5c00540050a000c0f100c0c003108098229100e441c00150040c80f068500003030610382841130b0510180556a0462429901311204656081d02c4113f40d140036440d00b941d1543c8243d0502c81e1504200c20821190094 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 818548929 1250 818547679 818547689
    0x902070c140d080d061d0609071e03110d0e0304210b0609280c02160815070c0b0c030a0b060c0c0f0418050c030d0c0f150f0213 56
    0x40c240555880c0300c841e800081c9000103a010202900300070100f03441501410041e4440d00c00080d89954030802c4001d076040c03802040201d0000e120030841c4500d001b8031103d070701c080c15091500241c61461a450705100400408909055580d00b01e00b0500701400207a980d1070040b04000c011b8500e00c1880c1d01e40d6600188520159454401d001941e174401c000c5030142c0311544240c9003107035070319000c00308807142500528000c07400c00e805100d00a2a900321002c40b95020402000094074095408001e092442c1c191200135801d940c860204007880e8001540c81c0240d496104001c000c1e201d0040c103c0e404038070010080c0522002c0ca0078800c100354410000d42c052030030383c0c01c2001b440c0003101c20312295004090001c03880ba004a600b6a030360b41032840c41800802030007440090500240d00b00d0b0481010402c00540d2903602002d0b040c1c8550608000798819540300f0700301840c18103225500c41e0030f4002c002c2001807403180403018868510210f0b81014517106191502951501a15282c1000e2034a0500c21 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 818550179 1250 818548929 818548943
    0xc0509060a173c0d05030a1e02210a061211060c2e09052505120717030c070b0903010f050c07020103060e0121020312040f24050912010e07090207 64
    0x2180c0301031600010020581a0942c88050640d5500c002c10401042d201188c47c0c4c22100d00000c3c580448050300c02820406c40113001e40845c088607252050304404c000300504506480c004003070194103880d4400300c1c0d0780c0781d20642840c4104860b10103e081406405500c5c0301030701c07070307002c10103030300d81800341b4040d410f0b1200700e250403040310441d080c1006d40d0b40031074019286400c0085000ea10810090008007031a840c0520404010b40e41c10101c0d01e61301941e0750b50411a0011801806404070500c4040d542075402001541403003e00108580c0700c010703d1040c05009500024079010f0f5071000e4104001080b103000d0104001c1c5030042c1028100c2c5d000240807400649005004509854601d07082416100d40a50074002c8402031040030800e80b510b0441680e01d03128100780740f0b40340309440004001424115a1680c0c04038074200058689000d01d904010f41c2d50410075035000f840e0347c010b007a01d950840848410180e52510760810b40104003801004540c0d00900001203040c98068004202646c0b2480d0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 818551429 1250 818550179 818550283
    0xb0d14060c090604061b0b01090c020f01061a211003120c0c1e15051e0f0a120906060e07020c01090503070506070c1503090c0509060a17 60
    0x910304810312502c8022a4410341c24002480403500c070382d11000d918003480851031103216142e16240c203c050241d0142440c0782d161040c030b0b845140d040c003880d00301d1001c10000344019400d000350705c500a1266503545050090204201524401429985c0204200080c9015070382c1442402d0014045050005480c100303d4041c41e00c60a6100340d0000186a07048041d40e04101d050018208070b41d61094030324124004540341c00314540442149411000300d01c1d4480305d42d104282ca1f00881c4100f0020034a481c0500e06001c401d81c020044000c031181c06040d4546142890701e150032040040c070090754084d0146150003000701e40054900812401106141c0846142d42003000045030103d9140c020503800d40c102920800150805d10040c1482510a0050172143c5850f00341c111480042c00740c80c100020348801d001400c0c022501250000392505403900038451400b0030108009412921543c125401a0004071495040c1408550f40d0070310301092000240d00c0b080c14035002c0d1a041d120309002c1c1c3e10b0200f = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 818552679 1250 818551429 818551441
    0x1c1205060d05060402042d0c0f0918050601051216200c040203130209040f02090f01151101110a0801090e1515030a12031b02010e07120203010b0d1406 66
    0x721440000c1da4404020b100550381e40c0d0134040a856440c0119813900424820504a12081e4600142070400030700005011402410010b04405454548500380301010400784200400b0b80c000050702c01800170041059111100120307214841c0a28858400d00c1e41c90610048034280360312600829050341d540620805500c0004800c1c90010480e401144d10803107440301c0324100361f00503503881000c1c10300f240140149500803408004040390101c07064801e180b405d0045141101c4403d03004801c130340700242590304017032034119284004108c20044c844094910218581c094000442144014a18540707603001c6100161400c01e00380a161105814419002540440081d000004e4032062212a06a80391070405040540307d21030300c0307501801940c04182c085003110440414441290381c0c0021481c3c9030340c3e02101703221340b114a900c00b10b9040c00c450805004000415400307859054603091403515444c40000e0042089040050300424400b00b84014000d62403411500d483c414002d487d4165200 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 818553929 1250 818552679 818552689
    0x902042607050a060309060b03010501120b0a0b011b06112b0504050a020d06091a090f070305031b0c0904050309181b070501090605040c09060611030a050306031c120506 74
    0x1801443d41250120b2420415140719420018440c0e004200006540c80030030040303420342e01c09030440c05001c0d000c810302c1c400f045040949254410021001082214407080009118044107198036000c030204007040c1d010b00c00c15074801c03a070410295001e290f5034442d160103500070200384c0900003020180c0ba649040c0140380740c062940308a500801905002c441603003041440000c840c0280c850b103643d07200c0c070000100000e0110140b64039420b100300d03e070b140580030781e8601040076440c1c14660700078160802c0081e1001003654414000c91348111070601d060b6101918002034040c840760b20010f00c2041c4428000080000d040104e010b650352038aa50800003118a0440c06031000c851041801a01c1d031203e40070724000e846647c0c4654004640450247c485c0d00940e1003d50b07040c0c44590000e6410440544540b1542005141e02d040c141d088a005009003500c13401110307640740c244107001001805e1640c0512a030500d0ba00c00b01030012450303030368203001421a07900c111880200c0e0b1034000030406c28544 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 818555179 1250 818553929 818553943
    0x1051c0c090e100501030b011403010212190f150501080f090703080d090602031e1008060606030601090f2c060f01110c0d050105040c09020702010c06110409020426 72
    0xd44040002480c1c8524140180381c920003000041c0110583e03c045411a401014000c501414000c1165410706140c1e0700448141c1d5401ca101e030b03104124a05615819458103903010031004000c6456403100e410140180c100300f185601c44500d41304030080c0080d690840d51040d81c03020780c2c0c2ca030580da8034068a60003414080d94031800a03844000304000044460005108038040f4081c04580c091255030344000b80d070419200f404d01c09a16012001d00400690a05640a0310043c1000c248030300e484580d0f91201005851940607001c000005440c40c0d011300708203030080054003d480c420031f0ba181003181c180c5c107120300c0d00848640360014480d201350f00c140f650303405000c0080c0104100410790740151040044502007040318056690107103502d640302160b025000340070303800120340f0385001c1c600b1842041d255005000407910501400d409030f64441d220010301d40c2c1c0a00c0000d4034030740302c521210342406190310504440d8000100411043d06101c613440b601d4541c0d40c0c1f85043c030104140f0702034a541c4 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 818556429 1250 818555179 818555183
    0x120f060506032a150307030b0102010e2103041a13030314071209050f120406020105091b10030209130c0e0307180b041e05091204030803010b0a1b050601051c 69
    0x22440f07003450b18840d00703943e000b94401800d0354408401d44940302002d070021504500842c1d0341d540c01c191503503020300034600310054600107080319980c1d9050030719040f00c4141405458503000f000180c104860030380c1c034150364204060302c0107480c5004c40315210012030001d81100000c0c1000c0801116103410305506004490310f4031403502d20000c24031810002c00c10904140c40a125000c0401d040c2c01042c00444504090310b0030a664072404c01c0000707425034070f01620200302c40e4046010910001c44124648540210449080c080c020009100f03c002e801040441d0354000e0004031507081402d019031141d2154101d0741c88d140b8003144c14600700760b10350007244110306182d000341d00d8450244506a11002e2124001000015403203509100a030f030b03224188541d145055954000e0040001c0101318a010800d640c9225920700b07400e50351006035600040c842c8109004012500e80c80d00f9000740700b00103214400c48649103000743c65080ca1560703940284201390150f201558005509a140c0810703202c280e07 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 818557679 1250 818556429 818556463
    0x4170c120a1a061c1a071115090705060a23030103020901050102012d110c01020a0e1002030f0d02040b0c06100b0903071a09060c0105010801320c04120f06050603 71
    0x81103d0b20f12110f803180c510440b42d414010082176440011920418081c0401c0e40d41c1030b02c3c5c0300407164140e182c50035503500070100b080b40000304a0461400240402036030b00c1174a10a44940b84036005540e40051260606c05021080c15400259801100598101d034001c56015501341d0340d87c001607088503a0100025402c0c08000040010031203184040e803655900d8000010340341205004d40c0c0c1403504907000c41107140e5000038841505a82c058030a070881d000c1100c04a411058400d0081e540c1d1007030003004081c100d008141c0e00d02c3c45841d981510000c01501244650325140050b046032100401c132242103a9641202d4080351110b000000e40d41c00e4a0054002c04101e400c01010b0309003095928418408407030108500f000381d45800c03014103201100c0600201e003650401660070309603280c02015003c00b440c5001ca60000601540c021900d6403014801c403141d948544c1060700c83c41c41590440180b21240208090410091070220449107000e40001c01543e01c0b40000c05850314a8210410004 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 818558929 1250 818557679 818557699
    0x31c02030a03050c090a0e09010c03060f030f06020d02070f021f0504090f2c0601060c0b0c0a0309080f07020306010b0c0703031b020916080f0c04170c120a1a06 70
    0x814081d60050760481e420802e4541011720740c1e0b0015240c0821a00410741030f8011006000d0141424080c10311181c1c81400e05014850900889548a00103440041c201c0515180030b503091100b1581115401101e2142c1907545d0750240c2803001d80c0707810501e4120b0003000130015114036810b08076400b00021442c1c1e910b4500c0d01d0f14001d5a00b0240c103042803c041e5844d985c0f0740f40c440c070710580c01d03084214402e8400c41c80d818a0a10402e0f5090101c141e1040c81440491242c03800010310140380254806d20250003507032aa4621a0700f01c00603d44040c00070441040094401e882080300400f50003698802c4048806583e2074041c41241c07802030f000040800d9101400500000b0300499680b010754081c0520f0643c0d01c15281c002503100b840a40c2e602c4000d10504c11401c401ca54081c080704c2c0d115200340c000c08120306011001d43c00520451148840305030921440700720029040c0300080402034000c0c1140200c5032501003607600d03100d01c02e0341121400540091311224a00001c1d1551140c40024100560 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 818560179 1250 818558929 818558947
    0x70801080d0305010f1502010b06181f2f0a05100e0c06040306112b0507080403020a0b0c09030123010f151d0414010302011107050a030f140714031c0203 67
    0x1b4202404440000b555242d00c40d45600b921483d02800070343c0f5100728800e0f4081146004d0000400410a00380d0700e803503440003551511900011030002850102c8402000441070a4107400da10003400102c0116000390800c1c0c80a05c031001480d110300c0c0301d54020800000030040341c41d907a11b2080392403803a0003038000d1108101080b0164042140c59640d1440d0a00d0000b5030300145120400c180750f80120640b44011803296a0f21304e03c10349a010010303041a16690604c0d48010b55a1400140c0040410042c030300002c1214400c0c4056521426028000780401140e1914082601901c45001d00500d00040000101c0c00034404c00082100c1420301e00d0886500c0d020390403152021307611929003600c0200300e40709995850314071070100360402a81040310301d9411440014940c03080d4980d04542648080c900303108039918030481d5012298855400030529203a0b142c01039101000d0006000b1600072940c000032460488550302d016a40704509450844403002c4407810090604108007005074001e201c4448 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 818561429 1250 818560179 818560199
    0x1e0106060207321f0e011d2407030201090204110403170a020a080c0a0515060f120a0b04050706080601080403091e03050d0903060501120521070b070801080d0305010f 73
    0x80001140500c402e41c89000502245140b40300541e040c100d1901325035264866603101c240602100c0b42441c03d92441c03014140c00c1501d0066a054136841002000c030080710800d40b400300d00c03c2c640070315036140761a0392890802038002c081050b01039002c0d500f4601c000100d40d440c40c0448003507036805440c0820b00140ca0b500303920650800c014400c15489001c01c074801050110020b44601d2904500920b00001740e8035140c0e081110820f400c107030140c01c07103007404003940e58003a401b1115401030f40da108a62003c5500e40d03280100305400a00700388840d609000601034003103503003020303581d0729125414103031a03a17001141c0842040310050006100c1510a1214921821007020550303c000001c000342a01d0b503c1c3d041c1481c1080c83c164000c248040c400f041040384e28011030b4010140c45540300c506428546440e078852003103000038441c00740703607a075280c542c1c4040344203866000707412090341c075614039014001a0514400307000740541441002c1c52500d0741803103805202d040c2c400320400c0c1d19007585499a558 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 818562679 1250 818561429 818561489
    0x2070f0305133303200c0304030c0e0603150c0405011409040608010618020711040b190b0403033c021203150f0a08030901050d0209031e0106060207 65
    0x5014212078820000d421002c4040000d4003001e0f1981551046540858800316407070916141001e150410031940218000540c50348010320440800307903030762000b040c0c841d4111300c1650030007080503203a00c50106001c598010060321624065045135a104601c0c000030f0f03401601210100c10040381004144034951260440701900303c42c000300b66040c4104500014240c070392642000744103a649820806c102100724242a03000e18036070340b0842c503041c007c0c0c80b00c41000940d481081d01898558881c2c00c1d45481c1d102c4004d26101c0380c0381082c1561030b201e640c0c40249501510090300040c200c031030042e01900b0f50080000c2d0030881141d0080944201062006164442001c0c00c1e041d8018a00040c1c0222403810080d8854110508182d022030303c81c90401407401440f05802c1e009403904441030020301000411242c99070b1003420440c0d00d80d41c2c82c82095010380304908002c0e82500481100c1d002012080039101460840d660083c00806d4899104980d0f8444c54850600079600e500c10203500741c42d5540580d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 818563929 1250 818562679 818562697
    0xa1a0d0c030f02061b1614030303370b09070503090a11012a23031e07021e041a06090103090c0504050702060a1a090403030b010c05072702070f0305 65
    0x41d0401720703284c1c54481550f9000098508a4001400d02024190090001805005090318040c00c6142100100703603280002450b030079540350300c071403112030351410495244901714031a280802050110340580c00030300007241c81140640802004030b0a020b0081041d01d2168046400404110300c0d1512000e2403130060b46a694103102800c0d1146400341d0500001e10b090350b40c441a2090b8008952030800580c200007299682d1400002d110b80340050404000c07964843c00d055215281c07001d203444c840c1c1c120701c03c0d44802540805405034030740f8541182616010020303000c4408000144a00024a20203c4c00c81030080c2c1c803031000c02440769590702a40c03020001600900c10f81018644510201d011160151150740261b8024820000c0342030950284003c1ea43d108034600504c203d088000c1034000ca0090001030078140c0300c4201c004103921078190b100d11241c0101c2241c3c1482d564003c8101d00c607040c10500c2e100c0d26141c20780d11070f00c60002e0085584803640010308a40399950b545003192190007002d00 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 818565179 1250 818563929 818563939
    0x31104090c180b090c03041a18030406030f0c090503120a030207020901091e09020108070c08210a06050105070506130206070b0a0f2316170a1a0d0c030f02 68
    0x101041c00d4a154074290b03840080c0701c0000504426050801a80020003002c1c0c600b000f00820820000501322403ea10300c030700034003401c1c040c10307103c1030f100b16204c40d40c0510000c400c2c1b10106002414a60580007800c4091803400308109c0e00c0d548480486042c1c0030f5024454155119a03403802d009000b54005140748511454010300300760380c5500054402e02e003a0b000d503610390b450702e440012006003260240c140c2f1850060420a0036515030018290b500000c0a0b00244158030001e44140b0460740210b801d41052041141802002c102801c0c40c801000d980519100b46050004503055020710101d0f402c10703400030000c1409688102e00d00080204825049821000600c02500064800c06c6034602503d01c1180c04500804500d404000702c800da80c2000d018030072503c160b445140e604802090300040c0d003000f840d440c82652102983c1d510605085034403080d17030707482c2041210f0206500511200004c02d0003540584043c01c204544c082c48440042c040c0400c03100d08000040d0040c046104031440540 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 818566429 1250 818565179 818565203
    0x50a030e010e0102070506220b0601120c020f06010605250503070c09020702011403191a1e0405090114310614060405010b18030a0c080f011503110409 66
    0x61800d09642c2840346001c0c46a401003014000c1000901c030440c0e00c00206400c0b10000d446a601c50500071010000c06000300c1e01c0300010078440c0e413103140d0300c240703800c41d024040c020100d807008000d580d90348a840b5003020f80988000400d0341c61040c8200c07050000031145003d208a106080e031903036078a544804a83e14402000700a0008040c1741c81003000300508080140c4540c43d50001409507100462080206c820400c00c000003181c40c4031840d507000070100000221008040d40758602c03107070481107159012a6000ea03a01c80361801c4a07a414000d642550103002c1902c1d0445068280c032101480b1000c107a841c50002810304c92a10300602c0300d1380709450881400504030041104801410b00e0560391140c403030f000e007281105403041003a0000b2003940c081040350726069007584e40303010b60480280e000030031a9441c011607404001446085422690450109aa502d0142e03500d070740342c00d00300310385508003420803a002281110800c112a0402e0340c0000300d240000400008146802086482c800d000c7d07 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 818567679 1250 818566429 818566451
    0x90f030c03010e030406020d0e13050601090308031003110925050403120e031c02071a040f060816080708010603050a020d050103080a031a0d11060c010906050103020405010501021c050a03 82
    0x405800d000f41180c2029558841c149100207040400100841c401e200700788070340070256211a4508180190500c03000200e540362040105c0301c038003035580090304041d00402030140d01503c80440608aa02c1025101120504e510901441040454403a91701c6201c0180c03405a080038a2000e0400b0502481c100e0702d07194695964a812000c4420b400000802d000d01000040c10200b10300a000316261030b1418040e11004002035455065000c1d4004000200004981c00b81c0f080003910007615002c10f8141d841038a4036801003030305004440c0c040e028000d5050100301c1c940540c1c84140a10050f03030341c070307003080c4e08046081c1d002d8280030b052034107250b5080005443c5000300b441070f44d000e036201c3d00402e9036802c2c94503401000c0d118481107085084a9041e00c40c0640c0c0c0d02c05103048a51544000701081c10100040010620300840c00c0300c0101e0b500703160f400f0003042040d500c001c0c1030320b100310360400c2117980350401244d482d0303440f0300d81082502482140b50740c9603004001522246140e03180104090510b1 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 818568929 1250 818567679 818567681
    0x10f1b0807023c040207051c0912060c080f0903090904031b0b040b01060e0609190305030f0712110c0d1103030a0203030f2805090102070c080303040b0a0203070203090f030c0301 78
    0x1510b00444104501c00c01c1c541980002c0403281d010300100e80950600c1b140b9140c194481d0f42400072001501180400111454060381ca008020b005403a03020f960072071141040b101805a61940d100041c0c0d0f50303000560801c1402c01180d002c2e160041c0190f0038081640144907051001810a030700744000c1d44120302070200010b48056005116901075060382c00c2c40d182805922106070444403e1001060000029480b2082a180100c10071242c41c0c00740110741f03200084121031608040d20310b010000c0c0500c06911400c00a15110f0300c141045007114181c803c00f21241e8411a88111182d0020381c40c2c1c41040c0b070400c01c9841154000c2c604080b0307002c20240003a245520604814000da00040104807200041c0541a039010000254041c0b00100203e2054020308041c110403801d035076200082009070341c00b5816180c0f0b80386d100d040041d25644951200b61369070000c4804aa030551500001501ca40303003070081d43d01849594004600304060b40c410048060780401280b40c25124800031440c0caa502 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 818570179 1250 818568929 818568979
    0x604090507020f06070e1c02061e0a110a12080402040f020412020a05030610030b070203041e150e090c0d0902040c09061b08030c0306130f020306010f1b080702 70
    0x201e038008040c0b91810107203460608000810070301c1030000d03000c401d0145484d2002d84034030302003229050007400700007440015070341d00407152034a81c0102112049462021510300a0602c00000d441e030401142c00101c40d1a621101180001c040e0010103020032102c5005044481c1c010348010b02c0440e4403540045544207e030040d90040304c161002c0c0030500c041d03051075014000580342c160060641e6103044102ca404014891200510621040700020b500e40d201384191000341c02c07840031941c03900c04a0000b11143c44001e0150400040e540c05110b450305010300e4414103500c501402c0c10005a0320400c0035002a00510480060343c0c0d00c0c1d04c2082d0050f9101d01c6002a088195215002520300300a002821042c400300c2070741205003509a85400710316840c050b80d80c0040c002c0110f9980369600008a021613246500380da0305d0a05080c1d0200c0000c1060300598890b00b42a40c0d168005600d40004462040204c400e10340b124600c0f04401010030450750040c118140040c0c800341081c010f02e60344c0b1002e901 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 818571429 1250 818570179 818570191
    0xe030a060203010521071e1d04151b030e010e030d0f0e0a080d051e07020d030f180f0c03020a14030705010c050d0e2d0316060504030305030606040905 66
    0x26000005100a181101500c0c1c20717030035904d054455400004620030307030f1000503004454415a550045103c4800c50380c0c2c0e1b101c050311800780109104016051084c00142060301c0c200d07016014041e07020340c468810320400114822400c0241503818001509a00404542c1030b5500381d55288c0400440100742000185044030010100060310881043c041d01112918000408190402030000002c40d10400555010300050140061240c07600041c041d80751505078a508040c040c0c003400c000c0c0254001c2100052100e00b51014080c40441203108401c03074a17007400c0000582c0401d8840740109100080482506200341e4006000e5a2250000741d0402e00c107074400010a84c44440444060900f0302c01900200000e08101d0b58036202591440d4581c0c02828245040044540c1011003e03990302d50000b0750a0400068104210800c042e240c201c0c024032031046000b88580b04903080b803581607400d40380071148aa41d0306030400707003103a030221410b85c005410300d0303030100d0140004a05c008840c4100d50040c1c1d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 818572679 1250 818571429 818571431
    0x180c040f062c061e0702100c0b1f06030f0b09040c0602070b040501090b070f021201200a0503041502040b0406112a04022a0607110604050c0d030e030a06 67
    0x1429000050701225070000140c8002c210700080301c1031a0b00c5082c2620440804108110f9810f400c0d188142c07624000c01402a5012a250725400e100302c1e0400a4140d1841c051010b414172035640902d480307151041103040502d44062204200a194480d51120203c0018004049442c0f400c1c580054445d1100341d40558452803d43c0c4100f1120380c041003480c0c0100884e0040d41c0c20319142c540081c0055041d07120310759a02030001840030401c20f0341d10343c0b1059194014140035107450403140703081c001e04043c220812801041c010700141c111104d000c2e274080340b00603900d103403459403250342d101e80182d2144042da0010740c013403002054420f00781c40508054a03050782c2d410001e151000c081c0e45031000e010f0045140d6000a031044100d003103003000017160340c41d01703840142c1c0e69188803560380140c140c0c40c42100343c400940a0b4908001340046800382c042c1c45283c0e104102031705404c2d070103502d404042e20010141d40c0b102c0e8013003482d81000e1070300103881802410140d00111044021a040c40c6860400300c0d070071 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 818573929 1250 818572679 818572697
    0x609100906080a05190905030904090602130b0403020f0103091b0e1b0319020f091e0109050306090d0c030c020925050a0c0209042a08060a0b180c040f06 67
    0x1680b00d00c2d06a40004282401d01090502030680c1201c0401c810030900c4042e100c0d00d008050000400803102908000350040002d0110307030800b0342c0290412440c074100c0c0c0407114800200c4e0300020042d40e080c0e0f42c005044500780c5109000560040c0f010328011035807071414141400440c22952109801000314400300da6580c17400c04810040b0f12100f24203aa141d03c414001e012001850b180b407900c40c103140c40b9006035070b00044034005001d4003402050700d61007400c1000c0e141c9440c600340c120b600700308020b0720b42504d0741740c540c0100741d203450048520b140140e00410607001c0c0345c0d1092190b00d044c2406030410500b01001034021911484003100c00c6008990300c0b246814507100502c80090745c802d01850007078180300020b4001840f403540a03101900c036140100c0402c00348180c002c43d00003001d002d91585450241c004802c540003001c1413040c002240141d5001480b00301d041c0c0141030600e0001004804040304004a800400001030172111012005000108004030020358038006050f4a481c1c20b002 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 818575179 1250 818573929 818573939
    0x171e0301080a0201020c04180609050c03100204090c0507081912110a0f02030306010903061512050607030605011806080a0b041802033705030c0d080114090603070b0906091009 77
    0x141107010806c0c41e0040f880c10401184103105100c00d0156580c0c800008110545036040c11490000c1c0070100b1681401102001c00b903117903003513009004031040400184402001a9801c1d030b020300489801030700e920f00c00c000c004010110490707140d04c2e4200340e08000800e1504030008404031078a40112608041000488822180d0070000f208007182403440207501d185400f000080c8034902c01d200c0184469100c1040a100c41401510400038041d0104d0400309109241002d581d40c550640b0340c0382c040ba00c1c1100101d40740d440b8509407183d00308201d442201940c5003003421200c441d801800310381d49554551040a866840e070242483e501845803404190401c2801058200407188040029055410340102054140700ba001c1c904550030051004515019041450462107041d9854005000c1e059a0114654100d94504d05076542c580c0a04a14500d03a02845440030040e1902e80d07040c1e010100801041c01000c0061041c040e010300164285001400815808440d034084400416403856050003 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 818576429 1250 818575179 818575183
    0x605012a0c0609170c060f0d1b05040f1a04030308060d0609050304080c0414040605040c0b030115122901030902120d02060c13030b04061b0c02120a171e0301080a020102 74
    0x1382400b00613000c0e0450f0514800020028407804240884040004c1200c2110380010341c801003203112480c50407d111501024010a940d20031b01401242c901e01c16008541508003804010440308502e203210310f0581141c4040d00c41a200620103980b2001042a0300005203a0b40a0350300014443c10003103803190b05140b20203041440e0034140502442c41c011103d071132808140178083d006504031200040076111424120040c001c66005100c00070b90000000500607004601203845580d6079a42080307840e03404110328161420205548544021282c926050003045003401042c508141000100000b61b82d02151000038a2400801c80350040301407004840d80502590340d0003079916100f80d10704060f2442c00075040300140809010002c1300c0340007a00300200c030f0b03110411403048030182540c1c1c1041094020200e025100c000c80c0108800034088018860014031f40b1510396010595024014000c41c0d81c1c840c64219030711002002d9007843e903032950b05500c00c0046002c2c1c40043d01070b000c4441743d4000a4 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 818577679 1250 818576429 818576459
    0x11161a06040903170405070506160b01052d030c030d261b09010201020d02030a0e0c030303160813021002030d05240405090a0b090d020f010605012a0c0609 68
    0x30380034500746503010002941c402c06103100e0900481c2d6001a54580d0b060142c135105064000300c0e001017001a42c902d0141d016020071281a114100070151603888000340310320b22420003550f500c803013018041011802100411507410722405030480f00710420960001e40b800204094600c04900c5190035201100340c100c000c0d0020326881e4a072000d0908080e0285100c4201c043d010108900000c03070030340e995078801e4040ba202502144c60554890808081010003402905444000c1d80300c1c0c040e540f1500c2c100842070364456400400001105496550242e4205034000c00501c0824011820480184c0e2a00314141c1e40010a600a6455040101c2c90300100c0354003404217003040c2040d0342420450f4815200c50200088140c40200c0c103130b2603044100d45068095140144200251300810841b40c50010301703941c582079a54200c5003094042c21416003210a1801200c1c001a0400302d850a0200010f0090340300350070f103694180c11075500da280c9a0540785142c000b040001d07403284042000b4000c1e02158 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 818578929 1250 818577679 818577691
    0x9082d220506090a0501050a0e0612010501020105070f05030a090f020406030b010612060b030112062316050301050904020907050d11091315091a090103151401081011161a 75
    0x2d40c6064480000100b4103c10b620a240c10050000b40c0c0711043c80c805d4690b10b40c454405020710341c44c0c25440a40b4032198109010390340c0190302e0304001800b0715200d0301e1070103011031454542c40c1c5562251340030100030b0702220009881c044a05a180c030016101c41c407543d0003c6010b16590101c0d54144000141400f80700442c581401e8107080c1e044c0310000b8a0b2003140c1c1112014800710b16440c041b4940113001c0c0540c503a0400900707404003111a054480031042c00e00c40e5148019080c0c0d2180300040c00c0e209400280501e640054100c40028014206119000c2e0044100d04240f424042203100030026142640d032021200d000110307141c91749007482d29030100148a0024213000f90500ea005040c001e540612401d004581c4820000154404900c43d124440c20040c0021407a0f41e102d080508090780c0c0e80318603048240c0303000d58085040604e440120305032031000025150000000c45824080c10b102c15030300f91099410000c0303800c0d03110f01002c00020248280502120390100c00c0302e001d90300ca002802 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 818580179 1250 818578929 818578939
    0x5010303031508100b0d150618090c0506030c0f070f0b0105180f0601030b030109060203010518060d080a1e110105070809121303120c0506010909082d2205 68
    0x1080c00340f80ca0200301c1c0001c1c2011300c00000340e00030083d000104ca820045101a052020a01c4500d02105041e0021820fa401001540c80c5140c4081000c00c2101c482140140c040400c003801404245401e03801590400440243d1900308802c40303c03064502d5001c11400c42d0042841c0000e0820882c115040c1c07401041c0850321100c05c0004241440300c1034070000c1c40005440340030800252103030700981c85051403540241c000c2000e140b0f0751409030025802070003103d10501003034180042c48844800c01a20840001c0c18854180c10b050f60785100c103800c4074140c641841104e05c0f0b15000e01c5041d5542000c1e80c0c160f90380390404204295401421203c02402c52000c00660108000e00344100087d0901c102c51007819a03581c521000140d80704914194100070a20070605410b031400303a07880310000c80e10f94002e9007a12600d90342c9417000b80840d20100c8005280200900072450031024000d51001d0800c0d10024004004440c03048405e059445601d40001001941480050040c801e90090b405420b040d12 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 818581429 1250 818580179 818580221
    0xb06010509100c03020f0d0e040b03010b060f0d14040305040302091312180b1b07060c020a03080d18050607031505090105121204230108070c11061204060501030303 72
    0x115031600030140a003410b12680300203c8080510070000203c001e01141d040d03402c9400c0703540006010f81c92845407184160304040b80d031486854107104914490303400030711551807d0725501840c049504480e40000100d0b6840b0f1401501c2d180c00c505080c4a944260354131070780c0b9803c40c4108100078038003820705c5148800003e0140002040c0e0350800b0702160007420496200c1070a18a0110881d6407908210712420b80490144007185400541540204009080e15443ea4071020304072043c84040300082d60160306040c081000c03072010300052581c0c1ca80705402140d511000d4030141c036421107905d41120f03240d224000b00400380b035141c4100900c5450008007112020b191600081d040c1e031040c007400780714901c2c035002900710100811208400f2030310080a03a88442d075030741441d0000a0040d00107101d0000c0740509040561013105007038171500c201e44502c1d003100c9407130300d410324100340b43e07440c00c0d0b002442080103000c40b0540000542c4107610034880800c1030b60451030b00400392a24080d600b014a02081 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 818582679 1250 818581429 818581447
    0xf09020a030206090f03010e070f17030d050c07022d03010b010c290c1905030606030a09060f150f0f030206070b150d0302060f0f0c04050616020a080a0b060105 70
    0x14100344126030b0115003040c0c540b0000720004610010745007070b0a0f1b166103040074030682c00c540411270104032011074000407542651031900c20444020800c01c0344854101300700745c1c1101180c030340c407058200b103074080d426081410b198082500300d0b4039081081165000384a245080d1001c203841c204448a00703400034001011000000f81c00c000c4004001803110803201c1203440c00725101d944e40424803001249c01081c6040a08a141e900d134080e100c0d1440031400462040b0104d4003803c11207001d180058052743c0b5540d074038540d08c0018006000e0444401d034441400020300c0ba100c1c00340f03840710950264aa41005d12b17103044070b2815000e5a1088980da8001c0034104050394030341059034800da820a2540c00741b0354400c5410078008046c00b030155402842d503c1c6410034507074001102e91003241d46c070900303025645509800c984554022144d1180d089000c000a20660401c000035040c20b10740711034841640c070701a81c0060324000e459040b100b0694002c6904100f032000c0138540541264003801c00515040c80d072 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 818583929 1250 818582679 818582689
    0x706050a0609110a031806090c03060c02060f0f091f2a080417130e090609060408041205030408010606180f0302130e150a0c0306080c032508010c05030a0f0902 70
    0x15038460f105041d030742e1b00107601030140003030300e0f00381d03a54450000c200302c05991500c8030710025540002c0d10700a1034005c0d8008042c0c00025091b001c0d401a5281c14001c1d030b55078040140c4201d005000409a00450750440b412009510702c01c420811001030200f140d20b030028600c60192424003058a516102110a81c0b0040c0c02682035038005410603a800e010f035850704000b50f20f5200e903404c41103c00715900e10006048404102241c000c14012058503615121051030340c1e42d0381420f6a001e0019041000304000120f24600120707a6184607000381c0f81850b0307550038030364215680ca5020b00c002c11503041d23a01504064515214015000041002c0d80181c2107401007000d4004652108005035650344404035030840400c501c8500341c940c07030304656851070f148248601814040301481c0110341003000c0030546040200b8502e03038644015000703184200c0181c40b00050007544d000400c01e05c0303400308000b0071001d4003802200002c2d201d80c1c4a440d5a030421054900c21a4902159071400030319101c203680040e511 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 818585179 1250 818583929 818583937
    0x1e03160b031501090f12061b21090b090c1008070534060915020901021b010306151d0105070f020f03030d091407080114010e040c05060706050a060911 66
    0x2d2000e803800702d08400011390f0000b43c2d54000d02070083c10300c0d0300010462900480d0f20b200b01d200b01800e00004408958a01201e01c0710400c0b84086810903003a04101e041c0380643d8032940741509804121034216840d01c0070550001d0303d11084a82122101140a042c0300803042001611481c24114500e080c01c40140785000303174a1011090711844035500e9040ba200038990202007a0640e900c00f900031285801d000404807140c00b00c4525010889211310150710344260341d1aa031068020b41088241c0500b000c0399414034034800d6042c55a01c4801148156090002c146407907465100e6440203070b4031017000e00d100200be244c0c840c1000420010f0301c00140284040d500d45a0307060703420b18441003603040003070b06500600445886292501002c4418000b50088400c0c500704028160b40c45552500d22041c2a158285100c0120004801c0100100540c10310741950140c01400354402e055103d04c00910356034064502910296224018451342c11294821803000b0716144404100710480c030303c1c1d02505801 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 818586429 1250 818585179 818585191
    0x91605011b0609200109090501050112050402190e070e09100620060c0a08010f0b03061c0605040b04031106040b011505070503040b03011815120305091e03160b03 71
    0x38000d01d07110401c00c1503080303440e203c2d90044100b80316641140701d030003000300c81141d80390024134045070021361080c2d0703441098160780040e03403800811075038024200040c180103042282c04c0380a0000c01c190041c4100d00803409011400c03920006400c204000a107146440c004080c840d2a2090601a421001400b6503084410908055076680340110041a038000f812400e880b150190344100800782d010b440080604850035101c0c00c0540e41c071000006015221400b4041d26042c0c01c00c040b6001d460888420303030030030101c0400b0b42110541075036105d00303030b0f002503030112404a00d140c00c0c00200364200b559001d042c803604004145520382925010940c50040c0300d440f8005e5682c5060202d1103124008039801c2541220807070b5076032035503403a804030b284c2d100b481940b0710200000e03040c003036800c41801200000340354080500321950130b240f489007181d101202c0c12001e108003081485066107510741d840d01601080c420480c88441d001e0240740c2801e14011032003029018040b01030050b2a144070a590b00a0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 818587679 1250 818586429 818586467
    0x180b120a020903010c0f17090601121b0e0412030b102718111305040c17040c060f0215040f1e0b0a1b02060402011809060e09160501 58
    0x2484101400c402481041401900340d400c00c115040d14540000d1000503071422640c880342410486c060f010049802601c1900c2c058000800410026030b07034059080c00d40380031746010b041c40c080d40b503030840b481601c0e50301420141900320100014081082c112051901950a00b03200701202c1304c2c0002c10461100316000240080d043c0441e820f0601400c0d034003030320300c90010200045521403c18541c094072583c411540182000c03044640d203410002a40c2411704281d5100170b09070704003010003024180414220040200c0081621264600c0d490414041d90103110829281400c4c0080100744101049040055521064140c2408500c0406132a8040d400014903d4541c00a00e02410b000038010035040101200d0b070155802c2c007602d80c02c502c0c095468038030104080340050054500840a0b1a0350b140540c00400010700954000d010050109036900c1003050703000e8942096030115207040d0401c04280760050108000c0031800c006044920405800f8820744038986000288056842d136403180242d = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 818588929 1250 818587679 818587681
    0x709091218050d0501090606050f060703030507030f0203010909140111070b06060417060708090604020112020319020d0207030905041104060507030e04020a080f161b0213050f07180b12 81
    0x10140d03181c07820014000003000442d001da15410164042c24698038151941440c0c507000248a00c1c041600402c404409414982010400d4800380c008100040c2000103043d103c00400d0014541d0384025070103041d003210005580e002e5800c20611f070f100e44180e1200c00c0c0c1c0c504010780d104e4440030010f4070350003580000000010385c1c40001050860081d6880300c2c24201c2c41c20600c0a0b40040491401c1c8038105941c0c0c0c2c0040c03940c030140401d45c0d4440c1a2400381c00b10310891400c1600c003400b40c00a6903c00a003c405245071701c1c0d62080c5104aa1101d11442e401039404034900c001c05603c10440401004c1c02c44050180c01ca160340386041d61310481c426801448030000359a4101130141091082c4038000500c115201d001508029226200888161006e20544e100244c01c00c0c1c07203802c40b040c4242031039441c01c8001e024143c104000c986401000daa0003484c088044400c02c005c0d005003071240b40c089400e01d171f0505200328040c0c10041e018040c800c10b900314140c18070540601509440b4102d585180d4180d007 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 818590179 1250 818588929 818588957
    0xf0c011805061f051e04470d02040b0d1b0501030b060d090213020304061d0d0e010f090305070f1e030503030708060f040f14060d02010804112b0507090912 68
    0x8124285001642c000b400e04400317420494004c0d03104510394007604407e100b804250801c0c02c0300780c100000d400c40410345558400d986424860048052310f4800390000500070000e400249009007958012a940e9000c5c01801004125018901d00104420700301442045400c0c0e0026003180030b85004506c1056890100c1e0b000c1d5a0340a1044011100101f421962414681405800b8007400e0601001e1090780043d8502c100d0302c0094102d181200d0395440c1d41d0425540e40044828003078490000040000708840400414801c1c04007800600303044030700400f00d1345000c0e01e074543d000d25007542440c4101030010400204601004582d0b105800b840d0100d03065403464001885d4180184603140c02c64540701e0071106085c010360109080020a80c0807003040d03601c0c0c10800418014110000740001c030480f0126002420034643da400d1000f005200a06140125155010250320740d03c0c114009046a50208140201808240301600100009002010254030f811040d03c05a001e50010850400030300c1174 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 818591429 1250 818590179 818590219
    0x1a011b08090a030c06020105060a06050d050405030c030c01090605060901061e09210302060604051b160b091e010212060f01170a0b121605060f0c011805061f05 70
    0x4040d1900078401c08a06843c0d0416203400c03580f9000e443c01661801010a0341c40c50f01c0c4815200f00c40741035441500d0140d207020b511020306805803080300c02e44400c1c00391900014040c000b812050308500000160a45103081c03410076a2009170640340520f0a4500500501341d2242101c041401d00071400900d0740c00d420b0003144d90040a520001c1d14120f218003919615501e0a89040440d02a500b180ca0b1500e481003040201c2d1401d603004c3d500071407800c1c0210002c4c0400005404581c80010f800001d01c03941c0e881d18049000e088a0041184d0040116107680a01200e040828001020000c60421014400c2c22505801c0603100900c0b5521100301112540c0c800c2c4000403441c2c0d217000d404030303984c14044074200260414000c001c0c402e008014400495800000325105003601c180040740e186403400c41800071550011207100ca80341801c12911451810034009e09003c10701c8582c0840803c01582003141c188403018102d0607900c2a42c148c1500b00c61a2082c81c00261141220401042100300c54030107 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 818592679 1250 818591429 818591437
    0x112201011071d040302060f0705090409050c0402030a0203101212140714010b010917030f16050a0c031208091b0a031b06110f0703061109060c101a011b08 68
    0x400281c1c80b00e040f245102e6100c80c0f8040d80c40780d000ca07600e940722940d051541e920225003800c00a4814000c2018515258202652641c0210151044da12144001c00c090364070488514140355000014040600015642580117105100c1c40c003240354820340da56008100d0b01d107802010081c2c0e072000644040c070120101e61130268460000768880141e098824040c01c1001c060601080950314001003181d180c014645401e010782d0007842c549940d0070300c1030109400039075141e14015000c50245001038020001181c034203004d00070f24040e891451418015405a0f41428810000c4e600300b0301c950448001004c00401d03086904003d00c02110301c01044083e0031070b80c4041c0c28400099200103020034290354070000e031485940c0f4074015500d54a6405d503501100b40d11031006070300041041021881a40c005000b00c0381eaa18020700c0d107500100040e490760454405600190007440d0803247c905000d2050060072000001c6004510300f5400000e002c401d0781c18104a011020002403008200c2e10300212 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 818593929 1250 818592679 818592689
    0x306061912020a0b0315040b0f0a0312030912020303012c161e11120f030a110417030310080606010e01050c1006030804031502040e060f04060905011220101107 70
    0x754032490040303440080e005102907a2401071707141050b108514203001e5000c003501000501601e80040c0755603201750100101e001350cc02095602d166290004654003082407400d000c3d43d0065807254108440310200041c0001c81c206044030818641c080705041440a9500040482d60401010b2040000b580c0d03000700c00303001540d20005007100b0000c4640010003120007003000310480d0326242424280c4803e610801d0300b2028060001c0c00040c480900c60340000102c14102000207040c19600c00722410b951940503e984e21981000c810400d100000b0803002c1c006290070401001141082030000e814818000c0e42e6034108140025140034441c03040161440c44a80710802300103407962801c2c500225040707408110780031001d80e0080c034030400340390084c4d8081e11261550341007680c598004120325070760406881600180c65400c00540207600d4854036000302070b50031703100c82d80c180b181c07802c0700c0760389401a082c4c0048505c1c1081e004c090b80303454000745040c06a03800c111480f1a07800c4230303041c5030000c0d45e401 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 818595179 1250 818593929 818593949
    0x1506080307050105010b03090712080d0f020a0324050409020d120806090f0f0705090d1505061009030809120a06051302041a010e040c03140a06050306061912020a 71
    0x10008501000100908001e0b004100030419030f40c0751400030346a484266001c0c03ca035800074106004803442c00c150903448902c5094110715200c0110010700946600d041c004040d42d6001c140610391903014000d201030101507900c40d120400c1c08001140b0101ca01d8012580241e43d1070302a02c1c210341760700d202084001d03000345030080349100006005081c980c088900e40d005100c000080b41122001c840300c240038680c1503110110540c7c804c88100d4280c1c00012206034404542c41440300032903100c22052505200340e003004035017481c11f03e0070f004159400980400402040080c10804a16103e050303a4800000311920241c03480503140305460015010030181c001e42c0380c0000d1010443e4080d0007480294400c1c1c038248030001c002603841885008200019006c207129840e410741da4a416400602400254100010384000c03100d114031025404545000360384c3d641c3c032418403162030b007086225404001210201181c80d02050481e60740340c400c1c4148403d45d441134503441c04554890b0a000d002d4007402d48 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 818596429 1250 818595179 818595191
    0x204030c0312090608160320162a0e0403020f0f0102090f063109110c0127061107151407030e1902030705060a08161b0602030415 57
    0x500c40e20600900c1c101e02c2c007081148000041c441e0095909900c40c5886107040240c030313a2a5501a07028009940d40b03c05842d103d029400406004c030030250212a2014203052401081032500c00380d1401c0c1c150040c0e81a812403405281e00315480540716003038411040d0414119201c600d4241c1c03522006081800d100d0140c001c6001000c801540905407000c81141c070004144148014060a4841c40001e014100f441010305110000c031400b4040c070001c0102285442c4940e2140b5800c2220711220404c88603c82c00120b501c042403007406112100b11100d449507100841001245491140c0780c807005100d20380b40c05140705203040e20816034440540109581c0389003000501e03008000d200c3c0052190f5106c41e0000810416803203031140307031100481c5030010011100d564001c1c1400051301503040764544644807000c030302c903141c0d94041c040d00b810725110080d850514050003110404090206000c0010b00e51009496549850a8105054000c18016a20346550401e00201c0200000141c4810708002c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 818597679 1250 818596429 818596433
    0x150c0601030b24010f050318030406050d0b0f09060d05030c060c04170109030f0e031f0905070e0705190519090f0537120c050f060306150901030204030c03 68
    0x9a42107214511005401e1104442d0f9144007041e080411440c0c1c1c00100b280d045a000e0901500007907810090540c00b00c140b40001e4110940740d80c1c4290060300c005080460b400340359803034500503168000030854200c0c14440740040418a6031100034401c0d840390002666040c05c0c08010710803a4080500d1001341da0701460408050402613200340726038511501c14201030078210750180700311000c030b55041e601c003021103a03411000c0b5a5807040c0c0840d1075050080403a4400b522800310300144105400b9280410080e419040540c100542c0d503000d20440d210542c01c01c031030940d001007192000c0e0302e401600210312140300c0c4206c5060003646a0881c0600c29a00d10740c0c44203810441050407100c03410303a10114552104140100d00c0340c510204041c1c10450360300410303172025490900425a2154081155150f51840040410301c4ca02805440713075000600240010b0034500c216105c1948255442d0b0700d14103200c0d000c241e00c404108500d0074080380204d041e9500d03078802d8040342d004581003841c0c844459164 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 818598929 1250 818597679 818597693
    0x213060905040201080601020f0d03020a09050405100e1006020a29040b0a150f2310030b04110a05071b050a320a0e0a020f030c0a0305090c030309150c060103 69
    0x2d46050303012800560000d03c80d98400100c60102502e010003a01103034140000c21b030080c3d00114a03181c18030958405c00301d0720307480e24441e00f4440d44511160a10651600f031102e05030b502c02a0202c6404002d40c44140009500001c84840b181d503c00321041c200640034690100402c1e01080c5901800480c0051105000c1300012480c060341c090306d010051101400303106954054035216122080d40488400c01041c40d00620110008090a0140c511030310020006014805030b0000030300401e645030048911410325125000c500c0d6020440c4605c4d00316001d0002d0000c0c010244000e0545031800c4d1604c00043c0e00448000090401a040da201300e80c60f0708001120310060707105070130050781607000034000b01c2c99943e03d02c04004000d030400c0e0810342040005540e1980003000e0340700b42c3d5020001d5000d1061110000c0d885240310410003512000101c80080c161340002d440c03d422980001d140f0340c00380e5030100072691040400c072660041c0214241e00e0981c2d60140c100026254007400300000305012403 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 818600179 1250 818598929 818598931
    0x12040506070e04060503120918091b01140706150e091e01090201090510053604290103060b07080c0706020d05040306110c07170106090203041104090213060905 70
    0x1151101c0c0c00b0102c015042c04100e907000c2c42015813640c801e10001e2035020f030040c024103161002502480000640441e60380e130f0883d059446040c107a004d500900c04030300c0b401310452081002441d040c400500c107117150301d0390380c0207000300a0100355540c0d00c9070500385415010400144180f014420580ca4401c031030ba41c845950040b0030503030000c0011039884180b018810b03803c1403a0305844114040b418a424080b640030003c0f01743d4280102000f60402400415608200e07500900c981c4036401c0d8900c801c842c80705080782c020180541e040002008954070840f1101e828689454522a04025020012005000c442d8804100d9510018200c001c0c00314080003440e1549014080301d50312035036400c2c102d1340c2d0921a80010001a800d000910024000b50004a8520a8442c059042c00b202e03108250030321186030701c050b03136071152011011507000080c0100300c010800360b01c0842c250f1a00b500c070105036505a1050354415541e40000300c04543d64940e030321140441400d4104519034840918030000d141c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 818601429 1250 818600179 818600191
    0xf0b090c0319090203070303050903102a1e053f0c040b0910030603081b010e07050d0b0603011508010e01050a1a040504080409021c06060903051504060212040506 71
    0x142d50020344450361264061501182d90207402400d0191035524115a560841010191706006401c4c90b145003080c18018005502000c0f80019081050000d5800071509000301007818891f80a40e40c070701c035603c040e50b8100c2004c3d05080299640c2c1782d05e81c03606c002c0e90344511503485003407441304031754000300c139100c112141190b585149600a0300c9006107074129000368407880007200c0b4200162070303c90504010080040d20b49090209009480340e43c0d40851340c10503121a607171000e0600b800a08114240150003142680c02e015140445c01c1101140200751800d0f80541540707000f0000c0f4095440960228181100024280621607260344040340607080c500b02d82d4100b50301304030100b07200045600c40c10210b00d031604140d00e2104000014030014100c0240103a84516043c840050b0000700341c0001c03c1c0c4109090100d6580d00740c0700e124003046a41e0fa41000701004010041400040c400007091807140b003010403890a140d81e11320340000030740300380c201440007200980113100800c28000b4040780510 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 818602679 1250 818601429 818601451
    0x180b0d091a0c070335060306100506040b25030f030c050909010302100e0619020f070e0c0c100903050d0c0c0803070e12060108070e0c03190f0b090c03 66
    0x84a03021414102442074900d1689002c04015400c0042e000d0b648800400c0e07454007940314031005054920403400042c1164089580d1100b003003156034038042c00020ba000c984070f03021118042c141800300e800c3c3e0190b070260696030100040ca48513100c01e5528803c2e440c092000d014032000c00c040c90000d020910101c82c1c0b0012034207060402d0101d50080c0c0035107001100241090100380e186408011030150303080281c40030300045c41140700e20744d02c4240044c141000c6844c0c001e10406501741c8020314148080038182140d0b0000c1400340b009089040c0d0050300700401c1c03442c0d642c403070044121260a04503a24000c0c00858a04120340c8201a00507000e0a03030756944420412101c4141102030340c091107040c1c03004000803070800c00903612034041c020310001c28402800200c4000018511189041020f0b00401007940c416042000740c070f070b5400300d070a6104694460302421410036810b608140003903050400c0070141c0b5a10032126003c8590b000e8070110200030659642410280c40d1103213a94401c0e51110028 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 818603929 1250 818602679 818602703
    0xc230706050a081617040b09100608061602121314010c020102070b0c0c040204181d030301090b060c030d0e070b0f07150219020106062d180b0d09 64
    0x11801a001d444802d01543c8502e0125500c0e50001c45040a041d081d00c0d080c000c4005052511a0f0040d4625104610a4140c02c070a03003003d80348a8039041d00b5100c0d40d82d9050a081d000d128015011500c01d4100741030f0318401d00150f00c00c0c10306074100b10500700459401c140210304110070045680c040003c44a008180c011201200c80c011a103c10071494007038090f90040508001c1400060000c200d40920b00e01501e04145004c0c2c001001d80c0d00c19800b41c201810030040355070050b0064420aa0f20700060b030000901011281b0805880b40014410215455607031700d00181180c032054120341c64003042900b41c035070329a0b084446500070000c80c40d500a5901c9041c4c404225040c0031412290010440080d082c14807445581e103410300302a240f008030130b0b2602030040c01007540d11100184180300054002080c05801d02100408041054410b00d40510146031084001081202c000070411444e01d031000b6003140e4110201401c040b00d0384031494034800000c0c0b0f2240c01146500c014960b601c2a0240d6000d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 818605179 1250 818603929 818603939
    0x703050f090613062018060a080c03071205040303290d061d01060e0901051b040b0702041d0d0908060108120304260a12060f150c2307 59
    0x10500031070315002680d02ca44089050541400d00c103440c1a8410340380411038441c0c624100007150912040400042000300b0003407503403000c0700d13000f02da0110b0a0744c015041400e41c042c02080028003a10381500141c00001041409200d00104003a01240c0756040c00f09082c14138004004050b08240480144400b10600c00d540c1500c8020242c1c41030014880300000034251640d10081010b00d51001d020031403100300180000e000e00a0400a1201c130007441100d1511188135829104010003c0080128040300d070030b0741000c120309481c02d6071420030a850f112015403010034014000843d01c000c0501000c00070700f420401c0020600160b805550b1a010020303654200d03a59641d50038003409416821a050807042e5a511710041c59019000b04160308000036007150418070218041d01a88400100042d0003c1d6940c114840500d010144a070410502e45406083d134046043c0b8060340303500d07110800b201000c442c400c2820030042604001c0c02140d11406203200b01c191086628815582e018440300028 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 818606429 1250 818605179 818605201
    0xc07060e010b03031b0a0209180607080402013f15140609190b190f02032107140301120201080603280f050f1e010213030209060a081203070305 63
    0xc002c0380050015414200604c00500c3c50016042540c891807261050303440141c3c0d2441540f078054418506842c9243c7c0d100f511407414150700070440c200384900380d828000184d83c4140745031601440d080f0050007901c00c00000c00b41e0720050900400d07100c0d511110302d00700f140c810f6100b00c2e005102c241030030100c0d542c1c5404141c0204104202168840d1003070200703003100c0c01c0071050300c500d070f013045c6800002a80c0c0303940382000c00350841c03030b20381020f429a100400107060b04a000c0260700389990004500340210b80501050000695004c4210f22003940301107031400c0e001c1d000b000000c40c180c50700c1c2912503844040201e55101c000e40203a0016841c2c0000c2030035414041a802d5070000f06c9011a0360040c02ea0b0380440a8a507020800ca820500c440c1d10b040110700c080c40700410021620014118080f0010904031115141d1024105541d10406c2402d0310003aa4040303c0c800c5a40c10388803107805030b403408001a41641960b20000c0c09028584050b040403008400861080030a80c904115944075440400 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 818607679 1250 818606429 818606441
    0x1d0c010906090b0d0b15040501090f08101109220506010908030d0b0102030d052e0f090915051303030501121208130221011a060f0c01020405090c07060e01 68
    0xc00415189031091081c00a01002002001c002240101790a203400d000304a0210300f003c144a20340f100498280029a80080d000b40180343d50b00c015690507041c440d0117070301c5440c40115407102a6940c103505054800c0394003034440d8580e005058898468680100039101e0341c4510751441410b00d0000010f020358041d0300103400f075403880c030001c504003a1402480c00c000c211070f01c181070641c0710621070801e10300c45038061980b08000040e8941e18030700c00c00d00c81c0c00d1454049600da0310a460080320a200b00c0484c01110b004070b550a01c4089070f0611582400b008408008804080c2141408100081c1092904903134048610a5808001d0381e03a885280b08001c1038402c00003007601e00015903070003880744208021500203040407410a035030612a03002802d80720582400b219880401c079002d89643c1801e00c80d100c08510003025960f85d010002d00011818031400011141c0d000c07003c00c41d821180030960540c1c2c003806001e0300ca1601410903110352010313900701080c100c40b418101308480c0780e1504180202 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 818608929 1250 818607679 818607689
    0xa14070303051e09040f02040302120d052506020c06071b03020c2704050601061701050d021903170304020406090c090e060409081207032003040b191d0c0109 69
    0x6043c1092184607845089114a041070f03840f0080c841e0205071303542c52080300804810365400503178071482c600c144a4080d001d0804100c1c6600101e0140e401075420900302c2e001a8054100300d00c0c005a100039006148821000c054511440410040742d161400900b0728010120303915000f14040b80791031840c00800d00c0074001401a003007100f6403015410a15100b03800550042c0e4000c10008080c9000e0b81e42010469003a5110381c060001085110703004580105541404c4020f16110b43c102004a11081080b980c0223002c3c0a104102c4401c40e1084c2c1c1291019542c4490107800b21034407082c0201e9180c0050760180c0c422443c00340d0006002c11a84070b40740307416400e515604480c41c0762802141c0c04c29002405c81d078200780c03070b00351100000c0c804c900104414810300000b0401400e000e40e0080403214010420260460440d000703842a42da10000d40e6446540800c0c030180039580c42c00369210b00d2a1011000f60340605050a0980d01b200805400d4003000c0001d040794110f2042d078004542c6002540f00d1 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 818610179 1250 818608929 818608937
    0x60605150d0c03020f0703031a042c0c03070306060317180d05030c030f030f010b040b0f032215050c04380f12100308030604180c080a14070303 63
    0x10103091403007190401c2c100c40312142001402c0c007500e030440700f00c2036108500c22000660364509080303688441100f44504114103590411100070946441c41241c1081e03c140341203560b010b103003084242001c1204041011000d0b0650700c80507928034105015060342d00040f5410301d011000c1b94083c48418080d1000b980c030fa0b08a054030038011200f4441710500b00c0b4002d94960104100302001910200001d024004101c90b0a40c0d4901c3c0c0040d8841c2100c0048e00644e030a100100420491400c07d1800c1d00c883d000f982210301d80e240c89401608402204603d64010400c50b08030320300041c0100da13114456071881c0c80c1410710180d030721208042e515104078058807030300340780d139681c84050401e01c09012100c03804410715010380c0c0c403910303041311150fa0003c1400300a00f410000c1c0d03080028940786203c42e088680501180c1905042d5a116030007800010665409999141e0b541d032480c801000465032601d8200703485007030440c0c4503040076488003102c020076541d591440b01c19002a44c40000c0c48000c494255035 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 818611429 1250 818610179 818610187
    0x10f0b03070915141b010506100207030b10080a030806031b22020c0601080c010f0206040f0f0f0b0a0f06081b010c0302030c060c0a030612020a1403190b0406060515 72
    0x2240c0403a40044030f000000300142480007000b40169000208002049507122841a81100c50200c1c01c0d204000c1040c0d0042c180c00250b00030580d0001051020703031364442c03a41c07901550350580c03c024003d59640604110b1084519031001d25403c002203502600341602079905800204009410060318403400c150010f446401c41203c900c0410b813040100910541e002d86002a4055041e28045e000e07005039640d40c0205040908030b6030842800044180345001500c0e00346490b4451031000700c11264003a04179403c14001d03008210020041d2032569602524661080c14001011001849101d50b000f82c0d00389003401c04581140002031010030f0038042d0b00c0204000340040011200050604411015071000b4011002051000e20445200d4500740d407903982c40e0000d00100805890700d56119040082e400100c00016807510500030b0280c0320040c008044440302100400c0ca8406003500c02140300c00c035075070072004110505800c2030203180514414814143c580c810010074030781d00142008040c00403c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 818612679 1250 818611429 818611439
    0x90411090601030e03070507150804050606040207022b030e12061f050d030f02070b1602042012010f0e0603100c090e041506060504050f0402030a090c0e010f0b030709 73
    0x10491070351081041c500400e400d5500c1c1c610314a541c014413000c5072036401c403c1007409000003100c0d075803450505500e059001070a00da2101170b110400900b44070b00171900041d031842035440e5020402010ba141038111058562961950a00e202c90b2800840018900800d0f024140c0b0303000e202c1c056092049406401d4940740c0131000502515220782c3e40d8034880841c5000101562914920300c0c10a0082d183d10700072981c44a0002d0402c101900410317581e22007804214140006151020f901c10b03410b031400981c0f000c03014843c180005111801d40448480080d00c803a031040001c101904271032101e9204140d0039103a40d03d00122050460f09550158000410400380e00d92540160b01ca4071000c1c02c0c102c82d450345400304c940c5074200c11a01a6464424161108010307810b9100f03c00c010061454141d09060030a40028807031002d141d00544035540100c003240400c2c1155110040c0d5541c0301503404415a0386113040c4191034424800c404240b203a0100000740400203900312449000301d540c0c1d140c2072038181 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 818613929 1250 818612679 818612689
    0x30b0a0212060f220f2901031802011128060e03120c030c090307031226010506070302030c0106140a08010501061b06020d11090319120e190b18090411 66
    0x303030200d0b0043e65210b650b15501d07000a445001d01068220b10060401c003680000c4086c110426070200c2e041516007000e50780c03e5402d41100c49407140e0309203442e070b00101801000c0da1612048084c20004080005111540c48411049071040c40d8820341d024070203a440d010090352a40180c2820800d158180304c00a1800d1142e04015903020a500c840c00e400d14000c0f001107072400641d40c0040f00d401002100c00b82041d9006201c1d01c2c103441900030100e007002604204415008418424180185000700307102c02054005d1040d0784030340103804001c1010a45d1140b88480750b80035492410b00841ea41e03074000ca140c1d4410b0180d0740c141d4400b03807126480204642400c25080001d140c00b036401c03990911000c413042283d03002d130541c0c4c2400500d80589600e481410107050803000003c0700c5280c1d41403501140050b030003e010072800115402c007090ba030b02e04480850003000800c2c203080d8100c0b20707030341d0040b9000711201c010741400354000108141e005000428402d64120554001e0001c407134081c5c40c800d2a14103 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 818615179 1250 818613929 818613979
    0x60e1302030c030c070c1e060305130c03143408032502060405030a0c09060603060518040302012301060e04090206181c0503091203031003030e0307030b0a0212060f 72
    0x1103400b086c0712a0345e480e003010059031401c9a10910401070308600b0043c1d580d05001d0309801c80001c84080c0c03144181503075108a088120300c40105600f1603600581d403502d2013882005282c090080f0050490600d001003030140030325001640b580300c5020000880c50490000544000460501c3c02030650074070040f200500f50b044410403a4011810000481c064a0610051881a100304c070b030080710301d041480007015aa6150440802c05203840c00801659607402030320045062149a000303000c0c0c0311802d040740580014a810440388003d40d80f446031800065a90604031442aa6650308100c821820042076039103414004e9444503043c06210340d0055030040800071208020105488089001408103a80901040c16903054001280c210418100a101c49002c5005034001e58914a04044c186092031424000501000300104001c16280c600300000b10145802c1601840b041c84c0c0480e840703001c0c1d4030a034200c0c1d00040032074021540350308044084500c2e4000081906403d1001052038540c2042 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 818616429 1250 818615179 818615183
    0x70b0c0102130b070c0b09060a0509030109020301020415020705011805192c0a14040b0a0603081621021c02070902040902031e102102030106060e1302030c030c07 71
    0x160800c00000324060b120080c034002d103e50b000e8181c0301c24480c1424012207003142d10080000c1002c212400065076024220380c143c40d0a405c009440b00d6a46021070300500c06101c0080d01503100103008150f0040c1e002203140031070303581d500321003840d80c445004403505101500c01641c803585441f0706208c00e2034162021040090826241e6042d45ea42d218003007010501341500c81391030703940e070700702030003002d502c0d459040d07010b50801024400d9801c1c2005581c454280208090614050355020070804641c54000c07400645d0401e80d200e44556210482101808090408446000e245d02d030f660a00b401d00c3e4425961051141c012300719551003611483c000486500041007180186c690100c0d10181341d102a10190417140070041c1c50f0b1400c409141050701016002c4e0726402d051000f08284018031407442c90a031500015191401d41c4544001e00c81c040300504001c3d0b155003000c4000c54640d41c0071075180203814044408504448400ca42c034005c900c800d503400c1100110401c002203007921694000d000c068 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 818617679 1250 818616429 818616431
    0x40c03020904111e03060f0d080c06070806090703050f060415030c0f080d09120303090602070b090a02030606060c0715050405090f06100e1018120c210302070b0c01 72
    0x301000c0c000030119070a6040343c1011410202d00c248412522004060844a042440c0c0b46541881c600040351107007144c405911450310140020b04205260060b28031428034030044540c0b90400980240c410700c03040307949500039210000041c1c0118401d0140c103005a01c010314014840c2ca0b0707001840041c04d41c0d0211030030030040002c40003000030642000180180240c864290380c06080088035130074a040e2500c2a4100b194550b4244020700312046603400c3d26600d41000201c108103803500d08041d004070320011344880000700410005500104440003403030300c02c40944082e0341d1510200142030041c9a1b01c0c004981c000c0b42d05010440303030044c90a0a55100c0c0c2006411b055444001803666507080b14603074486400c5d00184090360402566059a08801e4102100034034001c0007c651607201382483c4104111200d520b40841203903409404ac042d0040380c214000c0c0b0310140c00c00540e440141e1042c4450325002d45400816640103c609010095155014011180c5401c04840c1c1e40d42207c13030340c2d074595 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 818618929 1250 818617679 818617687
    0x5031e0420061303080c060105040b2206170c010906030203010f12050a05011e0b030a02150904061a0a14070b130512160b0f040503030c0d02070609230304050906040c0302 75
    0x72a551850f00c3c40154840c1240303c0e42c8280c0c5020041c20058180e0203d4090790400031143c426540d0106c1c1f41011811800d8259034480882c1110405016254440042c00c0416001000034204c045680c4059080c01c0e00c4082000da5034460440480c8024802c0e0202c08500c0f41051014a00c000019240d2601850440704000e0b41500d0702401c41c1e071a0503000b4680d8500b1045509a00300a0041d00442c580480181013104d6064010030b04181e4446040c1c814251b0009a840c0d4641d50303903000744040e014000087c0500c031034030621503c607a40b0000a1070302245514188200c201048000c8a100304e42c0714022141c0b80d00c42e0000b0800812800f80101d03124086c0b83e10020810280002405041440e0001c00303070040e816041040114201410707419003400218204400f10300e000084940102081c11000e0b603e0f07580340281402801203000c018100c41c1801c0041c2c0c140011070b159004405082110381c1e407200f0031020301c65943c1c40b4520410327070001080c500042040c5030650000441d1845414054030b0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 818620179 1250 818618929 818618947
    0x90607050c060a110f030316030203040f3302070c050d051014010303091e17031e0c0c101710051003090501050c040e1f08030a05031e042006 62
    0x5a003006940798000380150780001c1c0400000c001c00c001d01c03013220024500d5410941c000e550000c40488c640020315400101003020050788070802e00d00c45401100c82000030613200495901c1030b1015614400070442c42e07850705140b100f144200c41940d03500c030801f0000c0d949007006100e0040f0010f1400e0340c840c003c1d00c01c40b401c14402c90040c55840010510790184035030461a0160641c0c11640040520320f8100c1e1030503e0290f071045d004010b40309c901f0480e5107400c100c81d9800b0300c0c6110300c0b10703000d082d14825107100081c2c0c02c1c800e000d4059000e8010540b03200c002c840007440760001c02d1248417000248044041f4801d00624102903405c80146484070f00300d00d403900f011410306600c6100400029541d2902c00b001e01100384145604501d02074095480c01d0b241000b00319001001400549070314048441d035500f00000e1815038401420400c0a807500c03541a503001070602e4004488843c8084a0402c1050b4005c41c40100c0d584540c3c2d1041c00c400d9481820080c60290b44e00386085190400310810030044 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 818621429 1250 818620179 818620189
    0x2031c06120809010f08010b0304061a120f06060f03060f090a081605061f06050906250c08061b0306040b09010f03110402070c031704030f030903060c020d05090607050c 74
    0x640303103019030002d80c0d9690f030450004219074035034450b81080101000040c0013a0440700120381d007117a00014045100d001840350301c2440c88901c584140e00c001841c074130399a240c1020800708140e104400a0312055542e070070073700c0901c4030030b81441541504080006200010401d0a0980041020b800c44800502d0741d80d0b003004561000b008440100c0c103103049002044010072401c0c0d4001c1c01403a205104560754500d07850a9090360041c442444404508055161241d03015a154030780d80005004071007101c1d0603286204403000006590490140c0c10105050702c0c00510280036035421610011640110740ca00e814035000a0503003544641c41314490200f99541c00f010714080e004c032507100402e061640c9041501134401040c0b4a0140f0700521202c400300340180340110807250402100c00d140c81507180012818070494100824011100303a08409269010300d1580540344280410040b00504405c180e0f42c1d800c0524500e00054000c020035007840c20703c0c1c405000c05500c1903045840e40000080026 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 818622679 1250 818621429 818621459
    0x41b0305070e0f07090303120911090a05010e010911030a0e0c03120903010606030b060910140c03120f060a0311120102041707060f05030a360b0601090602031c06 71
    0x550b50000ea00070701002607401e0300e00355002205818005661491a0750180c0b150050b4030741c0c01101c9584d03494483c2400803200380301e814010003c00e04855440c1040380d04006020a001c0d86621610f244004030304a0050f01c515242c0701e8003003005c0d908558401140c0d1000d4101c2c548544010300880c4400b4160351801c010400c11602c3c1c2c10300b101d07104c4440e07400f490308641140e4003d0040504040c00340005032500d82c110303811030100b40c40d412050810300703200340d03107244071a8440c0c14401000159480f40c664084060801074140c0c07516401e50b43c8441801308401841031760455400411400c2c200002003d5407005000072201801203d810001c038101070342243c00560010f040403400000d40d50101c001480000c010746079508000240c60040c0e0380007840d40c040104260640c650314030700e40d801d5800a0103468001e2302e0425080d40c1d1300f81c80b5840151020402c400458204446c4000f01340c0c1980691409001d5501d10b50085040c054520040360710740401200700000d03035540d8080860f52084c004414 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 818623929 1250 818622679 818622689
    0x31302090a0c03243b07140c19030e0a0306050609062b02011b060f06150c060209060405030703050a2001050a18050907181a03041b030507 61
    0x506040c885000340035190481407540c020141d42c5001541e00d600c8107007032803d0343c4001c10060881980e5150b408a4410035013189501c4a103e606005440000000c1440c851b001540d03500140012000d8030586c180203141c08001c1a420850185040d01d21002205401c580246061540313540c19801003400e91080d600140e4100e5110001c02640f41041a8440d030401c0381600c144400598802c00c0010b4007042e551001c6584611250074000d6a01c200c0244880300e000548600d120503c40c60600010440030f00f01123401800e02c1c400160380c40c0525002458071945448085000d5150b60380e1900940c402004194006005d1201251580742003041d04061445000104054460350030142549007241c407540500316654507140710180d83c044d0a80b20034846601340803491600c05402040120255000303c3e0f04044035004102d2210380c014403e5990707205070300000d40c029440e40111429031040000d0181142420004a8001441c11640c00c0b59800450310f5038419a403282d46e2941000d049900c2 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 818625179 1250 818623929 818623931
    0xc0317090a02011b03020d08040f02040f022d030705090409080313051002040501020c0f01030219020705040e010605180c040b07150506180c0a020f070807030512120408031302090a 79
    0x20200442d42c00030304e0803400c101c80d440b60704019030096070000d50b1002c861405404024480c40820200201c036100e4a50341c6500800c04c0c404000d100d84400e0007504070384070034000900a110081d41c00e28014082c0e4003040580d999040c034680d030340481540d42e54000505540c204c0d43e111018800300d0146406503000312600000219101d04508005180c80741d05108849040d10400040281ba130300002e0f6640c0100040e40c2c2c900714035640b0f00c01a00280100e0310340c01100c0c60003203c2405081c2c0d000c41c40d581a160300b11410041403c810221074225543c0d0b00079140c01810a07403840724842d45540b0f100d03922500d01e41e0309903e49503d880c041d04140d0450003048881408603001c0a1850145015032680210140c034400701d02c004008141000c90341c003134000104900e0006441c04442c0c403c0c00030ba024004400221582c81da6070303001ca290b65446a200c01e8409001381c00c104000003002c1c10486003803003042044140d1135252611243d105600140407181d2210603000b400c8016162f112220f4800d80344414 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 818626429 1250 818625179 818625193
    0x80304020306010617060f1c1a01150e0f0f030a03030207210c02120f0f0c04140105010903120c3819021b19060c020703020f010c031709 60
    0xc1894508032040e0070410034841e038110001400300100e2000359000c1422200e111040800d0030109501e603500310087e45400102c0715645040c0141011a107500501c0f89001020300d0381d07242401c0141e98030308100200090355900c10160079142041401030140c0740100010140352445000070324180c042c005c101c020a0700803882c00b0a101d2803000340c42c844402c0055000d5501000640103080c20a10700000344101c01c020200c1850301407c0145004800e40c01c821540c403110024030701039030789070584800ca22903800c0000001c02d810103c00d10700d040740d00c10b0311049055400c41d5180c1c1c9030701241030040010400c00324175202c0801c2c907144120b1203142003019019141d0411016911250205400d001d00110016080c07000700245240700d0401010005401a150242407810303a1000c49000580540361080e81c9001006040c41a486070b51184600c0040000400c50181640c46030b41510029510070050101c518165006101204c003280c801d2800101040300045850b002180681d5405440d5100310b03 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 818627679 1250 818626429 818626433
    0x1008060603010b0604150e0402390c06030403140307050702010f020d092106020a02060f090a11060a03021e09010210090f060c09080a1101080c190503190207080304 72
    0x1220180d000314055000b400441c1100c40072415512035480780304d1140c0906807000030600c0c81413a80401004c00184155920515040940d2020383d07a101e694407022000c980040c0000311100d140f611002c00100544010b100142c20843c1a0300018019402d0080c0794041200907015000118800c024980724030ba00d4240314000100034480c0c54282c5020342d88410140011550018900000c6403581501c90301c4132817412082010b20300d90030344014071503400032034890038542c1c010401d60710511103507410444c0c50b0790380c00803d556051840d8010749083c0c00c15014010342e04080c401003501d401c00d81005854503c0382002200319040151399440100320100c0d801c07a441d80c0c18090322181d0f0542c140c1c140440516610f9040380c0c002c0c1c0100040c005991100320191080c001d503031000c003e1204200755243c000e020700b4026240c0c40550744a60000d8480780000e55214642402e6820104a20b000300701e07821001d501c03e403150703032000d00f01c031f030050344a010003000f80c2140b800280300403481010100d4417030a1034 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 818628929 1250 818627679 818627683
    0xa0c0b040302280b19060509010311150316050313140d140f041806050901061d011b0f050705030f1b030c180a060b070809030d030b030d08060a0803031008 68
    0x10b45042c0031000f040e007006004641200102900b155408412140303180c18500d9000c000d01d096030246070410041000042032002c000318058000d502038815602c450902061920280b1045484056829a01440f0b03014207210350003655100c040200707400760084254650012120009900d120705030b00c016100909241e0204641c1c0d40d14040742442410710b0300c501d10700358460080b4050000c01c1a40d601c07040711980c4164201c80c004240140006255503114030780145940c180c0b981c20b9000b0062104203061755403103440c0883c80d5120406090f0140c240c19503403042903081d45070b81600d40b407281e1000132a056900b030100d20800c1e060500201403050349480c00118030020941001e00c80d410223010160162100301c61a07180d500265004045591540c0050000b07003e250405000240b02007000300421111000800d6187c50842c11101d1101b00b03242c08509460320984001d0701a001182181c1407240100c0368141c10140c02025201066110700c0c0140c5560811503e0302e0344041c0002c0b08000d08031007 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 818630179 1250 818628929 818628973
    0x91202010b040c0912020607120513081c03180605071d0301090b161103040906031b0b0405121c03050f070809030708031f0b090f09010315020a0c0b040302 68
    0x8152018041c10003c000701400144240c07041c40042650361051a04569421080380d80c1e1a5101003a0740c1c12107164a07006041e034101c0038140143c14600354000c0349265001644010b5440300d10b00703241d02209050412406015110420f41016680c044c5110004015025040c4540102c0e41c4000c0c2d1080e0942407004144048a42c840c0643d14020843c80421b00001444d68070030512082590420340d8100e04403242a0680020f41d000c1c0408540131a40004940090b0101c0740103810151000f1801d10410400c1c0075280f040d40b8101204000422150a200103a4051000c48800751003d040d05101102d203071a020111400c00240e403541003100412a070244a03030040c03968070f44203d0900e8000442075891085100142110401000060051603a4807003034442c003110640744203540c5c0c2d40324803501550304600800b40c4540349990340101c150a20f4004c4034126504107406003880b030303c0009500300030b5000801e9481000400c03e94940810011682240150302ca03034010301100460030181440440 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 818631429 1250 818630179 818630201
    0x1120c02161e152a061a030a111504031b08390315010918050c040203071418040f1a0f0a090f060509010504020f04150c0609120201 58
    0x4490b011440702c8102d0301c045a05480f400040c0c0390195010190a603611030a0401507006400e4002000700c041e0102c54143d001e0710b03c108010b019000380414242205c07070a0050b9650940d00c030301400000304048860941480001401c40982141810306002072588260429149400f00446d48054900701501c203c0041c4520700160104035205644450030400c0a5842428000e044206120803020001450342d0560010104c800050f482d180300e400300002485180d150510307000300b810810810010802c80030364400c01510703242825204001c003d400c050070000801101890300510300c00180c0084c0340b52104070b9010302170500c2d62000c01080e201c580c20840c100d0741c1032024400641c004c1d01c000080d920700440b140250b0680c080c0c003180960300c3c250300810495080c0f1060140203402548504103981050f00d540743c1c47d0380c8a8003400140e00c03550814060a0404010400410403c0700042c0341c0d510051400300000f039040e17100e078800e40e200801e00343c84078a08030f0070b90040c1607024418007401e24 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 818632679 1250 818631429 818631449
    0x1b03051b040305030d050a0b1e01020f010509100e0106170304090506030703034a041d071e0b0f0c010b090c04060f03021b0a0309060504080705060901120c0216 70
    0x140c110b0b91125102d009480345d800c040781d150000b113180340240d03800c40c0d0503841c0c0142042d0402ca024001802c1d100224041141c090302800300051401c04040c0071341ca110f66065001814804031580240700100444804140d0556880340c0104000c0940c002a05070240c28000039512103041412850031140701400031446035010040820010350001518811401202c2200313007031116400017515a640c00e00721a8140003c007600c46010080a440d0400001000341e07010064103c1c511607041c10500d0b65483e250182d800b00c4400c009403138a401410044600520140300f40c1343d643d03245808160001610031804440c0070aa03114800424403c11514450407180e041705401c02045101561255008031010041c6c5680c45030031071402501111f4900810141c0317501101070454000f515203e40c80c0301100000c2038040c0000b060b40c410340648003550140340184c8a440c0c600301c00c001c0c16500c2803604a0500c01000d0120b42c19a03d14821142c0c00800b50300500b44141080c9405000c00d06150032054441e = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 818633929 1250 818632679 818632687
    0x302031e031306091a070917070302090a0e0a0b010b0403060b0f101b080c060f060909032712070e0a06060c08031b070606050301050f010e060d02041b03051b 69
    0x1c541030712141c100c00c82d001800080c0e000d40070f017000300da84505000c00100ca0301d00b1506005c4640ea000c80c18804a910248c00902100c8045103001d407142d509120203980a4041000700e0074100d00b541c469403804103c44215007600c00603030340e8444442c0e401d0b40007000c0e94001090800a011190203881d00d2000200e4900d17140c8068000081c1e00051402c500b0410045180c9100c002c00742d06c101800341140d04507141c00d4881700003c40440d5100000c072440115a6408004100c1909103002e00c180995200400346040142d101e2585400080400e2500e50710300c10201508010b4484091150001003504041c007116400c080352000800c4003d800148403514060303041007060750208002003a00d622001d460360742d445540e9011294140d00c81e01b605002000103101d400c2120f01e034030000454601741c00074011507640d00302038601e40400748141001d1007420340000d607880c546180000400303880100006aa002d45a1011209484c00c2400c580802d80d03900c28401000720390241010f800d001c1c2c180c09460 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 818635179 1250 818633929 818633941
    0x50114040f120905060d0e0c031203011202010512041a010803090a1a250506070914060d0e01051501020715210b0411090f0306250302090a030302031e03 67
    0x541102850040d24036402240e11410300ea200b901414004e0000030312040d101d0000a091000030225014203104a114004442499040105201c3ca07180200d03210340b4196841c05140e80112490310904030304000080200e080c1c0c01402c28019400b41d17009202c14070144134a00740d50800e140041e0881c0c0c003aa8000e01c452035050366000500c601b5250082c041c01c002000d4404c3c010120f006d4190105080805c03c02c841403003034a2820b003610b480c2c2c02101158019101c0e82d205a946189a009410106101c0300b45603c4c1802c000c00203040c5041000c0c40012008400303844142104c8007610109040c5680310031281c02e5603810440b840c080c01174414130703d14882c02000083c2c00d000c0c0c3c2000d03440b11041c40c0c038407200c00301c111a03200b014551406401480000e015003613590309548140710451244550300038044950900003001c0384139411012a0074024545503907041c2401504a00190030140c00704141c0341c054a0305a02c600007540701e130b001146c664441c000b04100140560040c02d000d000280100b003c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 818636429 1250 818635179 818635193
    0x3080a0201024e1f030503040b0304051207030504140607060f0507140909070f120e060f0112050d03180816110306071407062a110114060f06040503060a020705011404 73
    0x81c214604007030348070910200703041901000c04d46610241840c00049800240f100b81c100080d4030441c030401c1034805221821035844205d004a81010300018010b00c000c0c0041c00110701d003c88207020080a150429005a44020948072001c044091700c581700c0d8148100d0903044030101c056601540d54460134045510045503901800400c1c136803c1107004510b03000024000d141c1d03161744003011603040c003160444009a641d00c0e20250343c0d03032040704000800001c1400342c408070714005660090180c29489074001d4100c2c05002c8144e0030203000814904810700140303051001380481c054034210102c01e900c60b4100201f4040025426034000d0b0024020845119440901c034070140e545071030760325102c010508101c4024002c200b418612039034040000c0448403440356104c0701d20280360340c64540c0108044011403d0300c10b420b05101e0080ea00b00085081da18040010340898034000c3c100508241d031f1031000030301d0010309480010190b41d00294542c00c4c02003c0c040d040002201140121039420540da40c41 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 818637679 1250 818636429 818636431
    0x11070b0901170a0b18060a060507080304031d0a06020105010504110403150f0f230610020309150d05040308010f090c080c03130c1805011e03080a0201024e 68
    0x1000880c2c840001800fa11866103e9406510050038114074402d1042980710302c51419100c0b42e104028024000440511900894880355840304180d0309686a0303030b03016940000f2110740f034007100d04004041c10340703030700d0f80e02c0b80c8001420b0039800854554904018402202c10024405055030800c1100b48089100079070110725000500c0000500000030844800042502c0c0101c4101682448800c0c0c0c1c03640800303903104890600c003120302d1801c1d44607642000a03201051b0a10000b580043c040000380e0710b07041005a07181300e241c070076091038040000d0500c012510304840850101e22004d00611810342030b904142c0103001001c0080020a218100190000e40f0007440360448240c000001003890700411590f0010030350080d4840100e075252007102210900b20081c03114114508400000c80c8078184849840899100c0d0604030030301c1c1940c81b180450b500007184c1600f959020403441041c81036000f81120341c3da190038071034606498020b640348041220440f00e090060303440a40f4a10f07a640c4020341e6 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 818638929 1250 818637679 818637707
    0xa24110f030702010c03121b031d06150a0306020f04080f0c010203030c03040f02030f060610183803061206070e040527010506010206061807210c11070b0901 69
    0x4a10711700301910342214158082d0200c070551a0501c00224000107281d2251304201080b502c1c00d200b110014408407540191403070071075202d42d005201040c201c005c000c4d02140e032440041d000084e05501c9413216404c0c0c0e40f001d07034103c0a841c0000740c10400d02100b40704021a000001015200003003000c00003d44d6800080d02c03034500c8000020103d400c010800d00c3c4182d4030380c0e000d0300781d45407a000200383e981c9600c412507045000b000120f03140c11906208000342c961004503654070084150401030502852588000c10403608102c0000751303c120709880391800042c10f190441d650340d0349000c030140a10015401215412580301009004110381c02007040f00c00910140c8001410b990f920400d507030640c2c1d40405008003050329414002c2808019001140b1401003a000c441c42c075140c071001d00c001841d94000c0426101d40c000003081045124004006142c200d541c50400024065545101211084030018000c0303621b8441c06071100505201d010000d2144500362400d1244040010344000f4020301c039 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 818640179 1250 818638929 818638937
    0xd060e240906160903110d06090c05011202131511031b070b0307020c1003061d01050a080307170706090204062409062001090b0408070b0f240a24110f03070201 70
    0x1078003001f0388a0014080039180c000707206012040107030030050025149806002c2c00206040900c080200a03030084801d4000740c155641401440c0050040c0c240043c0c0f29980b00704a9140310307112655904001500b00348018280d088074400341c03140d52a2900f01e907075000c184c00c8c4c102402000300054021858a41440301500d01d10002004028121f000344015006404064421802c040342030301c80e81c840a0507284241d132580d11031515458115524042e000b0b000780209801202c81103042980009403032140c1c81010080b61004140c0d00180550b0203503004088140c3c0ca8080d4141d82c00c141d11030001100641d4200b4065450414000074106280d54036406074101c5210030b180c201540950041c0ca546801c14502e440030b00341482c01c010654801441514010000d00c08242d1201ca1800010301840c1c01500040182172282000010800b1240950758440d4003060000341009514043c00303902d0510038050310903c0d403c01409401c2c9040c1104c45c02c0503610180f0b5920b11078038000b04507001c00d03809083c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 818641429 1250 818640179 818640203
    0xe061009030609050c0901170118120f1e030e1614060c1510152a0501022b2009120f07030c06110109020d060e240906160903 55
    0x1005490211003101079038001b5000000040c642c25810b280604101c501350003484072144d0583d040701000f045440241030840220320b03ca0071540650140802001c19081100c4043c02c5034014541401443d2860000710740c9a4041208111082c00242004440482000c0d0790b1402d03d0032004c248400003440c0740c020f000004031019103800402903d0740c259901e00785d4088074504880d8090040c5c44501c00c000307850384149110340c8a5801403101d0001280c440340f110b91610b4000368285211000c1d084180c5565608001c04954008007000b40c00131034548004400c003403400106043c04507400751400c00d07120010302401105603400d03401103440d1440308070f50085c680e8003d008400e003812480300c0d600c05c0c180b1900000008009400c0340c040102c070b881d61212078500000015050a0b9031040e0700095009040d014081d002400307981c46440000e443c00308071014000d54924a0034041440018484180000410401011005c00031164071952841c00d24149034035400001e480c08500c1c3c0001401280c04039 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 818642679 1250 818641429 818641433
    0x12060609130e0106060206010f2115020d1e0204030203070e09030c0714010311090607030c140d03050610050a0203030703020309151f061107090e030d05010b03010e061009030609 78
    0x6480040008031048100010302d0038109080c001c2c1014422003003d03008000001030b01c1c50454081070216242850101003040701c240082c1c0d9070180070f5204655268100c9441c0d100e03171290303101809080300340400008003000c49015002c17507120414104681070303004202c180016140407803031404940301903608a0300c60f103e17164184c1c15130040034040e511031700c5800c01c001001c1e4000004886440003e0f02c0811881649c09030201061064842180e08260704200410000e0321444420207140d01500070140f203c541c50440b181020340701210580080d03141c40a000c05480c02e2142c0b41c0e09081c3c10305019282c00b440c3c40029441e800014039201c10f040d8003000044041e60184404413035442c002c0103907c3d02c0e01e400e140c04959003280140500010b08c90181c0420a94001d049408068031201e00078105a03152020400250080e05410b4040340410701c43c80034001c0050082c0d5000c2e00d1021b5110b9141d60400d000310940420040000f031280f00c3c00c1034041c1c01c0a8210021200b0f032a00403a0106a8603904c0c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 818643929 1250 818642679 818642689
    0x30f030a05091804260702090402010c020d12050405010201150e01030b0a0b04020706140f0714180d0c05130504150c02190308070201110306101112070b041712060609 73
    0x40c5600507140c3c400c2c8410407041200c440c1d02e046805c0e500300107040600d0900403094420340a0140c0094002c013880001c900507601900110702001e1004000da00d04220030b54822040c1c0074104002e2020580120b001d000c0e542e02801002403e40911000c01c0586281c40001c03030000e0410301c005008183c115010a410f0031243c1c00c0503e408030064010341d030301e030b642e45410002060788103c40c600008168021810781c4415181560142c3c601e030383e59000f00da81101400803a84d0010300039110300640c145916441d030b101d11001c010214050a6954122890030041c00f0000c581c211800803114a0001007000007800c6c900c580040c4800d0100c0007660704c00d09402640340c803c01400c441c0b901ea80c40c110b018105944511418403c62483d802071110341001c41e0048614001598080c2e4400707540143c0c0c0382c04034407501c2142c050100c2e0b00d0440c1d04c030320003206540780340e907020380340c1615885441c0301080107200c000b801130740c040e154804e24035140015114070003a0503100034088510401d0002180107482c0c3e90 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 818645179 1250 818643929 818643949
    0xb0c030c0102041e12020904020906210a030206102d05061c1104030503070809010c0f0b1b030601020a0308060a0b0c030309070803070c170312010e070e030f030a0509 73
    0x200000719610350710780d040d04066001c10042e404c001156441c01151035000a10641d20141d8081d020000380d445030760800c005180000d200340e4001c516030134689680c00e1002005044241c07504094001c12140d030074001e041400050000d0490050a03008011801007070100030b10100605c0b80d40250b10b01c15031400d10841e1b64644c04554440000305aa9046103180003d8914100000e24104015013950072001c030075000303502c80a40a90000c2c04004041110f002c028240c28405140c0840d00c0d0300e07255200d1182c0c070020b510688aa03559401044107000c04a08402c041404110300c140c11440c2030720000b90380c1e43c0403000080c10072580e84041001521030042d000080d00c0b13180242c540360803500c2225580d0360001c5074411101c0c4600200000d01601c040120744129030019441700c3d00a080c800f4022035031000d8885042103100400900b01c0300400c0e0503c59010f855030a10341074030303814001c1d0005d05080c406a5514840d401c100c030340c44449100002150203800460400545442c0504c00098000c09 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 818646429 1250 818645179 818645197
    0x12090a09050903030a0e0d0f030207050f070605070b0a0504080318010b0303161e020604030b1003060c0309030f020606010f030b01030b13090308280905010e0706110f0a0c0b0c03 78
    0x1041c982444807000020000e14401c1e01641400c200c0c83c400c03681b846030748000542e102e501003000869010704152080d0010b0200600810494081c42c08959481307142c0080340c2e002400103403012981c4003c2042c07608200d5044104004140001d0505480f0050350f44405000d10315140c5129501c42c524a0b42074001100001c0000d064a40b00c199662006103540302844046582644024880c290b614010f0004451260007509050030241540d031215840391024000c0126444049800400680140500c900f80c09042d64081064841c500d4003a002c1c42c0d5005011041d50008410804281d0b4814660890380d80356140200310840b590005800500c00d2001040d000110034031000000c84051308801a03c622a80d50485643d5800b41d56010101c40300c841c003c024070041c41d0390814814941c000314055800380b03000255048210410070302d05003940c2d0000b40070030203d4090340c84144060201180314440400900724017651039854005040c42c0c5e0080c090410008034804101400400a0b961051 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 818647679 1250 818646429 818646431
    0x131b03030e36101d060d02010504030501090c051320030604060302090a06080f0d0912020109050612150402122d090303150f01021005150607111003020a0212090a09 72
    0x148034200c107240300030380c101c81070340c0c4015900d2070016060007008000b101c3c45842c13022294207500c9690410011030000902030b410003100348008408900e0a20981c055036100300c901e131807401e00d4030051014000c40904d288030614641409001040074075079402c0071072800301140315a03e035503040c001001400540c102030740050080041000c0183e49a1003041a075602c102140e010014052090f5611360741e0401030800601d1000040045400402481407414030504100c1c401c00e48a6022500a07001203ca0039041c00d83c0d482805026804400d06910210058609500d00030940d001940c110701c003d0070600656106095041d01045460000c004040300d4150a012500740350703c01c0c940e6504160744c107820313004003181c940c81d0514000d03903000312180068000e40341c1d000c00009948011b100003000150342c0c4c0900042c00045030344400c020107040e0f120f030307c0e40961070700544140300b80c041d0709010881c1450b10400054203150340004503501c0019030009600d9540400c00d0101d40041c5940e0b004840039 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 818648929 1250 818647679 818647759
    0x1a030a0e030c0f010609090503090405061c140c04060b04060c151a101b080c0a0b04140c0603070801092d020a020111040e1b0c0615030d08310b131b03030e 68
    0x482840d9207848116200111556540b10004000445034b043c440c0304080e41d010001008134a0065003852480c43c0910010081010f040c074140c1c0c20303a48106803e00200d40300c21034038410fa18203400c030314108545628108a0300400c980745040010742105000c1d0504d500404d014020440030030401856030f03401101c0d00f5241c0ac03e45410202d0003480385000d0300501960245802c01d04014003034910400650742c034844281d1800700a00c00a2103500128180380720315103885d4681d07502d940624820f10514240050b5140014038000b42142d806d200d15152000c0304020801c440c0403d01220741d000100704818488489000d02404814070030300040035054002d017002c1100c1c0c9104042c00301204107042c0c05031a00c04c1d0303d6100856101c881210b0a40715004d4041e91713240080c14091050703074841006e020b00da10290058a8005106808440400e06121105001d03010030441d070f2001800200b603c0c0480c80007130308540c2c000d044480343c11001e2b030040301d50000c0c95081c260140410860004205010200 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 818650179 1250 818648929 818648933
    0x513021905120c0702060906030411030601260309030a14031c0f060b0304030207211403091504030c0308070804050904030f02010c091a030a0e030c0f010609090503090405061c 77
    0x40c40d000b0510041c040d030450000500c2421400044034140c55004020900d04013140080150940020b8025141e1000d504418415900c040100314040c040b804041d8020340400701101104500010141c42e4940060007001da19460003c0e041d803095602c03001031010843c10421452541c014100500d2141840312071161105040c1e40c452004144191018801580c03240f1100c04a84400e803070040060303008210070040700e020403110308062540421003c40e12100e83d00c9007044078031501070146503a0400a40d0300618075026107900c2130103408540b242e041c949551034080b00408580f04c06014100b00044401c00c105843c1e0484001d098010117020031410507090062018045501d07080166180207001c0756141d000f074010320102d90080c07001842148008004200f16080604150820f548600d408d00002c24140003618503003004030300510b03580c0205105036096403915440041d80e0b600d030680e06030100340c001c411600340e60b900361004601600d88002180031004040c1d8941d01304400981e408007 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 818651429 1250 818650179 818650187
    0x6090411160305040e060a180b01050c010f061502240615041e05041b121b0f090909081204020d060612021809150c0c0619230105130219 60
    0x1300f641c0c0160100321542da10b403820302090000314096080304603650f01080c0d056850903042400880b506141860410b81450300441c00c5d609048180e00665455030418814040038071850b00f40c1401070b2005207003e0400103042c200b4004c01c403801c000c022007800006101502e03a00080d00a0400986125a48664408a2000d088840040c00031401041000001e29103080c0c0a08e54000229040022280350220000d803182d61540c96402520f41d1590005030304006000c0c1350100d4800c840c0c444c607d0101ca1840300500c120710a400c6049200c1c50103070000003051440e02641c913244160320311144592100d00010303500c49d0003d10000c02f514104900131410300d48840200307000510036581884403d01102d00500c905204407501c5203d503000b03006683e15036216802c0c0325001007400220740d1601c9007000c045801c2c080c046030040764400d81401408005495481004041303a031030040b021424440c100f00c8602004103100c1d0038881e0103048101124840503504031030340c40c11800d11580b1001c582001c054 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 818652679 1250 818651429 818651437
    0x512071511161d0a2d11070b160507111005120103050f0c0a0e04171902010204031103010507140307140c0106050f010f2304030609050f100b06090411160305 69
    0x4900c2000c03410104651690764000c40c5d00c907040c061258508680c01e5502d0101d402c0b071110342540c119894010400d1032001086c010241e00d8090703210904a0724081a1090208c880c1000c081e0811604104c02000f06107620080720318060101e41c5110044150001200c0d5401411502c0250b44004800003040007000510f0080011984041ea00c01c882035030f0400054200a1049001d0740d01d02400003400100d900c1103604228138849030289c02c1002e4181c0030400007106484071005070b9400038081c0b003400586646103030180001c41c000c1c052454288002812b03c02d00c00710417071080c0004004100d019000702500510510900c4030642c48050300342c400d03400390800c1c1c401e0a00580c0d00c03000d0112694030800e4086800243d40d150701c0144032000c2d0f001e40c480c01c80d20b014209513502c144008800220302c1d00412813103901079001032100607090f4031f50300c0c01c0072040125002201d182030082601501d030340c03082d03903c0b003c811140000d64902892109503d40f140701840d8040c0d80c1462500020190090094 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 818653929 1250 818652679 818652719
    0x4020105040503032a0706050d05090703080c0c0102070e01050303090d1401090609141216080f0a021501091505090426120f061507020301060915051207151116 70
    0x201d01729003070b0385c003090b211012805400d002490400941244c0740c819040a40c10126201c1110340655030390b00c1d80c0400e42c003c00804200d5420450060001d9a41041010b000d0300d080d80c489109549000c0000b079680c422a000603003d581040b500005220180f0038601c80c0b003c41e40003c2c41708428605e4401d00820040c03004849101101107644046100092108074098020741010b14082416540708030703c1c0c1c03c1c500201e40d0613004001080c81d82081c40050842898030740c008015070300319038406182696058020b0b20043e45000218600e208500d0a20800c0381c0047e90b083d031540d203039800c15050390580820703009005d0403541800284c0e6101c000c01413402c01c1d4881684052901d48101c101040342003611160352041c0501a000104a0304c4001880568401000000c9965076450201b040d900d02d000d8038a861410a0010031650510b00b010841010b0b1003c00360800781e050000c0707a0072401d10b40d58407400b00110a0032081d201c040801075401410303081440d0700302e555554540401c60070020140d07 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 818655179 1250 818653929 818653987
    0x3150e011404050303130c050d0308060108160815011707050304050d110601030209070309300801030228030b01082a0901150207180c020f150406050402010504050303 73
    0x801244100804001d80a940d102d405146561641e1050f400b084403144016541c0200d08080061070b642d402c284020118841e8503040801d140c40000907001c420000d0628a4a008500d201100540d0245182e03601c110f00c1520100d00b90754200040780c0701d41c09a00f0039401d203401d520030b2004094010703010b1881640b240c0c040342d5182200311421248105140700e000a43d40c0310000500040c0340800e0030552011523440d0011b0340707051035201c4128000d1915200d00161040004060508101c4818259500114104131b29154510b6000c82d0060f10075910306400154140390181c00100c901080c8001580c01141d280c015503100c2061907100c0e0300c40410795910040d107507011480d2004000794540090741c0201326aa0aa01c1c1080140032802d110700100b085003c0c490010410b0034402d51401d80c95084040002213003212480c010b854540c940152485991107448050451343d2042d13032299209a00007000304803030311144016912402642c110b6039243c0070118079000a48045030728500389a401d001 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 818656429 1250 818655179 818655191
    0x11070807140d1b0303091a1807151209020f091f05040c0e010c02040e010e06010515042403020706020417010f0209150c0c0307030b09062d0402030703150e01 69
    0x50140c0d0080100c031030b5440300f00b8900d28074030040b0b4040d9000c092810f0060720600d52500e215880c1d04603085080310309500403042c41c02003e0301d00f10104200d002074001d03d02065940c0c655210041d041405480380704000d039132500c1b01d400454488480384800990042c0c0008001d04004900c0044500d030311a5070040758210840000eaa8a464042c1050003913280e11926500414403004503a080d03140031090707070040e03111084284052024031556020500c0c520241505506183c00c001c0c2d4001d512503c800350500600060182003441440308401364040e44801e8000072030b580c5d00ba4068015403001501481c13010a001445200d503c0b155000c1d118a5802000b00030201d803103440483c0185004140c0100c1d90f4a0392951a0100c074009000d8020010226640151580c00103451304d0600d8008942200d41c5005111940604200311501b00031241102e203025040f80e5580c454400c100d000382042d40c0b000758081025520b05005d10000b4540206034a00d0302d01c3c450020802030a980150105d5941c039102e = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 818657679 1250 818656429 818656453
    0xc090609092520030412020f0d020312071e0b07080a06030b0c0316031e0209060d0501091d07140d06020910030e0d020106120b060307084c1107080714 66
    0x4c0126000e031504404100010700043d02407106510320204042e07001002402120301598040107a5181d036002504120b5848a8030b00c4c2009018004881480942d01d407a1418000640481041e40c4e2001c041e14101340e4951b0f40a99440c05040d19600c01f815400045090082c2e0503403a400640c41303881c0c002c0030040c200854400840480b081c29000015441c46e060903111030b0b540301d03001840411402404281007040000007801203d001b0303802076503c80d42e00e444501a11305004018080808917034040c141040c540804502c0c0040c0e825452442000410250400c02001c1c4d8142c4416101c007504200380340c401c040d400390060200350000031491188001c80c6280a00c140a000c046c0c9800216000c13030190141d8a410160300042d1260780d01d401741c5440490030b8441081a034101e00301031140110f55400d180896044220007c5004503c0c102d0319104079401c401d840c00890103d8400d84000902c41100f406c1400c0034025018020800000001c000042c0140540c3e07404180c442001a00c582e00240 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 818658929 1250 818657679 818657683
    0xd0f050f25050c030d06290c120d06030b2a090a03120c080f0403020f18070c0204150b030f060409210302040b04080d080c090609092520 60
    0x201180582040301e0440031140344a03030040c00c41101060704403402c0000c2d00b01c00400740c44d060f0700160210600c441c02d400035a40801042a00350301d46800b0207152005462010340c07074855038601e8100901001504c0001c031081d0f80e20250040d40c00010b03040c42800c2c11280040110442c2a40e0b02003640c4e84403051898482641c2110703401c400060241d503031185941d886002081151480030f05002c42041e8503004600d440300140380780e01c800788405982d64154410018294007401c696401041214440010600010105a0800764604100c10000405e10018000d0300c2c200c0c021031821500c0104c00103260046502440c01007002504c40300580d0340345000e01040710003540014003000d00d140740e50704409801d0340e200210118903240c00740ca400d4590b80d0032045ca50007580008003c1d403110400c43c4096a0200c003183d0400b49031100c0501e00001000054864040c01005c0391080102c000807a29200c04440316082c08010034910090552852070087c100c0d0000782a01245e000c40320380ca42011140c0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 818660179 1250 818658929 818658961
    0x70203120c03100317070b071808060106050403260d0e072112020106120f060b01021b13020d0c080f130c0b0a030b0a0e060a120f08030c0d0f050f 64
    0x51a00f0703491840e1031a2502c801c289000510203003101c00401c0402e001c00c80034080c0620403000ca8464112500d400b4203e015030390300d2540a0840313a0061700c014012306507c0400c680490760030005e1010000f00503041035840d41c0040c1c1c401190380714002401c0f44040384c1500110002c003901001c1d943c00c00d690703400c4889040e0300b08c078016031905000080c040005105100c03a815040c00d070320001960703076190f24001c0d40e0002100c078240e03031800c9440840380070000300d801522200c01d0700b840075001a80b20020070011240030721401d07a00c101c0c2980103c0000e102c040d41a20740d5130640450512800e405890b028003044820f40b412041a0203260000710714041b41c0070603401c1c15500c04d01c00c0b59007518103420701d100782c0c004a41c41410151030740c01841240d9112000c00014007a6206031603043d00f0b200082200520440d0b004d0300b0031189814441000c03d62a5500a881c103400002ea41d9882c1d59503040041c0a104580f00405517a1501e907419001072565030111f40b0907500500011010f03200d0581a880d0041 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 818661429 1250 818660179 818660191
    0x105010318020d080a11060708060a081609021e0409050105031c0f121113080601060306120803040c030206030a020304020907030506060912071d1f050d030f1403070203120c03 77
    0x7003034101c0c0000b13050000615810a10345484005d5003941080c003801c2041c00c2d508c1d800002c2580080c00403610300350240a00400740d0400500094201042d1007200003882e1081040f0b959007c1070804500c0f00c4d480005020717412078100c0d5541ca64455444400400d400c1c081c950007807103035000d020041d0004002141d0101d0558440340544054108100d9107400c42e030751500d20140d00c03480c1d03480c28800d4080141c00100c40c40414082d08a042607003452610b10140d00c22001c160800305c00b0802241d001451424203030f00010001e0317981e602da0420b5031008095900003508050004208198650383c0d5018500440c800c6a420320365884070003045080d40c80544145034002001c00aa03102485c1511000c98440108001e49113140d58802102c59505401203581e0300d1a03503c0e0b010803142e81c504015903c0c250301c1ca4628848180d081c40085203070318580c0701b0b004017401120320b07030030b40c0860080c06c0561200015500c0d070f41d940d14240702e009480c1e41207103240c01c100603d02c0340850b01d0541d4070001e8078030440e = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 818662679 1250 818661429 818661439
    0xf010612110906280b0a0201020702130618110903070b07060c03201c0c180b2d0418020703080a05010503030a120209030106030f0516063c08010501031802 68
    0x1160003860030a0100b5130341d4800c681c42c0d00f20360001640e005040003030b02d07114503a60001602c41d50580140302210f5820361540000600c2d10205200708268084e08080c1981c0102001503072230503103042d40c4a580b0462402d02d81c50f11a4010005045000380300030312207603100e85824403515050386410b0b0f041c8d440c0c01040740c0701c80c059200002c444200c0440034001e0303c8607884000d90b8030009814248101c4100191420000c1e40d0340705051812142400e24000501d1107500d814a40464000d15a2200c8090381c486038031811001484091401844250f4011300200107150001d5004194842d000f541b00c110304401140e5000f001580c21206807049034101c0e01d02501079450121440e00498171841004800da0000ea07080c0102025510240300e0040a140300d44404044d0b412503060a0385040d091034a483c1d41c40810781d10a0042d070342e00c420511000b0101d08003544d581d460b2a0540c1d06134940982c41c00e138a000082156560301da9000070f0140c1254001e0324100884c1039004168001c000742420b02075000707 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 818663929 1250 818662679 818662699
    0xd050406050315010c0f0303150b0c060a0902150f072a090e2401080f0d0207060c02010e04090c06030b060f07080a110a03020312100303200f010612110906 68
    0x1646194410f5541c40c005140c2507101e4034055a0b05034190309a280203a00103541d6180021115140d461a400946058040c1c00e04110a0071030a980d42d040003070400c60250b48076400d40e42151100340700c1400c4610100c01850319800020a10b540c15005000107507940840082d550014140002101310f1034025154148007050a00402101501c140003d03c0b0b0341b0720500740e00d401c9040100c04002c0410290722903c1407a5450004c0c03c074501140c1c010420461b0304881002c2d452290000313010b41c210765190901c02c142d040c00c0c0c0010703541030f2a00c130b80c1182c2050405500004104220000c034068841c580c50411000300f00c070003800980d00a10203c1070010700300b04001808640b994005d0320000c4018034107200c41d2094414200d00b084954401103003d6440440c1484000c160a00c40c5a40300b142c210140c0441d510b5510014590303105c00c0108011003459030700e108241d0006210102648042d01c000380209a5200741342503400f403810106035000802c03440703900b20514211140c1ca0203a84000d01c1080c003 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 818665179 1250 818663929 818663941
    0x20405100816360b0a0201020c0609010c17060a05060a050c0d23091908060a0b041e05070314070f0206060a0b190306050d080304060e06040c09020a030902090903030106020d0504060503 81
    0x100c4011107241030038043c2c0000c00090814080703801800d0750300c096400540c5400d20350016928080d8040c1100842d40d041c18200c40015074030001e0401d03000400c0c0101100d035101c0c2004a4542126504941e0b0002c41c0050940c01c03c903086001840c0d186410822100540c2441200b15807007403400360f80e40c81c03480710001e1100e148a2804098920448010070b10103401c1c00d005d24000070880b080e88403081c41d80043c020060a40300c0c9205103081d0354010303203003441408021004c0c007403198042e0800740b01c0749548002041d41188240e2101c429040060750034041401d081101400103050403982400502c100c50002e1f03041e09041190100701c13500b4100f0700782030000c400d002c190540d050000420402d0b6482d400003446a03602c20300f49004a025910065603404e00d820000c05980294005216a5001009020015503a055003c0c101c5900710001a103e080103101200902010300010398049030310380c01d0021304600403005504840040d0201ca50001c501c820a036035501551083d03002050381032000403a = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 818666429 1250 818665179 818665247
    0x723070320182a090f09040f020d060b0f18151c0b190b010207061d060f18120c0126070309020f1203090d0501020405100816 55
    0x401c024014101c0b806207103440318100d030034003048070100118441001e10003031080035085081468891842002c3c54102414046010818070307003419800f8130260000241400380180702140c0c881c1e4001d080500c40c0c405424404064030043c0d5006200741020801c0260528185102c03440c10504201440704075550098042d4805014449450f080f050350070041c07a060302c2e540d1945e51080c5c0700d00014103031402d105416003109101d4103100624185082c460f018181c1c1c00082c40310490300c032880c1c042011100d040d00b5100600202d9004c54221034003107030380e1416150141c0070b0714040d41d1558035224010b8841c400c0218400803c1c907003440d2500000060b084d00c1d4410303042070190504030580300c2944400305107110304400c001c89075100000c0c1c3d945110021841d040c0c0e0042c0300e4080403128130031020514420700380c0f240b00d1a04000d21a094038650300f401c00c5000c2d01910005c1900409050b9060104040685540070868034110303035180c10072401d20118080e1001190000040c03210a000300070640d00c8d44 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 818667679 1250 818666429 818666483
    0xd110c16140109150201110a0221161104020c010207030305011503050103020a060503072a030801051009120c0e040f0c05150d020705070e011d1b09220207230703 71
    0x3c46d5200c542015440070000700420700521a0f174000c0c038003e080703036174200001d440e29034089041027001c1010b00440006052902062900031a06d9000c003030388000000c0080c440c0700c1c00301c2c800754008950f81041c0747e010f0380054101c60240b04d135054044a01201101164130900000758410080783c01442443d120b00d000d180d001031141007a64141c40c003c041420148240c0340f400c0348101405164204056002000ca80104000d481c00c041340c0001d00c2003d0403244141c040c0540901d401c01c07910b001e200000c58000b00800c8041140501401c043c1016500050b0014050700c224210a82c0050a070521240c08a1600c00881d401402c00c0c49044129020b54046042640d541c81020404525403852513001802401200e818041c040c110031180c81120f03800404c0d034000c1141c0511300c0240e03680e840c0300701c0c1c2207102c2c212004441000f510001d1620406042d01e501281840894030800b00309540303642d000700b4858220b000d1904801d20100c550f4403071042c04020440c0c21401a294444c0308001414 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 818668929 1250 818667679 818667719
    0x50d0f08131e03030f1505030c1e0d030207030209010b0c0f0a1703060f0916020c030601080c090601270303090e060a0902030a06092a0f140d110c16140109 68
    0x706516083c100c1c88419240c2d1850107a10150781d1040800075490304000c0b064009000b900c00000240c40303590201c058ad07040050f2107004034008444402010310911030400650340c010007200799546c4481c0c074407007a50802ea04030074852250644400b841000003034004041648203c0f2240f80104078081c1c036000d03400c00307048a6000840803c0d162b13180d5032900300c690700c950045008240d100411880003403500c0030005a241c041d4001c100144552035001c9403c15180c1070903031b0410f019454110040310301d44016141c030248840f2020340f001e04848014a4101100e000c0c0c0d4951030520b0325030880041c08801610406d50050540504200883ca9a0003a55002513159000100d40b641e50340c088059410340b2818500e00c0008030090800e400e000300450030014424540b00306540c2c0401800350103001201a0502a00b00108030341c4503110954010400568190b51103917100c4901a00c0d040d0745a130031051a420040081401140b82401c900108903010340594620b54a98584050722480454103401 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 818670179 1250 818668929 818668931
    0xf091a180d030c020406120215070201020a0c061112040b090f03030c03040305070315060b041202030a06110306100e01020d11010209060f030a200f0306030703050d0f08131e0303 78
    0x8100025994108118070207406611441412880b0703104020071113900307402820320b40c071903d203a40d00961544420300e2840782d410100907a5a070034500060385007094000e00282480811240403c00369030200d00f031610f09151504484100d10012a0b00c2070313038007441c0a0b500481e03005103c140385614160701004040c0901405032444d003400301d05118150381c419002500d03a075118013010010400d484000d0403145c00030716410000e0900744440004944528444d503211035903540c80700c0d01076545c180150100305520050422528039050039030f00e00c2c6e40044618910a001a00000101c54020501c0301701c0c80070140e02401c00b17403840003c2503402c40d0341254008029075090010b60120b03240c0a00600c81480210038940d12861300c08a010181c0f66070706102c81000744401d108001021032038096400d215031108000791651380c2e00001c41d240603820345c806031603449901d10b0180190b8216108880c01032142c1d40344001581c8929500103443c8000000505008084402081e40d4070036684240c800341c4a80b038 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 818671429 1250 818670179 818670217
    0x10b0117040c0b2106040c0207050d0c091d060a0b240706020a090f091a010c0809130c03060501180608041a100617060a050f0103060803070803070f091a 67
    0x10001100d500044c5400f4030008011210803104220a001c199100104a5082c0404007140e07500039221140c612419026200310300c0841e042000f0f01404001034040c400e01000f0341028080c180121100a424440c0d540c00b03481c01040361a40c29000c0c0703001103c0050800400403203150800800d00300000007003001c542c400e00030100003418a000500420f020ba81c0c51070002e0f800d103a4400c210078110743c440c2d0340e0340f89403003a403c81881180e481c0311080e0509083c4442e0619441c1000100c2e03100d00300c41c41da440040881a09011a05640f125061801541c1c04000b440d03112001516841c0002025076400f8400c4070080200520078248a5446445103586605640f41e42d03c994024000071b07101c01000320b000c07840074809103034805100414503051040140982c200348010405950361400360a002e2080b85d44205040d900a801c840000e012040490380e0308d51050130010407a1700159081400070350420a100350041c443d40c08941a558840116a03103038403400b070a01102d0b80002c412100182001c0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 818672679 1250 818671429 818671439
    0x302010e041116120c050c0f01090506070303090b0a0603081b071d01090c080f040f0204060b041403120a02281202030c01111801030f0f02030103080a030c02010b0117040c 75
    0x11000d00f450b01404081c01c00c548141c1d151a0249880d004416410400c004841c0408504002020f0610788000e584044044610300d004075800c0724290041508040c0c00a982001c141d0705a00424a00740190791a041d0340d1160044201038484904c000f8022842c14810003040300180c025440024094408075080a0750300c2e50b5041303e6021030031030700c200c482c16003004003e883c481c0c2c0501f059504031440c241c5414a00381d003140f4010031300a0000b50501d050070802d0000c43d00c1701e034003e00141404c0343c0544e855542d20740644000540f800da4440c0240184c40140c00c924481100b035800c410314540240500d00b8034822001d50b1141d0030a21210645c070311144000114030b1401108100180170341c0550303a81c0c0081e041283c00d5a06c421052902c0181c100b000c240180020f0440224050091901141d6a07150400400240501103c500c01003480007000000b040080c8004158100c0591030030300000100b84c1e400d90881c1c159021680c0440c040455010042d1100400710394094800d061512089440b0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 818673929 1250 818672679 818672711
    0xf14040e010303080415020405010f051b030d1505030706021f0f050c07030314040201081603020c240a060e1803120703060602010e0f152508060f010302070c0302010e04 74
    0x80c2e10680c0842c054074140401d0001151004080076101c5d4010b6281c0351a0200003484040c11107600010404081101048a0030b9452440104100602244e46400f01c1c012148024008622200050034121400140600f070214000d03044405680180506800301e0b100180070070a5410f282c20419039400200c080c00215229070350140324007452458441006141c0038080b80c1c2c01100c010b404180030410000141c3c1e008070515404000361400c0c401c4071011f00000c1e000307400f40c0340690702c01340203051110784100300940b404220079003400c42d00100d5440e151030340c100304c940d00d00421001c000d1500c001210340c1c0800c1c8802c0700b00d44211040324a010220b42c59424940340c142e40c590700190310b41204105096090040c030411f800d411028120403410010201d07a100320b070380c01680106007120005140509248030030a110301450740580c540b003201100043c480c03003080ba030191041802a900d0480e0394400c0c030a90300b019038001c0b01c40c40468123580056401a0210a0035a402500c800d0304852207048 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 818675179 1250 818673929 818673931
    0x302070f120e0f06030621071703030a060b031302040911041d06070f08040b060d0b0f09120c0307240207080d060b0f030a0c17091509030a0f14040e 65
    0x115659074107142c00b02c0410001200400c1c80e00071320401003071041c0102545c8400c540005560861005405003a0020304035003000e030940e00c05104090500d249201e1042c01000561081c42c2c1040e04201052701c414482e038950005172018080e552040300ca0314010704080d032001c04947e0044100008a03c42c0e2000241524100c0740807c50050340045144c00d054000c00c09a5007042e66070503d146103042c0c41c4002441c1c4c9400400207484d40f21042c001c82c102e82c4500d40100240c603082408130b0710502c0c0c02c10900c0301c408400e4500810512410780724004503003108060302c0900f1134110140d4540101c9031180120130003103000704500040303940b00c00d40c88041144000c1c645144190740c0d042c0c40300b50a000c20011580150300082c60410200300030040100f4850480e0f40c4009034942c006090420300c90111188007401c0d101001040510041c400031400000310801100010203490510390b030b41c4030096440c3e005900c00c4402140d5003a00002c8406c1c001c1400c0103101d00c8500006061607500c140140013044 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 818676429 1250 818675179 818675213
    0x20706050a1d010b0607081b1e0d0c0b040f060b03010e0c03010f05060f12010603061406031b060f0d0905120703080106030509061b0910030506030705040614010302070f 74
    0xa0356002240e0010304a10344024581500302c001c1015044480c0411414800c200c4001d10082c00040c6007148450805541d509080c9950100d680b0046000504284103905641d8110700c0d1007800b0810310503600c144811030116920030910159515140c4e5605e841205800c0d088801c2500c41500e500d07240c40c2481103418280e041001000070318804010b250031140154014040941800104040e40d20760301a0035103c002c054034403d00f54426200c20302c0c0100400d41004100078203201c1c80050f0700f54188007260155004800351000790790a1f0440b401420a0100e481c0c0d0040700c02d00c110f03440f40401201601c43c03810040e001080c03182556a40a0902080070389240d007943c00450b80c42c0905d50300440e4180500640c1c1000c02050806207211607483c6401000c101095098030b070300c07103200300b90a42030740d035044000303441c00ba404400e4240c060064a021158140203104e0020006a03900d003c0c080c003011500d030622990b42551202004401035480740c0020f0760380c1c2e4608000c10300010003017100d200c0014 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 818677679 1250 818676429 818676431
    0x60c02011403090a03050c191b140604141f0801050a060804030c0201031d060406060e01051909050a1410210809100c081801031107110904111905090f09070e0604020706050a 76
    0x210442010300000300c043d003261484ac8600d888182076501da030300c00ca40c01d44a01ca55100500c41c120400a907426001850b5809035820001c0301c5601300e40c1240080e81030f200111601c1c0c10003a1105030454035840e00f10307800b400060307000f0310200140d4065480705030381c0d07811040c0c1c009590035032104851420505580840c1c2a80d914402048848503002d06a4050401254034002041100030503406691035400380319803480d510700c045113108050340d01800c50502d110000103510301e4010200c84140700035100b0a500340c0d01000c2e000c0f00d14000b0344d54403180258003512450800f0403000a10000092a01c2540180708105d81d4071804680c65101505101e1007503481320740341e040d580b000101a940345500f000d8401d01d00b8400240080c0d0700f02c024a210f40b400f6240b0348100c0e074450810100c40d5503802550360300305c40b94400b156180c0444400700b4050703d40030340315060541c851070300c61610a0000c44110800380c000310001d11003088120111900008010005401c00503d9118401110010340d0529002 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 818678929 1250 818677679 818677703
    0x9120406180e042a0b18190e070f020106050d0f0209013c0506070506100b030408030c160c09090303110408150408070b070f020d14090609040213060c02011403090a03050c19 76
    0x5850300c7d202c070022840d41c0081555441d40340c2002c5884080000e4105e009100d0011061103600c3e00c04d500c01c0005007070007082001e2401c103505000310628100e800a074085c070810b100105d04411240c0102810580c0c00b588441c11811140100c0c0c00b8016005203007400307084003070000805039900b07030250021030301580c003a00c0b95050048aa84042c411944034041c800d00c14010040840c0041c42580d40c00b011620009955112014690b100c504110070000d0050180903004650821030307a020100c501d119440411000d03005151125050046101e20a07040e4804040a07150900c0d83c1c0d130b404c0c0c2140c0704805403824012250380e03445140700300300e030346400185d20404500e402a504000c161440400c9007060703440402400321480043c07107554075090158500003075024098841d030341220311842c8101c0c00c4114180e16480300520081d450742043e0b000490803075201d8582d0200000310783c003030a0302d54003c160645182d501502e1640003001e48041601600b0100d0381c5141101d000b02e10300c0ba02c650700d20700704 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 818680179 1250 818678929 818678977
    0x209030a1b150e010c020f0f090a0203010f08010b061902071d10050909060402120f0a1b320a050d05010e0f010207050a020909120406180e042a0b 64
    0x1c414080c20b042e00b0401422502d100d540d801c05080700102da016140c81180c440c00402003440a48280081138010750b082c02044042c03a40365002d503040c2c40c4501c456100c1542d071080217034240c841010041e603203c0c1c8100200b210090b850014041c1003445801940c403015070b1a00b282010540035000e0118450154080024a030b003030f050760078064182110076021030705002c00340d5a9101d90080c002405552212600001c200e010000d08407680700c0c0d8004c40c3c541410034900401e450b07045801c102c6151050b83c03001315001c2405042d400d084221409622141c400f0f4011400c2c600344444290394020f00c43c1e00000c20a03854603910440c44c01d00401c00802d0311442040f246280c0760345074034a03511503441800356400080000c00e60210181c0c0403a84505162510802035007040341c035480e8401880000034001541d00d80043c0e0507010324400c81c0f48901925914900c00d648402c084400510208004e2050f40100a40c05694400741041403c265074941d02c80403501e40781d5000502d00000b584d280c01100c04 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 818681429 1250 818680179 818680199
    0xc04230901061415121503160e011403060c0d0f0f020a0801061b030e0f060c0a0507050a03030e090703090816061109010f0f05091017160905040209030a1b 68
    0x840f001042c1c400c0d12215942030244400c9001d1540055003104818003c12241030400c80006100303400102580e503184405904a15075008500c00d90340403081e41000042c040d00f82854400a100700a0082c00d01c60b83c441070504000d601564055145a90315031500075500100d104044480743c00380c10044c1c0d1345081407406841c0e01030503400201081107817501a5580d121301c1c03403000d00d82c1d43e05040c0040a1131003800080c810580c0b5802c0c15421000124203158011400500350f2201c50085050710366181e20340040c004800e040c0c0c000a00400c54541c8d410481c2d06200341c01ca5400001c3c0c0c83d00140c10f520942d0f400c02c142d803041200e11242c01032014040240038003031048003690004000c415140180030f000203040c0c4503220040c4418081c0c0700443d640e016005c2e6086400407400140414000046164060018803959200041143c0e0840028440300410b4040d050a06000d44078040406c1c50b10301000b000e0b5022004694150041142000009600c07103881d6600b51102107102070722600700720103c2 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 818682679 1250 818681429 818681459
    0x70e0f0a0506061608090d05010c230909070c020301060f0f170d05030403051605010c0f0309020a050f010306211e0305030f1806160201060602010603050c0423090106 73
    0x2401a1601c1e041c4001ca80d500c000720381001c003101c4400d224180160400d54214054020900d03048258003001204010042d80b200704080d0941d01e030324800218404004544071000c0703c0c03502c0040e200300603000a901c2c2c48100180c0c8101c40d0701d0260301008683e07000c6401e5420503441700603080c026040511010b241c00c09a03101804200184481440803c4880e6903039000c8204002d0070b0000000c04070307050500c90002c0390b0401100719200842c2d0005842c00c10300818080d00460000764401c042c0b451031603c20702a605245400070900c041d00c0c0c0c00c02c4208a6003084421a0a05240c0d5882c000180700d030004c0800c0d07480da0990900c1080305015810407210800d5540f2041e50358036010400000026046030982c0e13000b030a42c514201c0329558600c4046120074207250300003068456481045020f0040280070054070013a41d0080c000d00f41d42c0c0030706a083c0d680d180401449030704906900749850502d40c0c41060044544000080b4505406007141d07400319090300c40c0c8a00340d4488a003400b5a1414241003 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 818683929 1250 818682679 818682691
    0x31204080d02040b1623030d0c020c031506100801030807020405250806120d170c0412080901090e091509010b1507170306060304240203010f050a090b0904150e070e0f 73
    0xc01c2542010f040e1b9585c9a110704001130440030780e25524600b0325031007041000143c0c2c40c080c0c200e90104040a0714140101d404a449074852082c9060400d5124421101203040b071f1b81c40340080b82011310302c1c2d00b00070207403100508503000782c1d002600c0407210800c01c4030511480402c076103442c000d50400c8001e011011a5a02d0b591a41d58051650741d810540d014154a04d8002c2c001f02d110740a40341c1c103c0b500d280344655400140500d40c1c514001c810711454500503c60040241ca81c3e011003650303000c2c80a440c0504407002556038202c1e03800c2e00c0007034902c142210340c800708860000450020b02c00018540c182041c0004601c06c901040c484104180442086001c0064017605030644c82c2030000290b281c440144020001e180f2030300d0044001c03010175007942d040100c0c810250f48a684602d0f0350841902d681c0f04c0c1d14410300442c50001003000003440f4202c4c03601c8001c0d054100c640d03a01d4840740d055806d2041c100e50020ba48200d0b480c070000d0b00b4098600506082c0304415041e05007282c1460309400f010b041 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 818685179 1250 818683929 818683973
    0xe060d200c07170a0c0f0608060a06270e130203101401032306070513051e061e070f0b06010e0f0909010f050103050102070b0108031204080d02040b16 66
    0x24081d41101c1c002654411078912550600b804071150440794201005030324001c002c80710b221300c04648800f501c00c0d10021740300d03941d841c03960503902ca0041001d44500303031191501051080200c0000399021190546215000d021340140684d0703101000ca5050004580c9010000c410342e080e20708501c0c041c400c05441c0042e180e01800984082c02800c1406c200c10703c13005040544032120b1494010346091854a44090042030300d03403510744500098515400100324400141140c100440d141c13600c4201024038006202225400b150400148001903015800b040600090082c0c001c114104140081600d130b4824410095440342500d0300120030384024155605011021500c00245d80350406600103080c01250700c0030103502c510442c140100701049548444508140011040c03240c150005d010b194481c06040030f69a03601c0007015100e0140c40c043c038560040e03d40205000ca2440d1016081e02c010810005142a51b10100c801c2a135120b0500c0e0301c8105544800c400c03c3c0003c9540d2031000f071408a1f0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 818686429 1250 818685179 818685187
    0x4140115050a032a0e0a0e0f040c030203071806050f281e080708010b0d030507061404060902040b060a0c060906090519061503020a03120e060d20 64
    0x40915003540216040504000c404102c51100da48260001c0c816003411003404564000c12286090050030b20b60181d4010401c2940703499482d0030141c0341d85084591100b0100d080c1d48810740c441e0346030040900140ca86044403070b00400540d40c00e000920060801c0d800840310300c881d00e1130000c1a00c00641c4078911504201c1103100b1551101c207038409001c0c408811500b008003514001c0f118140140c0c2154041e80c90341d862050b103c43e4611184801c2c2c480c400200c80c03940c0d17a00c9144a0903100312400d900d030802051911200000d003c1c0c0c001c0c00f0b02c00d109203030102c2c41c5504268040300f04002190305840703460710f9003000c1080d400d182c4603420b26600f054483c3c5180810451000e08046c010500080000340d0300c40001c0305101244c9d01601500d83c0c0081920260182001466034072404600c00b629007a2510190103082c0c44001c5413139044039030240040e01d4407461070b2100b500501c0200c1c0320000b8001c007288084655603628004101915045000250314020034642100c081d684074040010220204 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 818687679 1250 818686429 818686439
    0x405092d0105100f05010309150e1b0d051203040c15030f1a0114091306150906020a121413030602130e15060705120c010b04050627060613080c041401 66
    0xc400f01e41500ca00782000b1980081626003c0c00043c0c000149c61092403920040000303e0b0b80c049444c921941c450303030310415070440c0107080140d5103107034840050480d0301110044111940c004051684940102d92030403003a42c3c0c031451040c00c0540910840c002aa9840c0c1e180e014080d02d118411a20070f9102c000b841c4446420300107030070306c88000ca1003030300e45001069408441e41d0b10f05484100880c60401800515620b80c01217920455503072501c0082084004041206880081c0a01100e1b40040d0501060161140251205003441d290300225200400100d03004614803155180114410100142d6842400c1031510906115405c4803055810131800d0104100910400d42c50500049030440e5a03203803a484e00301c0c0750154885070b04501c50000716040d011408190b01002ca1510700362024001692140c08201034480002050800000c200440b121b80e00070254000e0f0f80040d000d040742e454488440509081180240c1c0030002942c04131940c406181400e01800b040000c2d0000701c048154141 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 818688929 1250 818687679 818687699
    0x50106090f060309030e090a18120e15120402120a0f06050106050423010c0b040303050103050606040c0c15180f1e02030304061812080a090509150405092d010510 71
    0x84d000c1b58803c409440229182d610349510904040b16400030410070003149203400d446069400c100c2401080300217420307050300d041000300b9000788440101014030f031483c0088014001e080241040c0e801110415260600c10b604200e0320f5242402404e600380c140c0410714121040d20014cc02000070440140020003086542601905451101e543c00e0703a1107081c00001282c021100040181c03c104104041c0024180c041d44480e068074000d005460050b91030200b80320503100e10814150001702d807801c1076004a41769141c14000c07000403d10205201952050400f0541301b51401520705081d007042d03940c200450b604081900300700314800d40c56800d01c142c000039141d00403480b40c40705110042550000900c0c040144002034034805650004400701403c140c2e55035005140c441010452800c4041110702d00422403d00c50074203104902121801442444003500d0068034440d00c80c41002c4005400542e20f90401d00d80001c2c0245214100c0790050f1180e096490282c521180508808014000d00c501 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 818690179 1250 818688929 818688947
    0xf010e0114030a0f0c0f02120307140d0b030105011e080106030c1208040f060302071a04021c06090209130b070f02060c0f1b07090c11070510020f01050106090f06030903 74
    0x21441c4580c0c2c0ba070b525140103a029010300001d80b49101d14180d10405525040070650301400c009508a03110825242c084200324441603413020046000080391030360781a4050002e0810b400c10ba940030407010083c1002c2400d4400a8004085024000701f240b0020981d0301c910000801e4070600a01625196031112840401980201c4905055040c4441c0074800c50b503044034020072000615880d002d9945800500a4100c00003c0b6480c1074400400341c0d400b01d4100a0900654006100741034160320404844607100c000c4000311038468a601c20382c40580d8440707010520902502e403203101e52a5841c0707024581688020061000c1c48080040102e0084c1d00141065000e040074800740c4c3ea0b010103409440d054000c0c02600d003100d5003070700500044c0000c0801c4440444030074850a003d25040501e0948461f961610300d00019800070b0410400762601c0310032020b42101600591302c0311a40c850485080d15000d07041000401c40d41807081007a01c454140b0580100400e00d410482c80195950080280c40 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 818691429 1250 818690179 818690207
    0x314040b15010c0f0510051e1609050d1a01291809090f010e07030f0f0c12080319020a02060601030b1f0e091810051b07050c0f010e01 59
    0x7094400c40301c0e402081d004482c19008401140c0c8480349141890b940c000c43c10304001c500d41480d01094002e8000400001141da5502581c07000359a1848035101c40314111980408100003204001103075110614901161130048483c03100c2c030000f0100c51900300c001130f805030011103010301807400f082c00e080020203501c0f012180c0e456500c1c00311102d03441c40b404d842d02c26154404260018050341d4140042e04000040c02d034030090003c0c44101651700e0300c4da51148406040d1340500345a4800040303402116220687c41016078060141c2c5400c9138500500d4480c1d01201c240000000f4022003502c81b042c024004200103000790301e80100180001e440d850042e00b1507041c50380701c0072004000e55401801d8030340c4011800204412000280004007075003200100c490245c0799910110f0100303110040000b444107a0380c4014100060040b030400020300008120300a0a0403130781d80740c1d07044840741c03004040e003034080c0c002003140101134400c20031405480d08409040c04040c2a220342c0c50790700110140355940c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 818692679 1250 818691429 818691451
    0x106020a030e030c09010801090c080606010507020103050c12090703030e0d020f0f040e01020a030c1701060504060f091e06031a0a090902040b0306070c050d0c150504050312160314040b 81
    0x1102c0b03580440e00d4121404841c5074000e928400120300e1000562080341d820f401499806503069481d00c2c2c0756160312041d00c4103030010754104016001340d4080d4010303580000e0801400c6241407841c20410110050688166280d40c0102c0820418164040c901180702c000031202e035241070040750700180c3c80b180078800e250301030030382c1c502c8044141d601e82c0c1c480c1240d030000100030740d1b680c101007000030010284008d2503804203031003614071461003112195190584407261200c510345070030b003401640e511800800a0042008a90020841e4003070700101490321000307034082119103420140050117603900c010b81601d203161844032410403556048107103002c50f0720404001a0882080c00410003400401c03084a81611444007440300650307124004004541c09102a20881c2e500c108045a600100f16005010420840e1000e00b914200354040d50f00588075100720b0345840100048000740610844039140d4001458603410482509405444e58040d42c00190b0300b03940c6000c1d5240b041500c800b910015240d = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 818693929 1250 818692679 818692697
    0xb1609140f0414040b1e192c030d0f020a021c02010b15090f1503040b22050c0f0d020612040303020c15060418030c0308190e01020702180106020a03 65
    0xa40720380d8400840560088100e0f000c0c0e1a00d4100f0452051003901c40490310003141503411710105010107070502501304007601d050152103001e1090082c00042500300d2001c051425104404410b6031202045094a10003441c2c80d0241c5d50a118100c3d6070348506421150700421000c91047e9000c40c03c56000c50100500c80c0c0405009402203004107140e07035a05422040c0907840450300c00c0d04c4009894914001c60308503661110500600c01a582280000f5034220024004100007940b14404142c1c00381c0d95008854542d009001003111004141ea4181da042d008200d082030503042480c0d550b40f801c041610800300401c00d5601081240c41581410356280303101d10003283c1018800d0b011640b506e00418100c07120f101d6003c08503e410401030351998030132841d005034000100359031240000322a405454903c980c4105032800e41e102800186081d00c5644089030100c12103456100350b000d8641c1840005890306d0300c0341f050215409109803581c0711090709100410101c0c0e4001103d2990b564145804d2140c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 818695179 1250 818693929 818693959
    0x305091f060b0403060204050a080705131a04020a0509030606151e0c010c08070905150f1804050702010603030216082808040b0307030b0a0302090601180e040b160914 73
    0x1040690040303000c0b4080041c0c00000d00840c0d80240065820442d814405150348984060f501e2000c2d200d6607410141d40043c0400d10006c2c2d80c840807081c40801b1100707481416200c00641281c0c080e11010011500100701c2081d1130501f08000760f402a0241c1e10103649000441007680070340114070141218041c0c0d940140e401c101050192805040000e009000381752142c003019114130001c1303803c3d00008034050070018440c0b0f010f041e8003c0328240c5208152921444101c0040e840d48a485582c0301c40080c0c08074802980c0700d81c4101c61040c192503000094450031071400a0034505020b03208681483c440c07500380690702003c500c098100054910a528412107500401c5840f4048203000c0c1840d40080340000c2c1c5049807030002c621802481c0d0341002407840900c2080b0716841030b0300000e50007042d039800240295000303100a0903415449078640460903070300c050055100800f2101110751907000c0007440020400500156a00f09660602845144c1880307201c4420b040e1088120f80700395541ca08400e0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 818696429 1250 818695179 818695181
    0x303171605251a0106080703020f0d0e03120c031b1c090c090c08060f120a08090d02060f04030201080c190e040e0303090c030c0103020928051807030506010305091f 72
    0xb9a1540101c181841c800d0074811003440d500b0921402c00468551400a8441c1d8480d20803210b84000b0038807524204240704200e6002000407a2213000988010407054400551040031241709250342c8807669600d24180c80c0203d051090160702c003002c02024004806031000c4100b03c080420481d00380081d06803001c0c248150804081d500000401d45401803012000c1c1d40400038034030400003600c6007188000304c8000e000c901800c5441c90f603c1074000808800000b4641c40c02010000001860078171001846d80006240354040c00d0b12821401c400241002156040b03400d01c1e6012000100f2507042c216040d00e04803407400040b1500b4100800030010b00d10350355541d803003a1010b09a0b03030100e90700d0b40b1705904902d6a4801c0d011046210f0b00c1019840300b1258424000c441c0c890f00050310800703800c28580c596200b001c403005003040411504400c0070646032200250685c650618106201d45410018809011100050100c0341018101420080c28031400207486046105c180342c41c0b03a43c0c2009400c050 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 818697679 1250 818696429 818696497
    0x603021e091807020a2d030f180b03010e10180f1b0314091204050d020a0504020307051c060b070f030c0605010b040801150609050d1502040303171605 66
    0x182c0031000d000140003220b0750002e1503803502c5201e2522403182c0440074800120240c01a8114480c500c44d098a450009200b004910010440d90601c1c3c03030340c02280b40d014403001045400221380c002c03002c0700401202c0d0815881c5504030706207404440540741040da502c4125015500200007031a1207007400003c940d055800580901c003d16608903100d8080c0c0380c0100a440c1c2c1660505040f00c1e0440421200640420180c0d150601d0703a07101c0d868a880e081c24007500403680d10f002da900c0001c003080007030142c0301c1d0300056105280907552030341c0d140300400c8106002c440c0e1f201c40307881c0c0c1c1d49002c000b44010580e25084079080c40e040041c42c20a4204c0340740488900044100007000b00e410f0000005901041801030000d03a20080c00178070004003c280c020100c209a4403a410004550301400c02c403609005110f010781c0c038002e24414111071641c0d1401c07402e03a80300e83d000300e00141d080022a41c010036400b003403a41004501c101f0100000e02c11100502c00d00441d040300000900c100800310241c8030f03940c100 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 818698929 1250 818697679 818697709
    0x50a1206050c0703270e160e040e0c010e0118030c0f140307030f0f05010e0304051302070b130c081b0a0801090302060106050f040306050a02030a1b0c0b040611030a06050a0603021e09 80
    0xc442c940740c0110083c280454647c4e0300004100c0c880c046198901d0180a007000c038141810040403c1c0031210011602d124481c5402c50502440310600b40140300580c0210380a540170b0b289008405250106e07a9201ca01c03540c0c01701260052510750010941d5000c41c020b0b04803504144103c09041d49410b100c011881e01540042940d03180c80c11290614501001400458004407a00004c00401d0458907043c2e00c900c40e80108150009000500c419040c0d00400000d14011000450456107130084a46820380e10410030025441403403841c801480c09604560281142e1002885001c155690280d51880107016039424490046500d40041c4c9180d01650300460308a4000e000c5400c0c00300c61034000798419900ca000c81030501c81d200c46000b141c0d0246080258060795400c501031a42e85031905000d0005d04102e0302c05840701c080360344449207078010310b0190a95a200003540e514003c100280854070342d01410a00d4014086204181d4103d0400d040c1c5203840b001084d65400440000b078a885d01e01c80749 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 818700179 1250 818698929 818698949
    0x50c04080f060405240f1305030c1c05040b27040f0204090605040e030318010f0903050a17091e070503160f0602070e04110307050a1206050c070327 65
    0x4034190305080081c03854003c5019400303a980400712485c0404c41c841d80d000d12100400001008209940d181105440d031241c0c100106040306200da58801c0c2c1035038000203242455a100c01000f41200c094007100c982540d03130b40d040451805161a2900d426030055245007000640071a1120050540d640034003098104020401c100401c02ca05290000790010300800340d80a00d01080400c0e107061070310880314800144d500070f40c2190b640c0e450f00c00440e500c08003900c115548420031804000700c90b0107040300981c030030344406407581c1444c000140f10805903101318403034102d00801d200b86007501107a14041ea0300380c0d8200c0c4070021b5408140c80d00d81080303940301ca50140f1402c8a6981c520000e294090262480b10369500100c5980d10002c980d90714050050101100d10400414009406110000d440603406020b5400d2140c1c2e4100240d203071503d40c2c1c8000284089600000c0421140d0700c0380d558090001620303c1d003401da098800402d40c540035540d011160001c08440c403201290100d801005011741c10b0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 818701429 1250 818700179 818700193
    0x3020c190e280609110702090c0a1b0c03021806090621061003150b090a09150501030b0a0608150612100515041406010e13021204050a140d080a050c0408 67
    0x440607000f44110300c80c10b1180e91a01c0c0950b2102d92281085565040d0010b011501a48904820000310341c00701c40c11109105c4040210007900f068004101e1002d402030911906580c694014011010f841c070070b900c100c1c1c103040010003050780c1c0c4a0300410b40050003921070806c041000c1e4081054034883c442c401d42c15101d10310401c420740900041c0302003030341d01c1080103400400040c0900001d603849040e005038040c0c1c40320002071b40500580c1c8a401104d001d08403000c282d044040380081143c10a800641d85005100b0802c031003085035000716801007d49100a0442034540c2d480134121180151905101d1006c40e80d040105507020002601940c416080c2003010f0700300314207040b610711181191203000d135081440101c510140e40c00d503a84542d4040e114a5040c1515404124001c6403250b08504101d500f40040c410070086130382d9151055116000502c2d41a0003801d102c3c0903e416040c000c15983d210b1410240241d038007800442d041010800c0c0401c06403107a290095180c080d0f600311a400d40300740c0f1 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 818702679 1250 818701429 818701501
    0xe0709020a021204030c150c110402092704020a170714040b1507050615010e01032a0e120703030f03020d11070b1e0702070e0402030a1e03020c190e 65
    0x20f50074100d41f400c6050304600340001505403440036000f80d019210688100c0c50003040d0602da0018201a18028603060000220060b40c40101150459035403890801c2d4003003008604108603124041d094125406c03c1c05000369440741e42d038101d039008841c00c010000000d42500e0301e4079040070441901c01040017400014010f048901d80d00314400648540c8a81d1000c640002c03080400c0c09040b04040e91644410480c402c019000382841c0c0703a0a1102d40350b5420420340906001100300b00002c140c1d518041406110801c02007000304924280741290010107003000001e80100d45001c1040d02c6080260301d440c45c12075803070002c04189680200c4500c0c000742070400c004201c03c20303070b1144950f01030040c09500c079021610400b040c02c0b0740c580d0140e8060b05050050a85416509500c284004c04840454456944500c0c01000c020f8101295211461003a0101034040c40111600c0c070782034900640600a185990303034503030040d12980340d548030384002003210382d0003d03a124a00c003040e018010152040f0a = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 818703929 1250 818702679 818702693
    0xa0f200c06250803091b0a0b072f0f0a05180406090f0b04140109020f12011b0906020f030901091403032134140d06060201020703120e0709020a02120403 67
    0x1701c0d2040064011400740035220380c80554140c1d41d4410250100340b2850619904901c15406160103071a00740a2140480c4d002d0441e050615680082903414181440200280881c100b8a118102e10603a4099820701064031400f0404010404c50b242c0014603403078a081c05002026413040103001040070700403e105001c010002913000301d00c181c0f6440e074910010a1200e00301d48003907400079030090400038802d0075031419041e030f038101001800c00021804080b51411449480e60b40c0d100d004a00480810001d41d5010300141c00410f40b203130040c625044007400024800040c60042004c600b1100400c00d0b85510100240c0e05030312915a150300340d002e000c00d0103180e4940200ca012040a40d0b4030689040e56140b0080b903c2e003152480102c28010569041c251140260030048204140050240c0410040700703000b100c00929558000681c0c614150400804251030034219031012818080c805000c5400024010112224140700607224513040d00220b0074814000d411000303001d000700d4048240460 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 818705035 1106 818703929 818703931
    0x3130501050c071d0106020105010f1503020d290922020d0219060804110a030f120e060706050105091b1b0c04020a0f200c06250803 58
    0x2200c1e444e02c1c19628420b40b401554440c0c40c0100f00d542d8083c03107140d000d400381e011002111303401d2a40100e01500302a9400c42010b03030018101d102032805a02c0000c00c0035142c50640e80b154030760302903007201c5610908402d208240d030348003040c501940641c00094076403800b044c08990700142c0c0c080050700010114203981000e1170b103c4864180741c1c10501e10003e410961100d03d42c600b800d0030245a08a000004940158180b072170500114100340c4204016030341c0b19941028244203068125440f03405001500d411160104a92080000d6a0800c5042c1c50701034901c000d060341c4400e50250354016044c084542541c08011143c06412000c005a58502040c030442e10080b0b50314000c20304a03400001300c0b40004001515900342907510a0941030180c0d460718584090f441801a41503e0300742c02c0390024400d89000800807058414101a40c0c03651000c9000300050010300c3c203042e155644 = true := by decide +kernel

theorem cover : BRFrame.Cov 818525179 818705035 := by
  have h0 := BRFrame.cov_init 818525179
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818525179 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818525179 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818525179 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818525179 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818525179 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818525179 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818525179 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818525179 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818525179 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818525179 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818525179 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818525179 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818525179 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818525179 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818525179 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818525179 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818525179 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818525179 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818525179 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818525179 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818525179 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818525179 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818525179 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818525179 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818525179 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818525179 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818525179 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818525179 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818525179 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818525179 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818525179 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818525179 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818525179 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818525179 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818525179 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818525179 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818525179 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818525179 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818525179 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818525179 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818525179 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818525179 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818525179 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818525179 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818525179 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818525179 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818525179 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818525179 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818525179 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818525179 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818525179 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818525179 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818525179 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818525179 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818525179 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818525179 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818525179 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818525179 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818525179 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818525179 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818525179 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818525179 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818525179 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818525179 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818525179 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818525179 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818525179 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818525179 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818525179 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818525179 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818525179 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818525179 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818525179 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818525179 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818525179 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818525179 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818525179 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818525179 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818525179 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818525179 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818525179 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818525179 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818525179 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818525179 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818525179 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818525179 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818525179 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818525179 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818525179 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818525179 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818525179 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818525179 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818525179 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818525179 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818525179 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818525179 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818525179 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818525179 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818525179 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818525179 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818525179 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818525179 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818525179 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818525179 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818525179 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818525179 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818525179 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818525179 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818525179 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818525179 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818525179 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818525179 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818525179 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818525179 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818525179 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818525179 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818525179 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818525179 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818525179 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818525179 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818525179 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818525179 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818525179 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818525179 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818525179 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818525179 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818525179 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818525179 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818525179 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818525179 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818525179 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818525179 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818525179 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818525179 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818525179 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818525179 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818525179 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818525179 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818525179 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818525179 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818525179 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818525179 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818525179 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818525179 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 818525179 ≤ n) (h2 : n < 818705035) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
