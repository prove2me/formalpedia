-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2328
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:22:44.94549+00:00
-- url     : https://prove2.me/submissions/1bc4c76f-7516-46e0-b643-33cea6da1988

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 418525179 ≤ n < 418705035 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 418526429 1250 418525179 418525183
    0xa05030301060518030109031b140f011a0402040f0e1003051906150302010f0513050d0302010501060801090e07050112150905010611060907050402031e010303030902090c03150103110909100503 85
    0x54445019170082007407100c2500e000b0188100b4132040d0080030300381c0c010351003070242c09812100c6a4864038100d446034220058524020b10440c5016a840303c00300d0340100c0076181500880e02203d0341140100070841c20202050345216015000320710840c2c00b0003002000810a000c402d441065170b50000c1d14100660401c00b0075920b04c0340c00107500c500316000920040c0c1e0000007050b1b000c103007803404644414969500d12181e0000c2d4009684c0502c03024498001c2650540006059406c0d40e80d4140c00c42c2d903680c00722400d60706120324001d406e8004000c00d116551041c0c1d61031700400c0c070303100010a0008001c0c04a240244043d00700c841c2442e11030006114907034100d02a054801154030003814035140044040761607080030701420b0b104603000030115918804400240b040b004000d40300700020b59503850080e00512280b0412400f03911801e001492080001c01600d10403080c991000c21202c8421004400a080f08040842c903c00c05204000c2152503a41d03031244203540b565100c241d21820001014 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 418527679 1250 418526429 418526467
    0x30614010206041a0709030b0a050406140c0d1109040216020108150306130c0e01171902030a0605061306061d03030a0215060103140c07020a060e1c02030a050303010605 74
    0x9819548004203100000d40c11403c1e4401d29180f11000a41d5a2503010f412201d51145500142280090000b4405505c0e0b00e45d0000c0d0280e4412030082015494003050380003036180c1200c102c640483c0c188408102c91b8440d810100c681c10801d00c0722450700c1841000501203800c011804181019807491000442d6003004640f0342082c150f4010041c900030b00c03000241d071a0380080100c0340700303818100000100021255148064401c00c05903050f19a107420002e42c200a00e010207010f03601c10780034510328074064071758090161074010340500441c1e002925900080e15001d0111500f041010034022928102031040781d001d40f5241d81c44005c800000910441d11102e11a140c0340300e90410481040d0136500081c914a43c00c840001c0b41d0782d599214030068004007821b001c6e000d14040c02c84200005201000000c040d00d0b8400c0300d4190071261100012203d0312030802e2115001201490000f0018514000e10050148010110744001540d13a171028110380080e402040443c03000b103840b0881d143d0300f181003 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 418528929 1250 418527679 418527719
    0x140414120405060d0b0d1218060801030c0b1e0c03090301060e0f060d060902030106060c0201120903051b03090312040f080c0d0b06030f1b12060c07110a150306 70
    0x941d0a29007041e0000e2200c1c0305504090000a59552600d101e03a06c45010f10a04503411100170050b11500030405455841d14200610280451500205080f0300a0840b941601d401c40c10054010f0704144c2207030201d40c050700320141100081b068241c401c02c1c0c0900104208490030011b19103a075041742c00e160a44043d50044204408000104400300407040d9200750f00543c2140c05c0d00d181e4406d414000014030400d00d029416500f0904085001900b01a40120f03040c400e0341d03200d421004584901c002c507040b0b803a0060010302c08008400040310707952030300d9081e40d10701415a07180c1100c1c540000d140011030f900c0042e0700100414104040d500140d2448000d2903501c3c00b80510315001c0d4000344d1b2031600303020b0082c0500010004160f45803010030040900302556811a040820641052036104207070083c0c0c14850544030025441c03501d00490a035004003510001c0905010701070b51040052000007440940000201c4400254800c400102d546840e40d2034500103030540c1850091420000201c0e00 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 418530179 1250 418528929 418528963
    0x21603032613020402161707030e0301140406050615120108010e03070503090d0305040e0702060a0c180b0d0212010e0a0f020405010518150c0c0907030c090e0901140414 74
    0x30403004a0481e5001c1c80c8543d4120340c011380d500b80000d1b80e07400000e070360384000e40071030fa4a59403540e800d2003075001000c20f03500030303100d444000481c1d008047c01c0e42c10f401c5000004c81c100f5008200040c4003504543e0304403400610b010502d0b0b00c80800c8428580203030040507660904440100b1032a1400e00c58a04172000d4640a1807600801d9281c2503a80e118501c441030154008495100034140300e4404d45025000c450000145030420050096460304143d50030074a03189418000300e040f500902c6402440c0040c80241107103c4d18009240d00030b0b800c40400c41c640c2039001c0055580c0002180c5001e4040c0c42c0718510a030417420860300310f200f00d40c41c81300c10710b0788584104002d11441c0e0300601903030001c5806215550402c480f46c004141c08201540c2020340320b003c0403c0720f17080100c01080ea1400040b044da903040036561483c20031420345041c1c54519002c55007251081c08029840c005040c0d018001c00d0001c607000d0844042c8840c00b183c111419a01c1030302c2e0f490300401010040c48003034000090800 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 418531429 1250 418530179 418530181
    0x5030303040507060509010c021012050a020408070504050604020903010c080702060601081b160b01060309020117060109030b041a040b06010f030b130207141501170307030507060902010216030326 86
    0x10b60159208954003ca0f402d02401280e52500c6a21030780c00d0102841d4040c280100e0b041200c0d2014200340340c0c0104404010381050000303440c10080c0d100352000c680e5400020302070360345008140070043c40048c2c181034000b9020004140a61024028045c0c0d01481e642c0d1102245020a402801d00b800501b892341008546410300191030050404006805e03998805503a07078188240c41036a00c89554203000b05038142c207400000310550117600281c0014001c0e00c0d201c58061850543e0701a07220101c4034580461a001000d001195001080c10f41c0b0500c600100c00200780c0542d41c0c0d48203000211411a400500d2904104255230301c0000c5c1012200d46003401d1015801800005900550380c0f86009203155020408030240001f000c2000040c21a10381030751211000b80580c09000c170424060702507000351300455070f0010100001241ca200360166a86420100e1f142e841201500c150802030b41180f085108800322800e0302c4080708001c601c42d841d0381c412000108000450310341c03250600d110b0850b00d0304c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 418532679 1250 418531429 418531433
    0x306090f0d213b0604030f0c060204090501230a030311071d0702070602060103050a3806011107030320030f040f060210020a1d1203070c09060503030304 67
    0x308141800c5050400031884000700b00007150500b84140442c000c1814601c45040100a0010415955402c0e04403245400c161035401d100c0c400060041000729800400014003180c031541c21500c5a070000d1402d40842062521450240c2c3c003d60468100a95210010031a1610800404c0c0814404808103918500c0801c002a801101444090306001c410491181e2041c420301192014003070002c29a5a58481c0c103401d00e00d200d00407200c40c00940b04085001c00c25070700015515040340e6101005084503500c0f95543c2402043c2c102c000c10000032010014041d19444803102c00010030702da0303c0d54469160050004010500b10b43d03040c103003500141410f0001c00d074007010f90070b00702c46202c00b0720000c50401c1c02d01a00e144a01c9070000c0409002081c00f040e04117900c0b8110044850355822a000b00a2480310b40040b88aa0202d10011a103400031460600711442a4401c03103407401041c444095082c040424115032000c40d007107a00c5c1d208100244140017070391041e0340241005400541c218036080d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 418533929 1250 418532679 418532683
    0x160317071407110609041508070512100b130504050307022404030201141b030a0f02030310060e03151009050a09020114070c1a0a0e010f0e040c020102070f110306090f 73
    0x5400b0240c4480c00b0000c0d0010640c40350021100c151a010b082007040c0140d85024010b010310324014000540100b82001400c1d2501e440c010f00c520860401034690061a89040401803100300350306504800708103c2c0c40780981051040d240300d6405003000c2c50f0760740c51501c10082410031300c900303c6181c092009205040c80c114030069909581e8207080446064039002c11070ba1340d60096880c000280e40700305a0500c0b0102d0088064001207100b501c0e0140d0001510509980380d00003220010604c000b841020800e00d81305100310001c2d5032019042c3d0b00251017140e04e09540c14001c84984420a000c0c80e4200003003641c0d44202680107200382c200b04604226540002d10f00d03002d41d40300c0072101d6000305480d8203010a07002060300900d102035039451081ca0001000030740350030500b81c0a002c02d072010440d1006501031102d154030140d4a0307862920a082c40000c2000402d14810102e08541d801d0014000003414051a02031090107442c1c600582c6040000301807911800902a12541d007103a4180d050359000 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 418535179 1250 418533929 418533937
    0xa0c170601200106090603140a0f0f02060c1e0706080f0f100e0702010c03060e060f010305070201061a1e1312031407062a0c15021603170714 62
    0x240307040408900000000450720b402016101619440c0c02c41c0000d0140c44d82d07201070100c03486100000d920700c4101c0070703064030707810b42d45806440851080030f64000211100b1004880903c003c0401c0e0030004008510384c80c100e103c449640c10202c00010142c0510000c004d80d100810440c58900d40c20b29000012a049260290058070070391048408103102084410740322014042019040d02d103482c142d0b40003806405200320401c0031a16126003c101a007000d0131040c8142c20141c0808485a03607c80110700810004008404656030340300c011400000050700d0f50300d005403050740c050300c5501e103480019001d20b961140c4090706408010110a200d842c21410085070648031070403e107640b89050682d0710880505c0d10010342c034800108c1038100002e60344130440c4a41c42c41301d000c0c85d02800807555a441c0398003101c6140416464003c400c009040b003c40706186d404e48a0780175003803501d400f80020341c801c800082280850b10a166240b070007101644483c0d0302102514144200aa00b08031403404c40c40303 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 418536429 1250 418535179 418535191
    0x30207090c090e07110604050606010e0405060123090312070203011409060a020d060b0d1e0605152208030a0206070306031a0a060e190b040506030d1b050303040b0a0c17 74
    0x41c041d0000f40c00107020306004002032120400fa100f443c0303000d08c1d019444010468400380860105240001d041c14148202d03845554182c407001d05840c01106120813000030344c1c110123040c00c01003080103c05c2d203040c060b038130300a44840c8042c0d803229903510415080d2440f04200c0010310405030304001d8a880000307041ca40100b900f210040e52414681804006080d00d17401c41032480c1c00c0080c4e400c240c1c80c141d6010141c202d100304515280401c3d81e6807560160f8486100700340d4000e001b114441c2d00d4081c084020401c095035aa6604000001c00f03052025440d99980555003903000800d081725013540600c11240d22011a02e001c2004074150707910b100740c4000c2012100c0c03803020207200141c2c0e070300041d44c00030014204c0d01140b42d140d840d10122009100e04483c41d080c14003030500300d5a46441c01c05006540c0100c2d030040203007624802c2c40200310390030031450941401d120341407540038005c04e2080c40218010340c060400078106190038500c40094074541c000704010448059a0214005075441c62160880 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 418537679 1250 418536429 418536449
    0xa0c060e060412110f150402011b150218181008061303111615090503010b0f1221070c06020d0909020310030501060923150405041a070903030207090c09 67
    0x104801301c1d8035081ea03c03007010f4520310030146510110000400c55600c114401d0742e030701245801540320b4907441d2402d0340703000740302e200b4041449500c1c40142d00580041c038030290045003140740c3c0c4030002e42c1e100da1801c0501c2c16000703440c00f40440f40c074800c00341c200940340000c0104030b14202040012061508103401030200804880001c4000030b060145000e843c1700403051001a85d15441c1580ca9000103040c000e0224822600000316801d040c060841400b0f1b000304820319040000301404042c110142080b6802d009003188450021061954034440b0440700c03c02c00d4583c0c02030f00c2d050340501203a4228109545c8086624040c56602604050958820220158494031684030320300750032645800050255080060201e10030f040d9600c242d0000b0141e0400450300400c40c40c0c41f43d402c80080c0c4005110b4102c60b40002d00703604080d04815005840f849500c4810034420b4004014070f1015245130000403c080d10800506a04010250181660f48820054080780803c00f0385015828896240300c0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 418538929 1250 418537679 418537697
    0xf05250906140903010507020d020715020307120c0206070b0a0c092d1715070504031e11060d0f06171e0f030f0c0d050f0301140d080a0c060e060412 65
    0x42d110b640181c8440c60710150082c051420042400f0791119132030314071f03e40140b040401c00991000d41c402900704842940e00a10701c0c04041c0d44440c8000c10003500c00b8000d01680502e694010384880004041440c0958130800460500c03801250554909251441c10400c2034901848290201c0b01e03503211401c0d0685800000c520300840d148070b0f41c040b95000c084514120b4400301c403c85808510b18910203a86148a8001d5954500580d1311b4040c40c00301a0040c03c00341c080d4140810100c4800e010f407801030400c802d4411039400002d06035404854246012034880380d136175071220464040c203009002400600c2040000e164441a81c2c1c0c0000725900e50310301654046110503810030722928511440300d6050b25070314526001b5401099014030980d224a1150026840030a841101620490f00e44c914146183d80d280c00450f420768003040c2d44450727000c0700801f102c000140c461802040e0850071604c803e4098212400d00c601102c4206400f100590030210800c000107846106021601c00f06060a943d2 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 418540179 1250 418538929 418538957
    0x2010806090a060b2124012304060e1002010911061c050f010e070c050624100306051305090c1012020705060628150c02040f05250906 59
    0x5044583d1141c540503000244030a1a0f0440b00350850700c800400d1710401564450710000000190390b40007600c88848402d00c2240150310602e080d40c1070304424241c601ca6120701d55864400e552140d80807101150301c1c0440c0004500f400004240340554600003004455403230b40300e440303200a010701050321034500064960500a071400c984100710306441010040d81c030308003011040344c1200f8005c007240700116400080d0007078807461b001952280c2c05005000203496000300d03800820002140c100000050020751460f81d04c0f10380c0700790300b5291203a40108285140406110b003220303d04401b0401213050200704640c2100c0061607000048041d581c0141914140000701d43c60f080d4240742480301c0340006002000e01c40009001c034001c0c44100c0340e2400740c0308008050210825003903000381c881100054100100f030705c2011045070800310390030034041d842d0b9036600140407a01940005e03010581c2c1c4100740440500c0d03c4064840307014440d0000c00000c089060003400d4003903a445000c04110084902c244 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 418541429 1250 418540179 418540181
    0x20a1707050604060902031903020d051803030d0903030f0c4b030c051204021014071407050a0f1806090f140901061202010e0d050708030307030b03060402010806090a 73
    0xc221a0000c060314000d040a140490281c0440c84060b88a48280c104c0e0075107402001c44214001c6925800500c04040310103402c1d10300b5003041c02280c2a03184203c0e42c080d4076840910042104400304140011030340418500601210070100700702015500d4038034001c0c0410b0b00445d40c0120b20100c046004000d28800e9403c41908108010440084130b107a28140b83c000075209103800c0400c070b00e807000c3c890007440190468940c01f52040d003020301e80e00a00403c01504000d1900700c080d840c685841a0000f008600420301e13039108071400c56900511043e6a40c4a2406000ca80040e0004854088429140c04045050030502e0300420f0411445046041241981940620000c05143e901800516104001c0a00801d2040b503d8600d1183c42d50020f14030103c10302c0780c034007a150240d0300104d00d440650011909620072051035600403068801c2c1002140040ac03501c401094004000c5aaa182403c1d00809899100f88031501940c03040042c403006030307003000c0c09a43c480e00a8800b1504d954406083c08 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 418542679 1250 418541429 418541437
    0x50702030d020714030a091a090901120302010e0115060219080f130519061803050d0c0f1b150801031e030519020601050a1a040911040905010b070b0115020a17 70
    0x13400c40d120000748540318940005481045444c0100788442c018032119442503580304904c0c4855110034000018066000d0310a07401c803903980207200000d411495840c5031402c54206008880c0b200002250400003c2e9042185940c1072803000c2c20b040b8400c0e455503901c90315005201065940020104111aa0700c9101102b02c0003090028400c03080c203449601c4840c1c03080b540c1e009100c00185d941c4030700d0400c4869502880c0460b0ba01c2401000801030326101228842c074403132021141c0d45070051452012550141003c00b80c981030300c07050100070b0701d40368181c00e02d6843d036601c410038030065100400100303e22010034a00241081c0da00c03800c3c400d5a182c03c0f100340c401c0c072400031001d0301c00010740110b140c0c1c0000c079036060320070945002d101592030302c841c43c0c290184180c0e064889101001700340440e070354942108420b5017410740d001d428691500360f104107a810980000005200c00315018082c000141d1845006040380b92003c640101c00840081d01c441014102401e4080907103511010340711500116 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 418543929 1250 418542679 418542713
    0xa1b030c020f120d0b120a2a09051501020a171c02030a0219021b010f0c050f0705030d020a050a060b0f0909010f15030230070807090c0e01020304060c020301091a09010f050702030d0207 81
    0x21148c005d85448115004100568081000f804443c2d09080380754000203030803440341c0e0040c1d01e0400591b00042c4486003070713002c004003001c2c9414507409108149042c0c0080c6009200d000d4000d41c03945105c00c1c11444078620a8500003c40d400540c074a443c040010510013003424084c42c03c0d0015007001002612002c4030b041c8014182d00c03600410301c6aa02d0003003050070654108405684d1900c0300314034102c1c1d69114980001e4925041888000b00041e4950301500d09040054401c4854060400005088bc80d046036800001d075103509401011450b14421403626401c2c21524030103207415900400c03d020f1030180750710b00c070050f45103a5001c0b0340c1c040303900192160a4101141c40e040d4a03075610316121300052003100701b050b082010107102d060041c404d0b180d1402c01030b40150300b070a01d000300840d091103042d0820781e00344d5070fa0f0b001040403940c1d800c12620b01300e00c43d0914200c98202003080381c0c21146d540c590380e10807905e000c043c08400d540c0807088404800050b00e0140e15030300d080c1003e0100c0461b84140f = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 418545179 1250 418543929 418544003
    0x2120f07021e0a050c100909180507030317060409170702120102180a0803071a0a06052d031507030b0102010f0e0706080a1b030c020f120d0b120a 64
    0x40c0d90b802d03030005414420a1244040d540e0759010310013800b00d5200d009566002042002805010311007044d844040302c984004440400416170f13031500c1b82010760f42e4000f500043d20311419111117611404015400940699007045064240d880e60310340014200311988601c6800a800415940c0d6442d41d8420071216400856460000c032000d8080311082c843ca05029060300d035400980b112000c800e0b103081540258000b5140400703111b100c01c60f0f0000404c11a0041c3d5140c1c80490581c551a0448c91603050090580860581c009400d140100401d08854072952001e04036044203004010440d8002076281004941c103c01d400050307001d05040d00b22401e000d480d01505813081940020303d0030441d8042e40354071003503032a101c00d08000d40c4d010185d00202004100801e2401c144640d100b551484e031148140d8500307244800e030280c10001200903541031880c0220704149002c030b491254050005c3d08848060800e446540000d444002d115005081a01d510707006c0d01e50414042c3d6828810400100 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 418546429 1250 418545179 418545223
    0x9060112060806090f060f0103020f121005061e03101a04150306140f1f0306020c21090108041106040807090203070e120a150b03010911090a02120f0702 67
    0x10710290b8a100c2141c00454a20070806178280c91400420903500a915002108500ba0b0030354080c0046261082200c1e50000780001c40c84c0c0c1032220500c100071030004c03204030103d0141001400c010b00038010000c265009280750300e152100d941d002442c0d4000c04131141010480394100c546003041d0200300c458454000d030912691f405007000d4035002d001501e1041c1400c0242080350404030803610012034400c0c0c101c40075040850046d95403a111000301c81400b1200310b84803a102d030f607000140e0300702e44501c8402d80d00005000c1005955500314150040790450042c1c18000180b000038601180607001404030006860014040c0e00c0c3c00781150080d201800c200da030015a00c040c01802580115921000119480d104890f580381800403620510481d038004d01e907040c0262038402035020a922a100240d40c6c800070030655032028010032643c0380c050410320f6040c40004046c414041070082041194900c10011180301110803580a50840c4440c0407000841c2c2d0b88070002e91510707000354505a11050203007 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 418547679 1250 418546429 418546439
    0x22403040b07260910050c07030c02060d091a0a0e070e0a140108070303030e030a050301170a05070f0f0e0106050f1b2b030b060d0b01090e04060c2c0906011206 70
    0x70f5450307000b281181e0882d94041d105a5200c4102c0d0310540b04030510020401020300842d124041d2a44072900040c6114a01412003540c4000c4131038041c400c071021041e491048041c0740300c3c2c9030141c1d40301e450640b06224000000803c0c640384c001e5070040c001a602c0c003102140c1c0d003608a60009018030300f00d1a0186541d41c6590585076a1000c2e031108500003030410944074042070b008001e503582140c0640720304d4110307401c040790704108007034440310860540f090f81d229070302180c030070400c0c040200300b0107140c01c940c10b00b07004070080e58001540002a80280060042003465070100c1120b08103002600d000d0380341d24488464507a8000e1a0100d003105102c0c0049452200c24203201c20900048400800e01488100f01020b509403420280216413001c0f0030300c40801113075100d0b00150710082052400781c1b42c2c251282040f0f1441801500c0c25940541c0c4e8812341c000c03403a00540c815400002d4039a1811411070060300c40480c044102c91028003590306200840c2a44e40641d81c00d0703005d02c04501c0140025a111 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 418548929 1250 418547679 418547747
    0xf060610110a0503120a09020d0303020304110a03110102100605090c09120d0207090b01020a051b030a0f060c030606020703050a06020f0c030309010b01080705040f030f11060a03050103022403040b07 87
    0xb2448000c00000389004190910716034410008852340c0a0300c001441901d986081d0000e4200410981d03140040c0fa1950095642e008104000b41d845203151121040002000a1420010b0882403108500c0d0840c01d000d180c1e200c10481e5404403045102640e60300304107000c10a2481607013101030280c400d09004c800026004541182565011b203810408407281000482e40d40035221000381171034014845446090045050b2034642d140701402322034183c06166980840b00c804030506035042d0b0340d911008480325916001d154020803551008003902c81c02c41e16403585807160300400405242c0c0c00a0102d420500c948180e4100b800d24005aa8036031070001c030201d0181c600501c0d10307400030743c900c00095001801034050300d0584080c1052510050b00312740e15980c800381c2015003a00e1251035038103c4909603503010300403c205603403680d010510713500d18414000c01c40c40700c401001c034000d1103c040318010000541580d912941041c0c03003406503251128207403007000e819000800509842410070400c44a1303 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 418550179 1250 418548929 418548937
    0xf09120d17071d041506031e02090603010e150418062417100501030804030501062403020d090503030c0403150e030703050c100510080c01020f060610110a0503 70
    0x110307120609107401032119001c1d0301c9412944800803662078003003080481c103000c0c02070001d2030010b00b00181e00e10006a030040040110f42c03005002030f880741210304e40c6078186140c450020350b4600301541001c0d0302d2030024105000c1406422840060500040c9091848000003d0140d1028104000e90105c1110703514000420040c2aa085e5051202c01800b4401c1714039150300380000b22000c1c0b0101401c100b1040d10b02c5010800001c124810310f4107100d43e500303d40c844c071402107114001072642c031865031400509451b526480f445452048800741c0c00c04803d0058084040c490b10300d00103949201401c40c0100510301c04401600c0c5100110400101d20103070f44c0180156805005403040c8080319020344415104e0312071001c1c0781e80d003082c4500c10019000e01c02030081c8400300c005561056030344d2162482140c074211003401c40c0100e14901080f0614062000600100d021f2018100c680c4510300d00d19903d9602401450255585480d0043c556125000c80700402e00e156082d00c40035201810304590300c1e00 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 418551429 1250 418550179 418550203
    0x50702150408010b091005060d020408030a020d0f0306030f03050c1005010b3a11040e0405010903270e07030603080f12250302090a2105160e010306020f0912 69
    0x201c4c2c180241e2131071405444061040d40080545a1400d007401c05021030b07900901c06148103241c0034040400c060005001401d003a41a50740140601822843c0040070300701030300c412100f031615064003400400c0301205d1640c18150582031580d80c406d442400d00e860034645c40380c00c4417124500700000c41c0204580740240143c9800d501c0100e100001d8051108100b400d120031011028060800318441034065000118592000301001e8205541c0b00e1110700c00324011201120165900c8495904058100c00d11414101c0400000308140c9820b0380905c28142003070284904507003c0d00c0005520074802c1d000301c4095644111929101c2004985140040d004401c070090aa00828006070000500181d140e0400c5030030740c803010400a45107020b4009501544240390052008080801c40c100e01e1003031040c10040440741d000000301c8500300a4107000819481c44003c41e0000401c100c80624000020b0560381c000d82c00581d117003088400071115104070400241c12401c5519810700c80c00b4042440b11481c0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 418552679 1250 418551429 418551431
    0xa02090d0204150314013b0a0c0906060e240c07091506030212241206090c01030e0714060405191d160c03140309010b1f0807080705070215040801 64
    0x1080f001c50040c241d407003030f1036901800c26a520550340800e00420341c40d81d50b88440b00c0302114401c0c481900f1824400102001c0d07a89c03600ea40002c0004000d0b03842401d005004070700d451450b0300305103030004c5c00052210210017801800002900b442c03014800c1120740c903001c0e0030100c9545a50703d81400d8007a0031030150b1504041481c6030001130060103070007224407040020040e100a5507492042c00c901d20b508006040100340300b0b030685a9a61202c0a5a5030609a950010328461800c100c4d02c62030141a44101c90405082160748401c08900003880420b0710214612440350151a5020410501031540a40e03403004010018007079910180c2201c9003500c0d000d54424181680c0c06200d428815002d507040f00310b040310340440540f0140309505098415110380351561130710280d90000309141e0000c0c1e4a003007050b555405466802d00c0c220395400002c0c00d18803c1142000c003049009414800d0007030000f0140807141d4001144a841a800c680555034010502c08601b00c03240c10000c150342103401103036069 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 418553929 1250 418552679 418552703
    0x71106061804021f03150e061005030405030d050f09100905031c0e030414031908040308070201030f090803060102070f080601061b051504060b0409020f0f0102100504050105060f01090605030a02090d02041503 91
    0x1201440140c3d08c981c9001d86030701d81c0788182590072076560348001c00a503820300040c0706003280148140a2540a41d502c000300c0001c9081026482d4207090601d40c2080c202072030030340c201380042e41c044141c590340e040081c11404003026020300c034009011540780e1340c2014000020f0124000713000383c10502c000a03060302215481e0403190403201c0c04032411203010f008001300b4002040040d440e44020108640306250101d004405191980c007684d419401c11034203044040100300c3c01d0b590403c03140b4014215280c42a140520b440995911030206000b05000c01c45c14030441056941102c0e07014a001e076000040394054490442110b0001600380d40440300d003401c0410041503031502d4000c0e1104590010815030014858004102009880002e418150b0244407000c4e10405041d00c11300b44503a01540011a103840c1c03120410001c552440c40d45410310100e100144881940202602d50104054100503640c4034108005214410f207050025841401c20b12660030712017195603503804580c4928500c0c80d074 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 418555179 1250 418553929 418553939
    0xc09011d10060c060207060906141b040302010c020f0f030313030c090501061b031b0503091302030408040306090507090c12060504062304060914071106061804021f0315 74
    0x1d4a6041c1c80380d14000385101c0b114101140f100c2d030042a000c0d00c1643d0009958480795150001d4460050502528440b00010451400c0380624140d28003642884114601030455001804044200c90040e0040300c0c8000e80004545503860b040d007240900500302c0f501c4d40040d900c3c803060420503000458841901c46800241551a030155605070741d06c9480700352400c0207041840c04417078038500094003000340c455201a80654080681e00000d4050130103956500c0c0c2e400305100380820b9000b003091a8038410003c20010440100955003560b9015201060000d0107003442441c5c180190800c0040d14545002002c01c035400c0300c00030131440c052417014040d10b03548004100c1214541d114100414902c2010060301d0102c00c4007502c0c1001d8002c0c800103243e42c039010f421040725041e84c03890081429203000d1001090b04558a14240d05006001b00b122346007207000f203001420646042c4100b00307600310200c0d0440d907600c1c001d6080480c4c142c481c101401180d040050140c081c0b0b50350906025013410001c14 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 418556429 1250 418555179 418555201
    0x280b060a211b060903060f14090a0314040f051905031002030703051b0f0c010905100222080a0b041e0b060a0801050c0313050a05030a0504140402190806030c09011d 72
    0x304454942d2100a0385170300e980c4440000e00190300c1c4021002d0368a40c0c0341040903511084807030107425850002e02504502d4600500300301d146c001190720089081c8000c000c4410002045000e544c1c0a5078220714005007900f070f41d1a0000e640d00480c2d40340c0039500d01c1c0c460340b001c254081c62140301596000d00c02a1502500c04207008468120800100350802c44070041c52608402850010710b10000000c0140035519071a0030a2610884081810340002d8158651220072103140e69400c10200a4141c0a1402c0e084940d10406c0e890020403040c5a01d0010301401124584144545c50210030503c003802c2d00d241c100990001200e2613880385050b0107000c2001c0c541441400d108010040398546191136001a6000004038443d080b102881001c00380b000007002440902500805902c5a503240c0781000d8440c04500c0c070140b142802144140444117040400160031601444030381411a240c0d1586000310f800c10403c0301d2800e030085091000044c1110742540c03d04070034030000350403440c1c548070308284c04 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 418557679 1250 418556429 418556483
    0x110312060a14031002130f080604050105060910050f0103060504050915070c020f1e0a0b090906010c0b060927030c010c03051e070306030b010803030702280b060a21 72
    0x5805a0021007160421840d5178003c11034480c0c10f01d500d218242e52100640c1c500c0850f50021f0099401240901040290900885800140c02c031015922072904c0ca03004402c0e401c0c0352203142c2c0706144030040100a6400703071f0300410203030a0103401800903240070200383e0307540c0c54607454410000414200040002d8403811000c1203195000302222a42c0400328108030b83c03040e43d42107251469031000d0304004d4680d600340b07800009100101c0980c0e2030b00d015504005800754000c00c2c0c5814400d2400300e940000e00030440040d44103004503140d040d103490350401d20b51340810b44030045924586041c0d04800d81000040644042007842000748403401400001703e060f26401d4840c03020509100440c0024581a6070005500448518002800e60303a2501c4012840350700303a01c01c034401d400000a028020794180b2481081200301d020a03104501003114015a10140c1040503000c04c138814003142c1140d4410800d48010003180b00b0600c1680e1704004220515880000c1c200c400b00c60300d03040e00c092906442c0c89a = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 418558929 1250 418557679 418557719
    0xc0616152c06060d0209061f0f1403270c04110903011503020603070f110a030e0f090919050304030c03050c011101050f060103020d0b191511060412110312060a 70
    0xf50034104e059401e10a40e00c13030140c02d684c1c1c071a0502c07494001c0c40320180203c0f03100085940c1e690000103500c60000d050a8000074030b50501460802c2040544a4080300d80b105c1c40d0000d0481b800781140101d405801d14035560901d641c45428002c01e000c1108003403015150144040303000300100704601c803401e5004281488025000181480003410040c060154011488001d003030619070b02d00c20412407402d0002c1408210049034420460320003e041c0304029000340c04041d0341821050400c0d2038925030350390540030040d0b581c0110392070680c00c0010500c140c0700103580c01120ba100040d2079142a80d00d03004000e08081c0001c0740001e00707919411050213501e02450a40320135620949550340110b010394003640c000700f0a01d40700c82c44100c850721554411018500303511500900c1604080f0300c0d405403032410140c41e007081504900080449004180207801c41d901800c240d84481c1181c01c144d44a415018008115020200c0c00c200301d1002e203020355208050071100180200c1d1660309200d0520004090703 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 418560179 1250 418558929 418558939
    0x708150105040305120f0f040e041505190c0504031a01060810060e090411062703010207170a0c0b0c0904201215030a0f0506090c0616152c0606 63
    0x780d0031518440ba008103d031041c10740b00c01e45411f02c103180c400090340c4554040c0315010946400c004c10300c0000c02c06400c4e00c010b820710521090503c2c0b0354440484890341560300c10640d0b40c030100c26003140584116801158008a0130310b202184145003015683d00344242c03000318412000085184042d081c0b1602a15040d89810700e0390304030202440510100103000f00c07035251410307103454155651407014008241c030400001114402e007407000b4101e06195400a0701036801072203001c0024400c80d0100540d8448250126140d011036401242c01400042e00640302d20000d005000e0f5a00800c0020800300c44283c0702030042100714481280003046550745484824802c0c0a2104000b82c00200c503900440c581506481c03140030303a80041d0403c2c40b40081245c541043c81d002e042007103c1403004943c01482000a441805004004941148038650b014040f5203c01001c0ca01000b400412950b081c2e00c50881c01c0080c0740c440bc070365666081414000f50b6031030700c04803142e103020000025518450080a01 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 418561429 1250 418560179 418560193
    0x2120c2b06022217030f03060402121807060c080a030b0d140c1e090c071a012612160204020c06070c0c1a12070201140708150105040305 60
    0x2800d400030000a08121403112880140402103040340c00904a40310010a40062a00c080c000c1c3c41d14040503540710340020001c603001e25100c404040191219881c100d120a035a90340c1d64000a0000e100702100801045213450601c4440c41048003003c02c1c1a0f581401ca0354259240d001c241d403e142c0c81c00e001441c80004102d0310104034400d4000641c9000302400d00101e4000c2980c0d40500c42e005022064000d601061024030b46107070403410307400d070702c1d40d8103803032046110144c404618028401070206000450009140040004800000a611403e05040c022550b169038070201e41e642202141311340825070841496001c60003040c0c02d201c800d28090340510704100c5074402c011001c1110804daa00030350074007000443c00c505020341407054820b95618564601c0a02d0a0700315106ca542140720104219010401208a540c0440d415905009942011644e51082c200e001d41010207400000c43c41480910100e2078200c83d5403800b07886031410004502000000440f076501462100bd8002d41c4944 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 418562679 1250 418561429 418561459
    0x30c170f030909070f1b0809010909060b0414010909090b01060f0e0d1101030e01021b01140106090506070f02030109030305070801081612030207231306060509121c03050402120c 78
    0x30003030b5210240e1800c0c090702c0d035014150060b00250406e4810f82e41408006141d6803290303448084000540701c0b480c0104200c070305017160341002e40298060341508821410311140300340e003d0500180240b451000c1030151028910f42041100d0b828414107008c40c407918101c006481c0030362801c00f44068042c0c514070f40c5124503200c0c80a9414011132080c18561742e0790840c600d040d400c1c00107158000311003480119020103900e140f401c5030030780d2918180c585107050043c44855400f00d07980044a40490380941c488031242426041c11a45101c000d42c99841c08600108040d0140c001600c20400c40c2c440303000c142c1c0d80e004107030b40f03031444c0c01d40440002c80400303010700040c110f002d40704d19114020b10448000c0c0f622907103501da9100c003c1400310100c118070007a200c01d510700034a6850554402903014000c992a00e0009001401103809035442203400b20511020310300100690242e00b024501d0000c1e0034038040b0b8000e00149030540d416402000340540c2403030710100018000d02c50034000781649010741842 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 418563929 1250 418562679 418562687
    0x1030902030316030327110405010e1504140103121403010621020d050108100e011803030e0c031b090c04050603060d031403071706100207060c030207030c170f03090907 74
    0x100c0c2c0840506a0386d040d4014280c1c059039144c965004d1401030129035107820f08100c101d100700009014891801c1100501c514800140020340208400b405060701021560000d00944100500380c40040d201e40000028400d588080302c52260003512880742108201c44015240e21007401104003081c15115008030407080b0001081440011000c01420010070489201c2620301c01ea01244a0380e12109121906080c10303c5480300200d8114000c02102580000c088000604000e000c1c06043e66440c0031402c0020610003505502401400c1d1929061400354901020702500d0000340200491000245161007080844050750070090105086a54071801c10403e0540758108404010b100d5000342c0710035011101860107039259464424000d501c100255a42c074070005d0801e40306c0c100224074440d80c140c01140c41c1d825212145007056a158080c10240d18155403a40014040404c001e80090741482612040c0001c2c0c064034180c614180d440940240e50b0b00035055403580c0191803002040c005409 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 418565179 1250 418563929 418563967
    0x7080316020406030c0902030601080a02040509061201020d060b0c0f0109020d0209100b030f19050f04020118170d110303040b0f060f030a050a030e1203040e0c0412030504060905010309020303 84
    0x801000800c1c600d440f6641e0005c00314155014440403500801030100307640e08040d1860b444840d00031b00310304191418001541544004d40190f005404010120f0865071080d0102d4180f40c40c64401845603076516980c040c01980710316103440d20b6004244940079000d206000b0f81064540051219241c01c6168081010700507010b4a016070100910340005043c030718a801452140314002c40c04403d41c5015000b04001d0701c2041140d20142c1d03e03110030400b060303c2e6840190741003502841d110701a01c020b04806880c03e88160400101d980c005a02070850004c0001c813507003040c01c0c0d03a071156249520104010390300e00080c0d80003015554890002440c21a0410303a41d0b0707118000804540011040e100801c0c1404114502950107401060012040c19082251401420001d86224420003e9504041e0b00d03802a8000ea510300c0c485000845c640d1500c101c203130b40191a03410420307013031051a458054261ba0140c03085402154003071000041541c021710030085200d4003d405107107410902200c0d05d108680e = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 418566429 1250 418565179 418565183
    0x309150e16060302120c0a0912120e1005071202010f060b0306121606050a14040b070506070203400605030708010b0702010e0d0221010b0f030109110108070e03101d07080316 76
    0x7064000018061988618864500f40240184034040e100cae8140104110480f90006014010311170b140c421981d8441c0231241241c0e00b01000042c00c0e8110101280034005c9000c0a20300282820310100d0580d10100056000d401c04440c4410941c1c0c1a00a407034907140d0300b190403030103190008010000c0710700442c01001d00c10024602040030303100c5004179030442c1d082600a850300d45c602080303090400004015860700000c85000035405c1c081e010b492004038070b000c403100c01c0d40301c1200200882e50710054042800c003d040e10b844661601c1d16198010002e41040b12403100080b4040000600440204100c840f13035074041c1c0d01c0340712410704a014408a070f03828800880e0002c2e1902030700c4110b90420f40040f629040b501002041c0f01e4440c00403c80c8455a2091b014800c0c1d2520420700c0000d0001000414546020309011500d59070f0301c0c40540c1e030f039420b140c80c507505401002c000429000041d8060040c64500880c040303032184d6440c0031070b80c6d1050f040c040c03610740f070f1700c200b00d5440510300c083d465810b014 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 418567679 1250 418566429 418566437
    0xc0a031a0403031b0509040b010206221104051e01090507020a02100e032a061201031b08030c03040317130e0901060810020a03141302010309150e16060302120c0a 71
    0x803c2084861101e41d0000e01c0300065000b20b1b04910b207291034001c20f0340c409400d20007490317103050410b000003d13017030054900d04410340c615121b074042250110b038a40e020301005101300014500303c807070024249940001d10764100e10b240008103c0d10b1951042d2030050405500400d900f5286909210741d0210006a240c240054144d9074400340e0340400041200130b03240070640244040140c15031090340c002e0203200f131050b0307030902c40380c1440360f90301c0d2000e41140d07004004000c0c401490000d0f00140c81880d045603030385000000303034403581480c0080100700300d0703200301410522401ca10700c20f10380c640540201e0404e03d69040c401080011402d0b14513640040b0b000c1c0c0000b40742c583e203270802441c00c5080c0b400305242c56000f00324013003a142c040c4504486801034a8007003007103240405004e010343c007100d900241810303990b0341d50758240020016200c81038207a1501c100048210040f150756a440d04d01d070b2136410340d084d550b00442e8062007402607130b45000c90001210100c2d160107444201581144900e01e00700 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 418568929 1250 418567679 418567691
    0x6091d01151205040327060804020f0a03080706090507230906030f0d0309200112111b16090209060d0513020910060201060803070b010b0a0e0907050c0c0a031a040303 73
    0x200030b52152900841c460345840104001840c0d1011881008800394805d44003039580170000b031504001d0507980154100e482c045540c0c08540001c0c10104107820240205101107428020000c181e40100302141c000e030111540b0139a0761540c0d0318001e14075880a5201043c0c80b0860f212418003140003504024024151041001c800150f50319016204600340000790312080040300384000c038090340f0f11158441a81c41c0a0806400000e0450300e2501e807511082d99581c4038410016244c0e4090f250500c40410204844a8000da4056030360191008030401a840e50400082c4407002031003151110b031030151070141401c00a00c2c40200400004089901030b030b043c1d511030401030380c03120f031410306c01c02c24400d620b202d00e030030010000c1c21503c003078100c0c00b0180d1080010501003001e00c40e02604496850000503a29842c1020440740c40c0400e00360380d504007419806110509400001804c0464080002c45941e40c84180400c1140c000500c40a0000d41c81d00321803201c1d003803202e038100350322502a06000c104 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 418570179 1250 418568929 418568957
    0x907141806121218180103080d02090a030c06173601050403080403141e0a0210060e011406120f0c0c060702070314030711120c0a08010606091d0115 65
    0x2014080e1018451552001a640ca0188100e84c002c0c6071041d81541e9503c01c0c0002112900c0d03454406001c060040c42c8041641100c0d00d101d50129022104040d086c400720740e980b03180c05210002d0a010340e2010424a29440e4010783ca01180300740311301b4203e942d801c491102204200f00910b0101e032520348003140c813109811003403400d00600b805140f10740c2c4c0e40e040c1490903041c020414017000f40c0b60105918104089031400405003004c40403d16000d103c0356a9403902c4c84140d281400c0c1d40d0409044a0a002c00082d540c0390700511241281c0340484141d0140b8a00070070803625100701a044035001003440042814503800302031903644654890906807800c929061014a8404200c45007001a402201d00f40200a130341e901b60000d8082c200c000794140700050351003034080d03d90280054006c1c0c03001858820030781c9041048014441001d003207681904d498420b00c40c082e15072806000c000c02c4244c540010703030140c003031500e20503c280007208440310b0342050b04081011034040441030804c4840c0601d100 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 418571429 1250 418570179 418570183
    0xa020f010207110f0102030f120a060e04210908281a090c0d030f0c02010e0a080601051002070602100b0f0603130b0a1a010c022106090714180612 64
    0xb2110f010324000ca0b003421622081003c0c0e00c020003013440c110f410034403c040d0302080c0c2000b612039121010780d0b18840366403428a0b402c02418a98420701d0008100000d100c00d104168120550200030445035201491a034502911018180d03c01c2e03100691181a00203510018401c140c62071060704480c00c1c0c1048156115048100a04400c0d540c0d101040c0062080d10b00003082600071a4a05032a0300c6403d00560310064a04800341c4441018412001309280031a0f00c2402c096a03035200003800728004540755205580d4681c1d09001d4070303007c0c0884103109040c6600000b400011112682c0c0101004001d482d80704e400741010300041a00301400c0d07007000000d0f680745005148107100543d40002104e22900b003400d10020090040301c1c8542c03a00d03607a44e001440307803490300c4003000c000c0c2061036154529101081200401da82c00d1080705c0880307014503050200108910b0b0007200c401c411180080c0d212200c41c17402c0b04400742c007107078030490340902ea5101e1000b61440702d600c0080240b0101c2c0c050a8100118 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 418572679 1250 418571429 418571437
    0x140d1502070507080712080f0306030a02030f0109050c06040b0318100908071e0507050411130f17120412030e030d02061906030203030d09021f020309120d0804080a020f0102 76
    0x41c0c03540c126083c2808010b90800820004041240420300c410601d0b031640803c51050ba250103030300c03050000c001191a182004001801c0c0d5015040380c00c2d180d100307186d075802401071a1086841e0b0041004600c0386107011800d50301906d1407407100b146140c90b102150300c4c0361448242e9144041c0503483c11029201d4052007000586801400318940e21592440c2000c28042060f00012074401e01c00b2a5601155001a400c801c0ea142a83c000a942071610341550142c041c4206143c0a05202c01c0b01041203014030307425004564140034010a4541c3c40031401c0d8840385140c508098804080c0004c01c50203c4851400038500e0081c00c29408040c0041c02007400e100c80c3c0003040300980d12160501070303141c4603081c10182c138280362901001174a0641d400641c892045198440100b0340f40c0159005541d6840205034a8404400e4528031004540001039240d4000322203c1c2d210b007e1103880c84081d014003046d104000c038080d40d03464001c0c0c0c2e01ca5441d00301c95086400c0880c2103106108040019200903c010 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 418573929 1250 418572679 418572683
    0x8070305030109060b161214030c0705010b06030c0a300e1002161506180902030d08091c200c0a0f030b130602070c06120605040501140d150207 63
    0xa541c0ea50304040031001030318100d511103959400100701001e54a489084150b01450748071201d641c0e80714011304115014104480700541c101c1c4000140104e2850501c01030007240c1c418002405500d140c041000003e000894203090412010844180503d110303d04101c6510700c02c0c0703085d4244002040b0105444100c50011510480d0350300044168800108850100d46400711815442c181d41c9c4041d540c04070085503401400c0140b84803c918424100b60440b00c064200b944042d04150b419918800203071894000aa010780139922481c03c10030710402c03e181c41207203848024590724000d02c911440c140c12550000c42005011003410760318242700e00e507240201c948000144001400c0300c041040304541075100201e66545035030104005540c0c544034a91007000050041d4501440d81403010181c883c50700d004100d44040c01010034a180c1040e80303030005845800081002e56211018081143c1c000c1c0a081260111042e030014540381c0b000c0c1d01c581013846151401c0d681551000000182d030803041d02 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 418575179 1250 418573929 418573937
    0x80c060703200421050a2a050616020d1b030c0b0c072705040b040618020303030a11270112020901050714011b030608010c080f0604051003080703 64
    0x140000294140181c080028402c402c215620414650050551140d44140c004007130b20020901108401501058901074002c3c0c00e8444d01880c4e490441e5404c25000010081c4608040d041c5054030035209114068038800341c0030501d00341060308420a10180068101d80c0104007200e01d100107428602c2c000144912a85004800c1e401c40ca8420080f80c0d084e000010016014002402204000102c99040703443c1d40103864070749079000030000044110316003140c19250800051204214227aa03170140710340d01883c400c100310000901d66a00c481c00465001e0b5050784184040713002403a20f80d00844d6040071902c001c52900884500d050b00d58000019051450038a1002c81d81c103e5070080d1202a441c0c60428046107086034001c00601a8008c01901510209400c84009a21802580142504002c6108841c0f840f05075101c020054070303050191300001d50900e941d80c00114003d900c45070041c0e00300c0d4410f40256840b20148001040020000c403920494544004041a1540010708155000f555 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 418576429 1250 418575179 418575181
    0x1309060605120c06040911190f08130f081b060f01050f060c0a080304080403060e0d09050f062d1b060f0103030e01080c09030d0306050f0105210c07080c06 68
    0xb004045001c00c0c480307400d0b54101101401e01c0766554400c031800d9640314040024050100b20107410940500c2c0d030408040c00c40100108105c541100c2400103800341c0790754100c01035403294560f900000301380400810001080c0d84102c00100c054010742041511401810014078414031814035110781501e010780c00002c08001800305040c030380d6070300c00c400f003054406038906000328400036581e130008403000e0b102d00c1d0040041020008008115001960807072002c1c4103c0f404c0b540c42603100c414842d422800704000080000c0c2c1ca040050f04c5000068005000e0b6082030800c401c40d00c0c540710301030000c0c20030844540900c849052a5409440405000b0307241003c400450020030386041c1c400340120500c9004030004100082d40003461031154a800c3c41c00c80c405448a41c544135035070064103211075041c0111110200e4050789a03006004680c01100c140c0300d60042680155141c1c81005a0030346010008001211440c0c034110b00e058021030940305480c582005034460404580103417481c001140c00c088 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 418577679 1250 418576429 418576439
    0x10140f0f0c0a110c090a050f060316090203040c1e060801090b1003020a020a0b0112051b0f0d05030c0109140f0c06160203070506040306020307090f030c0504050613090606 75
    0x2151240d00803000e103011500350410007100c40450003101c52882c200410204801c0c081d010903c0055031100d0302030034102e030b20f05040030120083d010480311400071508000c0003030018500022100c0c600c144a4030101c4e141c9040100404c040c0d48002d0090b03485585079180054030b003540c540300300c071001480205074a1040c184503004045400c1a070101c0d41e881d04004010266607184202d00a103012a4180181c0d1a02e402c603050707041040000c0c002d03201c00d48040000580c000400e0703190352510311a8090b151100c108000e01a129441d000450750000f0040c1001c01103424113031400104503008404890404100c51090ba0945500d41c42c1162206601c030551848032400300310a200620f00070020381010905400400c00a0144000c80716003100d4543d40202035407010301810015010141000b5a070b00d469043c6003000c3c0d44243c61180004a40500015001c5a2407245500340d0398003004d407001e40c074a01420400903207070127846554440d0b41100c405070800e40911829045da071280c080815203d181c0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 418578929 1250 418577679 418577701
    0x9190e0f070b120c0a0206012105101b030e2e0c0c12050a02060c091512070e030601030510020a0504081b090604061d090a020d060b2419021014 63
    0x2a1402204d0002401518100e40e004500641074801c0585204a54801c40040180722030039050044c04034000d02c50140da541c08030b5002400621000702030a002e01d40d80b0b1100b10f04481e007103400010745401840200ba0740405031035507640c100c0c110801c604030085e01c000703080044030311001ea80008191035600c104204445018018896081400d2141c1000d25541d07000e51034002c001c08000c15854006203020b483d59421000d1004108094003050300d803050741451041c46041a940c80c1c0104201040300c001d0740c540051154180e130360140142800d013920603485c00180d0014207141090203403e00001c0f42d041d10421034400f81c13520104880c001420380006109554201400d51801141801d10510200320820a50401c54440241c031083d50303510454024100060004020750081d02070800e4130a21102c0d8100a55600c4101d030f10400c0042590740c201c008907800003203101990b07070500c201d001e604018104140e0004250050307502c0300710b4030038890b01202c12aa118031040040e62042c05514024 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 418580179 1250 418578929 418578931
    0x60e09060d0308070807030e0f07090f0207120e0105042102010f09080318061e040312020d0e0105030411090907090b06070302030910050409062309190e0f070b12 71
    0x240c580300705201003034800810076a401000d000c28820301c203000c542031b103110b5400001c03034a80381000d0740c4100380800340b416194980d5104e010702d105d0405d080034440441620840d00c00a03840724030030004090010341920400d40e8503c0769818000c082c0030004002820320200e855880c0501d203006209000340c4005020300050100319810031036250070900c00034500008032040e50b000c002007020901d9100000855503c40c0c0c04400b40c20345442407040d0041c1e0040c4019206a0740b25061040641d0041c110480e0ba40000c00e0030440014401c94800d5820350040004582040c0240c0340825841c54407030114510740c1041e51881c5040c6c0c45014100200c452620a004600e14100c030120300c1d00c0d6250320001e689015580720a4407031750503120f030a84200e001c1e07001c80c1c3c0140030350031091082c56561043c2c03510540d180580101c445183c08011040703031400c900706d6845a00040c0c18800007691880180008181e4102d622280d803092301c207000c0b14203500300b014400800031541c0f200c1e5500150100090b00c810 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 418581429 1250 418580179 418580191
    0x2030a0b041a100e06071a100b07080304060e010906140709050103090b180312090c040c0f0c080d020f0d05012105061b0d0912020c010e0a03020d0516060e09 69
    0x2020352400002d90352000100341d0040407918028281300320240c0080c8041c859003c0c0280324415403100d81c1031201180040e01d219015080700704001c190703144002420b41c854080001c100c024100005000210b03070b41d0204200119040c0002007070304141ea680c0080301e805a685450803012801041100d940c4502290701030b020a10f418068120190f580d020100000b922440100e0800034480c00090701c01c005540c2c0d80c0a480c9814005030602c524000c2d00da11403040d8141c000ca0074015130144ca14043c0c8441d0440e01d0842d0384581c0b1514a54070346c2c0c400c540000e508508000d8003000042683c22500001d09420500d148001075254075149009042c2542c150810101104880895000c01c001181032030740105081000f618a0400c106445118031440e00300e0340d401440c100264043c030101c05991148000103408071103c2000707010054900e0f160220303da0354440d03c05202407005040003d94280d02500c140308452040e80c592111900c0c1d69110b40140000070071400442003549003030030390950032407 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 418582679 1250 418581429 418581461
    0x60f1005030f07030f05010912080603060708010e1f09020406090509070305070804110a0f080f01470406030b070215061309030e0303030c1c0209031f0f02030a0b04 72
    0x1441140200c0d103d038030601c0081d000c5c0c609550b0340c40c1401800e41004811903446016034402c82d01010000c2d02564007031315a10702902c01c0000080d42203000c0c9602905856030102c042002d036036002c1c20140601305840c40198105001c041c000b038000300314000740c4040d01882e15003030b09440c200024000c000c5801816003003014280390a0201150300440801d41003038200347c00b901c44507919400300d05600d20540c400c2c01c449103074140c00a00c0d8040880ca000e40aa03201c4028480304482104441d40c48481c41012010b01c0c04c3c014550501242c1481c242c0e9084801121740c486150306240080c1c11030345076620985480c000c5104002e8140d0f4180000710444d2200b02c4181c00e94101600030800322002000c1c01c0c82100c1d60307411280c003414015401c010309004014102c070359a00d04800306001c65000600780701403484a0b0340308408021464001e030703464144058020442400e0820305490030038114400c07800781540c1c1d410b03010260803150000b9441222949004500010700200344811584a8041e000110f = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 418583929 1250 418582679 418582693
    0x3020901030b1e131b05070b060307080c042a05040f120c0b0c01022215020f100b0a08010612020907050903070501211b02060603070305030a050f0c060f100503 70
    0x150031440c401900d03010f001c0e12501d0703400310600155002805032450807841020f0310f4034240160b65002c00180309841c0f040c00009640e44941052503650300d510b006240268102c00b180f00001d05203940460759060080c2d041c602c80d4014541c010603a200d40e084e0703903000200e0014041c0100000c4840c0c80b401401600d01011000249845d610342d40103e5000380c01c0012000a40004c900100350142c42118a0911042d001806040c40e25082c0d10b105120707107070f104c16040402403409800850400c4c5030048001c0901003640c0841000d100600c1111246548990340103030108000303009104a40143c841d1407180c04000c00d09004006a82c60010119002c1090030850041d4545021034038404495007824141c01d03080b00007100d01450030a010301500e0310351030001c2881050b041d0401405061459400741c403515200d507000d01d078407041c2500010741030768000c102c0c1c00c0303640348241d00412061250140b500e052607111107419080000544910301480c1108044c070810032034540f20100101403c400a1441c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 418585179 1250 418583929 418583959
    0xc09051e0c0703141206090702010c05300a0c02010605101e050d150e070206041a040804030c060203130945150c08130b0714030703020901030b 63
    0x40010020032441106001044030b10401d80940c00c1c0c4046070410000b0380c5d850b04d6950003000c800810403100c241c4502c107400042100503006101e0400030500d65034650345040c424440901c2c40255910032002084094841c507807540842500c100c0c0507591040d4049142c406501c0002c0c00c0d40c0142c1c02880c403403043c1640c1580007607001266850f4510b421a1020441c6084100503030300343c050030100200107418194000c042c00c0159641800752044800c0c1c80119880740b0388100d9a90700704440c010103010000b40b100584003210700c1245e0b800751180544600e032075181c0d51060251350b4207a00c00c002680c80403e281c0c40501ca2126040050400b02030200542800507031603500300c14017070090074814441030607140444d4544e00c008140496019522200d8034256241c000d004881461303c40c44c06a2070110400d10703240c0300b0b080c2e880c010300380180b074802c1300f110710744440400e80d001500d500309002c844103031801e640c0741ca00003561040040303840050b2075510640016040d42d0b0b120220324481c2d03020f101c080c20 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 418586429 1250 418585179 418585231
    0x504090311010605040b0a030209180f03090a0807030305030103080f0403150e0c12060109021323130203011d061801031103100207051209060c0604050106030201320d0204030605040c0905 82
    0x448c0d40444108140d03884004104200d4500354866100e40c4c041c0070b01a1100c2c10000000744081c600544030203055a640d00f60381516026140001400918108010400301e01010094642d201805a002c2d1900c3d940755580750360200a00500d0a500f034903003200102110040c01007400100c0240d5400b5100c40300b41c1409031300c95005010f0300d40707000e6001c9000011504107000280107808081c50402912090b00c14503044201c03250069440383e00002007c6a00d20014002d6034100c0d82024105004e07119251207085c20300300014642600208401a60003191184824640c021401030100c0d241000c01d0000b0302d41032034407413003104003464010030051000940000788101c642d10500e480c0c80d101c0000c3d000054003481041d000850910400f01400144403065001e4401c680c801d0701d0b15092407020030201c03940d201c0f11180003190441601c00038550300c5441c2c0018011814500030041c5440e48030380c2c4407012204140c07000d44e0803a422403000c0c8182d0015118198105907040d5a07184100c1a0035807040b = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 418587679 1250 418586429 418586449
    0x924140609060d02010503100509130b090f0307030f031e05060418030c0212190b0105010206100e04020d02060f04120614010806070f0203371d0d0c0504090311010605040b 75
    0x381002400000640640b18000d1028027034200240b071040542400e0f11000b00c089a080804d0310051000b4001c6045e4600024a506241c4040d1029500708042d03a24180ca003039150040e0041071549516031802426543c0b64080c0f00440f02c0800003406080100c10302c422510b2202e40320803a042100001008290800b1003110960740c121281800003c140011034107110143c1805504804d4401c0c02c50100646025502e0581e0000e0782110303480d40c0e07030000e071844625040c070078800c91031118800328001d070510483e100c0074a030015100c0343c50072206000e840300796131142d070116114400107082d01003008520b00030303c03030010741480465040e0350610502c182c03980340140030b600504c20900c6035400c0b00c80c028015282c0b002490b41c10b12440d800142c042040340509071500040f1608103801c8514124000c0401410801284a0070103008800d00c050181c5041200001c1d240400e4142002a15558900030704090f540710b5904d00095071600412a030a4072455040790344580d041541e14011500c400000c0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 418588929 1250 418587679 418587683
    0x92115110d09060b1f0809030406050f09210a0c0e0402060a200303070903031e02030901030b01050702040c0302040f080c0d08161b082e0924140609060d 67
    0xa0140321900d07161004001c0340030790319000b0b5105001e80e820248101300800085505d80c803030250955444080e6500c0380b01e0b9001d050042a000d024083e0009020b60142100110203020503e04068001e8182e50040003d00555400ea210115290410820821040041c90351304801d01150629070b000a8103030240307060f10310801150a040c2840030013500202560313940c8000540c0c0c0d4a0030301034801880354030349010540115074125070320100405482c00f200441180b5a002d541020500001140949440381c0c5150420000b88101009a502d51042c1000c0800350388005075282d03d014001240c0321a15031214040e500806207000583d1181940120340580c00a441940c604403903a500071020f010f0b0314081c004d180c010051501e6104054070320410307100c1c6581140c0c010610448109113108034940e106815014520054400c0441600300d200c50314131401032842c4031401c1400300b5030403c41020042000c40e85403044003a80101e10440343d900010280d9140d011403404201180c1401e090000c0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 418590179 1250 418588929 418588931
    0x6181c180e090c030f07030b10030c090c1d030c01030b120106090203090c0a0e04061e0903030f11040501020715021f050601090603020a0c021905030102070614100f0312092115110d 79
    0x9009ca442d00f00001000d181d10001c45107015455403403640040490340c14401c007003403004008138403511580d60002c03250100140140141700c40600110050242c18081301c0d00250922601c000c940000c3c0101c902074071200701c0042c0c6078900b00c10102c0c605040420143d024403207248003130200c10707032821031168001d801c83c80c08500d10a02408c500c06d1040c40c4065051101d25248041c000c05505810845441c45038210502000c100d1188000f124030a84c450716001d680086010005101448480021408103005845603c05040b41d8044002c0001c0c1018142171307600d004000c50b540c0c001003210b01824240c40d0441c1403a201410141c0440480c0001074810000880d044002c02501c881e4a006450050004d5403101850701d00030015103108201c18100ea03810000103498070140709070313200840c2c543c0501d4040052540e1100311a8804842d4104100a04440082610040011031404000c92a54202a01c0d005070400c101e01e0040f541c00c0300741840c2403541d20b4103030790706910a981100c5080c080c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 418591429 1250 418590179 418590181
    0x30b1513052d0a0b0d050411040e1005130210091703030c04120501241d06180c070b0114040e07060e13091707020306181c180e090c030f07030b 63
    0x83d41c810391a030054508800010320761540000d240c01050050b4411035507002800808010803041d00c00a0b2035810803544100e0b8618003291041d04050b0300142d410a1004400400d81c000c83c810002e40c0002e50302281d0ba80800700518866101c0307026280c1144000386041d4104000c0d2000306100b180305050540c2e85608061040c0f050070350007107002040610b800c0000c47ca500380910040d03180c5200d0001112900d1304918030703400050329124403a100040c640d048107039601d10f08114044014081c009144801e01c2004000f4054454150107840d04091285521007030b50204026910400303003400480e000f4900c10003140360400b0003984102e004032070300b1110242d9120460003c1407000740207094030b115004107030341c2c03001400300503c01d881c000d405980301c5940c0c1e14001040d10240c0101c4103416400003070103180700900a40c1442c4980700a107041d800d211038018901895002075005034112205250a10803070300d10030041c0580d10350096014110141c0b050310280d480e19101e100140800744c10b00 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 418592679 1250 418591429 418591519
    0xb060d0506120a0606080f150c1b0a1a160804020f030102130e0a1b0207030201120912110601050d02030a020405072304060206070804110d03030b151305 67
    0x56460600c0c0710000c0b080f2075140180c0d003096000743c00c0c030380f250980a00a6119201a452010640a908104400004213903807143d0014480c69403000c81d000c0b20b0039403510044112000c0c02c0c08004c810300c0c0101909992051075004030040000042c1981c0c2c205800300704144900758001d1880b590054048074110403455640001c030b07002e40302d04407115103c0c101209002c42e142e188144800e004a001010400020000564a031403000d503c114000169026036010030041d8400c81c580e0711106003860000c2620200d6540d910039041c10940c44402042c6020003c220310101000098010041240d6034001600c81d0740110780c9425009a001e0f00031900c17070740010941d078050010103aaa0b0401050100419004030300307042190858041c42c0018091100851120f500c2000c40500070751300074094003801c1d1b8149003000060610381000700c050580b543c2205015581ba40d154103d00f441c2c0903d6242e8502c1c00c1c071000c480c0540c040d08801d109000d42070480c0480400d0300f1002000100494900071444158 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 418593929 1250 418592679 418592689
    0x2707080f0c06071203331404110d020c100e06151c080d1404030504540606030e060f0c0a0f17040c0810092a0e040819030b060d0506 58
    0x88201c04188020f12020004011b03000010b5201303e40040d500080c8001a400401068810100d20303544103035000e001e402c4c2c11040b540d00424044800d0422200c00283c1c0710006004d9580402c003002c019000207041180100108a40d030540c1d0200b00c5074111a014a030f10300c61082c0d0004400540080e001240a0b40503c250b540114007505400360740180503d811311340149154440e02682e0b050101c013003102c03116100c543e040c040300d0000030703056001c0b101e0600d0403c3c59a000c41422048000d5400ca0a4010780205881170401130031032a980850000c40250300946000030203050403aa00c5d64100c10484418040025030310004030610f07003174488680d8002c040310380c00f211a41c2e1000c4880c00c2c001f40020003500100540032074403550184c80c082c810014507070040f192200006002c100c2d5507403103c902c9280c009200d401c035581d44035042440d00e882c1c00606491100072074007103031007844c005881021041e1450081103040401e1030144280390381000403901c140691800150450745460101e0119665 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 418595179 1250 418593929 418593971
    0x80f0918010906030213050f0103080304020d120201060f05030a02030309011b06060b030a0b031b01080702010f0509010b090c0a092106020c06060a080a03082707080f0c06071203 78
    0x4000c0680403036584030b4100784001d12141c030040b480f40c1049000380003200510b0045500c1030182c00e10600c45a860b40d19100c5055100402c100d034010389808031103000801c200000150002d155000043e10390419a00603004469038104034031075400548013100594000080301d1540b1401c3c607008440c20ba90a0340b481c02040960301c02080182416004580c0038892000f4522400c001c072424040d810354901407544490244019032000902440c3e143c24950080304210740115561000140c8482024440c50407079805031104641039440301080d0301d84d450003282a503002150f00c204245041e020a40c06002c03503140d4443d840c2115840c1d407411514502c11110070100c0307908903100307640e1021b00d1548907860340c008032019446070301407000c045842e5100080300718034183e1503200e04856132038500d06410550f0907440c0c03141c000200b10b01c0440f460303c401e218900003008440001c0c0025407100c04201d003003004103801c860040d84180080004180c0d1b03688010f50140399810f00040c0d051a43e4018400200 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 418596429 1250 418595179 418595209
    0x70b09060d0e100c03050f0105030a020d0201052704060b04151103070c03080c060901180f020a08070b1306022e1d030c010e160303260a050a0b0409080f09 68
    0x5020943c1400a4098000198040c0c10f581d04014a6845007074071540b00c8028007032281c140c0c3c40b08501c03a00500341000c5400702c4500504001c1c4c1013400c10001c10464644004030700d1850600e80d941c420080c01d09010307200207054485c10341401c190a10304038188011429501302c0800001d407001c0507c106090044a201540028501c2c3c2c520740c603420030b869190b01840004c20b8a00c200e10000b191090107110710004140c40e0514482080304940341c000010404100603030b440740140a00090364202001442c1c02024080140c903200d1141e5001400609840c5d84001d042d90022203940300300d24050420049282407012100da0b00600c0c20700103070000c000041d40d1400c20300080034840d40c50140003002d801031100c298000c0c403001d208640c20701d4175050b642006400d1078090003010b000017405040500140003850711103030310201c40b9422618001d4010345888061030307a41c000348030b4403804c1c2c3c0c0114209a1000d9409000762042956207000c54460345601d9040c403540031403450250358a042480103128 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 418597679 1250 418596429 418596433
    0x120209101407051603051005101e05040f0e0f0607020607080a14010902040906060507080403140a081611012d0905130e070f030b130303020706050a05010608010602070b09060d0e 78
    0x4401c4c40d0120282c40c1e5010a031141d104032540760b940035110f8015144103038102100070b0005442d1288080e0170007015802401000041e070f6020030305031035509c201e00e06460f030050301248000c10610302e0f1781000141d010320403994200200300403616400142c02900f00d20315190040040d42d9110b40d500c003c241c003003005201c85a01324000601e4400715009841034a00094040102e2a502d18041d40e182c4500e650040038048140000c0000c12007440808401e00b900505841e90207925550312002640900010408500c100ea10182440044210994502000c1c20180601c0b443e000c6080041c2e2131103071b00c0c0b100b0f8910748a4800103075480360f50303110010034000c0e019184516000c40c1d5080a401b410402102c14816428001007811184803000112500500d44411685403c404032101101000042d01172540030008007000900380d206281c0304042a010010762941440c02c0200076002c1030b1722920441d480800140195034258089480003001200c1c46d0b0750b110807682c080005842c1141790100c0038 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 418598929 1250 418597679 418597693
    0x8190606120b010812041202130204030203030f0408010f0e03161716060b06070213020a0302041d040203120f040905060a05181807060c080d090803010f050112020910140705 76
    0x2440d030b84641d0685443c001036808101040c20014058015842414910790104c442c0f04050b041c0b000c40807502900c0200094940347d2203401080c40c5a00c07071103c0d0180e13600002003c2181d00c0080c410b000724000061018400ba86064107610f960380144030117070320070040011551041044030301040c290482c855410700d4403103285000d404051044000c0030b4880e0f9080c241e5001c414580f9504482e040b55004001c205112448001c3c00000d42104240c181459420040852411000c1e0b952080d4000300342c003107400c249082c2c4185428040031031000c0b60701c00b400707001c8900c840750248250b03001e032400a50300043e642c0e6844c0c001400219582e00c1030350080141810300c2e900604900d44244215005c0c0103008000c1004503000b80d032880b0b50710910b00050007628440c000561050014400e41403100b1000c034105000d5103d880301a0700030b921030041201450010001e40d6080445807402040300d0700c0c11403d00f800040410034400305140050104480d03280c1c0c1b511046a2002954034640e0814226110 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 418600179 1250 418598929 418598933
    0x3041503150e0a1b020c0a150206010e090c06070609060b010c0803010506090402040308030901020712020607020319021e10270b040206070606091a092a0c0102032703040819060612 79
    0xf03802101d1b0009010b6810385070081801ca40800301781904001503030003001942e190041641c0900e0000d0f007585110b00414a40c40300e150b544401806c90140240310029647d04289017500c200d420030924241030045100308000401c1d00841902c0c1182c0080d201c440d518880c000001c5d0091007560401402d0340300101c00d01041841c158090f105241c403030161418500c52406040e81d0383c0700122190b00040c1d00410141d00c46001000e480c0c811038526004640d407182180400060850b622000c9280640c8502c2c9100e144042c0d0b030007401e40c030a0182c1441004201405403208010410005c0600030700c11032004281151102001c49040603000358040040a0302c6050a4024003010350199101504040d81c8001a00c3c01c00d41e03143c060308240740703001c080680030b4a12000c082139141a034650b45200388600204c0140c28002548188490501d00011004c0700c2061694200a40c8041c002d940c0180018040e20100090a6040401c4200314004481152034842c000e0000341d00304500c50b49a11000d503003 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 418601429 1250 418600179 418600183
    0x9150201021e210c07060c0306031a0403020610060c06020c15010e0106140f1b03041d220206180a09020d0516020d021e0a05060903041503150e0a1b02 66
    0x28008405000c0798481c00f10395080e48080003400d4800e40340c00c8008003c10f00004500381c0c4005250300341801c0108441c1d9903070b122840b05000d0010401c80c1c1440c2c0e1420031081550510009500c03010920340b00c034802c0d040100080030101400c0f0001d00030b80d0b00190050741c1110410583d9010030720a00c00001c99a15079555140e4031a00780700310404a104e44601803501c9003000160303101d880a80c86a42d060250100a218249160383c1100c08a400304000100e05860f01da202d1717248249a11901160782c1c00c0040d80301c0c04514921203120407405c01d048401d40103966a030215007124002e5a035075011240002e00041c0824082d0340010081403000034010680301c0381c3c0c3c004521480462451500c50300b4411003c2ea281c4072800361102c0140c00a400840c2e03030001c000c0000307030401400707001c40380d02c10060303541d45240c944283c881503d04c0d40045401c12201151100704002080360707150910181d1003011807203803040341c94050210340508180019103403d2956011183c0c1241007401003400440005e00a5 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 418602679 1250 418601429 418601437
    0x621060b03070e190b030f0109020922120201020f071109060a0503071511030a030e07060513150e0301060f05010e042307021603080301050108090d09150201021e 71
    0x490280c00c0c540c190040349030100d038031021110a000c00c100b9070741d18080301c885500f104000500c480d40d6105401026902e00300b08a400701c0ca507187c00061443c5490040000c140b8008000302d41103206d103407074000d00e2840031980c40901580b01c050002102d82000c82030f0302a0103a400c504090f400c01103039400600c48400010100c40780159501c94541c0c5a400c20300240d00c0c00e0b40201c0d609944004001c0041d0848a07003000741d40301907807174405038080d600b156040c04c55100c0000240029250309681d1068241440038000401c480d0400a14150030040304103850b030103511501084500c3c01d285110404c0c0182d001c0707640b604009000300501e503107500c01c280782c85005000c4c40e4001071310070001c00f4460500340710351826100800d8507040d0004983d40303840c8022030010040000c6025517010550311500c0d414522010307520900c00c042c2c07a981020700050000000038842100c0758015000040c0d0325070800b8a01090344c02245881d048c0b60a0303454180d02a20424102811004040164a09000003d4094 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 418603929 1250 418602679 418602683
    0x8090a080d1e1a010503150a0b192a0f0b040b0a0e0706081b120109050a0f02090f012f0f011107020112021303020603090607080f13080c010621 63
    0x21a48454035001070040700d40620021080e4444401c00f14070759805040a03503840303080b2030710035940208080081007090700c4030707841240f04200108070a20407108040e02a01d1030002842d01c07120100c1070540e802180305009610301082c144100f40c9000740028900c2c00140b60350044615031250600c0d281003100010100c41c154a4545010b1402d1254400441c4044c00c442040da540082620340c83c051400b846d1440d1420b0300960000c02c84894220031210815000b80080d14000505103810b0090f5415903001d00303003030344020744100b0404007699204000802440400e107813400045280d00712200c01c7c1d000c80d541520104100d0020303c6041d4000250001c030300010000288047c2c1d8513100109101d000d5a04024041040809100c44480c0a503000e4401c0d0a10007002d4411070f59a90081400c80d401078401d01003542110041094440c2c00070002038101d190b209114565280450030a56142e1683c20b00800380140000d542101c4042508008040c150011914118241c00d546422840c2050311007 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 418605179 1250 418603929 418603961
    0xa1a0405180601021b030a030305150414040c090908030f090a05011a130203010308090d0309030b0403031a120c0f0a0e010f080618031812010606030506210d08090a080d 74
    0x1441700540080c0071a9017079402c042d0040408100f1690180c014103230003020780d400941d95510b880074a82e0740c0d005940b5180740c2e4941c808164280341c10000c101903166040035001c5420311840a000070130b45000c403984110030b82000c00c180d440300c8070024144030345001c000e4031540c20041d01d50441c2040b1410f1010908003203c10f52030468002520344240c0c00248000f0f00fc1032720030300c070601541c1450300000303541a00c24509090300306e40380c2c0e03103101c56601e0503030341079000964480c0150320303544109280c4090148200c0d10074858155000c81d0540e40c5000210090042144840c0311000b0f4840d0381250340941341c2103010409544c1c540d2840e101c40f020310f21640959110f2100854900b031140c10324100c050b11784101451030220340c3c101ca000d00000c0694620341140180401505d400001e11031000540426a40800c09081420800c008802100d0400ca1805154042103010420000e002c0d8084111410201941d60344d421040d401c0042e859005044404005400680c80f08544d2005c0144400290 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 418606429 1250 418605179 418605193
    0x1b041e021804150302010c080d02030130022d03010f020c0c010c0f031404091503060c050f031506070c0e0f010e13020409140109110a0e060a1a040518060102 69
    0x10401503c01d440305561203e04403190501c095440b90b2080300d00b032401004c40c0745c0f81045030b958010803a40240d100b19003c1310700c20040418110302c44401c608047e90440d1040e000181c40c4c00203910842070380d0b60074002e18480c00120b0742c4044040101405010014000c000d8580101b040c40e000c3c5d8007204c10405c040c059014460b803698014131172041115048a200ca89a880c156019140003042d940c003218150300621000800b00e0090141e081d91a020703407071070040d60f40386140c95020788141711405401e100302032040c84d10001c4103009895101200172940e5a650050901090340c0d03109003e40603000b08c03100103000c071b00c0a104c0980e803801081d1213402074000d40c0ea41c040411800b6004e41d8400400481c1071403480241c03030a50405000140581d102450308094001c209084072421a01140c554400442c1500350349840e40f900002000180c00010b6270340f901c80f0000e400070b070090140c40e480354500000807000c0d1254005a802406001c1c200c00255540034155440041d0300311440e600510400c0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 418607679 1250 418606429 418606477
    0x2030c0a08060705030601021204080f1005091203060d02040e06190603080702100e030613140f1218100809010c0f05030703020a0201180b18030307021b041e02 70
    0x808101241d2200000d030000752101c10046030581e0000e041c00d411440384048200301450b080c0001c0004182510003050751000502c030241c1005080291200410f103070800f00134403201c0118541e04018803a600150b034940e100070000300c3c102040c6d1806500540b800034841091840062414040d02c16015558041242d0000b00000e40d103590100818441080c0a80e10041c20070700e5212804019500f40781d1362880c200b8001c20300d840011200d01c20b10f14200b00200c8140004040d50030040d03c0c00b00007510304444034071003459440042d03174407850824000043c1c5001d0701c0c030700f0300d100c0d507221a0003416403080521561005120312001d8548444a510380408500310602a188560484032261505421942c40400c1540250800041042955218244488080320404e03600754a24421203224a0300d062120b0147c420200300c0c0e0250a080e031040007803011180d00041c20a2440c0b01604000104140a60128002d400c0761142c10421460b030b1003840c1005080ca4018021001c83c2001d01c00b640903500e = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 418608929 1250 418607679 418607689
    0x605010f15050406080601030f09050c040c08060901030f050a06050703020a0e030102130303050d02090a09141b070f1a0907170c010e12030702090a052215051b0c030702030c 76
    0x6a000c01c041542000100b018034010b045035680610141000100d15802c0f04018040c2c6020701380c211001e8020750f15260044c986846011840c0c409441c0c03207401c0740342c8040401d820645c103000c042d11100d00c90307585604000d020450309603000d07800742003441a400c00c8203014001e9042001e400c40460041400e455032070405200360741d81c040034040d503c1074007443c58074283d417154010014000e0041d02080007402c030fa00c51212080041c41c01c440c00007030054443d01ca0100d0400c010b060005100742150380c59040e103541000761541160000d120380010b51840c90031500345004410b074080302096250402401c4180821200112030f40290301c1000000c1d42c41c1c580b0f448520064109000c1600300213461300340d0030004600c240340e8903140c048a00d4160560006074040c05d08603000400c840e10f5404220310340b15240040300a00c0140171008000d8401992400c400c2c0d81e11010070000c4a949030300080e503c1620391800400e400c0002c8209a07204008810075403a0b50044005034024450812910044d05203 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 418610179 1250 418608929 418608959
    0x20d031a0405150303040308040f080a050601090b0a1a0d0608010c0504060e24041e031e0203071e1d060a1503060b1603020f0f07151205040605010f 65
    0x41000c1041031880804000091601070104003110f22488007059154804100500255014942851b251450309904c420020b403181c12850b0503404c125100c500140d000100d00d41550404c035400b0401c42030b43c00220b180b02c1c0c42c3d81e04c281d4914511545194610701c01d10010050021098001c2c0b02090700c806116007039544585442e00015020001000100c3c8074550801e04940c0051820400d90700b410303180e4400c510300a4411102d4480094108001d98801da00d0048000d560010302101e11316503141c44110700040014018041100d41300c0c2c50440d5420f00143c40900b2500315030090740b503080209044007002c80c1c010801a5541504045a06010000c81c64030503800203044c40305440c1421100499004000400d00c185601c80e0710210f040065000a8a00c542e07860f03c10b600311a40c07074100246000e1086856500c2900084080141a200424140140c07070405041c002d011110035411114080c010303000948991514080c44104a21500641e048810108481c02015142c0c1005020189 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 418611429 1250 418610179 418610201
    0x1f152706030b0612010608030f03060a0602010509030405090a0209030109210905090402150d0c1707080f160207080a0501050412050310090f0b030115050301150311040f020c0f0c01020d03 82
    0xd80302c030002c0c80b589041e2003581c048030011400402d0035980c2c2d0700400d266070413034801c016240740c0210400140f400c0040c20b000041c18244020b02060030501880e903102e200b6405824000c1c6100000141441181c0c0c040b220922000b900810202c052801c100780400219040800301d078900010035003480340b05450b5001619801412091340b03894550030841107440e455141014001d0600180701c4201c0c89100b031302d0f48160591980300540c006007042c0340d102d54005224400380310222040c0400000c0c1c8024459005810317503401d06032141c0c160010303440d220a5602154091141c0004a010440e040d00f04a0049205541c1002039607200f01707040c0c0381030008841ba100000b0710120100050701d06c1d40c01181525480c2140026106a801c1c08030b403c1d14001314450100f804616420020360a0034803071f4a40c200c250306c0314041400d081d565003d01d802c0c01030403910f2066444004c4001c90000340c3d81260003061051089030911030164000c0d0f51a03443c645000c41c098003038504040516406401080b214038 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 418612679 1250 418611429 418611443
    0x7080c0d0c03112e0b090c070510020c0c040e0309030d05190e010c0303091b1d0f0613240e0106080108010504231f0b0301051003051f15270603 63
    0x80c80c81c04101c0040283c1c00c0f0504c10701070325034048240c19150300c40d05500a282080c0c0300755446865082c9035140500d407041c007440051040159800b030755404910f40e02900412034010640c1d00d031142c0d00a14502806400fa80d25015400100710400c0d0170900420a00100140007800034840390015540c8000c02d48000d404111803411040001e40700b94458484c0724428100e84182c56010b95001d001c800c456000001c0d07442200c0011000b00c0150510154045c204507082c65a62401e40301203841c040003007254072240e9481d00e00c00c0700c0841c102d84494072004564001c00c520155200b600804600003845030341c0101d6242000031802c5034040c00760520650300800741c107a010b0ba00c140000390744004400c25500c18002c2e02210400c0701101c80c8004000001000c0101da4074074504109800c65101a20480c91483d210001300001403000c80d50401c10702040c00010700c42901e801051016021444034044444000040030035590069804424810100110225168904201f020848455000c090300e10 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 418613929 1250 418612679 418612723
    0x41515091a15030a02070f0b0717010501120e120304050309090f010302210319052703070e0c4807030b090307020a031a060a0b04060507080c0d0c0311 66
    0x301180b4004581203420302000521780003060b1910a05d240860340200c038683c1d01081440a1903900114651948ac0d4402c81c13401554074110011307000c80c2114080640b003d45584541640000c20b100400d029584206c01a83c0d81c50103180c80368403984883d100c58070650401000c6209030018041190699034098498062410302c11070540110750755135a000c40320701c001c03c041d40e182ca030004908100c3c111562121a254400b1a691100101901c2021141340448d8a02e4001c0c56500041240403600d0b90451540c15032035000c0c03103c1440c17058401903c40c401c0c09501c0844c10001c0100c0f180c1d6682c101ca02d80505100502007030142c80c108440400304207a1000c001800403032888140c03560082800000c4914258203607002c9106031519600695503d5490031411501256080340c46038040c0c01201c62910940c100307081e4004900890003104c042000c0803c40d070701040030a40484054140344c0c822510340080740440100f10025408044001603c0311404034030000000a0031182c4c00b908a01c48440 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 418615179 1250 418613929 418613959
    0x150c06091e0d0f051c020a0804060507030209151e07050703031b11091017010501050f040c02070e040215070b100f05013c02060a0b010e0d0b041515091a 67
    0x4290002c03d2056029060b005883c0e25400e406d1008014603075461b107038211240707414101030301210401000c0105040c010050b450b880d94810415851400c03101c0289904e0308040e90000d006003422940300b00301300c000000d079030007804000102c900c1101d11070f03580c800c42000300ca51109402c1d514060010f081c0c400542c900d130030625002c0300d411790080030144485589551806280107203a021100c115450755180014800c5003090b094414203410f064030300703000031482c01800035561000c522035000741c1204c06000c58110355400c03510b011006103960761940c80d20002c0c1008581408240c403c03003500e080c41d80c0c0018009001507140001c41d00141c4855040b17403000303e46419490100010101403816640c0e40b00c86d00d2800780668484581194014003803803070030408041c2225075032041207060140c181c5c20b0001558a03a40700e681c0e9990311842600306a255071404038035014200501c28545400c1100031080c4808080301442250703810309061028000d0820103019440050121541104580b0380a02e1 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 418616429 1250 418615179 418615187
    0x4060e072301020114010909050c06031503010b0301020a0e15070213060510090303050d020a0504050a0303030c140705121804062c160c03022506080f0f0402150c06091e0d0f 76
    0x103232590103601585c119201840001d0140d6108031420f028141c500c00c0500940c1c1030910035040e07008019802140f41c0001c0728000381c0b10810a080092007111949020803000c5514010790f083d40354041c0c080b0500e030b07261a0181028218038041c0300d02403002d060284025501c1040c0e00e07006c803501500c40038a0300343d0400300b1402a5222403494428884208000241d58840101640055000e6503001440b000300f808003c00d05000781040380002e500910001700800e8000c52600400507580503020f94600b42c101202c5880d001a620741503009181280c0003070001400e0808101030380000c11640b910701e03c40800e51000205c00d070ba2500103807529030425441280242510b2030f0550180c01110001c28010500040a0300c08411811059241c2c2d0010464030780c00c8036005800400480010341c003490034204090040000a002921800a004039030004000000440e0b11a203400070a079000e41c0b0f041c4202559481c040b04040d460381c944900c0b5a40c2c0032801141800d00f81c0c1b110360b540d006050068000312 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 418617679 1250 418616429 418616441
    0x1206040f110f0603040b100b1801050d0b0d050a0c060c08160c0f09020a0f0504080606040902040e071d0c070309171f090512130e04060e0723010201140109 68
    0x6074010160282c10110b83c0d944074084d40c411446000c40c0e01280c64034654095500040c1d40c04000b10500c103201c5201214107402601a4900e801c0c41d00c1900c0d026055641005851028003864000e000041e00350b0a0100120390708004a018001c0003000c29a9100c0c12a10a143c46101400c20003050190078440300641c0841c4c142503014480d0114000d13151039201446c482294804d0540950000c1c3d11050301c2c1e000303c0e400480098500780305040501e4118450b803105c1004259501c100d95600399101196619800100c800444800b16412070780c442a1080d8051026032800060744122800601601090021208070680c95541d800500d45490300541282c214106206180e0080c1ca02213145110310003201004960054004a005821030811904168226a0005d0340d00000c0140d03a1004800c800010101d4240001d04a1150340e207041050092610b4450100c0134001c0314400900d50100d41c1d080008041040c801050f0503442d030005900b260314482c4c0c42900652900010002808160312103 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 418618929 1250 418617679 418617713
    0x30a1403060d020306070206010303020f03070221100c090305070b091f140a091d010f1a07080309061009061a1b010908030115020114041407030c030308061206040f 72
    0x2d418007800d5400207042c81401c441c0000140d120000400030300d5410800c1c0d0003200202800b944c6041482d0b00482e00e00d42d150b809040700d071350409620860300311302004042c501c8804140200018500800c0c0100f900074588425101c9100b00c034808034100b2800021191541802001400380d420311f88a052201000300b03404d1002e01400c00c0c440007014146c20001c110320540d80c0e072220380160900040d07444244504140441000000e401400303010603014000702543c511181440e0085464142113120384940740b40108405004014030108400000d16903008180c046541c0008039118030010741100c019208122a5041d466021403242c9007010042000300c2e241c6c1011040c16840c1580786095904030f0800700c43c00710380000100100e80c401c3d2452818410148000c0c030a01c0404002e00c40100c8000d0300160040300300c1e103800e01381604100070788802154864103c240742d50790f905002d852400119801da000301145000d020030410045122449564480380848121140c4d407a256641d0342c41d050b0b5 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 418620179 1250 418618929 418618939
    0x5100e0102100207120305090115090e070b0c06010501030b150f0904140f0402090907031a100e0903071a091e030c030c010f061a0f0d110a0309030e03030a140306 71
    0x46407150005078001004440d00600321817502c9481784030000c3c110ba1006007000c103d64508580302c0500b00c1602101e8088503004140415442c0079001c06a0500c0c0c0c0c80c0d400064000380005108601d0600440c20034122038090f02c0130002e404038803050200c10302a44020410144003080340030360f064408030150607041c0020b00000313880106102c01e0104244152034030105c1d1401c0d44100000c519052aa0300e038806c40c0345015245585c510764403c0d21580040c1c841003050100d046c000b40da1a94282d139428000c245101050362642844944540c6a501001c0180c0d03407500603a8507107804c4441c20742c0c2d6034000d12250005106080c401d1031201920095801c2c00302c2c03140810002c1e9035082d41c040001d00344503103101d80000794045c8490368201c1110b03642e40c0600d5042c0c00110760080c00a01003003e0703904070000ca0000c6555207604803c3c44008200400c414050044041002c0070303003552540c40703005c005219403201c120698038801010782c1ea0149000e07000020343e0180c900d60303002d586c2c1005113812600c0640 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 418621429 1250 418620179 418620193
    0x6050c0c0d030302130915050405042108040c06020a120f020c15091e0f0907030605030714101707050d0b03030301090203101508040b060f0d03110706080105100e0102 73
    0x80041c41c51a0104010b40010760086020f0070110aa8030500008050070301040111107036000507040685490320070648039503900c50000e0240100304128000301d140003121090811015003020304003220079501503c418840880200d0700c18000100c090301c0c1904101003203070950203c1411607559240b042d03540700b14007580002da1415140e05598041441e041c0c00b025803540b0003035062201c2a90a071005034100000c0c600445402c0e21256841041d000741a50041d90b1a5201c420030740c05004664851a01403145800000e50005030056058040b4801c8540c8420282900c00440380300e404045200d80d0708040a003c5402280150000e005040c00894082010441070740002c5c11a002680309a1a49400004000c0000086180b4030080c0c0078003940c2811002803940002c240800003040184006102e20124180d81c1c1d0b541418002444c00401d80201644075203002041c1c1c000d428074042c2c0e42d1103001c0c0c0128441d4080d121a034142c0708041c001c10403e1200c040110b0300c0d0181c6084aa06500a0702 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 418622679 1250 418621429 418621453
    0x10509100203220f0506032d150d170d0f0203150103061a04050f0d050f0c0f01090509060405042d0203070509040f060c09090c26040b0106050c 63
    0x32054100321140340e000b0310707210981440304403400c0303501140d8000d00c90740d985424418070821071a428140e4000356502900c80d5244d14090104c40703c400138002c090405500301038601d203121090188101d00e0700d60555000761a403030030300c0b1819540c3d0344c00820240300844a5000100c1e4603001c0c3c9002c000702c400214100f00841c80d408100d030700990b035080222501d0200c07164a0b5070180101401440d640d042c5400c0c814485140404a001e24021580f0400e240c00380e180c0503645414001200540100588880201841d41b0b10742e0780005610b820f0144400b08144423444d8042d0300414111100074108510320781da018108001000f008004458203102c03400c007a0741040c14540c030520700050b0404011741b6044980105071801300c2d182d00451040b80890300b0040012183d1071100c1d99039610020110391010409004c3e5a41c03040e6030043c820861804c1500103029a0104030f6180f041407241640700e0782c01301e04044001d908011540030307043c03409490041040c0ca1144009281d0324010205450f2908005 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 418623929 1250 418622679 418622689
    0xb011b03030c0e100804120503040515061923030106060c0f020301060f0806010801050901021303030c03170c12090d0c030f09052d0f0a0b0703020a021203040e130b0411010509 77
    0x401c0d5400b0004174141c04100401c010040341034280125400d02900318a003070350350720b07a40d264000c4603210100c1c460808030740641c032800320313842500000b030140603c41c5403a800d103490130702c40d0303c02400354448848000c02c242c0d0a06206580594000c0d80d40c0d811101038540340c40c1c8070b4008600c0100d03015940c41000003801160185404050040f410181c0465407500d0f00080c2176402c0901091081d9104010b04400e2004558000c001c89615080030007041c0c0365405c050740e40034190380d00c0683d5039034400204003001d10200c00a000030040c1d91010790580c1c40d00c1c283c0c5561442c03c0360800d40803c11a10700c00700824024a04100007170382d986040d0010640b20300c0816010700461044100300e01007070212a00d00030503040d5a045540c015a46031039005004000616145400d204052480c24006a06014540300303004120105401800d4000d402d030310024459501d03401481100c4015a050b00422a11180c0000c0740c400280c00807041e502681312510341a0301155072409841c10312004210400c415128 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 418625179 1250 418623929 418623949
    0xa090c0914061206090606010c0303230a1a0609041104090606020105060414100902030702010b04110711060406050906090604031e12090503030403140f070b040303030b011b03030c0e 80
    0x500441c818071800c281c03050080301e480b454000926900020204441c103c00001e00a03800f860928103041004030500701500200040c115082d0f00412031040030900d50080440c80d40580c1900e00c041000246111160004945483d4015442076042040701c1d0741d490039800243c090780c801010746103055136035400c52041314007503408540075035105d00421101c0c2c9828400c5c00341061401c0040200703498010003148014095014010350203030b0100105600030301c01d40c0300c04440c14028008001c52280c281076440b0b507400001b002c94001d00141840b0f162401c3c440196000c807901a29218100039000080080d5070704442d40207900400b0030310000011400c90352462003480c540d11160030307075001e243c1000595410307008800d009100300a02c0420080d24000200c0b01240d4006142c414084000c030505400c0541403071040b00c062045040101b41c09074000020011a03110342c23010040ea046843c0155440e520012030021083c840d2003084020034080d422072000e03d1000e151030829009140001010303070344 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 418626429 1250 418625179 418625201
    0x18050106030b011a07030f090807031401060b040f0b0c0307120806091005010c140109020904080a030509070302010507080310030b1006080108010908042d03030509040f140a090c09 79
    0x911098100709008480440702d014280080051220424602d07040c0d20520400e400102003080054031450300e94800c0ca050009024024242c51550341c0d07a0a10046801c1c03100c0da092582d51070108002103488100f011103007184e00c5d900c0c1a1101c40d140520980d0b06400c1003c820b2a24001041944001100880115082c0d00152141003850411038140020302c400101010082c04031a03206010580e0814070341100f2a5001a0300c05114805c6182e007409845449030007500480a2000d01c010405910060600c44c1c000d5501008140e82e403161455940b80d81d88000303030111748100701c078501003001c4000460740042c0c540c500c0030029a0f00d0f03030b520400300e504440880b03504003011810301070035a22032045c81c0101800c0d4002d00a103a89516031182c0b80c03156218481401c500304480c419811800b100c2c0030080082140320500e401d6690802030030aa1010000a201c0d9142030707000d02d44a0303c1403090151450b039a107142140d690359100e01d035005090b1040c040c0d410086903000011000034a0041c940000 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 418627679 1250 418626429 418626431
    0x30813030602030109060612050108100906090209040f050d09120b15090709050f011412071e030506040e03070b01090510031704031b15030b0f10020c10050a21180501 73
    0x6c3d1924070000e00a402100741d40040d18100780042050030000102d90311903008403100017031552480d24103200280100030b8001e40001c0c1c00f81c1000300b48100500600c500502030760680305550030144044aa0724403038040ea2509410090341c00011544204040e58030420310020060340b034502d903000076981c04003100d0300400140c0140c0180540e040180c0518840c0000713080950130865100074100a90140b15400e1035031944682c0019580f40c460f080601600194800055180603800d0004011b80001c680881c001e500307045d0904004080001204e4030583c21401e448808d90a1004010203008050201c4074100814400070000c500050804441c0200d03807080155101d1039840c0001d40100800f038010007001d101d010400c041c220541c54584452102d240024101007008001140c441142c0b07640c42d000144e00a0328414590005440400d05c401210303000049240e65504841e01d100701c01c841000184c043d0080004107d540c0d02d5813001070305803203000c101d44108007541684440d40728000d403032903 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 418628929 1250 418627679 418627691
    0xe2b0c41010921051218060703022a04060f061b060e0726030c030f0304080d090807200a060c0819200705060a12060b0c030d0b09060a030813030602030109 68
    0x44000c101c242c141e900c08504280c00c1c0905800c6a03040703010f481106e103018000004603172081500c01c0c4a400c442401c0300e41c80b19a241c038002e42c81150644248072242c0075525118010498100122100c02103d28581d6a00182d1909152101e840000c0d07400450300749465903940b814092051280c08050900c0e14110801101103241420030499038015504542d002040141c840880c0442180d000c510404441a566200d500d809800c034442d941030340c42c0f007505e4980b081013082171103402021068024100f00c102510b540100e400302c41c40c8050010390120300d0302020008903008076400c44031107018408003400c181e061709424102c9070070b00052000083c0c114007491030500c0408200342c607102c1e502005160240c10700002c00d1a500c14400000244090a4000300d1104030762303045038014141e4000403d4640120300d180541d03d8200086142070242060100040c030b0820101c880d208020003010666901e155450b032404030350054107085c500365003030000840401c001d40007d6009001c1c00c9000150 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 418630179 1250 418628929 418628933
    0x415230f0a0216030b130302030c01020d0c0e19051201020d020d050106141903050c07020a0e0105041a0a030f080d0905060f160e2b0c41010921 63
    0x10030f07202088480b03140584110500200e88030f10101c2d5401041d040e00c10940b104135080680c598028046003201a43c00003454030361074000d5820000e4906800c0e168116010b00190400c4071940f01a440c034040701d02c005038200100d01e0728803940728401103900d0005140c071120319454010f9030300c1000c8400c0090307291070041265980c000c12501001e000141c0050600234007400300359409480d11928802c050302c50700800c100341480c80484484c0c3d0380c002d1154030044e590b40a802c02c606801d00c99540b0561034480f4001c103001c4054a556012980109601200e45c2581d48940c04150b407001c0542c0d81034024800c0015940b070314494600024095001815546006d2080004504000300700729500862580740e00013954000081064503103040310f0032000c000215407150380442405459042c402031050404080c4060490034005540801458509a088501403c45030100d9118503540da07045403c0301003034014440a100d04119014946040110350715030110000d130000c3c6100610005a0491a100b = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 418631429 1250 418630179 418630183
    0x1501051e071103070806041b08030a0201050a0f06050a05090a090f05011415240904060f0e010b0c0a0b0606040e091b2704050f010507180b0415230f0a02 67
    0xc00b5500c100c000f482054100039406464460161005084030848080c0c01013850144a01c070003c1e04c01c82e42100c1d199640884001d010700001d5442c4a811860300c01004406441e9006503030035150007911550030034dc507140070300403582c50052004400039aa01c0e4850006140c0542140d0813500480c0081600746000e40c0540c0c0445000e00301c0031400d021340c110002c003a00c9072960341c516096020301020042a060f190401c0f14490004020344c030514012000c50650501a0781d039003500e14400d1144881c0e070300d42d180c3e0180c41c41025030440e02940b200f40c40d0f50019003c0d02c0d035158000c00181c80541041d984c1c0002c12605081500c0c0c15400b80c00c61030b6280d4100a0514104500c040100d41c100c86c0c150260128200d509040c459901c507a0610100042c2800410484e002c514103941c00200640e1a09038030007482220421100d5929403449000094a120341e0341c256001c2d00c1504240000316400820261080c80070141201d90595081c00307111300b842410006801201020580c599680214a170024 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 418632679 1250 418631429 418631453
    0x1b1501080318010c1703090c3601081e0309040906020c060f01030c140d0c08010902090a020315060a03090b0103080918090309010c0309090c170702151501051e07 71
    0x241041310280030f000c0842d242d0f12882c05040220020b00303680e622000380d0340381407500030700215400202d0304400b4038080c0e02c040415035000c045802e104c1695081c2ca4408201c1410070311448070035500042c07082101042c900c2c1c501c3d03513505242c82101d140120070400320302582c071581c070140e609a5012854080072441800b0345a8090100500e2078074941c1150f0354000952558050782c00400a01102c500298445428200109412440b9504c0c1b2558502056020b8400d403070f01240146e5030200032520505d500e0080d00c0c0030f4521000c82d810402c0303608082c01640e401c5048034200f01034483d002c1c00080340603c1d600b180a54042c0511560320b899042c04d00c50a42215003600e9a101c0380b8504000844401000352100c01909103040c624042d080c0c1406c0740c0309005038200d0442149081104c01105400400b141481c040340046c03401c10380c2c0d80f41001d80c1c0b11700881d0202c51401c0c6003100052801296400701503010b0005051650601d246001343c00081d8034840b81c45000c1c60400100c090500108081c10 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 418633929 1250 418632679 418632727
    0xa0206030619030b010612092a0b130911031332010c110313030204021e0c0703020f0108041e1b08010506030f0606131a04020309061510051b15010803 66
    0x14814807202756500c0a2400e001c3c000c514041c1c490390809004c000d81604140b0040440740d8480351203410700340c3d541c0d1007030321203100e0011070a1400003810350700a54502034038482c0450444000500c4120340f170b0f0f031102c000b90307040c00b03503940d0900c01030307095161204420444010303000f01c00021180d11000015200300920f03865001c0b01d602c2808901d14a090008403801925415580543c440c500075860040c1c0e40c001c00d030311006013400401d03080d02003880080c051007100d00848040e4100480c0e500107642c00c1c0401e98000e80061096242c00308659101c2940644840c4a009604542c0c54082c2d101120300324103811541580e5105c600340482d91904201c44030143d07800c80d01501c02400e040000581c00b5070205000380c040c035181e0006441e01d0100d5010040039250140c8290365900c3e00465854603000700f201c041d8800a02c4c0c1c0950045410040140e48440b60b80740c84046c680311035040c1040300020388a030310601c144030b0421040542c000c40c45c0f09a0003452248002c5407645203404840032880701003164 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 418635179 1250 418633929 418633931
    0xa0c06050603070503120c07030c08102703050a020c040c020f06090f03030f1b0d061e0803040b0711121516090308070206120106110708010506030a0206030619030b010612 75
    0x1060115a90120b011501b0342d0807070064513076920a649085041015560000d4114100c094000a0204c1c1c049a4000360301c069040030001040503a2003184000701c0c41700042d0740301c1c020a0070000004d00070300c002c0c207400d829401142c40380b8a4000005040d2205429a00010f80140c3c110318203010b4104035036a045040c04014107110310b05031107007503941c0c0402041c8200282020380031510030200d28814035030101060300882d984401e074000b18805001644502201c04405404041d06a111034070700d2800d895840c40074615240c03421203503081c0703504280e200391541c003070001590240da0307a0700010004820340341001d40500c920000990440c81c0300200114054202c0184040f0716580c0588034206480d403000485803200302c06e0020400314051078042240000303658001052464102c2400c281d856400c01c112000c0079200d603074550907100c0599801c4d400d0ba10224143e401854050040d5512800150003508100707a00b600c3c0140d010a44d620642d07070301d01c00c10300500010380d1105e0346a507580c02d1004 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 418636429 1250 418635179 418635193
    0xc0210110702011b05030315010e0f01080a0b01030b220c1706090c190207182717030f04030f0801080c094201230705120a0c06050603 59
    0x82090668410201c000703041245482d40ba4030080380d600c0e0403ca2079608041100c5e241c0c907080c500c4c0e52500c441c0c82c070b142d40441c40c7c14040d04541c0c034140780b40c0344020f0410380d107840e00c644410031254003900c100b100340c40c1455101d401a85444e1198030400c0e1400b040c0e44805040c0c2503c2c42c0400d011500708a6622040105404c0c002260500312515560861816580180b0365074402d240d0740ea0901a004100103c95112500c0c0194980d0016188054622002e402c191034108202c0d0714080702c13100000810801180c84a0b0410086d143d822015098054100c142d0460041c1c412040c0ca54001c80707210ec07841e080d140c140000e05520010030712482d071190070190490b504000440703944841d800101881031103840002201010060240f04d4007081e0382c1ca280b60580c0803126900314060041e014810094000c0d00015603544c0304043c1c081422441c2140040c080d0f00d000c20700c0c031460344224410744503072280e10761082d2420b044000404203d012030fa5060200c9820780b41ca00c040d14000380c001c601c2644909 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 418637679 1250 418636429 418636451
    0x22030801050a053a080d0c1206060f031e020403030c061a090c07060f0c05070201031407080103031103071a040203010e0a1e0f0507031a0705031003030c240c0210 71
    0x111071813034a602c1000c0004084020b05003c84858504000c0075001e000c00d007215204225000381c1c0c48000a621600000354101c00302c0001c841c500c5c41000000380d00080305100c030501940c0060103181e9100a4400100d187ea0800020f0f03a1150b8401c0780000c854000310410b0258501c51107126601c1c001c0c210454000f500c0009400f031202a210410504c400076140c0100610390707005500e01c0c62840d00a02a5400c01000907040b5048240b060b4003203420100c0740c85600c030f442c0700d43c14800c2c40c0d16101c0b19145e03401c5440845030b04c603020f9070b0340100344002c100c442d01141000d0f140c0384e0681080240000c191520380705060946180050401031507006030819400140c031100800000a004020301c10261924101050100000d010251050040d150040188180d115424074111041e011a14450b21080011201e40c80f00b12441411130311a040e0920010303100d00e1501503114012030705400d079005100c0001035180da4644880911580c0e42020038bd20300d405020545451141290802ca080b01c00c0b = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 418638929 1250 418637679 418637719
    0x50310020a02030f030c0915180307080d11100e1c02010b010e04021e1603230d0504061410051504050604050907110318090c160b22030801050a05 64
    0x201144c0c1003908004000501d14501000c150341540d100108084c401d030043c07801441b95a400703007070503190720b120040c1010304a080c0041e02e1012501e4a00003480da145800b1001c440c010f0602a010f0900d02504410400300035050090000e8400504081c011982c950050542c1c989064000d200969042c4800e5240c04c2e80c1080c08009400c0080c2c40140e666014200c125024003080d480b0100104008240e11101c410310500029000b40b02c0e0311001c1c1d5103410810140c4031015a40e086101441d03040005c8940410580c11444c3c00a1040d80e01003500c02002115210320b280444246401c00035142c8108200c3c50451a514010f0a41d01d106510381400d00010803424899800360314080d00aa902164400e4800c61044da4001c0010041c2c0303840d00c04d000314040d0a00b005000300b9209000800100e004502030300c00312040c0000751450756903600010781e58401e80400052072510040c001c1a55a96102c40a0b5101d1520303034400d07500e800341981040c00f0001c1a4000303802640c003802071040702101180d52 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 418640179 1250 418638929 418638937
    0xc080604050f0604050406020904020a08060909030903120a0c0f0b07021015060c0f080a050d0c0305060f040e0109120906081305122d0705010c031a0415030c0f050310020a0203 77
    0x84d64040341d55516070502c24080e1280240050b042031001502918144e48800600e01904d801c640407880343e220a81d020350f0760301949414541c9508041519030001c2c000c403004101c0b580036400c004003007004c2921040070020700b420082c3c4003e143c10782003029440e03040c0555404516001010404200003294034010000f041c00741500388a010903040051101c407040d1041421b03071081940d40d9426225000820582060300c417840fa244c1001c46141c0701900901038a4402d450141406a00034841020800904041d10489940e0f558680c0350780041022503400400c0340101d40c0f52500540c2c94620005c003090401450400000f24910810000490100d10080340441400d101e580301c1101c90001d98800020402d0540c1d04900781181c1400c80b0450300240051601031002003201051200054040d1140340c4c13182851a00c2c00f510840840c03070950322008a03444030407168001030740c4030703038806081c5501c54101040c3d078004450100b0040c5400c000c0300c11340350348407802507083c0340c41c40d0030195403401 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 418641429 1250 418640179 418640191
    0xe0c040507020d0c030327030207090c080705030a0b280f03052509050103050c0906030a030806040e10110306030c180703050c280f0306030b040b040206090a08010c080604050f 77
    0x12142c6520310515220b81c00c048800d07c0d074485a40d000400803030881901e0701c08101d01718098090710100055504803842400341c2d801c91038803401000d03030710300800711800d52000309212040c40e614031981050382ca948401e008244000070901c0b00c03820300c3d540e60022001c080d6010303010b2409084403e0000030070100728040800f08200c0610300548402d40048130b90009170b0410740200d03180500001c01d1140c0002d59000c10a81a01e0484143c1c88040a04d5120061281c0c080e01080401d00465050f05080e446035100b04400c80c16184034224080340c000607180014440c8200d0b00c804821301c0322a00d8203010191010324115103560181480e09500289c40d0001031440040c990750b04001203403070120400322220350000509401c1034440c1d40300a0300351402441c000c00c00141e004103482400501a00c2510b050f65000300484505607160740e10100783d20402023049030014810301291909465418140014207407280c00804d5400c8000402031446400a10341c5100750704050901049410503518550491 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 418642679 1250 418641429 418641437
    0xa0c06050c0c0a080a09142808150105040b060703021509151905070e011b02040f0e06070806010c020916170a0b04111e1803010504060e0c040507020d 66
    0x5070760a40d00d10303480d000e04808001107000d5208000e080081c01c2c1d000340b030b074401c241d141c82c1c0f0001e440d10707561000c0900c1c0d140055000010419000100c40701c0d00100360304003910414000e20340c0d4842001c0c508000d8280e1100514a94910040c00300d0b140c503004000e800203055602c10300344031542d1002942c40704880900546410013901080c0710f01c109001201e92070ba8004501c842030309024040c0ca036400c502c040d04424440c502004145c0c444c0c8030341c01038424031505075600c04507403100030051200c00320500d00c1242c1c4079030b441c0300d440901448c600400750301601c404080d04141c604000040c04400c40101418100b10500c003011005a443c122200d800110094043c0d44003440084140d94400003200c02c43c3c0580707000010041c046880c2e420400e410034090360148842d52f21824440e2580c0502c1003040004049418048030101f14500680000e1242d180348402d054000e8000c0303802c40c0d07419141501c40a8482c4543d00d148041000301e05682101943c00708030b0707440c0050380203442e1040e0740d40e0b400c104 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 418643929 1250 418642679 418642681
    0xd0c0308100f0e0601020f06090c040e03040f0b0a080108011107060509010f0504051b010207080706050a02070b07050604120c02130209060708190813050d23070f0c0b0a0c0605 77
    0x508480c0d000c14000d007103540e0000003103d4440c059030000340030480e40c490040c41105841d10b00d050f00401c080d40141c0c4144020310040510500300005028075a154110900c001d000020360900300c50020402422800040d41e96a00320600090884005801c2a64603030f06041c0d5010f501030010b011a1207880e0040000200354807204d0941d801b400c41e0f0350303110b500d80703040c00144030520101003000345154001011803c0d41104071401603031a0442c1d88070750081c0f504000400c2211138010340050502c04013a2040d640c0b19912118407036100c4c0c20003003003500c1c0c56002e681000101f040b03450340da0308803450354103250203401c82c40d40c000750030421600410b07241c40c0d4001c90040002c1d225042500d00c0294032a02c00780d00c60305004000341c40303903241c040b40c0340c0004c1040c3c010450085103041c1c080d5840b504000030f007004010044d4180e900100d1000c1c19090043c1107070804441100000c00307000c100d48a60300b88100300c1c07084d04080c3c030b6403013260f0049070b040801000780c00081c0f40c01170039a0550580c009008195 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 418645179 1250 418643929 418643941
    0x30f03090308070309090501151b061409100501051f030f0609060909050705040c1205060a091a0a0501020c010905220501080a14070f05120f0304060c060b030d0c0308 73
    0xc101940c0020420140428034000305034200c910308080d51440201004542e0342e603003c202c3c45003070344c00c100b00203e4400341c00c84800800d40a0300d2400c20380241d03408110341c50108000415140c04640c14442e5401c90441c003580d501890040900525040740d41c0205042e40315099441013017001030031010b059a800d000b2640c6405070b08601d00405184900300f0038503940720300000190410400889840c012a1340216252030315100c2ca8079801a90b83c0d81400c0a01c495141d00000d1101410703080d40250078501c00514000356010741d1640021007105006468011401e11903980b81d950011410754200b0701d05081140d92010240046440454841200c085041d8504160008642480000b11704100003c1415040041c42c43c0d1428460706c02414030304800d01a040e00e40d080e5000303500046007040c00802c01403800e0451400c02100500c141c540c07401010050614640c403a038480408a82890085402c2c0300d2a4400e00d00350340c0b0190003a103209180d070000206078402c0000002d05000c0c3d0f84000c140 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 418646429 1250 418645179 418645187
    0x501051c140c0a080a0c0504050603041a100501110c0105030c0a0c02040e0d0206010902160206030402030114040b1005010201091205070507080105090109150b0f0f0105121017030f04030f03 83
    0x458492038007000007800c10881d00c07910b65105030340340008540c110300410300d103003514031500d02451a15680c20b8106420102080740d69403018106403203040003480042c00241c04141100e024060f5107424801051030400090308a18500300c07400d0b40358000c100d002032940d0700300c1c0440303501200800110340d4944c88078030140c5035100d107480040d41042c80c0070412110203000003140b0a200100340c0071182160307615281e403002c0e071190342c2001194950502c4003100604106001c1c0d6007041c401000031030320900485a583c004941210f065900d2000102401101000c00342441c0c050b1a00307100a012594041d11603070f00d00700d4420468010000002040410301500b03010f25806043d08000900460070044801030180452140030340d05040301010341c42101c0214466000c96400c0540201c01a4a460081103581c0415400e0641800010440200c5901000c0c0d070b254412030ad141c0104c281c2e541040b0f0105448041c580c0c80344410740c0200148179122103050140d404980e845604d1409080981c60211 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 418647679 1250 418646429 418646441
    0x1d090c0f2110050717130f03090306090c05040e16210b0106020c0406120201020a060b1306060c1e0308040b0a1d030316090b04050603130b0103080a1106010501051c 72
    0xc0724024445a08060101a000b2501a020700c0d40c52403c010f0000030280e105010a9503081402e0000a68040014031030703002a0a070700b40a420150400d5036291a580b003551a24270040f24840758a81091203646854400c06000d0040f600081c20084504444240030b00c0b41c50242c40c05401c00041c6595102d1000750b40080b895611400340d08884d40e40d8035000e075607814105401c1c1d101d1400d029004c604001d0711074400d80d0302c80c1c0590040004203d0344e120f00c2d00901003407180c00d420441340d0180c601184014025040144003540d600514003200b81411055000f200315030004001480c55001c0c00300760300c10340407070300701e41c10039800486511607104100c001c110074907080c64519a041c40388005180040050351081034030270040d59204c1111441200c0a6900380035044007801c05000034012810710401940c0e000410859a04140c1d40d11345a0128080d0261300890f0358080c00540340d000070b03520049021813170551000421155051000180035400b41d003c02c0380710340d882c6803040176120070150803072 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 418648929 1250 418647679 418647739
    0x160f0f0501091203180b0a02030a0e010615030b0a0e070809010e0607030903020d0309051906090b01030c1a0306010f03050403031b050310080601050906010c03050c071d090c0f 77
    0x800c210022850110f8092850182840110b0303d00084e03000810710f402c51030742c1000c0d031110811016580300c4031072200035000502640c1600d651450712415030a0244602409403051000d05d441826247e903000302590348600885004650041e4100032000724101e03210f402041604040b1036907580e034400e490050000c100e80311703468400c2c041032207a81c3d60154000410207000b07a0907141c00039090380058090f0344036600002c1c001e40c0000140c1c11f41c1c0c0d40c070141320f402e980d208100104130303150743d500d5581039040c080c2c00c240c070560341c8071208000305020340000300c40c00020b6617040c6040d0b01d007120000e0036014030060610189500c2d58005010144070384d1009203030710800003901c04610310005000b00039400898100001110a00f070100307251000142d0a4101c49c03000f00861a16951400111414071032a6400c50a100b070a01c40461843c5050100c800502442c010b1090300b10040098000420303c09412595a5008104411070986880100d41030940b02500c07501841074290444000c004016284 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 418650179 1250 418648929 418648931
    0x5060d060203100e0a02070c030212121206010305100311040c030204080a06050403030c0216120804030c080c040b06040b271309060b090606190302040b040b070b070302160f0f0501 79
    0x2003003c04508000f0280c02d45021101d0382410341c0d90159010228414224003800042100384108014034008943d50150071421007a1442c0b001745100b980c130550001c0440c404241c0a12040061a580c5807040613446004d07139a564000620319141c0d4003641100d1600b1600039502c590401080c203000750104c50007804e05a00319000c1201d9801c03c08020141035404030000b0341040460409907200003550a4035042d6140d03000300766840e000c0c40245015030a00102c40e400c0e0b0510000012902d8040701800030b26500010701a43d40c1c0c610200811280304a0040388204c1050000307101c803140410a40b1007901d03402403109551844484071a5490040f0084954042802c241450828426400684805129880901450303c0000405c420b48004554070707600302e40d090040c0c4803d0a015a12690f4888103410010300d01522041d10715010b6105d50012006d44c1400140303042005000310a10f03501c40154a000c40c2444076003468100f03a01d456034005405403c0540f9210144001403500650450340100 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 418651429 1250 418650179 418650181
    0x90103110d140109050126010e0304030c17010207200a0e070c0615080606090a020706050c0a0f021b012010060302101706060c011803020304080d050906070605060d060203 75
    0x1256030080e000b20064096035025240001840401c2070083c103040e242d000241c211100b0740ba0000c00e800440f100c88141041d920741d83c0807103031008240000d0014501038140c44422a00300b540c0b000307520300b090a80c0c207050f03841040b030341c00030410281c0480e145103180c00860b0401144940044e01c40740d4250014020302000c2c80a000200b03810079185a162403080c00b080c023810762881f00304080410144140b0200340c100000145480c604100e4069100403111401030a00c000c50f00d560301120300803a01044c500d07500082a21034542c00c060000214407607032005240707100280030450002400035080398180701c1c1d0801c642c070280c4100700b90104084141400c49409c0c42c120f8034040040c00031448103278024201800c448000d02c1c0314134401c4d041501d0400010489071156424484542d000c254495125582d4640b4801c0b03507080d01c801c0303500c0b09000f54021500c850908542500380103683c4410303400e2001c10402540140c40f031005640b8904e410180014140c0c2e1000085901ca40010074010202d503c004 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 418652679 1250 418651429 418651447
    0xd0203011d010609022d070b07020c090a0b10050306060f0d09020a05090708070c06091401050609011211060d020c16140604031509020301020c030d142a09010311 71
    0x160080034901d5110080c06020303643c15240c02203125030340f60705040e030090f1a07040500e01180305c1503030008614039a05500d0700703015450f203841845080e100c82d001a008412003170001d18000349080c0d00b00c0341140303080100c0204840061020070400000d48240a004030018049036202016100c0340c840c1c0ba916507944421081c030182c020812008128485c09000700c012402e030401412891091070303280ca42c020682c5a03142d040e2020180e0000485280762100b8402001500c1803e000011852813000400c45060090401c103031030005030010329101da450b0b54202c0100b003258000c000600001e07565140c1d106042c0d12104042c1c81003110540c51480b5483c41003600038013003200241264140122103034014800c0041050034070541c80003401104250301300300c907070704000e80c4811152480200014902022850880c1c150341040e40d0004040f955841e441c041180444c0d00316500100d401000d1aaa900f85c04c0c0503410a030641130a003440700360114140a00341d000b5881100e00605200d8004e454403096 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 418653929 1250 418652679 418652711
    0x20c13050f010b040f0902030613020a180e0c0a0c020a030f030807090e0c0d0b0406151107151e0e09010b0c1009080d09050a02090f0106081803090f0d020301 69
    0x1d448914841034004000142084032070192800d40309a5440c0b1042d1600e44206030010307400103007040c0c0d4070080b4204130b09041049480104843e0040b0b03104c14030a07003007118400c1d5400009170702c00c82c403591840b401c102040c0503507030480e00d0000c2142002d803d010100d0005c0b901d00040342c4c10003011000f28144000515810444580c82001903544a800054403448241c0031400d056a007422248014450f96208460980005040140240c40000c0c4190303680310100380a0845440c41c07010070302d100c2c13000c28194018031681010f414040700005254003100401400b15198205650701160607a075440e10052040341c40c1d03160130000030809115035031200341e43c048550004a010085d0700c00d0003011042185140174001080390800c0c511410082c09200b44806051003e400f21558000c003110080143e560700c101758010030000030600b98179810200094080c00d0080c08180c58043d5515404503686000400c9500c264415514010804264004150f901d1000d80c0c3c025403550806590044403078ac0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 418655179 1250 418653929 418653931
    0x6030c040305060c2b020c060f0a0f0504110409020a09110318060f010504240f05010201111c090204110c01050a390507080408070e0622050601020c1305 67
    0x7403400d88070781d44c03500801d0507640d1182d94050715030000640c05003140f003041144441d44110744000094600301e10f004005080207002c44107441c1d030210b91014003a0b07000a038414000380c00c18410003040b01e1b050549901a69100210100788115142d041c12811500c2e891301d42c10040403001014400c940301c1d80c0c414041500202ca40701000c0d5503007842c890002c48001401c13405211105103001140c3d00301004d20002c2d001e00c10b6103621218039900c0d8000c0440700c51803024001d14003a070180d030180c1d0030305000a0071743302c0209201c011980c0c00c0c05180701024900d500a08104406000040c0c2d02a85101043c00b8052000b401083c0c04004900d10700c5601c010b400c9a881482603010802c41004040c0403100752035000c06810740b14001041702070785004401d0307031841040c4250b414601d08251081e5103140d0390f5409034000a41c182c0000808124020010000940103001201d088804200c008684110303a044000d6070402c00f9141c0e400319145034000c0c0300ca1b44540601408001791005503c0e100c6000c2e10f0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 418656429 1250 418655179 418655183
    0xc0a02010e070e01061e3e0f100507020304120203010b10051801022e180c03140111070305160219180b0108060d03051306030614150901050f0906030c0403 68
    0x80c5152407006d03651004018100c8403070f41d48030f4040c8442140d81902078500b5103404202035a0071243d0320340141c0240100055101480002415400c58281c46d050a00c9200c8900024690500c1c0a010f4003580100940301900c3c0703400f91403541030303810740006800342042d03140594005c0c1041c04161441a40507001300411854405600e44101c003440c01265103607444000850840c1100e8001e403070f81180c60700c015401c42c00f550740100f2260086180c4001c1100c0f00e500c00ca44103004020f00704108401c80305404020801e50001308100140e5032040111441881d6000b000c21000080395140b142444100103034840e0090051070000400c1152400560703094001c1c0c5030707060340d05001c1c2e980c0c028090156251319034043e914000170752900f105010464082d6003044051040610520000f0319101e0f0f140c5004020558000c1404c5191240040b4628820301c01c503405080c10b10003220060a50800311440c1030004c3c40e001d030707940454080300c01d280d001e8076a03115840702000040c0034112240401030410380e8 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 418657679 1250 418656429 418656437
    0x91a04110909070b070c0b03130219030f02010c050312040c0612050411061c1e0c020c010207031b0302060706020a030c1809020f09030d08070e030102040b030c0a02010e070e0106 78
    0x2060384810850700e418200c455412030751004600744080900800a000d02c0342c8039400f1840500e80362100082d20f030300225205007428a03d070350343d90250310b8000c60084284101404408035182940c03102c82d0a070503000806030500a20030400703010000104115095549803011082a80c1054504401ca9081e540f25090014110030901d540541d158071400d0302540d0f00c0358010804c440701405100d80e540055101c902000810840c08442c0f80e41c900446500b02e00809071562041541c13001402142d250b02058411035100c580e40401e543d0f000144002500e40280b99621044035688030300c0345040427500000d4204002081407410400c00780c0103098a03d4907601c052001046541c402c40f1050344251006940c06075038501040141e405500170320784500007892240c546915200030134030340703032031604514006102d21007040702c60b90307101141c80f4880c44210025464185080e0352035034103010160050442d14000a20f01d01e195000b54050f80c50340c0c00c1e00f070a48400d42e54070a0720420b2013400b445400085 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 418658929 1250 418657679 418657703
    0x51501030b090705030a060e150c12010e01180b0f10090f051c030c15110901030b062a0f010504140f0a0c030602182d0402041d0703091a04 61
    0x500c01c00300f028400c0d140041c00508030a002c1c0c0d15424007074200e458003000e060007251003248020300c2d8080f403184902c000d0b1040c2682c0e051042498402d0301e405912442190a0600c01070212180700e2000c031086984041020603420fa1403000544814031800c0820ba10202d480f0350381032041c0d04183d8400840701c0d041c02404840340d440c403c0c03252902e014103200047c01000c0007004000303030245140490b002d020b20f82003510314200540400c1143e15501c41460b42280115011445680c18000c00c00d202c1810b54042d800c1c00d124a0000b0306e00da40c58203d8000c1c0420745204104940da0411800756000d05c841c00a0010703060500703000e40080441c1d589411a400b0308114441286400105100f42d01d81c880c04000149107076885440007500154a8080031400300c1040d540159643d80c04021140d071183d002404038402040503404840c1c0386c0a03030340e001c0c42c0180010001e07100d07400d0020072a40f05014a400c6d803a80c40c3c88007240107112040d00107202403807003540d00043c5018448801d20551140c5080e00070 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 418660179 1250 418658929 418658941
    0x61106060f011704051908070213110f0d0b090a0e0d0212030403030b2706011805090a0c120504060b0109060203030f160201090c09090c120c14060403051501030b 71
    0x50182010040c030b01084070040f41548644040f0b4106501034091015140500403040d51008407181407041580e48100108410080d03240124801d01c2400420404002440d8074402c40a41c0740200c0d098020201e20100d200c0707015410b00d4110008001c0018081003c0b45402881c1c08014203074032090746850304c1925042080c41d8000a0001054410122807a0450b40d4980c1e040700a000c0403a11035401c01c0f0096601e171040c0c1440c6814000741d040200c0c03604a14944040010880941c1302c5035880100c03d0400100b042d500d840f004680c000c500d82a003c03441e604207200540d046c030039882444060a2411040000380252540b14140380c203426603815a2076951080d04070b2f5240825a0022030200b561070103e0800001c562400707804807007034000403e0b0034081d42c0f901d00030100c41ea400148910f48481d4550100325842e5404806800c00140d440c41d01780f1207440701c04c04180365011781c00b41d03d003c0b065003001c5503680c1c81c00d40d401542e1020844065810000d00d030303404803c080c40216054020880404e41d = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 418661429 1250 418660179 418660189
    0x1f0e0c030a0f02060a1103070f141f050a06030f050303010e1302030c09070905060d0e0f0d17060a03020901080a1103010203010617040609120c14030702100305041403030106110606 79
    0x841c103500504500079400301d580820020b68170040800c0c0078404584c0c41c0e0f005002c020310190144030f004558507251000310742080e91150f03061140c100000d810050f054011502c2c1d40c400d050b010b02e040030000506640e00070301c2c40000c1503560009040511b580f40c0580070802d00100941c10f03620f2020321008030b1345885060050249440e000203505821100340d15500381400582140d12800d185801800c840d40e800100c7d029511181040305a251101401e6032405010001e042010300e440740189501183c0e984000e003100c0e071406140c0003c4054502244007030340c8411a8030051900140f40c4642035030348080c610f80c1e07008500e001700c0d00d200d440103804255203010310035241210f406441d6010b2404010840390081070f00240226203040d601c00842010a10f181d2240d06482c00b2904c0b0349a04000742e052a40f0720600c565a01d0320f107940104009030058413025a050110003050802107a50340b11490815114101d512169050b4800800001b4656a00c14100445580c04c0001e85500d901d8201c1842 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 418662679 1250 418661429 418661443
    0x3040f03150b2d011710060215060312031b0d050109150f1202190f030302161404020901030b030d03050109060b0c060f1f0b09010f03050f01090e1f0e0c03 68
    0x1907964440d420010803d20301110821003040f405240c40210704a16040504440c0070030b032071003100b01440840a006068040103400c0c0700660302050400c0340c1c80c003040066a100c0e40720031080441c25010000c59200359860000039070f401440d00e40981c44101e142c20320030090109109061165080c001d1107050351000e849403606031480301c41888421420b20f4440c1690a0503580c00320780104903d9203001040c0c0d08810f1b1680a46030a1400306582461414000e10700030202da80e0b400000c52124081200c800c1c00d07080c0046008095030050303100e820040c01030b001810502e202a0f0140034020048a100c0da250380b10038169a07040c42e04103d5981ca880c000c03a084d01440055104561140d00822001402c0f213a9495220900b4407940059807140040c0c4004600380342d2150b841e8410200349002150781068900f42408a245001c025078078166204030042c030b2062041504c00c40e55162180c41641e001d00450360b004d012808030780c580320540e404440c02422031101000b000e0159030300310151450040365072 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 418663929 1250 418662679 418662709
    0x71205070201020705040e070308030112110303030c0a0807121b0305010f2909060c010c120507210608030c0606040f02041a130e0103140c0a050a0e0903040f03150b 72
    0xd01c03089043c481401b0041080c80e1000f801031260f03c20000003c2c1c200300c01103001e4070001601901056191a005c0ca4850f0720341d074032601c01c1d0814410404607042c04c0040e12001303d0035241511164813145810f462242070880058000d80c240381d180c007690322502d0080801011030f030f6001c04c043e07a030b40c46607103a600c0305e1801962420000103031503440300c08000f03407a200d130301105420507403814040c500050b401d07501c441e071400e0242c0d4654100e60701c03181d0494491000c5100010003400140383c5260f0003450003509048051840b070702d4100718400d00740c041e48010081c0101c501126910b0b001c200140b030380c80000311416481a402c0038108425000e6600980d0121080302200b044005100c0028051035003004045c000143c02c22034000950080d01c0b01614000e600802c17110070018004240d2506155948405034020502103404204944541c640f510441d5130b40c8180c00026202c24141074290311559105c201014440400401400045e4600d40d50280c2c0d402000c0043c074002e1800d020306001100b4103 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 418665179 1250 418663929 418663933
    0xe011a07022103070b0903271504060c03090b070b010b0a0c1407080c04060e01060f0c051b0405060d0201050406050f070203010e060f011a07030507050a120302180d08030a18080f07120507020102 85
    0x40740781d11640d822014941c818009d000c503203a2010389032010301c0d50300240e0104000814140201c018103400107039032400340c100e1504152410042d0f40318042654010b1060920440c800141103604c50701c24000325000a80c041031032244113141200c0c0030ba4680307190181c0044e900441045e040a49020312a5034102c903003103000c02d4403980c6000420f48955050a44010a02080c0442c1c8000070703001f400103c08030708510f108802058038800c103010803190300a140501542c1c032008810050b0b138128041e0381c115196894645e6984244941101250040e03440c029015807c102181201031004a9080c2c4181300002c01005240c0e80e80780070b4822510f0305020100503c0b410003000011034800d0300241000380c020b10032a4800340d4144d660801c0c00d2515598900040d0307010903a0a180c100021401824103011500d02c140c8040e0b50315540c82921000e8400c0c080ea6640d040d40c480550107030030b0003007010780c1c0209016842d09054004400154450201210071450311491100c2442c042c1c41620000c68040e40 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 418666429 1250 418665179 418665217
    0x10609230703090f08030a05010e0105010e010801030b1801050c0309150709030b0703110a0f091706060d0f0515040204051303051909090221010e011a07022103070b0903 74
    0x110540042c0180c0c50252100f138848030b402c0000c43c09802c002c50007400280d400050541c5808070400c03080c50181c1101e410003805035040601a039001c00c2c41e1f419283c1110540c2c04a0b12001e55000c490318042404900550800341003181d03c031003282c007852045000e102911644101002d41e20cd40841c111210310210304695001d00c00308101010b402c1c1e02a6190800040b0034054810b80e11040d080861540001002440f8685200341e00c28220402804d010341c03240803510703080b00ad07907480d210010140ca00510702c0709000e5052250380c44101324181d4003d010b90f80c00345030301ca44282c1c84510403034090740964240383c04101d9400e2716010b010140f980580c1c0d030a080c01740110080c481d0050100303840c070401c046654040f4031462a880103201d5000480001c1140e02d018041e000311a09059122402c5482e44800411501c1f0400b0321200d40c1c3c0c400408090307aa508580300151018444404014550f100d40c003400c100c3e03050010080c25030601a030b00305545556410003184d07503442141c0006499402901c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 418667679 1250 418666429 418666441
    0x2d14150603060f13060e0604050706110d050c030405040c05030f06030316021201240306050a020903031c0905191e121d060a0306030c06020601050d0f1505010801060923 74
    0x1680180c20402052001d2041c030801d40345d003415600c04015001c1950004400e001c1089020460341c1700038070503070600b18141e8082c645046d86880e1000620b1050001c00107004900c80e5082c422100681340050007001710042e2600020500d400403a0041c41501c0300c900450a1442d000041d50a04008005003600e460055802d10040c1001540ca9071704640d21010303800100b441004285401c3d1080745544400c0c0b510b5030810380c0a0362000b07481b5440d1548100210318082d100481214480980001094a80c6501c00751020040450307080142050244805e0342080c06c07024000d5100c52409208513012074035144010858048007043c0c02824a072a20030081285401003200c1071040007001d03039142d11038a690002c034201e68405541040081d98588081c800c105c80c518000020700320718401040c280d810140410340d04046410003400780528484404200581c0300003010080c3d002c0803090165594400e0704601078072150080441c05410032101c942c040120201342c0040500811001005403524 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 418668929 1250 418667679 418667701
    0xe01061407050111030a0b060c070509330a08031219090804030b04020306070c08090409170a030f0506040c0503010504051b030c03010e01212d1415060306 68
    0x520410088080c09201e5400401d0082c8a000c080312072540c602a5680740c04c10644084600180149118081c00c2c41040500e56002403040c068500940303280e12580c40d8645181100701c48040000d88a00c080b01e03010034003444030b61400400d90030943d0703820354545d100d1800c13a84902454500288010441000030300103400e84021020103d1070050004100d0141d8071600e5140c0d2198100340c40b070030320000c1440704505042091a07130142c032a281c2488814a40d90311744030b89200391043c95102e2500c40a40106200e481c40105544038000103201d580c0748541a2b010b03001e403051a010a081501c0c01000600a00f01801011078802c52a512070307107182c1c00d107800c000c000c0002904007140c82081c2c4111071514050040150b00800110b50355a03180c4d03151031400030441105030800310034072a0141c1e4644d0481d00d80481e900c42e0b42d6002c0074140761003030381c2004000a018071103814055180707420310400501c03420a420310001a50001030340c0600c00e40c841c03094074081c0b0584d41e0503010350142001401260706 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 418670179 1250 418668929 418668947
    0x31a0a081f020f070c170105060121021908090d0809070324060e0f06010504052d0a090e0606240a020118060c120902010509040b010c02181f0e0106 65
    0x1000381c018182036455005201d260050340017192510003030507080c401c410350b0320b01103100c0c0b515a500a00c00c51800c03000007042003007003880e024550190b114003410512519010381d0005654030144107145000340710028656a401c1d034100126015500b46070a80720700c5105064403445c0c0d0300c4001c00c295403441d541c034005000428140b1105c40340c41402a4404c052500494000341031641f40b034041d03401c7c007143e1075520100c0035261905224041104100544601d015220084100105040001982c43d00f42e070410356400005035110500902c003003100713400b41c0d01400015490b80204c0d1215910b420038002e800d10450200c12502c61400d007614103040704000203001c1380301540700104481e004c024401d40f04240304c1c07070111a13044e110b401c80c00444d644184d140034001c8114005100c4c1d48001d40001e840342c0316070603019001d59203c000080b001d9000318524000c50781d028103003010031442c4d4007a8134151355054810610302c0c9940c210f0f118128004803842c4046c0c410203000300450b81d02c0d10400343e401c011 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 418671429 1250 418670179 418670233
    0x8060f0105070219090e07080601080601050906060d05010803130801150b0c16030f02040c0203120f061c080403060c02060106050f0a090302043e0d0f0e030307031a0a08 74
    0x15039139504d0451400c0024090002d080e5484041000d004031840c6908000d0241c01090380342d8041c1c001040810000201329044400c2529051526210503001ca07115118020300307650400d00b024000505540b00100408208503d03a21a0b40002d848088403400c0c3d4245000b940c2445008d50400d11414114030020320490198004031907414a405050942020741984240c40100b4040004001e60500313008840c44c2810520155192889042c00c28140400241607036641d1100d50b00016116102c843e0700300001640030041a18004040ca0010141e510501086580f141407140d240300e400d00010f18241618206c4d143c10303080540c0d2800300155900140c6807442040002000040541c640344125161010052030004005850000303411914040d030144c4400f40f000d02a010b115003484c1d00a860082041c0d0501161200854010002070050002d200c491030000100344030209400d40d00c030032010b4070b510080940780c2801b041001000310f081d1180c5da400c1c1d0000031000c504800d007011070b110174036 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 418672679 1250 418671429 418671439
    0x20102040510020c03011b0507030f090504110c1603030f18050904080a0f02030a12230c040f050118052125050d050c270c0405040c08060f01050702 65
    0x595600c00101c102c0c5401c289000940c00c03205041c2c1960400313002d80d28182c0c0910603a0b0040881001c0010170310712a092001e07042280b000d6204e9031580c480d11070301004000c02403040c0420203821400710b8050b40505c42c88030701840743c95aa2038210075440b10758000c6079099121f03868446d050b55002e5400c0840c20028000039100410089041d41e2003406c41400f46000b00355154a5640640c400307009980702558145c1994010b00c0180d03030103030b03000f4003001c0c0a10b40300751b0100b0180b10007149001c1d10300000741e00d035005440e640200411612200081c008840e46805a090000d0b915801910300141540c4a1044907544550502c19400c22118510f810fa17100f0400041e0380c50300d080c420f414500141107021500ba0313001c22025400140c0c0445030054442110310940c180d1965a4040c0c0e1f0f66140c0c3d00280c040c00110403102001d200308c1d2003403100400355000380101454907400b110100d9116000d0305100f00c1c5000c081d02c0303e0505c00c0c041103214180c0500144510004d2100568003a000888103d0380300c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 418673929 1250 418672679 418672687
    0x20705030a05180a050a05040207060608030d0e100c050711060c100b0315132301230f0907050103020d020903010f05180a030e0105030a0b090f060901081f050601020102 74
    0x18a04000400c1d00d0449a980c054980031140340c16191500381c0f0b29a1840394002c481e003840543d48040c140000c40703404070340069403841c0900c0d060000c0c082c5903110344401e00021580311003060094100356890305d00002070f15803e0820201840441d100c503950300001407414014000001c3c00d0754001b290132280201300b60306001004c07107128a450312040526621944500c0040640d0602300051102a101802d81c000c8078a412510401c443c86910400780c100f0070040000f103000d01502d9a001c601c5504980240908480e00c055a603000b00a2442c02414003441d10000c0c400e610000ca5040c01407001c02c014102c1189440c00441c06074000a1080742d1803075081110304050f40e0f09111300100091420800700380341c42d203503400000f0f030010784100300c401f03030020382001c40081ea0241c2401c01310102400c0403622a12184050002080c038004d4294020f50000180500240d104107110721030070040713607000d09907a261502103840c0c400400500c205c43c1d801c8622592081c40e160010366210034107100040c20 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 418675179 1250 418673929 418673933
    0x6190b0f0d02070b040c08060c0702030a021e0a06110c040e0316150608160b0903061602030d0203071d0105180d060e031309142221050d0f050709050d060207 69
    0x20700344c1a03804580140d404241008010070078000325901c4048050403906162094005c640c44500490000703104604a0100721900e40100300446a102c0010301000a03198481c0400703041d000f040b101c0000716200d60800e8083c0c51401d40100601350814a001c0c6050100d482c00c02e20b100c40312601c3c21602c0d04461a045019241540b040f40000c00c5032000502c0341880050178810a64841d4221184110701080000a1920005001c5810240840c942002d100702d05d1000c0703003103011708483c51907020b0001081c82001584510600c40102c1e03d0486070700b012600c18010b568a220719100707200c1e035000c44076440b00d191800d80c942081d510700501e0040350a1038035075441800e56000500700402c050903944240700000041c49004001824940900b8507428070b245107103254804920000c0d43c0e50308000c401c00400105d0100c0c49003100804124210425a0b80c8024010350007043c41e180d2020301d4403c1e44022511103004003070017402142c89903a591418101440000010f4101c150307101d03a020060800 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 418676429 1250 418675179 418675193
    0x150807020f12040e090a0b0c0c0c06130302040b01170a0b010e040c0f0f08090a1401090f030206150103021908100b030f060f090720070302090108030306190b0f0d0207 73
    0xc107011a28a00b5070b515400d007444101c14410181030260103070702800001c1c00107200350003032940004054001680f10801629240e01c0d05c0c5070018040d80110011401003810016540c00b14250f92080303400303101503030245004544c4200a820a0250102d05002140c000009684040820710040c0740a451000300c03480401d054407075006c1d0349000119840c131881061503005100301c10b076a1030f80c03420b0002400d10741851941c0b2a40051b0140c0b101e0325403a200b1000307613025404820050b5102000c0b8111030480d09001c1d4441c0000c4801c000c02043c02001800250710a1003103030781490a01c002c28a81c48400941240c10307034002031042e51620240c8001081050020010358802c0714102d0750b20784a4074004042c0b1824541045405000e80b170400148990307641c000349201594180303107140c45020045030003954609500b80e400650041d03425030002c180c2680110041d880b820060740d003c4410907446081c2c4800708107074803031122120b00c240044c80005400900030700105501e260050708148c0d25468500c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 418677679 1250 418676429 418676443
    0xa02070f0b0706050603060c071b0512060a0e030f0d0902060f2d0a08040b0402010513031415060d03080a060e0a1b03060f0e04080c19050105060901150807020f 70
    0x568400114001041040f240240e0ba8009000c0c2c01a04141c100059001714501a5120041560b2034105581030b080c5502032003500240401401c040c9030048540c003030b549a140035104044607505104000e1f040000010403a10840301c400c0185203070454001003c00105003c0c00100e902960400c984c5c0c00c003204c804007501344840d03924032640c2c0c0004941d5210500301d113070b690038940c4142c0501800c9203264018008640c4103401c070080400982d25440100d889204052281e4095100004048144100000324075454a000301c00c0701d8114132020281091600c0455910394481140150a000a80302d004019082680d603800401d5051315041d140c1c010b01d5040385c14a00340f941c0d0f00d019100805120446980c0c04032a410304001c0b650415052018909603802400340920001c004a0100403801d0120b0301004114003e690134503e00d604003949a05900e0000d40d031640c2000c000c80d21500d08030050a0484885d10781401c00303d0420f0b501962071413000ac24010650203079004e0080009010311100d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 418678929 1250 418677679 418677689
    0x3060b040b090420090105010c110109030507060f081e04030f0311030424140a090c0909060209130203090312220305030610030e03030c09120102071110020604170a02070f 75
    0x1070300c913881d18035100c5080315500080e620311600700d0f540100001d9030082d00c03ca01c00c40c1c1003140c0001107290300d80180c2d1080200d0388001e0042c070178603c00040f0554001c41c0c07280300c49055603640d000f9488020300d0240b03441d921441c12850103d103002080000c0d00456028041ca4218240450300c910107280101c86030304121001c1d00d021203c4200c40310010000314040823280880c1c07400300501134010300d82a6500d04003c00900140b5a2076803000244620101c0c1c03400100480801800000194541107010350002c02005003e09800900b40c1c640120038002c2ea442034030898001e5041100a824000340408040e00489180854503170b517032407900c640040205098004d44549549003002814090200b1845021008252610141d0031101c80048112500504008005500d42c10010001402c0b4106200c010015610006411082217540e0a180380c010000315048400c04583c0c040590b104d200454004202c4400802480c4808080401501079945248100c0d0081616110400c84581d0741c0d03000 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 418680179 1250 418678929 418678943
    0xd0b1503160e060c0d1103120405010f0b0a0b0d020a0c1a220b0c0906040e01080a1217040f0627050c040c02060f070302160311070f060903060b040b0904 67
    0x400003a094001074001450380c02507880030301c0e00841c3d1084a0b103a010a0170b12500300903614045c074105010070001d8646180b6010540d00701410f11b450828003d12060303610409003410810100c03201d14101030808201e6035030340c1d5401d103820f114146800003580500c17101004d2000b0040c8802c0401c0c0581442d19000d000713142c510841e818291103610348011855846003804840c4102c0074001400540c45507044026480707000d840c0c001c00c40021300540925000442001030a000000d0042000520800e426028800440206503090411214051030384a12885920007102207800104c1d49409203091034000c6d01d00098144185140040d4203104000d440e0f03000030419104800c0c0002444800314640c0c08480c10065a003840c0e8020351102802000f4034000041e000001c5d50240c0250103c0b0703603002c840780340f0810b800f100b850050140c00f0320340104c0c42d03940300d030480104204483d404000140c3e0615100e0148440c07550361041c2c0588100b00c000c9804c0340d02e440c4542d9280d141c8000c0940a5485541 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 418681429 1250 418680179 418680211
    0x1a040303061e03020105070212010212040b010e0717070c0510060f1202030c0904030912140610060206011a190e030d02030708070f031b061a040b03030d0b1503 70
    0x800030203035a0300b9005a144001c6040342604000c1d02c103003014048a60a08080761070f85594000104800c1c0e409420000c19400090f02c2c405c560398120410348690311951750403506980b140d0000c0340b010011100321011a1155203440c0c090030700307d01e19503440b440750f10b8803a0080540340d88042c100070b00d8040200420f40c60710002d01c00344003000c0003c0701400d045103005c202c00b102c0d900040c4d5200c0c1380020482c025440c14000c00c050501c258408000303064000220440e1444a10b04401046083c00042c812801850045108446c01c04149001c80d80107900411042c1d003014400b6020318080903840d08002070410840071403102035004020389800e2500d510b403442e91420203242c2441c0782d4100000c11900100a00d000050449040c2c2c0c100c55081000c620303070a04545010b940040917115000c051120710040f41c41001501e800458526803440c00803042441218140025216000306180c1c0c140c00c00c1c00b40d00455803580e402151039820052104440000b07580b840704840d4800d494902e80010805 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 418682679 1250 418681429 418681433
    0x112111e2a030d0504020105130609052803020f0a1701020a030c05030906310b0612010b01080c030a2a0e060301030b130809030d05070b1501080708060d1a04 69
    0x5118104030440d40029800d070341c5030001038181c40c0d00c1080325a0b00056503c1c1c011806592040e000d030741c0c410741689001c44803141c80358006000350f0721500c141d602c2070b904039401c00010054007444411000319a00e0007040700b42941d00304404070070a2041c1ca0340041800d2000070301a1095030482c444854a040010780e40c007021200101941c3c40ca0210100b440360800c24080041c0d0002203c540c4601600201d2200c440d00c00a03401d83c00060004203030381c3c0c0f160003660b201070004c00810b0502409084840c041c0303086104420701c2c03d0b6507c1c03106450100c1c1e41000099140b001d148001c40e0b00c81d464400000c0c09a455030100d404080024010842c000c1c0454500907403142c00540860099500b11115421507266541d95020030748010428a001024541d10400f0080b041047c1c580022008041c1c55140090640090441d000344000740c98940507240031490800c06250300020041c410f80da400002e07502e1401c01c4d12410f00c094140c50704540c135401c104000c9016440402c0d403081c840000200541000c5c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 418683929 1250 418682679 418682707
    0x18031305180c0d02071b0905060f0306090c04020d0f050c040314070e070c0201031104090b0901050402030403020a0b0718180b1509011101091406180c0112111e 70
    0x68441d074030105901c188821403201209890754051038440140c1d82e03c08515112154241c03003010854070410b01c079400b08400000e0b400171403140d40250b170030b01c414034080002c16940b40802d40e4040d2440c0c10101d10035509041035002007184169140c0046400e240c0e0200d0101100c1086501820050021030b041c4100080914407000c80c1da02e81c402415403030708114074465103010150903501405100c41801b8116406908400800b041d0141c00a0300d850f03881c4e011501901d00410824403686c0764030004200e41c50b0500c20760b4000d5030903900400e0b1001c1c43e60744801c42d011010741014207000d00c2c1c80d0803613140c5906080c410040c0001c00e240004401d81c0403a030106580342c800500d441000010400011030094205a40081c0000d20740710741151b0204010700d0040c11580e1024002c840041c40610720a540000e8160042c00041100e075000444183c8840c1c6809180321071b64005068644940035204a5810582168240410a1340f40902c449815505007080440b44003c80380080381e4000d01160b0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 418685179 1250 418683929 418683949
    0x303070f08070201020c06060f12120307030c0201023a05010902070b070f0215150409050f0601060903200a05031c0206070e1305250e15070b04020918031305 69
    0x2c079000a5003008008801c0d01d0703c50000401440c02801c600d6807002e07041d40d6004008001220240581d00d0007081e2880c4008240d104840c00c80100342000300d0142c0302032051080b1804c24086441046420b0540c00c172030740c0d0440034900440200303d420780303000d4400d401c18403c6e03600070910038000503620321240c135080301128001809503084c4100d101000c29402d401040300103204c5007100b01c00c5025540c4a08504440c0b1040c0c40158106142c0421300040201c006a90185030000c40d0859416a90b2210308940c01016400020803500d0b80b48200c1e000407880d02e00c8440302d42c0c00148425003160300c8502081c1b401006041c81081100e07a071280c490410340602031150090b56070f151410800100d1004510101401d030070030508641d64200080c048140a0b000780c02c003025020100604140c4409c00130200104941401c2c03180510382100e144107401081100c3c035107a4025140c041542d525001c000010313000a0052036141c0c84420400c0500748280028540901307a242203c1105042c0b90034403490440d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 418686429 1250 418685179 418685191
    0x3020604061d040b0603071107230a0e220203070905040807060b0901050315040f050f1027110a030b01120b09010c1e140f091c020108070f030b030303070f08 69
    0x45880303401401c9490b0f01c03081b41d50000c054104080c400152111140c9424056403182401d00c050659850074102c05588a25100c181102e0800c18a61540008d00306d0860036100500035401960303a800e0f0400c0c00000c49001c03c0d000405440a0503600e1106005403442110101e03034450f000034500c01000140d1140c00440706040c2c512410540c140800300b5981c0700241041d6144602c204c0024007000886c00c0c110740a254010b099079144000510b209588040712006032100320304040b018a41d02154004810340e994002125241542d610741300e6108038a418401950052203440012020801031301e101130090901580b210340c00202418891304003000603180d04200e0b41850701e43c0301501d610240425050200d814003900e80040c040d800d850780014400d9228080d140807500411a554a401038101316009540c944800071000701340d000c01103010b0000901103007004000c40c9046100383d1f2000d426071918100000d40003e46400a03103950800c80c0d0035030002d04100501c812441d403154501d5003010f = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 418687679 1250 418686429 418686431
    0xc030f0506030304061d030304061107080c0f0909031204030f02071d010e19090b0609090d09031202070902070f0201032003070e061b060103031b031b020a03020604061d04 75
    0x1040c1440000c0d03d0344114881d100400c02c1d030500c2482da2001d81c0d4449074801030010700320380e0760360740c0d4510240c103950b43e0b001c4004190107858800988481c01140f202c40c02c4c04003c140310340450250017000710520004e0420b642c0c6100038860103005054a0266501641c025143c1000481010000902d043c0341600189844510141d98154007001000524103603040101c92200307640d10207900f0520700c000011440354480c18841c06109005035404080d0107140151000a03041d40c51881d27443e62500d010f858a0300141c1d0112040000c03032030301d40c0003404020652068400040e0b8903800007061343c00200003654034090700001e003030440d82c1501c00c60058907402605406000c0da0744013409094000101f0b18010f016a034034800b042a52034000b00e41c281c65070020280d003032080e501c24581ea90230003400220017003840360f000c2c06110440740e0142e400c2d145d45540d500709441000007408203141f401c050102e0300702c141145d02100507524080580003505c41a0b6500c0c0800040c030013001041484d0913065400740d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 418688929 1250 418687679 418687681
    0x2090f04060e0706090b0f0f04030807051b090a05150a081c0e0a0603020c070b0d091203020310091104030506071e0c020f012106080d031527021c0c030f05 68
    0x440e4104d038615041b265554105900c07182c2400e0390f039206205910132001051f0002a01000b004603010286c42c8040c026422a601c4001107200c2561080c00c020065501c0100603000400c9442250021944a4011400116621004c1002c0784034040590071440003504107000d08800d201c0001d0440c83d8080803071411f400c503058030b6000f0809820441c0140010150001010060820108030f014010800d001d49541d890310184940402001c0c003010465914022200305060280300303000b968043d414288210350002e2034041c1d010b0050040c0000d0211a0000707100010100e5804d014941c03040a80d40c590701408040140f0b04904040701c0000601030001000004000d44c569031010420340d03500b8201900e100e0314071544031002103102c0d0300301071049042100106080c48007045410f03400c2d02c1901c0074421440030482500405005000381101011550025200c41481025030312181000d400014030301030034008248a046481d04010001e20348441500a40c90b03031500c540d08007944110750800c01 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 418690179 1250 418688929 418688939
    0x60d02060a080408040f170d020705130b030703050a030503061206240102010207020409140111070f03050f0c0304060314010905040b01050f0102011509090c05030f07051c02090f04060e07 82
    0x19405036010601c10403100348001010800c1d03c1c821900034242112017800c80356030f01e000030010b42e00c0b48244d012080c02800b8410302e0643c0001116000d4580040420200c5024001604010811810440d81c10b118034400080400d06c14000010103500aa81305d43c0d40b45414001c2c464000c1100c0101c80981d480304041009003054501100903003030030710310104d07064400171340100e0282c003076442d010358401d2034400014100240d4041041d81607070341000a000c0c0346030300d03e41c0880500500001a010b05a42c10004000a02c948000e0041c520104c001604054400032410702d5904160801c0b00072aa81d684843c2844a05001240c010700c103640c0c1c03d10141c54141d840c15480700043c0b0445000b001082084003403603000390450043c054403001c0c03040a01d07a03981095000341c0800401514042413070700c4003189900b408034200e4404040704004103a0b152404081c030807450f480589a10304035481c04100d60042c0c0c0e40300360090040100c246c409540f4100382c14a182140c002d1101d40109034881070003000 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 418691429 1250 418690179 418690189
    0x40e0c0c011d121e0c1e030705071403010212040c05130908090f0a05040f05061c0506040321110a020c0316060806060409060e0106030c02060c0d0203041a0a02070506060d02 76
    0x30215100c500c08030785441003030341141922648684458044c40001c82c01c4050310703400190f0310701340290141542018052a034042a2248a038050141540e0013040007402103010303ca07546103a4880190006141c400940302c4a902d5000a8408a031584c0503000100700b18500841003410b041c00d420b00c10882d4020540d5003104601c100031a09002e80c030041c4200550b6a84c0070011401040080c20910400c055000c0900007030100f203402c1441110004c1c1c241c2c4500090552065185520100800c055100e03070314291207007285555115210710b45040d5913010030407036000c0d41d00446100750011b5194000c201c0c000c0d00304802c846116020340e02c200603214048841c42c0b40c443c11160203040c00f035050b4a07400046080ca2045030015a045401c03d08006034291034112003d049502c5035070304000c01010984200d8030340109482a01c1021810311008000100a03401140c00c81e2040c1d448411185c0081c0628400c0d4000b2100740305102c0c2d0110354181800401c0c845554801d004035845803820000b81d0000b5 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 418692679 1250 418691429 418691443
    0x30c030b01090509130203010e030702030106080604240b06070b0114040e100b0f0402070507061202030c09100c0c080313080c0607030309050f0a080a030609020c060601030b0105040e0c0c011d 84
    0x313440b88089074007054890454200a00140382c000e0001e022a8200c09102640da6000c000c00301c1c045e6203409800107070080c020034254000e65010f900071000c080c44100c07000b51420310704aa581e51950f00c5490f1080c81e90380c64020442940320312610a00c640c980352815050910780f19400b03003c4c41c00d004d0b80c0701e4440b402003038180190310300d880002680494840458a08503a0701c600d541c02c1440003500b8400d00200213403000840b45141e80e00d2441d14081200e6100307900090b144541c108601b44450209464070f0200f0381c460000d18542000040d04541381d450540e400c0350320802d660b420004226489404009118001e0712010005140c40d0351404e0100720316200f1040080d0070141c2d10240b9030100301040c03115050085180c82120074184050810a006034007620129000c28600000003d100885000781c518000e486000f416855a07000b0042d0044c029081445041007001c100100da107004051341c403406034191403815500c4000c2d0045c45400c40301118070f5014414100300c4610003114000481d0703 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 418693929 1250 418692679 418692689
    0x30905070512030d060b03060f18042009070e1003090302100b01050c07031a0a0b010806100203040801020409060807060c0b2a04060807021005071407050709060312030c030b0109 78
    0x82c2c2040811114242d04600599003485401c40c2001000104c10080c4c00c051170261400b140c119081008120402c0b11040c1751034120011082d400740000c020922400c2280b103500043d4907140001e04030b02e800102c02d00d004a400d5004602d10920340717599802c0c110a406400031480c1010818080c550f1030103992000c051481c1e54445855040400f1564481c8064408070f0400c4012a449940c880c50400526000c0c0740a0804141c20b0200064014900d40a4001c5210701078483c680b46440c1c181c20b00c40c00d0795003c1741034410342c40100400506200c09200810050040103000100c00303042c00803260a155881d0301c6001007250409090020a41c0e6900c41034116412170303111a503240d010030070004100105510070305815008580000c50f0b035041000c580c407400c1c04d41d0035075640701068102041280c0b01503400c0800a004e004540e100303c09410001d03d8070900540854484903070752031900d000d941d06608100c810144000381c0f940410303094055400020102d040038440e69440c0c1000800d0b403280f52241c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 418695179 1250 418693929 418693939
    0xf070e121b19180f1104080607080105060d0c18140108060d030203030c03130c06030507030e0a1707021f050403051204150c1509062f160c0f12060c0309050705 70
    0x1140303e0b900e032998418002001c07222800c0c044207020041c2400641c019208003043c900030000002c4e4440c0c4600760060584800819840c10a103e840403900101000f54038a024041e43c1440d10415016404520004001c482a105050303a6403200041004270050500f60080305251690030000c1d8021003580e174006228800750b0f46039071392a245400181403190028124403c000004214541c0c1504450302c1640e16440c140002070070307007058540d907019140c0f0203032507568007184680490a81200800c0d0703403800180050202000041d184240c402c001d0034200c04610001002c0003003100500060003a44812183e0b14101840c003c44400d040c02c00d65804000c0000c8026050200072803001c11000c40040c0000c10400e5181c203180a600804060090044009140585001e51f140301c04510083c03407010b60a5600f0100c100217000f120429001c000c8519011964022030000000c01c019402009800071010100c041414500115101180400200350601ea00c4202284000031318504030784060700d0b = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 418696429 1250 418695179 418695209
    0x203070b160216091401120317060d021201021b0312162d090f030807060f060503060408071101030614010c030302090622050103050402090f070e121b19 67
    0x1c01c0742072003490001406800b00c5564041154112684020794031642c02c0441040d85e45c03500000c0d1143c0b40c030100c0060000705d80900d0001142d0f103100781941c005c3c0001d40344061201c0c02d54000380c60711a1060400015030b601041100c0340c40b031000b50300500d0b40700c0f48024504d846c0d20718504610f04000100740040d1884040400907456110b030803c6056001707a1a102c0d10700044850307445080281c403e001000180641d03601141812000c0d10a000b12a8018103c0c2d241c28200d03681c0102800fa0070464520995880070000340e19141808050b00c254031884409030b41d95071901d0034003142c08481c02d019041500e01501801081002c0c80c1c6140003104c2401d0941140e280352400314042c0c481ea44200740c0001c1c0100e507040d00d940c07001030f2104618500314a00349001d901c40c80110120350044034042d40c0006c0090119600180d0001c0442d000441460060021025100800d0004e80c40358544541030b84038905003800700a1f20b022410812001b211060356900340f800482154840500a0186007031080d0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 418697679 1250 418696429 418696471
    0x50610091e0e0c0d0f05100e07060c08160c09110307050304110a050a0815150d12140a0509030f0a24140a091e080a080703091a090d0203070b 62
    0x200220700c00e02d00811300001131380145040207616a0121040301c113031090742501048400d0718000c040440300b04000500406281c00d1080b5081081e1032400d07507602d8000c210500c0130b4400041a807917020300417606c910380e80346425201003c40c4c2440d192010b84520500038800784590050403290030940040013858100000c070f00140d071444199220703079402268120300241c801008142c004003a8185c40c11012260303a03100740000c1d0111401e0200d603010111640c0d0307000242020464008220040c81d1180c09991140d00780b088a0740a06000d001088003c40c82ea21645030800400e0401c1307809102030040c419141c2c0d54003109100040310034001e8801d52000c0500c000c0c055000003001810b22104000500340807007035100400a001050f00c0c01d031000031802d1a032010400040c00e14560000f0a580f40000c5940110782d160b4001d004282016110b80c026800b080302d01035414000000c00003254410b041101d00070b89070010107502c0a040d900705200030740209009403040303070380000d41c5261600c50402c80 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 418698929 1250 418697679 418697683
    0x1030e01050a05090f010225050a05060703020d0b031c03020313080403061d0d080106080a29030118150c03180309030203010b06073507050610091e0e 66
    0x1580900961030300e000c100b0b00c5007040e00301c0c40c010400a0b00340c0c1c01554500d01c1d03070707800d030300c903e4400e00c0c2e45000043c030036031642c490131041c0c1404174010000d40307a002c0801e0352401e04040c4140d0303c1000003a00895400081a040e20451200c090110000d0485050300d011503098a58640341e6003060503404030009840c4402d01281e1200c1c1680207103019611a00c030300d0316000901d0142480454440e1110703680400b0a030000c0c00300f070340e50b03170036140c003d080e80c68104100c0b03000c68000c01000b6030607181e0000c810651003050710405552458254000000c1d1981d042c5821038618814248024560f611b186000c108002c02c0071081c200d404e00c021800564441080d0060540588814010b0708551903200526070304c8881002628801c030002d1004065040400c50a03001e500c41c06082d042c0d03d45209a04071450000341d40c10340020554581018a26401e040005e4200c0c400a03038682e0008410059080c2e4840c0e056006410f10090410000c9a00d828542ca003171072485060f0146a07a404828400000c2 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 418700179 1250 418698929 418698941
    0xb0c210f070f0e090405330108010501030c03120e040606020c01140414150f03280b090a090515100303020114070e090403180b0912060708220b07050c0708031908060103 74
    0x3036101e2440c00c0e07901f044050002640070b6060076151241007002003420074040c020317141220303000b0514540050458648030b07120994040d511060000380070009031141c0f1070340560030080402d0380242c500304030b5a500251141580b440081c2101c4010441071220444403a01280020000e40d000851601943c6451149110340c0702c0f540c02d0b803503000c81004080c088500768101c1c0b103450008041241c504000d209000d8a1020321055848105040042e80d0704843d940003011440c0110100ca100811195072180b0030082070710410350360b0719049024028035409000344680d0f80e00503d0003107240e00c1d2000c0020f11021342941e86511486201020034149442480003090007006030050046040d51400000b92580c040c2581c107002d81103029401a540c0400702c4c0e05403050344151940340c40c41e82e41070014412807034501600184100d14000450200d004081d91500c54842070701c03416960b211020205103041e038207038000170165008112004482e0b6001e035410308210b101e420800d070300362070380303801038001c0c2103 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 418701429 1250 418700179 418700203
    0x50a020a05060925050a032d080903010606080f011a1b0325020d08030a0f0218010206011a0406080c160b070e01090b03040b0c210f070f0e090405 64
    0x105641c1802401d220108100344da40a0191902c06101e0f00d5012080030b6124910409620000e00c18003000454484101032102d0b840000d80f2264803c0440d000750011181c2c200e0642c0c88420204134107060307040c01d108000140440e414074844500d002c3c1c080d521566414020504c02034400000b00c03000d50441c8040d103101045101c0a42c0f46039103258041c540c0c941000c040e600c1d0b20303500f000800c0d000290500c8180f083c5a0003400310a140001a19144509d90001e010250ba0940c2d40141040003880ea20191819000b001e594010b10100000028506034045e00041460102446880c1001c61084121030444d00d40d400c15080990352490380d5001c0f03020710f8200048945482a0700000c000392003072203038802d1103e6120400110741d841c00449405205024881e1550303400c001017404105480b03285503001050025641c0f83c4078414200e491417804001c224109503484005001c140e051050012340d00012615010b00d5450803190020444002440a5801344001c0d05c08a8284041030040880c035078 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 418702679 1250 418701429 418701433
    0x70b04020f04150b090f1c1a01050904061a03030a03020304020310060b120919080a09060f05040b07052506030608030a12150b27030d02070e07030b0a1508070816050a020a05 76
    0xd80c0c801d102d19220518104102d0302030103080742d44001c0c0021007080d81c1c10b840ac058a0f0452a42e2940d13201b00050001040700c1c80d42c403c0c1e400903102c960390704000900000c4130f1980c0c09a12810302d8410b051030054107038409205141040030a2006902410903512003330000c10703900129440c0c100919007800341c0407080350342d00d500d015014424080d0030300040003039002940d0703030b0021965550802c0b10300305c007400b13440f8000940810041000c4603102c006450503901074810b550310a2100030b900790310600c0d41003c84400c1c82018004201a0350140715010041c0f510700051450700300c0b030803801400098584140c00d06c0030307640d036080f6840702d600d211b081c2c015110350840305a4851091078400c07104803d401020b2092010444603800509001c2801d803600000b03900180b07001030400d00c0356082800001d040c1002c1541e620303120700d403540d64810080010036100c00307030b03001030840390000500b03952004080030203007c540300078040045100f540c0e0320514a0907213890303601d030a841c5900301d0a191014a000d0a64 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 418703929 1250 418702679 418702699
    0xc06090f1109070c02030601050103020714030a0e09011e0b0d0b1201021305010e031011070c0b0304020a060305160f030e1b120604050c100e06070b04020f04150b090f 73
    0x80c00e1040d00e15481d4044444580c1940c2e940021200c45207038450007905604410010000c95009401801c0618441c07440f01b0460460700c42110703d15000484140001b410040c0810624100b20200902600004050020402e900c0c040130035200c05500c11903004030f1000503410000704c40350b4804030800c440205010300c0c17168614505800f0f50031000c0454212103c080307000a482d07006480e402c1845030081c02825044669416010041a40c0e40703490613840030030032220001a44041e0644041c0c001d501c0c0490f140d0401d8014805444410b1b0840001c0c149000103110b80441c498410442c6051145030940c05010005130480183c07440030301e07040591060902d9507142000d0b8541c8001c3d00d40040c4e50030800b5010b100000c598412003542d0282ca141c11601560312070b42008541441640060f0a2004c4034148c00c4020a00d01da00028003500c1942800040c802107291104440075500e101b142d0900140f42c05e084070842c451014071070382210b4440010700c22000d80b103c0c03c600c05056002840b080d19 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 418705035 1106 418703929 418703933
    0x71e09180c150c0209130c0305071a040b120601180305010204090b0102010c09060e0621070305060618040f0605060403030f0206060a03030f11011103070903030210090f02010c06090f 80
    0x14404401790f021847c1d11a00c48015031107040140421031600b985c030b41c5880c0c0281d00804860404200c2013003414003000645040140c807000d906000d807501e20059601120501450005100201000080c0207065010b00b088072008001440b03160341c598012800ca621281e826004102800d009016a503c80d0200d01c44213600a010a45090400c205084880c00c0501802d101d5032503180400c5505a414020190001c6050765800d04101100b02000b00000020000c0c40c000c960392600040c100d541030300800000e11014040e140d4854803410020940c40b064200e201c00340c0301709404a0594180341612104480c0c040e6035035a00c41d074129030201c5090310b4180fa048440d648840905408100141c0118000d11040d141c3d0002c0c64950b00d40a0300300040c0640b403002c80b03413601d13180744041061000305603001e07582443d00c08130071829450700d500249400540540250301c0e0144d4081 = true := by decide +kernel

theorem cover : BRFrame.Cov 418525179 418705035 := by
  have h0 := BRFrame.cov_init 418525179
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418525179 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418525179 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418525179 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418525179 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418525179 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418525179 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418525179 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418525179 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418525179 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418525179 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418525179 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418525179 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418525179 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418525179 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418525179 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418525179 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418525179 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418525179 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418525179 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418525179 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418525179 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418525179 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418525179 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418525179 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418525179 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418525179 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418525179 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418525179 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418525179 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418525179 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418525179 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418525179 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418525179 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418525179 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418525179 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418525179 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418525179 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418525179 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418525179 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418525179 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418525179 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418525179 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418525179 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418525179 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418525179 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418525179 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418525179 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418525179 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418525179 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418525179 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418525179 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418525179 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418525179 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418525179 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418525179 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418525179 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418525179 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418525179 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418525179 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418525179 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418525179 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418525179 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418525179 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418525179 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418525179 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418525179 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418525179 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418525179 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418525179 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418525179 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418525179 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418525179 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418525179 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418525179 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418525179 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418525179 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418525179 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418525179 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418525179 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418525179 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418525179 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418525179 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418525179 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418525179 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418525179 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418525179 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418525179 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418525179 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418525179 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418525179 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418525179 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418525179 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418525179 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418525179 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418525179 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418525179 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418525179 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418525179 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418525179 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418525179 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418525179 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418525179 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418525179 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418525179 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418525179 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418525179 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418525179 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418525179 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418525179 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418525179 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418525179 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418525179 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418525179 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418525179 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418525179 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418525179 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418525179 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418525179 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418525179 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418525179 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418525179 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418525179 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418525179 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418525179 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418525179 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418525179 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418525179 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418525179 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418525179 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418525179 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418525179 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418525179 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418525179 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418525179 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418525179 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418525179 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418525179 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418525179 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418525179 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418525179 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418525179 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418525179 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418525179 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418525179 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 418525179 ≤ n) (h2 : n < 418705035) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
