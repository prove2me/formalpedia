-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2840
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:53:52.150326+00:00
-- url     : https://prove2.me/submissions/615e2718-4c61-448d-8f17-c2a674ecf988

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 510611510 ≤ n < 510791366 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 510612760 1250 510611510 510611531
    0x30b0a091205250c0b0c0c040b150d020307180806160201020a090302010c021302040b19080705040611010b04020c0115081504030c1401110405040f050609181c020d02070b0f0d020a03 80
    0x4170701508140c8286070190114100160400040312104400c040c40b50035920035446448908100759400f2030610f500040c2c7e41d4442081c25110402182d8031840c0f412469513010030841c0022404038011f120700d04a29a140030200740a03400d03401044801d00014034020010005503118140031103000380003400c1010311a5070030b07140e01c06a82c00b0b41c00801d8200030004850900e8518001c50465607c0d0502e00020b0318100158010a035220342e20896003009481410303c03400d540203604c00c60116000074411580c90803201c4206000c0c0c1400042c2502034042d0b43c070001420407020807007800250080545c041a60b41c0c980c3c054a42150b00041560002c0c0c4a00014500e100c09200305180307190240c0d100f42c0c40340c1c41d11003004290b030f09102d21001098105414844130303440c0e1b80b0b8415005040c041d040c4240d009203a032058582040c001580414101221032040c041d0b40208192103a9045a82564515511815000164445c41188039100d03a420050344c580c00c0e0041d4064a03510103540340208090181 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 510614010 1250 510612760 510612779
    0x302091305090703030f09180e01020c25050a050d0215120103150c0f02060703020f09030312011d0c07030e0f060307021b0f1315030b0a091205250c 65
    0x100c03800b9030558000714060081c16001005907008555038503000034420300740240d40d0182040c041a41600c15100d950b042d40041080d0140c6a1004410040311084851594580c8506500400216206040a8001c03946003030007174428080e158082c102c0c05010117103a0070303c000640340d14800e00b071485062105a2842c00308407102402076000c1c0960220b0300d600c1c0e10034207003180d80011150061200e140107401c0d1050300414010b5010101b0f0a0042e00e40b401860307501c105106401051b94107000004011815800e04003855043c0d4041c20001e540b92045110394110120341940c481c40a804103020b144000707803103084107110070303200070300210442c12190b00442d01d16041519a540540c1098210550203450311780080402d60048800c0c005030358018000c903a81060a02082c4d500680740d01c60012802a4806000e0080d5404070790386a441c5031141c500001040c0c2c69404803044403001d5159254a88148150742c050381d140121490202039405e0703048091129003074115100c03c500100011a100d0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 510615260 1250 510614010 510614021
    0x705030a030c200d0804021f0c230a110f0a0308030a0c08060a05060d1401080a1e030909050403030905010f0608011b090611070503011b0e1e0103020913 67
    0x21601c02042d825034001c0c01074220703148050042400441c2e030525600390440002e84100b4604282014201504e550021a038001e03205038081d041d00403d074590300c0c1c1c0c0550007070150010314018802d0108d451800300c514181d603001c8080343c140a9018030181001b003a0102104407440d0001042000d0b05142100440c85030482a03005484021010041240c05c20050042c204441c110345080c40d142d10b84000041c15600302030003a0f40c0101d601140a598000784ca0f803110b09445001c003044034441d071351403c001da41d803d5148022684001d03009100c1c00100c4528400d0142e079a89911032280c172500b8034015070b008040080056080640311a64000458400c0c8601c0d5109d040c1c0042c0406ca03282055401406d4400d9110500214490010841c103c3c9500694403c1904c10300d281c9241d424204202c0d003407802c07529400c034580c554603180d03d0341501c245c91a140d50b1076000e5600e400e212400d0f01000c103c0f40807510180c0c002504d0078103d01d03d0041d03109600906101000405004210f400d02415004444 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 510616510 1250 510615260 510615277
    0x30c09100504150f17060a0b0a0c020405181203090a030c0f02040603080d060503071518180510060c030903030f02151030061e020c010b1005120f0606070503 69
    0x9904c4d0707078900c400d0741d441005c403038800d4020088040346003081804a03485007541c0c800c000111b000031509001240c81103c0740842a80c0080003030001c0d080c5140480c00800055440084602c2200c0071405e0380150007068a1040412401904100b20f464a0990b680d00400b0422542a80c0b141681001a51148038000107140103031a4607403119001031609007207411541000d8401e6012038420071450800170000322148a031860b10100c0c2e07199201e10115500d0b000d170440901c2e6802218001001a0300b90701c0b4a103d820345404402d545c40c0c2c1c6000030b6448204020010307002594801090000c44c0c001c42d0010354500a03841101ca00c1c1c80c240e45403900070603081e04c00000c068088a41040310054115606000d0b5104940fa0020f0321020f102c00c04600103480002420243c40e81c000e07440d402140310980c80502c13030384007041d9521081d060707181e80200000301080d841580c07910002c4600038410010b541c601403a00c0b0300d81220780c440382950510180c000305260340c1b200040100e0760006201f40302914250 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 510617760 1250 510616510 510616517
    0x1e070933020a031103090d060b0f0a0b07020405060a1d18030a0513090b0d110103020910030e01060f051516060e030a030f091208040515180705030102030c0910050415 73
    0x4801c6450000c2c5002d0030598040b04e40e900078813007140300790b0310603c0000c01607a2001c03001590155030800310300c0c05601109040c4d4001080f0500250354045035008200c2c4901c00c940c2046541d48190400655150502806510a1243c1c0ca1082c1041c00010f1058011034000030441c0001c03182a10145950711030350074100042c1c2c02103146554490301042010107001c441006010b108880d80c04a0261030010740013400800700c5140d164083e03402036048802880c00641224495100400c01070050040028281e00d10b620b08100014801c1c010b80c41c0b40189c0d00c2c01080a11030007100541c001a5800100500c014000d0b50707582c03a0005901442201100c02908000c2c50321000003c202034112910601103680c0d01d42403100b5000016298440100c103840c40d03080001054a517820107038600341203c82250009203030007081c04800e09500c030031880c000c084403084401150b1180103142c240e000544111075000030921000e00075151550780c1c0080030801d40342c4a810107603251072107644440641c038440e000c03 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 510619010 1250 510617760 510617773
    0xc0a0b090301060b0c0607260a0504111f051803070e0f0906010311040903030f0623031501050d02061303031706040c080105060a0c0c0e1e07093302 65
    0x20300702809640003c1c03120f2024281000c14000c4a40e803901c0006110b2002c000b01c0030041005102c510b01c0a4280c0c114441d54400d05162042200c8007d12090b9019101072840b0710320520249042110030114042c10340780030b8103c058061040e03506803c0405160099a4807070080da160361010004000105440c580e24a485d081840000041e83c03030103441d04519400c03180051011610264484840702419200003415102c1d038201100202401800440c0076410700200064040282d0702008214500d030030a22405003400081540c0c0e13108031407841c14014441d1740100590701c1c14414203050035001802c407501e041902400c000a5586a810840118004648901410096140081e4005002d603401c014500c1c2810b805803440c10305200c1d00d031194400084044070325114070303005160141d02249034043d1b9500d800700702c81280002c460340c803002019060106924541020701d24015403403a02c070b8100305824007401c0140008402a8180f0408100400c41c01484018a003070b0b00540d45580588207 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 510620260 1250 510619010 510619027
    0x3020c120c04090813062a11040507020c01030f0b0108010e250c06060509040302061602071a121515090f1807080601080919020d0204090308010f08010203041e03020c0a0b 75
    0x3141c0f085070090002c0100040907c1c5640c001c000c5000301d404600003052182d80c080d881c0003c0b0f24203012584603080b90a0400b8407030340395000162400c0e002c009880501080c0c0d940c0d000c0d0000c0314400d21410f0300040345070b0f00401c029004420482d0f0000001c482d40e01a11030b046800618440c051046000001c640e03c0400041c00a01d00c2402b018010803500c0301c64074102510000c2d552130010f00201d500148200820304c9070340c020040b070001803a5500c40c0c102d030206810080303500f581088001c501c0007501034000890101008032001820320009200a201c1c0420040601c074503004003882507081010b01d0f00c0b003031841e52032003864214450300f120140105e20b03003640d009120f00400307404641070194010a00504180c0803410148804100428100714065030000440c050030f0842e02940140c5446509c0c414941d114403800c0c107031100100404041030781c0340e40080c200c0c8801c590140100c50505940c80041c034090011510050092048403288400100010f40211459204c003100000010707a050 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 510621510 1250 510620260 510620287
    0x11103130f050120030a151a0c0f071203030e0304030533010e06030d030c0f1112030702031207020a0503030106120207140705151e030c0f0a0806040e0a03020c120c040908 75
    0x141d02000087c1041003891508210b1802820a101d94980041c0042426030000c1c0b020000764944003502d1003201e032240d98070302007920306080ca00c0c0e065002a08100c40806001e000004980859500c040280311204034018040c1c0c02d485400c0d4607050002d05a092601580e5508034124040c1040340709182003402d0040030180340c201030b500309109260515100410f40750304070803210106441820f121b400344494207412418130900c100300d0a1000c0c404014440401d5001000c0c0001041001c0522181d13100c01e5420f80e6078000c02c150003040c4d64410001480420300c606200d03000352001120260425106607501c80c0203400c0801858115445100200510b2070520501c51785100c00101c01880c080c0c100c0110194410030080b05c040101001003c03c0301104c07900701311120301018922480c0c0302c41c0300fa10010a07851007903841070300c07490400341100c100e024003064207224141e06800801c02d81a40745c0610200003402181003049008641480340c0f240c403603000d0007404910030b00100c1e40da14500c2e400e08 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 510622760 1250 510621510 510621521
    0x3030c051f0b040b0f0a181119090602030f04090c03021b0c09010603020c1e0f0d030c080a1a010c03030b040c020105060a0e160305060f100f02011103130f050120030a 73
    0x1900c0b07480403043d140b0445c6c41d03441109040d179001c0000710000780000c21042010300000015041d0341d040020360140c03081c3e001909002e001980c1e5071910701466442004903528001c403d442087c051041004000d0100e590380b0124940015050250030b1414078060140b108080b03e0b60310066811105e4a8181480c1000705c543c00742a0600303045081c90103403a00c10740e40d03030912003120700e2204202040346580d40d410403110302ca2080c400101e0310f503a0b030580001800303880c280400d080816003540200f80c20f500c442c0180c5500c44050403001880348451030045038841d452400680501d907480f2103c009a4685008000f1001610780021a4500340740c000e2045040e00760303010307082c1080345009102144040001084514007145000b041603110140007135039030850710810390303030110710143d002c11070319001416014204c5094008200384252014014458402190340101c500003070750f140d40001d007441c10801c5119004000002c2d004440a00103889441c0031414030b40c40c8600401000160345007030040 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 510624010 1250 510622760 510622781
    0x13030c0b010816060513054c030b0f0919050709050112230a060519050913031e02031c061502070f030f02060910030518010e030403030c051f0b04 64
    0xc0d454080d0301c2c0c07485048500c0c07e0007154400d01c3d0200380500e641d008a020441400140e80304051410407111030000d02e00e81c10150512070302d000c0300300c2d02d403100e0007407003020140c100c09052003442c0500030041080071500140985a403c210b00f01c40810105c41c1c3c45032511a4240e92100034145003090f001400c0e10345203019103100e0038105519503a002e00c999170f400f0b412099a50541c5150386540c841000542240d40265402a03054005025042c14481d14001210310a603a40111600c407400e032102d00201070080540452401c80702e11004a00c02c510701d0301341540d9441a80d00700300c10703c0c80c8004241c00c5510f4134201d20ba110f81041c450603140c502e1110040b030041c00144200c9240091015405109100207401c0e02ea21215807025501d070441100d101c0c0000514000102e08022000b90052000381d90740464404041101108145c05105036500a00c06034000c42c28180303580d804880ca4040d01404644e107005036050050741d0901944004105288000702059108000c6d045c04112a03280c01e0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 510625260 1250 510624010 510624017
    0x28060503190f0b07020a050102130501030507110604291008150907060513030f05070e060409080d0209030a0b090f1c050306040c05040b040b030f0f090613030c0b01081606 75
    0x3600000403002e901102c0c6165001d5002e00880d07076000000d81c2000c0c50448007810b1540002103d0b07503008045000c076803d4983c04d80b402c01c1a41c032038000c1202c9200541c800f45005600100204020400d00e0030803414100b060558001c0252940700b800036041001c2e0381451501d20103040520600006001496000d0b0410481262510301002c215594000c0c620806040c84000a00b0021390740c403002c0000080d5421850008a01c0102c4c81c0695680141c0d00c5640c8403040d81e14040768080c40d1900421901540001c0c0c464102075180d0700c0302000b9030042d02803d40c94820300b441c00e00020070000031144100d0200c80a0408012901300e42c0382420404c0110f140d00e10010400b801070240c100e07042d0b0740c100360140d40c00150606801d0301641c0d240310b2074001011490011800003820380f03a41004601c900c4803500e1450403900e07602d07001c211160090b0b8260b00c44d13410410000d450b100300f448003c21082c1c001d1805044582464071203444030f600030b8001c1079050700001d8151000d462801c80a8006203940d18 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 510626510 1250 510625260 510625303
    0x20c07080717060103030e010210051602070803040f06080c042417060904030804031137020303071502121303021b01050a030c03020903100204030b0903041d28060503 73
    0x4954640f02d46050000500b0301500c0c90318032116903c2001443e400480700c803801c0141e400c0100d41e41c5a8a0213200d001c50041c8a4808007040d90b0380c001c0f069031708a81c2c401d4052025203050a90a803240d03c8003c0002c0321040c070a210001d110011001d2808220f400035a061100d10400c02e030051800c50151180a445070f650020300c5026103c19100320360081d01840c2500c0192602c0c582120b43c007603c80000605840744003880c04183d002e00401a003400400c0c4049c644014400c02e03200241d10140d000039526810a01050010920a030300410311090b55603c01071400d90010000a60203209941d1520005c48a40d41502010340401240860039104080d0340002c0900e0340000b0246d102c0c02c10b1810406865440310b000d414041c0d019541a08001410388150f624148031000094100b4801640d41c9800701000c00c06c8070101108880070303100200b402010340403100d05801a00d40303000e400c45000c911400c80c0f41300034140b8812100c81d5030b00555804a0f0072460081050b01e082082000310a4414508 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 510627760 1250 510626510 510626549
    0x3050105181b0d090605010e180f060f0624090f090415020a050702030703121707090b0703050f0a080406051006050711030c061612110d21020c070807 66
    0x11a5200382c40a4031000c82d602c465003c00c0303a000d030001c0c1c0d0700280100e083c500089040e5400d00c0705244241440c03c26607000e0384d118214542d455801e0203004030280c0020010a60100e2184855580000e0142c16181ca01d58070081852400045e4000325049030404542c0721264a8482c11020041c50100c900c0c0c40c50303052984030000c031100000010794100780e0020340014954000c005aa2145d034006042d100c0890766818100301424050341040c0000f119001d03c03019030708501d84018010f81c16a87d410030070700d06080a0442e1a4410b090550074844184600ca104075051002003192040d0ba40e903043c1142132915158042e1039014104407007207a414a401e00ca103541c41000e80d5000d5401c0711030741400b05440c02c046400d003040c441c41c068204030006402250200411000600755200705107280c4580032020003103800351000038504282d50040464041150b1090010743e024500001d200600035031203080480c1264044100e0696603001000100300182c0305101030801005041403904e0b620f20407 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 510629010 1250 510627760 510627781
    0x60a02030109380f060a0306050909030406090e040305040306060902220b0d020f040e0708041a0103330c0c050c060403110603090a06020d022218180f030305010518 72
    0x7610055500710f141c0440003030b15500e44d41c18204d41d410150030603560310100032000307018203114040c3e20300a454039404112103040c000121022074945644501000d4100900101702c00000381054041040c140000300c0800d605200da0401083d00040050b42c451100d038848444801e41e01c4006c0324404800420441c40c2c080c103007101d0040381f07140d00040e034a21a0011080e85070059800c00407034060800c081028143c2c0140c0001d02560282155400245024081d840071440901000305542156680a0141895400310002c04841d40182c100380c0e94254401808584032100c0030390001d801d00e8088414801e051043d02a078500c10340c3c3c40e07481c0a00f1a100c101c100820020558020b000000018040072820711080910a0f40200c096645e460030748e00c088069005129a041c49a8011200b00d040071403c201c1542100c11810041031200d402d045903c00800d150154070350035000300c40001002a1075241000c5080d0b20030b4500050550520041c4040201000d0552210229071020f10031804c12 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 510630260 1250 510629010 510629081
    0x1101030915020c03040e011e0807052d1905150310030212160f0f09020903060403120b1c060e0a031209060623010e030111071b08060a02030109 63
    0x22004070140c0c0d03031110301004600d5882a43e101803400c003404400442c80d0406001c03014602c0b81c2040c15004915124000e040c1c81c1d0030280b09056100480d0403c603181c94500416803000004d0400f080859190440301046a40720b4170940321400e090f803d44240100e2518044520b11500c440035030a042d0f24040c040300000803904d02020348070340500c1c12420100d18041103070b5005a14911001d4180b2644c541141e2288031441c0600056038540a20100e540300183c400d480841800900810f100c1d01d0700d0300c081d1110140000705e0700301151140d0042110340c940161080c010788004070780324910311690410900710ba600001c01c0c28507401c441c8901000c02d5028459601000507018009004a01882d01000410305640094403d111014800b04801b81c0e03c07140c08140882a00d8480c8081e00200406080701c001d12005114103006001c10000314040030f40d41c8110080c4034000034030540d2241d0399a45010401c46003400030769000001030005025078001c404410302e040150030f41010500d80c88020819 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 510631510 1250 510630260 510630293
    0x203061003050618030f0f0405030705060a12090804050d0b1006030606020a24050703020904050105030601180207080915070c05010f090e27030408150c190c1a0411010309 75
    0x1400c07030078003500184d0500407a11412654407400d07a4540765280303400c81c5504a4828203110740580c00c0001290300f0500c04891780020580e4403003a04403031042002000788140642515026000d102c08034a54641000078640c031030048040007005e103800640c0c0c0125902a8201c1820541088400c1040d29000200111503550141d0100d045d01c0c00b81401140304107514a820100303608001c2404030841d0580e0042c41c0034442035034240310507a200c400b8076540b446c084c4504002c1c2c01c41c000201c1c0400c0007a0740600200c84c41031410a2601031801c0001c1c0206841d401061400c034400280f081c10030884400c2107000b003800782410016909140400741641c0d41074895030161130807000008031078802e9498210040d01010f210344002c5c610124090303640c0d40081c040ca044034403c540025125000d510f080c41d2280361500401880c0286a1003010307805031f001120841070010501c2840001601540c6416401d00049400720003841d00c2d08207c02d194001c02c2540307043c14603100c0c9503004508658024070202 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 510632760 1250 510631510 510631531
    0x70302070e040510050114031b030d03020c01180308090f0c0f210a0b070201360302071d0412110703020f0a030218060307050631080f070302030610030506 68
    0x15511403c001d410400301c2140300680b1458000080f0b94004085002c80c50150194119135818881207003801d1102c1e5000400381d07256210b0035011280c54400d4004008a41c0b0020020491a6403003c801c1101550b07049d040b4003141803a8100011154104401607280c508180240014228503021841e82d00c4240c8407240640c120031041006005410540d0031004100b00486200d800c032070408241140080c0d03000b60065080408440c4501e0904000061240712500c401d000c1800000f049081d480b04100300b107056000d401b000188090400e00200040640203019042c3c4d8501480c01017422003084043c041400320018007515504000510882900d9050b2480c0515007543d400003101100f095000030740c000c90500000b02c007070301c4070002e00e80036180580c11030b1042e030340b14400c008081c0540b1194402c000100703c61813800110b05075075500c00749600b039202a8840c0e110180d00d800d201070b44036400d810368071110b0b0030800c6042c00c000c1c09078401c040200705001a820755646036101d000140c41103001 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 510634010 1250 510632760 510632789
    0xb06031b0906070b0a1b0e01080109020c01111c0609020414040c021908040320030a060f06030c141305090a060e010e070f0311010f080a0e0106030602031003061107030207 75
    0x42d440c1c00701260b0080d900b1034158005440c00c40c0790314000c0c040c40694000200c1050a40c0c0407007e01440f01c06110120507191040e0507030811040f84001c1d00304000212896481d648213080c20000d2500801c03d1105082051550410380746525040d501c142d4004010306104100400481d5036220b007025020600b00e801150180001c1012850a207000b403807a6404c0403505075a6003000f40b2280107008580c803030500c16000d42c4010900300701300c0301582880c98141e0450035445000810700d600c00c2088252071040001c7ca40e8680c1c80c0d808000340240c1080d95104056000001300386030032060350641e452981c10a1000d4544030312455214210380344000d00480c5c40c0c08103400e25003029040061b401020008032548c09644e03803c2c90422802601c4150740720303522841d000305254468561554500740649580d10303039480b00600301d402009505512441c0d55070703400002c0000341060000718024041900d500c0046800c606150007160003041040303081c941c003013184400080d00498004110381513a00044070 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 510635260 1250 510634010 510634027
    0x30204020c0f030d060512010606080c031e010f032307121a0903191b030f0c0204090b0711031215011101141501030207020f1011010614040b06031b 65
    0x140c12400d41c0d4070001c6001c040380e0381401481550080c801c80b06c04540c40310044d00c00a620340e08980302d60180341c0c0040c107010001255a51010001c5410040200780031480a00302c13031207900140801c0c0c01c8000c01803811003041040c0107030b00e6902c40c4590b000c03103072100b0310088141903a03a68101600c941400c80218280c4182401010900c225100e968055130300c00b41d09c0c04400e00360b1240d00c00e401003040e0000701d001d44c400c5640320348092020207204880b041c055851640b800d80d5040781f516800810001181c031041d0041c1c40c1c0c0c0c01851201841385040340e10a06180344081e20b09035044003080c15540c0b042c06505012039025040320f4100e14806168000f114401004a07800200f02001880d42c0d8284440402d001c403204410900c55440d0103207032070301040c86a00450980c803541c04042d61100740450060041d14010307020b0950300d006800c1ca040d24540c1461660b0035100c81b540000100c0e48800f001400300c0c1080d0140d4401c1503003ca81d09840c5180c1b141080d0b600074030b44c130300340d82070031303034040b91603203 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 510636510 1250 510635260 510635263
    0x140708100e0702030c1902040c08040804050d060605040c090312020f1b041808040311090c0d0e010b280b071505040305120408030402040b030d05120c1303050d080106021501030204020c 81
    0x500ca45d1001c03096909141c0e0880700c0300c0213490801c9007207008515012102d15214843c00c811801243d0044e40c4500c0c0034a031400b080b506000c0d081c4180e41c03142c3d452000140c1075075184902c88002c5142e0321010807052950034204401f080c503513802403d54000d2907a204003000080381d44100a442070000200d000240c0300405d006085000400e101c80d01318035520070a0115050141046030320608103115902004014442075000c191400034800714180006c01d00340103160061010340207040300004050504c0000035202100120620301d04882035032401d030900d182141c40d04043c01d5810307500d03450324000e50303100c9920300d038550082428940e4500109003010301c124101d0b038504072810300e82032039418103090a0034107600649049109500e404180d0f8030a06011602c500602d5541c1c83e0b0714181000418007003160107004204110b000800c01100101c2642d840079580651301580c000c2421440e070250291440f10b040e00040203642c80034801144400c0c0f0b1303152041c10340303038180c40168654030080e4419 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 510637760 1250 510636510 510636517
    0x3011a09040507050904140709180b0405100501230607020f150702152a03031605091005211308070819030b0a051203040623070303140708100e070203 66
    0x1d030b40903d8000c140414001c0d040140305119070404103032022540d40d00d80c01c400712001801c046044d0000304502c02b001c03421900480d40d0180c011030582d0404829654400103c65090f00256003118858141355103410840c016078003119002c3c2c661600e40009a00001c8405854242043c401c43d400c03000c0740c4d208002101070700c3c006035002e03004001c202c5c4680e40010058100550204110070b40d41e1901003020b04403d00510040d2000003e54550b0b207610765141c0766440d00d03015410502104000400054942c0781e800070048540d9a9401e40391668010022020780d410441507102c1200402801225441c569200320559800b410a90741c8014a01d0855030714028504840d29440314114000409034154021313002d120f208031902050207884404020b90f003485100100360329802440203000280c003905103c4000350342c11044045920054030680096402104214002070b01e60301c8041da500e1030401c00382e41064042c18042420700d007481004954411510a591420b800400415680750007407044 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 510639010 1250 510637760 510637769
    0x33702070506070e180a0c0504120b2707090207110d0308010f0605040305100b060f0304050705040513120e0a08070314070801060e160311030106031a03011a09040507 73
    0x540d1a50501d081168690008985075408198140680c410b94584040e249503100c40c80b541c0024680ca400e52003100030b2181805000500008000118203101c807c00c0781310400b403080c0600003040c50030004650108181203098521441281d5688041e2200401c250303099602c1d2840c01078480750282440380c8c800c00400e40c41504001c024800e901850342c4003403068140d69000a0078411240c2c3c83d5412242817103940700c060101c0e04400502000d10503290003244054100416143c1030181403200862140e00035102240c15601c0121b08000b641064000d071548441442d140c6010b526203a03e503d41c912001c550301c00f041140c02014070803aa510304591401030312000007110a0b40381c0f00e180014002c2c05240b20445070f8441c40343d002600030014003540058943d100400d2400341c55101c0c0001d080c031801210700007403684a1602007003007440040034500910032507602203480c0900040009403e090300c010700740280d05082201403030f079100c02e1412101c0b200640d121043d55a031807c3c40da0402820303421 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 510640260 1250 510639010 510639121
    0x603030f070605041101050307090501080c04030203010203010e090d0212041202010908010203070903020f1002120a021c0e040b09060f0d0203030904020403081308070f0e0405031323040203 83
    0x1249070a102859016130f118510030b4651190a9403148019211400201c1c1d8880c0000c1d0864000d000b80d520a0304a2608004c081c03a01c0303404d0035140c1d40080d099070403d030044a403005a4100f00842010104044179070480103002078008030580783c02800f0075115074040e00d142c00300307904949011a44124035107001480e00700001c40d1030781403010004080050300e01c81648681c4d820318044005241c149603400328800c2d40c3d00200070f4810b192416030711a801411030941540107100c42c1410f0000d840d84050703024201591012034840e0404204800c41da88011410300900c19902044a25260024030030020802103d03045c56225a61000078030f5403041607200c6810034000f081c000200004140540000040502c481c603000d61140380c62030b40c42a861182085161240004100d151035000c030007a00f0500030000d407803401040e198118007035103455003c44d02c070f50029040000e403080d40c110160000b09003298194036500344a070318085800d1050104002d44076080050780da640341c04210307209100d0103000 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 510641510 1250 510640260 510640267
    0x60f0d03020615040b0619021e061e0906240406090f0e191502040504050f0901061d1b041503020c0106061b110a08101a0415060302030603030f 63
    0x5030080d120796080d00d42c001c554502000d60710b92403805001d40e07200f42c44042d2420b41000300490301e00c0301d0030114010039029401840451070f070b80c28642580c1780c13202183c18028501820031200c0d548401445844d11560030720300d81e00b8081410b2000c02d2a0340c100343c1e003003c045080d0880c00740441c050358034544459445840c0080001e41d82e01f0503044030005104c030500c1000010030480d00d641d11001d051081003101c0000c444014002020b0320b60300950446a614010304058880340402c0031502c050302d031045100d600e1020444242402d00802001c4d0a01c1040b2075880c5903074540c844a070501c081c11051000c03503180031504c1c0e640180d4007035400820040078442016080001e02030020341c404a84d80805500700103020905c40d02039a10000070580d520302c0781d551b4440c01d8540c041c109050050040e400b42284500245048040001c1510302d91840f8000500f80e4004c10300310552904120058010b60070440702d88040c2820880c1003040b40d405043c00f580d130b60342d140002425842407010095401c01d010 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 510642760 1250 510641510 510641513
    0x190c230c040b0609060a080c040f0e0405010c0f170901090c150e040614130f050915150603060d030203040806010b0a0f18052103030703020a0813030206040b060f0d 72
    0x9218a03010310984042005060510522115110309200c66800c00000c008000c0f000d0300c1140580d6008071503104c040c0c201038075400c0c440b40e034041603030020600301005014401130150a102e0244210154280f094003000e03a114050b040841da991008130840100740002c2c8042c0d4290000c00e41c40e075003c024241469101d4190002c4210075107015400500c04071482c00103414544189410750f60380301088403142902c007003003004600c500301c0e083e0505034440740b003030040184502595014948440151184444040180c4994880109030b0304074403d603201c0a0040c0e48414040f81d41218050b00c4c0c92081e145c1909090340740d44a154888026803007500000a250311654010b0200e244d010781d600b40801d001c0340011168000713004485002c400d6120402c00c01d0340b92103246201c000b06e4800c5c20840c50250210b1160440d002103490030007098000402e048c0c01c2d94813202a40d0b003e40302c016144d00c0c02e1031076200290340c0e5000900090501d0885800304002d0b9442c1081c900f2240d100030800e000c10f03141c070b = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 510644010 1250 510642760 510642763
    0x3020d090f050a17120a1a12280c0302090601021c09170606010e060a030b03030f1b06011401050d0e0d09180c12020304021c05031e190c23 61
    0x45042e5091580d040c08102942040c0e0704841c42c554030f89a1080c05c1d9210040c1c21801401d0001002c80c00d13010408111a82d602d900883d1007a40075080080c01c00c10301c609076110388984881c40300001d501c40391440c0e90002200065040c3c00d0f84d405030b03251a407580c2c4200060f85041e0102d07010f01d00c04c7c0302454041c84841e900440201c161a134040c803400c10003103102c42050ba1101c080c2c03403650100707540b064020800d081040250004410a180118510701c1c1711010a04541c048e040c0454002000a1409403840c104043e800d070480440b4000c003202d6240c10801d201c00c400c410491070400000207800e010b450281d4000001c514140f20030b95850b0100810041e103614014415000c8008200d14282002a018800c04c0110f840d5500d5941c072140d1307003102180003988018001c991201400646446100b01d03249100c4405100d20015680c900b1108040c4480b49945100c040c02110100410414801a81000d0491364900c0c140841818003030320b040c115600300d0200d021104aa4401c11151400d070 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 510645260 1250 510644010 510644023
    0x11707180e101a010302090915220509010c14030c0c1006080d08010510020c010c0501060b0c03040f0503011808090103060305161a0313030f050c0307060c02010b18010603020d090f05 80
    0xc81c0124035144403c41c4015810307406840d00c0150300c90010000512241c0320380c0c04c200c9100700002c290452102c1e030529010140c0c040c00f04510703600c5986504004441000b4401d04100d941c040c10445001100201c0c18221480000e00601c60100d0100e21616800d4041100c060700b541c03a060184001604c550b4407554034010524910001500c2074000152414800d00503031450322181d011344920225800155800e01c8081030484081d0758841c1c1c0040c0b0b014070030025000c192140c0f409036a03130320318040c5150107140c0e56420040c400c0e4500492442c219a40840d245811680002c444e901c0303500a0380180c00030015940042d2050142c8000c29800d00c0140c03107031005480c000748a00010b01c101110960721404200e42000d94283c000e5184004030b405070a68a2100080c0e1525914100034100c1e410f0170760b0020001141c90589450b6400146502801401c25100701668071444c154141240b00710240018031841042c9540062000034a1072150090032029030050341040410142e407418603138416 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 510646510 1250 510645260 510645281
    0x210606080613060f05010f09080f0a03020d020705010219050a0b070e1203091513080a050607110d0c080c0703020901031a0c16030f0c060906050f011707180e10 70
    0x402c1c1e410a0681c00304a206400945500c5101c01001d03a040000640f10025503090001c00e000200c440050401400c000030355154090710302414428429103000303445d140c40b0140302d17020740d000088140030a980c00114107221400c8000c0003d200c1141e424101d0511010013809400350a4000400c4000c9400c08843d40c4041d0042e580840c010104420719a2039001e0303122400d5010003407255580d86c2941e21405403501c115101640c1503869555952246040d424050031100e41c3c000c1c0c400c028049801c504075400c034446840c05011103c00e5a100100038078540c400042c2800d40c041441d126242c0c0800504003e164081c01c450300c107507128241a8001300040c016016692800800203003010a03210603141010040e0b0116040c040c42030341c0903554003905103001810040070000c0c5c40c000c136031140600040e0f0740c010080001d4500786850850210f540581141450089030060340c0c5540000054a404442804103141c410500c120300e840e01a240304c2070352030702c01d00c140e9591680d2001e8540c030092059 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 510647760 1250 510646510 510646519
    0x60306020a0c2003060f041a0412083103110a0606090c03090b01090b011e1101050c040b040308090a0b040f0906051c20040f0e070b070b06012106060806 67
    0xe15040d000700c0c4000010300030b125091740040d00407a1040d40440c08494001d481080144442c03103030040344c5c1c0c4030b07440c08403410b49411545911718800250040c0d070325500001ca6a140901040412611030f0700340b00020028554401c5456120043c1b43c81652404600074607c1d080c2e4000c1e40b114200400901858050490b00c60301e000180d400781400380c03080205141d0702c8143c040042c2c0c64181490010003d03e403a1a0620a010342c03882a03100c0b41d04100c8030f0000040c1c846140280c080c16006003119401002541d501204000c00d10210101109030f600300c0b541310040e15030360a00302010466100d600d0307000360301c00c0c0800311340031810b170404a0000c0140c0f100941c040106554030b07410800010190003030503980101811201010070022083c540813445045510440d900f0064042030455080c1c41c0d000340c407180e880c050720980341824803840d0024010001414181130107600c8500c0c44002c041d0240c1d0620100c005c45006a91201900b1203900000000c20061a0b50b03608000e0000300040307840a109 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 510649010 1250 510647760 510647783
    0x3170408060f010e06010c03020a060f02031e071b06060305030d02031b040609051201022701020d11150414030f0a0e12070605130905010801020705010c02030a0e090604060306020a0c 80
    0x58801042c52207040352030600200c0c00c42d4070b4200042d5542e0100070b005600314018500000045419401901060501103c00607500d1820b110548900c0c000a0141d5070502036071414090800d51244240a45826420b103180701034105151110003400e450780020414007000c02d000d02e82c81d40540c00346205400740c0171014004400e05103203e4552042d4042c1401041d0044010f200908000c4510180b644102000500d06807600000c0000b0442e210a0392940d1031750580d0301441942d050002404007042800c0c4004400e6851204c40c2d15480c0203c184846445220000b8043c0601941c90034040c0d41500c1c00d0f030380d4804190032441e010390302050107000498840800d035001418080d00c401c403040c02c0c81024000840c240b01c0c045075180e20501a01414044003280880e04141c81c1c490031740201036010006035609c07a907261650a50380c03410410025501b062100350f60558000d0484014554202e07425215a9504c8000400500c1c842d0005802141301140c84a6926000072481d0300b6035004000c034110 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 510650260 1250 510649010 510649021
    0x80a020c03070e01260a110f010c030507060504030c23150717150604172107061806020403110909070807050111071746020a0317040806 60
    0x2a02c40842c4500300008804000412038024003c00040044d10901a03050b12000c003c0120380c41d001e07440c1010303124900f05006814061800b052003020240d800c0c01d01749807914141c0c802070a2400703014400b816194841e4000b5003003602c102c203c0f440c50340e4445048040300c941044807040c0d074410030000026600c0341ca071100d641c1d07503c0500c60700d12404040c0d1740c005840315101020391019070040d12450a05c5010542d2481942e0780310003034405030058440100c1e142241030724485c80c1c0600f000700416100c06e2901f007140307140020350458060176000940070500d40080040a00700350100c1002034160b52020801000300301d00d0628250780c40b001124144440c0d00c070990900d0300c40905105a50403648060300c1000994003490200d82803520721409e8441c03081e920035003060800f6402140b15082e40241025012034162a6070622105c5056250340d000d59600e4101c4100e0050b800840b00b41c00e20500154004568852100d0805036502850048a80ea007110250295030410302965509005c1c0c13400142 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 510651510 1250 510650260 510650263
    0x120914010501120614042a08030c10050a1a0613051915020c0a1a1b010c12020f0d020f09040c03020a02101503030f050c03030f0402100503070e060f1303080a020c03 72
    0x140100c0e0440c000d01c1d051111003038412147c054418040030411000f80000940d10310500103441082613000207046503190000461044407001440c400a5901c1d107586082d440b5204131b25002c1116041e1040c995401038065040621003076980003942c031400b400004101c4921203107d00086403011002e0300703003413044014166215170804800720b400c001e201c50700700100140010800c82d18401107092514000d40320444900400e442401200581e45803001100319980c4004401c180c603a0042085041050700140c1400d2031092201040c2c110b81c0202c0c0100b40724406000300c3d107031071100900c10003c41000c0034000c0c029400581d461009070203900a40540c0c007114ac000c110b0140d10b000003080040d0b00716034065840d1124a54001c003008000c0c807044007651410401580255451140302c01c2c0c9180034810081320940650300c4504002040c4103100215401007007072000b4400890314591076060b2040c800b0103e005007098611442101d11000013407016460050407489640d6080d00c070282081d00038035 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 510652760 1250 510651510 510651551
    0x3050319170411040902060d05060909070807061206150e090c040305070e07180f0305120a080f04030210141509090303180a06140f161209140105011206 67
    0x8015400c0c1d800008002942880460160140051002070b03880802e03004a00746400100402a04698660500101e86080e09085038413404000c001e0501c2d50414a10340c0d02d9030b0315449000300744060200b0600024600c0e800810140000041ca039800f03c516500081c010803c2e10700340ca000300c400501041c50030040b0800c5800741c0350000c000b0500325103411240c01000310018000700421040b0089030601d1405940303684000d100e40d40c5c030146581c0c103508015042040d49150420034000410566a1131038009070000e90105402c07840038081c0e521410182d0030310340050301d180303e00d43c43c18404e404407084041800d402018030700b90744081b8803d140240b009008090b00c4104040d842400060740d02090074210f801c0e41001c0c00151807504000d5074840d416118140b800c080354004100030840940401c0705c800b540301d010b94900d00403942d0f1410019148007515504800411385a503503407002d109540c0c21491017451900b00030021503135111040c00316229104000c65005003800d04000c501400078641 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 510654010 1250 510652760 510652787
    0x6060807060905060702060d1805100203060d110d0206210603010c02030301270c09140102160b0d1418160518131403030907061403040204150902030103050319 70
    0xa40c02c4a60034041000003d030080c44c0101c0c1d002c6010070059031468554040c001c030440031443c0118442d541498182e0501c2c009c02c0301c2d8030070207105004000c4c1c640e54611907000004d4002c01e10010040300a07020400c00706042d0f43c0a50040b0700001c00c0e2600d680001058a02d000030061f40b120a038a4460815003626a80d0b00601e00507403062005005e00c400740340305400d110540100b800d01c8858541e0070842650b800480c00d00c0071a41944c010800f003a66801c61421000c024405011103051146140940c101d480c05400351b0803e010076425205580341c2c0c406840140481e030203800d946000780c17406400c2d4020550810303041c02150310380c0d9a45400c2e980c0c5035042e114020410414500c00840303100070400010141e251400d401e401c56070203d610341e00300c005a209c00344095640c1f861300820701c038076115803684250300b04030000d9105e000e1030300d05809907900540c2c119008200341100310900b0960584030340050600c0c0e440040008108100000100310901c0b00380b1040c81e41300740984040d03411580c00500c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 510655260 1250 510654010 510654017
    0x80309090711070305070b1201050609030a0303051b03090109020102160f0501050708040e19050c160f060902210601091a040905011104030c09050c071713210606080706 74
    0x4541e0340d40c0070b04480411640008100c0740e00c15a20b8980d00c1c80c01e4a25440200420400921500280705521495024205c00c0e00da462800d1060404640c5d6488031000c05400c155a034be001c0b83d8090307011401c0b0f81050106aa00f26220700380712450500038a4141812400340c03185402c00c40310384640c0703e0018201c8880d0700030b0700641c41c0351000544560340800c004444442e02000701040c1003c903104010300414240c080d20500c1d100b0301c1d02d02c00803500007030020b02030703400c00384007000100b59502d11946407940d0050075401c0d042e8803403500c1d102070500340b00020340c08000d54070701404140250701004c2000f1545000c40340a642c5c0c4062b880c0c119100c0038106e40541400301c9500f030407402c0a40001c44c00038480c00001450040b92410400703640c00503041180c200c00000c1d02004812024003e00750081043e03444649440f074659030360f0b80d21280070304d0440c40c1ea07280030520710b41c0e01c529022400000d1584da515480d10910400105c800c48540c140d0440d0080d15084012907003400015811003500c41689 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 510656510 1250 510655260 510655279
    0x803010f050d080d0c051603021005150a063c08130f080705150901090311010e03090d0f0503070303230c09041508030414031b22020c01150f080309 65
    0x1542c4d0013030300b40c1c405d024040c842d0810900c4100b143c1e14489200c8140a90b008c0c1981c0114010301d54240c80001c0d18040e40002e80c880c0215071940d071100c450b0300302c1f184d5003024203d030701840c02c80c8041031852803840d80e4014141d0030141c02c01d543c09032019500318000d550780a03c03075a45c114040700c0340304000c20140002d04002c007400002041900280400ca0080c0700710780305a203146d803100c09032510841e94141540d440d900d00800b0075800403000c40035078420400a00901d13402c240c02c80d589000d5801d40e28852201900411f0900c14020601c2c0681a040400d480c0d42e00300900b8007070054000b042240000112684401d00c900302a580814003130003a03000c420f0316240c030f001e0030007000c0c000d00d030680048210f10280000f601d4404000810080a03210b03a10703480103416608043c1000c43d00310a1209800000c4101e0350641e0310b160300c00301014500f02c2105032089814950000034040c5c18203802e0b0541c80c221040c00c7c50894900980304807034168103440740058854600540303034000c2c034084682000599 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 510657760 1250 510656510 510656527
    0xb010501081b120603011409011b08041109060607080304051f050f190213080c100203030f0a02160519060c0201200706090c06080106090906080d081f030803010f050d08 74
    0x19120344c2c02034070060011a000f950402119180c00d0143d40c103d40d41d030340d203151034803028802601080140c68a0704000746186411b86611a600c1c0707001e40f10510032051080042d030076a076914159203a250300179a9450700c9240c5864956603c10503060b030300f440c915510b02520321814440c020705100300010b844074032070354448600d85d002c16000d8003c82407400d0b80a01c80900c0c2c1f010100c28081c01424468000d140e08410242400070040b102c46414045404c1013003049844142010307042d0300128403e800503a207039242e803800e000b010365101004081e409807165440141d4240d0276210b83c0f583c02210304001c00000d075907040c1d08881c0301d0340102040848880e100b07c0103070484006405c94900542003c124800c65941b01c0208420540000020503035110041c40010f80c040c2d500e0300a80390f8800c04100c02ea040c110300329501c45202c6000e41c100310141c0e00050910041c400841c1000ca002149403c3c580c0e1a458104800d070424054a0801b84d9030884c0014545400c041e0082c29035003110f10716103010f20300c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 510659010 1250 510657760 510657787
    0x260307030804080405030307050106170a050d0e060d050f0403091512051003020405090a12141605100f020403021e01051e0c100b030625030b0301060b070b010501081b 73
    0x74425110484103000c001011b0301d0600042c0f800503c9070000040190400c11007003044000004011000d9003d1900700b000554002111045070200e0f00b40000d03407511030000039426108a1210109003814181805101d141040c8440e008501c6a110406420344070107020420340d609420f5980010b010700e01c6071005104560045820070b4031600c3c1c082004d602c0c0d401040a50300199881417036548080744c040c05101141c00600a04c80040c81c01d181d014506002640c00c6000e0007140e40714111a040314501003200412035400c03507140021040c4601004201c0b040000d42040c40260b014290169040310a0300c0c489408040000d8140c5416042202d0002c0c080313107584440d80907000c206410880079103400020443c1103030450785801c0c00b1034280e0701c2c40103050030140b000e4407018403845075003400c41403151030740341507003803000c46103000212043c0110019024007001d50142c000b03410300090003418040624012070607110207803036118640c0c403104002900005850030002c90800284030b102c024151 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 510660260 1250 510659010 510659027
    0xd03050406050d0e06040506040b010f030203060712090203010507020708011109060f130e04081c0209011d0102122703061e0a0902180a0c170f0c040f0303050426030703 74
    0x3414040000c11041314000189000301c03d543c00c2c1c6055201e83c0c100001c001901c442c060250550120100900c3c0c91980400d98a500140c1040c2c2803051401b40c00444d0700390369015003c45034000340284614244032801944903442c50050180035400c1c02417407407507403242804541554001910051510700100c4100d1050782241001c126120340f50440010050700001d0301a00030350050704c3c120369584100c00031a40b0788a143c41c2d80807803a8014080389c2a20381e04101e0048500e000c0100008000b00340c040100e0420030140c0200254160101e041c0c020540c07549100040c9100e0242c0c0310074004c42000030180e844d102114400700740c8080c54a448003000d020b41e1150b400c03594002c00840c0031403003640000c420002241c2d1601e00305074070008002648146001b1040740b407074075007001f8507411941c0310216100078001780700c00500900880462190034054044074001d182820040021a442c0d2a000b41168031520410003036214120005e40c0c41207030106955001002c44c0015407400041d580d01355080e0742c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 510661510 1250 510660260 510660277
    0x31804181121071e0906060e090c09060a0c2a03030309061d0c010201140c1602060d0c08010305150c12070c020a0b091504050a061215030f110d0305040605 68
    0x460101c810802c810807000c4083c101e0040300d056021070704128007000c00c01c0c0d94002000c0a0074003108000380358210010880703580058600c0d00c240e546000b048801c6204407107429410090003c0c3e0032070380c0d680c40400701c0031052040040d440b0415455440d08100c04018040710301184c000f11003040081c0c0658040c1107880c1c403541000c60902d0795015031450ba00c020b501d0710349060300100d900c102c0c2580d0a02c1581584d16280d0700196584c284a64860882c0c0641844402d410300ea040e4a40300b0355139480c2c02d6071740503031080c0c1d0140812298040002c00303514082c8821a03083c8107c060b00c8983c0c04802c145580b0411101050343d003071181040c040104024090100317000d00504007405400b5844000e521405030100516059444000c0c0080c8820340766400c1c6500c072501400d1005226a0b641d8203101021104149400d51074103a40c1d4a4040003854003032503a500341204110000100440c1e01d00e03043c0c0050060242c1000310b043d40c001e00a1101c141c410040008904000a208060040c0013a0103540c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 510662760 1250 510661510 510661549
    0xb040b0603250314040308010302040507030e030f090a0803070c180204080303070f11070f14030319350f070509101b05121803030a08040602030c0702030318041811 72
    0x40d203003a13102d54503680c01030307070107038009010f1100510541c1001d01501e40c001c800391078100801c01005035101e441e8060707000c4032102640c0014400c2c200744d642506d44d6001d8100e060a69a66802624101b50b00071024440c1c0300711190f2040315a00070303030001d10076103045400361300c0030b5840e40c0e580400854825443d034440c402840454014100502410230031003000e0f0181c4107030040d0076401d10300d0000c00e1402c401403640c403070ba0040080303482d001c401c0020b20f62070742040d040084034501d115410084568024024460b03462540c0c414200c505040440c0c00d015452804401d03919440d0f070041145c180c4581a140d0f5003117041000d200102501c6a501d04600b12000610b0380501449036840c507060881416032a14803083c04601074148501c4510b40321680d040c204c009620f860030f00400506105002800a0411030380440014110074240c000c41e065168001c082d41e81d0740c05105841d00814522502d401d00840c9401034030003411042c041d0b500f4040d500b00c00300e1452a4442c10070408446000d4100f00240e = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 510664010 1250 510662760 510662771
    0x4030e0d15090201021b0109030821090c0f040504020603040f02010219051c0c020901030b130821070302090f090a0905060103032a17070f08030702010b040b06032503 73
    0x1040754040c11256801001e08089041c000700c0c000207150040c00462548600d0145903c03040c83c0e070700640702000b26239003c1c0d400c94444000342c88071804000c0410001c400d00b50444200101c2040114080e2422442240d01c030358203950780010300080b94001c4900035001a82000403030003003110303c0d20ba07044840c41407048654000b1060345040101d10805801c440541c04030100702d94040d00507048a07111071840c03511004030b2000d03800059110340c041c80042c0080c555031020407030040344603800c8600107411418095848001d000980c0c0c0b620052240c0152118058002c100b07000c2c1301e070086504c1d1107401802080441c0e1003100b00000b851000d024111019910000000014802d01520303008501035125111809084482440713001c48640c0590802c0c183c24080c90006101503a040380b03e0062000c07400d85a440c280f13014103070390803000401744c03891b9004010040000da0542041c0c0b1400e5082c0c13000d0007030300d61a5052103882d01069443d00980c01c0119071070202d42416286218000034117140200341c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 510665260 1250 510664010 510664013
    0xc0905010b27061605070e04051504030c02061b06060a080d0e010504051e120f070608180106030605060a050316140a030c180b01050c0a12021608061b040e04030e0d 72
    0xa459021000210f030401078913510505008082c4100b80003405421082489440d065590584461081c600d042c2e40c8826127011509251140520001456015150640d200111907030b04000d43c00b400c039982564803845000881b1410302e00e4540c1c089a010000400e49400514820746800132041c40042c10000309200010b102d070b03210070103014500e01c0064103401d2451140280300c0c1c0b0310f0240c40e0000c180e5004440c0c40e140034a0024401341100c2c0d451a0082b0701d07880711a038802c05451702d41c251460300e40c02c091000c0b00b072100d00da01950240303004885e03007940d0513a1001415201c900c43c001e00c9024089042040050510b42d580d0b0074841e180040000314526203c1d91028122510382e00300c6a61005000c2d400210354800b0301c81e001c0c00e40d00c2400c1190400c070340e4482c026942c0310000c900404908d4100103c3e000e840c0204001580b020006a100342c880d03854017000742c1d664108903240000201001d52113074003116040100e800741d0300708202c50009a039940e2000c1c0c861f5480300b46242c2e04002c80e120001c0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 510666510 1250 510665260 510665269
    0x7020d1707030b0306131407031a040305041707050103050112170a1b12030b090c071101020c1809100606050d090f020d0f03110c03030706090203010209120a0c0905010b27 75
    0x140314581c1b8040b100010159410f02c11030820903000045c0c0940d02c0001c0c20301c040346070180207010700740781e01c048000c1d13030703503840c64225114001d540c803158003c007919109448240011070801c0c1502c900b0b9034200801c3e0b903245800054100790000241c031641c00c4259500d400041c66004116511050925900c900c1c1d903854403444200d9120402d403041c024030b00042002030b6041c051015045000c844c814114181003614424600c2280d0b00100303140a1b030441401c29900901248070002d100626001d003203019541c44c401c2c0c80d9800c403400c05071401014030b110401d130180d00c1920b051f141c0b650303625421301c11803c404a005107884c40b0280c41120002d02500016681c0405a03000c86100c0c1e41031000501c1c0520b80680201049141c80a40b50070481a4000315200001a00c5145400c0500860410181d001013402842040c41d9160800d48440d644600d503500041c89410035403081d81c1c8420b42c42e9680e0780720802c95000380962000c4201c1040000e480302c040300781501e040008000040300d01d1a4040006 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 510667760 1250 510666510 510666523
    0xf03062a0c0f0c1e0306050705210a24050a08030a05040e0c040315021209010b090c2506020304050d0504030203071203020f0d030608150f04230d031407020d1707030b03 74
    0x940784030b000c02d0091040001b103014a50b00030096080903410603813850090022540140c00c2110481d1014001034070340e4078942c2100000e0000d10420401c500100d403808403070a803960007a0345c00b0386007518000800850004c1194880700e025910a800d15003010000c00340c0f5480546407038240d003030501012010502c4154241d0400c00c124200596400001c418029a40e000610650107649005000c105945450f2903441d4800e001d006415640c16141980000065010400c6102d540b480c004100402000358000c5018500940842e4002909030104460382e205070702000390507800c00c400400455411711b02c8210100d10a0041d600e03035003051071030180f414481c40c3c03c00d00060380300c400c02c0245030410310450804003060402401e241ca400c400d80024403501070700080c4109074981c0051200041c040307a2010945440080d1a003403101036070020060f01202c240e55a03031050000c00710300090300000d035040600d141602d0750000c981c010080d14402c000001c0078002071540350840c0c15115681801035 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 510669010 1250 510667760 510667799
    0x20304080d0f0807110607030c03092f0d05071a09060d05011502030408150702010204050a091406091608090120040306110306060d150f03062a0c0f0c 66
    0x5a80e50700c844820000c0c041c1e800542040b0501c080c515145c581c081010820303a0380710945040100c0c00c0700c0358440440c0148288840503111a00c40c0a482c200f02102c2495914100042500010700c11102000c1000350150090000d0455001d07120810040f600012030090fa1800052090b04004400bc00700c1c100e0750001c80143c44d00390381c40c0014030902860120007515610244000e50426080c0407070241c2d0707805800010035128803403100251034203101350100c82c050b180203000f00c880580e89075007a20141072003076840c181003096900040c3c01c42c00c145600b103118000580c0310514141010905889400c00548110015504d414421a890301c1c803a4070207401c801c4a42030b65030b44514500b007100440d00c00304140104c0307038010802d000240d40c1c3e040549600596021001400c05070b040800d58038010590700c600e0020400880003c14480c4c2640004070b1088100c00d8440380004d152003c0e40f0354a80341820b0408621005481808246400d400100c1c007882281c1106020b034232060b0140240441201 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 510670260 1250 510669010 510669017
    0x203070e0a0e0d021605041d0106030302030d0b061306051804110a110604030c02150733091e02030f01020f03180a020609040e0c0d0602090411120c0703020304080d 72
    0x107030b146516004000e44990b060301d6101500313020061940524040040d40b00b5907216688403480b2000d00e00c4843c4564008200050003084140d580e440c0280d12508602c1078107081074a044403c62450030708d0011500c03a24907450501101c2070030240d05880c13a07000f42080c40d10070ba2140020200039111481503480440d0b1340c10090343c0301c2000070f40042481c520340d1500481c58100340280b00010350007a803c3c40d04640d040701c04440701d10400920711400e000b0864040d100b100f0b06149072213504006000890303248185050202200403d00841d07054a21a49008219031020602042c50309403510a0210080c8020250380c030103104446000d0a90304029204820214000148500c1800c50310800411040c2e10f40a07086440c12500000c0160244210380f43c02aa202c01c840300041034288a01200607400174881c00e0003414030300340f400c025000b00041e10b004901c1c02d166600c0e01200c01c0140c54811010b07031881089030303070360450301007440d04880b90850540c03009100200b41081c0911806d5108241983d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 510671510 1250 510670260 510670271
    0x607030f1814040b19050f0d121d01051812100501030c06180b0a0302030c190206040510140417211005040903170612070603020c1b18040203070e0a 65
    0x420044600c5100920701c078500312200d03407101080549017681107603070072a000641c104544001c2030f400201d0740130090007040703280074129100390011001700070034903a40c0101c04043c40b51001074030307541720740300042d030700414119045501c5203840c2d0401c00302c0c08000e10a40d05840b01e0341042005641080e00211451a0222001c0c01115407048090389461004802444503602c0d20603070805a00c00c0380712290415030008006030030161005d088400c82c200c0d074403140001c00d41c81c000c02525054152421100d0307010300303001c00070310722100d001c0d54145150343d001481c8691503580e240102002e5081d0404007501003070020220032501d09050280f0701c0b429441c0e20782030380381020f5100e0104403503402c150322a914010321940429030080c2003d841204a40c3c4884860700c030600055650301445600300c20750321030308130f01080c4250715402804007090048102d03000102d5400040c0054560300c2940e907042441051140d5808440000c0c058200c0d002030300b6201155260300d16a40186c6040b1111142c01d5200c1 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 510672760 1250 510671510 510671549
    0xa05030a05090a080316140d0207120905101101090c0f170a03080a05040c03050d120e060601050a0c11030601060f0e03161217031602120304020607030f18 68
    0x60140380e40c008940d0b0003402069155a440764003d02020f0090038841244a443d05040c1c0d000c0d10202d0700041b5046d03001a10707840107181d80400303540f1480084a41c3c0f015950144d0506000d50f1003d010b4600007080d000c5442d11401085540c10483c4d01003c43e10344d250311001c0042643c0d02148000b90609042c1c000d6100d041004c00b00d0745048078044c04060384d01042e4a2000f1a50011010f5000751802d8400f2401c1d0300d95040250b01c00c1901e0b0800760150181c520b00182098220050303044d14400ca41d024003141c0f4411440f61345400c005c540b0603021030300421804000603c941c80415103a40b241082c00011b20704200800c2c500b4009800c100d01050001003c2400746401c16400c2c1110031045009255414100c5001000c442003031040c0324401c00800790328001c012502c0a064210111a01d52944074542a480d41111480407a00310b0094000c2501444811030f0f000e0449124540103420645010f10943d070031241491011000c100b040310320809140c038145a40103200c01406010780803142c55440 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 510674010 1250 510672760 510672781
    0x14130e06090f03030705030112140708031e041a03060a080105040309030c0b092220070209090a0b04021c020306130c0501052b020f0c0304090b041e0504170a0503 71
    0x2090b903182155401482000745055100d0105ea065032250755820030318080300d1a06800b014400180298207020300080030440c0500080941200c00010b010b0722481120b0110031340d024170682c010300d0320411404240e18400d21442000b1034001c0e402400d40d02c00c0b0795031240201e00b106d505a400f10f002519100c2c040061190030700107080035110742588075280c0001040000c00d800c400c203031082c0300d5080000100c200342c819035001040240c26402031890706121078440d4002d035400140b04030300c03d000f520040740c00381100107140c9140c0d40e030060100600d5211078080050010b0054440e4a102522203103690058400703110241c0103541300d00ea0b105852801c2c0c5056826030703070aa00304904010040c80b00b4542240e140c103040c1c080d11048008800d003044024132a5000e171242c80100c103251040043c0300c02640c00d001000344110b8602c0c21007040001ea5103020842503640e0840315155000200a1140a59510390b01587c4c01620541800171506510f60320034025070045080c06c40071800200412109020 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 510675260 1250 510674010 510674023
    0x90507030b061204020d021518100f1b0503190e180c0904150f0f090c0302120609060a0e0c0702010206010f080d08072a120e060414130e0609 62
    0x7000c95406061450b0480740420340d0a008001030f108609080701a820354840c0c55004968840e40907240341d442800e20501e003d42e4582c060014000e4051034249401c00e441007850300c030a802e4a5890502928560040840340d05000c41c0582d80b5004c1008058003940200025500841e5036403036202c3e420180b441000680c26451841808918000b000c000c2c00c03100b08400c40b007501d0001ca800103001c0d4903001120000201a401482046100321004038a070042e58030210101c2d103106070140140c0c0508003080302640900969000304800e00408a203492810282d000c2d88518042c3c40d1000d13041da02d42d00c0c028602401c0d100a004c1a20011f601025540d05100c0180501070f418031981b10030b494280c070555241140c40c401401c01040b4008510928480c3c0c04103035042d400c0c03828201c840030740b128210510b007084400803241964015400140d2500512000d580d006000349203034182894204c2c1003205091200da2154030181d000c01d0110486c021740300b10440e640240d0010110351601a440078540030 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 510676510 1250 510675260 510675281
    0x307080a0b100e100302070b09250e0105040c050904060906080d0e0310020c0f03190e03010513080915070b010504051f12141c1404080c040207020f060409050703 71
    0x1040402081c440b00d4020418852916050703a000d114003d522030700324028000d03044014101203148013845403642c00015138104015540c0c3e404081d08105060301c803c0d0051314400d51091001c40c10042015180c40d601c000544842c6003490303071804580000050440b40d45e60010000b05070b03507410a01845804000200c594060f40c00c0c002c001c81031100020390b503103c5403600384201c00e8002032000d003a00c106203d8003050511071021a9140d402982d000654942a010031700d0005203141604940f528050140b1405800702d241818280c6c8413640702c0c00d24503030109072055049000d0111000d20303202a07500900b10f640c00b8844064995040004010030f843d4050103981c0d41c0d0b00107490148121400790040c90885881c0d405003000c0c1d0781a807414582d409100111803c00e4003440134a02c0340721840d009200c40d80d806546d0340c4070100c201d649800000f805980034900a6a010203c0380040d809c01e98024500715000030440100e03452100700160590b07009400c03211585894006205940c0d415014405811 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 510677760 1250 510676510 510676519
    0x15090c060e0a05040b04140414100c050a1116030609020915280e040b1f08120f090406180c0e060901031808040f0303080108010207030e22020307080a0b 67
    0x81004000540741c1e000c6409803901c125921211014030346d540f640080308010014821243c14a05809e1040c80050003011a580d180111095550a40c90520520019810036180c8505000d8160360883d1072240c580701404543c407420001c0001e006402c0000802544158800b1615454520600289442c041c0c900d84078035003550422202540d412203440320055607141519000203020003d0060348282d9803200d4198036034602480140140d003002c1d1403140b2007080c0e802241d8204d8049000748240070344076008041d041011510207441400000300540300011441c5070901a0a00c001012503900303034049812a00802800885c1680c6406250244101d80c1420205001007001045280c4240b0441a04259403140100100c1210090f410380d840d400071511502c6c0d41e210200c4a84001ca00c3c00f064003c030301c10500004002505001700c0380b1055241d59914244218041840358a400203100b0400c030f20300300014040742040c5480030350310070b08840d9070341640c6080450a08040717881e00718510707004 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 510679010 1250 510677760 510677777
    0x1012060b1c05191517152e090e011505090a0c021c0512010603020c0c090c2a011404020607020108060a030605040b01061d0307060806040e010623010c0308060d020103020715090c06 79
    0x44203000b0206c07a8002d0445900308050525041c4100e90380038900000a910901144082a40d00440d0300143c4505844002000321000340c984e000410100d501c00c10364403414060000c2e04444154001c54258130481c01180c04169082d208100b0f86071130390b00070800181c030118001039648040748050b4010040740c02d0071071420b811521030540301c0100700d221030b005028001c040f440c40750095080368024422541600e01c01c009442c0a0081c00000d41e40300e138419803d0482c940d410a0a841c86e450050754010101880d003c8181c0c01512032080040419512400d9803c000000c00c8036406038902c41c03445030000507940d604044000c1c140072611031a0004030242030070500025100007031402d0a540c1103040c0503115544000001d8090031020202c4482942040000129140f80d101c0815411440070307005d0301d89060400c01100c5c4203001000180000321030302c1c041140760510704da02c0d0b1800d038010f140c054500511174849220300c145400400701441d50380c0a400082c0f0011084880151044c1d2408414 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 510680260 1250 510679010 510679033
    0x203010915180b01060f120516080105010f05071506030b0a020301030203071a0706050a180f02040b01080c0406033218030f04090e0a021012060b1c05191517 69
    0x8441e01400340a0503c80c6d90784000d038406001c5e12a240c1034282d4185c09202d5403410f80000b210804030020b400022941000010402d50b0081d031a0000050280d5261030030500592201c140035079081d0010b561044d1b8500006c0089000b40b010248101400d8001695072b52440c810700d8940342c41a0302405114501d0f0200e12300e0114848100c0300510b421603404580b54481310350300d200800c00350310382d80903800030350a2442c00c02c035141e40281c0d15280200c1d0b01b00304075103441c4015240944201c9a00303101c11801c0005000050007a8491226580c2506015007440301c16052560400362030b11140c0300144d8000100642401030403241c25140c0c00c0342000d5400e00004105000f02c41c02240921250300c2d848100404180c9010041d00d14190703001022800c111841072000341c0045103c80c045505103040032400700300028030700201c5481e0101c107400164807103001c50443c0000c1c032000e000c0051003901743c00d812000c84040c0c0503100517000e40c035075a80f80c010300c5d00c494644110000c584100791354100c030a207150b = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 510681510 1250 510680260 510680273
    0x5211608040201020c03070f1d061507030203070209191a0f010f0e06030718210204050c090909060108010e0703050616051b060a060602010207120e030307020301091518 74
    0x695101908240006031500c1c40140d00b45191408519014450100000f40c0071803c84d4035a01191480070400003551041d0080e0b1115441c00c81d80e0603005050200c4003100180c4a10003071440314080e1040c1e0b81095000d40c0014400c0350291081c2c21107000000b5a950703080c4091042c1c140080000f5000501c924120f80401da00f143c0107500a418407a13518260848107000e960028440300c4020101c80e581d2070400e4005d450801c400c4025000700c1e04540c03011603501915042c11800178201c4c41c80c140503412a50800c00980001841050070101c24041404c40da00d030344c20160300861400001d800c01d90b0408200f2801c41e01d0a50206241e0b070310411003080850800f181e01600f0401500c0650000300c1720302c009413981d102d100c0403d8401c0108281d00072a140c408502c650040200540903c03400307913643c004900740e009041010700800a49290000c800c0c0c05030707008018510016040c0d030304004450b000a401c5541b941c500b41d5450803608210440d118180c401c0c6501c144420361134103c502d03019110807 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 510682760 1250 510681510 510681541
    0x1202070f060b0109090207140705030303100311150a170a141803070c2d03030e120c030a03030209040b09040c12050a120e010f0201060501050904200a0521 68
    0x50807150352400c010725264031501e0088050084008150358503002480c002c000d04503203072032401d040e01480601092910f0044212401502c500d83c4081c109030843d12803031500c64a01c203c0d0380c0d00840c0100d0146003141c500d005040604110b84428600e11182d81d0841d82d0180c0040c2030300c1c0c0c001e141901c4102444451400c2940054210503141c005401c45208645103108080000e4004c030119640040d24801d14035500c210450b24600c1c004410540c000d440f032503003403c1c0c00b004003c905a201c0040d010700780444007940b0041417104032000e108402001c039003405030800d0254002600043c074802541482d0155a00c500300507203c46903d440c00341c03070b00a81604507010701e03901400c6219103807044c400f0400402c101030707820505600242280d600050310f8032445a96040c00306504007009104240103101d03034822107c2c180c5480e4035007e40201044002d01d45000901144080110b04c20703802084a00a44190442d944590f90384019071110620f4200d201d2070300800071025074040040122800889 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 510684010 1250 510682760 510682763
    0x318031c0504020f120706170c0703110a140d02190308190615110c030c0f0d0c080102040f05012a11060c060f100603270c0b03010b07031202070f 64
    0x11030340c98a20000c3c0b0180d042c00c080e1a400310030810005c050781804503810341250308580f121010078a5161154031580011507000c02d82c03130700920403000841d000b110703999000d410f284103481e107045050b5503032025000500c120741115401b92041802c0650100100e041e18082c0c04d080b240d88412968005054a03001003840b5604e000300c1290307595111058110078090038403110680e2105046400087c1200c884007540d40ca148154840320390380c0d0402140740101c256024101c008803804d0a070502c5540307140848201c46242c14840000ba008500f0f201400203071411400004d041403402c0700040142c0084500410001c21805580c140807003007030702e01c80555910850950480405500203800c40c090110504041d000d804c080180310445100c410348100745112000403425290341d0100c044406804501080b01300340c41800b0034507030070850040c0d1b00724130844000b0351032522074068000c2ea810aa00418000c0c00101d40c0108251300b08031a41c8840c0b01d106000c60800900e80c60b004529200c40c10b0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 510685260 1250 510684010 510684067
    0x9160807080a031b080c1f1803051602060336030a0e040b0d0501150902040311060c160803091503070e040f0e16080c030703150f0b1005031803 63
    0x204982c0b005281a460780c0c00741c1000105444840e5031820603180c447c42803009000f102d0041c4007111000c02803003820b400c04421484400548410b903000e45141e4021802160004c0040c2500c000603613a0000842c03242808200581d1100d07220508000540040111041d0414610700c0600c1d240c0000025140b101d41d2518104e200039581c140810000c2591301403494100108942c1107050040c15080700e50b4400012405005455a41a4041c101d0090b80001008202c02203051503580c038108020304034010a034008d46e959030349100b48042007200c0d01d47c0112041d8101044030740c0c01e80303084540710702e0405501117007911314a450003004150040010b0291710550b0381d10b000240388401503001c0003510880a00f210034146140707020721303100b08140c81103c105100315540c4c200e607802c000c1001d404481d40141e400c0030070b40d01060703004003500c64150140d0180399128000341b19035a641605489021540e220030fa074070304100d000c0904900420741401400ea0080003401c1c81030b2020300074988400b81c10907 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 510686510 1250 510685260 510685277
    0x60512120d1a09011e1737050d1b0b010b0313050f010f15030b0c0706020f0703031409010501030b2806031101020615010c060b0f040509160807080a03 66
    0x40c00c52516000965100e4001d01038100220b4880340720307041703401400308000e9002106030fa2111004070440b4114000340280d04005002c1e800c40386294107100b0007012103200b1441c10003903090710b04414100d54005581503403042e1700c0c584401d60000c10310041c08003600c980c041e07080c100d074481184094040c80707523280b10f4100000081c1c0e680940c0c600828069800700c2662021000040084e029012010b4407001030343c60720000701006141c030803000c02226417003444003000b980c4003500345425401c00746059442c40c0c0c00300072030f1402188800080c04501d20948000840e540700307003103406244900800000f40741c1e140400501c00701d40c0d0b0034039103a0708c401c030084181c12205000210014042810108070051400c1030000302c2000a202c05080d074004c400c0e801c4808030b80d1500540d10500365003131001e6001c10118080700c00413596a800409618038050240d291000048011034101c42d002c481000d0140c03c09008111412200300e0613200500b8020001c0101c030b410f010029850310a051001400d02106e007 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 510687760 1250 510686510 510686531
    0xe06060c01240f0621020a022e11070209010510020703061401080d0203250f020d031106010501090308030a0b010e0a0f0816080a171c060512120d 64
    0x250400c0407141c5101000c1c418100152152048004580c000c00000000705800400e130107100312003030611404058035440100c036020013500002d5218410b04000c40c000c01510710000f61816159407441c18014040070311003503038881040d08a81000c0e03903d00e804002000340741c0140c0d42e4070b0040740c191031040714a0091030345078410691410307010b68401402503041170780030151010a12000c1381250000410f941e52088292800c0b40ca82c81411050f941c41001c402c0c00010540c80d44c9540243c0707070b00ca907030500603d4403c0c7d00042d40c00382c1c02e19412000070b061074408039401901446580d00400c400c0c2445001c06040d980c1d42c48403800300a120350a0720341c0d00c5a900d0788580c0326a14041c03280030042c2c00090184d803200b0f01c03010311510501038440144103446001c400d02d000c48000004071280e45014207488a90f540e525003c90b8030201070540d10080500c1001d1101d000135555108910529000048991030b00b824061400c494000b0780d07504c0d8100741180104e000206048440d5504440000280324032071 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 510689010 1250 510687760 510687763
    0x307060b040b0406091a030f1b2e11060108030405090907030609031e14071b05041a0411041d09010906090f050c090103020102030f0a030204030503121603060e06060c 73
    0xb186036802810079000052448965200321004040880c0880001c0710b01c0091503a1601c01c00384060341380c1c1c4051064680c031800e88100c0d480101e401020044234801c80312610481c169221003800d03c00d07030030358188001260840390041e0703031840d010007030404ca40c5841203042e101d02582c81070500421203a000601c070700005000030b402039070f400001003140c100b10341401402002c40c40340ea003059003180c03440b1551950086401211014010300c1e094546421a41c60740f0790707450000c0d005200320030003800226480e510b500440e0302940c00381074000b0200b01f4207010001035803641c010003600301e00100401e101c4c05907480500210300c11981000a440e0f12440d41007801000e4100b03020b0081e03480c0ca841081040b4640043e5017100307000e8005c81d01040012030400041000c20711000340940c1c401c1010440a05844000c3c0c170014a06040040c00d03c0d58070f071692421540312406a100c40004201002843c16401c090381049000074681004200c1c145013100c0b80d144c80240c581c3e4420b44011440c0d1003414070 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 510690260 1250 510689010 510689021
    0x91203061d0c271201062105030d3803100b100e030708070e01030209070e010c14250e0c07150906020d23010504091e211e050c0307060b04 61
    0x5003d05211914413031005268000d114600800c14140300903545244908254903008525a420402651501450740c2800004008038008101901452101c9890b0420110a560345415405500340004404c0d241090304001c0c414007038904081c94040c0d00e02c19511650000d4440b050941080411407000d200020f20717102c16648030300302a200c3c2410100d030705507030607103e90b040324400e0ba003100325070300c07074410a481c44100e00c1030741400280100007400215100d00030320345143c0c00800c16182145c039081100c07a40f01603540d0303440541104264040020b130302c6c5100800c2d48071850240385400d1040d82c0d03440f1340318420601c461080301034a0b4135066050000c254101c48012603001d90401020200680c00340b990507a8106a038a03512500b0000507190500b8010b50000c0d603444108100802c0c11607003d0b803010301000405070b0390f062807501414000c80c0c01d901142c261392101d88404901d0910a207010000c8011a0303540410000706009450340341c00000191a04c3c65804107002c6081505400032400500 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 510691510 1250 510690260 510690337
    0x308030a110f0702031902010206131104060b13060215041214030a0903091401050f0f0705030307020f0c0f061801030b04240902120f0a091203061d0c 66
    0xc4000b40807035903868000010b0461520030740c1541e020000b184d0351411004011072002e070244e0070100c0003610205d003a4400d01309562044010540e449920070114089820a070002800500006903c160f844100e90b221002000e81e0f1009000d82103202080030780000000c0e10041c0307151500b01035500214040c81d90300e080c060b8040380c116103a160040d40d007406000700800a4012070000440400c1c040b0750408902000081a15014980190001c00303421300d034004070100c500c400d01404018000b400500095005803080da008000e1490f100d00350505002245610303d200e2207455545000503194803080c0c03036648220844051021080c50010f802a0540348a071a6005103000400e005d002c1e40c60100380150b121500348050000e480d000307080101d129014402c08103008400008456007841e02d8210351141c4c038a1808103441c0c0321540e03201d210004401d040e0010a807110400d01c100119140039500e815070390544009a82001004041280700354080e91445ea0100c1b43c14550204503c4036102c07000 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 510692760 1250 510691510 510691541
    0x3030e01080c2502010315060e06070203030d020d05160e0d060507020f060106031d06010315022d030a140402010804170408070b0c0f032106150d09030f05040806010308030a 76
    0x82404a0b5004a00d03d44042c0c124082480c1032440080342004040384001e5502c19119482da10b0142d1b0200300e5181c024141c100d9052000308410a00ba41041c0003420300820300300401f14950601d400d514001540d00c02c2000200300c800e00001d45540e0700c4403501c5413001c0d003040c0c00051640340c5440c22800c000f62440c0092442c85084000226207900d40e029010890044200c003c240e403180407000d80b610710a200c050a6100f4040201210000a6006202c00c030700c04003207400055000e007980c02c8a9540200300e11402e803c00b004101406583e40940c108542c0d2580c41002d640c0781c140c0c0040c210600150000d00041c4040714802000b401040031200602000003c4448861b56a1014035044e40691110041805009000201708400009446070000b0001d480c10034000340070b10004003400010000782c1d1100b541911b900c1040d0516008040405415101141c4a545420b0240003541d03c0701c03003c3c0400108000801c440c02d00440c01c18192544801226901d4030b41c441c049001d00a44000e94451 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 510694010 1250 510692760 510692797
    0x270525030b1501030b1012050c0909040c0f05060a05030f06040e0313030614040c1503150303020109030305010e010810091121060f0f07030507030603140706031503030e01080c 77
    0x18244411070b5050b4500036a005e1003010b40078400e1000c0d10414481c00400310300d0000c034030541074842d0340040c0c0d841344114402d641801c1c5600d000a00006e016141607500b10710580040c00f4009030080c246014140c2661102e20380407032890010441e101c002c0107e0510720071326001c200340345d0b11500407124513011030080f6034665180c821806110b250030310044540500c2c0504000d020351601240c50b00c0350781c10050340070620349051a880004481610b151007059500c806804122400090b0308003d0360182d4000108400b407407501404036003040c2c000c1d104040d100070040005800010704400300ea454450089101c510a10b802200b490711b220185a0015104021045c22118550900c1e4a69880703c200c8115854008616000300340648a0034101c560300300c0001e46482c040d400c0703d50002018500015103590f00e0b207400020000c64011008543c000c01802c010b0300d0340c0750258045101501907040304051440c3d6024004068a0150034140300a040004d01c1c103181d03a0081c2c9004000d009500541c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 510695260 1250 510694010 510694021
    0x105040308090a1527050d0b04240603060b030606130213030b011202180c031b0c01060305030a0e04180609080c01020c0105070807030c0e130603060f270525030b 71
    0x4c807543da62520a440c0030007900e516060b80c0580ba01c00e086030000340c02280401f8458555103ca190001c006a82c07017141100c0e50484030400080001900881e0712001440074210720b0588280c07801c40744c00740e20070350103001400080c0c6d0750384d100050170485020005030361303090304042409034606a90014100c5000e0301c0c0005417211030a00d20385640b620032500400d640030b2500329040c0a000559080120032014000141c000402d141ca5040b60101074002c07505008201c0042425910140c03c1107640b90004128424456081003061016000c125400d001d890540ca2800301c0c64540610301403d480e03112900d0500b44002c9004886850f00c2d40c6000750354a1207945d8000d800f85c8816030342c440020760b00800240c03041d0305c03d2060401c081c13180d40c2e420f041142a42d08101d80d602c0040d140d802525078402000001540390b1250450b00c901490340404c220060000c01015802440d102000f80061100350000160011698a052490035850300e480780c0c039007480c000c050b060190002400c2c2d440036400d001 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 510696510 1250 510695260 510695267
    0x160e120a0605060d031215050d2102070302010518040615021b0a08030306040f020c0a0302060115030608191a43080a090501060f0801110301050105040308090a15 71
    0x140d640c0034480510483d00d81c6828494500702d00140a030005480c1001d0b8aa000c0c045d81151610300c100340603c3e60002e448200081d8204000c000449a80942818a04400c1a60210300d02d030318040d40003900816245800103002842000200c0f28403990030b080b107126076962980460064a14103c85222001c204034001c0e688803004a4644128507a0924945061a00200c0c07113050710141070145044d91901020300002d001105803041903180c00b40a00320701044200f1045500c180242d0003040554501130000d00b00400c6107010404042c20b16078180000c28002503803101d1448502c80c5804100c40d107090080d034a440e0348115007aa6a0300c4410301256802440300300409800309100400300d0b0340c944282d00d11007074481181031041e040c00c689243c4010b010300302455102114103404509020f0940e5024216201074015032a01d402d512028410000700f44a1010134028465901d861035040a001a00034081d0b03101c0244040c000248004581e2104166a07008007020110540d0381051150041c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 510697760 1250 510696510 510696523
    0x714011b020706080a0504020f04150315020a09080c0109060c140318042f071703010905010303180f050f030f070611010c090e0f0c1209030a080f0f160e12 68
    0x8000401c21404107005402606c02d0601541d4020071280c1020442014000600b120150f00d000c4c004110000002090320b6a40b00b4484400000c0016614041048081c00d00300150304603080e036602050103d45241d03082004001656981e09224440301c1c03103031401d450607000c2d40c01025410f000200c1c8041c800740d204128000d00c8201142d0a000121044031b07504a19001d807448140841c0c2e440d82241d0500c0314610080c58060b000d41c20706800310071080c04026040d4000c3e8040c80b20503a960004100341a07026000500f401c04042c50108120300e020050001d04071079005e042d10400c0400d5803203034103a80420503059032039401816100032590b5400d000e00004040c00800c4e080307500f000120b08990b032082ca80340c42a124810017a40b00780d00d5a01038140101760061020420200811500380290785d960940d502c514850402540d6500c20580000e0020034041c01d884480340c0ea401c11700003248150803d89601c65a4100d150b080011803110840e9207400b40c2d04c03040e03002401108501c08551010465 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 510699010 1250 510697760 510697769
    0xc0d1407030e0303040201090320040e0f06011d060f0619030603120f0921020910180501030201050702010c05030d0603050a02041a15070809130920060714011b0207 72
    0x40210025400d2955143d04c4101c4000307000504940d0284005002114600210f4001655801c2c0003244000424101d070f00c0241f0035002079016074200c0b146000204041405400d1403001e1444042981c4088503a45038064440c51003440c029100c00070079110360090702c81d40c881c0c2c04020151010f950b64094000d00c5030b4002039800c000d03004c0360540c03401c1c002c40c0405002c1806035101c270081480c100300326110000340b96008690408540d98880545d441c6903409005025521079514031034a445000e2807400703005032406000c05d04080040026030b80040c2034442031038082c00c200c40050510b00e00f5605600c0383d1080140494586040030060000001c0d141c2c8845100b96003c1180c040f046201d01803968004100c0355100804c180b286c408251800068034465204841140c00c1c58454070000760801c8425024071400780da2104080d05003c0074aa03450f200342416041880013809090121b40c49116110014046090700c445c4d001814100b50b108030149402c2c060756884c1e0782c0000c54000d4440610784034 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 510700260 1250 510699010 510699017
    0x39061b2f041b030504050c03070602030d15031a040f0b0106031a030c03060601050721031a010c02010503060114120103051f06060207030b040303020910050c070b03010302090f0c0d1407 81
    0xa50100d400c20b84a50001e440c41100901500c2c000150120040c00300140221124041d40b0b00400d00303a24208020009010150041c40c0c072003813a110b14604a601d44441d450007d240b010007040070544244031100a0150031480741402d80c0c0d11f080000d036042c00007a004080c0070041000240040d41640711140490310442514004020003081541d24280c0c0c24405034541c10500106a0940c020709c01401c0071440303401700300d44404000b8034019441d64065400c0307002c207031520900d5030340a00d5098004c0c1e0001c0d09003451604101c45800003042400014155818408241a111020180e00d0181c0300000d5410040c500381e5030f128a04641c50ba003c0c2c42906880607401e82e52110320090034000c00b800e540160b4001c2405c10b1440d210b143c20b501000d401a02450343c200300840107510354800040304980036884a40e40c0d1301090390014605040e0b42d0200716280380034001407006070349014030940c224064180700c3d106070b01c5003525803800f44202c071304406a403071400d41200040c0140702c1c00a44142c91030f84 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 510701510 1250 510700260 510700343
    0x406080f1b0c2104150908030405010c150f05070801080102131e030206180114042102060c0d0f0207140303030402060a05042105010b0405130f0c0b0739061b 69
    0x105c0542c0c3e8603c003400ba00c0303204d8000340700512a9502c0780025600f200e0151490750306c02001c5000810403103004801c00c02e003003629403003004501500051054014906e070802140b40c010031160b105071342d800900401041103850300781d104407040d1101407600690340041410f50368110320095003100044450703102d40410012a0300c0d5400c252440e00b603a0440f01d0004000f251000d42106007000b20700c01d103038102c0c0d011130144901a01180c0421a910801080d500c07030f95223502c854130020703151803103079480b02040c504059052011900d02009980d08940d0642c6c40d04d03141c02e00d8000c16600c3e4061500854100b803020001c0c1039950701d5240010051b0b50103140200405200c1c0c0d01840b060f240c08944e030107140700300c2c01000b01c00543c3c01c3c800809114002c80400307105e09d80380c941482c2c45030310640003600c0304010301c0407411701a280610150280010803070300410014542506000d0a44103100e0f038400d00c1141d602c01410740d450702c0c00f00303012140d00400f24040740c00035852081541142811002c1c10500e4603 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 510702760 1250 510701510 510701549
    0xd0c12030e0f0d11010614060a0e1306270e070b090406271a0604032913050c030a170c1c0c11030601240203040e0c0406080f1b0c2104 59
    0xa000c0e00c040c100020302501c1c5404101d05040e03c583c0c182b00c22060b00f004255030308808051540c41103c010b01074001080c400c00e0252801601452540e0b801000520700d4103a14030301035440091080300702c8100030007094549507150700280c0209956400034907155004c404041c40c2c24008002100100c0b4184010840080398103480b0150340011024035401400401046c404900f41103d101030884846030f8841c0340d00c0d500a10001787c40800e42c1d090b43d04140708000c000c104030040c42520f1414406500428843c6982e071180c007440105000c0c0100c1e82c076000aa1045005001d01000c400028081411004000108002000203001800c00c1e0345044207000c0281c40d80c540829264101c4484d0f01c54044650424400c000002c2000700802d020351001300710000303005034001ca00c0792003250f901003078540315880c00da005810130070010f1440c1b04a014090400c450a810040b803c0505134980e90340c6902e40105084c5107140110908032501e001001580341c45000d400d120041c0103a5000d0441000c2c40a4007 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 510704010 1250 510702760 510702779
    0x127140708160f091211040903021011120105010e032503120f0903110604080a08070203060f0714090424090f0b0307030602030a09080301030809030d0c12030e0f0d110106 75
    0x12504401c0000c00c1c1c048208244550290302000d1240661b10201401960000141c1101c4844000302c015800c8039045c3c800034030891141214036000e0345070403441c2100307180c816501c801d014040c43c0c4c1406900420803405882c108581009502900002c294020b000c0004041c001001c1c80210b8896803410004c000f400e12036041801d02c82c0711600c3d02c007100c504558882e107a441e284130703090b60440c0c024040003c81080401208103042d006900095845143e030061604181000306400c440108281c01d01518507884030a9496544130000030725102c26812000402130410344a000c584603c500050040710080c450740d4000701e0304503600412180314201648000e80340040d40c0c6680c55040035034100041030740b0b900115880b2044850018400c5c1300d0365103084958100703810540b40d0300000301d0001010305027000305004510490512000d4452a075642d4100040b031031000c0000c068032001400e01e0000b0412040b03694001c80320a4510711000e04600a0031140690591804da6080072000a0048038 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 510705260 1250 510704010 510704027
    0x6190e1902100f0c230d0504151e140d020a0810051c150f110403050705010513031407030206160b1b07031b02061204051005012714070816 61
    0x4141c640c4113501c10b503078031000c11403d14000e003800170501200064034151000d100720090712001e5114552201d0a18010340d64111844104406020220400301c403410b91032210301514800303034900403081035503818100556014961144100a0011030601200e940000d0f40c54450b4240d28405041c80303688004000305240342c00030642070902031403c03501c0880c08010030000b161807042d90116045001131898000c44403100e00c0780d414100003080600400c0401d001210040100746406403c00d0101d6412208101d16440000c02030714254108100052090040d10000c540040100da201d05064240303c090003060103040711010070080c001985031b60fa4a400340321029226100c1030526000743ea0590b1803001e4483c0c107200700f85194110000698442e4014404122503040f005c0c010304103482c1c018603000d010804140140e0070700006004102c01c242500c02640d0150f204481d480e000901d508c4005c1082c0120300c812007142d00300b04004c00760060303225406108d000207100d9507181c140d601240c13100e0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 510706510 1250 510705260 510705287
    0x30f021207230405062a06010e0a06051507030309020a09020904060f0e0c03040c0e0403051801022413060203040f17070b06041d031b010c02010b010206190e190210 72
    0x2c0e02404180a14144a006001030740810900e182c5c0022071020303030002010504102d402ca5501c4140103102a081e1050160780059207a8000c2c02040d0624001a03810001c540c6900c4400c8400315071030062500ca5003140c0c03102500507003010255502c46050b02c0280d848640700c0c5000c0c3e030402c500040c0c00c105100d0b1900440704184070314907007030300c542c0707203405113944060020b82d1090000100850840c41c04008a8040c034480d440742d5603141d0481c884008550400035416041d50462200801240e020012494000b0340c034040004181c2e071161085590b22102071f1f405482544003104210400c281540c6500c1001c1c0200b07410f648504030405021118850070034000e0014860381d01090060a20b50010003112660b004040d200c080b01c030468a01d182c000540c610544030304070b00d003d010b5510a1160007120311851000f48408074004c00003039960500030740079494074003029101851032116030384100c400c0d00001068880714040003540070a00400b81006900c20072041c25000b414a0003652030300100b1 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 510707760 1250 510706510 510706577
    0x27040b03031305040504051e010c020114010510210c02161a07060207050304090e060a050f010f06050924120c25020d1509030809120415030f021207 65
    0xd0f401e00081c04050207000e803049440e445042d000486105600380c103800c25010361000044c0790b00783d40000a003500c00a0500b6850fa1701d1890041c0520340325001c004043c4a01828076084118503c4c25400d441104005282c00d12171404110107002540856448103c85200e012580800d4842c65400c0b89458402c0d40c000c0c3c3e8180c01c108501c0014529009070942d14001c01c00d8a09190750f400055040c0c0b2180c041000458212400308240c7c41c01c24840c0c2900701da44001080d005604003100b083c400d01040c02010188140400c010a1aa0300c8144c00e500c04249106510141004888100140d070070891500032210101000606032440042c1603401e08250724011030200b486120640c003030008400c4090303810200b0500310340081404c0c0c9144014808803502c3c002030040403810010a010000740c81140c468015800b5501c800e40d0b144140c030b06554800340410f00d015075824040c0e006002101c24056000d00100d004c41c44c61600400042c80b0b0b100f5510b413015042060b0342c6c1e01114a107400e03000300b0351 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 510709010 1250 510707760 510707797
    0x90302091b160606031b1d070e040b041508061b0304030203120603011d030310060503040503070b060d05010f0606111515010e2d09040f0b040827040b0303 68
    0x1ca2090304103102d50309000718400600075803641c89508518040101115603000d016000f00003103200e800c481f00900341c411120035403600700040010005040c01c88500e12440d2034002200c031903074403a446501503006c1c8801e00855150382e954001d44400081351030020700f440c3d118408006d5112002203e204d5a4154051840d2201072100d2524041c0c015001c10307015035030f65403182c086882c21030f075624511038200d006613264036261600c1c000303140c49504003004002080c020f0000184001050310702859220861144070ba6901010585005041070041c0035036082507941d2448080742c1d80048190f5100780d417400b40503000e046a2503950b4000618009000702c90000284401002c600c00f19954041407404007a5401c100c000035403a0909080900d0100c200c00c8a500003d5101d08072944000d041500c01c1c00827031510b41c07501c002c054211003014010180f030000180822814608807000b021100e02120346521410350803140300044211000d002d01d01e400fa4000403481c000083d52411814008081c01 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 510710260 1250 510709010 510709027
    0x80307031d06240a0303120f09020d110f0604030201080f09010e0307032c0913060b21120c1b0409080f0a0e0f010f08040f0c06090302091b 61
    0x80a58101c580c01c0c0000c4030800348440d070300a10410b402512250412215200300701c0e004141284503c103480d00c2005010020800a90025610380e0b840d181c0e0701000800d40c07828441240940005a0005c0d44400425441410001c2c2035405095004d4190780e82c610340403812040c00114450703800040c0c0899072080c0094807001000c100d09501c82d91090011413401ea0340a8490302d941c025400c124049208000503c10a600505902001c5240801c402c0585034010021400c1c910000e403c07501600200310000d000d1101a40001c0020a4054849000d444815070611040041d1400c0020f02e400b90302e04d0178100e204c400c010b44a070100000094007020318180d0148120b440b0a6444940054440101101080a2402802d80c20071310040f40c6541c0c10b800c0c04014000029629220b2103105d03543c0b40301c0d056982c084003d284034041c505089201380c17a541059100e4011403203000348800017007200442c440d035000030a401228800c2c0e07005907041d200c002405205110f0000708103100711040c82000e1 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 510711510 1250 510710260 510710267
    0x405060f04110603040311060c0403050115051f181706090f060a0b0f100305070909020703080a110d06030503090111030c0a020120070e0106120b0f061326010606020a080307 76
    0x1a00a4401d041080c4030740b0f20160901d081808c01c41c4d541c6250640800d040081c44400e01901400700085800c0401090600340000d040f2241000079103420311040c00c0c60400f00d800360800500d024141d61102c6220f681e1039142014030014500038000d2800340b04086030381c2810004068211004940c060180392b900c03031201000030000040400d5115206103d48074041e21440040d41100701680d40c04909031030002006000314402d98401840c0358030401c00d05001c00c1d07010b0031142e0400c41000022a8000c4525251005030089503c0c500000e0701c1c0030400420098000f000b011850070070f8a55690318201e02007001c1d20381c014128042d4050f0400025400190705c61740716950051141d07010240b080e02d07900399640ca03000d00c9030080e002d540700800c010b000040e000440c5070600c410742602400b22440b00c001080041941c007807881d004600100c0c040d840d18000324001005407200d00c881e0720310f45141c08802d22801801c0204071000d546400300c003080451000c6060a820b94110a2061035900c9021049 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 510712760 1250 510711510 510711517
    0x10f0f231005090405040b070806010f020a0312020903150406060f080a060c14210a091a06040209060c010213050603040b13020d020d150c02010203061507020d050d080405060f041106 80
    0x140e080120070400300811340d50700c0c410070703004a0080240f450186040e03a8080e250390b801801c42414410340c0e80400320550f40c0096200703829503243c034010051000000c184030180c010501d145c0c1c2d050240e000c804a0502c1c49032501803089000b9102400000d90342d1b44912070701030a500a80da06600507481210200e515034002c044034111070f24088130903030701180c000713580c1d60041002e903040358480314070305d903500d2071003104068000c03103401c00400400904e5540c0442280c4440c2042400c4564000024400d07500d40d4159409d16030082d06c003e075203100d40805503000b9402030b00d056449101101d0041483d00300701c42036a00c44c40d88080012595110614000d0600270b8082049030310444400388000142c99883c40c041c0400c2c8610707242034440501c443d5207829122440c8200086a205008000141d90748c0581c070f0410700301c1400c2d07041e03403a2114004503584050950340500b03e4442c0c10074a1120503403000b4814807070743c0220f00340c3c3d4007a107038200d4070050710009590250000700c1070042c00c4041d14101004 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 510714010 1250 510712760 510712789
    0x20a021b060d0908120c090d02040c12110a0207140105040e150a0308070204231605070b090c011e090302120c0307090b0301200d0c05040905010f0f23 66
    0x3904050b00c00c54060195034038088125101c40000c0750a0f0046055002d810b40c0002c40b540c5a182091352800116a80a03020750000e840303542c44103407480c0d21344d0040c01c6078225840c04013818040900999002c0640e58000fa600d4001403090039400141d000ca01114000c00040503501d10345048d01e002c1d116041054084c00c08192107103081200c03142c40c1c5d24900150021485501c0786034035201180100001c45a860700010b00d50b00c2e0b14aa041c40b48070591500580c0100501021003901d0491502100c85000d02c410040c1788004c22000d10045030740002c2e010209540981c0d46030b00744241c8010803400e202c2640900710100c0c1c040c2006100507d0440c0d500e18001104408484501d043d00340083d142c035000d540143c518583d50010100542000c1c060024200c03c982c080101300790610000300118490503510f04034036030ba43d0960a1625108408982c01441a0b220911003543c490610007001150f5100300100f902c0c0a0100146640d10100c480e46a480c410032803224600300041840411626000d9 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 510715260 1250 510714010 510714019
    0x4060e060f18011407030905101805060a020307150b190303050a0806220f05100303080408070201030e0d121a090411011119060608060906040f020109030c0e070e0103020a021b 77
    0x13060500120050040d003181d5000380d580010482c540028080e01401401e0130707804202c00708250540c0a560b011014040750002d8034080c1ea0b5050b800002ca09500131a40b00801a11441e0051404d800c915042070385071a4048442070303882c0c1001c00400003810303504c0c800100407400c01e0208603000c50040a01c039502a101411005c210294040710001e119022130306401580d650324800516404d541c8650b83c0d01c03e0035000110718017821528007900c00380004000810018001890204592003034000ca400c3c03030640022901c060542d00009403d00311850540c0a0007803900f10800442c140e0100044016040035110000f83e40310307621000081640e0520a0f81407111504940034041010030040b01c04c400d01c1d000310154680d26140400c195400e03648401c40942c4880d0502518020100700c03d41c0159001c0b0f284401c030080c610069810021030351024228240440c1c001800b2001d004206228000c25961030b4800381c00000190704034003c1d03107100c0d0016400b2403504070901d06548200795034001c0061 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 510716510 1250 510715260 510715277
    0xb16170c04050405250e0102071e15080a0b040527010905030d020403170903060c1303080d0912020f030415020f01090305040503070e0c030a0203190507020304060e060f1801 76
    0x40103c3c00765030042d03d6100c010700d445001120029800d5090071000d40403403411151074400700c40000d50740c1c1c815004150800882000c10144056400340880c014030002582184941080d1005031041d4030454051580a042100d0382c03800340340c00d2181c284a0340c0071000d0b14030101c401d00c0b03501000701c1c004810340400d0342d80c0d6040d240114001304050014a4818000580c1d44d0342140380c5910905e14a9040700b44880b002d00030f4543c83c1e6804142c1c01d80c010000f00311140c40b41d0005901542303100300ba5001034000c0c0400109030a004000c0d4108601850003040c4007440000c8a002c120398a0814105543c072075007081c0700502c02d0060000000d00ea111907403048409490f01c40c4081800c4a003005000c6000c120000340800c03035400e0500032840102010302d200055444d0840001c0c5440c80010000365005d54000005618210340707125040d003070803c1400400c0103180682019503241d01501600020543d5581c0c2205c551418004491112042c61040da040c0040c8483c5c0c1c40c281a909030090b4144212030 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 510717760 1250 510716510 510716519
    0xc080d0c02190c140a080c04050c0d0207050a030905060909180a06050f01150906050f160b040605010e010b180409050f0d0f0315150e010216030602070b16170c04 71
    0x104403000c10f0055403007615051404d42000580c0340c0c85007145000c0c0d40d00280401610b0004120900d0300602a01c000c40c1030b03580c44800c00c5407441a0000300500034804074583d024400001404154148240c0f01d5002203500e03241009407900640c1405544202c48a0011340503c0d00400d1042c03a03c4250021110664282d580b41010380d401260fa9050326001c100c0100303c0e040c840d80490210825030f080c03031070255003000c00040840c03098000710a40030ba800134001c1352004120b03003003040391a000501c10310742d03081916088002d05001c0c850f0918242c581c100200d003e041c8a022038004040c4810b003c56401e06142c00e11001c0c0c204868103803658000d01c115400d030101c003400180306030515a80c480d9605008980c1c003030304440680704407541c2010000401e001c0c440c09200144804080b509103065a10a4000102d180550680c559003014020400c0002000310b1034024042c11841211501c0c00c507641c8031118400b100c50081e4280006184441584080b540e002c00d00760030140003808240b9241d10f4 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 510719010 1250 510717760 510717793
    0x50106092409151706010e0102120903070e190b06090f04090c08070605070506070804030516110a0b042c0103140c030a0f0308090703080301170304050a03080a0f0c080d0c02 76
    0x7401e03001c00b1640741014080704201040c003090b170007602401c008951112040c0007d590395038543c1d1242c0d641000260101480d034007008820000d04450701b4048a9180000c9151158040a07030301d02d003003d0034110703282030382d1612805071403841a000d41780100302d80c10202040013426601c4d80a40e01013011704170103340c0010a0040001a2072184c945c10790326102c600c2c2240c9480b2000b4400c008108030f41c0c040c400041da02400321544c0380f407000510500035680d8240440c0e614840d038a4180c5c82072305100005440b0362410080c2003101d07078482940c400302c2d9500d1107882c44000203000030343c4000352840042c000690003109032044540b42c48111450203503080d020a260849500040d40c0410030130980400301030307002080503844034206003c0d05030149180e4401056000c1800f4a0100054141c00740c6c201550410a4400404000705420a1903607203041200c0c50f5030012064070300240303003007001c00582e500814190f1100d95001070300070710703050360080000020b0142500300411806070044c4024000b15 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 510720260 1250 510719010 510719039
    0x5160f0309020901090518190f0218041211030c0d0f05040b030106120e0c0112020a022407030605120c01050703171807062f120d050109050106092409 66
    0x4d1a5001480341021031602d46600487e1020b140d4960108150b10480718001c0340501200e40d1003c01c002c10f0034400d200240b4004100c0d802c44204e042518104014800e8001c0c0c0c0f0700c00070351141c5820140b1148000f07102c2d103a202c0e9500040270f0ba03026190001a59202d4440f045020505d443d00c0e40c24107807110035000c003a030b00070f0f441100080c80c681c14005402e803180c4214020300c140840202a44101000060010305092800004035a80410b0b00301c2c0b058028002510456a004900702c52400e40840000850340c040c3ca11800080c0b0b07100b03004c0b074941031030ba1400d24401e120360000e104061900d0011115070344020f608504000074a04242d002d0584500501c0c002ea10300c503800f07030341c0007500d110b0186080d176690320100c10131510f0410102030b04110040718194080900b0355001d218102c1011b9890544402172540c50110005101c1840c1c91040d40024140e8100803424046030341d8424013200d40441900030780881038035446132468508803002e030518031405070b810400461951490602034144 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 510721510 1250 510720260 510720269
    0x304081e0409060e0103050a02041109040c030f3c0621150b060d0b12030309070608011203050307080907030210030b030606060f0316032c1005160f0309020901 70
    0x140841d0a0041203080d0040780c010308002c00e100d00c95580346071201c507075568030044060300031540c54000d00e03001e040c7c2d10100c40b42044080c00038880c040e031008008004042030b0340c5180c1c15518000300348582d09007502c500e040c0030400c0d00e0310103502c55030761500c40c2240c520340c030310f01b03c495a642000184584d41500d000315a4100c640505c500b040980c100810032007002c1d0385c0c00103068505440b2841d9540d40300190740000310b84d600300207002600b100115484644110140315a072101104000c02200000740381c00c01d0341c0032940c0754005070740c8c1c076052800c849240040003404604240002200c003841808041d40c4507801004491040350b81e038010034032002c1e0004403880060303107440e03102c980d904040000f030740c100380256491403400c001e40078040f00b18003004e0902005c1808182c55030b42c0040c1300c0c0d00300c030354600c080c0500c442240c0345241d0480240607003603145218078080d0308078541030f040042c80741c0c6104440c200084106a0b02410003120114840c0030388905143c6e0b900708410168a8800b02c15010b070 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 510722760 1250 510721510 510721567
    0x80712021903050901170105060a030b01021015031a070804030c02041508100c0203070c0b030405070902040e0a0e010b01020c01321210060e0108180a0b06090604090f08030408 77
    0x10380da1213000400380484400e102c902c4c1d05501e4010803142d10303900c01320f03808001185000030740310f420800100e0810290f885e401003013500704168180d016a414062360200c0e4800d004400345e42e1604140c050020700c040b980704004c00c03d60300010b00800d01941e85101c12a20040000444104240d41081c6200340794001d55110703800a031014032466001e1150344140e20490004505040656892141c000614083d00048840c01300100301044001c00c1000c002d00030021055446980703aa2050300940402c8520503101c6083c20501c8030b441d0411b2080401031201a40504140c50400c1d00540307070300c011802d410f040e4070301c8802d080b07210407020f1803111402c0650914069480a07245414130059001030421f840c0d1000501003040500e4010419606000c002c2c00e002103039942d964112410f8001c00c0310300d020725001c0e140241701040b4111005d184034010407181036029440c1e400500c0b0440b041c040005004014400030340c004600e000c3c001d5544144a00200c500e0b04008402c90500040048100c1189 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 510724010 1250 510722760 510722767
    0x2060a023003010308070309050d060b030715120b300d0504080304090c020102070609080c0105010e0108031209011104030b07172214011b080c040308071202190305 72
    0x1601c40881d16084100780800080600c11000051800c501c81840000e01000001488200b0035004000140041200605400d65005542894005000564902d6100b0300821901040025950301082c802e40880e41d2951111100382d0036000c010b01710391000fa640810020800da200003840b1082009490091504490840111842a20703240c084111281444024082030024040001c1500c084a0711281d02007000124200d0036402481801c0004d000241072a94260a0001c441c00826076030400f00001c00141c0e03030f203072282150508280a52125900b0030404c400d00c0e1020143c030a50040348020000894900c140d21603110b6a02540c0304441c10b21401042221968106003089008034982116002614024096082e004240e505240c40c4a07070400981051091f6003406052040d00d41c002040350302c111070400791904074441c03c6100004d00420005001c0100c290507601141da111440e2030030f000c015682d910207806642a0030045204503018109590302c07410070042407502984406a4 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 510725260 1250 510724010 510724033
    0xa030b04060b03040201050f030417120702060604200c0705040f06050108160c200d110a2111061e0301170606030c19180f1d0709150302060a02 63
    0x1a5282540560342c0078506004100150b45c001c02120030031001103a11990380c1e66039107001c04825040481c01145080c0109050703004c0d840780701d0914058205502254441d80e120b0b0100020b581c03113030002d00c00c2c03200c002281390305500c0e82c1030207481c1c185090000e5070b05148e100e402142c11600c0c481d40c6110850380303560b002c00055811003112034000c81a01c0d13885000d070421900103080b4202000004140072f01800c007900c1411703017903a441070001c2c100030250303100c001c42030401c1040e00400f482000e10a00e948400001d00941c183d441441d0500c1500301102c540302c0a89684094480601040c1d801200070030508642602c4022690410305031030101944075410002542000c1134158130b0784120f9880441800140da400040340c4d01811800c03100400b6140f008448581e80c952503038000445402140c01060100707515420020b03684011900801c41c180200e800c09100c000030211851040c0c106100900038101c50f80c010012882070041c0c2490415540e41c041030242e800301050200503088844c80c043c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 510726510 1250 510725260 510725269
    0x20706110312090d1722030c0204090308220506011404020f1b0717031b0f07060c1a0c040b070c03080a050a09150f0518030106080f010501080601181a04020a030b 71
    0x201e0b4a0385c841c48400b185040e820303044520882008414900c100449000c0c1010300c1025690300803903001e0024840741d00a443c000d41042000c3d100d03206042c81c000c07940b501554007500e81d4141e1903000401811a0707464600741042100c070f01c0141c603401540800803201001803160080000300328000d20047e5034022098101d04091003908102e1203525110190040c4c51400420781e0031030034411030b000502e424502205481d161910314108541d00601100040c82900682e0b40a0b2403401480c00038080000344400103000c110498030017442d500c0a000500c260b9504801138440c4602c24020100001d0302c0340c0b01c01250340c01003801c0100003400000c485c00c209034004c1145004045540e41d118010701c96641c00303441c07400030303042c000200a0007040b48031008001075034400e40c022016001b0000103440b00501c0e0707140d40d03419000e60015800e1000014400c580003c0240c101c40a1b04141c0303145c0c510043e035100c0034124100b0b0303600100b08080528142c91b913482c8002e1251007240d03140051f00b04402018403 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 510727760 1250 510726510 510726527
    0x30f0614010b09040506040617030a03060b0c0a030804050a0807120e100801120c051e18040203060705160b280e0d03240803030609010e07020706110312090d 69
    0x4294400c49080104201c51002e0140c42d0448022600403a8969030040814010314181d48440c0c0503003005980034050071004401854140c2d002c0d80d0920400b900c0f402d0000c0c8602c0380031011001d42c2d008185030740102e480b80c0000c81d0468070600940f40c01c0d10742c5803103002140d00100c505480c43e030803500e080401c1c40d8018242030b65184007691700070b4a03244000000360107000144140906031560070758410030055003c1c101001f5001c0204034014a03100a02034107071040e00d0503200ea020311320b5458444581c024112440d44290b038010024544c66850380000c80709500548210b0130031089186070240043d0064003407921640d985105d0340c5d0300184414184e01c1c210001a4024a10740c0382000300182c0c0c0601207003580b146442c0341808103001050028031000e0254081d11241c4142c03c4410101d41124040021802800101c0d090700c441c0c4d032264054401ca0034180c604a000d640400800c0100d42c1c040e00448403c144d0000a890034410944d0003002034003412180c0106030340020306001c11068008010 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 510729010 1250 510727760 510727781
    0x70302150c040608151f111e07050a1202010f030f09050f0601060309030801141c0309030204050a1803030f0b040c0905100504050102070b09041b050304052803030e0106050604030f06 80
    0x1d554815203840702241c0409404551309006106d0040c0e0301c9544e0740144880380902502070111103400c1c80d2076a0025080c00450310510301402071328000100c5203000403401003590b050b05043c5072400180e500550f46c00344654501010705071100021728605041d48107400c4114000c10240400070401b002d06420300c00140c10040c2807503d401544404a80d01c078112034155207400b41e44c90980811740300042d0b02680c10300d4000b042c1c441d1041142003010340c040400c0307007100c3c4295000e0126865503030b0384d40705644400d021411114241401c8001107440707600300d818003a5102d000018200c18080101e4261078500340c0c0100030590754102040b060800e03603240f046001c000d00c3d00c14101414880000d44a031103034465070741ca401c004510601e03a0360340c0d40d00030072072401c22880c003d014044013003010700250000c0f038042c0d9460040c0003e00505000744080411000f225250140020889640913801411100b0f81e04c4807070342d81e4132001318280e110240100042c600460500c030400019141c030a05403002c140c40c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 510730260 1250 510729010 510729031
    0xf020d051b0310062129040209010e040902010c060f092f060d0608030310050f012313120f0c150e150909040c060f020303010b0708070302150c040608 66
    0x8000003542a914a0029644c0c01c1c54600c0c004000303544101844040096407000040c606418103000e0810085a1540a620b0f00142d588200790801040103e00400702e105004c1100f009a554051030035038040304c0032510505004c0e02c1491186c4401049030f0340c4051000c02c0540d18600001441550307050a10240b822002e4002e0703040c8070703401e0404244070700c0440030f00500003c60480c0311401103403c038401420202d402c82e6240d103030005400407100d1041c411740740282054050400154810f1200c10001e5000c42e0380b2031002c074400c0880e61030b02c0e4046509803000b56803c20020910000b95072201b8061401029210000700483c140003c0c2007406e84e001004040b048801d4103d07081c0c001100500800c411070399031009010007008103959118224119501c0310156040000f005104607088080d5a020303500c0d4400300d8041c1c40c0503641c0c3d1101380502c00322000103000307000c00100301c1d00003800d5061207031040c1e171000030100303100b0380c54031405a0308071908a0300030a0a0107840c1d0b00c02c0e10319038003524484 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 510731510 1250 510730260 510730267
    0x1e06101403030403030e120a1a0a090c15020f102c06010605030703090b0711100c020307081b0a06020301051f21150803030423030d09060f020d051b 65
    0x340001d60300d00c03540c84001e09100003900c07400b00f40c1d92103108549113095200182c60500985d0300d445810001d0701e41c220035401d2180004164440300610038181081c3c1d004410190b144d06100ea400740c0e071080351488a04511a500d0100c848a03800c0c0700e00c0c40c224402d81004a0048914a2100600007440c0c1012a005121400d4248140c2c1c0004100c3e0448629042482d665200e0002c118064028464060100813255062003280f940c000d400c2c89505805605564107013800d20300200c20390f11640e0004005900500c0340c1000310321044003e0040b84240808150351241416415091118003041654002d0b404001080141401600c459448051068820002400350005481041000207050741c01c1c1161201c46104401c03944450034201c19060700460046d03461452540e41d41c0102d4040380c20b0345e0005c45146100b00140303104114440d850020358102240e8030301880082145040c01d64116807202d07020054900584000c25010308010000701720b0340b501032900a0052829450071541c0d40081 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 510732760 1250 510731510 510731549
    0x801140f07140a030c0509120607110304060f08060d1a0103050f0a200d061e15081203041b0306060303110a08040909060615030507020d02030903060103141e0610 71
    0x601c101ca4503041d0f141000107401804800445290260700c03101504400070381a10440f011f00002d486100d00d1003a40d030b00d04451a242d000c2501d0380210300c1104049204d41280300f441502840c4416400040500a401590104d450711400b090200106195809020300180184a0140f0051184124210042503049416500c1c2c5205451070010085a07492101c001e40700d0b581c91712401c502d081d4001c8024031014109880c81d10214030803803a0340c00039925018011048000c0d0082c07140072512448040c00c1842d5002504910035403004000f251a400164941038051074810040c85c0918000c142c0018541e04516029044d91410400d444441e4840440d200c0090307a12802c860070794035100e00104e40c034034203860002d0160825402580c4818072001d0041507803541a80300921a03001c0d0f608454524140b460140c2c1c49100d0801c145030150850001803021a105581e500081d85840089544941c90a1a82600c4414100c0008074980040b0280070144d851400300134040c000780284080c103003140 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 510734010 1250 510732760 510732797
    0x1803090f14040b01020c03060a33050d02010903060e0d08150d110f22060b0c0a02011b0203061303030f02130909030e090406050106031a09150a0801140f07 68
    0x40d001d01d03511a83e11024294040d0344248100000742802900b01c480034249280d000000d41a406d083c403d0314000c6090903100403007801510130450a0b81e81700c3c000280d0401c0c05212040501400a90501880240c0040092001d00c10300034524076403c0588900213481360b004124001c09485081215075041100700c10341d65450441100030b510025014500e2600b0010460b00214030440b50340c441d12240e101c0000d5a0003250301049921003400400c089504d03100d104000c3e014007254281c1a074440c209801c0154010003012011840d00b0100f42a080b038941e000030b00c1e100c400c0351110000c074940c040724810540c15000301d1b8117410954005500344496056140d8540b4014868511100e40340c0300100c0905018062005810601900118031403529080c010f0141c0b40c00c0c4a541c000074500381d00c900134a4080e0100c00c85071385004048809503110942c25900f00d840202c1c4007540b00f10381c0640020310710310901c40e0f103004201e9002007034050300d080f409403200c80c0070083c81001813069900003080c80c0d210 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 510735260 1250 510734010 510734039
    0xc070b010803040603110721030e1b0a08010501060903110402070605070e10031806054606060c080c010e010203090a02010e060c060c03070c0204060303050408010f0605061b0f011803090f 82
    0x110305000302304500700b80900324040c0c0fa6004681c03001c0d0007040c046510178420303028000c3c609031080d07030070740e02496643c00d41c5802c0b18024410480000d4214a00307200103500030b90a03071483c2e24018030160038180691942d070100c1c0c9046d6002c001142c8140d0102c14a4100340400f591075085504041242e030340e0070011f0b844007a01d156002010184c0e54000a040702c40058410a00701d158205d200d11307250a0740c2d103080300300601036002c44200c08801402d018a03074954000c2d001584c03055661041c5042c0c0cac540d03404000b504200c884000317030754942012109003407092002d03600c100300c0d050080c0700300600c1d8000034206000c410406170160303d01f00301d0200c40078400500340760400100046039583e546c661104584d4450304110081d800783c1004800401c2c1984600608181c411000c001c104030104030340312030116041d510815402200a10154140d2400d18054004241d0f01106445004062040d602e00b141e410b01d031521001c0d503101920b034040c5a4056402005042d2210807500d0450800500000004 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 510736510 1250 510735260 510735293
    0x150301050616120509030f01050108070603020a1b031d090f06120f0a0b011a1305090c070204060e04110909060f060f04090302010606030c0e01170c070b0108030406031107 75
    0x201d002407016420b21110303512054290b0840d20004000a040b41c00920f20351203000154030a214a41d000007108074188103450403a0404c00041540351300c0d00c0d030160040c3d04140c451006010740103c810050b08144056080b01500c0703074ad0340d00c481d00264141c0210310240c5185003030003084800c0c100f002c00b00d42d4a00e06500b00908950300c00c002c44440f56003600d05800f8812000044c02003141020401c180c00724014141c0e110071002405000c2c03e0b00d0058894001d403201c03103015181074a4200507078101704039215041003c6a100525000ca103402203000c2c0d4441d40d04c0450740300590420081445048809110a2082203ca8541904003c1c1c40349a40740005081d094806040001113039043d51840c0e000300003140094030a011800c280d09019000f002d09120302c0010a080100004200b071141900e030900400c1610303110700080f9410b808075060302d802410740305d00b480108120000706000c808002e00910003140150b589a08062009042d0740341400200304128092003284c0002e100b024280f002c09 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 510737760 1250 510736510 510736519
    0xe150103021c0504120c02090a0e0a05030406020a02030709050603191e0c09110702060304060b012307030806010f0c030809010902030307050d030b0f0f100215010603091a0c0f0a030b06040f1415030105 88
    0x10300ac0044c107141010030280004000f440001400141c880c0c010403258ad05034000c40a8031981599540018162802144d0503a1b040c1c00422500c0c0d0900c004003c107140399402451200c1d00d0000501400510380000703501660480176107a420880140380f805404460310702d81c0e00c441d00708042030340070503d180400340000740480c0c0c40340c541c04640c0e44103907800e424880103074120034504806c080d8411895030203200181c00003020304001400a5014040c034400d0f4030515602c0141e41070342514111007184003e00001c0c0c00355241c40c0d06601613a0304001500c0341500440c054204944d894002030103c44401ca40e46004030070b8801c0302542541c131648500854a01544e48009514040108038100f139107048030064a40140000820741690513840041c10500c55140041161450444800141e10807078000308003400800c544600001c1000c00b400c46500b82e8100400c0d00740035000043e405401642000070112070401d01000410f004400d0700340c000303038152000e040800c1800044d1500b4803050145031f014 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 510739010 1250 510737760 510737771
    0xc030d0c050a02100809010c0215070f0912031115130201030b1314090d0806030d140423040c0309020906091b0c0606190e150103021c0504120c02090a 66
    0x600c04140008581154011301100108420842c0500000740550758904150301c4c007c11903070a00c2c000101c030981440d038404103800c075644071f2034221500c401c0064050300708441c541c0001480054a00d210712054401d481d80441800c17480d00c0107152498560480408a0020382802580c003040307040ca082641c1c0a02e00440c00e41c0424010400c2c110f20181c010340d03e21710709000111061a0045541e0280502d001541c030101180082243c004800b0303a4420f906402003d4000d0b00240203100480030018054031190030309075511080701408449242c80356942d00c1c3c104403600203162a02c90801c0013592806c1c00c000001d4160003280400c000104814011804000840d01c0c42d00d0b2105212100307540b410382a0341c1e4980102406403903200c1500c4280c005c840c404001c2082054000520068440b811030851a99441010340401e1000c018040303410f00da420007501425040300840e403005521020404240740c1040c0c0b501e20031410842d8001020003540e0b102640c01a6030b2801d0709070f001010f0382c001040 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 510740260 1250 510739010 510739013
    0xb030d050a081b07030e030606010203130504020a02010b09040813060507150e030d020d0b04060b030108120313150e070902130618171609020f04230a14040e0c030d0c 73
    0x44040d5032074102c0702102004504d80c400c041d4082440982080b00f40c0644d01035031134082c01660341e4050040200a240120b403400e226600b45a40070784905122403001044200864001c1a001034054509441c071601c0001c414030b094201c0100c01d0001c040314a0040c0ca8003010380c442011500345861600802c1d41c881030f204099950400c180c0c1c2c41e00110350070865403080305c244a42d000341444d04526003e58140a00007418007100420380741241c180740c020300616464400c4221403540700620030781502c0b001a07102d001082051089160306100d0200000b04c00c0b03c40da04003450301d4613551080681d28010400360800c440c0c0b4090030411191181800502000d02d00b00305010a100c6030002c03c0c132000044042c0c12606170008000d0104414100400d51298580d02c490050344500c0800505450040104200d0580910004140c3d400c641c0c890720000c095100000e0003074030301580107060303030503c41045080d07918045c81402041034911000b44201c100e503c0210f43c0f50251280f4280c01c0c014000c00c101c0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 510741510 1250 510740260 510740281
    0x620132115090c06051e030103020616050a0f0c0e150f04090317100612060b09060d02070b180f07080c0f15190e061303020f0d050a050c040b030d050a08 67
    0xb03040340d00142c00400e143e101e0030002c2058014014400c0e14061001d68001c03510845030859042e00d8000d0400ca1800007800e90540c2e1141501c501103401c2d100b04075030320020a041c0c0014194882c868500d6828140c54030199849140c07000d041402c0d40903004d002c0449a68401a0740b40d2640c900b07480104800f000303810140c071078048400741030081000100c01c1103008000d00d4040e01c10354000b17440d98004d01c04840c04030301c11510a80240e4061100402c0400c40c40d18145c4098881600c640f0005807074410199035090313030a43e09030703615035200c5000707010003454103820b01500508041002c01081024504030a1a550341c41c0011503e00459454000d90000d448003400a1200520441003583d5810320780958241987d094020700000380d00141042003d10700003003103955500c4400f41401c0d1840c103640800101100d803000c1e40358442151080940000c4040c01010440d42c040d10213440302d8250f440c00d11059621840c00c05200f50441d1300440d91564000301500d0f070700b01e41c0d4139002d081d81c0e80b41740011 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 510742760 1250 510741510 510741521
    0x10090b0a0810090b0f0103030203030c09061903090501060501030b0315130b04052b120c050c0f0307020a0506091e030106051e0a0e1003020105070620132115 69
    0x103219030007910340c42d16103a1003d400194a80740b2500704e286a0303696601c030301c0110640c01c0c08018010b030420008a01c42d22144000380c40031007c004c0540d4030b005049100803e10400100c50a00800c0e141d1806409000c820b1150200524003802e0a01c002b09a00f400652610001c0000c01c2c0d400c421746011801140b810241c40e0700199011264182508240c2491556501900c2c02172120402c034075600880c1481405c5040c00e0402c640d12175600018090310400054011b06480c0c82c2000018040301c501c06404111515403c86050091603a075000c42c01402207410311070300402c1c01488208180707400360303c8059650110004241d60380c0d018030703020700009024180365441960f00c10b40d04000400742c40708003140b40c0c00a0304100c5003400210b90300c0308909102c0e10b089070b9205101c081341e1070400c059405074004084d40ba100d50700006040c44442c1d04c103d06000d801d10b50f942d4950002c01c001800b05c106941c0703400900804c907a0941220031130003c9920b03100381500020412006451512034450b000d0304103 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 510744010 1250 510742760 510742769
    0x40501150c17030108210910030c02122a1b0603070e04090606060201150305071419060801050307171902030a0c06121514040c1416060605040510090b0a 67
    0x80d43d50b6540d440310b0840c0c1c1c0341070186403610030300d10f140c403045002001441298145c21000c2e08603121412483e07010740c002e0001d03028500c254010780f0018442012400c0090071500e03601c0f010081355501c2d26141d05850342443c05d40301c016601003142c1c6541604074015403101100110b80301ca68a98807200c0484904a880c0c50180e045800c0c620310404200301e0b40c20040c00c0d0761040c0d000700085e20071168100c4202070288405041e0390405001032080d4071600b108560002d002030046444440c80000124903008154032560010b0100c600600c0703545410b000c010002c100b4020f1403010bc0181484e041e4036624160755200412600314540000c5443c203020000006400034000786802d56940c0001d40301e0280c0300444400149809902024460801e15280c199011380d880d010021030b104007408014091003812a0911003100070543c10401420002c01a00000c0002035a00700c51600c0d090060712020b41203940701da400d0078100140d812192114408441a214000c5200c4403618003103103003800f50382c12 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 510745260 1250 510744010 510744053
    0xd0615090608190b060d0512071703040b0a1a09040c0f05030f0303070503040c03080c0604021c030c020d0f0219060f092301180608040b0a0615081506070302060a0b040501150c 77
    0x204554030b1080d007011346101402b078020004406100b0b51100c0c0584000c503401845080b818000c1543c01c5082da000100c89002c50804001c20000d100010324050011181181c256000c4130091100700c2d204402c800003003500350000c01d20070165410964490000806a4080080100001c1d050190301108403009680040003ea6940c0401c0b4101e511500304640980c010041c400b4000d07000b1410100c0410416056522900240c4d00c0e5130802c5011100d1000c01d4824006c140c0900e4050381e10080c109401224100d501051103250a00103402400084145014015144000c0086810003615a6007000f41a03149803055002c210060318010180001c0180251140c0e0303001c40c072160410300c0d242c0903d000e41010f9003199987d05048003500c80a0250250812000340700c00e1488e8003400302c1170340004000d1000d2462400c0280844c6813900716801c2500161f208a05100d01c02d507107840342914182c426201030180c0e40c1090018500c1d058440700020401144810840c14450085003c9403035120403074 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 510746510 1250 510745260 510745273
    0x13031407030201050f01061e050304141903170708040b062b05010f06031106030c04180b010e0d080306130f050424060f0909020d0615090608190b060d05 67
    0x1002070003003401720f540b000c61960131000481c02c10300549031b004074800922007001140b64001c2040300e2580000d0302c211690445008c1c000d22036101070040400408002a1805541c406803c0040410b00c45184020343d06910348188400b0721741c4030304c0c8244d026070081e00200c030684410b00850014124222138003a0140c1d1000446c92020419120001003070007000203011500542038400101c8206220050245050ac5010041400c1c6207004e942e00c95103101d50a0308003a5508442c80514125a102c420080e554000c1c4510a40e00201418080c51041d03501d0089506166110300041c0b00c00f4240034801c0c1101c0440e8104054540c001c3c0780c440c004d241041c40541007500c0c10441c4070000310002222000740000e45180c0918030301c140403c45a403400b00035030b485d15051042000f0b208505090360001007498108000c1034441c042d9121040341441c510b1402441d1080c0f5804072403103134000710394540011040001c061402080c0c0e9072100e81000010110b41c0301c903000900540d1403802d00401d0382c01070780c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 510747760 1250 510746510 510746513
    0x20616050607020d0801241b030207090f0b030a060b042301050103050f09071401050f12061c170903010e060a05100608070c0f081b0a1103011413031407 67
    0x880c119002c0c071019001c4400c942d589040555080384240200d61101c0380d0304d40308441c0c048004040f001c0c040b540d4180640000700700e1143e9840c0049440058001d41e001300420000070304a84160034510810301c030100b1a05c2c3d501c01c00261642030f040000b402e4240c4411113142c03150f03502e034001e21002c610b40300b0744101c404440003440b40300701c030911819002c2440e010026040107a9014414416450b99000d4007800781840304e41048211034070121810041c1c24800da0b03210344a424024200c0494142c045c00c00392408804020080c0c460300c080c44440542c0c030340d4100004020080f420801e14681c00038645a0190501090050200b0036580c2e1040c4142d40501465500590101d40501c0030420403094003500c994058421800548003e40060400c2d101c9102090b499500b41714801e1280b1036852901c04c400c00e8008007a2402e1807405d09540010210751f04000d0344252020f10b10800303600a2112541d41100c00c99500300c01401c202c42034624804a02c10180708803920380202018500b2a901c03034149 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 510749010 1250 510747760 510747763
    0xa06080f060109050a0510060809011509091407140607150203040807050705041109060703030b041508150411060a0201062c15220e030a020307120516030c02061605 72
    0x70b01c03400c200c103071130403010414904440c0a914030454149440013203152904104494a040c01810031003255030318002080c81d00b01c040000e5000f8020200c0124101d42c1504107504c2c00285414805c600758400342007006082d0b100c46043c1c1964008490b03c07620380805080c58550320040c9000d86c458035200204200c10860031102a1000c940160102c03800240c550003440101c0d804915440080c0d40c050003440d00514010006042040c401c0c03801190001c04440824240e480003074140c2c1c1680190981032100c03580403c502c40140d2001e08081003a81070a4440f40074140401040c140500f600040e2007500703500035040785000b0b00c0203101c80007410b000450780110003c910505008628413580c04074031020b00502c4000d86501c00200040c8040d01c14594040c2046041c824a116044c0c075050a869500701c1800640180f1650f90080c0d59a0341007464904584041400d0302c0c401e004050210010a142e04052180d5450303141c100b1300501ca455000144d664000d40c45000c000f08134013001007003007190 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 510750260 1250 510749010 510749023
    0x3020105100803120f04030c051c0311040b030604090305041d160507150b180a050114010c03090506163e0102030706090311060702010b090604060305030702090a06080f 74
    0x850500800c660b6250071034681c40c0d120b0034419000d854541c50228100246078419250000d101b070420040040d4140e131064205400c1411625400c1d810241c0040b81d250075001c2c04100100841006290500f0b0107400c0381240005002c40c1e00441c0e4503000402018010821600030b841d0150302c2c4080c80103500658480c08004581a003c5510100030385002e9502030000e070381d002c943c0301081c1e6011600170090ba0000b4045002c102c0ea0041104515038100c20104091500a6060010101d207941c1010822210a410040c01604101c008200700700400d81c0300b01881c0c1511000c6039050741d2031545040001400c200310001603d100c403094198501400005d40e500082e00581041c203203818001000c4e0b1072080c4150585d54096041080b070000050f025503c0607050030310904248503990224040546000c20885000015030364400101c0004e14100a0142e40828112418042107066a541544032b0162081c002c1c0181d011102190740e2200c035800c000c1c040c001d85001c90b066070303c4c0c5096607a035840 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 510751510 1250 510750260 510750271
    0x140c0a14030301060f1e030902060f0a02060411030a080403171c0b0306010509060a03140102040e24030c0a030b090f010c0c030e090408070201141201090506010f210908090d03020105 80
    0x512201000810a02880882100c21006d50401c8420700000209801804000da0120b80c4840204071540550704000040c001c0155544d00404582c54246413001d004480d50781c409100e90f1103192001c000510700d400b04c0b410b69500c811511140340d0b00b4960800c0074010301c14468039024000c3c41c40071070250b8561050090020841c102c8980d80d80c0d0f1000d205c4c0d43e9030241c0702d4a400010002c030601c0410601c003001074041c440040010b280680d03c1d910700784015003c1c0c9a44500c8003d00140e140b54001401c10726601c10001c40152a008414400041e5031015912006000c090040002070f2050410300080c5040901000240038038249888010140a0210b00440c04a2444200b0b0010342c105005820305c038036800070782903141020301d40065400c4c4842170b106001c400c0b020012881d5089082103880d0080480a60100c2c3c1818000c00240c050600c00c90040300b0416145400031500f0345950501c0c0550807217520000b0f10038114108039030144110300c49076400c40c41810398401010390540c42a8840c4 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 510752760 1250 510751510 510751517
    0xa38160915050708040f0605040f060801061e02010b13020309071e0302190b0d0504120f0e10050d021b0d0203041a090f03062410140c0a1403030106 65
    0x4050410050340d8240d6540034012412441e00d4a05010030701075070003010468004ea4626041a40e074011030801c95046800c0500000c4001c1010010a2034400035000601400e060a241da0347c1054002030404003030213483e141030080009841c040c43d000b0340c880d400380c100181c04100d00d404c0014594000c1d601c2560481c0042c42001d400140080724240d4880382c1c4211800c3d0000d901e40755400b00035422614070010030b40d040c52003c001484100502c010803050484100c00704061806040920142481419001c1404200804901071700c2c0d020003000d00c2904221084018030790b4910003103416001d0a40c0d1085164400201214020142c0071504a1107a10300b04441d0300d0101518120385a008900c2000500c160280701a2110010b03c409040c142d600034009140069032000028078103030082c0c0e450680140301118454003042e010b0383c246001301c401d4602040c40000760600030210610640a03112840c00850300d4a00008180200100d15820008809080540c2a8400d8513a0f00a00c181d5010 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 510754010 1250 510752760 510752791
    0xd05031506030f1005010e010e130b221104120605090715020303012402060c0319090312050f0603071205120c0615010315170a14070518090a38 63
    0x241c6d1b10605502c1703401d90042e92000300d032207005014003071041d0220410a03d000e440d203da580503915280400605135204940c09500112950000400c8070341d90040074065040c1040305006014180c0090b418441d07000e000001c2ca80d981c1c500391130520780140c120f1450222001070303a4048923800400381d41178070003951188003908034403607000c46400c820055410158106a000400c002407010245900c05030b540080064800e1001c2c0b1503048030034040c1c08902049061000c140c8062503032040f60782c402e488444c242c1c0c07207082000000c0e940d60300340d1141d8146181848181410130405006c4603010300c59800c040d6455060b420042c5844000440d00c8040003149102800341540c8a1301032000c02031a820b0b2460039103800e111000d88aa000c030520314105200e65401440025100092f504868580d00041c1040b11f040c20208111089900c4903c0d01c01e103c03090600c075100f200031886504542d48081403000000c000c2003021400c1c83c2403090144060b8910840e44c0b6800500c000e054451008140300412 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 510755260 1250 510754010 510754019
    0x105100e0a06060c080c01060f0b0a080708040201120c05040e270a0b220f140c03070b031303091203081501031401051003060e10170a03020d05031506030f10 69
    0x44030400c0c820840058000c0b01c0ca44c02182244d0010902c001c01c803800450182d4440c008580c074036109501014940d04000b45c080b074030030340c0001d001350032181c54a020543c904143d000286100380307480c00103502c1c0d0756400019803110f0284d42103800419850513882d249203000712807402c1010a6980040c1010806138074081005008103481913140c1d0301120555003034030384c084686501e0320300000c0016401286c03000180852103a990391901d42c1d1196502d0b122a440c1c01412904026003d4807a5020b1340c400001400078500b81010f881d440480c103241d03018481e001d824212018003096008003c001c9510480505060b40501c0740c52240c403030310080301a4560340360300440c100d4402400c0064031001581c0140100d2a0003280004450201e02e0045186a191224241d120b03c0a031203801e14107070180d404201c4404410001201103c244019111280240e20081d450340c02e18110034082150020000b0682c81542c50742d02c000301e101030502a107910740030700e1075003090400703a40440e02103413800300014 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 510756510 1250 510755260 510755281
    0x8070b0906012420010b0a05010e01051b0109020d030228020303090d0312020a030e0c010521061516060e01201b0105041b090216081b0105100e 63
    0x28102c5611186510000c0b400c14007400302c402c0b500401c0010441c0740100d400920f00050425140e04a1071000080d1b942c0c284001c008800c01c00d43d00071303814031488110340c038003980e003041c103030786036590108501d210016460342280d00501c0c0d5440005d6014001800c86410725600040303801008140e503a01204402c1d109106d00fa48050f141d90095040d8800c01c90300921342049184400f115100b414540040c042c1406a8000d980241900b040003d68814403012200c10401104000f540c3c00c2c00c01519110700c441d0f01e04000c80c89501100307006a11a00401d1081d103414240b00c1b1140140e003604d50b21403240090740a5103c1d04005c0641c0c0040c1007098608150070180b1803550360060009500d042c0044600400010342c05c500072400202e07010100c0043d802d5801c0c042e40c1d108503c502c1003100701400b079030440c02d200c0314117801081d42c0c18070600c17820038900c1c40c500510308100e030800ca6140e10b0780415440300050a0074444140c011b0350800707045c030005007074403200c02081d240030f400c01d2072044c1d4800c200d0301c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 510757760 1250 510756510 510756523
    0x4051e0c0c120f070602070c0f120c170703030819020a11011a01120b130f0203070f02010c020703020108091e03090102010c031811030307120c03030f0e0c01050a021908070b09 77
    0x6941c3c40042090500142c80b40e40102200d6104842009859517100c0ca20400d10702d840c3d01c0020507801c0284d1400c100049c0c01c0590016240380302c011485c460703640c1c060301c1c0d0343d29160100409000200b0701041151703401410080c001c1d6070b00d4500355900d910700d00c1c0c014131030071950350740b03480560802c0c00c2c20b10400300c16040c003c003140301a500c480018190989038000740005d0080320340c12201c01030b921800a0803a0041c078078005d09060b000f69880c20b00c00001014460a6898070046902d48400d10241ca980450050200d80d02442c000090781c035450507050070030f1400485c0542d01e504000101c3c02800010000c2c20038107400740c008000074103020301c040c1c040d074440300c200c1c920348064030071000c0004100300c040301080600a801c4a041c1421661400d04450a1140100100743e4800c40003080641c540554542861418414440000303084101c0d599460001441e506101c0c0c00f01d40c10b000386200704818910507640318400c40103c002801e255000790702103942a1100203d90380010b41200000501c1e = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 510759010 1250 510757760 510757777
    0x706091d07030f020c070306090b0619060c03113a0503060d0c0803030c250503030f0403030209030d0e041506021207051609050f16020c04051e0c0c12 66
    0x1810180c1d8903040d0481c010304a4502c2807540c15801d020b208900c410402a00025610a031400603121485042500c101c82008006d0b500c203014041100709030400e04d004e0718080700e0303140c2007841c1c08035480d20b01a510703c0340d0f1000c000034030b00c1144450204001210000900008210442070281e841c0c0030003009805007001d003480100d8010408112142444089188810f0041000203075039900c90a8180c06c50340160b0b08503241d98800f2800781820f44500c80d041040741d6403101c200d1a6100b89a03151516800b001303041d900040907840c0000c0030316000e07804458800c030000701580c400d040103000151480e846241c040e8016890b000400c101690215142815940c041d001803460310400c981c40b6120f03a204060444582c040c1c5200030804a000743c03103040281054940109a91030b21900c01b60082c2401004241c0e21500641301040e8103401051080c0307045010f542c04075241ea83d0b404652152840c400c482a600b180d19400c0144072803181001d4427944248000b40d800302e8688100c4c420042c003c03000b8 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 510760260 1250 510759010 510759059
    0xd111f0f06060f270b0c060f070e090708070e0a060309111c02100302070c090b0118150e0d0b0901020901090e040b01051003141014060319020a0c05030705070609 71
    0x10b04d080c640c041c00c0345559220381a00100d40d0302d0325101c01000c0d0f5040121702420030b91180c030038000c42c6808092020343c09860340c600010000200c0e4006070960038054001d01c18003e000010030409480b84411f078446072400380105400d69a1504000c002701040e203001c0e07a0784034649075140b8480c0b402032181050340403000724181f04000990200000ca132448880b040a15908212400009030101482401454102c0001840071050000900701c1802d00e801c0f45074076000544c0c20b1290121548005a03400c1240c13500804009441740400c51820852030040c21885d2500100541460150001d00a280080c3c0e9960714403561070310108250101658010001c42003100103102d5401c1140450840038154580826104a00141802074800c10b686003501c0f40f030340351000d1144090038038105071442d90540e034140c914900400a03003000603407407034813660450f00042d00b8120584500c8055001c1c607000700c20b072a5100b190b403034242e0703855015129400219030348080c0040c5000c0d0004200e03407240242d00 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 510761510 1250 510760260 510760277
    0x9020a031b0e03100b06040b030c070f03030902130e150c0f04080106051f090302040f023108120403020f1203040b0c06071e0f1b05010204030b0603030c0d111f0f06060f 74
    0x343d0501c40d00000c03d000c2b1030740000d00164010800580300032030300d01c1c041e480000308080c05d0f005101203150b08602464415081401e03c84205130000380203d5440781030b07042520f403038031404503000760341c4514881166941808107010450707000c19804281142c604491440e00c0100202d40d04410005010508010485004080000d410300d40c20940076207402d81740041c41c0210185034440750000030000c412401e519021608680c424000750400642499030041c807190101102000740f0b88550b0000900a120742104101141c03120762a0304800c0d50080141e0340c44907110304c03031810550040c0401da0040e110318004078450350b000b8480000204e501f40d07110b1100c80b140034003d96075101858050010080e0262311404101568501c608100b1701c20400942d0f10352541c1000d80118001420681c0309400400c000020500700003240c848a00302410068084d10140703404500b0456904012382c0001200433040c3c200c4500e582c01040e00c1281c0c01d4041096581750308003200c032503d5407807001c8041200c42 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 510762760 1250 510761510 510761519
    0x30305040e04030e0916121a0d080f0f0711182e09020c07081c2006040c150c02090c070f06091208010602031309020a031b0e03100b0604 60
    0x40d5158080d003e4100401c0c00d6a9880c007152410b042190109014204030102040c02540041020003000c1d03480340900c40a134440404090b92005a0101031007078070104881010007400e1003c3d2403107030148140e41d90311500c0010603e03e199010920445061034003000c100041c1ca41103000341c0c0278001c400c907540820783c0c80c8000460140041992402c031880ca10a90034402895000b0202c00b42527040000b6890784103100b182864040d064100460940080f081480d80070211020311403820034501c0c0c01254241094803201585c2401000403009000d040104401d100e00c01d141101211b060280010803003e417510212868140724400a602100020104640600c2d44000c1c090443c0a500f603d06050055038811007120f0030f40c1c074210340c2d007458400515490364224103082e0050100303002540c5003040e103000004500d007090140b050f4540e404195000154840c1d4402c224258420440413240546100081c148c0c00780c100d07a0922901c50600120b0000b0f07540e001d841074030003010349030f2810700e070a0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 510764010 1250 510762760 510762779
    0x3050d05090d0b0109240302093105070f06020c0109060315090f05060315010e0a0203040c120b09070b160210021f0e0c0402030601020c040b0127050a050a03030504 72
    0x180740d070298040c07410702100d000310304510611402860705c03400010317441c8185074014007484d83c40025060751101a144c20409611640010340c2e129010070000e1054080c4e814034100c48100300401718101407801014071081110005900c801d0750000c00c4d900c0045a07541204a960b52008000140094842c8500b0801c1d1402a000b6401105041d41700a400030303201c0c0000811544021454201e03182c940c0c3c18400384d8201403103410a100320000107403403036605141001ca0b0a4070701804400c00c3c654000700050500c4200d849000180100c0e8036203132904460350800d40c9803800250303031040c483d02452000061424076076007103441c440411100403109080c240c0030000c5080c480a646415801031040c01c003102040103890f51080b443c0300d44001282e4203100701c001c2c985502000c10a024520420a10005a030001240002e08600300d80118460b46600012100d1400380480203108000300e01c02d15203411000d104030303016100c1c107a50385200c05a449e001c0101c000003520010707000c21410001481038500 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 510765260 1250 510764010 510764017
    0x1b080901021b072306040605030a060b0307081501080910110d110403030305010e040b150d0204050702010f050c03040c06050c01110d05041506081b1206010909031103030103050d05 79
    0x45000107003044081d4400c88500141c5030b000800c5a00403020070701030941100c0d0b840d00c0c440400c00000f14440f160780d01141540c4660b0040e03505105000c000900a1304c0c094000101401c0c1e03408030683c072420f1504020309201803c0d0303010451445041c80d40c18055104180355442403554400900c0d02c440b54292a200031f185003540803041e400200715030020541680100c000030b560ba4150305075114030f9400c0c010101d807010b802403007440f408241400003003580d1780c9021740c0014845480341c1000840c500000d0329183c5e5000000e42041c02c04003046641501984040012200701034240966a10070b4101102840120340c000c2950b10050340a022070b13442000070301207880404000040711100040d00c10803581020040c81450307502c980c02c020804ca60006104160a002042032240c1801d101c1195156505050ba03c642c01840e03500c00c11455a40f0740702d141c084802281030b152107585400d02c44020304800307601900450080444214542c0c00007045a04a0390400c000e498216000c0108458990 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 510766510 1250 510765260 510765271
    0x80a050403120b18011712090a0501120e01140a27060504020a0f08030a110a02030c100207031509062729100f12051009080c0624041b08 60
    0xc4015950201181450b9802e8043d0008071080c01d0046d60000c40b60345055800141005501420b0107491015144c1a404d102030361824200f03100300758000b46640008001c0e04403d02415820029402800c01400c0b880718000c58100c1e400b4804468106003071000850600c0000c00b4480000c0c0707045000c01c81d15844281c01520003040d4a201c290f0701d01000e4403400094200c08495040098001e800e5a0819600d09242a11002400c0407080746e80000303441c2c1e103101d003820340541004104121000c0c4288000000345500c003d03203200c4e442d45000307904001d11a4250844009103402c00c21003020800744122142e0141c41c40d08a0340070140c507500c009100c004c010440c11044c48410700b42182400d4081040d215071361054054181e00c1c9001c000703028082d010382c0700400340210155581d000c29000300740580188404c00c808680c0200d82c2c900381d145441604040c1c030300d074001c00c41402004488444599a03184040300007044180c145000c00003101c0034400c0084900103009000d03a410743c000d5080c254004c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 510767760 1250 510766510 510766519
    0x50d171c061e350c210d1206090903111908071202030723060f1902090d1704090c08160806040b040c03141003050721051c080a050403120b 61
    0x602803082040b42105a07103c10310442d0420340040312141800c04c140c1c00c0c5040310b101d0150714a400442e41e551150880f04919003000269041051a04890b800c80c100034009080d042101101d2414010801494510000030901492180c142003584070b411032400c040c3c000a0182c80d1040c56074607a042410400d0066040d80818041c00020420001c2c80d83c1c1b0086500049850183d0100c0c006803d0510090100484001c001b091214140c00c1d401d00c681c5590b001c0300f0060f911011140007610392041c40d04010924054080101103079a210b8015000f1180c04600601581c81141c40a8500203011100c00703111040c10070000c10182e1084601903081040504001035440b1950082001c1d03c580707500384000700b138031140c1c02240c0020181400c0d600100d07142740412483e06590300e4035100d0a0b5886000922101c2210103d500314032032259007000c0340e0000813501c203a490003041260070b00c00d007501c11010528140001c0c4c94400c1d28000c00d0303c07990341607455650421229085800400c103550015821 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 510769010 1250 510767760 510767819
    0x3330f0711120a0e030c0909122101061701060212070201270b03070e120304140105040f03031805010507110112450309050d171c061e 59
    0x400160301c004101d00380041d1380351a000d8000000b45807401e030412594a009031401c60400c07001d4000031880c07011100e0145103447d5251088001e10300b403090500ca81104403d00100002003641c2c109071280b821405000388540580e0703a80f00140e8940d4a140441c00c91401c003000004015071040380c09108038450a0124205082c41000700310140d071542c1c0011190481c004181310165801c80d5401c503a00604507405800440062041e54a0780568890a60b1909220000c66481c1e80104181c4014040581007000d4050b640d0400070596949541602d90f501c1071881e0116240d4801e10444041c3c9811a8040c640d0303546a900440708011900040000c0702d983d40d8001d290f0b0038105003c0c08425030b20010403125043c2100d8032400c014070183c0c80819001c00d0111400c0041c1d0090f050004450086866500b4441c40d414440700150406910203905000042c8a06540e214845030510506007510200314241c0c542888141901e842d08503000d11154040e030420079908401c01d0014040c6c03942c0c0d042100d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 510770260 1250 510769010 510769033
    0xf1012120c151b091e0504090809030619062435060306071b0f080d0e0105070809030a051608040306110a12020f0a030f090203330f0711 60
    0x40b10b105110140f80082d03221800d034101e03580540e00001a106614048815a994140050f9000103520486001302d4458001c142441403540c1503492014001c0c3c152651450310304c0c2c1250546842c1400042450318140001c00d010043d0054034414a1800c00d08031050642c01a00740d81e648041c0c041070f482100c0700c00069820128010b407244140c00b01c1d68450100d4100042003600b00b460081a0f2010410410001d030301d501c040c42c030681d02c8540c00c1000001140c0003402c0c440b082d40305541415040f24107000c1c441800f05815804203106c1d14103a03032084915115010510384901c02c031014000060000d102002e1000f00d815580a91079224101c4c0c94901543c0e0743e00c10040e1000c0c481c4851080a021950fa050740da000000943c20704000c650861801741101c070014428001c00911030b080642d903d100402206165005041168005040300c401c1d8680c4440506441182e01000002d040801e6282d0844a50714291601039544110401c0140d07403094030440304c614401200c01203a1040c14130240c1c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 510771510 1250 510770260 510770303
    0x1d060d050d09030309090216020d050a0b0f041406071d0307091104061209030206190e010f021801030902100e2103041a0a140d0608060f1012120c 64
    0xc005000c0780d29008030a40ca1030901514031600f0394403032901180104100503820000d600840703242a4100c460030010030180c00c0803440e050303003041c00070081c15000042c01039004880d10001d11681c402c090145000b4081100c42d81c8410043d81d19802180355a03060100811703071100090200c400140440304c941c0d5a60210b001510300c2c00300c0c05454200e0008092050f5680b0506d91001d52410450510825801d40c0c1c0082d03a4170720040550034008542c10f006200f0b4080f0f600032640d40e0050200038000021080300e403000039800b818506000c0e00241c144122039501074003850305090340050041891f80c260000030785046050a0307003243d020608030131203101c0c90582454000618071403401192142c0c04d003964424183c0c460240c1003642c000910070103071207507408901c12005c8000810404d80343d40c0031006880242c8529009081c007030050304100080b000f040162588203010700b500c07001000e580c401c0c482050030440200944441c0118101c04500b03402800d0a80b5a40c0c070881240c4860740d56600c601 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 510772760 1250 510771510 510771523
    0x9010b04110a020c09090a0312061e05190e0103080c031204051b09042103020408070603050f130512131205060a06150c030e040b0405041b09061d060d05 67
    0x48070780c0580803907a00701c01941040b80700040340c0c040e80c0981035410280e02181e41e40c102d00c0c00080800100d649140302c01e411940200e00100b07003103480e00102c48481c00d858409801c07a4051a4043d8041098400d000d4030307800110381c122606112400c20320303425603ca000c4554032210340c0f82c00c80e02c4100001451030141107440e0313203d41d0007503000d0301d044180c03c01b00103600035688082e140715280b82002c3c4004102860400c900b07a40c90120841a101c80c105000e50180c007941e40b10380b0050051520001d141790700f64200d40d2003481041c00c1503050f90f4408039824a10b80f01220050300c607500840000c180a222130000b0241105480c41300b640c1d45036102e181801c40540090110780c50380201003405690349141c001c150241c034503003c8040c0100700d001c100420104c0003003405010000c07005102003840e246c944c0002050080600184000e01d0700e0b060501c2d5814180798100c40701c4240c900c0001e00d146152140c032042c1e820444003401c40100c44942c004414101501480e407190740c440b10040061000c0044 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 510774010 1250 510772760 510772781
    0x30c020d0218090708010903080f130506190506041107020d080d09060209030c03060127020409020a0207060f09030305070209090c130f0c020f0604030c0516120605151809010b04 78
    0x341c180c40c00482641c2800025401703407846a052004010001c2d80240049034049003000a501e01a610340da000480120038590103040ea0040c1e40501c504800c005019030002825140284100c1e110030301400103d41603d007180c0600103040c011070700185849191205401e0280200606064800030040105c803100c00c81103900300c1d80010000c007030341800c0c841c0c400240e008030081e00c099858031040600c03284030902d5039803040d0103004442584401c3c50703054802403c03861204545507140d200c006551030b0514091362021402026100b10f2561060310020103499041d59010b0a0100c25402e204000030058150300480c000c00072a2200c0b17480c4d200190b1100100500041540441c2140316000c4805e5403140f07a00b190010b116401400c45c0c0016200c0e001907152802c22044000341c14038504101ca80c040130440c803010881d0004040035038920141c000c40c000ca0003009151136906814900030820352003203400005405a01400400240100e94400907800004c102005007000182c100e400500d034 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 510775260 1250 510774010 510774049
    0x40b0601050d0212100509100308030c160b01140a030c0e19090308010e0901090c12051c0f031a010f0e0303040803040320010c0206071214210c0405010903030c020d02 73
    0x100101039100300001001088166100c2c401c40c02c00a0145236240c500380000780a07d500000815000200a02103805034100c4002d554200c010b1454002507603d428854021a0444041c480000d80303000c4240008490384461041489890722240c0c1c0070341c034802802401d180600b209803206515580c010071000c1c920076581c030300c0ba03903052502d20400c4000280500380c1c00d0f0302d48200800010450441c210130355240b1300e0402038001d0a80703041d41c03400c4056011907144103040c8040100c01394200c540d84600c415140c81c18449044800e20021380510714040e903074000741d00040940d0072140640b09180305581e01909885c40c2c1070700d40c0c402620310750242e44100c03480900d41c1800004498480c5032412201c9007442c128442ca0620f400081460007004c801170490160700c128040c5890060480c03c0b2a0020000c000303071910900700400c805440300e82955407452262000060384c4020b891300b10b80c240d900c161902c6101c03d0558408440c0441b54040482e0019110700004015036100c256100c1040740e80316 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 510776510 1250 510775260 510775297
    0x60201050a0c02011a1905121b0303090a0b0901020a240e0309090f0c1303200108091c0905090c071a0106050403061e050c03060a1409040b0601050d02 66
    0x30000d500320b414440c50761085914085180101181480040d0f2032880c04880c4105010600c5000c565400400d6000682c80000198a40d0385182c02003100e440700d414204024002086a8092544a104d42646940e214022603820321054007900003425034030310103204642040c0e0350b95907001c03424560b1440b16214682ca20102c801480400e00807080369052200c05142070000d01c0b030100e8000c9102174056480c01119070001440480414203492810403035140040c2026540e040c04075824048000c070350000601201048207a50092410601604440004240c1007814100d01100c003003210203041d082180c042400212070b42c170000020b01a86820800960390304043c5403600c1902030543c42e069807010610010403001d5006400d55044075017103040401c003d00009111603c0c107486034201c0c040b103482d01061044100c60500a035100356001d8030703503400598a40003c680040c50414115034000f80000000b8009456054070680216060401d182000064104002a0380000140c03030132015494 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 510777760 1250 510776510 510776521
    0xc0209130f0f031e0513052b0305030708011418060d020306041202060117100b010e0603101a0408031903090c0b030a060b0f1209070515030402180603061f03020a06020105 75
    0x1901340c00030303000080c01c04900d0100340c0d13881d4440e100440d00c00e0070701c580c0303212406043c00e02c1080c0c0e03441e604100390180c0700390f061500c2c40c0c042c081d0340085d54402c000404e00d0001240ca898002210101305d8030040401c41c04003803984a60501c0d4100a10740364002c0043c042100068800708170850190340300740801e40c00b10000c000003d00d0000c050340f121503080f9024040c4407410030007052000c401d020591010540c15680300040c0c40c0369003540c1d0502e0301300c6000000c02c10440160103022040d10010b201030281c25a0856058860380128062040c42e60010411040c00082d000605c8102e40c0c1507090100341362480b80c844020343c226a502100070604000104403d1604500c0340c036001e828801d00050608111400240e4540070f01d41102d402960807802007410203c04000590040c0340003043e0f1003190400c5260420680c00c20ba50803070141c65210080030071b4200481c12039214034800f0b03008280c1e5580380c0c3c1143c10103090304640075194103842030001c40542c4400303e881024000c8c5d500007182e0750421 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 510779010 1250 510777760 510777797
    0xe060a05092209051b01020303040c181e020705070801020910050702030c1818010c12020a1701060f02012007020d060b090a050f100510030209011413030b070c0209130f0f03 76
    0xd017000761381150810410440052010500401642c8484007140300c01529210040001c14905c000d0501840c074961074ac0c0c03500c49280d0010480c1600c40c609580c1501d80d01c080150030b03400740500403a4171101189012500c07500c1800640b10f0300c1e00060880306402d0500300466802c800440400101641100800c0305000c07001d0707c80f031500c0480300000c011303d80800340d0023060805907459800f6050f0f00004d41d50f20703203849014414108101c000e5000c00c5541c0d1610003900060f4418184009542004801e0002c6199400b0015545c41c000107040d00e0314031281d08002400308401c9048a030256500072074402500c40f6880030b4070a80b459000045c10b404c0444c030000d400340e0300038114a0384034208071041c4043d441d0100090b00c48492400c1c003584460701d0500580b42103600880303070a80007a0100d20402400c0c044581e082c200cac0c3c021148515180c036194800c40700856070740c2010390840168804100c42d440c00d401c40c81d0f00c00e80584118400b510741d90f542e0f10144000840b09900198802c4062080105d4 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 510780260 1250 510779010 510779053
    0x30b010803181c0605070908010f0b3303190e061b0315060f0414032b0e09090705010806040b030a020d08130e01060e060a0509220905 59
    0x2809401181030101d5441c1c01d00382c900980c0c000b240680c07444120340b07119072190001c005440703034004c00c113004626102e50020302240003440754a00940c00d20072a5442c0200c50700c11ba10b08400080e044034140c038036448600019a06046190611800d80c1410100c00212003003d10b004c0d5851b610260180c0c02e8010126082d6028110001010341001044c8298000d80c91182d4072040c0382000341e07680b81c0c2c1ea000000c144101c0e0f0b01404070380050000032030b0b101501d100070080c0140d82c1c3c1c98915078090401401815503885080d505481f020340f901401c4d200040c20030003020200040751400101144058001c10101c1c94280c03401802940102d00030711166802545aa510003806d0b90100010100440081da0325650b24901030300070040119610b0600a28108440720048605920031042d5a2440170105518003403140800148030318002100b2480c00300704a603020200c583e612810a4440400c03c0010350600407205030720070020045200491a500540d050580500090110808032160340d04817000c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 510781510 1250 510780260 510780269
    0x60a050111060f04060b1309060c03090203060a0e10060815070206060a0506070f1208041e02130c09090c05071a0c1207030209090114010f0f0203090d020105070609060204030b01 78
    0x2014406030710708040001d805940320300700b0319070154141c4607800e0810040c41c0c40c240b255007040204405000c5006d07107404c140c1c0c8070380c86840108404ca80c504421800c032580180001d50540003040400e076200c440d500a0706140d030300d84081e00c480035440c2400d241202e210398004211a04020b512100d10049000c80716413000543c00500414a440300005480940602403948a120013081c00c1007844581e904d03100840e9032000d20144030806010340a080e401040700c080740c10400103030070b00c940302c0341c1d4962101090381e0181c90300307102401240010010f0100b940c680410004031900024048801d4010b10107484441d0b09c4040d900c0b541c5050082c06580042881106025014148811008a44116a4054019103051109455982c0c0480c040e03c43d914490780e0020068002051616405100320a1403a0988500d08402d610080c151181400100c5201c0507170024024882d9074180f1100040245105141480c0b40c0305007035444000300c80d9034590540d019079020800381304101034030901a0161 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 510782760 1250 510781510 510781517
    0x2818020306153601090902030f071503091a0f01172107030c15140906070e040e10050c0d0e0f03030a0234050c0a0f140a080d08060a0501 60
    0xb600c040e001c6040e082c58103207483c5555000050341d40c3c0042c582c0c2e001c004141e540c60102c48039940c0d1251210080c01c1c1d00c00007a407080c05100c0d88030a510500040140c00c4031081e4880305815101810141c00034204c03000c0988030f90b4024040c08514035441440d40f482080310710803499255040c11031103c901d16014209508a81c404d5044102c1c04505843c480004070980d010390b50b42c1c00e8546422141d025031a40002c21440c0f0760314032503084141d01d400100440042011072011a5241c0e1825640c0303480607100780f0082000b2501c00b84242c01c1c2134102100355403d401c12619143c03129100c801c11598119105c4031000408100e0f42180540f80c000c00718058002c0c0e001303111802c010090a900e078030000d0008880c0a40c000780c000c0d2200b44001090103003000c4040c050142c8241900b01582d0603400f414106c5007030098424000f8180341130a40340050f55959a0801d10680c100020307240340288451286034026001000064080c60402035180d5030b05940d92004900e09081d0240300340c1841e20303040581407 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 510784010 1250 510782760 510782791
    0xf0902010509210708030a140a0e0f040617010501171f0f0902040e10050a1109010509061224090f0c0306011809150803070b2818020306 60
    0x980e90180c140d070b03207031101110741160056016000e00301e5100009108060f50040301000108840044041c00309a0f0041d1985d100c030302c00f0103800003484c0c41626920400316900204010607402c0200120480c0480039200045003911000100b034044181a48517107a07a46440040c4402080000e0300310f122031100000f002031610606001010903444d40c00b0340d480a036904403000004601c0e0304400f421580181003007259000c030503411601d83c8e81418003a8031090601c4c010540c030b004c82d07200c0e500182c4440d070000381c00c1c003885100445041d4070200c2c40355030041d030078000480b0010680ca00c2a014036100c451809500d41c00b0110928005110000248180c0224007041040303125840c199a004410381a119500e40d50000161105c4514a0700c03800e0303d41080c800854941100d9000c19100c44c0751b4166050301a503103440165682c072482100425885000e03010811980c2c01244403403000f56040c5014070000001d250a40840300c40d031400d10b4a010608901e40300b9410140841034110b404e050100a8 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 510785260 1250 510784010 510784013
    0xd0b0a2d03030e1201110d06030308090f0c04020f040e0903030f07050c03070201030e031e03060a080c031203040c09090302060a05060105030405070e0c0d050a0504140f0c01050f07140a060f09 84
    0xd21403103c2055400760485441040b00d4000a40c03006610b515480b074815155070000d03031b140e001415580070850114044502203000144000b98151010305030100030100b0352441024007010350007030b40e2030001d2000d050101092400d0b01c406024032541d528001035442c1d1130001401c070103000002d400c8405000d41000600401c1e03402000303d4168a40a0801013500500700d50042d1840c0300e00080d039100801c440884001040850000b1801008201c0d14610460b031030b0b240040d00c4e00c403090318131035156008a401410014010010f154010301501c600340c0c0c4941d4410700002910740c1184110300603003028007008842d03103030b6204040e00000c1c2032904c1030445c581030b92400d41d02d424902501c84040c141000240c3d00042810881e17180c0c040004090001d07040c1506810083c110036036040b103420350b0400100c095040d000030061001001c0130014a50700307800c00019079141d4131003c244500c01908000c0c4002082c01248403103500c2091100618140c221401c050302100c401c50190542582480c00c0f450 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 510786510 1250 510785260 510785267
    0xc030105220210050903030a0906030e0c0619050903030a030902090c04050f0409140109050718021903090f2123040501050309030c010e03030708100f06050d0b0a2d0303 74
    0x1e01290341a6030281e05140000c00c142c58601841c0b040c070f6814440001c843d1400c07640480710301c04807406500c05111000303014210715110f17139110301c2c040d80150060000505070842c601c0d040c0030a0b1002d080292070081128040381c110f0b0f00041e0100c0110b40c64960500c21410200c282540c04020900c09505090410001460000d0942c2c000e81c4916114402401071080c0300c2060007080b05000000c2044030140e2410b236444001c40e100324000c07848040406240088180201d540111413100702d04400c03d075640c0150010600302e00250781c80020308006000250808101c907020750f111003403030340c4c0305000410010110f05490880680015101ca56100010714080507202662000d00b08035489a0300c10f10220302c2c40c0110200705100d90701703080061220301d102100850044c011540c5030781c4650307070f00a001c48d002a024420740121000c0c020081001d644140c0191141c09031169000c510070314a100015115030458011102254540c04002e07101500ba5107210305465861403504a414610345014 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 510787760 1250 510786510 510786571
    0x9050303070312200c0f1002031e101206050118060b2506021204051002160b0408190806030f190f05070803030103060b040605031603080c031204050c030105 69
    0x8604161a008000001d00e0b8100940000b6483e0078044c6032540300c00c030000c0d030303403038001da158060341d401000701000c614601402202d1140410006104000c00849030410500900505810f00c02c1d090841c0842c81c005002c1d0031302d1060f4003c4001003615418020450b02240e04202d80d515100d04d0100c04011001c0010190b0301c1e80081d02e000c19614124200c100504080d403c10014001403002800240c0040038007036441c052030041003103071245041810100220300c91f492160f000704000e690071400003240c88a100b40c0c403d100d800030a0504008408002c00340100300d0052020520b00340c00c00c40035040c00c1084c0c0300e00c4100300d002001900b002d03106074540d01712001c401400401145e01507500784102004244020109202100e03520b40c0e5a08009004144881030107218074145540003030540390018049a0210a11045075000361442d6540a2154404111034070136010a0001da18600460044c091003640100c020b071081401c69004c2508480d00100003219818180701c00001e41d000b4030740078 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 510789010 1250 510787760 510787787
    0x7050c010e06060f0f0d0b090a1a0f0c04030503040306020a0c05010513050d030903050d09030306181512030509011d041e050901051311040f0c0c060c11150604061d010303090503030703 81
    0x1f0000c582c0c464911980c00c01c3d08451001d4603000440c0f42c07505504990014103803003030321310365041ca003951500c5000800718404c612000e005a40140018008200316034010200c00a6500301040ea0341340c155640b50949034201d030104c4168244030b11420074440180301d40340544520b481e0810000055030340107400c6000754081041d1865403a10032404240c0a64040c3c2d014020640d00d20000c2c080f4080460003914002d04465840c1c0440180016450a030220f80d6001650584880e41040300c0c4400440d6010304549200c3e02990206c6102a020b0b2140e04c1203601c8100c400c280072414a4001040380d0030389401400c0b200d001e0307140038204122246188080141d65610070000b01c5c50302c80301070005010700031180000501900d071007403032289241c0040b1107081040c444c1e0020310480d901ca07030003039070a90200141406142c1141d000781e004034000d04079041e0300c500e00810018400b40c031807211035802c032008140000001e220000602c18150441e054900078641140110702e0501c107954014a4038002844 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 510790260 1250 510789010 510789023
    0x3050c1213050f100f0902060a0309030e04060902090f0619300b120c130e010e0712020a0e0105060703050f09130209010323060907050c010e06060f0f0d 67
    0x200301e06400c4604411a15904581214012683d120205494501d10082c03980c605180c41c2c1d001259103114083d84181a0300286040d0070001c020308250301070004401d044040009900c4c1c091140d580d00d209900143c01000c07c0140c82e500c40e0410f01c40c1030198195280d100b11003e110b000b000c01414409505542e1a40c036142d000c50410050340148170000c0d05035580c00a00b2440310030503400d91a40105895001190740c141f14210800c015a00c62207640542e58205071240d2004aa002e03036500661002c51540c000000e04c41940e8600c2c50404030142c11480306d2000b2040c0f55803d61802c480c029020b8410003560a005500d0400000d6480c8035089009090210200d40e0344600e08000c02030300c0d04c0e414080d1a45000840d403004210096114481c07540c0841e141c081440c40003c804803c2c28034143d03e4220030071840c0c076000208094840000c000004004041001c3c801094081c0100d00440150000804035400c282c010401c41c1081c0c0d0340d9081c0a80a81c0031140c1c00caa560340c0500c0300c440d40000 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 510791366 1106 510790260 510790297
    0xa0810050d0b0f100b041424090d0602040302030a0c0906080c030a1713060c0c14100305042102070f0f030c0611011401030f030201050703050c 63
    0xc000b8110695032400a6207580300e1100c196001100020560a500d44d00d0941429507803090700440b4946a041c482c80c90300341000307000f03052442054604810780c80c0c0300d10880f02c441d0180841241c400c0e4035041003034062100036412203014680140030b9403071640c180d0400300d000017094030425201a1070301000050528010451081000c2c00030050414500035407500c8030b4207810550b82e410071850412400301040e9141031244001c000340d0300d6605001009081c151101c2400780e1010321180e440000ca08c0c2240c0da4890042980605801c000400d5122810b1004c50016503c1c1c43e21035850309900c810384c4550b00041c541c1c044a840c108130150842d2a50009540184548001803414921074003e000d61030292541144c44401c4000000d540080881150b14a01c001e900c1a5004440c4540c1310b41490740c20b0080951010040c201445207080c00c0781207509500c41d80450314030491007603 = true := by decide +kernel

theorem cover : BRFrame.Cov 510611510 510791366 := by
  have h0 := BRFrame.cov_init 510611510
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510611510 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510611510 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510611510 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510611510 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510611510 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510611510 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510611510 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510611510 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510611510 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510611510 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510611510 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510611510 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510611510 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510611510 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510611510 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510611510 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510611510 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510611510 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510611510 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510611510 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510611510 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510611510 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510611510 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510611510 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510611510 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510611510 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510611510 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510611510 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510611510 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510611510 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510611510 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510611510 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510611510 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510611510 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510611510 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510611510 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510611510 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510611510 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510611510 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510611510 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510611510 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510611510 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510611510 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510611510 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510611510 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510611510 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510611510 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510611510 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510611510 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510611510 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510611510 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510611510 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510611510 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510611510 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510611510 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510611510 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510611510 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510611510 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510611510 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510611510 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510611510 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510611510 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510611510 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510611510 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510611510 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510611510 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510611510 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510611510 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510611510 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510611510 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510611510 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510611510 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510611510 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510611510 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510611510 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510611510 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510611510 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510611510 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510611510 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510611510 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510611510 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510611510 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510611510 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510611510 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510611510 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510611510 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510611510 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510611510 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510611510 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510611510 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510611510 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510611510 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510611510 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510611510 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510611510 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510611510 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510611510 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510611510 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510611510 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510611510 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510611510 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510611510 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510611510 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510611510 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510611510 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510611510 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510611510 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510611510 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510611510 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510611510 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510611510 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510611510 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510611510 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510611510 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510611510 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510611510 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510611510 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510611510 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510611510 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510611510 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510611510 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510611510 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510611510 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510611510 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510611510 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510611510 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510611510 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510611510 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510611510 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510611510 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510611510 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510611510 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510611510 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510611510 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510611510 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510611510 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510611510 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510611510 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510611510 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510611510 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510611510 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510611510 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510611510 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510611510 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 510611510 ≤ n) (h2 : n < 510791366) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
