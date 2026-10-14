-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0621
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:46:26.583454+00:00
-- url     : https://prove2.me/submissions/3ac88b61-2bdc-4592-adff-e5d8b7930e9b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 111510791 ≤ n < 111690647 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 111512041 1250 111510791 111510793
    0xc120516090b07030c050601060c020414012607080d11010c020c18100302090a0902040c023c03040f08010f0c0f030b01210603020306060f0d1b0b0301090617010e 71
    0x11801c0c100d030726842d40c0c0928411014060001d54401c00076400b441580c0c020a05078840c0d0110310084d0045c8000c0d2040714852610185003980140b249641c115030220743c220030550340000915910844524105054011820500c244150040b90701c3d8001e0611102c06240b000a001c0d20b01e00304020390390342a003181720641c0248408003007032a5895801c4c455034000201c480f240200e60b80c030340101d00da044041e50750001380c0303846403042001d604060184100701021840200040748008220a041c000d40309524000304440b005003000d00300700c0c2442e800e910b100c2001629a141d80e944105c2c0031000151051001e15403d00c401d050719500b16214203082d296050f181c1060240b9104001c6004010b062900c07418007500300c401c401ca01f10805075261400315603541c002401421030041600d41030b0010002c600c101118554040c690710784092407140541c0c8041010703901020103420300c504c45e00c15041a011144007000018403100d480d04038800b1200e68001c0541c2d5000f00b030754042e09071740b039803012031070a = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 111513291 1250 111512041 111512057
    0x60806090d0804030215010f0e06010207230406030b0f010510020a020a030b062205060f150702040207020607050109051506011e050307030204030c08010c171023040c120516 76
    0x1080340281e4000740d02510034419500306ca4100b0f00101d50f034400a07005001045c08102040c4030746d5039003801d1a50001c82c02d0004124551a1002c4442d851030300300b091507429030103030000008980b16608090065a40721b800703110340e40342c1654021051942403081031b108a03c00852a2299030020582404440d0054813410030035013140ca40d118080d00140c4450340240702400303811100c0722054240040398100200100300b609000f01040700c2c1800010541d17100d030040500030702d640c1a410b412220310030707415034025031501a10b0000550500410801400550030030030140104880442c00b0401045118024291134807464011038810741400358040c0b4090020a400080b1405a00503503032200c058580903190035140d070744503203032030080d980007110380d03034480c0048199140c01038207490120340084203004851404508070111210148038008400304403201c41c041d0301c54070b4402d103219079a02400510159200560040c0404500c5500b880410700e0000850410030035401e0342502d205e010381d543d5070 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 111514541 1250 111513291 111513313
    0x91812090d0210030905010b010311120c121015050307080a053d05040c1706010e06040602030909060102030903150c070c060807020f0304030803040816050304090b01020106080609 79
    0x9500e5100d040019485810020340c2401070742d51044191500e2003a40c0c002c00e940419280c55800d507a46001e04030705040c20031611b02c01041c00001503e0100301c041103444203e4440120f412130620400400c01c01d010010401c0010a03421940d4182c200c8404032680408080c161400300e405000c16141d81c0005455900860802e50b81600504d400201d0188070100441000000c00d0146450044450402c16055403c2400079400784120b40100010794042c0011500710100a10285070170245140c84400200071404ca41d1054140b0030158034003400b450380e2640c69480280d0703680c01281d0468403403c00000010015407010064032501e08000c0c00422501c220780242d00300141c0d00501040d000d400501c01da40c0421480c1a4450044c41151105c20030f500b4940d8009003000003e18056445034020032040001030030700780890340d00603001102c80b0740790b800d19100309081081c1d040c0f02808a00c0080703004034a1492a9111122032a002d230020480e156440c0011a02c0b6901101c2841c071680003005140 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 111515791 1250 111514541 111514573
    0x1020301060516150c020f011824020403050a080403020418170a0c0206070f05151b0a020c040e072303060619030515040c0602010e2505030303150918 66
    0xd1940c030b11070f103882072001040703036085030441d00300380206001039111225811040d8404c1c424002e81614483c0ea049d2292016140c4084041820781e44a56001902c80e1080300802c140d4107a6019591290a983c0034107504c1c00d0502d6240c019001c168032851410700e200000900c00820b00c0c11840e070000b1010540d48505040c10319907006201004103101020340d070b90b401603075040020b2003203511400b104118000385040c45407a00315600d03da22140c00c1e00d00b040c00601413a42095180803c0e9203400142d840d010190200d090000703540c3c034650498140001301008130310100710034040d5000310074400c2c44001d1802c1c0c00042a1584003240740c0640019007c1941d60074544809207071114120388880341c0b43c2e542c0c0c1e03600d072510710412801d4911102c5a4248020444e11101c16001000544000d02c40c14403c0da600a4540c401c8098100c414500c1040042a2850800c0b203000140401010343c2d8880c6000c2508c5856922015800c500c80c0c2d80b101c00056040617803100d0381034031035502002040c10944400c1c541c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 111517041 1250 111515791 111515827
    0x1103010c09060806030c0a030606091404050a020405181605010e01050a0801030f020607020d05010903020d0c11190803160c210b0a091211070f1503090606090c050c0609010203010605 80
    0x81501742c01340c4462050a62280703441c82e4002c500c51400058018a01945842103c05012281d01c660b040001448049040003a6045036181c0403100050181c440c0711602c290f280f40c003200001d80703010b481c035400e4404070b0106c52401128420b8030380c064a0303511000110792034843c1c5c42c940c80108801c0b000620109030f140c0c406030036041c0f0160019203041c03e1600010b00620003110300702d40c0b40e03444558607010980e0500005070314510170306050007408201d83da6070313015480741c813091400740c501c00d840c4035600011900084c0082c400e0382c06483d030751088a5195080042a050141c0303429000d00b10008188481111408940e8480f000301e450301c01840c0c0d00c201802401070203000d45652280700100102d00120900108510603440304481d0705200c90b0014200b0030301e9407100c010b529112008200c0407a0030721140160f01401e2400041c845c0207850a0401018150800e0000c01d2070034190f1a0019084802000c141000c030781140c0540c0c0d01d20701154282d110034012343e0700048050180390b440c0c640c801c5030 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 111518291 1250 111517041 111517051
    0xa030b030111220e0402220f020307020a020f100206010614130f090b220f02040e070c020a0f0803090103020a02100c030209180609070e031c0c1103010c090608 70
    0x20501c0310142c002c2e5452038102881c000b041c40e031501c41000780c2e0010030700756200401c603050320940645007030f40005500d0751411132081858485c00040241c245441ea000c00c1c1010401c80c81152a424040402541c0b004152005c80c040c440c2c914030f1200e41c3c0386c8140c4a90911540d507000303081c90780c01c100c030865004644042103807401e002489203030000402d228000300540082030a520215140440030800d0741e0b0812401e038016078000814071803140340c0134a4814046040a0041a40115929800028071860340718041250128003403181141c0e00003c1c00d0f50315030003107030783c0d110540d04d801c07178140c0e0384090b4030481610754010004040300394044d4014003000b074044d0041c0d6541040c4050b42005070360501d1114400650300041c0b04015240180c2001c52100d031540c0e03880e0040c50810f001c150b0301c0e18050641406c0c0480510000c0003030740c08120041d4000c1c141741d8049a04803a011020704800f50000c0110b0304d41410114070a20f508051051820989055030381320300d0070749404e1040d03800440c0505 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 111519541 1250 111518291 111518293
    0x31404110a0801091109070e1f0909050109020315060301080a021306080d030e0d030905030d09080910180603090203061305010225170f1e040e070c0c0501020c060a030b03 75
    0x6000160700b0400e100d800d07002d60040200309601310603030041000100d0024a160f0a01c144492500326a03112045201451184401d010441e003480410030380c1d075500d16038040d081d00c82c2880008140100d050b001380d8015076809001003100c807074040800000c2c1c0001d000380d0501c0d51004500340094a4003507204404141000c2e0001402902c50b10f00c01c0c1080208040341c4c2c082a12034003051140002001955048422440d007000043c541d0740d03540e612440b8442039100e0303541e00c4000c5041480840400c40d443c002d00100801c044045200d0040c2c0210250014507002c80c000580004072140240140c0040b1640200500650b07509c0ea40054494078805100751082e650030b000d0229514010541e00303424100002100041003510302c0c00e60450420000d080310241401e00c4100c6a886100c0140d807915203800141000c000f0418003a45528042d41e403101e80b500350140709011b42e82d5004800001c085000b000d4541d502611a0016a81c0c2c140c2c10300529004401046032038590b81c840d0380f062960b814014 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 111520791 1250 111519541 111519559
    0x1003050c0906030f07020c0402191d1c0303050105180408030414070605040302031b01020606130b0402070303050411040c0e01051b0d17361609020d0c03140411 70
    0x40046601c0f03030400c0340c201c60114028001c2c02083d03601002040002c645c100da05500d8103241002c0904d040d00070b0304000061204a000c0d496500e0203e901100c8640005007001c00341c400001114140030089030b200341c2c00b1a1402c4008255030800490055044030030070180005500c40c2e5a50b9405a4802403041d030b582c40700d80500b6410b14000384080d8000b4511a5100f070f03100d60440c0101070800941090300f6101c403058420070312150b600400c0990b0301100c1200c1c0f1204000640700404081e202c0840050341c410b1000031a1030030581c2581c01140034500070158034050304440810302c42100c50131914100810101000c103072040d8419401401100e0217a0798241c3c001c2030756469149030080003581400881c1620146001c0d44848503171140e807090700180e1030100c05054078695035510201030f001c4400304801e0310214410312001c0200c1d0030440c84010341d45002ca035450f10084000d4008001048610b4244a920b0300001d11a004411a03401c100146455640f00d0b680c2d8214004620754291350462582 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 111522041 1250 111520791 111520807
    0x1031e0204050108010c0f18050f0102030706020a020336090a0b0901090e0d210903050909100303030e150a0b150d0c0314010b1e0405040c020708011404021003050c 72
    0x181c0030b1036000786010000410010103512015200c2c8036013245101c100411008a41500106d514031401128020b8510451003200c0c4c0b40101c0c114821214041c150900028114649507030000081112051040c401000c096881d07482107841c4001c07010f84241d10004a41040052800001d0fa54000d1083d044c0000c0e424802130202c0d10a40d0240d0092254941d100c02f501d070070040601031101041040c0c9016000c00b00401c100703100303a4510720348810042e60744844000401d4003c00440e1003a03a80288421000d1a0100c200010b11a49010881c0040d04080d681c3d044480001800c81d00c104600507035013107a80d100d008000c0205031580c2c1075503000e2a00300e403003010b2810324002088508036088020821400200001d0f007a035840c0540000c5120100740100604005082a80c954264102143c208080303903200076801d500660300b006030b002e450141c000c0d0010707800140010131076142c07100a00c8001c61541100e440c2100440d0081d4000c3d1141d03440303607205d600c298015507000e00041d8149041c100c107 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 111523291 1250 111522041 111522049
    0xd0e030c0a0b04020f06070305041a04091e0e0f0309010c110402070312050f190504020a030503130303020c060903120d090b13060e0a12030c0504080f1e0a03050301031e02 75
    0x8001c240d502c848140c0a100640c1002c3c002c41c0480c10081d20b00d00c0ca440011b940042c6103205500c83c02074500c1008020300c40714509401114010300b0201e40034451051514690102c1c0c000d491340c11f0100e40c0c6050301e4140580c2c0302103940340e90102c3d0600510b06140714000155004145001c0840740540909a44091641c07244003070458140a0740d501011100390783c2d010801c50b0300c0544000b005498403000c0041e0400403145a0300054444040491241c4680c40820954240340d040141140000701d455112405032100c0d00080740e000303501325004d00d04d184003400b07a14440c1600b025090b4000d4610f4000c00004100240101c58003441e000405038010384400041c44420349402c400803034581304200600465000d03002180007154094000020700e03a03126841c002c01072640109054441c1d140b040c1c00d9000c0c2d020b540062038614203458100c205214080c1d05c1d00300b150004000202c3c103011b0050b6000000a92641320f41e8562039a6185034215100c00114001c2c002140700300b055426421001615 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 111524541 1250 111523291 111523303
    0x1110c06010312020c03100207080c010509010e2b030510150c0215030f0a0e07032102010c08010b071e060f0516030902030c0f010311120106081b0d0e030c 68
    0x5000014003100c0d4150f240c0222100038144041d003c40d480409020180d070b401081c00c500800c8801c0d0016562010b03403601501c64040d0003805000c65107000100210803c040d002a1650103549068490088000903c11105c010b4103d503c0e412001d02c14203030002030302035803246421496000041039000d139601c0311650000c4e0042c0003c0001001e654440c000c500301744650020f1621513529481c158a00041c420481c010002c000d221895110000b22032200e1091210a02950300540c91002c0c03084400b40031000407164803040e400541c078168103041e401e8414441903041c1c81c40542c0c6146048110744481100260b10002c2c00d4020414010810000741c00f4850940d9100c01d492000c100e5182c1410350703005548491308044280350070222210016500464816844501210700020314501caa004800410140d2a482d8140100003a1483d10081e1040050304940d03503075a50300780959840300c0110082c00c1045165015103002d10107900200d1054000003100c8020004480c141a90404044c1ca808 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 111525791 1250 111524541 111524557
    0xc120c151306170610030e071d01050a05060a180b03070804031701182301030804090e190f03140d06141e0105130e070806040b01031a120111 62
    0x24000258800c1c414050640070001080141001c0c40910050440c0c0d803210300c4010000c9209140385405401c0690096124584040138641243d8040f616001c41c08174080880c01c03041303001008140005080e10780340c4400d405660002d441c1a05001198900391050845010035400c000c2940e2004107080c843d030000b85210b1001d642e5055442e007094203000d000844034421561040d1109801400024120400705440707040c01580064106185948003004a400101000c8060582c400000a0007604070107041510b203111401c21462400c1e140d05650b40744c00034010160240c01a40950200313a0f4012904581400f0f030030400c205140d800c103012502d0380560041104150760390000e01041c2041551351200c07100503110304c0186418408440c82003104100098100940062100c106001c1d20110700c004204c0703480c100e007950400c0100a04000400c5410350f016a10748030000180b50310900844044804103248452019041010f00030b0703804058407292032075904c03020904110043c01d0003e14803c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 111527041 1250 111525791 111525829
    0x3260c03061c120c06020c2401090b011407050102070b0412110708060c03180d020303040b060f0a050405060402090a0305061f0e060108042d140304080c120c 69
    0x41e1500c0760822407840c00000d4a07103554a21002d550340000c07200ca1400400d1103942c00c0c1124403000b41e20b0010003074418001741c0d4400c1d01410503004144007113550341c030b04030395010740b110340490380c13540340345411100d00200c03440c00651809082c0b0300c110407100c0103003030160081c0000352402c5841c1d15101e0136094150b40807204400e101c14803000302c541c422032403020b1043c0c142c05000382501c1c114a40d43d507804050300c1004000c00000c0401c03615019600040c0c078510100c401d07102d940f0240480a902c070b420031030703041e901e410100c00020721038a881c0241c80f0124400920a0310450300704024440280402030182d80c003d6420481d2002075652141458001c52040d401005189841d42e0003048400d01c5203c1801762414185080c1300c45907191001130341c001d1083ca4051100c0d41c45081c00c0440c0d0301c104480c0005e00c941c02000d240f91841c080c5c85550386602492103ca038070010345204c40d6a0b44a18813a5045c81d41105050012a00d41a0788500c001c1000c04102c03070508010100068054114441811031 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 111528291 1250 111527041 111527047
    0x2070818040b0102010e03071101031b020f0105221101140f070606050910030b07020705040903020615190308030c040306060608071d010c0f0c030605010f05010201060902040b040303260c 82
    0xd5150038060520321000c01c0c0300078000d442c00c55452035500e02a01c40e00501c500103408070f89807507901ca80d0198041013001c07100c405c444881c60001a4985074844a141099404d01000501d10f0070003440c034040701001d00403054078007000d640351620b68000c44c40b012070402c81d040988138509400a40500440091003240b00c0d038443d4180b0780700342121919170005000d140c000c010016061340684c116000c907904100a104e0581d20220202e0906109070015613203c0d1070260000103056000607503d1140304068402a9007450002c100400016072847c06001c4840750f503401c0c0009125040030b5900070603246240c034280ba450f5134440c820740e481d54001c1400070340e0640401100300e52003405090038088494800d042c03545402c00080600c8071140d0040c0c400280820028200040c2c42c4125009540200d0100800e586982d0072198103d298441c0500642c24402c0104080038540b01b2941115007070a0f20510301850340ea019031304d18101204003036040744480c0c0704802000c00401b00034418450203500580d = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 111529541 1250 111528291 111528337
    0x30a0906030f0603080909090106030203010f020703110c1e06041701091712011502030c1005010503070e0c0a0f110706120f050601090611010b0a03050d02210715020708 74
    0x464210b0003603030080341d003400c108101040c072810131140e015105841c2c0c020035545400d0418098200da9000a4156181c14072035510608182d0140072001e209070744940c4100002a0200d66070b4000e001075550181c01ca0300042182c29003640d42010100014140b00d00307003603a400c0d01e107a410110b444807a03041d0351101540010042004102e0300c120314448006070400e10480c1203049090014001e032040e24044c804e1029800b40200159070044410340101da400a40e41c0c0d0080c005040280b00d0315000303210300c14011610160004499120b544100c510905001e201c8004840400341a840c00040c80412842c00550050038000c14020f007100d61110a1041c4c01543d0404c01c89000300c0701c51510702d241c20203112440c0c0c2c0c070011513021500c1c9864000e200c4c8003044805070050942c4860680c0c0100c0c0d0a9000003007003c0800d0481c0386800c039800340e4040d189002511b841060406402d602c00c0d010070003010000a141e8808445440030b021801410940c207592120080e90110390b809104d61540745483d4 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 111530791 1250 111529541 111529547
    0x60602060108030a050901030b01120905070501021b0333010602151003020d020f0a050d1a0a0c0807080405011413110102010e0304090f0207080a0804290609041103030a0906 76
    0xc1c0104100700043d031620400444c0140a0b010321075416040640321071807000d10342e203d4405444d0244650004000030f80740d03880c00d1a0343d48003a21a03540075009000c45080110784080c00504440009000743c5002103884144112101102500c1040600400100044003040403201401b81c605c40d002070800a0304025a00000c0c1c20080044101110060701440161120040000c2d901c1c1e0580344000014000c4c400500c1c2100b1580265401031680ca21003014404070100991280100c140d12400c142c4928183c001515007520004011030380d000045103469101d02d400e2903106008a000080d5001106910744c10301800b0340f01101c05810394a4140288603240c80e04c00196070090000704540c405000d401e603180c1c00341c3d00c00e0b82c8000340e403020300c5103c20955404507444190b00c10442e554480f5007032406480080203450950300b668902c0d010075100007220b25840781044254118040c988d03603440402c41c841c81c0091040307803000b440b075501d0400e90328108050302e80840301e912400c1e90749043c52401 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 111532041 1250 111530791 111530803
    0x2904090807050f01111c0e070801020a05041404021e0c16060305090c03060709050607050a05010501060302040e09010c090b0703021903020d02011514060922022131020a0801060602 79
    0x3280e5a505c100300d0000b860810084480281d0001c920100d80e4034050000c2e18201811075002212a5000240742080b0540c008000e0041e2807066200d2024001c200041c8030407070150080501a1201400449881e521044007074258891164221403c20120f0a5880d0a440c410b50000d00420307115824080da440d4140305980340b9160031703001018189031442008014121381d100d018020003000580e00d082c0003040c0701c1c2e224010b4001c1e002f030166503541c410050084d4002d01c50325049954030000f00f1003024044c058001107520342d61f03921504078180103119880794801d4004406502c40c03610441d1200300c4500102d07070414003075005843c4000c40e00a020f800e40304228100480504100001d0190903203c4c4405900d010042d24040d45a0b0f034000c0118080000c0460b030640000103180d020b41c0748213580d8005208640b200398404c01410041880032041007130a030342e18150a0480103090350078944010540c0c040d603c0c4140c0f40310701043c41d40c0208a4090903038210201d1651110401c0c800b942c0c04100c4 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 111533291 1250 111532041 111532061
    0x3090111011b080903090d08030a0b030307030c020108130204090c090b01020102090312130b030a0504030f0905130f020415050706050f01030f06020a050d0c020a0302102904090807050f01 82
    0x2070114240b0010710300c04000700d100880c028401020081060314100300180d40760024041c001c3c92080a4078100b8282d1f681040714085151820b2003100c01c0142004001e54003583e0381500c030b14481c5c445a900650303550300000c1181e1011040400740c507000d81d403140500c402c054003402240e800a414643c0c00401d68103200b5080d419a8010403a401c0c3c5a00c00107800746c50740743c2640c02140c440e290310702d008802c00c20542c094040d980d804424081030300c0c81988000e02580c4203454440007030300ca40300150f491a83c148076050740040600505104000c098010308100040a0070040c41c082c1c0300e9146104030764000405d03900003040800d4050400c03070244656500080380b00c141c5000e41d855a503c0300140c0c42440402098240c01040040c0ca1500a90075602a9802000300340004000d451009645030b05119080d00180300b81e00c0000300070701461280100100c0c04400d441c040310500400300c4103258803201d2651300241d9481d4800b0100e111b440c090101244035038054141810000b203070a0a50b840852 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 111534541 1250 111533291 111533293
    0x2010f14040509090c0925020106030b07030f0e0706020d080612030403020d08070609030507060507090b030a0905031c020423180a140108030a090902090310150b040803090111 77
    0x84010450320440041d24102c99040310080420f540d1301181d24100804c0c41801d41c0c01016003418002d025070b40d5040544203d10080040a91038044da104a0a03501a440090300c1400c00101250760310b44280c211803104040807001190810301409040d140002680c001d100607004071150354100781c1c0c09220b254114408840d030244401140d03034560b4a80c85540710003071044000701c2c00c00081240c0501910b00300c0b03411420401c100441404e014050b940091004c6503c00d2804d0006144140592140300a580300190000e003540c4d6040440d0b401000c2c540c02c29620303880305101590080d5145c0311100c0d1200d1204501517100c91601c07503d28950003178003080d15007000709254000d4507602d680d144020140d0110031003a06540300c0100d00001091804514000d0429007000803804400010007000c0091255440611059a620301300f800c038021018415411340141420104011207600b108001c0102c0600c080c9202c1e036109a401c000e684964408401e40d0070108084000d0340c0c101600c0328000c0e000320 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 111535791 1250 111534541 111534557
    0x3070801020f1603093201020a03020a020f01020a0b0c1b061902090a0e040f0320060103060c050c0a0302070f050405040809041119090e100b0a030509190b0402010f 72
    0xa80c442c0d0180202244101901c080d00078800901d0310034401c00008110b5042e0001c142c00011001e1603d4407511030600765121594220b5844a501c0061440e828941503401361074114069820000d280038480c401c90304501c51500c0707100204103000f00140c0280205070310681d44030400b09a54804180e60a1703241016006881040140d03c3c85542d10710381c504143c800181c3da032100c000041c04c11805a00110304441c40c0804010402400507054040140a5160040c45081c82903401400b2806400034008941100d0010400510240c02040403c0e0050401c18206101c4582c01440c21208240c10350050307102650800010218400c035a010b050182c50500907843c20b41c49699440c030884521a000c0d070390300c0903490764402214040d02c880d0441c3c05051840400181ca0081948000c2e0203100ca22a0305a8080380f401980c0710382540c100c8507810740d00d13800c002031320505800401000b00024014010074220180c15403038401705802c803a01c01d0b06042c50341d081500004144050b0003180170180032440b = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 111537041 1250 111535791 111535807
    0xa0e01030c0b0304150606050306040e0c01050406031a040c08010e07020102030c090d022202041410270302060a0914041109130b1c03170c07060b0616050c0307080102 73
    0x80c0054029118080b00140ea03e0722186415542648041d100d402103e182c1000440c0e600d074000c3c000c40c05040211020f005001208110a440b0346411103104d0100d08108810055603000703030030001c0001040b0340182d54807242440420240c0c1c2030031703030340f04006000b03000148050111a000c2c5134101eaa0f5200850561800c2075800e2014440d00c3d080d40c2c85540c0c1c000c2201d045550b501d40c7d02d56000c0c800c4100e5110407801641e003a0113500306000f10107014148401011345030414044045c14806d00303940b0b640850340307040e08004d1040ca500400310201d40c0c8002d00800961500401040108016950980010324064429203100d59003c0014465400c00d0300321000440203000703940b0709074003c840c18a00302c05815064401850f01f01401707a0000e5041c94011000540308c09602d0307040d402620783c003010074071421504d06015011600340d40d50031000d000b480003051680d84181000c80740513250515100d5404444420750b0b814080c01c641c940d001d1501c52105040070710000e0b008041c050006e500705100 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 111538291 1250 111537041 111537053
    0x3060702150c070203030d060902030105030d02010b24040b070f02090612060604050702010e0106140a0e07140a050c03070b06030d0e0d0b090a120e091008031c1d0c0a0e0103 76
    0x80602401d10011003c10514151340d41801110213903098090104106c0e40e4519091010b50824440c2900c40c0c0601c0e040ca1064600601440800c1040101103a4410b41e0882c400d03465601100c2801558103030900002c0b032901c107018000d0010742d015049001042080788100610800003c000d50b009078041e5222402d9142c000401e1600103108460200b85036545120490050203000038181e0290708018000405402000c000c0c407000b0f0b82070307401c014400d4541054104c0c102041c0e50b217000180344685450305a84024010305405030191411500e01200400c0541ca10b030444081650b00009080500540345010409412440301c0750800355544070301c400001d0f066189400d0701500d00e105c450f00107171844030140507400900d0b51000070100c20138240b906c0149520030000406000e0107445010816100c242102e84088900e100010f40c500400c4032500f0001d8500003000c00e14194a504100c51f175802c102c03441c044030b20b050718020700c80050140b080080c54001540010801703454a8011700100328 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 111539541 1250 111538291 111538333
    0x604081005090f121308010501050127030b04231c0c06140f040611090a03020d0201091703070c140306010338150301060f091805010e060603060702 65
    0x10009400180e10b0381d034003418a00b080c000200c4658240038450b004a0b21200030005004481c1210105101d001c1e111401c4a0880da021b018007408107500011510202141211018442c54032003028900c95130f0300d0b41c54900080d001d40302140d6074424100240681400301030001088151100241603454018441480d0a0000800b03681040507041c450020b100d01740e001100140c603042c600403c10718158404400e84402078604445441c10440d10380c121004e100c3c1554000304005040d1039030301e450365080009607015100228103119807240c0000301c28080d072600755403541f002c02c0610345d12100c0b40703015a20080242c0040202e0750100c20501010f440c0040c2480c152680500196010014030000a0141d1400c0c0034290784076601c480f8110904e14100900350043d000c801190b0b018540c04400c040c244c540c1d034081d18084240c840ba0800020b000b540111030425039009401540410a480d100d084d160b5443c03881c01564007031000d2103031506040046645c002c01c2403000d40010110b003c41a20042 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 111540791 1250 111539541 111539563
    0x3190911130908071101080f070816030e10021b030721090e07020d0314060d030516020301090f11010504030f0807062304170a020c0d080c12090906060408 68
    0x600905014200c485950b01100c0c019800c44000c6454501516002e2070780c10001000c85e00007202140825000007242d51150b0080d00941ca820301c45546001441d40000e5414000d4400c245d101d400c0007043d250700b80074001084111640150782ca054445103858601c82d15001c1211540c02000380c4004078280311580001950700d1503600d000051441d1048440103055002841d8001402050107421900052840c1072102552424040120400e03a2907605032000c5961642040e22242480e0003e88030710010450803020403848044e40c545500401e007101d0348154103e1300000411558014044003102c0701d02400001d1074024070306801c40d60b480d400401c80c041d00400440000c0750700402c0005642100613502c1e5075109804100151214880c1a6081510145c55030a41c100448055044038021600d114055400074041a000c040501c07000300c481000681b51800e080c8040240d1004c14028500c0288440308595100c9100408000f10604003400e02485820100003c000100d00031404e22031746 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 111542041 1250 111540791 111540799
    0x51524060c011b1d04050906060d02011107080303010905090f071e031a060a060203132c010b03010f14010c0b100906300b0402240d0203190911 63
    0x40246071412030161030450308101c0e07080510308400c3c11141d400341050789500d048880382420b8904070818001207900035030340600d4503082000040d00604250002840483c0b06146c002c143e00343c0c0e5201d0a081c101036800914040e0400401080311b00d0300ca02810b50440402c001a00c4a4500b401e10680e540d00a44110090704181c3c04654000d084501c041d07000554010480e01c040208134800048001c1c0300705c0b5500e00c90b101712a000302d1220303c000f080e601d480b0100085002c6e15030415154500211000d030620b08124100e040c01004103030701d426054024251200303481d8680d41450304074070403204190030612001d01c001d912880181c0e8410014103403107420142000c8151104031020f28941c01c0c07078026003404c034289000011100000c102e100300c0b5030020503921a150500c50b00c5e42910988400010307003d1714051000c10003620f440482411242c0c042e440b92400d0f051a00f00080040d00140540c41e001d66001c410401024805440d030b06075541401001c001404281e9140001ca14405103100d0203 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 111543291 1250 111542041 111542047
    0x3010c20030405030a0303090218040b0604020c0f030a030c090b03100b030c0c16080d111c02030c0a110906010c1a0a06120f0204060b0715051302090405152406 70
    0x30009204540c06050068103980c2e099043e800d015010f880a201708034010711000002d0504501814151030050364081c100450940f14007082002a410448044400d0700480c00141002041080102860300b025180400c26a038440d10260201c82c01d0380c80044960020030400103d80342e251f0300c10f8150f8007108403458aa44527400703518200d0107858030701c0040d481481c1212414101c4404a0301c03c0740d01030801c803002d6020b01d030021100000c20713202c000704540c06040600301000c00c403180400201344900c1100c0c20911184072070f62912880c000151844c941c8002c20904a040c000071890340400203003000d1480820558821000402c11280b500746180140041840750030250048001412500d01000704c5883d2801d2000680d000b2100480c4101e2514100092402404041d00c0040e500040070f01541301d03661804001608008180c5030900e0316021403280160358910300c0c1030040c3c0c0030310000c090140b042c40c0e94001c141005801f030206a01e800c0813540c0040508500c0e0309080c44103075059130f1 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 111544541 1250 111543291 111543347
    0x603150f100f050a0e03030a110d020a02030c060c1906020702010f0806010507120e060d0b03010b010905011e230702010e3003070827010306050d110a080106061101060503010c 77
    0x144031a17491081035454040000d95201080d0300450480d1454a1007060f541101800300302039039180c507101700086d01a082480d483c0c10030b240c0b50b4060034144181d002038895504070008445450181c43c03804540441d408500f4030103550380300d0780c088140b1045041c000081d00b000000a006030203100303030040040000c881c00000c0144070300035502c983c54024210075101d584d000d418201500c1070305e0700603010358a0301c016907004d0b40c1304e401103000325607040e1603003100500080e02c0340e000740540225031000d10144c66082008007429811400c018441200c4050b215000d6100060810a103090740920030700401d40324000500a030a0011102c0c4080325441d07198880e011400d0b411340c081d0f5600030340354017004205581c1c03000c0501e0844484d0b50841520410310006030700158107c2d5024014150000b0310080e5007800120304074a04400408000d01103006103982d1071510f400d413105900032030300041d43d414818220340e03803d02a0202524007140203006009282100800152041744040b21041d10300c0c045c00 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 111545791 1250 111544541 111544547
    0x723040b060c0307030e031203160201110d020306032e0b0f030d021c0305070203030703090501140103051612050d082715070305090a1704050603150f100f050a 70
    0x4000ea0102034846626010040241e03030f142e0708508004c3e8085582e40229640341c0c94042030001101c00761840503800c40c1c03a0400280c1200c4008803508042d9941c4480c1a420005000007034811810b81c04400350350303454548141424034803030a2484000380000c085407254107040150500e140241008000303400703007006001441507228910b2403a014000c19039000035141c0c2c0890744042c640072801009020944900c811170072901c0c1214031900503081030000ca01e000c0d00c02c2e0801a541805800049003d01d00003990144003c020303070003142d05a03c4a0b014202c0c01400b10f00704001407060014080c0180340c107441c0c80e61211ba40714840401c0040d01c2d070000d081e081d0b01101d0006103042800d083c505003144a81d078540e81e60b42c035227088420002803800003110316110340200c80c81130002c200030345010003085d55a90011120f03007101e003140e014144404162900e901d4055441000c1500344500c03000500e006100c0d44c1c106030006070380600d402c0a0394142c181c0d00140710b407100840c5840e0407961116000e03012 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 111547041 1250 111545791 111545801
    0x5010f0201021c06060e010c0c050103180212010e010c05070203030403060203070306030f05030904050c0c19050304170618150f04020d230601170d05030a0e190506010602072304 78
    0x101d099880c440c010a540d11195a1244061703602503181e04500c00302d0740b00152400ea0040200402c1c1412100741400154400c1c2c01240860354403a80760a03540c2c084c1d5001604181640c00c14a010369900e005403640d00c00c09001e02c40010300203003800d81c503142c1d00d600070a45a101c0d40c0400f130000c503000804100000e10a500260042d074101c0001c0041012078a00715440358801c0010b2031080d030910022882e00c2884400701c0c2d40407071030080103104403810400700700e50303448d400030080c0d0300b42c0000e01c030004049490805014612240101920117440c246104a010121a60484501c0d40c00120a0311081d6a981e1125800c1209006054210707a60b51000a01146071100700a003070503a00307400380990000210100c84409261410388080f60389440015a40d010f00381004015580000800c5400f14000c0c4021a04400452404251020750081091900c00d00d2070f03000c2840c00d40c0103c3c1c1e01c20301078288a0301d40035040501c0546062490300c0d5003004103503500740780340d00c0e0842100000c44c0250758581c01 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 111548291 1250 111547041 111547057
    0x3050306120a0803150405160806010e090907180911060c10230a050c030a0b0402070f08041d01141005120f0a06060203070b0705030402030f03030906011a03040c05010f020102 77
    0x4640c16012145482c1c80b00c4e41054030a5800c2c0c50240700d9003e020302e4540a01c0f0b00c14001e030b0900325070302034025508440c1501d01502d142d050040500c1002480d423124054284904108801082d02a181084042030104070142603a4610710f0072a0100005040c030002600542044881a8860f440c0d84051410160503011001040d49041150030071100c02c40040c1400c1c0502840000159407407240c8401608c5003115811541d18040001609141103640a04004079001d480182000210350350400d5103011100c00351a0712001260400881c0d08403a4214600810034103000b03500e514240b01a44112454058244518000f6124909440c492801c2d02c0f9080c4d006030015481d810308940031050030304199942c00c011410100f0100307411f4000000c444995a100f107803140c1998552000b01d841d6040544202e80c140162207030340541a10400c059800350215030041c1c00a940750110b2a081c21400c4689402001414807c00001c00d410f6031044084079400e080c400351003941c90a01324024816515 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 111549541 1250 111548291 111548293
    0x30308092401050103050601021b090c0f120103022d010c061b121b021b030717101d03070323130806060103090f1b030b07081f05010207030305030612 66
    0x32078502403004104018100c6a007a2020010740d2903410049840c2c110b4400c8000d1056220380b143c0045003001580d09078810710591201381804d071100c4501110307030700c0707030500b00c03c9025400014810b600c1c244600d010046c04030907980f000302009007110898040c2400c141030612103100c23003510900115810124620407000c000700807406481c00085c100b040d00c030303103020381261070201d0840364048400c6822150708001d400524580a840a410703407050360607106240c25003d2810001844910a5000d4115010b00320280c00b00c00c981d02c440c1d40881d900446425a0361203c035003d0094440003008840e125a0145041445c00e10842120084071038402c0081441780d800054015100000307100000645980c6001e8523055182c040c0114103840c07001c2c0024141d80c0341024803900040c059000f1103407a030052000f01400795502e031141d60004100301d8465000c94220801c01004452440d00300e03980c00d000307415102d0a9418100001d560b0703081400014140038000010481e1565092149048501844 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 111550791 1250 111549541 111549583
    0x21201080d090801020f09060c0709050c1803032104020a0302100f03150b04050105130906031406090d02060c2212120203090319030c02090a0615020307080403030809 73
    0x140d001c0d6a861a0741c401c50008454500110321010103008031081c20745450401810922444200182070780300c1e4141000900c9000030000d007000c024050b4030320500340c00c2070b52a02c842e45c41842540c0300e0100e1042d603101ea04100004e10303200c230b00c01150803140b00065500000d142d803180f0126200d40100d81011754886050b0221034001d0368000c86060f005d010740d640610900c010900b4280401e01a800342034205003003480107200c0c95100c1d0000e007080b000010f51500100b0340c0c40813500101c0b0032581083c1e55541c102d0f058103850307060811400b50040da440f4024400020783c4d54000f901c0302e05c0503020180d40440012145840000680e0039040c2c0d000c0c0143c40701010b0b0360760258401d813314681007203a00d4854000140e1400e8000300035201e9103c00600a0305000d10004025201d03068140d03800c81c1803001d104a542c0c09610342980e0710303200f0400755500148240c201072070b401c440300d02c4415400031540100714040c009003215060b1000c903541410050210307128640c100741000702e0060005096403c203 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 111552041 1250 111550791 111550799
    0xa11010906051e040506150d0c06020a0c120302150603030705030c03091f08074d0a0201090e07110607020a020f06280e0d0309030203010b01110d0302030406021201 72
    0x1a0b0140e03014608107040303850350001d0700b4403d203441e1a0498001d0050340111001030000c0e80c8165012180c828028220010724100d07179101d148085207608140010b81c802d808031010000340000340d00251007800306c1240c040c01d451760f0003580c0e092140c40c22502040c0010118840b62404c006540c00e4550000030f490701c414003a03111a543c0c1d080800503510230300c808002c0d40c20000b10941da06203064000c3d40c41100654139580e00b502c0c40d0104601c00c0c9250603120aa403400d40014090712800000100040300010030110140100481d0340c4905942031f8100d80c02610050f038200490300b08486d005420703007101d5550400282c840002d514640c4556008400401165070390200b50030001c00c2c800c441d005038088144003030011500a003021202c1d951444d481140c40e055007c03508000424903440c119082c40c1e00d4001242c0e000c2c3c82c0720411030118140000900c00c500d001e0003039401644c020720302120100180c050082e41e40d29500301040c18581c1c00808035040c00310540449001101043d0000304650395 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 111553291 1250 111552041 111552053
    0x2040605060406030b0f0f061b0709060e060102070816170111040f0f12030c031101111309050a02070309030201050a050915030403020c010c080301211502130f050a03080a110109 78
    0x80e4800644c840c3ca0f06d248407804030324240100000304007001c0d00050400d00303c01d0107070f0103456640c1407070031013445481ca0000b000e000a00500015103c412403101c00d0b410410006844c0401940004523960056000503a095184100c46021100150120f40e0403201e5811400d00600e035401b1080c00e0420001404115442d1211460341110210141071000d40d41d1510711030402c078640c800090005041d0b00c061000309100b40742502d940ca003488000100300c481415803a03125405005007900c140050041003014064520480381e0040405000394502542513600418080303a1b0b000081c14402c011070000d40051048055803064070000c2e001d50460100f4030020840c0d600211000c60040c81040303500b1015510498444043da54400c8002e4156424070070000b4003149055801045048001048008151141c402510071821524016583e800c2e000100413502200c0c4c1041c10030550900080109445070502c20302240e8110410703a8880001034822200080700d404a040598217045041091180e = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 111554541 1250 111553291 111553301
    0x3140f010810090201020c01030504050c0406151d0607080a110601080313120209190e010906090b0702030c0a121101020d150f0509040f050a0c0e0f0f04050d0c0204060506040603 78
    0x500c00782210003038800318440e20151503008500a005030080701d4000c18550013500070079080b41c452005d4405440440d4081030490703d1070303071200c6100034549030f0440d6180e41088020300707494245040128607512075400b01c1d0040c4500c01008100e808001403000020f403040e40e41c180c064511a05403091940e4803040300f81d0b03c1c0c02c142510803600d905041c00140840c40c1a800820f80c82e4050101d00050341d070600c011010200644006d002a42c40302482c0482150070311841400c184a41000180e4006909280f804114020b040c03905652042001a0602100160300c5805580c04166444003e01c583c008031010905001c00000b198004100d0a10a13003081e000140258400d2150340c81555548034008040c071218072030a50048503000c0072401181000d550b04d049a4042e1044444c4203419659400c00035911713a0040c07400e40d5810003444020b0555980703264105c603200c416000c0c0c40c10a038460503103980400f4000014001000780d0001191102d801810003404020030683e00c0320756800d07020380548 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 111555791 1250 111554541 111554549
    0x102041d0712290103020c030a111504050a0609050a2f04020306060d090f0804030c060206090109020f0d0201020f01050109021206060705060121060203040c051804030806010f03140f01 81
    0x40c6004207003080c1401144034110002c001005085100740d18180f4040000c602d8030440d0b0b0415400f0001e04142001c10001081d100e00742d0350f00c07001010780003a41103040c40d03009106e100304030304404140404101d000070402c0c2c0c62a00b006000629016529180b46003501107500108410b81d022142c46c0000d0707508103840d02c01c100301c2c40c2021b03005c0381420400080303120488100d40d001c50244114083d001040c0e00c1070805a1283c1090843c1c00107544600100390011344c01241d00c414a004140320681c1d043c4401c5401208d02c030004d001c8100c46900041d020501d140b803845c020000d00744124103685c03081004260800304000200103550b159100c00000e544042e401c1b4401d4510030011071281d041080403640d100350010302070000e59090280b00c149009803c022031040c442200c60301400b08065200940c0600d00c1a0951038200303203404148001c00701c043c117610a03044128410400070036000760500c1d500c000c0900c2d01105108000206038010308040918a402a030168100b045015070028514140c1d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 111557041 1250 111555791 111555797
    0x60102010b01080c0a05130906030f05070902090d02090601051207030c0f0903020d081c0609052d040204020a02100f05060f060408120721030906110a020705120102041d07 75
    0x4001d4000151164207080d1110b04d40d0040802211400358403502c05000b01c0c2c80c4c40420218140e65803020308081d01c03159041038444a00034000c0808100040282e07000908914000b9401c1c151403d000403c901078800019000d4114200055011383c420400c81c0c0803580b09030001021810301460040c01403900c0c452080104140f0340c0c03811a080c1c00781c40e0203400c0703070340c01130502581019503601c0d03401c1c68202d11030201c80c00302a101d00080514885c0510401b6201c1803c0004052400800b0324202e01180141c90341d0311604543c00281100c141c2180c594041e405450250707844c0c5180303000300c2c54403e039910414000e620707208a140c2000c00e950032141c003804007152400c5800f86400c08011603441184644201a80090200c0413007038111800740048501a24101100c0314a041807030071800e103c1d060381c600080d600d440c42e0042014510641c50503070741d0f00d0320046c28159003c801035030f90482e901803203115080c0b925420428140940484010300411201000c0881031300104103554502540c0282c04 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 111558291 1250 111557041 111557051
    0xa0e0d11030705010e06092b080703021b01021009021513090b19090b0102120408010212010807120605180d08010303021b0a03021903051e0c040c05030c160209010e06010201 76
    0x250320804100172411001480342c3e1510709080100842506140c2c0e9a10b581c1d014150b800e0341e07003c415002d007002c2c6400b4110440d503485a5190007810401c00c1c1018a1240081c006054240d903130018940480e0007032440001200704141c00024440040600360064020300080c240030030046031004001181c00a0300103009101c01c40b030800001071543c0381e42000581d80603200b04004035003070b0848521f603201801514100300b402070b03100c0342950060308102d1880c3e4001800307043d007511701116a401081c0101c0901001418400601600080d200018203026101d070041101d020a0300e2018801d04281c0040b5402d004140341c0242c580d11003484107030050300030302c582e02403950503000c500001b03c44010724002d0a01c0c2950708100c80d50b030300340c800b0100d03084290030b010000581c1001081c15014035604c1c2d10a00402c200c0700c440c50051030300d880600490030702d09040c52264004003903a80101c0390310714180d05d45602400500801003802c4001e07621442c18000080c044a44903526409041c0c2070b070080c80 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 111559541 1250 111558291 111558299
    0x15051503100e19020d0f0819030603020120070603240311190503070620010903030510061805061e0301060503010f210311010905120316020708030f0a0e0d110307 71
    0x11002180c01c0004c3d400c20340d00d04143e0000b030040e014506a16104041181c00e0209410016018024892452001ca503403202e00303000303540c0c020301c05810340d912400a0100b60040071082c9500c0361014400c00c801d0546901103184c03070341d807808140600c2c422200c0404030b1455607070a1420b640c5100c481994007949030380340038682030081c030340c0d500e0240e4034094001c00141d0b1508004981224550060307410648a584002000d00800e0060118881c02a03402207464104080300300b100c10700c00e90000c028005131101d0640c424081003c1001101e40c01c1701c0058948000402d0441a0642d420062012403000400420004d4000c005107050751804032800300c000361140811040107990b164041c940d04c1e0b0302005840068495105002658510300000c2102c94080c2c0d036040c44d18400745400c40b00418044100201c0118408130000c1002c8a880101140c501d00b404050b10381c0b240400c400380e40000001d80345074680c01611543c0d10421302408805001000d030903d100c1030310390004a10311074056550001 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 111560791 1250 111559541 111559573
    0x906060906020a031209020904120807030b01120e0f0a0803010603110a0210050c0c070303030608010e06070c08090409080a020604110f060a030b03120406020f070f0315051503100e 79
    0x14081d503005800422007509281c0341524100040440e0f401000d441d0504000142c8034410040c1c020340c410b00f8071848080310800044d2007508010f040e101094540300010300703160b030701002c041d203400c6444170001400c812400145042a01e01401d4603035920684842000300103140000310704039031980c0c4e01003050618511420407d0300c078140030b44005a00ca0224980c1106456100c241c114440f10007107443c01c50844079007410015294030135404a0b94440003042404000e0040c08000c05064000d03040c58035118001518003442140701904665000c1980c03a805d0b1610360110f01d519030000300c907949440445900966402e03013140d08440502054885580d14107100d502d41c4007d54004005904243c50740070110700030300e85080c0c4658144500b8034004078504001c0018405000e0550250680c6e400c480003440c500042e962107901f40b05014102000400e2641d1030980b22a00d4110001c1181e4175002c034010000064410f03290b62500589403240032540e003e51102c01142c5582058403c9200b02c03151003 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 111562041 1250 111560791 111560807
    0x10f091b080706141305040c090305010f050402100804141c0e09090d052d031e010305101d120415021209010315090903030207110405041709030c031204090606 70
    0x6640490800e076030f008450074489005d42040030303030000c02d442c9456171000000e05840301042502c0c080745d8045814403c2c05005e000c0e400032100c20101c18009410b0541c0464034442055110300b041008900204040041c2c00c00308100c0044540210350304420000a0380c034000b03203040a81d00101d00d12041103000b0b070410b907101502c5840d031034000d040c103013610207003e440f607901c21040300410046004907011034004450320100098240307803480b5240d150096080310740000c0b6451001c42c0c0301c088001040045c0c00000d803080b041c40c1c59900850742c00c480c0040c950560b03560340f4034641c1d180103908180c0d40140d6280050804c880a02c500c491400c804603038142e0719a8001d07001014004e20030448400c65500a0f0065440c05101c080c4041040350307160340920484540440850029400061501c00d00411341e120364500b43c02100c0c01c003c0350510f640c4810400070300d1440302c0c01060700401c0041d955030b028054242d50140103006d039070b1a0b4001441c12010f6902034040d10755114500313080803e07440d2240350340d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 111563291 1250 111562041 111562049
    0x304030516060f050603011503120c020a03060506010206060a03080403080d0f02030f0403141305060a14030c030610030612031107080304030f020901060c0b0a02030907051e01140a0c02060c010f091b0807 89
    0x61a448c0b811078907918210203220800e84280512800e107140182c9515403100020b6006160010301824401d000905207900035042c14418404c0c501d050020441031012601104c0d442910282c1c0c410800c2c43c2c03480a44917001c1400022480402003010004d085078030640f0aa1196031000c41c409106003640c420360051607807500c440402035405000d2800d200c801007069808504086141905010300045d15a004503403c0d9075541380070090000324201031090416071242d03404c00b40b040c1e60420014012100401ca0050100b0040b1245081101c00c02d00c80f140190180b1801d03030303503610780b2410f14a80d2002c8650007280604050400022050b110301c8900001c60b0740100704000030381380c0011060203900301405102c62070041460001b1255165006851810f89481202032041026800901041d400c40048422460104601c0c00c00982c4203840340c010a50407074000c0d49881c4000d11140c010101d1310509040c00e4a00554103051098130003a00840c01c0030f007201355844a4685991507140c65007841 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 111564541 1250 111563291 111563321
    0x60103050609160c0807050f0706080603150c030a1d2b09122f03013605010f0207080903190302060a0b041b0503070306050a1a0304030516060f05060301 67
    0x250202c40d03607200303081400c2c1407800b941a21b420092075480c0d0341d08200042200340c07102d51102c001000000d03000300c0041c2e40860200c0245c10240c801051140b00442d00800c0c080b50210004000307445007803a03a10480c1c2c1c18400021090360100882d0395103a0340d0f001403c071450242a2030400030501101c038005a80114210742d83c105407145090a80d0b1068900a032007242e058117509400b50080460140d4046156545240d032045840f0740428982110703404403150500c0c0c1c9030102c0b06078082c0c0b608903418864804c2c41480040e07542040c00e0441c0140142c0d01c0c500b42c01ca000250303a274242b00002c40038181e2004210241d0b4002d40c40d49403004800750036003000802680194000030150181d81e07005950405001d0404120114001c290b1755a40d0801c05440002c14400f00502419541c548140c0c0064581035131300c01d1300c030b9061543c4484080510200b49480140c0000000d00705445002624242b04260001e1218402545400005426002c3d00840403501d0680010712034a03050103805030000e04c1075 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 111565791 1250 111564541 111564571
    0x405091f26071d1803160201140903060c1e0c0a170309060106120603050d0206071107050d0f030e06040906031205040b190e150409061509061d060d05060103050609 72
    0x50301d189100f500080c203081d04200c48202c2200b4420b82031005040864480c0d03659040c5096510000d004403041900684483c8410300c003012003601c00090440d00103c0011050380c482d000450707030300e0204d40e02904d80c161480c5c0c080382c001010000024455400c0b40310350b50746400312601d101000143d000c1210f00302400d0740540010480e00340075079503540e01c01681980126150307490f5100c0518200c698000400183c0c041c90401088a034480740c5402000250400340107030314604000542c441b001902d0141c1760a0320f56030007204060103401000301b94400600481c0e1603982e180011801000148000d45030304480e0b030550250140300d18100c81c140c481940865090003400307041d401d14902c0c0c2c620301d4070030321840d001208000ea59500c06008043c44181c050b41e0740f94244500181911503d602c19403580011503110001107410602d00d006803081440e080c65151510b12001c1c150f802000d03031041d00608001141c0c920b04e583c58005910505003030301c00380101d4031800140132400b1030884000810b10460 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 111567041 1250 111565791 111565829
    0x102030f0c0904060b0703050d0e0102180f0607020a030308090610060c030c02190909050f010c02030a08090a0b010303081509061f030f060902030105030717030405091f2607 76
    0x100010b00b580040c058400188240c40b84440c0c4e10a5210903400e90110348041000e9100344564000c018100c070505000350708182c0168107120780d0100b071000c0248555a048156041c513260442658403060f00107000401180e07403410042d04219083d6030a40050240d174000481500907509000112206603544003da41c1c1162000c99240c0580c51003240d03c444a42d948040340400c8440403070141003440000102120035140042c50460281c850714416418071050b40c02803900441940c0104480d1300b06000c40b9641c404a9908091080034000c00001400c8000b001341503210010070700c0b0700442580714070b110480e0300800a10400880d44181d00400d1044d401000e452070003005029036030700b800d010909610344102c0c08107441854005504091380880104080e10301000007800514464140c0240204404e4045849101398090607024104050125064800e9800d80303104130027044108481d0300f510b42101d401e01c5003000c410104082501480241c01e0940400d2084c115100c4000e0705c0101240 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 111568291 1250 111567041 111567061
    0x12050408190b011a0705010c020c040b0f090703020310090207030309021e0d080d0e0a1110181505040b071a011e030b0a0b0a0306061a0c06070e060c0304060206010e090102030f 77
    0x9500d1218544d01d42806520005582401460100c080d00d80181c42040601400c0c40102d03508a110b80f8824180c0ca000079106032948424190008a60728016a49603107032030412140c00c029500c1980590320002d2401c050603456480511060310845144082006924081c2c0a02840b2410f281d8810161480340e000520007030028100e43c040d050000c50b420245549180c10001c1180e4103644161220a50542c00d1414041e403668611260030094508510071282008048080c010700d045640d40781085102e050040d81998010120501e050766039260b14500030301c603007102e0308482c013045140b0400800c10358506041d60070312109800c01d0598080c910748951004074009440d100c42c039955019081d0707154881e00e0070f60020714010030011a419103810441004600d8010504580903001d02a80111178400709001e6040100d81c9045404121502e000501e0b621a217032044c0414840040c00064407500490030038102c5080c004100c046a5880106074283e100072203041143d4241c0c0d000003040308007 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 111569541 1250 111568291 111568319
    0x50a11062809050a03050601080601060302030c030415111b010b0301050903070b0406150806160c030f18170c031b010e0907020312010306050610090501020709020a0c12050408190b01 80
    0x7485180030a010342e940c0e000b160592100c5d800541e49504804010b0102030001c00c001801800c041c602149545400c5141d20f54074040540000c00c0c1118000005003040c2c070341c0d04080794225940703403c241c2e04c40d001e6020000605243c00074658550a0001e1460b00340307418821507100e854403c1c082d500d03141d09642d900250100c02402280d465035100381c40040d6811110f02d810140c001c0c0030050681e800e1019a52031703440117000c14501045018100900002d40c01081a80010402e044c003400c849506410781080c8030301d5800142d0411803401c030502502c080042c04011034401a01501e208a012403880100295400c0505011402d007544490490924082d9558841024070580742020140a07220b010f8850a074404d403102c64560040c4401450580030120100c841401d020031010701d0140080d440700458403803101c03400d0303000c90700c4403541e40105002c00880e0340c461310600603948a40405003441d0081d0051000b01c0c41403900f1445100e00c05082d00e0ba1094000c140164aa03203080c40d00c283d920 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 111570791 1250 111569541 111569617
    0xd180902071a07030c02070f03110108190e030a0306080a1e030215090606011b02130b0f060f03090c12060a020306040906020712080a091109071b050a1106 68
    0x140940c448002c8054403604018042c0b15540d4010860701780c403040091400030650423221030340001240800c001840c4000703000d078000c030a0910303003450f0b9211900070900c3e40d085046524901e0500b071020441803000700003000c0c1c500d00707920104502c54441c2d502507915041a2001000203a030707c02c0701102030315440c6a10800d24031900c110303070156a108802e220300d5581910942d041e81d21090a02ca102d43c0c2124040c078004450102c800d204a01d0b07500000c0030100c0360101039140c0d5503500d60701100340d1070b00361110040500180c00240d640e111140040c84540c400c9484010303e0050010011462906410341c2030414000001494a500c0740038040380258006811507902c5943c0d0442e02000070040d001901551340101307a07207074030310132010400b500751035000300290005071409225a001603848403640700055015100328040e82d981da0010350b1400c0150048014594419660a00f0420006441c096103403003030040036a0b01c0040310501c4944c0c0a040d030207400c00c45200c0c3c800090000681c4e80000f00c9 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 111572041 1250 111570791 111570803
    0xf1103011412030a0306181a010309020a1e0801050901021c0209033f0a0909051032150304060c2a05010b030a11060d0e030301090603050d18090207 65
    0x40b90320030011920b1a030000b0410000700340c4848080208052621480c40d169050501c03e10a100d01b84a1464851800700c4016040c10b59448118007135441e010b05010107000b02000610754186440c1144001212070712a0034519030070308000803414001030090390002441c00c4a03840c2d082407408001c402a402008031940c141c8540e10304d1003803001104414440c81b0310103008101455162403500420020740150300d41a280040280c03184082d80300780c0e42012204200350010749512005002c07240c685035980940c840c100418000030400700c00d00150104240c015120410700034640e000d1180401421074100302c02502400003e0204400c2c0c0c124410300d1546103010f0442e240545408101d09890b51309650441171581c035070b603041220900c500030140314110001c1c4052030217581c55422038980c2103042e500810020461414101007900400c240c00040801d81381c8941e15410010f0040c0b06611041c0d400784500b0210500780d0340074240107040c80c0002054100c8250030400558084d40c8840405ca400d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 111573291 1250 111572041 111572059
    0x4120b090f1f0b0306010f031a061c0503071208010e070903030f0815030d0e040b091009020a110303040b16050307090605031503070807030317011401080712050f0106030f11030114 79
    0x4654003400a94043c080a10491f00b8182c110305100302c156501094a0383c4c41840d6506000c0365a581c0041181d0030060380d1090001c4965502c0c1c218254090280010640009100b03504003c81c3c1242402c0e0584101102e400010b68490130200c0d040000c034070000c1d001c80da00c0100c185510344503401e030329405081c1d955942c42400010010030f00e40f40040020a0001c0c041c02c0c00f038046031509000784c1170440c004541e1a1031a003031008552101d40c1540c41038440c5154009448640d0354024142d0f0505040301e01d058940381e1500f81007040e2100c000300c1b051040d0109a0f00115942070059054038010a01035407100e00351030405006940c1c07580054003501031207142140250781642c5c20402500a4040300010300f5540b880c1d407401520b018500d800e48810480c07020010702c04000584840c041c044005d191040700c0c1c1e00d50307980075a080c10500380c03825011428000bc001c028501f4804041c1203c0f81550100001c0380600107840480b10940b80000540d50200010041003104c492501ca00080003080784807 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 111574541 1250 111573291 111573311
    0x20901090806040b0a0c0c03090513090b0f0405060604050f13020a080304030503090f01050403030c08070f0209040501020c100606020a11061902070306110708040306020c070b04120b090f1f 83
    0xc900b00007124203e500810207030800c0f80301c40c1c40c2d000e80aa40211810105102a100c0e90003a000da882ca02800b40a00c0000c0d032400700156040d002500c001d80c11002d0200705061140c855a40904204c40c191a144a4180441c0803420f1a101c2c0d60711421032103220110545a00e0744031043c1d0a40300d10140da200d42403e4000ca020780c014401080114818001195160000018000e001e8999251503050281c03d102c1040425004044a0b80d0694001307011561408146001404108040d170082e4100700690108010040158000e000340c00c0c2180490381c100510f01491016500c40d4003a01c0c2c0141c00c508011400202c0e240300b2490381081c02070001e400c0c0fa49030052001c0035040c10855100680c45034004206200303140c03003210201505020190f07d41401c80d00d03060010f115521009000ca07a001031200708041c400c0c403880028200019180340e4581e0780d0f0311801d61302c0c001c0100036034404440c0d04c0400d40500d00005d1000c81d00c00d0b0307200a00032400c0080c0407051003c00c0e200c21354408036140d43c028a = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 111575791 1250 111574541 111574543
    0x70602060f0f1503280201031a090412030f021c0f05162303070903020114030903040e091c020102090a0801060e07030e28120f0905040b0d020303030c030109150311040209010908 78
    0x3028524141081172104240f80001001d8401141c20001c046080960040c0240c4580354950751240c3c01509040003550444800c03401440d03110f11140e0410700c0460004101341d612414611341c42e50350501030040c540007007440c80480d0f40a90340310800100d41c0e0349140402c0d008403031407081c000f14840f07111500f074402c023998209648100c400d20000380e6458070900441d0780010103d952146020861030070340c0342420b442a80e9204a00440f54400514000102d0070482041110100482d80e449000fa41d0000d200181c00f0790440f0f440a0b1250051080200e4404014400c48007220090f11800301c80341c4510505400801d01c1e1f117070000c020700400340207900ca5070344c003284071002403114012440301d0301b03040c10318110b620402c03c40001008203061001c694143c1c0315200c1000c1e22400c44d00004e0019042000401c08200036000a40500020003041020074100c3c0c0a1760403074690060612002d400100130565003805400010a80c0d0681101603841d4180342e406081e6816060500c0c8842c03135142c010903 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 111577041 1250 111575791 111575833
    0x605010b0903070812030f15040c08060411070302150a020702030f0d020d4d010225030801121b090504020a080105090312100e09070602060f0f1503 65
    0x9451648009100e41042c14100005001410500080c1c580c601c1d00d040700407051301c00034001400c81070149011551b0104203003440100c2c103038002d000f000170030601350015002d0001100e04038411403030052600d0f40120724000712800d15601d980901030310018030380c04005d000009441007500b503a09104410040c0ca00b00150708140352054001c02008202440082c41e10342e0540c004403c00c10900e0f1408029403a1542001910200c0180c1000001d0310600b9611071094000103030f91401280d00c0502d04103801075000740700031241401e1411010030042400002070505850040c00501d200004002c1d003059920010702e0288030b9800c90070b40b0004008400c00188094102810007961001440308501e03080d401d0030003c0000030000c1c0511321b0b081401c036480c2c1c042c101c0340010718030b9a030700092021021018904042c0501c900c1410042c209056180d6903402e00b4040c0c28050311424002c515202951040e03580300e416200c1c820700b6141c0d14203000c00e224003030208400e50103115400324854119030f00800 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 111578291 1250 111577041 111577049
    0x3070501140a111606080f0a091e030e0301020d0b01020c0904030e06210103060f0f050402060901030b01030b0315040201090e01080a02100c02150d0b0f0306370f0606020d0f0e01020a060501 83
    0x5207158908101c02c661f010800050400981c507481c003021140040c211280544840c2e061200340c101c1c08215017400e40303100924510035030b41544001002100e20701d40e540540315118081e13080354a00c120640503c07508000076a00900880c0e040c00d1090228680030005100c4100701e8407002c4243c080404031040f4003002a0000c9900546070102144030545071b00c190740408803a420140150704054000c184284214101941019101d03540807019074000e400407840b502000c0c048401c500611050a2485002940c0490000c0c007602000200b1075001c5c07052a0581d4008000780100c1d01d2254204489160403140300c50504c10544071034400740c0d85903404107401001703c46005580e80c401c41031510440d1084d8255500c05e0100c040040007070b440000316603600c51418004000301c030003464004000c100681c00302102c4001c0d01406191061455080100d0a0000c201c0074012551184016078440e9035100100c000240080b60311a00d151050000c0904c0d214180150740c0ca130724054031490260784090304 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 111579541 1250 111578291 111578297
    0x100e040c0f0e250806060a0302090310060515070b07052a01240f0504090206040b0304031d0418120905040905030c0d02160312090e040b040203070501140a111606 71
    0x1002031408008a40040c40f441d04924401070b10b12800c001340c9040e4002d45520f02a407004248025401d020b641283c201c1203000381107603161192620114003400e040d000700b0340120101e041c402d0400400801761032403590312110300b002980d40c0e80022110703a04810f140780c04809120140f0310f1507000700710044020905203400070884410501c0306408901c00740044e00101d2a000c4410010791410450400594208a4000c10321584034000220280155001194244070000074001055004035098060075403017040800120200003c0bc0111845032070502c01c05180e285019002920f10402c0380601081da0600704005501c0b100494111b40402c8004c540301d6100040c5070701d40c51070412002d118004544000d090300c00e02d0009041900516200080c8205196510345070f000e4000e0140e00042c2402044d03010984c40c1c1402c151031010380990b000c3e0300a001e410400309455207c0c0c407a15180009201456103401222101144c2d0a04240c0d010002401a00b800d000504000c906000060440fa5 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 111580791 1250 111579541 111579569
    0x90d060c110c01090b090108061201060e1e060604050f03100501120b0c04060c03050a02030702060708030105101418040b18070807090f0308030a140f0a14100e040c0f 73
    0x49460014140540b9050108650017000041115030450310200020302e000e00458032047d010440c15810b00c2c011520707550900e02c02048190500368164482d0105080075403880030800d80085070ba50b4256090b17904441c04000034451814206070303030084080042c0c1100d24001843c1160000c0b50b200f0303002650030880111400c02480060b01c0605d0b040f102108031207150910700080035101c0501010010b05001006c00c50103809402401a01da040b50043d02c0c0640c1d41240b840c0140307075a0b00034015144070b248603441c0c07950018810f200030305104111038115440d140c9107901e2110131011400ca629030258482c07004513100d4440e01442e68000c2c10591485ca03d500305904081c0441d20002d01150402840d458100700c02088810000201e98000090795030706c0c0c45801c0700344040c01d4070603801c5580902c410306000050350081820741c402e5803410030400c03d0b1014000600c0111030b040c0d0f10380352108003d10044c0115101004416040b510460440070815035409015424400316440703403540402003 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 111582041 1250 111580791 111580817
    0x3090305162118050d02060c1c200703030819091104060602061302010807030b1207080613020a0308130305160602010b011b030e0316080a1124090d060c 67
    0x403030b00200c640307406041c062640b1211403440c190f03404852040d5445054200c0700d500c2135440b10301c1250722103038484040e1040400d00070071200c07c2400c44c12212000800f190f15070300b40c0d0304441414151a104400280010918685003262206406061151000c550001c281c020344c0c154030420040910401161000c00c001340200403c89001c0d500100540d000b9008000b2002541c844c44da4190340c0c24208044541c581d410210018a00580c105070001000301c1c590b04040c0c8002503403c1200c11180c01c0700c0c86581c600000c088104d00a01c0d0013034000303800344820b00001d074020000c0e042039803807074074982e018543d40d440729440e00352084821441540c04620a11280da07080c040c0c08410386007801d00104200d00482184101211240c010b03003000900368000072166014400b40351601c041e140940050b940b05c030304a030740310004004200d442d0390b0742d24884a100e090030840351703000c6592073b6910261110105443c00e084d0380400090350b44800380c024401c0c0002c81a10400c0c007044c11599a10750400302d6 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 111583291 1250 111582041 111582083
    0xd14100b15030601121104050a260f0a032111040f05101e0c0c0603021b0a020f010c110d080403020913020f100c150b0a0b0412030309030516 62
    0x220300c60080d4090030010000302e030f6000408001003103480c0100007206c000703c030031002d0a4090794200c9a40840c248400081d05000d121480040d818410303c0060715151103551140e54603540e1100b060150441d0710303002c011901076140728071400780300800031070b00e50602d076004001c071510341800154508011805115070000304401c800540380aa13010441c034070181e04017900741d943c4041d40c0d4042c3d140340032040b20a039108543e041141e5070f00900f441451b40d102e00001e03000c1e41080c45200070965040d5810802c2c9180010207080381c0345c014019032003a19514004488005803c101554000059140c8111949840710340503e80d80c0503400264072103085104101c0c07c0000a0001d408000018101c100540d03901e11800c560b030300c4111a0250854607071b090968081c010144090a10882c103800c038000784986402401c96041c045a6a41030540c41d610405010b01440c0121015108c0760a0948000303030099000f040d0a038001d0900c241800c1d40805501c6402e4182e2400720303500e441c16000e00d05083c43e = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 111584541 1250 111583291 111583309
    0x3070b1015170a02210702060a0c0c21090e0c1306020105060f04050907050301050903030103021c0b070806120d090501030c0905060304120c0f03030b0310060e060d14100b 75
    0x81c2498084402440c44400390311200c806000a106580d0004d09580c8208581d208504d036003005019005580c641134034007030b417102c8007102c107011054144040000c40c01c0c495a0040c0105900100300303815a80d42c0d00b43c009401d4400d101c220706110404a001c12002c030018441445418800011941c1e034100d00c000e0580b280040c0c0c80700c0b05580c141000e02c0590b43d00c031b5402040c200d40541d1b0018140d9603522515107070648a900c0315070194600020320207450740105c01941a40e0007a510b04c6451000044e08440f50403e038031003e4001d00c140400f0601091207008030b2500103000411000d40b46101c0b0304006e051404862500b00072410382c02d42007003d0758060107403540c6000b142c1410000d0381d1410010880c00e100041c00100304d01c100c80000701e02240210341e01034202c2e070800e1110b82601c04a15016000b0805842500e2207032040e0700240e00c1161403805440c4c2a01d01c10801c086842e200d000034024410150001100c910124038008088140c0810101340700b00c0c603030038003c205540300c0f10520000d84 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 111585791 1250 111584541 111584579
    0x31309020903030318010b06120a0507020604080d0924090c080610050103020d060906120b01080a021e010c21080115050906030a0b030115080105060306090c1203070b10 74
    0x2500500111030955000310580c0c3d404807005065802c01c2040d028914010b0218000a961140000c260b4150030034001020901c50429000300b00030302d403280700060781d0352102103d0041075190100490181c0d00c21603004166005c7c0315605402e42050300f0401c0324140c0050405170007100c0d030340300c40010902003a14001c40c009c0140d00c001c0c10070350074070394102c1200c02d245003d014103054000540c086180401c0c1d00010050509460412025466a441c0c4a0b00c3c019070380c4c19141c0400701d1001140041d004100e0740c8155500030101c4440302040624416800d100d08000c5042c4507580040001083c10100c4100b00da04502012003420b910144d405401c4070f01c107030004042250200051b505c0d01d90410101e07507411508843c915165a1000d0907407015102c841822031300755003868500c2008010a090000545008200030711141c2c2e200402d259a44104072180c1d086540589040307290350505001c3c01c40c106503c10b0580b450034600340c0b1101042c040644100503c1d10a610080022548100e050140c42c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 111587041 1250 111585791 111585809
    0x4052e0204140415030804090c14041e06030536011a150301030f1106040f0906030204050106030209150f07052d03040b09040b0a080109061e0b030703080708090904050313 75
    0x418151b80300c0c1d034600d00450141ca00e001d80c0d201980c10800e405908095605040e0a030031070ba803241c0760f03070a030b1035210380300c180c034124400d1100d0000c2180c81c02070050602c9206000360b84001c1004002c901c000c8201c58040e52000002142c004000040c0301b80030b10703004170803540035900c0045140d00520030b40000941c2482250034007800103100240c1c0c80108504c400790020704128072139402c14000340d518401ca40c030082c2522000270001030440740540115040328000c8408100c580c1ea1103009030240d02ca00880756a101d00310364a0011940b62140141000c4202c0700600e81c1440f6a130380e201450310b45050b80c41310080450040c0125400040303441c0100c40070031540918145450300d4801d446034010041c080b4891a120b5a84619030b88517150054001c0c0100c0001340880a280d04101c00241109400750403c51289070f82060315400da4003e000305100d025004058003880c40c2c40b03412154024201c101c403400e800300b045e81c20964802e038215008078001c00c0a1a9511404884026040e0080d4804a25 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 111588291 1250 111587041 111587081
    0xf050108121e0306120607020d030b011d0d050c060c010b040605040209031b0d0f030806010801060207061d06160b0109050f0f01030308100e070e0301110304052e02041404 75
    0x40100b41c2002c003000d180c1c442e40241d03103946415001071002c01c499101220244101000c22080c04d0740002c92924030726054400b00105000080115a10030b40c050030249608d446101803500d03802c011449100c068001c03400e80300101ca05000143c125032100586d000e141c3e45070b01c880c00e40b074a07107481070800a14049508506d070035420008681c943c25504030f80031a000320f00d0b8411a050315001d4810b003140d036005900b50890701040c1b40241101d00240d0703099001410740000854018000030300b0b20305468064440b100d41003501500d00d029540c0f8020b03000e801c080184140303100080e1914043c003003039100d8030301140d175503051210303000484000600c0444030a8048007400020580c01d00310318192505440d28103402d03560950300030710752070381e0fa1b1000e0b007a440d241c0e080040e19a030200d07040010301d0003180240080c6c03004140310982d502090780c0181c913503008190040714065511290000e11100c1d20b152002c10710010b10818100c1e0401e500c1400b107481d443c50065130502e007600c15410307403e2a40301c16100c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 111589541 1250 111588291 111588307
    0x3090e01050901030b070201140709030605062d0d12020a2906010507050a0b0f01081207380406020706050c030411040b0315090a21050904090602040302040f05010812 73
    0xb800c0b50701848054004400900402c400510070f410540808150f02d0401442d401c003054028501c414901c400d0b02c4182c0342c0408640c5e94901107000541d0b011443c003040c1604190528940c0201c807503c3e00b40c80d4404002020840000c14601500d20500c0c501c0d009007038140c4030760a01703650410030741c042c080505120303110643e0a400c0c4012000c2c1c0149007032038015110021407070401e00c4e05040b0103000d0b0002c81d21504011304c0000c0c070300ca024144e5202d6030a80d103542903504100035480c01881300c003c001c2518500c07030744000b00024000c100c0380c0209218241803080391404080041009075815511142c000070a201407101c0c034002c50f9041038946440f02c7c503501d4551505c030724200303510395036034071490322004510a0b6940811448180382060f12003140743e42401c220b540d40d10078021804a61110500510f80c40c1c81081000b000c140c0455911141d1030714030740d4000c010007001c0515007140d98a50a010100158407240f168501064041500040650600640300e142404901032081000720810143c0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 111590791 1250 111589541 111589549
    0x301060801120c0b0904090803090c04060b0a1b020109030b010b0409150503031e0c01060b03061503041709130e010b0111060601050f0705030417031801020106031a07031e060303090e0105 82
    0x200c0f405022216150030400000501400050301c1c048c0107400f010040c0641d0820100319000c1d4048116010051503940340342410003401130310307010b402160501d10000030035528911404005441403504400e401c0e12641c1c0d44080a00a8000714403000002c00e00380f211030060f120321415604175023421141c0c1c131720303000001e6641d00c0b440404079502040301c0c10001c401c84060782a9078503100600004c2c800142c50b80c641c00c01c20341088410300d1003801038120307000710003c050703048a00441e0400c000b400800805040842d0740e500040041c3c2c0c0000442d41c040701010882c0c403a040400b41e140c0000f02e44011402d00040104081440000d89904500180002aa0800b0850300c8484501e04416101c8141e800e00300d066000f01d910400042c4c00701c590f0b01c0060b210100c0140502e017181d03a82c040d80045058012402c032100c07400b001313000111048100f0881251050a1035004030145070200e007403c10381c6080106403040c6c00102c1820740d01c40c00c081c01056000f402e0304016010504070a4510762402c8005 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 111592041 1250 111590791 111590813
    0x11401121e05030a05120a091205030408070515070e030d21020d02070303020306150a080c090303070f080c0f160306090219060903020a210201030f0b15030106080112 73
    0x144526a011a800481c00021040345074064022095035120380407500050540d070700044070170310b03901e00c084005100001d8900c10b50150ba031308140e01d6a08950040819950b42e4030140054030320880030700c254800a14104403050300c0080507440c00815047c011005400c06a40f04809071003a040003900400080d4009012621300d00307440d0560b941e4105000d050030081c402d1a00f60b14150340000781d03501c18140c040c0c001318021b220550740f03120800f5042c403110380140155400e43c4001030190001c901f55040110244c0440e040c010252483c01d016659804402181d24000716018840444c0c690000309040c400c102c898074a000113081880d6000541ca585540035002c0100130541e00c012920554880c0401d01c0f0003e89402408516a07844120190100541c0e100483c801c510401c00850b0a503a00030108000e108101240251104c0560040d4094030340002002a62070b9507115820300c030b079204900c07010030304142d00780c8aa49505003400200341401c140c000070400c155411801002842104032 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 111593291 1250 111592041 111592043
    0x1020304020907030b0d02030f010c0206011a0904200a0905040c020313030b04030c080313060c0e0d020f12011d0607030b0d0b0403051306050a0e012604050109050307050601060201140112 82
    0xc0c08040b100000c5e01d40001c6071b0380039406120f000b2140f150702c801540b1805418000f502100e00f60703070344c40740481d0300203410700e1940808100a02805000741000d42001c2445600c42d00c602d1310350407180c0c00c0a0107540001901c030001818030078082090381018851418040c80d40d20241d450214290344904001000e880014080c105100000f810315119614107415107601c0b20000e65a0b091820902e12080c03803a9000b61403c0340f07800a01d60115000e8822480d40510103407005021102e95000c2103842684082000d8003c0c92001d07105004035028131a83c1442810274101c00340c12401188110b2a000005010720241407030881c800d81c5607034400c0403c0a000d076006882482d503545030700d401c2b40c85002c3c9040b0900d080c16441d2000c9000c5d0780190241451904550760190540c1035a0011640702030341c102d240c5c40140100003624200041240440d60180c042e50000c216560540d4035513155a0000c2010784841d04414010f20240341d080c021a102c06006080c2c1e4080c550410100503507078118460 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 111594541 1250 111593291 111593297
    0x112030e0f0301021308190b13110909100f050c07020d030309121115010506090d0c08030424030e030a080601020a0c0801061706041509050a1401020a0305070201020304020907 77
    0x25010800341d681103880c0080e100050029901c5102d60810303500103c10500404440d401009000300c0c80001c88156100e88680003d031745042500c62203e2124080500e03002965482ca95030798610b01511a501414058010000202040100d1800c15004c0f2070494404c10080750500c000c0c40b640b6032504c0103031648581c040b5640026420315140550042014080061100300c3c203014026000e40c10009440340c402c08001603d181040b00400d04c0c2c01c4040074003c1660060007404a80c403039061807090f02001c0d512070b050461040d5103420700b20b03241d80c000c0d5100804410000000001b441021080c101042030700341401e101272081c0140054881c0942d02406e01040342140025420380e108000340340203d13811140011403152200c260342d01925141c0159810080c0c80340c1481581c5400040c8144200c3d00030302103da02d4a030080c40b00000d0854250191003612031a451180400e14140c40540c0c2102c05000060340c2e0b01040c1000360075100c00801503400d5900c140100720268890213103036544060549 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 111595791 1250 111594541 111594557
    0x1a07050a0b0c0d060b04030213090f0803100906080c0f0607050a03031104050d1109100608010e0c041503020405010207050d0b040212030c0a030905211510050d050102070b0a05011203 80
    0xb08000840c01802000c0c2c1c0c441e41000800240001060300038002c0e01e00949501c410345000710513440a54074041c0009044012114041c0c0c003103072500d8051038019110b00c180103801e5940f1401e810568002d0b0700124100d40184505080d0380c50001c4030300743d01c1d1805a580d181080450740b03c00d611903200d0380c0003405041d100c0c80c0280c0041c038500200c1c0c025100003071600c10520769504200c1c6a0a14a01c40380c0d000706036074000b090009400341c0000d23044416070380d903660407131f13007844121030912001904040345003400f03010209040c0c0444400d2030401d0450f5900685540c50300b0002803801c95954041405005040064008282c120802940c0315405480280300b000c818801145503201d20f008800c00350003581214400c160b40619a14101d51302203481580300a20742c4030381140c0c20a502100c0f43c0c0307a808600500c130342e49400c00c0105e91000c110245001e00c1942c60001c11040c100c1001e088800c0d0b5400102c0c1c1c1c0800c148101c00701c0d00705620303ca04012640c1409a141c1480c1184c20001d003c1c01521 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 111597041 1250 111595791 111595801
    0x100504090506130515090604060e0f1b0d060504031806140d020a09030c0906030b0f0606030708091f09140a200303090a03060615140406030b010210050906011a07050a0b 74
    0x1c05c040c038850103a03610085414601660895290901030741c2c100c0b204d0b03040801403050500000340311440520900c002c2d06038004964460110344d440605141c0c5c00908210994010440c14070074035100e94040d4a50650034070a52404488071203803508600e080c00242036800c2e10f40c0c441e01081d90385040303a00340010f903140c00c40c8905a035108503950009100300209500031910291035004041200d200754640440f50702e070865a130840741070884000d6001007003030000800355480303514200c1d0002224400e6070190028100401e032000c00c0b811807030759000c0d220380c1c1c01c0040108090098000715950405440002d00c030b5038520700e00002c0900c141948000a00b40c500e0943c0d02402181c000200003011400c40300c0d43ca18100002d8a01813080f0341415581c2201c21003214010030030070070f07402d0159850b1b91030181001000d50040c04000e5480e0704510840c0c01c1130041d60350510840740507554036801080307250700d00001195000120440e01c20702440510180002405c00140b07206100d501035529a01a514 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 111598291 1250 111597041 111597043
    0xd1401081f2913050a020c07050f09070507020d05030304050313080105060a05240301030f0b070203040321051903051005031f0c02030717040f0b0405090a0b0103020d141005040905061305 82
    0x70f40c4030103034000d8900390030300214100399401008400035110994460070f948030204900355041181c4940c0092032080001c102c18400c000a140b503d2001341411021401515103501e150400c5908844a43c0001540c20384030a00c4800c05005081c0140280824034041000c5030544126124030350007041c4c141944040781c0b2000540124031020b20598a84a603902c0c00c0008100f43d90141c140da4001c029000f05044c1071000c000c940030341e504103005c6130541d00d0303c3d01503002c684910340c05681005001e010100d15444c00320400110940607680200382c50414801c2030100c003c1903408284a40e001d00799540c0700c0890100e41c1d00d00580901c0c00002c01d4510002c0c10380c2980b049410046c20350340300340000c403000d6120380054815280c501d101817074065121014030fa0315101ea40076807503005081d40b00144900da9030784c001c603e10000601d001342c00c002c8542d8412040c1d8a03005001000103c46034101f0140c0070700c500d0080e0080034200d905008401580d00c1c0d40341c403880040c11042c1d040c04441100414408 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 111599541 1250 111598291 111598309
    0x408071709040908040e090f0d0f020a060c08040b1005010f050c0705060a02030a1b03091401021f06060305060402030408071b120602040e0a060b0a03020d1401081f29 73
    0x1c042c2007803141000900e4400000c0d4024000c0e104540d06060105202040c00500403a05205031402041000c068031000d66035144030300001c004500c03405a0400025605003d0109140301907180c00151741824035207410704030001842010310713001c01c0604200307aaa000c012a0386414590400541d00c07402c1900607824801182c00c0f0640101c0f0018405d44003550010040042c45490761300c2e0001c480300e6426000071480b0f040406030010f02004411b004031612800180e05041c0140120384240c7d010300540f007140c3d0075100e00400710a0380c85004102c03117600740c01640d511020031201140f8600d065030720304c4107070300480c000a0030010107000f5002c03451110000110142c6003c80c000c0c0c81c100b04c40e24000340a036200d03000b21000700a454000c110080100d001c0e841c01e0721140310940e8103241c05030340128000d4002a07000440182c440c50301c00349035000016190b0180000001600d451390f0980c185406005400e08041040e03443c12101c0c10141e01c0352071075500c0c903d100300e4070850005201d20000e16000 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 111600791 1250 111599541 111599557
    0x50705030c01060b03061207060203070602282304050a03060b011407150c0509090711030904021303020a0b0415030b0111060f06010e010c050717011103010b070309090504080717 78
    0x26191400104c4c0d500240c001840c03040704100c441d1400a00e0000d15641c444401e4421840541c6c81032080c3e00001d05984c010f0024036011103600088998249444001ca01c4529040c602052580781a81c0315800c0b0302401070b800450700b0008525240c9080003080c5c0c4c8006030f00c40a000036170b42c0d15072901c0d03684c0b140060302041d218054045880e84801d0800411103030010000c01005850050222a00703406030003645c1c2d00520062213183c0326510b812080d80c07a0a109690348045010402501c0e006503110b01c054010100500700780c500a90540c0b042c0083c50480b5088070121420505c000c1100d007049909000e40340c0c440c1e14000c5003240c01040141c446402d02c0c181a000c40c00741408004118506621701407044000b43c0c0c400180103a01c000544851214040141040e000690207000d41008500342c2d03c1030b00c80031400018000701d4204420803a400c203801c003101e4590006004024141d01440300b1002c0c0c580b401d4200301038107103030341c03004070902c01c061000b03003180701e00300110000e44c4003502690f40f00 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 111602041 1250 111600791 111600793
    0x2070f061e020123060f04090302030d150b0d020c0705190909021c05010c17100e0411030f03030f010902040e15010c080a0228031709010f02040609080f010509030a050705030c 77
    0xc1c00c4e914025001000100c0c0d003140100c0d40d09410001ea0315290043d640e6058064014600d030484071100000034000640e00b01c2c1000800c8500020040c04400c0185210b5040000040c1c0b65502029468200203050344024071030881a000810800704d900e282c0c0c022901c0204000607e10410710225420041545041e03840c1c032066007140040c040c041d0480580d85001d603481680640ea1000d40400c0c80ca025500d140d0700d4034140c102480408030070350000d07030024020381a0814420f0940c3c0040c0c50b000313601203034044640022081c00407070a01c01e903466001d0b00b80084150b040030304045040550328801485158114110681080113034007840c0d5503403070142c2200c0f00300d076201020781c800396668482070f40401e1a01541b942d1b44900b04854064890a113902d40d8840c400c43c5c01c8c01040119100028180340361035542c821444040c0d02942c0700a2001b07100071f4032009040d901d0701307581ea42094011a5030310780590500c4100400039101004440c0e40304502d0501586600003420968614083c18078080d2103 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 111603291 1250 111602041 111602081
    0xd0b0c0a032403060b0a060912020604090e01020a1107060c200301090803010501020c040203040b0606030712060801050610030e07051c0c0f03110607080f030a0f1b02070f061e0201 79
    0x410041c04075502030f01d01559040c8216815035040c03104200c4144620000904510010300c0119460881d000c0c01038001000c2c1c5061a442d41c0b0040101d0f03519108117402d980d0300050a00110f600b0007844803000d25207001034843d15251503030107880e24040c070000800c1000b0320070024255140500019241950141c000c1104c54980c0ca0042c02d07591003801118058401e44520b172102e46424022240326507801200b494164550f0002d1009a82000c2c104205012150030111680d149501c1130b000141918000462242412400e00c0501c0c071b0002c01d103a081504102c82d50350f041e403000400c1070407140113840c00301e0741c075208a100101a01d20398600400324800c48030006034503c008151441034901507405140940b4030310040000d80d1203102e1000f0000c4806100e59100829540c0255510524124020400e040f204c448007044441a84505418174204482014803690411040e0090701d842d0008020706801d16001602c58144031541c60032880d142d5508440b014400c0d00b02d4803c030002c4000c00c0300 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 111604541 1250 111603291 111603341
    0x703060b13090e0d0215070302090607060f05011a030711030f04090219020c010f030b0a0909050109060f0203090c09060402040801020a020d02010b0306071d0a05100e0306060d0b0c0a03 81
    0x1001d030a681c852106441d090071450000108081614092007005070000c01e81e01206115048400794020400f40038103600348030b0200c40e0303101c800040c0400c40c45207600003030704c02c0340103086401c80720181c100030b045040704011a032034180c1c0c24007200e07001147d900f400e0201c500f98001795841c501c40d20001140c200004600001c503810319070080d2003108130707080c449031110914407400c0781c0e10b0103100c0350b03540040c25a00c140301d0541c0c040d500400c0100340c00703020760410380d80b150300d104c050340c1e50340004580680d5128950014031103144108e4151210704030b019842c50401130082d540ea0a10010b21921910710100400c0103691968102c50040a06074000e6494800c4020041d4407001e0303600c1c0c002d01650816100c0b807001c0c1340204a9500c10119511540c904400e41304900c003800142c1005a40c0201c0500d5021400741d1700d80d02c07041c0e12043c13144d8910355520615010b00d420311801500c0c46000b0300100c0c44410003d28440d02d0aa8001081d00e481602c2c1c0341c40241c01c0303000d00034102c199803041c912004005 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 111605791 1250 111604541 111604567
    0x60a050613050a2c0c0c031602100c05030a0f0e0a0801050916080709050403021005010906061209020f0f0109030b01140108011e140a030b0f010f05030d170703060b 72
    0x11540c0843d4480c00c0301c2c1c4d403440659040c03820007000c0e0581c520040c0741c000050100b040415001408400e6103410f012106034420318660041104001415800411908500d0300709030b03107000d0411502c1c10044051044c2d640b2030340e80c003c11089106001e192403040c1c900754030032020300c907500c3ca0040c510418596243d62041c002c00060356400d00c28000c0031407820300d23001011804400c80703003c040104151458801c1540061001400032030031800b8100c02e90340002602c0c06854041c000110700050401d20b051400342c642c034000e200c22a89a070900c1c800380e0241c0d4411401070806001614a188505201c00048881c0101c5410040040b00010700204a0720740c09040ca40000d40280ca594406036250541e0010703c03081c60100410a00f6030907814000303460388100d003954011015020411040e1240d40704150480101e8000d404945241e004001d00811514240d000f81000d401410050748010b10060000104100030116440d00101182165129a101c10002c2401248403515003a02019003 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 111607041 1250 111605791 111605827
    0x3070c031103010b0904030509011409030d0f030b0f0609042403050d031d1905011e0b030123070e03100903030509070905190e030903010c0215090106060c0209060a0506 74
    0x1c14060340c84c140440400782804812140242d41603180c142c140860301004452002d66035105141d90038040c005542d003910200b0a841320341c1c82c41d480d60780c103a03000200010300700c03440300c0041841044c03611440342054442c48100d410145090390302084a6100c032000306c2146055081504980344000d40010602c40003250244244880e660140540c1821a602034050700030b115030f0200340c1d0800c4c00c03044000304018100842492141340042040159410000f10300301495030801d200a4440c001044140340a10540303d01c074030180c0d1072500000824195500d0340300028880e40c21f0041c0c003001e03c4503540d0108040d248900e0540810701a4a08918004005e040305442c034251502c10444045034002d024040c50b480340e45a1001e01e020201c40103010f001604100c001136510380820001c200e02074400f0300910001e41c0007600200701d0814a8042602b020744020900b0569900d44003044c40070b131747e110035100540e540440f078040490303c40600060580e8000d9104981c406400940059007400c00b09203 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 111608291 1250 111607041 111607073
    0x9120a0501060b040b0f0c010b030106080a03090801050f0c07050708030d0902040b0a0506031f03060c080403090803030c09040b0102031611040e010219050304050f030f04030c06030e0a0602090303070c03 89
    0xb40a0190703502000c20840c00340780035600c3c84680521041a0200e50789007d803e00703038610ba00220728030002c50042030848203150001505030304010700050038950080e01840c000c000c041d000300b100d8036046541e0350710310310050104285503100051240c00c1c818100041c01c0503008130390550782c0d81c09000d580e4000815078803d0403030180f802c0801007034071450600040c604890300030705154515900d514101c04801208030190310030280e10b40d008004600c0301d12a54040c40141d8456201a0138141070180800d19154440f801d2580301b001000349880e50407094a09140d400c1c1d60200d0002c951000507410340c059982645080c1895066400034808104298040d944050307030100540c48482e40070a080c2e02c02c01340002707100d506ca550000b00e000e110b00019940030340240c082c0c80c030f10842c04a034941103038000701343c464413850042000d0081c032031240c015500a100a090070840110094851900c403022024003030201d55007c644403582e038500748210381d1030303079400300c04074400c0703600da2070091020820421 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 111609541 1250 111608291 111608293
    0xc060302030a0f0c140d060b041503110c150604020c0118030e0102190b060307050a0611010f0c08060d030207090903030e071e03150605100e011106060109090f0209120a05 75
    0xc000768400948104500003604d6503c0501e00036000d003420480764060040155460b50300d403800515100810081c001a0440301100c0d016140c2d41a0014242c504011809940c0d8004100313000341d29000244808950303210002c014038540e030300c600041c0280a101500d40d0607500b001e441402001840d100e0850480c46601e0360b041c46c10300e0400480e500c200210b4001000401039880c40042202d40315200d42c071500080407288100e0710f4002052207440719038465004180a4101c0c828203207403e01500d04030030300d40c150800048a0908004041c084044d201754054804c074104041414400d10241d00942200441802560700c3c600e001001003044114000050064071400700301890450b1341881ca0030708038281400d1a40c1540c490640035401c04144805403a5204400100303511001914923040c000c0d61110201e407a034044c0098005040028021000d0300180100328281e0b805c444410f00390f42c0c20420001e9001440031298000f8450112a01d9100c0d8500c01819641507000640040d81c6202d00 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 111610791 1250 111609541 111609551
    0x20607110d08040204020906120106031103100501050c0c1c0b0114010906120e06011805100513020d0b06030a0c0207151d060904090c080d02060f011703070c060302030a 74
    0x500100c4458520503000d0400703800c0120700d410140d10031240c080e0440d000a000505d8114410002195903105400d107040b08800c4000400100341c0510480c5000001103c01070b186280c08401c803901c4049a00070241408400300d00c405074000b041101c44524140642400395161040e02c900540c24030740c0c1411150b1003071076400410107400944040c03043c400107840328158641050402d481c180711044803201010f50b1041c0001e0030b80380030030440b4001d00b0101d41103072050a1282260381034039070041030b100036829541010010354860704d61b4516064449600103807154188003511002d0810b01c140b15034840804000e101140f00c45030302c40c800f1012a60202d90a041d036032404040c0b4410030065201c0450120312516200d14401800d610407040c0003086d10b49400f4920740010f0071160003040603100d42c038040c035050001c42c1041200c2c0600300c000303000178012b62524001e02e41e21b501050060521030308200c01949047c0a0800a03506d400741d010103130014450f10707a44010000d420441c1c00482c514241 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 111612041 1250 111610791 111610801
    0x609040f151d150606090112020a18050103020304050c12010e1f0b0d0b130c0b07051b0402070b1b0405060d020a0e0a0303050d050907090906090c0b09130906110301150206 75
    0x3050a5680c030342441050041c1d0304d0008201c1160021038180e4140481c5c84041106510203100904091202c5c0c0c9590600c00b100810a110480c00b540226050510400910001c1840000c004012a1040b80c2c02c4904000350b4903c60301603c04000304903140e1041c014424001640003a000e102442040003c005c900302d06010032070b40b03001d1031030701629031041070000c1444c5003040014102d00a0207085a00c00851369240001d0581e03100384c10070345094010004c02007a1000d00d0810304400c3d0f03003c50f410b608280d5561540d590b030b0b0b1000303440789034205403500c0c083c25415151000e9030000c18004110a031106400b84446019501043ca44d1000600880f65071000303150001102017640d070141e6689080c02404c500c41c8005100140154a8510911760001495541c0d0300039015264030451020840c00388a180c1010300210540001c1e154160503c030302029621469106100800001c40106460906040480c01400c9001441040c0ea074000000b017140d02a1000c401e5a440c26030303007214001da0314 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 111613291 1250 111612041 111612043
    0x503070e040b100b04090507020c1e040c021b0d05010f050c040f060f080408031003050601090e070905010b07080a0e1e1e0618010e0303030f16170609040f151d 70
    0x450b004503502500144170501036000c0550005502c000d4074011200340912030300014245005400042107001c0041c0c21440070760409004180e17001403140010001d102121000581940a8940c100e0080340b035034012205004094022040380001c42c2410003050519101521441d80b040c010815410389400000500d1446444010b010111035590501142c41b90380d5440300300d034006070900700000184c00c4080040783e0103112003802480d0140c5e0014130f10300710b111124109807582d03200005003441c0200412a40c0c0b8403104039503107107502c80002d07a691200300005036080a036400881d03400010380342c0064440030181c8408003000300100d8441d200c01500955030042403000c40d440540125081c09240008046030344001d40200050605421201c404d02c08030f460b50300100d89034010185a4020300822404c1d682090f041c3e0003903440d0249100c1c40c1d06410342040900a010540124401c1c00040c040c401014040358a8030350042102c0d11001c031181f8004041c0c00410b82d54614041d88100800703502d54 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 111614541 1250 111613291 111613321
    0x150e010308030c0304050a05011a190b04060f02150103030e0a05040b1f020118080a110d0903031d21011d100504080f040303020601030c09060e0a090c0503070e040b 72
    0x584501c0407460b59441070f0b0002c1107078201820803515445030885031000101d00380190080400030080350a202000401000031007075941c1011600c0c81404a020702000c030143c0304641c1a201c0500700002071f901003240881c5800c0742154049001d800e108008801c0640c070070f020b12410702c1c0848441700c1007600d81c0c003000300f11030419036261b034424002000040c2d41034014403e01400780c80c3c1e0000140748000b40904036107240b4100d10407210f0401c002800404560403100b0094450003480051030171600c10350014121803200d000c098103004080c4018082c000204000701c0c21468041c00c0e1121046c05c41d19841c5c8100940481d0054039400d007181440c10b00d40c4c08114843e510032a800400e1071502100c03a0400501e00904156200c0104001c540c1c1500070210007040258400e0b4010f008562550502c03203800d00082d040680106c3c06c1c034104000d02121380d030b01c294003c1c030300d0400080e40740392900d014200740c2d0040c0d06c41a0580264840041d4103421130700ca251046006030500c0d41240d43e0002d200d46000 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 111615791 1250 111614541 111614543
    0x120405180906041407151707030605011706210d03060510021020040b03010602190210030c090e01090212090703120f03020c1204060e18060d080f030a150e0103 70
    0x281c0850b0010300416042c1c28900003000b00d00c03040c0e0301507a403900001204810462190030100761803a400c5040400d9818985a101440b49000c0104c6400c080008107040e003c1d0041140c82078100c00403c40b20784c0d03002881d04e803032080704c0000020300c0c40158405465241043c00c2c540403928105000929080c07035421012040c0503940580305021440c5a19001050811158484400700f40c034800c0960b400c090041c00540b0180f9a40394407907140000081c902a04040c0040c4c0c02598560708000503200c0010704514042c0c28200410350030802442200c0ca503000b90300c07000e6244490000010031884640c001c0c00c800c42c0d400b03150768180d82e82840c4141d03220f0b1144002071850010350380c40380c0c0840c8a0403500341104030304c0c51b001d858400d020300c90520f003803007051148030880c41c0020b0800007660046941c0c07030905415038075030807404000d100507118010002c1c4024001c1d4403000c00d0000300441d45046036000c00700c40c624141c490505444410040984240401c02c41e004803101151044500700340504072 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 111617041 1250 111615791 111615793
    0x3040e0702161a0a120f0603020306011a16150906051503070308040603020f040f090c080a0b030a08031e090d0e090f01060c140105040b04022805040b0f031204051809 73
    0x5611962440d64958030180c580c90400201081445c602c2c0c1141c081c0101961030201c01040305070450040605240c01a4400c500c10061580ca80c149201c1c03004c103135600e4142c041d280d0054a05c81d03051401d1240586810f840a0a00c3d00e1031400400c4480c1d07001d5800380704c80c01c0d150500d05451006140c1e540e901400041e0441b42c05000402c01c4502c00d0b001030041010060000e8106070380c40c140c96001d034003160014010540c4900d141812a43e004002541c070480d00b440c1440400c6096010030b848003440c0c003000e4411034000001030070141c06045c03241145000018403009900d0180f035060746645800c0c03078510005241381a421640d1401b070b46014058140191201d03403d9191103002d54a810a0400484400c40c02c2c20300c4407c41d400c01e00c10705100703c0c040c038000b07900391a02e441048000f00e100d4035100600c0c0481800c4081c4074425031440700564800303032000944003400d000013503042d40f00b070701000f645031144034502117500b43c2c1700b0050f10480750240c0c3c41c2144802d0074208644030000459036021a = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 111618291 1250 111617041 111617069
    0x5180102040315053412060b0901080606160c03020306090c1804051504210f050d1e0203040f03030b010309170d0e07060c050c060403022d0303040e070216 68
    0x814129486103070810201507070340c50107217807070303207441156a1081c0f07011010140c0c183c000c209842e03004402506601c403821020842e650a003140c4981e14040d40342c00904000b8a00d0000e600d90720380d00300316140980034159403000b03000e03503107010f5440c1030a50004a021f4060240400c403019000030340f480c8117650041231a03640000d00c003c0c400d6008802802039a00303100711042c00d014000240c0b10280510b00401c43c8440410008428200c1110344440c503000f0445034031494400982e0000c103440c120b4004407800b00790310140d1054440c03a9082219200c5040e4800800d10040007072184030400150b02ca602c0a00c5101c000d03d00660446070303051006404481d1005030b00026011140040440c004000d800107102401d80c0780c203030700d00000ca0300441c0110781151603440601c078041100380306c107003000c0b521145020300755804134826280801e080700e0b5441c40002a030340b0345034000c0256100c243c07001d011203868030f45e6042e218903104070540700f02000d03015030a44a0b0185203656039070b10544a0320090808 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 111619541 1250 111618291 111618323
    0x3090f0b25230a060f0506040c0206042409020303040605070302060109020405090f1306090302340b1b03120103020406090905060403120f0e06010504050f0f13020609040f051801020403 81
    0x42d2071a210440801e403070007584161400901240700744800d006002d000000d0901c0d00d58140801c4412440d4100c00350b51200c0d0130040001c044880b040448840c41802d00c202100782014000600540d8a00940c14040800c02080965101015104150180d402c507486070f680d81da9603200b280702c0e82c0289908103150740002a0b005d081c8191080d00048009080d0300202480d44a03d4100c0c1d151038422030058002e4000c50f241c03c1011000304600d0204c40004d480110480201c49020041c944a07400c90f11001042c058003001806070442030303641c0d40c5000d80e40e443d40d003040f040904920900040744150310700040030444058511030480d86c680d120004103016121600c0503524510084d0008079616210000c080c501006405841d0340c071681840100170b154101400c00c001d03900018108034142e4480e074200230490b8842209242c0100404441041501c0c0c240003065044c031405800c00d030041d040c800440e0000055500c0284140d02000520f24002030079210381b420f0f0b10540c88040c14015454000a0f = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 111620791 1250 111619541 111619583
    0x60f091b060d050f09060a0c1e0905030a06060801110a020a03032a050c010b01020d0c0305090411040e0402040c030213260105041a0105090c0301030f03090f0b25 71
    0x1100c8180c00070011414a50700b019842d06a0301c0807180b00c1d40300709030321060000100701000000d410000f01042071118080814005103e10b54203008000c4021303105050300d01090044d0100c1000d860050241e91180d0000d00382140a03090034400c20b80150b18080b050b409014103402601c51a0511354041c002405040d2011005490305443d104240c01c0f19820321108007a01540003d0303d00b083c1e4031030036102c02c1d052040500712442c0340d030b1880c1550490101c40a4550348180c490303480c0ca80c1814041e4036003800390702243c01082213054a00c10341d6030010300070940d4003146002a10462085905010700181e4020480c240d000791000c404120b031521100b448402d40d00701d18020700f80c0c0540c07103c00c0715030341303c000c1182901d0064805590308041d000c0390b400d02c0800901d0480c0940001d90348100740c2c6c18042c10140c004d00c0144070281030800310078091020113100e1000000204182190240d4150301c91410b9912541302c86841e4100c60f0fa00c003200c1086441d20307171014401641021a030300080c2d00c001009 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 111622041 1250 111620791 111620833
    0x6020309130e0f01020a0c03140304020306040f1a101701060e010501030902030c04051003020108010905010f09020a020c0315010602151b0f1c090b06030a050a1104060e09010905060f09 81
    0xd01c1c900d020300f502942d4a07880910103499696550f42e10203440e03044c94180a016a010000030f1903009008004101c050780340054815041a8404c481c2541404d0030b082403007580922231751100100108209010399140c0314449101a00e0310208060b900c01030b001c42d003d080ba0628800d10b5074103501c1000400542d8000e0388824104c0303002800ba42c4400110034009070480304100c0b40c560111282103820700079540c1c8246100c0c00b42c040000e0802065042005041600750644a00c2400301c0d000240e60f69031510a11000085840180494a2001552078146d101d48002d01800300144a13803106220030182e2998154020042c000e240050340880700c18614907507000080400e004842041820958004c040b441c1b00c1c050b10040001030f03e00d55516021801c040301034180c1c0d100368000c0f08171201080c00401c0c2c2060391b070b034890304080c42c840040010a028160941c0a0300780560b0100400401a07011b401160380c140c8200e003620250394540700c0b9450b078a0001c0d1604100b5a010406041c9040c0d10f079408 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 111623291 1250 111622041 111622061
    0x1305060906010809121b160b0d09020109031401050702060a02040509010b1308030a030509010c030902130515060a0503090706090303090603020304110904050c10030204050612061311130602030913 86
    0x40d1001c1320705c000380318502c540c020013250100008080081d050303a0b5040c4450306d01c0c0418041508002450503002c40542d02404020700803103a81c50080804580c01034030b41100441d800382400120070300681d4200c0c000c1c102222444003600442e800140c2a03080c80c03003120701341c074001404444140d0810b00310080e20342000313142e4409003015070301c080394800b0204083c103e030402640e00840c8a20386610039074251902903210713805150609400300c0c016512500c120307032082c3c0c42e0301c400150b03661200e19804010090402c6160400c10005070740b1051544000210701c0303407a40404545640e95150004ca49040280c4000b0300020b44000c01404540d100c0c0e0000d40e0414000ca003a1400c5202d480c001652200c030580e001c039141e07489103502101074200702c10380b070704000180d0500f14280340c9404013280c1030b0311a42c1002074034008080700084c515603801004ca80f01881020041108070391903400c07400b43d60310401d21101c0c00b04842d1000600d444c800811241500e4010b048400c48080803503040010b8405660 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 111624541 1250 111623291 111623293
    0x1006030b030309090f070215010608070f020a0213060609081b010c0c0518040203210906070c031506030b15060901050702370803180f0109090908091305060906010809 73
    0x5141039569084c0c022070061105181548080c01e007210080d1500181a00c03041c081c00c48440104007064000320201c0d13025215080c8102c010000c40000c074141210700400960040d02102900302011081d0720010540307205444101c070b600e4441100c00d9980061100070302c0e01c07283c4542c046405510449803441c40070700c81d95108403d540c0303420014213030507800030459010890f500104070070362908200c482040441101c5401032101008a418071611601c40346d42e010b0ad9000605008200d4842500d100441d00005082500465220448043c0c003c0d4401694903d1051010400703103c20024010132040000341114603100e401d000660301030704151402d0b03902c03030303604c4110342054103440600d0404100030043e1460314880d08180524006c029802903c426801805404041075000079070200241003110003d400d0b1041c0001264410041d4100a10f00c0e400c0c42d0050007048242401381280070401c4030042d1680017107800c0036003118004c07252a41e00c1040c681c040303000c07540680c0c0b0302c6400c142520 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 111625791 1250 111624541 111624547
    0x1101110414150d022115090703090c1505070501020c030304060b0603070207060309080708030901240b09150405030d0f0201050601030506010503040f02011e020601080f0604050d0807020106030c090b0a0e1006030b0303 95
    0x51310b807203040e0101b21011440701c05c000b041600359180c540b49055010b506410b08004080850715440003e80143c0a54080d0024184d20940c0350390040007903c260741d034020000d40d44c0d082d41000c0207443e608180c600301c2d806410000f602409203400000e4a1040011381e006140c40c0c1d180c040110060045804166280d40e0108621000700e01d014000b50b1281100c031001050598040c00b40c480d40d00e50070440b481c0350380310a10040c0b044420320b90403601c00e0201160049841080103040b100303548200d60105915100300303800c43c0d18040e0417081000c0000520340081215135a004015030959604a49241c0051410070005000680c2c03100041e80c058010704d000022054100912080c4958207004071001d40d00880040108480030080c8200503280d000180000b4203090303403401c0e03881c008201c0c0181880748100010394418802d6004ac401180c0215441045560f504507900041507621110b5006650340c0c08045601c01c00b03034680c00d00804c1d18410036078503649480d10840080004060480c0d15000070 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 111627041 1250 111625791 111625837
    0x8070807090308040b07030e0306060f0d0c1e080706210c03090c0b130b04050105070807110a0312030506010c050318060409060803190e0a090c1101110414150d02 71
    0xf0300030f0401340c045105440c4d9507143ca400d02901d01d40e64902d102e842a8860400c004580e00c41c0031119140c040180e411055040302d41c5041d800300402c03a004518411070481c40c0040039411b150b4510304403101c000039200d0664641d502110074280c0500c20341c5c408009844205044e0240b90f028880700c15a0b40360010b80d076085956050070220340c55008040030440405c050408036503d0819000600000c0d610f82d151074900400038006004a450161901c0404991181481105207504840321001030500350b1941d224680740901017808158500000c4c9050700040b82c650040601c00380711034000c00110b0403d00391a200040c0d02c030107120201c0e044081403000040300c04460203034401030f10362800595100c3c07550070802a14100404d108404000d0004030010b007a440e805000803d945071040c1c089286841a44191350a90708141c05e50320710762800008101a00c1f4800c09001550384251000000a031800100500700c1000e000e18181d0110801441c55044180d42c028101c481c500085d0f0b00b030000708 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 111628291 1250 111627041 111627053
    0x80c070b0a05150904020315041506090c0e0f0a30120806060a080609040204060b0a0903020901290c0a1203050108060a020c0606010e1302040914070906080708070903 73
    0x2059800d4a078050715403040c0080c002102221900b0701c030b81903a04696528160300000d0b92562051904501480b0103030100d410701a01905240620760003480a00500d5610a01180280700ea03541c200300050021001d030130940b4001012030f40b94000103060242036070401c892010721480080f003411203642c10400b5421381d51012442200c1c254024801d8000310708040001400c008801020310f44650401c01a41080c25001080030303030000d00c140c03401c0d00959103034401700e0010300c82030b007090004001c00706a2074841503220b00540103a80c0700350396009041c1d9030751034807401c41407421a81c00d086004420311140c4502001014001c182da17031300100c42448085849511240e0444800c40340066103410040c0101d110412010350040981d4404510300082d040b1101c2d1113103005400581041000c070b65400300c0d5680c203107140718410454101196280e940b46120310041051021003505000004d00142c0b850340036861243c12030780e050f140c0002c1c550b42e0308022580d401006056105200c4004000700c04514 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 111629541 1250 111628291 111628313
    0x1080f2703031603020a1209032105100504021c0e07030b0108150106020c060909040606030b1302010e0306040f0209040c0b040b0c010b041521050a05061902070b040201080c07 77
    0x120034405075503203060280507010204549a8100241401046600302c065400b5032036030b14000014100203842c5049280c115280001824115502c0e40382c21040d0320403113200c0d03111a0141c1001101509800da0f543c040c001640581081c1070045411504501074070501a04900d6503100000e0036550015181d41c1c0d038181c400c5083c0c21010f00c03070f40215103440c20030000c1c00c8a40e0151140c0d00040840100031f100041c04e510400b200240070b883d000300070604100e859005400990360110031040b540c03138000c52400c00ca03185c020080c0d001230042c61880455003804a4602d0060760044420340c580c00c2c05800744114404064021079108414400c00509001c142e006040940b008042c0c00f941c4560240781c3d0303400d49042100e4103200301d01d40500e20740007a602c401800d040761071181e4149410a900c80140c2001d5000702005000d03030040d140e03c841008800705806104035107036030003880001c02c43c5e603080c2c089005500005082080300e0000c5005580110441d03503001040d000d80034034005e04d569465950305 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 111630791 1250 111629541 111629611
    0x1401050a0b0706150b0c0706030e0a1205270109120c141804061a0f030d0f12060306050603011404171810020a0b06010302070314070204180807020109050d0201080f 72
    0x2c40802d40c080341d95418482c01f0000c1480e45828811402c803c2c0820703440310b5500e40700a001446183c8030300e00003406a81a00e41c0d420315074482d030380400d0170a060805c0750300812501c1070011b0f003000c3d03004c100702201508250580760840741d0180030b0342c00c106248041c81c6d44502e80c554413501011640030b080d141d0615581c403a611038040810503d00340071a40088440c2140c100b17215031840342240501d5140094841101e502502d46440d000d000c0c458195120000c0d080c03402d04540c1414004810f019487e0440c50144c041540200500301000b103101031090001e5900a00e40c080c000451410040e002d800351109003810b44507461b41030740d5100003503400501e41c503540c1c02581010002d6420301844803007070380e8010400c0c241940342c4035080d600140410020020309a031818041850303425500e49511809080c0800e20f000e0b2144502da0524511030303004110200d00080c03025002250905008166940050341a141d0103c19107500d483c3d21031104004000c24403000e48c28000c94904607065220385400 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 111632041 1250 111630791 111630809
    0x20307050d030909060b030c070b070e0d06060e01060f1b030504240e060a09030611070203010e10061401090501120915140903030f0c03041a0109020301050102011401050a0b070615 79
    0x2044c944030340c241c15900783ea0b01a607003c4409004000740208024104c0e2800381e4811407403d110717540d0043c2a540030b09080717402a0402080c000f8a01080740b541e00c1141902e400c100258503903aa103c10460f280d014040c41c4100140c00030400d00c4074401400c85000c00b84e03101e41412410103807900800c0c038201c0382000340340d189801842c0d81e51113480c0d0000e101d00525074050b40c542e8a00005a07030054040c0f06a0303c001449031707540301e03e00d10386081e0301360544007910350044c02481814440441c52b662614500019583c0324640782e000070742c0c4c103030f842164420341c0410384500750340f50300e00300054070403940320b1080c00030385511940718200043c1030841c0c1c990300c0030700071030300246010b000b011295450200034544402580100140080440d4002c1000c0d8088560303100269641e40364984410703d4006560030106200103238001003064800798001c2c3d07058810070b03070082000d42c01d14040325441d14001c3c03190303d41051241405000105108004080311400307480046066440701001325100c0b10f46034011110307 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 111633291 1250 111632041 111632057
    0x100606030b030724020102070b100e0106111f092f0901210201020a050105011d13030e0f0609031515030f0706080a09060e070303030507050f03040f020307050d03 71
    0x69150140728045803881d00b90018074403a401c0003c0150342102403400e0028200c10001c8600b8000e01c01d404881000c6d42c481245101400c00c1407608000c0c000900480041e0130b1440004114144120403944251160768010040262101c3c00ca0003030100d540d0211003050f441e542c02c200403c640c0c5840104000e2460811548030821207402070032080c80410041c0b0a504440040081c880c10031303401580580941c0e5602c0c4e82901501c0103074548100981c005105500305400010410a030180b40b50842c010b504501c14543e0720b0381c422001c000d0811100801103000e02d142264203040881d21701080c00c001509441c0f9041c01d600009140043e41412000701c02c2c0c0307920800c034400c51145041113241e64154001c0109140549030503494450500a5008100001001918041150b000310070300c0e41e040241000001c000800b02a1900f80398082074012a007400d0101c0c0000b881241121996100c6009660641d02c5540e03510b2078410345100c090b03a15100e050b20220300e55030380c00c0c44050001d1094440340c00e = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 111634541 1250 111633291 111633299
    0xb01030308070e0d020f06040e04060203070e0f0310052208090a080a1e06020d020f030402090f0108070e0402040219020d0210060506040501120e071508010e0402030309100509031006 80
    0x444000000c240b40200207480042d00381a89400003200072141c2d04440c90000a05000c0118469000365403180da08d481c810006e002c24031505078021400b54901c0c0d51003500324589201400f030544000d55405406510040000900407103613031040340c1000400400a401c2e41c140510b880c00c5804d0b00c141900c40e00b000240b204941c1c45d11503000340041c90182e01034034164400c1e4a845000340d804449820404003041110810440c42d0b50498840350f42c1500300f1134480c0c506424107801ca4100315002c0f401a000d00340030507130130348050301658102d0710300c10000c0c003c0350708001b0022030940018004981080d024001c11001c2c050084504406038840d6000713003081502054000d03d41400411041c800a18020707050205844050444098410a003408080418171040003c000d1010042c3c00036140184d240210380d90120000000725488240e50f03c40d00c0d030762030750610071a0000c00c0e58001c0d411740c82003080300d01d10b09011000a00364001402d001d07003071010500109040991407010061080e03600d01081c0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 111635791 1250 111634541 111634547
    0x90301060f050607080a0c0807111017060d03120f1e0501180207150929010e0f070c1707022e1110020f04031e08070f0c050d0b010303 59
    0x10008100c011001c0c41e1840c0b070500854041c3c8529000a0102d110004888585500070850031010991010055941d490641048c20901000600180c404c2c1c00380b400d4078803624454110045080106808620240c071603c0030082d030602c0441e0200c061190011103042074090912640b204a04040f8000c03030014503801e0751250140d0380da41003038802850034006200c1d03040c0412034080504149400103a4901940c1008203000140081680400b410107409908029039403580b0a101c880c20034240918a0000c0e0724074408079024001e890341650602c000031043c0030301d40c102507044903081c10610100b11650f2103085022034040c2601c068810001600380460422014001c6080803c103540e0100042c5a214100080f8085041c0410080000d61440034020140721b410344507041004110358441070614081c6440c0c20901c4155900d0350b041c02154002034260341e03402003096010288500d444079035601e05103a00c0c1d038103074103507201c80103108041031580368004200c80b018042c2c1d00d04405580340d86402 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 111637041 1250 111635791 111635801
    0x1020a0806121005060d060c1101060501020111251205180d02180a061805010512030a020d1209080a031b1b0b0406021905070309080601120b0603070806070203090301 73
    0x70341c0644030361441c0071058040480c007440c4521180001144a84034680002e07400d00c0ca65001400c3c81d480c0c004840e803000e0304900c0b00b9a003402500020f01c40d00d940c0300016822613280c100c2c21410b0141c00c0061012426044004540640180040c9144651700d529103003104414495030401141d000a007c0c100031480c00a0308106410850300a0450b034130650108050348800358040c2d42805002e004140003800540250014141880c2801c100d4050070000002130402032141034000d0000c600342681002c8040700310b48250100d60028040e60a0701da034110b404107021103220030800d80d1754001d40001608440140f0018100740d4003c81c0c28113070109094490050130a0359014050205c8112180400d607c000000d8541c000166440302c0c2c0c2e45007003440281c824a4111001e00c4000c840d01803019800c00301600e0014040c2d52000e4200b5110122259640401c3c051046414031811440300090381e80000c00385c1c40903010301503440b45540da403100b9181010660345813015800105500c03584d402d0074421 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 111638291 1250 111637041 111637051
    0x50409020f07050f0f012009062b0b01110307080306060705030910031409070f0501030e0f12040303020607030501051c0201050c060106031b080105090a02071a010303020d11161512050901020a08 85
    0x841c020003e1850b01c491f0b11707100311402c4900601001c13a04401d1643e034000350024601c5016143c075600700c0c060200c10700424000c204d0b1804a10203503d00c10384000004160751241d503002408601d16102c6808001003500807080c101d84a02c810422131289840d06080300d10402c0464801144d50500c142001c0c180e508024101002540080c408012107801030711020304582081c01c0002e4404104504a4185182140550524030a48010440321504040200700303c0340282d080e103100d600c1c3e10800320252902071180650204040300301240c01056003044815092050400b2444c10700d44a10080c20460240d00040200e07656030b403442500341e0f0310a540f8209141038508001c441d0306007000201c4401026000003130550f800b0071071030100101c01c40e101d895030900302501082503079a498020354504070900c4030000901e2910350300311455400a2000c200129402d4103c4c220350401d54083c1c9200481d2446904105c4000c00c0400010040d2140310302410b01030001580c1c910410760f004d0219000606 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 111639541 1250 111638291 111638321
    0x70906050616061806060f080f070602060f0c1c0504050c030d0507060b030f0319091203050702040c2a0501060e1e06010e04050f060a15050409020f07050f0f01 70
    0x11180284400002c1014281d521030000181c42560341c1030410b608107404e4000701450719090740400d56101240007002203866003801c40f00c002081c0d40d0a21744130119807090700301507400a404101910703a8520002e42c0b050103c48510700b44043c2a5001103039103581c0024011841c3d848040c00b00388203003404004c4040b00160001c046c6185400d1009003644116030010740000d550303c4d4001c0c0180d400340006070707454100e002180d071905404039034580786a2504240e400404c011071000951600c1c4038030111000b075010707102c41d810040d09400340405400050680700410490b101c403210050031900c1c51340103444030788940009105030381c40d0150840b0841e4004d15002c0041030204009018070300000040400d0307a00441d002c81e118100140c0e1203a802d5038540c0da1050030034040229100004403003600c01c01007200d0100d816a9280e114011404015a4040015a0400c814041100c0d0b54000700f200400616000f89000e105440c0c607410400800103145680d08034050210304100300740214040c41074555 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 111640791 1250 111639541 111639547
    0x50d0906050f060109090507050901081032090103031202090f1207050316080d050c03070506010605071e0203030901030e070b040324020310030f051011030703060b030903070204090507170709060506 87
    0x1a030280030b40c0214082141004041000280740d2103486a604000705603c060304140a2642030500083b102c80ba04070904040000c00f449605181400b000c40c101d0703400d52207800c10800c245209401035441181000d8100c4625440b07001c81d03840e000102c050801c02600500881403c120401d41008051b040b00c40304014400710611000301c011604120841c920f0421030740c0c440e440ca1401d41940101480641540075000002075980d40000c0140310140c4544541843d100d0f0f4072820180c0e038400e90380041d406034414881a001c95009034000c02c002c4844804032240301c2d075945a032241c2580550070440342c44e2054000708480860300680301d00e1100f681300d0203505500e85070010320a14501444064414049906030b8003d111013070011a50510820074240481e070f200302491242c81e842510400c0000c0c2c90700c20005070b50300414040d02e015600000c01b5503c3c0a00703d408000c05000764420a0314940226000001c0046031960191800048100070b400708a03e40070b860411500c8a0340010302600c810 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 111642041 1250 111640791 111640801
    0x20a0605090316050901050d020d050319090801090b0402220509030a02010c08090613110603040309230f150f0304030804050c150712020705100804061d0d050d0906050f0601090905 79
    0x3405da92415240705031200300f4070140034000034980c205135010180c524000010414003404608c0e4240d01d44026030344441c910a42d89041c0d46088500e007a40142010740044041001440d10301400420500d0114044003071000002003813086510903101c45036598800943c020b46290280103000c412503041c00c020016250441c1c940d910341c1002006a40c4134900060000c08114000c05d03004203500700500305580741d2a01d85005016250b89008217143d000100e0751006500110b0103c00b2001d03000503002007241118030b001d0015115840d07400c00f51201042c4481100c030303049580510710980c0a07988031010b50801c0d0a1041c101040607000b103000d07007038100c060b4550702c00aa049891b8198040e800c0c3ea260700b10114100d0030800d840e044207a216260291035494254080e418a02650064200708032406401000b0005040c100c003020086811010101d1100c0303005002400042000d4074010540c1c110f50341d50502199000c40300380d000c407013518081c4192541e00c400c008001d132100c00000c011600304 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 111643291 1250 111642041 111642049
    0x501090e01020c15040c0905070e04060f050a030318032a05090105010c150b030f010c02010f0b010f050a0509041e0509060903190207050d210519050304030507020a060509031605 78
    0x9041e0201030130300c2d140380c082030410080106000080c1072101040103182000c900040502d1030042d0703098802c0323050400124800b200b1860220032690001c00001b22180703151380a0310764091b0513408040702400c0000c0000410a44491321403400591500c540f283e003070190145004103a0707500128043d42802c1c0050003a640c11084200791720390000c00c0d00425000070400c440203810b040c1c5c2c5464050140040c001013840054201428401280d0000d000c12110340e10500101c031030546a02e800550800c154909550081b802020101070515055281020000c0868191a190884e90811100c0004011402c40d03452145036080100c07000548072508003044540d681e40144034036405580d8564650031640d90082140100405001e000710344203212500b40341300d4510941040c07520007a4091040303140030340715100700e4903821455602045101c5004408031803030b03000240200c090280400c800f101581d5041c0041004200d10391741c071f80d44e651124081c035042820f24418041032801c0301c041880300d541c03 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 111644541 1250 111643291 111643303
    0x40302030d0518061b010911032109012106031518030c020405060402121f060503010e01090510051e0a0603020403050309042301121b0e06100e130501090e01020c 71
    0x1412134040752a680c022111821006115400c200258640b07500082000380106045801035800c4042d1070541503030b41d010001144c002c0c200c040141c1010024485030b503000342e0003607880c1d5041d00307200320582075000c0e81c1c20f00b141e0707040c2c000342c3d10400015a4088180706a00030b070882c0045480c294041c00640f0381c1c0c0034041c41d00300030b0000d10440d03d0b00b00080a070b0312a07606440001140208104542c00c045002c00d603000f070040c5409035941c0e81e2020208816008804a9048030300050010140307a19016400c8001d0130044c090020300e48950200080550341c07422400c0965003403d10300d03583c400d00d01c010080c000506a100b40d042c94014017013000810004800c2d12001401a84d021825080705800c1846584954030000749282d00d090020442030900b034101c024861040ca03c8030004040300ba04a07501000500c03ca2006480c1140001e24030705050020704500002401c040800340c1c04000004d90340030401000840e2030313648100421558021b4002e00ca45004203a000b1860a007881061540f548 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 111645791 1250 111644541 111644587
    0x106090e1810091a090604030c111f02030a0e040e0c0402210405030301031e0804091505040e16050d03082a040905010302190602071505040f0803040302030d05 70
    0x74481125922100900c00e16141d950ba141c42001003684500d0008860a41402014076490945002400d161030001e45180110307010348a81d40361207034a641d0a1010030701500569044604590260f4070150301c01401085d889142e0040d43e00c2d417410400040c4038071200090513101e81e0802081a048280110b4190041c000503034001d40d84001200008508840300119104403003540c40800040c0107012015505803841499503114103600d01c0320099905a0102d40945155802c1008210402d415841907000050301000303005007a69800c0040c2c100c88281c4942c042907004880700b40c0c00f0200d401c030400301900c01101c6400c0c00c440c00c1d803001804074400500d10450700f041c440024803a030326464115460300185611321588e0341d07240c21281002d00002c2c071049006a8100007021341c05a035801510701a114654010114940781401804804180720b01c80700900804020220310070302c0d010710641c05880741600031035a591551060610b040200c2c01c090040000c03e0100000200c90782080782c00b11 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 111647041 1250 111645791 111645811
    0x3080a0507090b0c070e0117060f0408090f040e0f060105120f03030705030606070c060c020a09140a0c031404060603030f0f050a05130806040615081f0f0b0312040305060106090e 78
    0xa4510501342074904020b0b81c0000c102d1702180000090040c1c01d030304a2001c070b1020313402914015100c3c0d2850540843d0181e030300400c0c07860140310131005030a11030000440100020004141402043c8486040042040111410750080f000501c13260812044035881c030b0000f100100240900b04090340e0f203901000e045170003001701c0000401d18655401080e202e03000e41040d1150811907070780002038440545154100c0c0039510709000050650740074410b40769001032511842202e680d83e00007a030b0007001c2c0c030341d10700040c076a0396030000c1d07d41c06080f140c0038410340c42104006009400e600740a080c910003400038504000c41c0c50700594400d5880700c25a00d00008500b030064481821190303034121100c06130008002440b62104210074481c40d13030404841c18420551701461280ca40001507111211901026a0014103011010922090380e100c40b2600c0c40740400002c0920402c2c1c00039082030704d807102090800b0000305050007841028041c0d035004100c0340c108040350b145460f400c2020008010108005 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 111648291 1250 111647041 111647047
    0x607020d0c0510020f0705100e0904020301060b040311130c0c11030a060203070206060906150906031902040e0411040b150c1e0304080c03060f0c030c0f0d0903080a0507090b 76
    0x80042581c03050014100c0100301510040080e00003d50356100070013044610301c00c80c2c40015050501c04542c00031001269262080d4815107418400c0d00070014004a80540d650b000c00030b81c440701c0d000130304041c42c41045207a08891555080015030f10040c00c803000c0442c03a01c116007441c2034110001c00300440d849848004c2c8400040006801d1201341134004c2c00ba10b00000401c1400e030317408502544500e0701121b80741c1c03080c1c56100c140442460104030b0750220310300402c00e012080c5415006564415092a0f131014018550802e4106980141d030103030030884a1941800204903c480d600030940030151000c2069010500000304a1500ca8102c401169000500b0000c0080140195400c9010702d00c81c00e811001d0044820366207034014801e02007640a400c40071400b40c5808103010340900000d000c0f080040d16201542d896991025210052111040103101a0000060081d214241c11200009588072241c1405480d821005250040c014502010450721641001c600d5081c1d900400606407 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 111649541 1250 111648291 111648293
    0x10612111305210a0614090601060807030f0b060403030302070312020906030703050a02090a0e01050f0a0305060f09030d050a0504060b0402162405040f02031606090303050f040b0d09050c0f0607020d 87
    0x143c2ca80c1e581000b00b59401802d124200f40f003040c2c2c010001c10945c201240199560f4038110704d45030b00c0280140d8002609031000710300041e10a0b00000c07022603070f08000050131038204002425951080c0e20490200382c02040610915030008072407aa81e884502041d481c04150303400081e400d02c00107048000f4503542e20f0102e2003108507036041d20041440034101c80242c58a0f6441c2e1107031100248286407080b000111000340d64209103841d0402c0341d82c8100108a1a00c0c1d207180d8403491a002000c954413480306000b01d5031001507500400e4054210440d000030396080c01c2c10b00c8802e07142101000c9003e18010412412404440408000000c2e0084d04442c104103001d003042036204000c50b110320700281413205000030712000d5900c3c5800d1501c22401c683c00c00711102c460700c440400900c00c45000c00d04101040000c01c0c0540d0041400c424680c3d0300b24a40ba88400d4a10710075040845035031801551003d0900c108401000b0b42071740420101d9454445840c410001422480741384030082c001c89040300404 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 111650791 1250 111649541 111649579
    0x803090d1a0f0a1b0504051519030219050901020d08060f04020d0b0306070228020303070b01090b1008011a130b0c0a050c0f0607200405010612111305 66
    0x2102181c641100d6035100d00b0407022148600d9402e0351140810340c58900400c3e000450f003841008070103019150542802e1800d4200030a000e1000d4140a280804100240b04159140b20369a0703d003089440040e1207401c3c0700d44c00d203280018280e000c01800010000c4c60310507a00010551038113801440c2c82c504d6a03580340d020900303281034002216001400451002c00d04015908180e26185042d000c45031590760b140d1080340c0e9601482c8220800c4040c8540d035183c040d008490858000c0d00181c101d0b482c0c020541c1d9440ba0040d02640b004003002d546448241040ca85400c140c400d44e0315034540030002d0350400c0008030080500d5030550300071102c0050014203111603005c145004044900c01d15440d03100b40030f049078807500d0300c00342100e09014044403160035151000c21020180c0029018501706400380d41d80c0c84920b1a201d41c120070003201c000124055507140e01a460180000350703240c0404030480031081007030f0740d240280801d0808007404002c00c56040d0403918012204200e0721003c0010041d8044 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 111652041 1250 111650791 111650813
    0x30c1509031606052205060307110a0503030a050f0708011404020a0908070303020d1e1706011206061e020304230112090c031509120807022e05010f0803090d 69
    0x4a06400303460040001c0942e0024003a1040140b80d0300300395171049820320080c0703030503880d4054181d0062080c400f10704050b104110940e40516034a044030b10f070003180d846040c5140c0046400c050740e581c035a4100302d990313252400c4d09904844a410504820350400104e0500500c50364130090080b9404241e490015102e0000c000040940000307031407a96442e410020744660110000c1d0000c034440500010030408a01c002d62030b9a45560707200d000e403000a1025101d45200a0820383c10000d201c1c011401035500740c45090000d20654031094004d0701103802c0c2030f50a149145034241503401c188410451005070340c4001d5500c50f1840400010120302400503126503810007080b0100c54641440c103420030210440c2c43d415640203180360000c511207020004203841d81e03100c00805045c107100e01c1249c0f1070702520b07940341c02103040e0041c0c620390903a5420b541c03400075010458060b040b109a030701d2444481c0c181304480c05004152015540c0a0401030904da481c86101c0703030103024407400540708043c80080c41e00 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 111653291 1250 111652041 111652063
    0x1201051c0f08040503060c040b0a0f1e020106231f140a05030103021804030f080604020c030a050304110108011a0a120501081f0b01091406161a0105030c150903 70
    0x4241070705a05041000d0b041d08203008481c02849400081828050480c090300c0803100d03100c0364203140000b81c103800c481c0704035544694810b00020090349489960b88003420301c0b20308800d50000a11a240800c050803000c940305140031000e040151031503081e1114040e11000c0010038030040c0a080c0d00300012510f01070218440070401401084500c01541c1c40801541203d000702c4012000c22400c024882200c0c005980080109a0342c0d040300303170716900864019501c650007c000604109003c402c40e030031640941001d4000600010410040002c5019190600c45c0c080c6401d5180d98145075070350181c141d88a0041024120120f0031112242c40750143c0ce0210389414010301440d6500d58045c0c1c1d0746c1d1043c020000e402090b1400005c2c1c115442d11030b54055403016903800d40c16500e070901e0644000c9103410650781141081004c0d80d201003d00101082403807264a00e903002090310b2801a10081044e00500d01c00d8000081445059881c0010350200303050702d00401d9640c80340100000c0c601a5031040e = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 111654541 1250 111653291 111653303
    0xc0d110607030f080f0c09010f030902130b0a0b0c0622050106060804050d0f080a1808070c0f06080f0f06031c0f020709020c15040f0b01030b01031104021201051c 71
    0x7070000415600c80707120038151685840d1903100b610340ca842c900d0604003c44030300344400014040c2883e55803081c4e400b00c00c4200507003000544800c0b943c012540311201c191203a0185034540e49215200c0c00d20828101c0286103070700b4401c0c1801640c1d00b0f00b907220078000e1315160401811403508086c01466255074014540c0c480000c108181d600c4002401d151011201960240074100d03010388154020203200300320703c52a584860199980900003401000c800c1d2041a445c43c41c2d5050000285501c0004e101c00e40c028025001d680746400c10b04a002e1a0903080b40b410810401c3c18400d8100040e800a5001048496043c040c1d07510b100c0800d00e000381c010b4449100000c8003600f0900188c210400c01c0e4080b0342503080d5070315980c550098000761320650710501043c0d805540d400200c44104003c0a81241c410025810a485240c0f01c60b040c692003a00140c50f5651070a004008004082005003616a01580e080d4200030110404248502c41440380a003c3c40000400450300d0000c4110090030540c441 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 111655791 1250 111654541 111654547
    0x22107020c1003020c12030705073207031505060d1a060307050f0108040f05030910030b03010612031e1407050a0204060e0108030708090105040b0c0c010906050c0c0d1106 75
    0x88002960350700301000290103100110300100403a0f202e40200c5243e040d0120080544280d541d4556060340c0c8000d18107030400c48140000b000140808104e5102071280c0c0360303140b0b4400312007441c0c4120b0b104038124140c1264041c00e802c10001c1c54032061000801511507001580350780b03600111740f208040840042c503c1c0800e03010f5030f40070100804828000c9000750219001513440d031061048945010400781c0c041f500c0403000800040721b503591501d91510610650b03007031000b4039021898010a00a080e80800d8844901e1343c1c1ca428248220f400421a0382ca5142c1d0340c0000f510040c19030400c12100e052528035101c0c07440c014030f0154183c0c2d45440641000140d46442c64206162250f95681c0124032903401d100c8000f0b0303c039011490290590300c00342c1c040c501d80000d550f10f0081d95800706888034103100d0b042c40006048140307400680144450750001e0400c407801a00010407004480e00004140501070084c00e000342030004500c000b1680c1078440301480341c0e0302c0c02c05403825030f010445968030034400 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 111657041 1250 111655791 111655801
    0x81f090605090c040e07030207030203210709080c030c040203040602041a0a080a1803050702010915031a0a2601091a0103051515061806040b0408070b16020d031809061403010e0304090221 82
    0x375a104521840481d6205005c0c0742d00c82c00c0090311030100c455442ea040d030007904640114a443c0d402190000c0c481d110041c81d099694400404042c14520f402a180502140c2042a241c000d500a075000c05054010880411050f6101d00c200c00c1e80640030f0100080407903c0d41c211390081201c10040d01000d82240e1121510000050180a40c02108010b001628042544500303001241c10241c0d6455a12408400c07000c242d002000030b881c503118103c664a86030b0b03280100d088070814568405880142d943d05c4d41c1142080352400403903100842012580800f001030551400640d0400d4000031988903981d41b5181002265045200302c101c2ea100c880080e00280c1000404000d0080b550707050103840006644e51170307980e4540030304502c3d414100c1c8030903100d800619028560303001551080c00c01321904ca1640280080f000070a40144441941d114814003001d0300100e800954800c0441c0284914000114181c3c0c90303010328450307070444c1500403a002c2e54240c88240a0040d500900610781428901 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 111658291 1250 111657041 111657097
    0x30a1d180109020301060306090207020a050402070812090307020414060d03050c01110324090106080114130f1a06040501020a060f02091002060703050a1a01081f090605090c040e07030207030203 85
    0xe05c41c96002c08c1ca0454001806017290098506446e00103103900a031914020074003020b50700c5403034126079903501040b10741c0d002c40700180f002e805001084000e50300d03803c261040c48101c5510300311040241c0035040030000659070301c0c48100c1d21241d05180c4540c4450070160743c03034058526410200d142c85000310800400801c68019080058040c06801c2045003260b002e12240203000e0049000141001d001889640520503519a11240203040021000c041608a00481e6243d081c80c2c4000d984540d0301217400e83c0b1816101c002c01001f2280c417481c01c2e2a080000c5c1d902d5420680c0205481d4030340b2030408001703401d94152a110030000e4480320007034095990080d202d085c125501f0010174500000f00b00541990b00c030302901058217001c00c0700d15041c200010f5a000348001c00f2a0702d19500401c0c100210041811a00c0003000040000704d00345003884204420038400a00d802e80313054050004000b02410112503581110240c100165260b14038101282144901840512003883c89403d42490f01a = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 111659541 1250 111658291 111658297
    0x30803060d0206130611100e190804050a0314010b0307050d021c08040b1909030f0303150b18180601020a021e060304081c090203030a120b090106020303090609030a1d18010902 77
    0x840e0030595000b2420590294100c0b0751a402040c41640080c0700100845802c50704004274500442031103007429520400100090300d1030f0400c480309442088403c0050f80240920340e6094011000341410505100100c1c01c50000304102070f1041c0b42c245170b00d840100c1a5402c01d4040d541041300f05681c0d5031503c00c4d012036030344255142c11000801c0c000503c0071510a80c0884280e0764811082c0702d40a03682d8030105c1c0a01101440741110380080d003000030700780500000601002204c08210620121010104500390540d01c00380c20002e0300700b0f81000090303a400720350403c0d1a98110b07080c91848107004110304042031042d020326000f04000041c08188082440608500020300c1c442c0c000183c094a100415640400c40081d01940180f102d442068060ad0a071024549000b0000420740c2e034500001c1c405a00c203a0191002d03810000600039040c10900603140e02c451407800a605d001c00c2840020611502c111802e101c040d186116100a903403520791289102c5e0151514204650719041d00310f000354 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 111660791 1250 111659541 111659567
    0x2060d150f030f0308011d0106054e31050102130306180507060305090f0118050c12060609060f03010c0e0a051509060a020c03120304020415030803060d02061306 71
    0x502c407000009681f298095000801c0541300d01030280c580d01e8008240d404d5040308004800c0071071040c0622640c4040b080541c8001c0c5c0b042403010090b844020602e14148464101880485c411041040b5080ca4640b1580030b0324020640b101440c09030180c91a402c0503120703400108154000120043c070f035901d43c1c2911050300e0040d0420002c01640001c401110762141e0401007054000c68420400c4034025032205500000b44400d55406085c500c21841c2150307030000308040c40000c40716019040c01000c100e00b42001c20180d13800a02c21000e440c0030707a561075000b03100c24070603849040061941c3d100c014002c03252440141c004d0200b00e10300c803400ba1441d01100e9513140150020b410024482c82c04400a240705845081c00303c2c50b281001042c02804d610441030341066100d0200010b2030342c0c81c104001803007404041c00d185e0b12824240b04010948560002585406201d00f80c10b00216090000f00ca420100484408485040a2011541d24040c5001600240640717040000f110750304098000902 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 111662041 1250 111660791 111660797
    0x40501111c0506040b1002010207051606051b0705040905030a0e040c0509010311070b010e15040b0108071d03031b010b0414010e071403070f1101060302060d150f030f03 74
    0xa45041103608014003409840d20024100600c9400740c40d0101c1d404503030800c401420104105c02d00d600032840300c80d0390340321003401070307500156400900078240029190034091200f044240c5162410040481c06500c1580e80060790017155141d84075030030001c00e8010300b40a00148011209030074680d0702d030b412080500001ca010480040c42900c0c080c0719800310044561509414001c103d00118018418400d01d403076070070010046c1b1400b040d0b804041900904c2140c43c40340c40c914044210f05150002d200007680510f0622119240dc0c0e03030020b150b242c2c001903a140804002c082103955864a40c403941026401d40000903010742e61103940c03400307000c2c040c40d0f000081c13003104480424030085869070000810010b007850018810040d041014a4010f076641c50807107100034011081c0c80326548192140800300d00002811300c0301c9078010b500051100701c841c0081155900e10f80101e0324070302c507441091013600d5807401c8024540e0b54031100c01000e4008804004d40b07498a03442d2110200c00044420b5000c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 111663291 1250 111662041 111662051
    0x1d280c0512060301090309120807020301092303040b0406030209061c240305060103080a020319030b100f0f080a0609110301031a0106020d03020304060b0301092301020a080606070c08060a0203040501 87
    0x42c60074140200b000781980360b6242070a4500c1c008a002c0000da49030811241004100400c40140c0d074240100040f860040001c0e018101150030005d20840b500543e044142d0010f04c02085403c100b541074600712000d9040160b50b07004498001000c80c821803940e07a407002d80c840240c001050ba690305c6130b6021082c01c044c000c0d80a1000c000c848001c003aa200042944d8421001400028082030151000380c0c443c4c011a4200101d00d400140390480805608002aa4451005605141a00c1d540712030442a007451481c0581c1c40e40010300d002c910700102424803403c68080b4034030304490744c058001840c03000c004104280d1000601c0c5c0c1c01d44d10a01c415110101c802c1c0810300310a00100e81d00e8122281034005010003981c00c001170b8081e41000384140c3e10340740e0303686184021b80c1f82030150050044c400c03681001e00102d500300b00002d078203c9c2c00b2550010f07881401000e520503000100c84e41c2040d8200c1c1c403a6103070581413402c3d80500a4a8000049901442050001d095001d070041c5d40200d10031030003484 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 111664541 1250 111663291 111663301
    0x605060103020903070308090a050616120e010c060c09080304030b0906061002030304151509051807060c02010503190e071a0304030806060c15070203070b011d280c0512 74
    0x70590007400c071410f0f8150031408042002526110007050304a80103420230740142c0c2e031100001c0154010031a48507804809107030342c100700030000060a221078190304109030340043c008002800c11014003001046144c3c2d52140c006407600030802d000007862000c044030359031a1030f0301c0c0107819040150b44041d224810071012a00e1450000303101007485200d80d004508558842c0c0307035400b0000c4aaa80c9100450f9108000420750400d520104045e203a240c00200d89030400e0001200349945034401c00800342c11903101400781551000420b0207030790302441c0041d1251141552883d4000d48814841c0c2c00901d4881699011034000c80c0741022240240c81c0100381c4103143c1d000101910085034003c1c0098040c03070006401c0c1ca0800082c10740d581c81002100d031303c00209403414040600642e4040003503400410103c04010035081c41c40d0240c241051003803240301941d500e01c40c00c1d11019000c40076241c06d800c1080705c4804003a081583c52403001078180059112001d002d49103901903003110b8904501c80001035 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 111665791 1250 111664541 111664547
    0x5030f0a05060c16050d030e060f0f1303030b0a080601051018060804050a0b0106210e1b01110610030c060e0d080f0913020309070e04210908030c010906050601 70
    0x5511280c101c0050002c5a54400207184243e00040071080800c0040390118045a02005031140071612510001901200c030100d01c0d20b4840010701c903400c3c4403008010407030389101800d49070380c105149084d040c0b4440c0c1c2c1c524081e00a05001da0f07072030741c0250140c6400035080b0000240b80d03040b65400d8580c40c82c80b20f07242c1422034400c41d500581c4003c415003100100003c80c030032413200340d00c00e0207141502c04c18401580c82000a0500782e0191002510391704070180d5281c0340105401a00110608c00c111012405000644070301c1d840c8000505c5800078040000ca5074011840218028a901c003078440368a860408554100710031700040c0e503400c2034400080f411350301031030b1103220b00c0d18028442c00300c0c2d50003661031094079480410890b0111a09000c42071440d191b08096002402c1d11130805030300da1616820442c9490f0455002c07400000c0e00350140404034036110038500c3c1c08401440d8001c240181500c040d52500d420760303c044094400061b800300741d01c0c0c040d40200000f900c500803c0c889612090011 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 111667041 1250 111665791 111665803
    0x110303070308040f020105040302060703031d07030309050d020121020a0e09090a020d062405150f03040803090102120103060203070801080d0e0108040c0e0106020f010c03111204050705060a0905030f 87
    0x3004110101c003c200801c00784d00f41041e280384140b401d80d20b4035440740d01044050704141000c40100382c980c40490b02229441004240d040040701c01004260300d0754500500d04102481014090441c6100d00815640b282001448072048004582a5203104403100300c020350018840000050050003010400d140083d8400d020728072800040c49060215020800c0003281c240c01103807039a41d80d0103c0e6205810040342c00724019081d180014005242005000780d05040000301d40c0f0681080041c256034910b03600680380c00ca608041e140352641d40340c00c1d40e07500920485d06094500030100c03000008006054005521409407a0b543c1c01650740d0311504595900c0a03000e413900419800440303441554440c6904e242c0c050f00a8402da09402c0e40e41c6241d000800007a000500182c21180c24034056420900820905002c1482d0410409401c14000b600600400640790098030004000c507081c01010050b0030080c02c0c00801e102c1e030710000d418018104010511910780030703009450303210340d050034003140b4 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 111668291 1250 111667041 111667043
    0x60c11090f150102100c0c0c0e09030f1e0310140906100507060912020a0308011a0313060905060c0d1a13051015020102130506030709030201050306011b0b0411030307 73
    0x10381e41194075242d034108102203803000700c82d04610840180d0094039030240540c084164003920b0703104c5140c02c0341c03c00307800da840751390060b0007a03820240a1100800d0000211900000610085921040038248031038482c0308207800d01b40300302404020b200500620340d48840c200d5026820541c401d0344a4003d000c5a030204491007540105420b83e0720b09224040c1000b0508244500341c001905e42c01907490f221070701d8140d040c04005a00c180319400806400031f58207030141081c45070308603040d6500060110184001001c1200b2880000c1c2c440e4100301c03464005e2022240c1c0f181c20b40e0700f6480c8c0281c000c28a5000520a880c01900b0300c0d80c00304035140007221404032107a0180a4071002c04881d5091800f03448085c007030310895031941c01d00050b0309411440703284e400c1d2919400540e590207039049200600284e0b4200900c289002c1080c8515250048003040c116642804d002d40c0340e56481c00103075040701d1f07924600d1042000300f0b405201005006030410344903a100d2040001a801c1c403c040c03594034012000 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 111669541 1250 111668291 111668311
    0xd0b0a06050a120203060f06010c06050a0501151e05130323070b0f0f031f061206090b01050307030c0e041a090108031608030603390613180b030106060c1109 69
    0x1c0401e242c5030354847d24230340c012011704040b00d01e80c401c1d64603034080f1001240c5c5850695920070060019019001082c01c60019a01e01042000185c0d00d540c240e80e000e07084900705028000a03051034100140764980e00031a001010100a0104401d40398081c0d000983d18880f14041c010011400160403010748161100d00e403895030074800281c1e500300b99540050108000912140442003031a415404200c001d4441c0b59a510b445039007111201040d41c01d180c00c4400729a083c8022599107983c01000c0d87d5000c4018038002c2b0361341410000a895000895840c1e94100781000407500034509a1000c11040040980d05d1110076a42c032401c054480c020b0301320201182c1203908100001c00c580101554000c407004007580d424481d80d02000c030111310102d03e0420105d03e00003260340000128001645034440595a01307190150041c8a405940401c0c000d00009400c43c5a801c1d030498a07550207c182102c0180003000155150030014200c40c0600b501142e825460461031040c50800170329540c040c101c011 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 111670791 1250 111669541 111669553
    0x70905010c05100c0c03031425270611070e04030507030203040504090f02041a0105030c30040b131a06010c060504080c0705010e06070605060d0b0a06050a120203 71
    0x1100459154026640c241c07581d103e9681d09582201d1244114810074405403100d4102d4005031a000c2e058580c0040c5081c4001015810003003441c1c2030120701b42c0d6091001c1540b02d8041e8000030143c0c3c4009000c41604404540c150210f500002e540d0b12441c246d030501d4540e4108103c3d1100311503a107080343d001c2d40c4a8031600c100450002130107a0060132410303220b40103136803c4c551500042022180781c1d281c00d645404001d450642542003500c2003c290303803c0180c5d034400d04000707000042c3c40d0344000b0702310829a0b000094034080d4003c1d8081d02c0420000f500c038400c0c42503c100114a00001800c0e01c064803800c81c4039010802012641c41780c144e00b15400300ba0070000180108000c8010100148007a0601c0829002540000ca0300c0c030400f4419840394070b000340c8444114030380d07524100040e0456410700c800c0d11107100540d903440042d5040c55a100f4000300305641c5840c0410b2100745000c03002000032030034034184401d400b07803a00010305480e025580c07039141c1555060000c0c0c1042c0342c2d05029400d50044 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 111672041 1250 111670791 111670799
    0xc091401120f0311030f04060909050603070e0a110c0307030f11070302130f05040c0608150a0b030a0204030f061b0c0b1602190b01051005070510020903190501050603060c030709 78
    0x10400c45010b103009051620ba400408410300c0d0035a840800141d05c0c00b48002401d021640d000f480d036901410801d14100000e280410120340e6500d03030740c061110454100030000e41645246d4000c601040702c070b10b1050307840f8145501d029980740c0003c0000c40104400300c50189801d0310501c5000391103100c00e00100700030f44c595000e210000c00d41001004669494140c804940000e43c014640540e1182030040383e200c2c41d2503001011888080c190044400c03070b000b505000c65880001c0d800984040021103692511510300c0c45009110b5640000c200f20300c00d0b8043c00900115900c90070b80124402e00d030b51507203100b00b01d04030740c0d4990b24403004110b243c941000c6151172486403c4d4400402c00d0340100da03030300b0501e0200344415030f40041d81120b0715404100140100c3c01d0082440000c481c81c0d00345581844150b60340e00d41c540500d014034014441c3d010660003000d41d070400003002e261040c0784e0204980c45940c20400d02a090480f1424024428040801c0d540038031402281d208256a0b640d524901e814 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 111673291 1250 111672041 111672053
    0x2010212032205030915040b04030602130302042d1103070e010c0b090a17031003080a0504050904230c101d03070e060102060903070302030304021005070b040c09140112 74
    0x2500c50642010560b2000581031940c070244400d40303016000864486100d241001401c40d0b800d481075004100500c810042c00c1c5201c1d0594055942c4081c0150305c6180030009240c0c00119580301030343c0a810580d2401620340e4041a0320b4403a02c080c26004000048403800100f43d4040300160003500e0700400002d004240f0901c2c66a01e0440b0524005516005949801c007413400b00355207400658110803a41c81c00c11400745510002c022a03603000d241140307850030800c800021944006003264000050f80341c00148685c2c1106c02070400100640110309082c100007003000300081040c40d000c5801030040d010a030000800a881c103400030420481c2c10481c6d1011034040070604141e03d00254200d09155031030340c00b0701a400c0940550034200207145080030009107045000307803040429401c10848240866804021a5885038050307425006410900b04200c4551046200240100d140e020a1000304800348000700d0441c0e240c048140004004900d2950010f5001e02c40d940ca0004498040e40010302e03 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 111674541 1250 111673291 111673297
    0x1b0307030303111911070806090d0c140102040906030606081b10210213050604030c09050606071b030201020606060903030319090b070905091003030f230c011e050402010212 76
    0x1083d00d1106090104480960303191000e24460200810307031020504e0342582c0c04000400080500100804540c20303c4c828290304c48550040c11010844c0c1140b01c1400e20500820440149000000840d51241c0d00c00410008150900044a600303052200c00100c031103001031001042c0d80c010003031024900c1c0312030402c07054540c007141c01c000303206c0a20104407030901d5402404031254401d820140e41d542ca800e000300e0240d034040d0401031164006000c240b0200f40c1d6032104405480c0319010004450301d514000030024060001d000b4400b01c44601103042d00349650034000d045038801e0302164102c0c0c440c0801c2080394000c00d41c4c1c1c036405600510005401c030b4034496503c1040b020b490340000308030790103840b680094001228141c000c0360003503c0401003030074102c5110358000c0342c3d0701c0e62104203425079400605401c41d5115010400c0b0100044c0d011181c8c204050801c1d10f40e02c140c1860f40c40f590030f10750074003911806000e02400d0a0251454070002064000d4501c110b0781640540b01e070101c66899802650 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 111675791 1250 111674541 111674561
    0xa0207060305092a06120609061203180406030b0c0705060a020301060e09040f2306151c1a070f0206010906080303071407020d0c03140c010e06071502030a0506031b0307030303 77
    0x1400713890b424410ba8850000904904070100b40b10034191400350b02380201d010000d07162501444990301d001041d001f010081c0d60390741e1011408071114580101c0014080c0c070060300302410302e070100402d10200403000350040960504c207109849280c0c0e5080666400c0740002d02c03c290100d500e20741081600d24024602650051040c0100042890340c3e0700c500784006541c001d2880540c40420303078040e07103600401c0134030313030020700c00554175004041d12000c5820b0b000304d41d0700c0d1181907104c101294100490122241d45000800d080d5003001d2801070307002841e0340c480414460160147d2000807403001c905000f035400f6901002e004519640340c0038802c4441c1c10f408074594034015420f12013440180c1d281403182038050b00442c881800503085080140c00032034080000c0c8030030380c00181da11241d42d8015000181c0090121099520b584483c10540d80501289402400c0988000100820042b0541c4064010071040d0101c0c0c0032015842900000010b00c13648e0740e980355004840030400030b8480e410a480d0742c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 111677041 1250 111675791 111675853
    0x11101020c0d02010c17040812041a151804081801180902120109020304050a080a020a0803040f11061201090506040204211103070f0e0a0207050f030a020706030509 72
    0x10160140d1601d04242d0882c0d00d4000603511103034a10025580490081048600c1c41c080c0c80541c1440c1e940c03002244104000458040c01010000c1c01f1b2041582d040ea4600001c0c101c0712889203801d80c040001034100d082440e05c100c4148050039942c1d44403141c05880b070360f80f01c6140ca140c111070414441e120128504001d0410044001c1700001004040760003004001c100005038a644070011a448001c90503000750030762520520405c004582c000032040140c07134215903920b55400f60060308034280108500080c0c000407001060104100c02d090840880d2401120029088149801000b0301442600f4a0680300b00814005100100c0682d002030f4000c807004200503d0030781d8031011600e44071007420503481c910464040c42814064600c1400008080840142580703508100d0138400c0111a406050a0141d1200003d0504c07092903040350720241e005011204111500c840190341d0742d100c090110300501503600c000455078028002c103801882100c0142107211034115900ca4038841c03801181c014 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 111678291 1250 111677041 111677047
    0xb130e0c0303041706071d040b0102030d1e0606050a081519080d0801150c0b04020a09090c03060c0f17060102150114040e0601050d0b09010209100c060e0c090601110102 74
    0x4140c0e401c000410040218110300f111140c5610300c00c904102009161b00d0601280d00349414083c41c000d0841c1040410440340019120700d0000103e10303502409481c00841480d02448482e051030903908520741c0c16030800c06218481d203a0004541600600724140c2c003081c8080d02096200700c030082c030001d00941c05000040502900c003c2c5801152003030b03002c0c0318550004c42100a9143d4000c1d541405004406030001480e035440d0b000800030142ca20016000c020304501207030440d070b5000803202c028a4102c609119240003030030f0070030b2031501c948030445c3c10f585001e614018550041d0b8131220780000341d0321141d500000201000e44031020003031200303045005204d45082c04100c402c1c0c5e258003034001d0650308039041c12031409000031a199140760307c100d9400700c4010420b41d03480070546146542e018500e030800d03445550250780a0b004a244039a40040800001080650301011445000b4000c00b0b081c0107514115000385c0e250050300340104d81211013403002031459401025188d2001420200044ca = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 111679541 1250 111678291 111678313
    0x4050f01021801020c0a033201090503030601090905040c03020d032f15040c15020709110915120406020a02030c16050411120106030b0402040302062b0b130e 69
    0x20072030788001d652000c1d11400c04210307011940d040204502d01c01c426210f0000003400c54807000c5000070030b000b05a2001900041110509840c1d00943c0c0c0340c604814002e12445210b4075049440b600100c0c0d002d8005008840005400300c0d45000d040e0141da0803892161903281950280301c40e04600c4201036050019004000d81924808503024408110304241c40c000600d0b420142400c01540e10495043d0074861400d0101044079180020300302c035100800740c0342c1d080000ba81642088001c0d8000f401240c40c1501c0f041c40c5584010090845003002c5038000400e200407005440e6601075940e047d9101400c00000500007215a8002d2442412900440b0b06203814010464545140d440c11040c00d005001800c210f41e0409018100d03002480075074031420311000302d00c1e80d03000340c034140b14960400d9142e00400070a42c50b0f9a04072005142c002c2c110720790f0303003444c0e5011030400f19032949001d0707105850002c0808030421600c15201c80c60341c020f080b600050030208a19000d01181c02c208012030244680e465 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 111680791 1250 111679541 111679543
    0x1050d18050a12050f18010207030c08060105030601050a081005150a0807050f010906020a03050304031e1806180b0c0c1008070905040c08010302100905031006050a0b12010b0304050f 80
    0x600081c0c8110001d000c2980545000031040d5014007004043c020300b404050280510301040e0b1345410650740c0c80361181101000100c0c50032005504c09840003079000e50103d010301000c070b03e99043e200c0c16802c480c916641c070740c14000030045034810b002e115000082041410102600010f0304940c000307128030a081d01c03190000f540c112980d40701452590200d00308012505003100c1041e141030003400d003000e115103010006500e8040b8140000e040245c000000ba040600801e440c40440940d1400340740c604400910142940c1c6890400240202c00c044001072900d00c102441200501c490320059900d0349131650b03450090300301da03009282a015002c091011a01c400300802c5a542080d503c4030b0076030406034005005211940c0145000d2030038012007948041d01700d084541103070b50581e460014a00e80c0d00c011241508140c02ca43e40c94091311007181c00c601c015400050651b0b2040300d1400030a0380d654050b103410710078481c0c2040c05007034a5004000701c03c000ca007d198410302410580d074420800d074440c1 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 111682041 1250 111680791 111680831
    0xe010f0f181401020129090405010e010501150806040c09050409050f120a110a02100804060b09011401110102031302010c0305130608041a041a090a1509120c08070201050d 75
    0xa408000c1224200e42e8a540e4240900c556010501d02c21400715820400074400044004d100d150280821002103810418250b024071003882c540c2c0e00030005540c441194104072004035030010009080c00e8003050341c0c2c0c40c003441f0b15150f42030b00c0d0322a00030aa01d043c040c080580703500001a119401220880780700325400740150a0a03041c0d40001d070341eaa41070880054a42d002082c01803285500840c400130040e20b40a082560080c1c19082c5249246c2c0c6610340360b00034010044041d40c2081d18140002440201c405095610300700c240c0382c140b285030180c14914201d0204817501c4582480d020850000755001d201c10b05030040c001c2c9803280c80c3ca46486002c0140103030a40c801030014140300e04000c284072090340310303030f0551006c80c0201405041c141c481c00511004510521084a80c4801060401ca010452002c200d50312460b0358500d00b80341244d0074020302ca1003005840c064010040e841689109801401d609a80100968206900d540046a25400200e1000c020607907400740d82d800c60400940c1 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 111683291 1250 111682041 111682049
    0x3030c060601030606090f0605130b16020310020915090114040b04090617031c02040f0608090609010b0102060f1b0705030705071a0403080706090b041a070e010f0f18 73
    0x2400c50341001c0c8001002c4642c10391000b801c01805c3c41c0140b055110701104002103075801c2c5801c54440c2110a17100441c410a64401032040c100042c1006010b03960260b002c102c54001c4040e02c3da0690414450005d80c0304140801e540680c108020780d14840100d4007174503139442e0625001c0740290801e501c1d13102c1350780550081d00409a0106041140510782c0c0115030180030f514401108007580940805d6807130081001c07100c91108440030420b0309016541c1900d0007003070007512500145959500140c28150242e52101e054014440041e0751580140910160240180d0091002d9900e1084101c0c0301c2401400c0040c40c45100010310b8010040d003006408010b0052001e166076007403502c7c00764509181a070040d803940c03020800e880003549110003500c048913001500c2c50f58130441858804018007419000604404000e800e0001340500821840d9a6034500050340da007075103819a054504000740311245002a808d0f4002c040450f100c0c040d1440b03c0341450030403028180da8605644858003032a08 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 111684541 1250 111683291 111683293
    0x1050c19050f0d09141309060213030201030e030903030f1b2b020c01120b04020c0102070c081014060f0d02100809010f0b060f0c240609010602010c0207030605130203030c 75
    0x444802c012205214103c030244042c1001d016092811041140c02040159039900c00c0e070310403402404040007038000606c1e079035124100710358900c10280a0800c5070702500090740024a880000d030f540031800001c0b50a0454001c2c001d60030090182d000d04070b1a0703c05985ea0100d41c0c80310580c40408041007103010101c40f004585401c0c01c0003045504503030602e90350800d04c11944100d8003d4580d03600300000c440510311880c1c0121301d1803820380101d4060312800071810841c4d07100080c00e40c1400b041c4041501a01d0245090b200144007004840090b01d98400100c3c00e8510b411021030f03410328003100d0003c8900700242c44210710703c1309030700014042a1308207540701c0410502010086440c0d420310444151440c00081001018000008607860f40a03a40780400e503207000042a000c0e0302c50801242d0b09040349110745046200165a40c941c0c0030005540c80c5008030310000001ca0303042e006014620a491495009200341890b41d20707000050b21024111070202d0741c2444421026072001c0c07006020003e1148 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 111685791 1250 111684541 111684553
    0x6020106031502091e04060e01091505030312070c020f0904030c020a0515072a03050c0901060815090601030b040c0c0b0f01121b050607050105040605010e0c070201050c1905 76
    0x70a100c50828840d2000e426024810009a902950782d1100114100c1d205003014001c8171021003c200180303481d13004040106144c1000064400d80b6401c0101c0b400b03c540d0648606654540515650f07005002d0000400c0030301100054000340b040311206061800140040d084140c410085000c500c000e6a0a034006040300d0120070650405452030001400f0035500101040710060049515005010001b4500c00c40321070704000044d1500300b01400140f500c10b070030b50600d5a91502036a602c00280126004030a004000500300f03000c6c200300380c850a036101c00f40140124600030420248030040410b0b060642d00c0c0e1500406e0303101c6104214403a50300e40ca4106c1000c0b0f4074101a075455000411101100d60048014002d0010310840b02c91069401001000381c070181014400407018030386c224640000e004900003044c030105400c4940220b0081e401040944d0300e446010b080000115401c00c080344041080c00e005520410042800b8480b11003500e024010342e00191140b2055a0416201540a0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 111687041 1250 111685791 111685793
    0x1180605090f2b020a030b09070303021209060405060c15070c1109040302030a05130810050a050a0507050a120b0402190206070c0510050606070b07030f1104050a0509070c0803010602010603 83
    0xc00c91075001e4000407100644102c1c4811040071140250041c00c107141c1c10590101821901c85e130560002035540a102800c2c146090034004c3d540d001207100640c0148107020868002e03950081c11658100d02c0900690701d454200414003840d0fa1100b5a103101512038810040020740310700c841280280c1c0d41d80d80e4030280d01618201060701d040c510f03842d07a10440c009000e00000a03000002c90b00103455a08009131a116084d10948540c8000c1d4880c0c0c54034042d01c5000b0040d042c0980c4070a2040c8043c4000300036580b283c2c4442021140104c0b001808901c08100c0d1b80d0401c0d0081e240204111450b00b00403071041a07280105041c4d800060b02540340d082c00c00c0410703000396018410584c2c01b07a032f075140400b800c0e40561180c81d900d0040782509203c0315036540c042761203a10794600302c4e03034001c1e00080500900d080030000280103042e01011034401c18600a0300300d0b91140d945080f1b90032610010522900b4900300010004404c40c043c00400a000307400030300c4000525004040e40c001c203840d80001450b24030b1 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 111688291 1250 111687041 111687049
    0x140310062303160e060a1a1225110106050607050a030f050f1206120d08040b070c0201050f0c011503080301090f060506030a0c020316060b10030c090e04020118060509 73
    0x408201c0c2d100303401c190400c80d440410003505104480080e400c130019505ca0700080b0725034011756049400c1600e00030100c1000503440e8030061030020400c0c0e41c805155907a040c0d0102c082c403044903007046181d14107080d85000398801e0a6a1007c400420000126603076981f001030b0b826400300c8001c54907038001d15182401e044e0001821800d004482c1082441c0002c81d00e00d0f03440c0c0d0b10429101d48100e18a805c0400e1039511001c80e10780c0306809100407034001040b64603014140003411a4106c504001090000f07a0320fa204108a54019a0686503a8100301c801c110300c541a4014810440b030755940c40b030010815481c0d0b501c1c080b0055000d075512584e207506000503e0f060703c0c4220307505104030f030810000300016202c2800300e0b43c1c425100c450026840544040c100d0562140b030540302820a03800c4541e03420701c1669442200c0001c403c45001d02003c0d42c00b40241d096a00e41c800d58004222103600410503d8480d22144e54001c0c814544800007006000796800380220940040002850100798001203044c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 111689541 1250 111688291 111688349
    0xe0f0a051501080619110d140108030415050c0c031504030206010902030402100503060301060e01150909051312021002040b04090c110607120b030109030c17031014031006 75
    0x10450072100d503041000c0180d0315040074100551a601131414483c48101c940d1000300c42035200148180e94407405e1b0700c401d0103031001c0740d00c01c442040b040e40005010540001100c08442c4c005940c89401070300f20105584903003086d80e80410034055103600400b660b07800d000403060300b5110741e042c0d000d0381482c0c1002860004160003000f039262041080c40090395518030b06100a044920b410350303032950741c100481c0c05880c8560094000311001c10002c0745007502800b2403100780382d4581e2040c44e0250303520003103415501c040d101d88000740481e5410f1b02c04100301000341d44215509004071112645580c001508a80c05607209038542c02001c40c0038800c0540e540220000044a840c280062250003940182c4844002d40244103104081500320040856600018000140180200170b600c081e820041e04015044200b141c024580c1c5041c101c806001c44280c0703000e4580c81003078500c000e0500c0329103851400c41d030441940c144900522003401a00901a00c800b4001140041c0003500d840300c8d1010b4594 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 111690647 1106 111689541 111689563
    0x4290405010c030c03150306020f0c15040c0b090108070807090308070f050c06210406090b1609051e0d08070203030f040e130f02090603010e0f0a05 65
    0x22a0641c080c1c4061100b58605016103100321030120121034051000385484081d0b090203002041156000d040140d0302114014074144448070700d58034240b00a07203006940d41106007003000f0003196418480051103d2002c240c100409040068000c07000144002c08100c20040003500c81c5210300070150095410440c000d58401050410680000c000f0009560340d204416019140d03003009000c03200e40182004079001035098220040426400181003a2592920380c200640403a1210f03030503070301031000803007096005090b2a4018000f8138003580000d10520f4143e040946202410704a200080c50480c2c90100c2c02c9503514241c5100d00401c10040d405200110301444200c035140c0c001d00070384003054a80501980c580307400c500004d814010090100041c2c485e04001803c10040765a00494018000304802404000c11440d025883c0203034000d40d413001600740207011084c07000c08445 = true := by decide +kernel

theorem cover : BRFrame.Cov 111510791 111690647 := by
  have h0 := BRFrame.cov_init 111510791
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111510791 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111510791 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111510791 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111510791 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111510791 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111510791 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111510791 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111510791 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111510791 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111510791 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111510791 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111510791 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111510791 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111510791 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111510791 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111510791 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111510791 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111510791 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111510791 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111510791 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111510791 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111510791 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111510791 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111510791 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111510791 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111510791 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111510791 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111510791 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111510791 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111510791 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111510791 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111510791 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111510791 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111510791 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111510791 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111510791 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111510791 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111510791 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111510791 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111510791 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111510791 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111510791 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111510791 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111510791 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111510791 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111510791 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111510791 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111510791 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111510791 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111510791 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111510791 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111510791 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111510791 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111510791 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111510791 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111510791 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111510791 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111510791 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111510791 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111510791 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111510791 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111510791 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111510791 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111510791 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111510791 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111510791 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111510791 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111510791 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111510791 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111510791 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111510791 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111510791 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111510791 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111510791 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111510791 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111510791 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111510791 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111510791 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111510791 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111510791 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111510791 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111510791 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111510791 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111510791 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111510791 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111510791 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111510791 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111510791 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111510791 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111510791 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111510791 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111510791 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111510791 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111510791 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111510791 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111510791 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111510791 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111510791 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111510791 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111510791 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111510791 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111510791 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111510791 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111510791 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111510791 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111510791 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111510791 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111510791 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111510791 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111510791 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111510791 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111510791 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111510791 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111510791 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111510791 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111510791 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111510791 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111510791 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111510791 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111510791 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111510791 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111510791 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111510791 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111510791 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111510791 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111510791 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111510791 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111510791 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111510791 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111510791 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111510791 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111510791 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111510791 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111510791 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111510791 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111510791 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111510791 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111510791 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111510791 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111510791 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111510791 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111510791 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111510791 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111510791 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 111510791 ≤ n) (h2 : n < 111690647) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
