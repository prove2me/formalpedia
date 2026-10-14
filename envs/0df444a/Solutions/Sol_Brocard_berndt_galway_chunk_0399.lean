-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0399
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:36:45.004309+00:00
-- url     : https://prove2.me/submissions/cf7745a5-ad3a-44d3-89e1-5f2110d1c92a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 71582736 ≤ n < 71762592 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 71583986 1250 71582736 71582741
    0x90f05030d0606020d02060123060d0516181a1204030c0c05010503041a07050910020c0406050306040302100902040f060605030601110c1507061b05220b271201 70
    0x51026070802800019140c40c400d903921419141002c00580c00304004010010070341c0e88207002c615408500b140750031920000903007039400100550240700d5440d0b0901281280401d40a810181035040c100d418803001da130ba9030340c0b28886224101081d00a1251034030314511440880d9004201d50b6841d0401d400c06080003800603e201a0454440000c0480424151300405c140c0344115800fa2040b030407141c07008141d0700d00180251905080c0711040c07189034025a50304295043c040c4096008214140316074041005070303455580840e001e80c00010034003000c02c1e07000c41d00b41980d9462620101d1400021304c0800c000788408443d0780c044918004012500950000046028020136a01c02640c001401c2049440e140801c0d5820351141c441306100b80d2103080c0502805199004002c00140f004103a5040e185602030860f614000800003d50a0460251a140c8900540043c0703035114a882c00d00c0d5081245100c1c03000c00b101c900608220801c10100106032041010402410380040102041c41d034502 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 71585236 1250 71583986 71583997
    0x6070f05070501081015090e09520b070b07080702060906130c080601080102130602070e0a18050f01020309100b0603040210170709051507150c03090f0503 68
    0x1800d0048078030018142d0f106183c0d060060207032100c044082443c01d6041d0059280145070302003800000b0b00c00003800f81500c50b44601c40d105ca40301600c840040c0c1b8102107481b400ca1824500d107501b9281103501403440307502803c20825a41d00b02220b200d0300602560408214030b83c010001c426000840604105143d444103000f20403e0315142c102e0b4031508801ea886080884a40d00160f2007940003840000f00c86480748040d43c01803801110194841d40b44504140090704140300c01da400003580c2050502c3c08041c070004100d2440a00301140c10160703d070004a0005d0b0400c00c1940d2540c080c4e800d1540c41030040c508190f88942198043c41215807000e000c0e40040b2440245406240c21198000b909805070701c100ca82c00a00086c51550b4030f500300489a0401c0c0c8480301000061015094010301003080280501059200c0f04245417602e41086100fa03440c03501e0070f10880c014840d09001407030600c281804481191030204848400071821402008902809400c0c0d4401041d0041030010110003031070b = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 71586486 1250 71585236 71585243
    0xc080d030501061e03021606060305060105030d02060f13020a0b0703030b0a05100905090a150605070210030b0108040312023a02030c0304060209030115060f02070e0105030c010e030c06070f 83
    0x1c020ba90307406040d101c001c8000008038a41554103003020000c1d101c0d60042105180d5030380880202059501d450080f14029001103406901c03800062000c2d20301080b030000342002c41e1000741032500d0311403005280c41402508034005070780c04c002c5400842d6650745031000034000982103583c88415505005002c2c020009180e405040b081d103011135a0700349a07106240683c019143c001800c0c0ca40000d00c0800350004040361a079075594046580311408010b80c0c07500501007940c5540e01d40710a0f0041180511100039400c2c20b0520f400007004807641c1201480b98403c1d010f091501c0e07115031074910070020744a00d0a214400d9400701282c824441407803225501410880450103910001660741c6070100c1c442070352081c1000c3d9050000030009a150740040c03645020203000420440d0a0f041c3c19844204160810004603281c01e14000301d03558100201d034000d281d81d140400c000c1d49000d0110345c0381c1011010307840c10080c40e10752a200ca40c800b0800200d0205000d41703615554180e50410100c1d0106855044 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 71587736 1250 71586486 71586491
    0x50703060525021006061b080304020f0a0b0c1203010f14010c050601090608010f020c0a02130e060a020a03050f0402060f0703050408120703090e0103020a0b030402010c02150a090b12071103070c080d03 88
    0x105241c7c6c03007201002d544645058043c080450161a8402c0c1500000c0040341d02c002485648540b6403901100c40b0000c0c142031040b540ca41e4480308001382001941078008a203044c01340010400680c2c1303940f4800481d00440c01d1a0034041c0701e07100403504505041da000d41148588400014206002c3c3d103c02c08480d1298001c000e000404800c1d0303003d92058115030f868607032080c890130002d46400369030400c100800d4480042c40b1134a81403003600300703001240c0100b5455804910204019014058581c0c072411903249091146496030008146000710030b854000303285d000c00e0103030400d80a581120044d10500c0112000d0386006000d042040c1d00c0060110002102444c001602341510001c8074183c90780200781d6000702c1d041000400894100800a90400604250140150b185c000d441000940c2d000c441c00c4d9a80760304480680180c2a80d4010140118208000512001c04084160704010706152206034092500001447c50003204c0c0007410340d40c000b40700007403840d500140e820741010030303501c09 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 71588986 1250 71587736 71587739
    0x50904091b09020304081b0703060e101112010b0a030f060810110c0c0d0303020702090f10050303040b1902010b030f0703030801050906030c011101111204110d050703060525021006 79
    0x1080b00fa40419140145580030130310030304d0b400d80007500010f8001c1c002001262001a070f240c490b80252040390010b520300e41c00540c80206440d4450154008607640c40340501e103000c41d40300c042c28001005100e6068590070206100b60487d1180c0c07c85146001521030138001140c490550b07584400b55a0050118149000c00b4a0320450f1041d0603a982c41071420003600070a11404140719404100040442c20940d0801100f401691511302d640d015000c5c1c07003030745d29003498642c9070400c0c100e8079604054400d51007400200300c407003900021200b44030741c41d0600800240340444141d024003120a5003e6150080ba481c031003003e0300c00518541101c1c02560756040c50b0341d0750014481a030100341ca4235a0590031101d0301c1000f0394021800c2c011842c900200014005501f00e1540031a070f0001498200221241c0c0309100c00c2c4040103042544080086882402d501c4603030b51580e0366040b0038400242110749581c0005c800744052220818464004021050108203040c0000d4517800885c1c409004203281c680d0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 71590236 1250 71588986 71588999
    0x10e0609010e0417040f0602010e07050406080a06180b01060507060c080f06010c051c050c0106050303040b1c0906050a050103120c05120d02090a03260c0a080307050904091b 76
    0x4040d4100d810700c40000c120794655880d2120307090088840089101c5082000003400c00059410100820300b5a0002451101c24006103080200c240d0100344a00e05021082c0103007400030400300c00681c1e00010014800421035440f6a5603404050054048000790b800011030303980000c002e1074802c0c0f04050800c0078002c3c103c41550008400e507080d2500074000c4001440030b5020742c41c500c0c2298080c000300c1e058002426001d513030f03886010300d9800018001080f4894604000d001da2006006c048020b54106800e00c401c48403140200100351011350300d0304460302c505907800d5020350708140d042182441149010b42d2440045c00c1d0032310040b10380c90840d299500426110720840c407800b0398004050204a201c1c0340e0b26206a8000e0081c041c1c03016400c202c2c4030b1099807801c401d040258842c2c0c6910b030352000f1603200383c21040c200030101c600d400c0041004900742d500100d00700f50740c03990100805450b6190040120b50034052080502d8005190080890902c042c01e0401c4105004603d0465015500c601 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 71591486 1250 71590236 71590249
    0x70309080a03050a030b030f0d020f01150b07260301030309050a0503011e02090a0b040f0330080a060b070c08060a15090e0309031e0d0f08040308190204060206010e06 73
    0x85010b40090418421900014465008040c14a8000b03007110042e21141c0041420480c0000c07680c000343c2d2100c460200725100070301034130b03401004400000b025140380c000c04851610405c1001400c1210154520301900c80c040c401e000c60a4048400a840707603180d00e005481440c90b40112841020303081d1002800385814010004d50b0b80f070403e05002e9018214070604043e400900280d030740032500010105841e01c40c503010784010003000c2d00e51003d1902d942020080341649103140032a15041c1002c014100c050f0850140d11082103240c4806c2e03680d161120381c0700410f410740008a03034110008400c0c06020070409504141c030100ca040d03030603644a91a684044074100701031900103060f80501042090000d52200320016041f0056900d0510407a000906101000d03c480441002041816060319020400f01505035802d060015026070401e01c00781952400820040810a9000018464210a1000d072403e0b0351111400d6440d16224200a901d5030801d0003803075118804000060b12514040 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 71592736 1250 71591486 71591503
    0x6070918061206110409090501021201060801030201050a080a1503050c0a080c15090a0b0714010c05031b0a020f01020c0c18010b07020907020102090604090615020a15020a02010f050a0207030908 85
    0x4001c460403500003550b405000d802001d400202400e410f005c00190610180541c0703403500d1055000503607801d900b0354108003910060b0002010040c0c1e4000610060f60408100c40524801e814524195912601064090100142041c5a080b01a24000100080042c00345007550040b1501e80d0700716100c004d801d82c0d039101001c00b1a403060700000e00c3c1c03002d095502e0042002d040c001e8406087e01c1d4652000c500180d000040440b0000100000b002125030300303100b0010b0011240c80c049d0325508024804111022004001c0c01802034009083c0900078020000000c6400e8034800035034842e0500051542c51754111400c040c040c0e01c2c41084900601c01c13140d0413605a0350082c4180d810b020755a0203100055200030030350000c1d59800c01442406643d002d01420041c42070090104042d42000501009a00419802410b5604c81c1c5510700005507550340001803035400810060301c1d004212000ca0241c0140408800c4603450102071100e840c00580041540c60300a0302ea8440040d80c1d9040d040d6030382403a = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 71593986 1250 71592736 71592749
    0x2112170105010c02030c0402040303080118090b060405090a020a0905011706011a030705070b0a020712030506011215050d060e160f0501080a020712020109020306090106050312090a080607091806 85
    0x224014000e541c05060091106800903003115050950307800032508170f900641066000c44c01c000c004206280c0059400c08180030241028044c0c94000c0e614914501d2010300901c2c4030300d0700c40001a803114410002e40180c59001481744d140ea07565030f9503040c0100028083c498000c50001e55104194000050f403604850418152001c0041620013080c5036820103420350041103000c229003004221000000c2d0f0090554400c016610802890710408007403c40000d0380030b140c285400c0020581e00102c890141480f0421b0124412801007000d04550a06400c001c3c0c0c800b100c4a010024400144c1c02244400e24400880b40543d61501031407600c8001d5101c3e41050009285043c4601c1d4464407210707030042c0140b10054207142965541583e00b026049074280140c0d9510030120a500c0c042010320780201c180c1000308031090900e4081394940d0b2030b50f00405800003000810035020b4441003400b4008105481c2600c20600f072820004085d02e005d441340f0241490f980c1145040e00300d091042c101103411 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 71595236 1250 71593986 71594027
    0x302100207060204050a08011b0e0108060d06020c010e010203180609060a180c03060b150c1203090a0b070807020708030310090e0a06050c1c0207050c13062112 70
    0x100408044080d5218540854480b50240400140da40346d14034880040d00c0c081001142004800c15042100402c84840c1001c001c0e020604900300e9820000d641d4102c00c0644d00c0709680d440609100000c0d1281c6d001640441d807800c460603072810019800b55000b41c000c85802c48002c1ca41c602c0d40d6a4400080d03450511642102c4041820b00c040c0386e0110f01c0c01090407402c05511308581c2c60700341442d0300c603034020707550282c40e01aa202c03a407414541030300d05884a503c80790300b4060114800303951400480c10101032008004049051040b080240d000000d40c45070060045151081c00102144420f0b40c045000d44113200021455071004800d488c03003400118400d90000d8030340314440e0094442028040d0882c00f9040c52000800c2d864014248100000b200c0c241d580c0d1004150000c2d1140d0248601c85114418030610000030008100300c007040c00222610081046809820b00060181d036014641c43c2e5226041101c440300e01c4c0f950319400b14001c200451200c00030343c206581c844c444080c251500700 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 71596486 1250 71595236 71595253
    0x32703060f07050a0908030406110c0901061b0c05090903042103020c010804030c05010e0309030705010c021e01110106030c150c0b010b13091503060b030d050a0c0f05010207060b040b0301090302 85
    0x70303c079501500030101e9a16114030842da451506500b994090f81200d000038003052044100c66034104403010003040d01707580e00d81c460361510000900342c00c80f41c039030b840c0c2c4d4007088406001400840101c1d04040d0000a05a201a0601b41e03c5150b6030340c840d1007030311124440740741001404103c032407810740d00c41e803d500030b89501f003030280044480140045c0200d06011194000380c01040e424803c40c00700f40398250040d80c1d5a02140c0805252842c1c55000300d04000340001803e005031600e6801020f060755410000c0802d2901c0801030300e62100221460100c1d62918800106209108103507070120b84c0d094400c0d4030502d982070300c100c449015605c000f41003541101c00400815002a0050207000354440701e00761002e0300c960720b00c41640c10700c220032840d14140310421710034084544a50803803160214018140e10101d400e01602a0152406010070300159a0700c4c6000d10075540c1529240581c008000c56403481c1d1403030001300422001025500031440c00b40500f003582814444d280519405070014140300 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 71597736 1250 71596486 71596501
    0x3060f020c100c080106020a21110f0105010e060d170d1b0305040201030501090b0d0b0603011506080103020306060102032a030702121e060c09091f030f03030c030209060403140708032703060f 84
    0x10013500212703001c014008419400642d010702c402c806814a400c008181545000c1e0000108003001d00030b0341c400e42517a1003c800140c5181d0003071440f022008944c907123070003c0b0140b41000b40358181d41d110f000c124480710249107650541c4481e01c114405d0700c0401c0240d817140d1820049641e00325403290003c8550020202044c0d5804402d0b0f0b00880050000c41d10703000541100400fa04c40354000f10225840b02c00500031481e050181c43d601140031b02c015070500302120088409145020343d0201a8003400500940c0014244225410644c025000209403010341c00b00d0b035641ea180e03030510300401142040748414640081000c5000d01d0000c03d21500b02070060080050038003010302030103000000b250002c902c03c541010010000c5001c2c05024000c01071508018064071035464450040600c100070503a43c607540c0800343c0301a00e42002c0c03628000e40d07800c081d203854040c09030001425440302107003941e18030030b01b402501c5442d1850708c8590600e43e00c04084c507035100b006072550010b9860703810004184 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 71598986 1250 71597736 71597783
    0x30c031a0d02040902060414041d031608041a031801060b0414130507030203090f03030f130201210c0e040204180e0a0b04050d091d0103060f020c100c080106020a 71
    0x42038002000000c851105074001b81040d841540003960154004080f00401d1a040c400c0104294580c009250f022141380c0d481030310b85c0709800340c480c9414907001803002403040a0091b1006440345000c0031464808d44014648a60030460b40c40d84c015040c08458084184103005102c1203a48200a1501746400e0485440450740f004494681085455441030b084244074041c013070060704c2d5903d00682d282401000242030840c904000201503008000348280322401540c0980d110140c0d0b0221030411880d0304c0100c03000e221914010b6040301c5030f0902840202900d620050449c00345465034070105001a080c802a40900c1c451038805049012414040c44219000113031240f0084d13054030403050150391911220002642c2c203545c41d500c01e801800c0c200ea007002c0140c01900104450700b03540120440401d0000d141404014000c507110f00780706221812980541d00038911620507240070030b4800702402d0090182c1210000043e00c56800024601c1c00801c07044032040c3c01c501a01454144000250760 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 71600236 1250 71598986 71599009
    0x1d0703060c1b081206180c03180f06060a0609030b0a020309030906040303170f060306060d1b06050c0105011a03041707061103040203010f0501060e0409050f03070302030703030c031a 80
    0x9005030300e0200d804100303085520840c0c643c442e03030351540c46088030320154440c400010080350103920b102810400244800c002154044100640f06a4a5581580032542140b8954010391075100f0310b01d80300c0d03110324081045885464180c50302d50103182e480034111418481c52002420008004022820b503460705d400855002d200c80041b60710b00b024030000b10381c003076100da0720079800695480002001c902098443d81d0b001170b000321201540c0e0403c032001076110032015041e40d10403003c18080c0800c0011001c040450030a01041d1226001e0740d47c4d00c041c2807076128914a03da40d52900c1c0c0049408044450b80100c1c04012000f154259556540c1e201001c0e503a1a601c0340201c5024030600c800107005015101030380b0303215001e450701c1e41080c0c4181825580b0102e60500900e06200060048503408100c0c0b04007014111004280c00100e400c1142c03c0c5501e940c2212a18040025070506254002004005440c1300e65070401c4030705450a01102210400040005a1000c40320f0f9821580b5203c6000c04 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 71601486 1250 71600236 71600261
    0x4061707091814220227010605030108100903210b1504060e1806100201110a0c050c0f10050f07020d0b0402100f09060f020c04050405010e0f030f0904020f07080304030903061d070306 80
    0x4801b6a20030349050003040c0240d0200d40018000030040c85003100a00c1003613862010614284401d5405039005499200740c04ca9980101d480c00c0d1b0340800d4642d9540001400c0003001c0c040c0c00055005840b01d0b00103038000c0c0182004520a10020342e81420f242410101d0034401001c0261152a00c01c200034a142900c03015004542d200c4000394410300100c0c1c014101c0030096100c80c0303402c40203898070340d0510101006042c4251501d144a22098491081c08090380c112850100d42e02c483c11b101a141c9405207d030040c3d00500d890441e00100716034a00c80d6400307280216214100816403803400c0b1a006c281003480c60005461250400455000301c8601854680c240195007400c00300501181c100e07a4201c400351060380d150700507004011010301406440807501000765240c015142040e055030f10400c0041e500503980091000b603c240c260054664255001115035524207003820000d0650855020680c2d08903c1c0540d420040410400c1c0101c58451810103003044038a07584483d0010704450b002c02c0c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 71602736 1250 71601486 71601529
    0x403050d020c060612010c1202090301140103120e0306280603060e0601030b0108030a02060112170d02070b010f0509040605090118030306030c05010302040617070918142202 76
    0xe0365000050001d07045080c0410014411860501e00300901090b501610003401c0e40751079200c80300c0030740c4202c50000b580c8800001603070305d0013001e020074010608883da01c007205107024008410450301c20f00710841a0410351b5807400d802e82007807c0548440b02a6040b10040d9501c0c02040d03880d80d40c0c182c0303a100c040c60084001075119903a459448c203595800312400607582041d0018800c1004400025001d0040840250b05040c20030002954680060281031000402403050b80200111034070340c1950500c2036004640c5a050710001c120207501320741c804a80c000d522600200d100003a4824000c00c076500104030600a40b02c580700c00e002404094407111965403123140c900d59640d40103c0c8031013082c0c460b54000034001d00e14241214507002d40c3c1c01072030405004010800c080d80d4050411150440341c0c1c1d00740007844d03c4140054901d61b02030f03886154a80745100d881c00464205902c00b055024401c1e40485071551000c5c00300341c7e0421240c02c1c01d02d451080c40e890720054188900801d0381c0c449110741c40c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 71603986 1250 71602736 71602747
    0x50406110a0c1b081209040608032206030b090f13060501060509041805060412020c040516080907050a0b0705010f0509010902030717030d02090f0a0e010501090e040c0e040305 77
    0x9400d00d81d0311611420000c18218010502007182060840c40881d05078107680804a04140b40282c981c481e84a001d180b02c040818065815503641d4808001082c216080704e42d1000b4280800d01c0105840319040c02c000303500c000008441d8040e0050f002c2100006203e100f81e40c3d5020003800154001422044220504107400c00008083d4401d0501038200c90b12600d841300d406008000039900100d0b1004445594160302c500001c030005146500aa8030903948510340c404080c00720320304400b0303c404580c440d04010a00c0607003100702d440742c200c00c841c603902c54135240d80384e003465582c2d1402449287d4000e81041802c0000f00d0f1000302800800d03114600108046032803c07148410703100181c034600764903551648c0b40b0045250070444d400052a01c00c802421403601e0740b00103a201d025401d0270481480c0c0000e40610550388074013640104020080004040c02d4403035107100c4070420240940f50200301846070100f41409407010141c4956441103410320682d042484004445102400440610405204 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 71605236 1250 71603986 71604011
    0x10602190501090f0506011403011a010503040206120705040504060e090a03030e070b030114120703051005070e090a0f0b030309060403080702061e0705010b0117042301142a03040303050406 83
    0x13a00c00640038400402c40c40d4104140d41c43d130b45021010a5100b07a1618036070200c00039985510040803107003424142c0d1039550710700118070984200101c4403015505001006800c41d0040050000d42d00142c4040010a44524a0a00200301aa004882a4002000321740080e01c20b42103c44102c840c0415110b5507a41c42c0070311841c0b0780003a0010081d030020440c0c0e0304040c8c00c220808404403807403800108202031654171100d40300e2800e4108440038079100d00004201e6800340070740c0b580d5100090000c02491819141c108002e0000c040d5121040e401c0004214079883c001098038070402c401000c4924180ca5980d4409103076011030002c9820403014080315940c800941065030108040c810705503500c030580e1410074212508501da10b414810714904403004410078401c2c00d50b0143c0e10032030400b24641c0c14140e0a04c0c020154005000540c207240254081041c8952554020044040c910380e00e5054019a010440c0b400e1184c01481c510500c006400700f4400d8000c0c9070098000ca1002400311a001c4 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 71606486 1250 71605236 71605253
    0x91c060f060e0405010c02070317180a080604030e01020d050a0309050708010e0d080a0203010e131401020a0c030306080613170c0d030b0f12070b070203030d02030a2301060219050109 80
    0x20b01c00d02c400c0941100f00403c0c0312080c0a506550b0115101811145040d40e8680900c55407070011130141d242c01194803038a12102d08010b034400c00c00108103841300c50341c4100c040e41d030b030008503000c800188140302c00444d01d5000140201030501c250f1100740c1040401c100c200c004002c40b40042e10684a840e00014000d00700307100b048001148900a010111200000030781481d030041d00508481d1b00c100b0040103250346481d200c0d60484008070720640400c03043c3c00d064961011071510790029503c001122089290854980e03175242e0b04c40d450078450b5030b9a03181000e4907000d003121820301e0940740c01d039618009000d00b0072408001e104c4040ca82c1c10620009007991030b10304000c6621001c2503540d902d2140341d00d041d80c424040514200c1d080f4000c0c0c401100c4040d2940c259100b08044920081124070856900344141e03182d00c11001c03003c544070320306440c220780540f007002c0e00426000d0181c205124180d4492032024182c038016001030414145c0401031540007281c1400640fa40d550b00c07030b0a04000f44080 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 71607736 1250 71606486 71606489
    0xb031602070f0f060f050c07180b090705133c080601081608010c09150311070503030604060608090303061005070204020c061008011a0d0f0c030b0a11091c060f06 71
    0x80d6440310b03e505201014021880340110705060210512844061b004c0c0000d4120030b0700d01c148141c2c0e11800100b40c1c0c0034060b00d502d0707560541c0510b000c2c0810041d29481405018505d80d4240107100242d61001c0f0384c58002c55145103511007581d80c1207101c0d03196954400d01c100b0728084803c0081503541d40d60f038250400741c1c01e030404905034110318003442c100d070408851f5001402c1c40c44002c105041030104080c110400d94031800304400802c50f1001000f42c001d90100401f98034010f640c6944030b0790f40c60083e8580e8812100316102c2c1c0d180c0703100410254429611948900d0304400198510380310803040144410080c000341c410000c0c100000310040e1524006414480070042c000c0206007004841854424656005100325a141240c00d6080075030310301c0d0010b04000c040d50740c03440d011014101810303102001c806c054080b9501140010070020716080d890304c580c0b80c1c001c0c01c010003259800e00d50080d1142c0840258800e0100d8000803101586203405182c00b8410f2100140c41701104450506450f0755 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 71608986 1250 71607736 71607749
    0xf200901030f05010b0405090312070207051309050609061b07110d0f11010509030d03020903030409020a3504080306010e0310060303140a08070804030c0606030809010314010b031602070f 82
    0x41c0a40c82c08000702400703864400705c0219800d00961074804800d80c0d5074041c03505407085024900c03000c9400e00c0e0090202d140a0301010b007240c3c03040380032801d82c0c1d0050890000c04840e10b115141c0005e001ca00b011806a000f00307205030014602100007101224241c02c0528192840b001d0700302103a00540d100710284011a20444074102103a110303041c010074242501c3c000c40c0c144241000414131551740841c5e0413042800d039040c0181c5507403140f408a89140181d070880b2075010f100040f4a280907800c41c010902c0c403040d004040c0741d254180b50305003c503003d4040ea082a0b10071310802180c00144c040700510390141c4180350140300003140c0800070340b4281c0c05003400c520303040c0d45000620500d0350190a02d0250080606d4061a11103c84401440300d80010b012000308002c0ca40400c04051181140001c00f0760001c030103010326034407402c140f0b2640e40f203420a1408a0302e0700845005030880040803504171510029403a0a540c0c50001c100340e4000380a10000071030198002c0800d00104040640020317140 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 71610236 1250 71608986 71609003
    0x12130323030307081504050402090a02071a28020a0228021e0a0503060c07020409031701031109070c0f03030b010e030102030f07020c030a120e010306030b090d021002070f20090103 79
    0x10a2000005d08480b003401190040d4107210400000d030b100c0c080c07600d400000d00d0f40f0041c0d407440305051402031502c41240039650740c154a42400039181c980c0c0038902803018480c0301c0d01c1300e41e481008800104c1c400d261216025820400348041c4440c41c8070800300d0100030800400341d01c000140e00003170750000d5100052460381e1480c84900c0c0303181003c0120001414050b0300800c0d1a08200244c0c8005000d45040240b040d41c45000d1202010b203e900010300448495080e0451561640b90450880380c00442e041d0003030720702000040415106105408010703401605058200c0c0d0f007520110b015121040b60305060103403902451400340c400344000c1d4480d0344000440c00d86410300000090520004410243c401e5000314203220214800240c030420421030750525001065a0b8401030300600071a03031024103d9804081041003c120105190310b51444a5081c1d075204400020900102c1c01005005024021244510b41c00140324410421038a80700c6010070358129080000500308100980088038800c0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 71611486 1250 71610236 71610241
    0x9010f090f023a09080f070206040302100201050103110a03020108070e03070b0f09040c030915020904090602160b07080106090909060b06030903070b0a090308130c0e0c09031213032303030708 84
    0x3102103a00400c001e80c400c3c01401050300c03a89540c4014001c00804400d11a40000c4410071551802d049500440d805007000700301201100b4064000d200920040d5079460400301001800e10300034460b0802c0d20750507143c004181d11002002c1b584c40d4000903c0350381501c105040414240c8100307000d085000e040032846540e449802c810311007620300036140d40003070509100b040c000250240c401e45104081c1074000585942008000034083c20b40500b000c0c1070644005010048543c0f0744100f50401800342d2452005a11003402c2110509424864a40001d54103c010701c203504141d04030180c11809681c3c042101c1100c1c000080c850f82c000c0c3c41c00300007139100060703d0742040710118403280d10210001c000c12500b80301e80c801806030b0000514104001d1087c074a40b808002407420110080c100160404e00c052400414651381c075070144079064401e100d2140200407422080c800c560252a0041c0f08000c22443c5541c1c078035003c4c1e4038400300048614042802d900c0711000f040550b00c14030103a5140c1e682c60 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 71612736 1250 71611486 71611567
    0x90a0e0f06060604030b090102090a090207200108070e0102030403020612090708010b0901270908040503100605030a020919050c0304030f020606030627010609020307020c09010f090f02 81
    0x48216500380e080e5040001000410b5507600c1c00c0e1000c890704656801d02a40c0c1c0c201500340240308218000354841a01c030004038030310300c0c0c507805466200d1042c021440340512500c0d00030020480440c91500249071000060340c001d205130720348500038106004032030034907807640c0c0080e103203400100303250407000b10710b00c00c00100b28000c10860004240310402006212800804a002400140100c0b5880101401050354600020040003060510303a03404001503000d603e00501c080c0d1240c40360912a01c01e210441804002a115207001c4840040040550445545c00d210b1494402440b0341c0ca5020030554040101003c0d001d00d030310902900c46a82d54a11703282ca0060300e640f0082880c4011580000b0030403000d5140041c0f05a0045d4140628941d1000b5640700381c00300c0d48044060311720700c0d42020700c00100304002e900610700412850b000e488080b250807060190045092003402080c900082041084800b140c1c094504004180f8000d40360840381c9021055002e5078100554500420f00c02d130181d403 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 71613986 1250 71612736 71612743
    0x8090108010f030c14130c0e010807090b0d0903030e0d020606180c0a08041104020c030d0609090210050d0609240602030f0418090605010e090105060607020d0b090a02090a0e 76
    0x350403616080050746086854100415819000d80d101d460741400389034500d586c4484441c82840e0341d800c401d0015050440c13009080d003034048142030209041001240d03166014180301030030fa03040685501d0405905115001c05003c0076a402d8083c181d660340e012210f00c0050120480e5845580c00610b0107050110a00030101400c0d50360140303005041e0180303c90307040301c0401c5070b40c00e0300e484c9001042074a072410041e0320f400d46814482d60042c03000403c4101b9407000b00181c2510302d1015000c001c02c6a0f10680d440c03d586a0b5100254000450203140724890b02610107803803159540c0707000241d410388801c000421240c0030b4440d800e8540c015603401c01e00c2029407000c0e5025007854406141880b072100c92800143c001c40c01515854400207a20400d01c180325800102520b0300280d040c03205503581e42d44024016010b98070301000d1350070700002504500707101080710a11940605050300c5007550340c0b00c890070500007808140700c50081d8580c0340056034030312038800d000700310800f00090085940b084c034910303 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 71615236 1250 71613986 71613989
    0xf0717120a0b0a03060c020715020d0905042f16060f1b02120702130f060819021008060303070f031107050901030c03030c1703090309090c03100311030111070809010801 74
    0x401d603007400740102d119107804100f101101d601050210b003150000344140e050070007540207001405646812070220503800034000241c45003a13112840c206440f40d0a10040d40c141415042c5e41d0102c61a10360f9400d0501070f540e0b102040204a034038240844c0d000400a0b100c81d07901d003503a40740d0700d400c0e800d05c450b00140700f6008008400c0030200103260020384040d41342c5444100d4086202c00c082485425900c42c001030040100020600700700c4202441e155a0050450f030041018900c0303450b065002200006615001c3c040e0003d18584610003c1c240449410600034032203034050006010010002d80041c01103036180784603840d802c09110f401c0700e0031464400c6950250f48103401c00030040020550000702e8a05803074061420b216080102d0034105455034030800c0502401c0400010000443d40c007201900c80c10000310b809281d01d89400203004454002034038030300c1450000e203a0030800241c1c3c000c0907801100300500082000254400305110310f420006060300e22500c000346642c015070340309651031f0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 71616486 1250 71615236 71615251
    0x8070b0a0924080703021b06010815010b03010504150806091b040b06030a02090607050a030215070e010806130b0303130f0602011811010e060301030609110102060601140f071712 78
    0x1c0000e01c8403030341107042d00008802007040c031801c003020444280c80382d0100e0f20541d2086011080f00e611240c05c0c071740d1381c02d424455410a806800e403c1100020209030285c102e42f601c2c0851400d59081034100320050480b40e010303450342074656000142c894814130085200740744c40c0c0083e040c4502140020400d8048690290b40300310b140c074800e42e010b5641e21050b2070f0003c04020005841c1c11000003c00c000c0c0c807801a014051380b2505050504141c0e00007001c0c08801e2108500d243c064650f0882900c503000080c0c0d09038003003112003000482c5c2e820042d0001841023a000070100e01130700f1010219003154005800e01d9400090360388284000c55002e805c01d80108400d100070060b204107243c080c84240240c0000410f8400300704064250340e8800c00c40c00140d86402000d003562540c3d203140c5a4018205103004031004481d80c0102ca04660021655074411101a154103c0303881c40d9101d982c00070b0380300840701c10104034180400d80120b1204003060508503a03024555a0b10800700c100c5901542d801400705 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 71617736 1250 71616486 71616509
    0x3090a051012151707090c02061312030f0203190605030c090f0a0b060414010e030a0302030f070c09050c041a091809030714011b080402060301150908070b0a09 70
    0x4190040e4410020041c68111040000c0c0c070f81c0081000d9084000b1039803200c40407903141202d2a03541480811018116012214108001070b580c81003a600c0366811140703240041040c070340603004116a030304240d880703c500c1d00d00001d9540f5100038401c1240c2082d00e05041400803041c1940c2034912030310841002e001e00310000c0c013840000340001031514000400c1140003035230003c007152910401c0c2d00180d2030010f000385280e444a031034002d078030500021a502c2c20f0004000d90f003100791505003c121361070741982640c0610315200c4c031401c070820705601600c0c044442001c0f1000c002610f80c014420a070003510341c014103c0c2c0d40d80c602000c421140d006001d648424030010006e400141d5996001440c1480d200280704015a403000211401c50086d01805001c0710120705440700031200640c00f130b00c0c618400342030090030708201290071140441c0488009411000410060011042400750070400406900c1c02e54a00307038480341001d0510b803440c0d020811810010900401c0550000c194030b000d0714002280 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 71618986 1250 71617736 71617759
    0x90115120c1203120504050303040303180b0403051312230f03030105011b02090a0b10090302010c0605100f0801020a0e040b0f09060a0f0b040e0105030607081803070f0503090a05 78
    0x100050000c01d4441d002c1000103110498080601a01c4030400748000705100300858642401c021383c0302e034401c07903040300005e10382800c80c00003014900002d9410341d088603a681d11555642d900ba2982c0c0c0c045040c0d500c81036151200004c410404c0755400c80318500c02d49031010040030154a52030700003140000c004050700101e070820600d90002060b241103403000d00c4d010001d034460708030188042494001c069048689a400c04c01c940a450308002c0c003042d0300355101480f0b00740030b8004807100b1065020007800a0a400075502c041074181c0c12494201d00d204a000c03d81659401d484200c42503240d000f103006940124040304402d401103588038485c03d054405200005041c000240c0c00448015164410010348001c03130102d40302c5501504c003410420320700d01001900c0d0742c0c085455402c24440c6036a10404100081500d040200b10180140345a0300c9440858903060759030b00c111840c1d02c00d9403055110a00c21040410601c1c1000d00980b405074002d5039582e4080001d000780402030383c02c554010f034088940c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 71620236 1250 71618986 71618993
    0x50102060c0a03110f0c07090c02030d110c06130303050609041a070306080102040f091104050d0f11031501051002060609011707120615090b03030a050702011709011512 74
    0xa886500c28111208296a1003190b1016001050351194240035464042a000d81c034118910042c030350503940700708a4011664130a038090940b02c1400c030401c0141c000784801040464240c110b54000e05843d0561410b00038080b0f01685089412a20084803051a085000a140e0144240d42d001401951060000e1800791100f00842d0303e0070b1485510300000070000f850f03c0e0b110754014000b03061214020740d0b80d00c1e507403984100700c10710034011012187d14003003102141e48034840c11038045030405001d0100340c2c8070544400c0d0b44a1100b020540b40344000d548880c229030340600c040013040c0c15002d03410200d5414076090002c84518000c0e8002035500007030a00021780d8600f030600c1c3c1103866041d40b035140181008007603030070304913a680074002d05200745d4000000c0052940207020b200f800b00002c40122a0b80c1d800d0b00b019540074004103500354101300401114540700e038000b071099074018180030300302c0c1b5000540b01400c0030b002c40e005401650f46150104816a100d01288010200f01c05140300c078403110748 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 71621486 1250 71620236 71620243
    0x10914090414010209090132030d03020f0d02070305030a050703020a021c0306030804080f010507051c0203100b0d1a0f0108060d050705030d09140d0b0609040c05040612060b0307050102 81
    0x81c0058803461658141858030b02c400d4040b41d48001c0003818100740c3e96907a1200c2014030340007204000c401d036800c19030f01c042c8d41d091422000c81050700074014442420161000d4001350322140040a00c000c003009140d00d1300c031041c0010090b43e40300e552500c0d52442c1003418642107039030141041081500400503a101c46074001103010800948081c40810b54060392410740042169520040001102150007c0c224002003000c011000b072090090040b40d4410504451078802c404a825080c584e0024000050310b00b40d020f581d0028220000c1240c498898010100300c1d00802c203800e24007a103480148908629003025141c10140645a03031011241d03400001c1c090500080c0a40d001c0d05a4410b04428030104202071401071030043c00703036015400d8940004041c80d009000302c10424110341d00d40d080e41c0c1070080880a129801a218040030307128613041014240d00980251252440c0c880042003e69940c480d190050806000a0b0b404100d14500a029155100451340c40394215100411040c1d03000b1 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 71622736 1250 71621486 71621491
    0x2030d030c0e01030e100603050a060c02150a05040809041802030c04050601050403060f0b040207080a021203071d030a02030f03070515010b1b0316061d0a03020304090c0c05100203040201091409 85
    0xb400c2c00f217041035901c207126241903101e81c051001d90341428000030174040c0c00710f218a81700d4010f070428003040c1c628010982e51350076805200d0b00d407001181d002074503078034181e0301643d00944980d504070301d0710308920300123030584865162080309611400c1c00c030f200714981000481032415040c1d800f40094509030380060310b00d00481c030000c1e04560320b07510007588540859004000b6140010421515040d007410004c21079003005100c200540315105080a4030312080b030a0b6172203806a661130745203454a80300c034003109006041505070144210400350006960030310a04081d00d07591401562a18400d09085252143c4900001851144900140007600e2080110707040703403404a110421b40150685100d155100c1c2c1300120701d003048440850020403406400c00349061000745483d0176140c400c0301c24a40c803601128001000b40e0b000b0042042481c8198102c03050895030b900b81a600c1620355203c1508210000c0f00400c005580001004219a0010350368005403036017100307084040c41ea0001140780031601 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 71623986 1250 71622736 71622739
    0x1050d020c070e042402090d020d03180b180402040f0905060307030807060506010e04050906071404080604060605190803040315021c060806090307020114032a0702030d030c0e 77
    0x252a9429510030440d035001440f070400300035001d18041c100140f0b1a4441144c006094002c4a09141c03a0002802501c0040800405d0000d0040c0b0725400c00c08410072003881281844004031054114481c140407401c02094600445c90ba20703481c01010300300e40c0a007803150300c0c400d0b44140800d02400c2e0341c41803001e094801d0a400040c413511014000382c5002c1d8150700003441654002101d20030031010f030300310502408081e2a4054401a0f00381040300f6a102121040d2840e4061000580c0c000e120301043e00303d011500c681d0300e14150b2500140c1d424060f0481d8241e9009032a0101001300e42451101ca8103401604404070b2201c90420002c26101e01c80e034800945500e0404001215414055044030103113404ca01c00261341405544018014259903c034040c9a03009810001e50402d8001c011111001d505070345e101d041c0c507010310541001b0382014002c98100000c0700400000d482c1d150400c1c1d5142030403150f0190300c07004140b0415280403d01e1100d0800c041c1005a070aa26940040e18035180d82e00 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 71625236 1250 71623986 71623991
    0x1c06210204020c070e0109150f0e06090a060504020a0306081b030a12020705180601120b030312090a060603030206150303041d0601140d0b28060c0c03020d03120c03060501050d 77
    0x1841c003a22454213001c4d0308100c85c0b9404403400061400e10329130049550082e03019074100083d03a1152007821a80017807003050310b480025070000740b032841c01c40b540303580c8684d13040c80000d040794550300860100d070041c80c00361020a03560352080c80711120411a0b520300300a420300c3c1800c4c9a0701d003004240c0b0b0304101c2800411b003161101558410a0003071140c0c002600e00500820b1003821010452003901d441511543d0101e01000c094034013040c2c55025140b0005806002189403143d540703000300c0001c0009040c03251a0140030010300015846005880013140250300a100c80d0a10702c54100480e651074210911a0344100410080c5415035203802c4004961038030300307404550320700d80140c8000c03200400ca004c2c0c6010003e41c90b603244c1c14603400003411540c10780d01c6201c6051980011451040078140014884411107020003d19204091a1070700c0d504c0395244611440e50390b800b00d800c0001e5004201c01150011111086460003880b584510380c60910381800b14614000000e00184244002c0c103030142d4 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 71626486 1250 71625236 71625247
    0xc050a08150324070216050f0102100501030c06020f0c0102060103061d0703120207140f0f060f040303080a1b090605032a0d1805060a090f02061c0621020402 69
    0x42080808540c040010b41900c203140b0309007122041e080c0c00795001c81c0550382d484000c42d0340075200207107614206004406a0421030f041c40104041c041001019034114461885030703940d00c0c1c0380d0740911030080d0301c90340451124505014020307052546040300c1d211b0a0340700c6e0480e459660b900140003411607410120004988050a141200f1000c4806484020b2b110783d240000c1048400e00021072184020385c01d46110640300c11601c540d54003401c58070f5900000941500d111807518140342d0b6501d0748000c0119180110351081000705800c00c0c0c0c0240c2c0414a80810020700101d24000d51041e41e003500080b44080300c151a010b0901950350044008100000c40000c21506205410507000c1d011400012450100084c0f0041e49034450f0104569013420001d29003169194104894045503002000c1c100e25074555100d8401011040820785285900211100c050b8886000514504090f21021002100c20604c14015100568041c16921181e4180d80a0041040625582055046a003d0f81d0350 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 71627736 1250 71626486 71626501
    0x4090c030b0d03020706020c01050405090c0d0603020315070810081e030d1401031b0303091403070b0c010c0e0f030c0f04091e0507060f0503040318031e02090a0c050a08 74
    0x7030544580c030741d8100e4540d08658003803540009004044406a50807501e1100f2023500454960090b0310401c2c3d0001440404182c00501210103003645106850340001c0a65403900040d160081d0301320211200002c2e5028481400e030b0125095070701500c601412100149031490990303481d4a4605c1c215640e600300310408040c2c140600c01c40c7d481c2036101340103104031040c103060005400d00a00c0111540e00d9051207150041500d0380e034050840f6003544a58079024500700c0002c03007240c0100c00c0710f6410b004000780455010300b080081d040c03503004000005100c081082c0c0240118405a00d01762142c03901c01c9100401d646d00203450b0340d02c60300c103658042d00f224003030000c14003606d10010001e03c510701820004072200840315980c52018010011900c032941e681c2c0055420305060740c41000024030410008010030b014000030f90354418000c4c800c00f4820f40d02e4035030345c22240c005080704a00d070218200e00070561a210b51907a42040b44000704200109042e08040e01c940b181711100f4007844081c40000341407 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 71628986 1250 71627736 71627741
    0x90105030a0b0603191a030a1416030b01080607030603020f010c15020a020a0b070801030f0201080606193b0906030f011a0406140312130807030c050114070804090c03 73
    0x106010f02043d440c1c0c02e0503055507140c080d420500b81c0b000361500180074500c0c07821136a8908900d0b00a070103407580c16a42d0f20b0b1121091210841001030f4031800381e40c42051044100414019400340070b094201c0c6d410051050300f0090003030a144105420103000f80096900d0310b403034070f40458003400d01346540742007490600317084405040b045218070b02c0814007101c0c041e000f292580d00c80c2e05c00c03569000d0550390700005a400c0802030002074003030002600c044005501480d46940c00c4140142a60b050280d1100101a02d50030303194410006140c801c104000c4001d00c074590f03045811200c4c0702c18910102a11a0440a2141600a4030030b00511010510b240c409211290109200c81c00920001e80c20b4108140da44440708810340c010303032600000081c03540064101882c01400100600b00110700981300304901e42090210861329078001300005100c600c1005141c0046200780e0088500f289801d00241203540c1c4440c2c60368810508020680028280408131001d40e11000d00001d100e55003400704600 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 71630236 1250 71628986 71629001
    0x601020313090e0f070905090c010c150b0d120905090105011d2b050307030e090106020a03120b101101050a0b060403061802100804020910061b020d1a0912040b090105030a 75
    0x20303001700000442d0030074142c1c0059200b0305401080720558000500115071000d000c0d10090040c102981411400210030340041d620410700809010f03284042d1b071110f41d4024240c28150000c50000d81e000c005c035042420819006103c01d08164102c0d4003005a402208150740341c20134131400700725a0b80d4802a11040e82988030601d04104900c01c1205071801c0395499003ea101580883c890840c5c0e10310510300090035506803150f503806050201c001d50380c15110040502c40a00403242c58020341c24158590384c03060240d551641e5101c0c003483d240c3d03070845801c5410240c900b2842ea4180030a064040e00c5040484040706c1d803040c000107860700394944030360071304a0b51f4030004d62207102c14409011080e8004022800b69000320b40c01001e03529108880e040240c81c62040101268181c9447c1400103403070790000c0d01070350002e03280703024080307103551200404541e07030b40d140229110001c24000c04034802c104042d0900c840c01075842c6880c0c24008451040d006202d10f280c100a0000f0000d801d20246420012 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 71631486 1250 71630236 71630263
    0x708090f070509060d0b040804180c0f0f110102030907030308060a060f11121306030f090506190204030b0702010c020709060303050706050702010f0905030d0e1204050402090a080616080601020313090e 88
    0x1b0b80500305440c00602030b0b800f6200b041a544000002a034440310076200300078200300c16444000341648441c00907030703200307016507210800d00c06c40102100d603024080c00110f05c00c00d1100302620803c1d00718a40a01034801c007130004e50081a00e508103101e80368001d82c02c243e4140b0701d41408919940d101e0440e0f0315140540030003c05000c00800ca039250741d0044903405081d02c0b030136102403081540c6c0c1341c0d5031021161640406070640e4003510120f11445a0103110380442080c181c1d000d82703850780300e48178101e032001d003540e00c480182c1d90340360390030381003503040c0302502c081c10724441c0030b20880b85140c8006020340240403015058a50321004580601e0007540190840420f26030240720319211820310549a80100e0a4043c2081c00c0088a6640c01c40206044035400d0903983c015007010704000500000790015500150000043c11001c28011004c0005038401c02003640b8440e042440e14400500b100c030007503d0315040d036005010316070b070051152034248155101d0f000000391030200685698509113440141a = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 71632736 1250 71631486 71631503
    0x503180d060f061d15010806061209030403031b03020601141807270513020702010c05100203040501060905010605073203040f0807050d120909060e0708090f070509060d 74
    0x6007652030881d00311400b02d602c0032605503141308144540c900e151504650044050384803038034100496018900f01074004c1d101a00e11424244442c0d1242141300301030350b10291503400410200200350f4004014035225804002120f6101c103103540195650788180030fa11150042c440c400004ca849424600c07103040c20026240d1140d041405003d0400c01ca00d0107415810405403aa45400c08030048504049403000b0300300381c00795030700c180004009400454003207041101c20b8248502080d0304100714014448550801079590400340b40032400c580843c0e100c0381141b4140300040040315000429501203e4002c0c4680a04402d0b0780d280c030b05203050b5900c0c00341000420107003400035204004060000d6440c010302c140081754480e1000b80d5941058410340303a105c241c1c01204000910070310100d840000c8035080841d08186c803003490f401610b40a80110691280b14400c2000382940100b40b035401c41c40d9a009441c002c41c4401c0010345410450060b2401002c514021440549401c2000315400380c002824 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 71633986 1250 71632736 71632751
    0x40303030c0807020313033f110c060409020c0a08040b090111011a0d05010f0f02073e030c060c0609070b1318090501060905010f0608040503180d06 65
    0x1030001c1114606280010b030b01a070000710b04030300010844402c000711700c0141400358555903c041608542d518143d5421902072024495125121441450113095a090114110440100600030341e01c0b5090052641e02c41c0c03040480740e4440344100c0c1e0955010000150341c40000c1d800c01c6180c5120100c00401d000f04c00030740003440c8010b1802504410100341d0340d040003803281c14045403c0e5031400480c021824454412441d0b50b2070458409100380b1300c00c0d4004101d00d44282c07104003c540304050b010354466000908101048004181d040748560202d403c00c135030041c0040180c010383c4066605500745448901d2030030140c2d4003001a200d0f8030000906d03e41d602c10720303000c0080d21407200381c4d10400d9070300c00c0c01c8010900415241c10342c0c0075040d1008000c40c4062030100554841d1181c171407030500c2d50383d95003201d502007039080c01840c000d011804008616540b40c414264030206056022108104044043c0000114044100c407921a42142c0329100d418801b800605001c00462004103500e250280 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 71635236 1250 71633986 71633993
    0xa0507031b0504090804050f120a03081b1207050a050409020301030c0302090702030c1f090812150a050a05132304062a03050c1902030306121507030f0902060403 71
    0x10282150045900500041e603a0703109100030b443d95098020000d100a000c2800301d07013040c0d01c2c4d004200000600000301c451484030303010f05100700a00c0c150300090727042041001d640d40c189903c203448001800b84514080c3c0d40f4012000450020700030782c0801c6000288980700c24800d009907000b0b8a0002d204542e2941d4921701214211035512049010b0901d40000038074481c008420303501c0c0c0070103034000750a0402ca11016060600e40b041c440c6201607070350701a1080891201d401910b85000c90400c0c0340c2d450b0a1684000002800403c640c038851401240107100a4450110000c11190152490130a0035004034221000e40840300709415103200d0050b00c00d050040500c2e1050140b80038190400080b03200600c04003d40781200c0752403222405000e00c40d85214440d905c0079a100d180341420030705002c40a0702d40e1900c0010341000e400168070101c148000e514080111400c07041e11700004151103400c40f54444a0414010911400c0c141c0d910807402d00130042c0e400006c0f03901e07401001950740e1030702c0b840d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 71636486 1250 71635236 71635253
    0x70801020304050d090b031803040e0112050f12070821040317010b1206060306130c02030406180501020a0b07050c010603080d0b040b09131406101a190e030a050703 72
    0x11410b48844c80796000b84c4106a0148a82c0001c0e40d8002403460b103960b070303007600c0c210240c03007119031416140c402000005281c8a007004054080e201c501c070304201455103414003030f00e05040c600300ca07151904011201950260754100b03c646103907102070840d0300c2e2061400c4080300c0e0042d1021440101c40f19004010406074040002c4490f5400c0702c1111503545d8032009404014020103044160a01c2c4100c089481c1345403d40c05181d0040004296000043c103c0c41c044044c0c50440c04d4040142e0f00104050008a0b00508009809440845603102c80b91800b00000c3d5a8040b9000c00303003440d0500b40201e01c0243c0b081c0111640141103030020300107155a40b0b408000e80d40814030b10700c40245032200c00d03821440c1500803040c0f6504007e1410903113488041d02c540465911a5041322a10707840f60403464010780a1120342c1c4190469052400c0c802c3c80c2601c81801480380d402c2c3d1007200201000300340d02c2d01d11682240000c3e51b01e82c6c80c02030001480d07000032a00e000bc4d8008040c12921840c030300081003002d40f1 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 71637736 1250 71636486 71636491
    0x60910050301050901060203030105060703030f0b0d03030e012d0506011e09030b070219021201090c090c080c031012030e060711040e0307050a0b062101050403030506100e120f0708010203 82
    0x181c8404c10161b071794504c101d03220f0200f80034040c0d00c00300400801004c070340b0a0300200c00b100c0d814903001400d4010800040d0740040386080840129440d03142c0868445000e11840540040418800460314598041101820030b0300641a403055510400304074030f40d100d00460ba91090001c82d0340e203900319044801501d01c003003034070084030b62540400014025920110702e00505142d0031030200c8030040d0a50030002840c40d10f031030f910007641d81c0c1e038446070101da00c00180324010500d04c100082e9200b90310720010b0441c4402001c40515000800178010700e014240001021503202c503486500145440c80c044403205102040d6980c0200082000d105000c00e40310f450400b0301003117904000c040e45100c019900c070f000d107000140a54100d0303180e00c0041445241100d90000004080c0048015142d401c507a120103483c10080584e959402000101500b40c440c1c1d94120740e0468895441c1020080000d180103112003a60b8001c1020070001c00e840074080005803250070044094035011074441100f20b0003034008 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 71638986 1250 71637736 71637739
    0xc0907110309010c1502071113050103080f0a09030218090d141213020a0305160e0402060307210f0b13090302070b0f0915071a010501050a0c0206091005030105 70
    0x140490011401440a205a032050350095414415441c0040d200c0984490b0f0030340764100b6050b88151400168801851441e20074070310000b155009800740500c0402c501c00880c146440d0030010700224689500762017040c10086641960303501490030031183c0d446e142e03000942006082e00c00c50401681003c41512032094001110910750320400221746d043c00c0340c41c1640c048034040100501c4031060400b501e6001c0e08210600a8010059012421b0400c40342c2c415200307a00b2030704c01405900182d048020051901603194030070360030b080c0c002803900d20018100034144895450741603003141381500d4802560064410800410b1106507114010308411180244500c1d01d00b050890b0048081c4140b0160725015401030444601704803007950243c0c400428104003c0c02404200b815030b50300b502614030054902380c0c0d00d4441081d8a03020044c03030a601c0002011102001c018000703a607000040e1103070032055190020402d1614000300b045841104101da400600c1894107070036160300007000b14102c407030 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 71640236 1250 71638986 71638999
    0x6010e0405150c030705090102070512071e03110127150e190e0907181b020c01020607030b01090e040606080d18140a08010c0801080714030705060c071203020c 70
    0x40c003011585410030103c8825810304410301c00b086034288110040c040e0940706004840b0304584034400146019403043c4041d465a0200798140b1902422406007a030360b60000000d1074640c1c2c11542e4403900e1484203105141003046100210301c02c1c95000c44815140c1c1c00f646000740c0c0280d2541c0805410b01c91601010b00842e410081000702d505004099800140302092000300581c1018000007290750302405041e0740b44904034020030703001c07264240800c8016084000040156a00c1e03140045040790302c840c2000e6400001000c1090390b0003244041d405095480d00243c1111030b08010b98581c05280c11200410400301c0c200400c000403980154280c480100850b007103040309003812620003501c000301075160f40d0220810059408081c1008100010003003a0140d5282c0f0351800b9070845000f5602100022032110040080308000c0c484000941100007880c17501310001c601003680c3e40460b1180307500034480003400e07a8142600303100c4d010140040255030060000a804c00070f41d039400c00d000f101c1c85181c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 71641486 1250 71640236 71640253
    0x6030a1b05040b0301031e0203030c060405150603030d0b030106090c0201020702040f0203091b0f27060619110f0106030c0e06060415030b0a080706020d020f0303012403090506010e0405 81
    0x78020380944046070041c1840b10f145a0031541c40f0340040451208110911034141c1e010401039605101602c01110000002d00541c0341030305107a403401c042d00e1000940d504080e0180031403920048115a00b0503020301c0c02240101c040004640140800d910401c0c4103407a140d04a5503003a0306400414000340215010300142c030015042c40100e1100f034421440540c080301c0f22440c072890b030780a04820a1002030018103400c803040081030010380c1440f003404d0400703188035911114031200078440d038100d00c080d2a42030500710483d0701030031880000d24450051080384004524042010010348100d051050002c1c007078265685451000481035000d2640840d500800050440c242a8140c40031100f40e010b46441d0914005401d80040c6013001c0810b801420662020441103000c020600041031a58000c01d80c81e16545c1000f0704001e6921a000d034503070410001004124000442d46c211001e1102d521154201c910b6403d9004250480004000d40070b5080001408024805600c0c401c9018105841180 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 71642736 1250 71641486 71641541
    0x60902090303041203090e1501030c020a03020601060c05100c0e09070c0b06040506010507051b030c04060e0105011404081603060c0305090a140102090301020d02090a061b020d03030b06030a 83
    0x2405002016901644140001c1040200b400d50341d14046005c2e007003010485460305e000004000b000c0710764070200f08621400b1042940d051003000700d1418140f015040b180041d680094542506210306010460001007000034803d06011140c6a10100041003002c85000c031009001c105c0d100c142c5610400d042c00001f81100d016000c0d02d2001c40e0702090042e91540c464041100505000e0416810404207100c5400000c0081009001d60142180c03880c20040c03541003003500d0910385110240c0120300700b507410810313144c0c4160720b0b40c152182400d1400b40c0c0c901450070704d40207000d10751080900f0b114040304a000c60119440b55401d0381d0180d04d0600844880082c1941a12000e4900d42c2c4140d210000038800724040074a01006802c078030300054500900c0c100002d0998000d500215480b0703500140000741e900d0031213182e400600310760600e843c0202c040429500c5051801038045d001c0d03a1140003400405102e90300c84140b0070710090615440b428000009002080041d21102141f41c10a03c0791042 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 71643986 1250 71642736 71642741
    0x20c090412080a0207141609060e01030609060e030a0806010e0d110d021f1d0301050403020a08130504091101110102190311040f0e15090f07051608030106120609 71
    0x140781c00c201c0c11280186a80800c507140c11009100d0240c00ea8280700c95400114030240703500780102801d001341409998005105541e00c116400501d0040c5803d10401c0b280c0b07445d1781c030281142e401003000614218281464006424901c1c11208940400a428200e59400040d0075003e4102a6114980c02c80d00c0400c0c004030780c84c9401c01404600341320805c03584500d0810340044403507102811540c4036609800c00003000e18008004480400e000321040040d0201104540500800c1100240518205600c010b0b441c1c086810025062074000281c40c04518981070600c0d0003000054420081c01409062001d60520ac49480d14000b89114807000f892100c14020b90351501a1510060300d2032008441c1600100035690401c00014001c0c00001050340c0b003460541d008000c0c07070030a03800d03a1074844060956a914040036601c110900703401d100e0540c003d1011542c0c402500d06020380e55010101c211521030620348401440107000000114189034402c80c10000591110720070300c4040d4940f20403005 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 71645236 1250 71643986 71643991
    0x41a070303061203051b0c040c05040608100303170a020403050d09030b070305010f05060a1107080705120d050f0f0910020d0e01021c080c04090c05041503020a0e09071202030a050601020c09 83
    0x402c00e06c010206014005034441c00a10440c0440307040e80e60b50000700f0281c52034010414003056020400704441508015503551020302071810b1245c441c01d40c1d5024021016916154111004440000d4054240c550407034001c0c44d000001c583e03a1064641008058100030b00046601e009410701062181d8001c1c0100303410703550000c210490842c142000c1c020140c2090200f1400c001d409409003513448000d00a0f0307805440003002615500382003000b0300c00c45030980c00b0044a140d106050f59100c0f41d6005007a1540080c0007001907070380c1c0d0940e00200880c0d0003018005948144a041201d200540003d88007003840000d45500000d20200801681c84491890045038081115140880385c01e100d040010303800149000110304060311216841d0071124090040804210001014424040300d180700d0110340c1074070714055203003444444006040d4410707081c40300c3c00382c00200c0101d81c0d5503000d02c1510480700d40e105011912440c0c03070120800a440c042d10341c24054003484621900c2030802011061 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 71646486 1250 71645236 71645243
    0x605150409020f06090607140f12180103020d0b060c070501120905071e0e0403020a0b0a05131709060706050a060b040e160e0d05030307030c030608120f041a0703030612 74
    0x4802c41101004e01410b035110b403d45a03032150b02080014000f070703000707a1080800c80600008080703903840341410610344a420766640018110600901417006c8080d8216002c25100b881c02585410b8070403c0703600949640c9c2100c80d4040303404110702d1030548000442d4400c85d01c0c260b0360800b0680801001500300e4983c8400079010303030440c59080c0540f0401a941e5112501c0030654011403680d00d01e07805a00b200e05a038100e0040c1c100061032418841061407254000c1c0e551101003100f420030709459000b00d18052801001500b000128402c000a540240c403010078002d014190b42d00320514181e00201030480f0245000b900e1300303001040144207542502c0950712114051101504c0d40f11000350000404480c0130204180c0b80980e2321651120120000d1452003100110740700d0402c4280a025030740340c1e90b4444101071038080104106040011000400140003070b806568000207030301c5036600e1085400441c1e014042c2c0c4e090f2180490399200805116001e5a400c10007281c6030814001040b21044010303 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 71647736 1250 71646486 71646499
    0x5100602070e15030304030302030301090b060a08070813050105010f1a0a090e0910060608040b090114061005090301050106020c030f06130206031504110306010f0516120504030c03060515040902 85
    0x1400a580d4840c02c80303400400c10750041200c482c1000009256034080c0d04100d00580010004205600d400e00a8074042c15045600508082540c0d40c02045038000602c0c1000f00004600800d6000c001c082801280300d401200900c05917858111a080b240c4c050b108004680540307280b850340c100452026500d55113260b55a80740b80b6441d040035110b040034090031130a0640103006000d01298210b04c1074000600301502c40340d94030315043c106991880c20081005846da4140302019214551208000e58401e4048032800040481510115000d00a00c070280390950319220010408540000e0310100d070210450480745008015aa4151038500c00d540381540e0308507078410040145480400f540e07022014040b20380030380003003000003003e454012442046800d4000140300165030b0080000381d0305030950074840d01d0900301a0704c103410080c4150000c0e10401034a00c07401d4845100d501111300031a0000c002c0701000c1e4490401d140202002e44040310900c8213420003054a0a0500038411002d030001d011 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 71648986 1250 71647736 71647739
    0x70906120e0d18090906050f060f01020c01050f04030507080a0b070203040f051c050a0b040c08030405030c0d0201031805010609060f0b12060f0d060b0f0904081b1002040308030601030510060207 85
    0x380d49071018a0150140c410b440303c000303e80c41040740b060042d100d00901020549003800070350309040d81c101401545c002c85000d10340d801c099030006a0185e2007002880c2090341c40c075024031510028091030308028824004e07210005203a000020701117010a000f0010400981c8460350241e0baa031281d0b01c81d000d000001c6050170401d503c0c0412583c0740e0000c0030f05000305000039641e111350410200c96021242c10007010140b00034001c42400c15005007995000852401e41088006a0b454005003155441080b10040d000116440fa40003003140b40b94030114085410a2440c00601900050145100f010301e02400002d418000502980480d02c9400d801460098402c440e082140801001aa005400207181c5102500c0380c8405008003030203102c0000b11405000700b0043c81c800c994200921402c0442e0900c004504c0c0c00d802c859180103030003440354901800a4000d800c0003000303c00705d8070072072000c5070000c00c0c020504000c620402003680c0030000e03946ca2460a1004030307994000c00c40140c0c01001c0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 71650236 1250 71648986 71649013
    0x10311010309080c011e0b15090a0302060a1716090501080405010e030a030b0406090c080c071712070f090305120906040b040603020903150c161109070906120e 70
    0x4604000100626011401440329120700b0380e00c0e80100c0e1031480d9603649542c002e40032a40400081155120404244492028440042c1885942c5040707807195000c002640075140e03403040c0c4943d00441d805040542c403000302c07030b40140411345d100e00340c043d0201c0b03ca00080d0601007a450340c4d80b00521580c80d9071061b031781400c00440d94108018811a419944c03800000344c000c2040001c2d00205000740e80105500308501c0c2444191810780e84001502d43c00d08015007403040c0c00ca0a0140e01500c11242940c440141d8144140c458007461500441036200003801c82004401c0348902c3d202d070b101600c681082e006110300840729500a440041c0c01c5400054100104c0e420410003840c11010041149061903100d03042c40c0110f606c42e03446000401e038001100c001c40c1c10144041d603282110402c81c10740034902183d81c00850300c2440342c407010008244860710100001030342032000021018094100a2502c1c0790f014000200c2d501070500030480080d00400312000300d00500d982e000c5003202a00c00484c0c1002c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 71651486 1250 71650236 71650253
    0x5040302070303080613090b100602070b0a03090c0b03010b03180c030615031204080123040807060507210903110f030405090702210919050102060f0a180b2d0103 71
    0x5d00c010780c00b540b82c1d40100c2c0310069034000c200e480ca009500c2080c42d41800d90148444c0c243c2503000700c00f90741290504001c08150941078400742e0880307003804281000640341c026035040700c54001d00307290040032001150f0030b501c0c20301a61242865140b82016800d03202005aa00c3c203000b0720441d89580300c200000c10310b18200d03814283c443e80142c1110020341211b440c1d00080e82103500a0321980e03544450074046090030701c8502d2044807900d560001c00d0b04090f1103034949031003a00c0014080355119000315071114419165040700048401004030885641c41041002e4402404254001004a945030300c04030008580c036400c46640e1401180340c5413a020602c01102c10040140055000300421201c140c0c55080421511074400b01e407065035020203200b04002c11031403111590b0000c850703c03024804d5903000142980c10407550351165030141c1d544074015025080b01c00d140040d40d480c1a038200200100300c11014041d50b00070120b007005016a038003894003595500010603070040304400400c0420401c6 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 71652736 1250 71651486 71651491
    0x90b0a0305100f1104080a0605060d0201080a050705130320030303010b0d0f020d1b030c020d0815030c10031401050402030417030403020a060603110111010c0915050c0d020c130504030207030308 85
    0x1590085081c0c09062482c0c51360b5041030b0320850b1a900428001000c001c41e502c503c81c1e00000480d140e10191003207400081c921140284040b80695541011442c1140140282c0d03003201c0c00301c0d2a0760300c141d4a80c0743c010074081980c601d00c5d040013151250230b091454040142c0781a036543d64050b5081c8808032020720f014100c0c1140e05440181d01708001d18480303141e07025040e0104d0780c28070407400701c00650748020221034000701c8040c215005a1902c024850b44400c03180e40012001f45194007040c1c082c400203040044c80c90807264030a010071002c1c0700194040d04003469030075181e0901c8030b26030303a24428042030384021200145806d020301d4802c00d01301204c00c081e680060003403046a40311740541d41c0d000e04883c00307500181c1e014003100000900e25073f813000c0441c1c00b804401c0c00134851800540c001038901c40690007140d0b10400c88190390007085120f00c05803505a010702c41200c4030032800400c00781d00e0b07000800c0e0882c01203a0660010100400314010b0500440d40355005000061841d00d0850380d00c50013 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 71653986 1250 71652736 71652761
    0x60102030f07020a0906090e190503071218230a030f17041a03010504050a090c090c050d0f05102102100306030b07030c0e0414011806031b090b0a030510 67
    0x160f2004205d4003000e100c0d0002901090000041d60100d031031342d103032500b02d00b81142c030031754070184101500240c00401a159800e41c00781c0c0e801450000d00c3e1040d01d04c8415990050b20300004084000b85142c92803a42903008880c1d220401d60394140131040c000c00340058000542102403034003024002400780d040745242c6980e130300c92050425807581c0ca404604800c094850300c0c4003a002c030041c0107500d014403501e80c03c00c2c0b070941c08115900c09ea6841e00310b244501c1c803030300d8a0b881d0346480340c025160043c005c0350401c2c0c1040340c0800c03002c0000d02900006200c243c03041c188039900d0107c04500d0406103521403c022403003070f406482c3c0c0302c3c01d5803c00c08880042d411401c00c154640e5400070014111290303060040c1078607200400e800b0b0410400901c9220800c0c01c0700e208504240e40182d83c4c4021451030b42c10b64080300e4858100040f010081c0c1d025215541c0014260840741d003001c00c074004030a80308000c0d200400070070f00800081c4001c00040724550701000c1c101e90032500d2000e82c213000c203078003810312140c5 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 71655236 1250 71653986 71653999
    0x1202070b04080703020901090207021e040b03150a0e0f0a060f061802030a1a0d030c0206090603041b05100e060c07090e0a0c08010203011410020f0601032405060102030f0702 76
    0x11150303902400c41d0403640c0001e41d01d9016100500c00c40c07a001074010b0240182040450030515181c0014424009131100d101170312001180300c0015031110303000000001e4001e42210310141c850319080f9004001104c7e01400e5918101909000c41d10100307100d0108200034008060401c410313101d81c0014021034019104099886c00005070200000c44201c0e294041d0403401a100d03d0000081000d8a1040041c038503001c203130300a4559940c2e80c11103500d041c9505450121030420f42480410014400c4900c8580e00c0100030080008101c985290940313940380340020210050b81c2d50082c004c96901003007842010070401c6403c41403504045025201e05540c070402c03280c90300c0c4e81e150100119045001300054582101190405104007100c9520007008044001c51a41d03140442080c11580501d00b820301c00c984001741e01180c07070f10800003060612000429070346075503940c0c641400c1200350554608a800d01c841c44070581400280b00b09846020180c0240d0b10b80122048ca070340860380008022070b48040c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 71656486 1250 71655236 71655239
    0x120219030b04060501080114090304060c080912060403090801020307051b0a06050405070609050109030507140d1e03140a020a020f130e010608010e160302090c07120c060e010b030a120207 82
    0xa10345541d0700c0c041c500030600000c00d5410114054259480032102d4611008180305210072000c0010480702140c29504d08004801914030b0010303200c0c452034914590103000103d45800c40031000c01d406000c0c9200791502e5040d190f035054020b00780d0008813281008120107010007030801001444136100e070070f400380559840e000503030364070421900c0554090700c40e035100c240306115440c0c0007003030a4041c103402d08142540c1807941d0713281603940360036001d03060b5695a1203800441540b2047d02c9501401d901c9180c941151b980c1d111008568482d421003030b8001894032604040b50b02e90401114540b10040d4050305445155809105403100601c00080c2c109007400c808240404e8948180b200b090043c00000c07941d01e1070041d0285c00d445041300c0b02e510036000385c806120700c8181418400c00700c03507064695503074a580741d000040c407a01400c480035040303201000341315842c20340c44102008613034452002007107004c050304040303400ca4a002c0c408a8050744060001030100311122807030b80c8212038a204464807103 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 71657736 1250 71656486 71656493
    0x702150c060403090303030e0a080418020702130504060b0409050615030f0f01090203060610120519020a03050406050a0203090714030c15040e070806010903080d09060203190b04050112021903 84
    0x400442e0180d00040070303c0024001c1607414020307d003180540d28010800c096003a19201d40f00c1c46103200d00d0003449480085000805210b406550000d0380041030610000042c1c0d0130080502000c6800b110a280351060211003441c05100380c4034142e400600410140e91012040d0848011031070806a242c8110990100f100004000220f204402e5900118807a040392040c10700d01540070309030910031601400ca00b00c445030700115201c104020307040d0116032a103920f040306003044802c03409561001d00005500040c10b4041c0c100f01d0096200751010401c03a5500500d00f4201d000a5483ea09590000c00c2c0030014008000a81a1380580060030340d100c07464001f0000c4c0d45201150b0141c2d840c0d40c00410100079443c9190b04259101c0e010b42020296441c03c2c1d03000801c202e8841c00000d200c200b01240210075a80142d008204030384e88076104540d43e09080140324040c80c0b101320402103c030b04000400b51341b42458020b140c107c900074405522842c000e0f600b04041d400002c0544000100c9014000010 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 71658986 1250 71657736 71657743
    0x10b0301181a0a0f0305060604141303050702090109060608071701140a0503010603060c020d02030a14070303020c010609020306031603021818010c08040c0e04020a0e19020c0c0406060c080702150c 86
    0x1440840c84c3d44004502c1c600d40141005402081d081c440c41c980f200702d041d1030300b103040c400d40d009030700c0e501c414411241c80c941561240200300019401c1141c40e00042064000c80c0c3c00710f01940c0342e03a101c111059983c07031000c45245c1d6070500ea045c1e00604e514010040c01c0d001c4101e04a00c3e02004140030007240d200e102003400c4504940c001d035040b0351105566140359030184062809001144051742c03401d11040c134007030910280030040c4080540001042c001b454400e07415220540d18110091100340d54802c0820081d400540312540b003400380d6805d511646029040f1241103d80c040c210701d01c0c006500b400d01f00c00410042000c10b003452072500c8400d5100d03003031144082c080810340341c40f0664205820213010001017904a01d80303440000c0e0074880584c3c0c8000041d070071582d080254100e41e03603c1c482d42c2e0904e00c0841e41000001400454407940c01180850342d0300003071005a0301040020b64595003200c80d0301c4c113000c000d080c0900c1040320401501384040c512403005036510030640b0344480900d07100d00c0c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 71660236 1250 71658986 71658989
    0xd080712020f2d09060702150c0c030c0406060e06071a041a100302010206040b2a031e07090612140106050705061501050a0309050708030f03010608010b0301181a0a 72
    0x702c0c202d0010b000c03807090306516243c0304144034003048061a65040510001c444c400c00c84454481c8401140000448d03442800e0004c44030f41c0d9040098483d4000700304250750300c2c3d45014980c428082c0540030071803030400c2d12448088030b005030380301d0303480b584000305010040c3d110207800d5407119440e4000010100e000c01d0280e005070710840110740c12001040341004007100150124200388010f440800141c0e90000c0c0781a002074000308482039689900890001c00034078949a8916a83c40d03120b41007a40c01000d0184d48a0111418448142803108103803518006049480402055446400b400300c18420051600b4100088c1400030f24100e00d180e1210414070700341e210340c001801c000f44103410400305004003500140c100c0c01c0080b4203149280003070010300030340e0701c48410981d0380c0d502d00c020300500b040044000c140c04000d490baa00301006100b5073307584c002d00600300071944110000aa00e21840201c0e41200d00070a44c000c804481015880c014203511841000002c43d0300070703040b03800c0e520100040c0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 71661486 1250 71660236 71660257
    0x30308130c060518060711010305100812040504051012030c0609060614010e03070807211e020a0e0402150c0c0907030b040f050c030105091305010203090105270d08071202 75
    0x240ca5400c0b0300305841024621032203160041740244009800101c2900460901034800d00b80813505584200b244141c1101c154805503591042c001c43c481c2c041e2461005105a40080d2070a00442d82d0700410300502880c0c0e48104002c1c0741204070400c010038802d5004100803403040e4000b080d00b68203521041d0580316150010302d000f4841002d0b030302c519a0000d81038642910b0a902901e6000e1030f1002441d00c5134a03603c20480c40f49100103001e0600a009069110003c1d0b00020255000940b502802403008802c2d03130480c0907201c5a60080381c403480600b07090344501d81c0102402a540030380c038642441c5412000f0007001500c1038600302c1c81c1c942d9652051900c101000d94000580b0318a0008100a0340c1e0300c40300c020a800d1405d828410340301418400c50b03054420076104100b00b6210000030799001440c414004e00a03501c02b00c01e0005074903040d003199005282c0c0941200d0888900501d403003e1080b03000c030b921029409000c240480c42e010702e056990240d03090030092000d0a0307400841080c0da00196121 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 71662736 1250 71661486 71661497
    0x31a0103051803071113051e0a0b0909010c0905180114010504050904030206040b0c0a050d0902011803031d0105030c07020906120d020a0614040f0b1320091f030308130c06 75
    0x10700317080c00c015000086015685c0010720090400c5034001841000664000c10060014400038121800b6a0842d0303041072009450328035149052900b180c0202100c0059500061100d200021030385007440000d0701c0c10440d00c80001041c1d103050210006554041c4185062103424000040c09a882002461280b0701075000f514942c0342c00c1c608042c01103c000c1a01a091405111441d55640d11400b82c54104408801c0015401e04600050300c541101130b100b060140500b540100805910900c0551401201d80911640c000d01000650ba80c2c0411101c4000301802403020502514014840c65040b2070040e10103500b070620080d80c0c80c1410310300601000941c4c4048802805c1000d41c1c8150b01c0b030103c40820000b05410319a89808540c1d41442c0e02070034402584012503010102100060441039101284c0000680704a040c001c0d4210101c100b00c0c4901c10302c1000506611103c1c403120100339440e61000450b5095543c00c1c3e8190f08040c1403405202988080200014540c128000113800241c648 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 71663986 1250 71662736 71662763
    0xa14030901020a021e0c0609031002030c1308060721090203030406050901020f06150108040303062c06030a0816050c0411031b04060203030a2a03050702010b01031a010305180307 78
    0x64170301a490466076600194400d4100482c40010908200090084030070940e10351203680003a240001445008210500c00400c1c440c002000c0700042100f10300c40c02c03165241a80d207048840d2615400ca03102c1000c500e104851904210704006585020f44100c100040d4140e25900480c2c9507400641006d0081007000689400568040102360203144000e40104003504d4124200300101c4000301055050040c07020110b010107000b900450041c001d1741c060340c5c0c2c2d1007101902040c44003610007180d04440c0e08140c0402c02078100814140031003900b001c0c0c0c061402d2403400170f60106102060301600c00d030151030640915980c46005030940d030414040d81640344d007001d042ca800488941c0c580241181d01c1080200314054000c000d59030f220030f802400080f0b0400d03e40c220024030044402c00d00c02805c800c96200440c64041d408140038400302d90003081100b03180d00c015170485641004011422020f0000012a984650440703584070b03c0400789a10a203101e00c114901d1604950800c032040c0800d40b02 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 71665236 1250 71663986 71664007
    0x11101805150703060806041203020c0a06090b0f010b0c0c01050a052b0b0105041505030618130b060102120d0506031504060509060609060d030309030e030708010203060a050a06140a1403090102 84
    0x42e1394041c159080103051071303041542e030b08120701c00810070140a06402240c1c0e00840c08051091201c030542000080c03101038000c2c5015041da090880e14001043c1c00c0b68004500030501c80c082d60070034080714005043c0030b282c0c00010750b4180c000e0310920003000300400c041407202c007565100361a8030840c1d000b410f0103d02d441e0704a10583e042c04103202c1c104101400101324881e0400b407003140390015418403a40d03c0c2c03100c401142100e03144450f21880b001038030007400301c000c00c00c40400361000c1c044c100d203101a450741401244ca440c0411401c3d134030740400b440076402c5001c599000c980c010030020200c44070081602d80151400600702c034180c510aa0f03e20403c0204001030000c1c5a03c0f04e4211240401c03071070048005266090401d4000e420150f40e80120b000b0140200c25005031030600400726100180e58245990103540125829401001140000034440c14200a1801951070b545c99589a20003c010304082580019104404124000007c06002d0080c00d0045010704400c00c00960381d2002100c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 71666486 1250 71665236 71665241
    0x609111305041103070c0c1205030c1b0f04020d06170304060e03060609010b030604060b031003110609010807141603050306091b09011101020f031003050d11101805150703 75
    0x1d0000380610306098203181c07000d603183d0480b03520800341d00703214040d00040e05150f65080780c04c0e004030382c2030ba080940309000d0240000150480d1040740d030032500c016003412840c0506d00820551150054511826090140f806ea00070780050071001400040082d27607001213045c0356145c200b641c506600000340902c2141d0703103d61020f14083d001d030010000d50502c074020405069051203141c00000d000b002141031036075183c0000c001481c0b2a98102c0d01d80c01d00d0541181140060b220840c0d01341c01980300f10a581c1031210556102000517103c00300c080e540e01c0810396500b14145036001c10440b003000b104400041e5020b411217180d00958502c0c1c0c0b80e150840610041e9a0041c0010703c100c03c0c038048210780465a1812911800e4003032a042d401d507908460a903019000b440c84032030707207040003104000c01c40c00c2a40f0000c01f1240940b00b124540b50500500307650410068445143c10340042640c442c0740c6d840c0760000c0b620403901001000e49061561683c1e0f0502c4070b1000b00901c0c03d007110051000450345030 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 71667736 1250 71666486 71666489
    0x13090b1009020a02030708070201020a1208013b10030c060309030305090109260d0e0307030e12060601140409020a0206151002030d0902060408100c08070c030804021306091113 77
    0x41d4086140042401000c2d540f4000c80200424013000000e080c021640709024100013250f014031200603105101a02078030070b1109001e02c003818000f0300003a00100e039422004080c0d80f140c900070070302003941c4007044550480c0004d24580c0056400d00000001900180009c4010415030b90006004882c070718004003600d00261400009a061042d080b0208103410a003059608800c861402003526130005030300c02d03000c0d0b000c810240c14034140041d1341d664404001018841d2095442c0c11402c442d110130843c1c1240c0110f110705c419070090b40005d20550240b41600f0641d40004000d5081965926100c42664000180c000040e0030400034040628404000406030b8181192400901045020025602d000d4172025446032070b11032901d00c055460f424111006440040180c0b0750804c0e103c1c1d2030001500d811580300d80020040400101c03002c0c032500200b01c1c6c41b54960385640c00fa8495400700481c0f4074292032074008060365501d00250041140c8680f46c038421903402c00c1e41d12000e8036107501c3c41e511000d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 71668986 1250 71667736 71667749
    0x2030a09060c0b1303020f01020403030306030b010b030c070b220f05010c050c0d031d0a05030c191203050406141503070f0b0906030a090b0f010513060605030a0b13090b10 75
    0x2540d2040006100340700c000e501c240040104030b070180c4c00d400c1c124a0000340032203030003080d440002e02000745070341900820252401491400307500d0b40d8a41650f800d9100885031650381c0072040c09400b00103098502e0f403e8100c4808086412f4039909110314013000c0400d804100c524508421204003048401e000300704440c22241403081c108020035480646070f0030070038400420142c0c1c94514000a940f100fa035841703024100c074100c0c3c02211151506075074a40c800408001a071042040c040c0b1f029602030149160640c0c4603006c0c40c4dc1d440c0c0c14900790060100544116081e40e1071b07842214000480858140c41121070041550100b0251014107041c00c0340c5401c801c128183d401c605100c003074840e00c1102c24511090310030316640d6440c4650340c0021b0010000c000d2a5400307030424004a01038003c2410306984c8221081002d2140e140160022201c0c14880d0b00c000c500144001001040c0a0340318041080001c0c060206280c2c540a016049032041c120407030b103100e044018440081725042214014181 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 71670236 1250 71668986 71668997
    0xc130b0924100503070f111207031d10030e01021c15050904020306060913051b010f02030a0c031b1a0a0b030a0f0221010c091401021212040c0b040602030a0906 70
    0x3903405000b00140b20040c169000e001b04040410f062a10070a01800a0301001041e5440f642c4500d4200505038001401580040c1c84854540c3d41440402c244100d080002482071000705d4032394009170058024100301c0382295600380314800061031065900c201c80880c07034400103008603032440c02950030210340e04414003a0090800704801a10001007854000c201210118459a82e071360a801c91020315040003441c1d80200c0518002c1c01e407074a80d28140032182625041130080307410030126540d00030080040c00244880e090b000100b0302603060820340c102c80d152220910002d60700c4070700c0030b000d6400200c900c40002204201c03000d0211f02c910302c14004101c0c081c0c06441c030a5100e00489001003000a84986010701d080f504510000d240343c10700303042620080c012307040c031024090004203140c440c1103c01d0f14078000c80200d562021515000d200c40c3c03560340c1414281c08407510000301740b0061080b210b5141c00800030034002e000310050300c02400b8550081d9560b140890008102543c1540039070180039 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 71671486 1250 71670236 71670259
    0x100c210b010f0f0804060b0a050303070605150603040302060a0b030705060f03090111040308030106050a260714130905130204020c0a0c0807030314030709030c1404060f05030c130b0924 81
    0x660044d0100e8005411501c00300300b807042c500004220948a901269140c400040d03881c0c20001c0700d8200600c5082c49403502010ac0c0c5090301400110b200c2200c3c0200182c01480014a0458150307005c0c2c24490740180840e054123840300003050503035200981071036200d040802000b540900074040d21b801210036007001414145036544414560006000301703400c3c8000030984803001441480c00701106c09081c124402c5001311142d41d0124980c007966240d0019001c180754004c40c40054045800002c000ca9071f120400d41303041035402c01818040c2c4014ae41e01c080050100c0980c0d994000f40001019500151100c4452071030561401d0f06180d110200329048a070702000401d803c2820346203541d0f44040000d50707c0d92f820a003200d034501030760001401d4150500c0085200ca260a014180082065500704170458036240c2d503240e042e0700c500c901e0b03a01d98800c0050340d00138244400300a41002c3c1c00340340420f0407011140002c0020204441c070303480c00409403414100240556140c2e090b44d41c42030300c000f00e801 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 71672736 1250 71671486 71671517
    0xe060304260705160609150225050f030c010206070f050702120105010e09070506120c090409030905032a010c050a051002031e060d020103180804030b090c12100c210b010f 75
    0x50054480c2d0041c801c42d000300340707051500038050742040d2711410901c411000c0e54014050f00c1d000c040d00a1a00a07413001b2400d030444c0c00c0001d801844510160010321581c0d03614035040320150144055003007000b10903c05500182c40e020060301400700c100001090031744c140040d608960000804029440e407108000700704c0d03511b5001c01c440a009440312118100c1d034034041c1e600380901c03d0f8071410ba000351600815209142d0710220700300a64908509443c040c1e801c0a03e981140c4600300b05503841c008007941c08003080c0d0b01900407184010f1081066900000303054840780c5c20010210604403103d5000020050100c5000600c0d8821855040c5008102d08000c408200c6d803500c0144000c2c14566034944a42210448201c0805034a031b1080e0320960b00d588a180480c08000c0588020f43d0b180702e841210066031406005401d003103d503040042c90070920010502024140e032054080c01c0c081101000e108101001760604500c0c071142c00080794580c2034000052100018141d0541045200c0c1ea00c40000e = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 71673986 1250 71672736 71672747
    0x10206010b2a030c07060306170c0d1a01060207031b081e01110a020c0a05040e0d030f021306050c0f0f0d11030f03070801090501090203070e0603042607051606 70
    0x5488504040d00340b40d41608410789541080c40344604414072002c070780c2684a00000550500307940c000d66050202c180e0300c10758821079102888241406411503050003443d81010700703d249030103000310402c051000400013000d030301040a8200c4001604110010b000b840040071103502403421801c03480042a24084601c3d440b0701164110080c0301d4170911507031004034400d420400300d081e040c8845e15529800c51002075620b19100c07582c80d0040010786e00028061034035118041034a0b60883c080c00300203003241d004070020162255007007610355003130180503043d1503800c050310041c4c06c45071181a65400703528052468400c2856154030346500114a1004c0b181d4040340d007400726511828400c107020090721055046010b00150400d0740070001c02002403103035014800d40d041300c0b00e800c07003046039988400b0f48800360f200031149078002c50b400c1c10186580381010300085038424041d803914203004401008820743c103d81c0ca04040052100450300710309125041c4004a00c3c601d82d041d036803040c1440c0c400007401 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 71675236 1250 71673986 71673997
    0x2030723070e010f05030c10140d0f1109031504050c10090806072007050303040b071505010e061c0b0f040804080d02030a120b0a05040c05070812090c010206010b 71
    0x448040e0140446864601081440d025000601d401c00e200d60711620002581021131080030310a02c01d2080d038140c1d6040850048100c18810341e1203152081c1c480e4811000d43d4001c2083c440240c0da9014150005185407140422440c500b004150b46c13002c000b01013600d041c90404120802ca045070702480005a0006445a0300030030685421000440212003034030882ca55074842062409960708201106a0146128a498071070446900845a448071401e40d01e90a80c0502501588100002e101401054014250305031042c4020704058a0303000b103a106441003070307201c4010701c05041d0a002c4649001d20703c00142981c55801d100352080036496a100080700500110341030f80c0b040d0013140034411510110b0b000780190f4400ca415001e3707000c1009549a01807080b20002503034000a00a504415001c2d0002c21a0028100c2c128941400f08020003481c50500311800e000040006800003101c4002031321403e00c0065a00600b8607106042c40c0c14145039030fa07a0760454011900601002e07080c1d10a031407 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 71676486 1250 71675236 71675273
    0x1031d0c01030b0409080313030906020d140304170712031109010207050f0102151503070f06080411010219030c1109010602030f07020d020a030b15010e03070506090301060308070807050d020307 85
    0x5000080302e0202d8010300c0703445d00140c40c4950000c104444004110343e581207082c130956a403544d02e55a1203040382c0301ea4280da6524009000304650001043d42440a19045030085071018040c003500705a00b178036030b0300c008011510020071220342c5003100c1d01440741224840c1754000d510300d0310424400007900c0386500d00409100e002d0481240080364800c0107100c485800b902c07421402410113000f8100b149881c5082c0503c41e10030848086071300511700c7c0030340c0c00702ca240340c81360050f41c0c5455580f901d000344400c1c041811840b0344481c05015118944240c0f540300c5c041d88800380c00403e1030800ca2002010440400d001da2401c800400070140d0000445408640c0c10b44c416484500c10300c00600d03580034004010794000100c1102200b0300080351a0306000d0042d07001c03041f10450b5603400550b0705079281c0010030340c182c0010314200880e05000004007001c0301c009000180d910385907640c0c240240c00c003400584010b2800b0445c0c2c000c10404100300a0911003d000031340c18021269142580c0c44941c1200340b = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 71677736 1250 71676486 71676491
    0x10c0509091302090f04210813050120070204060803031005060f0403050d050a12052509150201060f06030501030b04240f0e0d09120305090d140c01031d0c0103 70
    0xa0103003507800c010101043d038001e043c004207040001c20088110b80c2a241511003e0103500a011101c600d80c0c1c48080700c1c40f950300e83c8540781c1c1e9440b032240310039254142e09550b0740d521808102c203800200380c864800f4241c00098151150f0450050208076a01ca40280b101c0768004c00c1400120f01c0c402c1103090031128120f035041d079581c104100c0351042d4000c990000b0010303c1043d403840b407090f42103005070111040c60380d119010b5161100111090701c00548504040c0341e20030403c060442e24500c1c1144201a050a11048250360384058440c2551803d0900300140d5403240f0a1100030040900d140c020071041c41c00380815410b64813800e008000140008160408081100c500200323280300c0842080e13510002003201004c07156200018008851030314200b8082d00c4195008940106c0441c004d441d40c000125211042e556801d840035441201c0280d4000054410800054025422500b00b40c2c43c802c007408030036500400150540320014000c10810f0585c48400c1d1180d000000c0c0307088100c0c02440d01 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 71678986 1250 71677736 71677741
    0x2040e15061606050403030506030c0d080f04030512040305070f0b03010603020703030e01020304060509010b01050c0c1905090103030f03270b041b030515070302030925090504030e1002010c050909 86
    0xe0710318455082c0c140701c4455100004002e104569100398425030090300d0a011599514042580b500080c2c1e40740c0c0c3d84403104039010b00101c1c0354178010300304001e5485251071030152251900d52609104c40910684640002014010003600f4400301000f44040600b512641e0304002c1144000d000c140a40820181d001c6580d400f414802c1d081004d1020246008540d203040609015010b401c0803115080f0369800c299404100d54880c00c01c903640544080b002c0e0000080c8041013000c407004108003440702ca0945000441c6655641c03500d01c3c0294400e8440100382c100390b08010f000d03a4000451034519036184c9440c810603140303d100300c000c41603120b03d90001984d0b5524105108030600304040403040c0e41104040100300b800114400010f00206801103a0b985640044051b0b120444502000385c2205c4a0001e144001000c114400000d81140070f6509444518400c100e41084405900080341030554020300e0038a0002140382c2021803000b3b00c040c0032807503c060180d202e028026405141d84000 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 71680236 1250 71678986 71678989
    0xb0601090b030f0601090e1006080406140f1509040c050d06150b0a020c033009060a0905010806030a0228030206190206100e0411010509130606110102040e15 69
    0x290300080e0690340710641c0c4900301650241d0701100211812030202e880c18201240314159080068819010304018140c0d03a0f041400c21505082c0c05001103d015489000201e80104c058112a10418901001c0c40741d40c901510a005903a07548403800d401200c001052101180404020006442094030380301e4070302c00f107850000c1c018444807205848480d00c0b45400700300b403e4a00700802c0d0b800d055074225841c006c090020180c032401d41041c049244080700d041600400c401c1400742d600703803a0140c091420100130f40082203407039005d44007030000100300c0c2200b40b006603086010305070003020640040901c02034940c0410980061500441d81c4a001100c21107840b2900f0380031003010790342c040c02c5141ca600109002c5620b0a15040740740015000d0740700024a2814140c50900460b803d0803030070046c42e121900c6200700e4000218203241081810011100e098844260000441003e4100019203915101e4010900c4e48406c5560060f030f401004108408404002c20740c0d00311005502d00069401c0100 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 71681486 1250 71680236 71680247
    0x2070e070c0209040302060108010f0212060d03020a0812010906060e0112052205031201060f050412020a090e07031e21050702030607020601050102060a020702030d0e13020403140114010509040b0601 87
    0x214001c3d442181c160801c010190302094190403030320504024030000d100184d00034268011040d6540c11611004001416884e000154081c0c02e4024010b4585024071615040b05036849000c0e01079009a9036001005070307000380d120f0240146503a00e081143c00182d840020040245c84801030703a615110703008284845140c06103040032105001c0c07583d4000e8007a01e8940c2d201c0e00056000203074842440e0000507400c4c01100001c01038001c5544842c6458102003980203120781d1160140d0300000031079030102d0100c89274810008030034240c10041506626600e0b1036002c00200380302d1031003148917900072072000074144030b10000c0702f49525040480000700c21008990f14041c100002c2d42c10f101d500700780141301f80c0102c0d405058550030f03800e440c0c03166100c81003c01a886003002c0250588d101d2403464910501c070f40b82034401048020022215203040c0d840460a03a0401d80003070b205070220200c00c40c4c011000b40f186070074600c140100d001203503140100180c0100401000a0445074110b4002081a032145 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 71682736 1250 71681486 71681507
    0x40c0503010903120f050402030718020904050c1314130e15040f05210403110a08070603020405030c040e030a080a110a030c0f11030a0e030c03010c030b0a0b090102070e07 75
    0xd0020041035219007802007080e1415007070301c5461131500321a4240340c1500d000c1e662060360040e00500d0500c0c94200c2e21001040d0303420880741100c1d4240122245541c175800760a0141c2a000c0d00c4a403141d440804e0214030032007070340c010415170001c804078010503200c04080c00c42d045814000090345072510004281800d80c0310031080d03400d454804c100000c008a110341e4501044c096022070b50345074201000401440ca4101d480c840e0b00c4010301080000400a400b0031b00941005440f0a080301e9030340c15013a18061554000401003174000c0340500c018141005050b031004400c0394180040f0003800e903802c6d01c074842c1d860000204141500061082e55160b0001111304040585282d6106540e510003401460001d8040d0001080c0300c86c0c07818407510a040c03c02e04140070380081e501d07080c1040003c1d94400104c5c404981c0500440340b403030015540a21400851140e00d49010078095806d908010489085412281c9e0581003071014503820b0340c1c001100030a5840c0641020050748034800306175060b2030b14 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 71683986 1250 71682736 71682739
    0xe010603061112010e071d01020a12120f0902060d020c071e0510020c100807110a080a200604080307140309010608060c070f02060d020f0a050306010e090f0708040c05 73
    0x51035406a6082c20b180020b021500c280b000e038000b180d07211158040103a5058400c000003c00d011031701c4c0740078a8400380000c50004140100c4404200c565503030710311200f07458044070101d0600400710710181ea050103040e00c2c04d5a282006c2000d20b059500054903405091102c0301c14560108140c80d003803c00b0018000940b001c0101a020442801144c015120080c001e15014801440c0d05c640c0c2e803030000541000200000f4150280c000750018220f400d03c50081481d02000303040ea000c807900c0030040c4103400c0a20301a040413070340d0340c101c0326003d02540c0008410007150b41c007248203035103c6000426201c4d08280d1291a107035890b10380244c115400502920040ca9400c40001489801c0c03605600c4801100c00841c240c1d0780703507900d0200000860003030920260045c0700c64050b80d80145481402007264141502e0011306014084050400e80c1d0003403220320b0049840041480303100d6810850010b0003200843d05424585010b200364000c2950103020030082c4142c5802007000c002110030840c1c00303040c0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 71685236 1250 71683986 71683991
    0x705030304080f10050705120403121805010605011115070302040f0b0309010c050c0c090c07050105010305060129040501030e0a050d020d110d0203040302010c03030b090c07031205090d030e01060306 87
    0x1280d160580c3c860310480100d025038030403940584610340c120b000b180c0c0b103803c161300c980d800d10245c0f002003280b515000700110700b00040f40d100300c211006148140b10b25401d504403c075007989a03a140c0701d400c50300d281e00280d062000e00070341d0300200d010000b24038080c00ea81c040c14540b01e49410070f00394041e01a0f904a0405250200780c040785825a4201561003280702c0f0009119014085405030f81500c10303405000c1c101c0e00998943e5840e8103109500c00d03003200310148954a000000e031142403c56031300b85c200301c8458000c00010062260740d00c10703030013254000540d6401e01d901d81e1024140704d44618072656040c151584000d1005285c14080c3c000010b402800f500c40c07003460300100a49491800c0320003400700d170044034103405010000940d92041c07034064005610302811750b00155060003008100b1070404d61100000c01040d226521100c0c000c40c0240803040d155015458003500c6011006030104a091510741040f0301c0050000309064036504078203001500240d0385452501402d985d41015003e6070 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 71686486 1250 71685236 71685239
    0x3080a0507051f14060d0302030414030a0f06020307120b130b030a1203061e05030706230408031803011b140714030d0c050403170f1603020d12060b030c03090705030304 74
    0x40c4241c02c410705000c00a0411000b583c2c402040000740500c0340000380040e0f1040c0003d2040300bc1001020781c40c020700034120790a40701540c0c1d5007000c8007021541119001d07000b205010710f0f40d40044c001445001c00c1c0c0c4040c00b4030310780700c1c1c0031846170079002d48101005511103120500e281c5042c001e0049460b00105400c800440d444d0014001c0e04161249403442d02e58280c016102d006210b040405440008025014040c81d29400320f440140180c02c50442c1d10008510144604018001340001c00c51400655103e8110040c2c0c00e503074210090616000ba41030904d212102000c0c04040e240c010054107198495807006d080140d070a006802005012a03074142881e4072610002020f04582014404140041510448121594002d504c00200605810402107004c03101d0000500803142201c07401c1030600340080404401c016000c00c080d00541c110342450b1460990044842940240c1c890f8180305a07440c1c0588200d0300d106c0200030034134a620100c00b05401d02c105016080c01440300400300c076101da = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 71687736 1250 71686486 71686543
    0x40f0b0906010302030c010c080d0209040b0d14060105061912021312050c1207090203060d0b04031701080d0c060e030903010903090807080610090209040f0609091502030103080a050705 81
    0x101e10078001a0300c24881c40c80240c41c3c0303610450f145085654002c0f5090300701106407601d20041d400000c1020380c801e0321649035403419100c1d403203030725401d070b0103100c2e002112502440d04504006060300410f01075941000f83d012801104a07480c116090f0514041e00c101c4045500000240904400510030308108007000904108088111207001d00880c2910540d181100400c5204030401c642c0b41e0007504400c0007040114030340d502440c1c3c088c038060036000b450700c5030350f84050303011404560890110b2680380204070f05904800c00c19003d0110325004040303407000c00314081c000a040780e500926840d15240030350503046062040c0c40c0074000140081c46107007034078907001c0c0c00c01520740601380d010710a555002440d00800118039004200c0660300c03090082c1419140b40280d80400351031f03070700241c48641d095505d1210f0b20030007005203000c40340020451030b50f14040f8403900d0f100c0069249140180014004264030b40111201c4254504290341e442ea058500241004c2c00d03860342c0b842004c440030752140c02 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 71688986 1250 71687736 71687743
    0x402031005090a05040f020108070e0405010611010506030129040b09101e031101050a05070506010b0a030c11060a0914030c01020a090608090703061d190605010506040308070b040f0b09 81
    0x141d031400c60361002e09544040405044503c111409030400303160343c3c10080035501442c0d265030015158500140000f048501050684100b80e20130000101407842d55461140300707210b040d80180084000f8001c60040e4200c0e0090020980740801001d0a1400c2104459503164840ca0340e150014004041d5032800c1c10607103002003241e10032444140d18a07502c440504000200c400143c0f5400070b05070000818920044a02d43c001c803044500b484010040c00002c100d040260038020010840c40541c5d442c0743c51401070588005a0010090212143c5200340104010039926484800600006041c8010f800c1500140e0502014022180000180c0c02c2c244501034000703000030000da0f1200038401d5624001218000d00c101c0744122503800c41c0300284005030389600005070580c0074402c20b80c044510b240c103050825612103804501c40d8201001101080f283e8087e9a0040c081200d0480c01c21346552100804c2d8814010000c03c15044080010100003021181546280e00030f061881305203804201c2c0c0742e5 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 71690236 1250 71688986 71688989
    0x613140108011a0d0f0e150106020d03141302030703020a0b12061804060f021b10051015110304030803070507020f090c0909040f02031f0f1a1002070504020310 70
    0x2841c1d58008103260707880c411030034041c400c01ca4007545000860512500209084094620340c1521050705040b0307240c04125482c211010406030355101d5262a001910300301520071008203050500d1500c00410303c3d022001c69000460801013045d25441c0e2002904010580d00003d5004418001c041105440394024000070b47c8900d52000864a40c0010001a4942140e06181c5101110001000200b4513006400051024040507040c041d40b40c4840e8450440d08030103a07001d60100e1104494401540104c42c0c20042d44030a8003426401c00794481d4002c0305818603802803010981c03d0031071444042040320300442d007194410742c0301c0c00c2c0000020901c4e400302d84140e1185070584500c1c8c0140c58203a485074010001d1420075031802e9000300c2800400c480051007529042e980a03014805a2014001a03a092a00020b048000100d003041030080380d00e000c000c600f042d840d041d00444415000306c3c01201c03200341190784108032040700004a1412603150400c68200e4008800d0121164492140c0c80 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 71691486 1250 71690236 71690239
    0x10608060a06080a0b011e030203010c05270a03081c0f0209030c04050106050d0e010e0304080c030601080f03030106200106170d140706050402061209060601030e0a03120506061314 79
    0xb02a501c0c09000d50318640d0303101c042d08401c00c140040044240050b00c40c0d2103000f9210b04c28482641d20340010742125265005035020580c001000e548031000c0000c01c004c103075204020319201000c2d40d000300b4042d004500001303080d10800992226400003a50543c0c500f600315500900003d030f80b0b181d90390042d400401c122030291003a00079418032441c050280314140c42c2c49590b8141401000500d8001030b04092000340c01a55032081c46201c6e408045c0000d001808000004042c00301a1905140c1780401c164880c00341e9400204214818903400720441b41154903c0c03070184202c0b40481c4080500744501601b1040a40c03031304c07600242044116015803203100013802545d02c1d05000a900340c42c500000b02c00111104010801e02000034003d60016800a002a03c078601700620381ca0580291002541e02d50115403048003000641d60f0b040c060107128820940103004450410303540502040000f081d292601615480055001e4980800b46d0b00c0c2c0c0711400030f95a0045548034021801c070400f040605 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 71692736 1250 71691486 71691491
    0xd081306060602011425180b0403050d18080d0c030e0918070b040b1e0f030a0f0c09051c0323070605010b2b0f05010305030306040b01080903160503040503010608060a 73
    0x89400d00c00b881d01e506d4280e2031140d5018414034100048a111480740051103e04001150114040d450280644040c521500042045584141c40580004440c2d4140e5106586011782400010380102d40040304034014102000203401c2c5140a40301e0f05855421540c02c480c1c07080800411500807142070900c0241c09090303d603540d49481049000740b00e5405030009091081001900c541031404500c1041e4556a40c45c1d82089888400d40c07100e58400c1d2980c403481ca80394074085d40e804103684507000002d51507051000c542031a210204007958610100c031404a0b452a0b0440140340c05088045821f0306104868100200e03407800e04080c9070004a8140d50b850b103803078008a10f030111a02180c090203c600305801d2a18085004ca444141d882c146c40e181064a5603034000b503d90b1a0700402c1e01030f6100c0c1002d10380b02d14100c428001140d01c0c1224141c10001c0c64800e0003124080402224801c01140c102181540d0b498101180381d4826070780940c0d055860003070f00080700f00c0041003050041d1004ca806 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 71693986 1250 71692736 71692741
    0x90305031803040f030b1e1303020c03060105010c0b040609050106060c1401140610021f0204150314180102070b07020c10020a021503070c0614010f060c050d0813060606020114 77
    0x185541e400f450040c0800e000d100402880403400356000686d100703203c4003400c1d158110301600a126000c00f030343d0995658821420000406805105800d4000000d5008029961420300007d22400e034120014140d440d1036804981842259000426405d420030000d01032642d558a000b0203650602c2029a001d01170400350b20403400041c069040001040d21100c0455105d04042062012011045009503c41c1500c0c14a0040e030107070528050050020006840354648042481e0312595a6441410980b1b449004007502c5910007126411500e0782c2e503e04001050844240d0081c0b10740e501c0607010452140c10440300c00c0c0d0008602d61040000d0b6203280702c4603100d1000380d0752404e69110007940010048e818804c0040c174240615444170051a01400e032502684032031089803115002d0030041c0c144000144501141c15840744001d00e020724000c810300c1d01c2038503000e4484021122a804002a52011134007900703a840e400e603d1207801840402c4403564500e00a802042004908509010b42100 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 71695236 1250 71693986 71694031
    0xf070e0604080d052212150203070206042402070b010f06050309060601030b15070507060908030f1b031210030203010f020702090a0504051c030506090108010209060a0302070606050409030503 84
    0x964049070b2000307008049003002d9240c191155080307480e06802172980d04100a0300761000d50fa010000f4540007001400342403141c02c0c03004000765000c1d031a050040c010010f000041d41e001851544c081d1b0400c3c0694500f800d00624881c0240342c0c4c4040401075400880c814062044000d030b140e048034020b1000124440d51860160ba490004561040c102d402000001d140c650194012040c1c0d0240109a0f440000c404003809800d5000b1b00c0040e0b03041c1d84801014000715070402d101c21b000e8040306000b035007401d5400d44103498504c10402803c01030204940c0c1010601e2040040d140304c0700101a00100500c0c128192034034010b050b00c400c1c1d2180d0308000c403441910000344211556950040c1405001d640c4a15680000d08005072081303a4610031000300a066010b40e140c00222100d03d0b42c0c010640782040d004002c1448030603080342c20aa4410172411400303590742c03012943c0e001c00034200942c5130292030504100524140e408280c0043c180f1007943d0170150720000452040d01c0700304840c0303420000c191 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 71696486 1250 71695236 71695249
    0x1020d05150307060f031104050d0312061703220909051f0203060906190b03090f07140108160311070f0203100506090109020d0207060903091d040b06011d03060f070e 73
    0x101e40404190801c5e04020350f184650842c44100d0403225500307142a59070004520b9410860b2400d4002400c1c2d81032010b8459101d0254000400d00042c540d0b5640c00c3e8031080c141c0b02d00c00d120030300400c2e16030180207010800880b0043d00c010019240100142e540505009071031341c00c4a0080440c40421490724a4580014400c0c2c80c003444003e8004c4419646040502c01400c43c00a01d982c00180303462000209110054000e504c1010010068902100840d41c858506491500005454001c102000c0c2860360300020040d8054a0446820301d0004401003e6000380001c40b440c0c1e011182c0040d20030305010601c01020886442942140d051009a000d03860172910241c580345d078004c100c000104400c00d1250060942104508001443d04034181c0d1504111241c1d0070b41200800c2660310f041040c80c522910819901006940c010000e24199403050000c810081407207041c0a2007048981c80e034103032403c0c0028031607000382c1100e80d1403d048070b10b4010720400701c540701c0c0000d45181c1200554100213 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 71697736 1250 71696486 71696489
    0x6061212080f070f0e030c130f0606020a02030a0609170703030515062a0c210c12060f0705040909051c17040f0807080711030d030605030d081801020d05150307 70
    0x44c4d0380d840e1003840349102141e0950b0203142c41a070512542c6004c0c89144e890800c0c1030165944118000795140a1919660070b81d40b01c2d50000d000c0d500030b040d8040141c1c8011503142c02240c2c1c48100010000350500c1c2c006400c4024581c4030708148000300c0c500c010590141e0106000fa1441c0e0148590f141c0004100304440c4070f540c08010344800e000000114802c09514921001504102035603610084000030800004900460300908c2d1503140d0b017001101e80601c81310180200940d181121824100d412555824000c2d010704000858900000c4100d4402c2c01510090721082c030050154a26600f403696845400c441c1090020b6000d85244012500640071100b0701e03404500c44000c01c0d80c41d600c0707020711030b1005c440030741e003081c010040c00700011208070003054120b202e51001c070101e0160a00385450650607108035018513250070360034805c50307500180380041c402c0d0620b03001c03145070f81e00c8005a5444a4a10545049600210b90b080300744085802580c4140b980750b91640210400004055890016 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 71698986 1250 71697736 71697751
    0x90f010302131e02070809090c03040c03120c0b0901020c06010f081e03070602120115030902060409090f02100e03061b03070804030903080a0801032907050706061212080f 75
    0x8000d60424410b03410606800c1c079100f1a43c800d040c0052414816613003d00000c03a07041c1c80c0040c0005191034418000c540201c00c40d6140d80c11454130350b4600c001c0016900016080300382060f680c4040c80c1c41070341e40010080d4003541000301ca0034400241c9000c1e4001c440c07191b601d402078000120319420503d0a0101711a920002070005490303040d00040040c40c0121854043e001c00c100c8070340880c3c92400186561040015070803840c2d89809842c40000003400d48da202054140140100960b0310a415076081e158100c1000822001510b41007105807007040009400c204d032048050702e0950001c3e1448080c0405600ba15015582c410020000c0858400d110304600303014400710350b840d031248000b81c2e809482808d01c0013441d42c40b0b80720b541c0c0c00e40020aa4070000b0311118010b00801414076040401080c81900c02c0560740c040340d0100c110617100600d642c08002020603540d090250701d8001c48000d00404a0744030380c4d000390b0300384030381301ea2040c0c80f004010500b50300105000e44681d0501a12800700d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 71700236 1250 71698986 71698999
    0xf06030501090e0f0309101b050304060f090f05060d1404060f060e091c020a0c03051c050a02071503110c060601030b03060403170a020706020a0c02030c01020c01021203040f0f080306090f010302 85
    0x2e1100407c0820725240c00e440c000c1181c842d801d22020600354000007031660248008589480c41c15070014551410301500d0703001c02800343c7c070401c61882d2000142040e920200c480c543c841c48008501401011408a4040030391803c00038001441030b903500c02c25001c801c658061014988460401007d40d406441004040d408880a028502c10342e014210508503248107403100000700b61296090910a41c0060780c1a8120002019990010441001e0181180e040c198103201082102035150661031255640396040c491108600b60300c030f0f5226038a091301d0580140e441d20001c100041c1c1d42ca40071a42580401d24008201c6806d244c0010464411585a81c4042031b1900403135904100c90006807140d030503d0f409010040000311103002408044080c5d03601d40600300070364010140f07070607230750b030061410341d00b04501c0f001003641e010964550b8100b40c0c0700c1c1d195481c0c0352031421801c01801e82c08042e10011165900408000c0540004c41c01072300201c4000005407034001d0f640780c2800b800c0c40001e41c03019 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 71701486 1250 71700236 71700247
    0x1090b0f09090304030516080613080a0f02070906081b1f0c050a02040c030c140a05090d020613060203040e0108060c0904050709050405010f05130b0901031401060f06030501090e0f03 80
    0x192540740c9541c002d00040559040c80e959039285031074032601c0804000d20708084007041c40030180030440315500603aa41d101201d4244144c47e420f60f6031117520301d1142041881e6040b08900b50017040f030000280b030040c8080050342e5403151903079101c1000400c01c2c912510603503921400b0f4a081e0035244d40151a0749408500903040c03450a48090124480499950007001041d001694491058004042e00d50f02c0114504092020013040540c01031254a0240010300c0311600503075104080d1142d440c004e603460200040c07540001640303809401403007948104a04808a00d02d5070100140c4115542040281c4660340c94181441d1640030448099144c1c250922100109103130076000290485a42c5c204043c42c25221400305094440982141b5039000030345000b0400f904ac2201958003607406d003601004410341d25400030b0f003001d4040c403001d44151040f0310480c0c80c0d028294070080c001c22903a0001d014403544c414014000d01000d00c0b800ea0100d1034031032164281303503020682c4010160751070040c51402 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 71702736 1250 71701486 71701489
    0x16021b030d08040c0b0f040e0906040b0a090201020a08030a021b010204050105031504140f180c1e0a2d050d020a26060a020c0c12060a1a060712030501090b0f 69
    0x250001802940c0f02c24070718100180440040c801484d5078141b40103039956640c01c016600d1845070000d04100120340c0304500300000300b220390755016003050041d20081035500960004038a0400310403409071074030b00c1c00814410102c80a500804c000c0c480311b4004500b6a03155803100f8200d015620845011030001c2000801401d81e0482c01c040c8140000c100052000b2000c60034195240205c0e108807661001c6028000b00c007001c1e1440d4107651482c14010046c0e0004400410401d464903904520414549580d4254654030919820702820344a01000c03801c0c01048594000d00040d81000400b00d04c1180c808926428003210703100304590041d00104800b85004500190061001c40d01403a082d039440c205018001c05000860160140b00c0001d078031078400301450390034260142010740c42104002c08440c1c1c103460110f20b055001618241c0010034018102110280d90f03c1ca9042d5540010f000411104100c803207001450040559a000c000683c0c0f02d04000d01100c0c810110035900c1008141c80c412507 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 71703986 1250 71702736 71702747
    0xc030a0203101706070305240f030114070c0c1a1801030e070305010f06141003090503090d0b0f0a061a09240304060b030606010507120e0916021b030d 66
    0x3202a4620360007080e50f540658041c50402040560150380160041c003213401c2e0301d405441c0c3c1003181c1140008840c1c00c040640600202d06013100c1c0d001c0d55000c001d04040f50303420361100011000386a00101245880c0c0c0300100b040190380b00889110502000101c1c018080b0380001c1c203082d078030701c3d4180c0c64640c0000c24024010383d038194080c10075841d442840a43e10040c4607280c029441803001140980641c52000c040d14043d81100321104402e0031210030540d907400c4401c0040c8141c0c103000030101c01d075080c03441c00c52080300c94040d00420541d00100030032510542103403090380d50403074074552900c8007400501a58054419918261040c00c0d40305c0e41c90303540100030407191500411400126101400c9151300c1d40c000d4450840c030980c0402004103024003802075600419040300941418949000042c00d01c1c0112100a000007540c800c4002c0340e280078403100c09c042000105105030500d0030171203001e4a20a4401000014000c0c407000e141003c014089050000c000100600b09500000d07204070b80 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 71705236 1250 71703986 71703991
    0x1103010e062107080708190206030703060306091202010510150509130501170d050a090608060303090405090d1215090e031612030b030d0c080310030611040302180c030a0203 76
    0x2807005548161050b00410159242507110300750016088681c900035149040011030b42c0f0202454001c00c04940d50300e5a0301e80004085541120059229264050204c0080859410080020b4940303000c94060103001101018007805a41c0240299690340c00d0b1230f6945d803003600c03620444560a00c420012280640d0182641800161203000c43c0d000e01c9034400151072003030740030a40007a4402481004120305010304060fa070303064140b042c41c1140c001c100030211003c0d84a65020800c1030004540c89640c240110b8464070f500030804d1089040030341e07907203440d03030506140c590101c0c4400c400a600e42d09140500035000c4500d0f0f155250103032405030400040c0c0404510490310380820061802c2c03d000c009110324a50740508102c09003c4078907480074085a4142015510030740c002100e034646079900494580c0529804000c040d02c9440e0f00000e81615415500020b1119042c07140c2e02c00c0d0f0b03c0a010150048900803621030310325100c1011403005280c01900c038010340001c20000117414040d00e400641c0c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 71706486 1250 71705236 71705239
    0x5060a030209030322080a05120a050412120915050711030a0506040b0103030801060908030702041a04111905030c030f090a0218070908010b0f091e01080a03020d031103010e06 77
    0x42c5031481860009003158000c0d5401141c000e001c200704d801c1c00201d01ca40c00c024214200041c100d1140d00c3d15215550084042c0000c40342c8800605444080d2080301958000c041150100c92100c1061130640382002d80c0400400010b1400200000c0c0d10445c00a0344195034025150701d440d1401a07101d800041e040558260340510a000104000900030001e00d88510f000f45100442c0d0b5041d40303030061540c40184e00103400c000c2c8424084c4a09100801140ca40c650b044070002a01d40c8940b501c00284000012059032007841d0070400d482400400d40101504850780c840c01a00c0d01c00f204042e81d070350000b80c81c04c9050000600000310b8800821000c1500a104c40d0219a120101c60307000440e01d4610b11540d40f006500c14050207001c90b0800070040240402100902c165000f0401040c10b00403002c813454803864844000c910a145054a94842c500d000c8030034401c2c56840b0340c6a1640c0e03ca41e00000c03001403203010041c1202602c02d03c181800300c014100101d20b16480c246000414420107081ca5 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 71707736 1250 71706486 71706491
    0x60402160b180f0304090f0207020117060a0306020d060f08010207030f080c1204060b1903050d0311040f0f031502040302010507060c050c0114011a0712050a230702040612050705060a03 81
    0x5035240780401c803080800c0c003c0b50095070750f6400d00d41d42c0da06488801216034030380c90043c000240140e800018203440340c040c0c038110b01032aa41d42d20000da0031861590010b000e0034400111072031107441e9a0065415168020041e80d94156607210b103500700c5c032410340090000748810f802809011b100d90241ca410403400c2c426203080580d11001d2490824090b101224020b90b5030481c80c0190400c0d9400d10002803031840c401010f01d1441d00c078685c40707a40055028081554803a101c4003030800e200b041e80c01504c1690002d241898490a040811041c240003d60703540b41002c0c00e0024202c101d00803070341507a506035030f00f40c1854030320340c3c8510140498010030300a1000074025443c030080c0901c01d4820b02c4041481c00042d40d40b40117400312050b44612528440d600d800c000703e8012642484109031514040d141540d40c07941000c10864100018070b1446030b01a0001c005140e40691380d10141071240e000300c404100c0c150f80c40541c0d075105d4038204802081504644410400ca10700480544259859400c01 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 71708986 1250 71707736 71707771
    0x703090e090a03112a0102012301032604031709131d010b060906070203010e030706060e07080103050c0103050c09040f091115041e030f0302010c0206060402160b 71
    0x14031a80c104885024050388510b00030b00606601c05812104048124040c003100740e41400c03115264001d802440504941281010005034800d5014120095000e11140795142a541441032105420301c425522030202c1c0f141c41d0661075400b40002d0100002c3c0c0c03a4240344c103140d81d594200000515190302500d0b40c06103c00e036955100c1c82d094811004d0501c0000944040c1042c0c0300760311141154008035961b241400204503602e0b404204e411700c000c00c44519444000b2480081d01500030f40d8441011400086a03040030800150800403e1300c143c0c108004541c0c0c1c406104a8003410309100c05402580a004074088950290f0f21850704000d16001c0140f5107407030136021070181c0707807100c0410b804030b0740c0c0740060742c24030000c25603101a840c001c450f103100020401c10090030602941c0141241072000100c03c0d1421910b10802c0c000842e401a290980c245050801900030142009843d0240c02180c0009030365150034401c840c401c0030212405200c1c00100d4a81c3c030000c2100600302a0b800343d2840d81c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 71710236 1250 71708986 71708999
    0xb0316230a0f060f0210180b190207050604030e0405070e0d110307060e03160608061003020904050c0405040b030609030f0a09030206040f1a0f1902030d05070f0221030c070309 77
    0x10b480041c3c0150340795428012880000289090001d5601a6aa03840c12290075030b440c81400760b820080d50040701c070750421703220300d4552904c10081d01c228034865032001070071100300a4003042691069019445640d41c2d070f900e55080c401500e6045424000080c842d9410b0141c914000f2404000e0301e00424040c001c03010381101203032804810760021b101080345901c07446060328041180b01c080035a490142401e0394031b84607001c0e09804014150a2007080c40e4640d0084551180c2e050352400140140244403a042414007000a6800fa001d01400f903410300d80c0103501414000348007030250b690040110311308144100e260019422036110403042103079003080000503a0302c00001d080903010358100242c0b1b40d031408040c2c01e0303403803090250040340c1c041c103100d0000d003441c1480c10303109141d0300085240a0b100c80d48500320304500c50061281301b03a902d80400d10100a6000c900d03c51900f00ca9001ca685042d4580020080d40c0301e070f4500114035450400c0094103981e00c40c40a40200d5100c0d06014054544445 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 71711486 1250 71710236 71710259
    0x3020c070b0903070f080703020111150a05010e0f04021008100b0304080c06090703053007142503120e12010e0d0914040903090b0d0b0316230a 63
    0x81c40034841640c0030445281c945070030701c0804020b010340a02c5111803840c107501581c03911520320004e4180140c2040e20720700b035441846890381c0421184400381081c5811015280100001e0045d0958900c00340c000400003903401c1c0200d40200e400510103d95003031240c004039225034000345010340c0a6031803000002c01041d2031014500988c4540c0c1b190351030700c041d0403819141c00f000030094403055002c0001040418404039101c001e802c41280040c000c060050750b03401c00c040c7c00d80c01410715680c000030004240f103070b2180d080c1d0602115a0603604044030103500c00803490200e02110010300a9010100002100410600b00400040c00c1c100c2d0031155440000380042510080c805140e51103810a41525405000800c07540c201804c1c200c40c86810404c082c0724070129659180d0159590700d0000d8141030041c60414010200000e0322542d58038000380c0d0101811106002c42d01a10a003180d00e011179001c541c0090503180124943e002c0d07c1c0b041c001041c0c2c640c0703044032403d821000064020504a6148 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 71712736 1250 71711486 71711489
    0x3070e0919021c140103150e07050607050a03020105102106110c06041101080c04030b06030c0a09020a0e311e0501050907090305120f1213150212130303020c07 70
    0x4020100f02c0100f0480e050056a410009500b0313403010000043c030000781100d018a10241c0300d124002031400c4a068054030f482030350b0b00903030ba00c0705000c80c00301708020f400698007190074072a074028002c54a801d41489a203003c20301501000e25130480c403a00c20740f5810003000c0c7d0018094200411349a28440783c50099038465010b128054201208020901c010f940c850008280b080c603010a5a140440c0c0b807500902880c00b0041c01841c0f440c001c283c10780d9041009420100d00100781203079035541c1e0b603000c3e4000d61041224a01041c0c1701844003441d8030744180c084d6402c800c06101103200030941d42a00c01c1c0d00411a2201c940d86540d207103200c2c20f41c2100d94050344500c1502070009900e50411080008006000b032141c010440541c0b0140f00040000c076001403000b1000c1d41090300c2d10751441312100c440c0959018990704042041c20000020702460204800da4020801c601e81d140c3c0b008180d4050344a07101128944245040101d1411750840d20901c200360b0183c42c0040c00d01d299064100d0034558607 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 71713986 1250 71712736 71712757
    0x3011b0e0d0c09020406031413050607050c01151707060305010302030a060b060d0203090a03030e030a020d030c020f060c030109052d15060c0703020907020a260f0a0c030f0503070e091902 82
    0x41d03415039020349104484c8550446043c904000789c5268581d52290340d180300424600800002084461603100c1c250402141310000c2c20200300c9054440f021a507684d040c100300360303820348070715240040d801d40284101d03416240c010b0301030240c00032161146c01c06000e41c290700c160400d4003081681c2e03100c901c40c400340d030043c071810300a4000481e027403e0040640e00c0075030741d010b82600104490140c2e02e40009003042e00100c10304010846400302503040e800e0005d82c420fa040b40c0d00601e0100320044907a01d005506a4040030400c00c41d40c0c070340c40c1c0d03012210780201c4260208003010640f810001001c0072081a480780301c00080000342d000100205005401807020002c07a603008080500c218900102403a0b8171801070b20052200c031190f9100d002c200e000740000810014805030300c5002042002046940300d100c041919607460690300b0004041c0510b13450103400060804149040b02c3d4440d004903406400caa0b0740d103a80c002c501c4c9003003203d4510082d049901500300c540940d41c4011460001d007038010b50 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 71715236 1250 71713986 71713991
    0x90311070303030905060c03012114030a05040504140907032004060b030405010b090c120406110406020a030f0302040f0627080a11040b09130507030605040f0203011b0e0d0c0902040603 81
    0x15901e045451b042c1c001d841c04058034824001400a5104801303021850000003200c0a414505414401211040160f841c01a0701000803190103050304940184202d401c240c40402c0320f0140ca6080c0201004151041402600031350020001f045140c50081051061070810004130a42c02000400f02e50340b80e840440440008010801400000e00c2481c4440701c040e00c05420700d02e40001c00d90712512500c01c1c02310b40440c400c400700c1e00b80a40307548840e4030035840c1e8a1080d55103840d078201942c3d40741c038114114000351300c50061608680c401d000340c03000c88914120305843c46080003400d94409000c000c01d80b000714080c1810000c00c120400115000740714101c06051500042e0603e84d8800700205001070055040c0201000551100b0030300d40d0b84001072a8401c560b462442c83d206003444410307400a8612801c060034007060010308800c0f007200300d00c01c4000f00100020301e0101d692442494011a0100b07880c4207520303800c1e09102005038001c0b842000000d000781c1c0c40761085004c030307007058020308000381c3d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 71716486 1250 71715236 71715251
    0x5130816030302011b1b17030a0e0f0f0a14030702030a200307050603150d1a060907030c09031205070b1003023a15090605090d0905011209031107030303 67
    0x540a2040c4801c0c90000c41d2880c04000c0b01d170001900c03a02c4510460085694032a50044c00d00000c042401c0900c12102c180c90f669040808070400a0000030140c0300e0103010f458034048040701300083c0200441120740180020740d0351030711a100424100440101203000401c1100d0042e03030288603c80400f8490041c4840c0ca030070005289400461611311a4000d6200590502003542c5070701c1901c0e0701c0200d4800008082c82c00c0004503148102600700200800401d20781da44128007a00309030b5100d031406480c0b980341940c0d0060210f091340e41d07080c0c807200410740e00b00c020300110744082800f409000d0301c0d04049140011b03a0b501c00c003001200719172680a100c0301007414070443c5440310007501c511545d0341c440ca5441d8203441b0708a103000005800800c03000390b10501c540070410301d000c0c06902040659401c01031465542004409030030b0031100b015550050041c583c0440c0d00901405080d11010f944a149415030300d40b500d8000e24000806400707010b4100010440d0820800840000d07520a940101d00d4030b = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 71717736 1250 71716486 71716493
    0x3060e0f060c0702010203120903090a0803120a060302090f07020c031518150a05060d0b070201090201030617120f04030b0c1b06071409010309080f090a0504050105010f0513081603 79
    0x122000d44805280c8008103c10310142c1c0e0b0010503a050701c50703103610b260180d48658491030315501c01d089540c0c3d004640c41d00005150180440504a502c042200d82003a9070741c4c50001000311a101e000095000710080e000c80da241e04d80c1e0700700b0342d440111401120900c2c481240041e291101c1008078400f540700440030840031556821b000141440050014a01000482003e91603c500100f0318100280d4800000c3c0c22640e0300c5841000e46500400c190965003410344009000c1d000d0090103a0120307040c4400006c845039407103400b00804032068040c1c201c85001c0480340103035070300100104030040d405200c0070012030f408008080c010301d007111380240e0b14240c1045d086ca60602c401000ca03101c0e0801c0c0c00304541c0a821042c8a4040c100820506a4807081c40005070000d00010034003912644c404180305400d50f80583c0100000c54040794200310307a603616000c20096441c01d008040c0098204c0c103580e10b005000314094107000840c10901d0b21940c0c1c548104c20300e01030f443d426004904080c01820401e1 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 71718986 1250 71717736 71717743
    0x150e0108070614030708011514070602270a1202060d0f0506150a08040201110307050106090b0f0307030507050603040f120302120601020d09030201050f040905010b0c0c03070f0504020706020403060e0f 88
    0x1102d10f00b04045013589030130f840140c20010305214100440041800c0f90030210701c40c02070f40c0e8092030300040e0b003030f10386560b820950002c0d00900588a40c1000705e000001204505401125042e1710040100c00c50300c0c14800007145455106200301c0c0c008905000b10100b400380e03030189100c8002c4100c0001400c0c5090420460f060320114180503410f0800c224240006074030246540d40aa02828251404450841c105141d0b00c124000903100b54030708000070540080540081b41454011903c1a50500626081549800082c0310042941e0301c01c0c0400c00403818460040d55115000b0300d242c407080c11280d101d041c41e84203200c0070000000c4d800240041d0751080b81d10000d4000700d081c8001c02900116039405440d508103400040d040c400081403000c40713031028030110350140111800074022940c1d20100140c0c036410640740c41d48540502c03070a0140900f400074030b0302c003295052f0a806030018a07107401e00009500c920810b4034419003c00c004404541507020b1804001c01d0032000b8460f08040907101400c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 71720236 1250 71718986 71719007
    0xb030a080705150f040c05010e06090306160917060f0603070803070b010614070206160501022215030e1b01090b0a11010609290a0e0c07030807050301060909150e01080706 75
    0x4030004140c1c18040071980506d54501601c40a00300b4840120310070002500c54007030044940c0d41031292000b002040c21900551501a244580700c0c40350b410780390411000424294400d0540c0c90b48594000350100e06801e00321500400058240d8803941e4540c1c02d40f6066502403d42a10396001c101d00405c481d5078010041903d440b02c155116082a4455000554612404058000c800e11400d403843c1441000e41c12101400c0c15100e40108074805c1003410045c0c0006407185080c401d80b614849010305000340521003083c10204044c00c10124030400b401d04580c18100d80c64104140d4140c0481c8103c10a0014280401c49481d154020070420003000c2c00d544c0140c011170b01681c01c0c40d544208114100c0603440d01401c05000b123010b0407901700c001c00d04000d442e07805400745041d0310090103c48040d280c020f0000034065504c0560542d81e000c0c00756074178442881981c00244013050100301c1243e096110305581507050803681a00c9a42c3c005100c1c0300b07c0300380c000d1407690704510420406550030241140 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 71721486 1250 71720236 71720251
    0x20706031a2b1a06043b030c0c0301050c0c060105120102070501020f0903010c033804050a09050d0804112b03120b0108040c0b030c0c010905060a0507020f100b030a08070515 76
    0x90090340402560300c40035492184584280e2500c214081d2101c6025800c140c6c0e01d244003260344548034100d0f00f0350b40c0c1c5030584200d8002d5207400080b44000d1440811a0307045a00fa900038500d991810f400e1007920302d448a00103025550034001c002c0040e000303000604101c2902d4190039100c1e6143e104141c00c45401d6110342c3c0506141c030807019405500ca02000480c40340020131610390311a0a88541081d4455191899109241c84100140c07540c0b56401b502c000d41c098000c8032050800b24006640140003030b0ba02420b10700c850b408103604c0c0c0c9017450300035401000f00f40c0c68201081c000d0a0410080211000c21808508042d80051950103a48107e03052414240b9040d42c02d414561680d1210500c02c0c020810314000000000c2e03541401c240807174003d068400c0080007460550b040440d00d40304203840740304580d810300e0045010170b0301c001000d60003540060003404945080401100c002c0200b2850b070380e0540100d0810502040d2481c002c0c0c841c6030b0050000d0300400e6668844448071000003040c28 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 71722736 1250 71721486 71721491
    0x309090905100f02130816080601030b04200d12020609070b0d0c23032a09010305060f1003051603021303080c1005090a03020706031a2b1a0604 63
    0x800100301c00007034811000d0421407001600c24a4098000f000c1d100b06070400b020141035010019000c0c900207903120321403005001100d0321546400040e0707200d83c4c0a1102500e05039455000c1800b241d248030094408061468529000341c04d4070004c01e161054085c2d003902e100310302018240d04c2940500c40150b100e11040c025000040c10101c0001c40341c010343e10345280c0d190f92a00321803e554000d01c80342d45072030f8640c035915480f492403c503508500d0b07008540c880d00e8030180c18510f5104014845c9075920340c83e81d8005590801076400300450081c0b2004000719400100208040b200c0d440e8903800380ea52480d20b40d00403c2034589131508005403138402601500309881002003001011401124034260b035403168406a480072880c0e020341c540030100c001f034a441d80c81c0406106070810000f803581c030308a1080c0c0035114400e42c3c4100940495405400e85080d00180000743c241500d0078060030390b80c441085406940005203040700d10407000e80000d08071064100220342c00d211094060060364800c0040340c09 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 71723986 1250 71722736 71722751
    0x61404060e03160f060f1103040606050901030305030c0d090c0602030705060112020607021002031905120702070509162d0206010b04150302030606090d0c06030605040908030103030c0311031204030909 88
    0x8039200a44902c03005400c24405494040822600f40c0220f18104600401480303003001482d40340e2488d0303006440484540e440c0c000005001e08083c070155048a03011b8407440c1c11580c485003165820361241403200c194994030f0f28031000003040729003542d0250205500540d245d01040c90180c1c40c098041c3c0008040c0d42c52b0114460050f903515045031907070707079061710200c907410090b4170103900d0340c0070701c0d00c0c500c10403000401010840380c0c0c414050036a0000c00c103c3c540007500c4628042e81c0354241c0e0f01426401c2840703400010007081c149580d440b44a00c040c0344c0444a81088070344800556030103001141e180c07070302e0312140f1b01c02d9034100007481c050b150500a413450280ba00031016000c1c00400c40c80070a2640200c0010190360b1100d050740c1d01804040c00003401c0d0714052a10f400c242e41c41d030080c0008240b0b403080c04034035424507214040d081e5a0100d016840d590850300c05694074a01c03500110108001c00c420021441000d001a0440c00003000071900c060402e0f103800782003030050740c21441140b4a865079 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 71725236 1250 71723986 71724007
    0x3070e0607020a03020120060f060a060e010c02150f07060609050f090a030e0a180510080102040f290705060a05070302090d0209150301020a09170d02060a0c0507061404060e03 77
    0x440e030f0f084030344c2400c110603100030600308032208243c80c03020f100f82d5014020401c4403c504c6290701c54819081202c18065060321400142c0f0072003030071001c0328001003244001c20010b041016441e66000c0000702254207008080d6000c6800c1d90200314104c071060340340da60401c0511894041e9076003019542254050710303c0d000c08040d59604101002804100602c0c0524040d43c45144000f40a411503a4000280c44084500e1901500041c2c0d2032030b8550107105000504580c040c401d990075502c40b040c01d10301e0380340341684020702191043c0a4440444c4000805400c10303404034010943c0c0751046000e000c491801082101c1210001403d8000381401000548810307030300c4002001515078100d075001042d0b00c44115204540f01c1080304030390950310004402014a40182510044a58800d80c59007003800c8070751a00d072544c5980c038208026034001c20104d01d403c1881c0d0010702d00240c11f40351590804500740c40e0070b0140c1d104002d00040c0701c0304e50401d200038091240516103008002c40c0c0118030785080d404 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 71726486 1250 71725236 71725249
    0x306031009020415170601150e010c06020c010606260106080f1306050c2203020a030b0a090512041d010f1403100507030b010f0903030e040504050a020d0803070e060702 74
    0x1a11030003290340e07030426181150740c1c80e4003e2501d10300d0032603041d580c261102e944501e01016000c0715000d5104030300c0000f54840800480b600c2034640e903070b1089115041040152410382015000300d503580d4003480100304004003442030400038002651079000b00c5407503980003000541c0c1c609119800c0032100d07005101c850380003030441b5040030f0154110f601d195a26103840c0f941e50300807807006004c81c3c10541405903032035007900a40900f41045030b0450042c0d42c0d8608c40034400080307100081d008560440200045049200c05542c003422420b004901d41d122541d81c607081c00324204550020030300c046010320840000560703843c0544503900b01690194140101100c0643c800c1c0728803100c01d0800d400c03500258500f442a5402500f0312074060100703041413070018018000d426407150004170306960b1030342820b105401c000b040ba40c15407101303203800106a0034000a0070004100b960b00e8840c5074000e5005880703032040c00ca40280581c0c00151241000200244003201c4000e956100c0c00003800700130050f82e41c0c030 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 71727736 1250 71726486 71726503
    0x812070c06110613140106030305030603120c0a0209090f030c030a090801291302030a0608010b010513060e010e030d0e03010506040e100902120709020d0f02030721020f0a020f1002030603 82
    0x9411201c204d00585013102d06200994591001942800e000104154010300030754010301049055130040d48203202d1801050084502c2d002c01640981956005410004107580d08a030603034044d9501012040300091841e07101042c0c21546610000b02c4800c0705901c054204003501201c0002d000060070a00c0b5203101c090014482012002c800b9128801c5a40b1781001050444003108159280d103400340803000207050a11800c421542840001481907200318120350440940d170711135400c01800e10b041120704a003600d003818184885000003030307410b6404024110050b0310560322000001104001e0500f5600003802040c0911f00b0311900c2040010082002858034004140029008410303000192038002c48000c0f021803030060030340c041082c642c560000d11a400c40c0c1c45090255010121000f001c0307100480b0f409002a400c1260040e0260b11140f910010310b1035124090704100d0407007802d10382503110b070780e4003000742e03101c86061a541e407024407149584803508071045007945080404641c80d40041c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 71728986 1250 71727736 71727751
    0x106050912010605040911040e12040b0306030109151d0c060a05030903040504020406090317090603010b0c100204090e060c07030203041e0803030a0b1e0a0b07020a0812070c061106 79
    0x42070901101d000003540300748000c03c4010000c2c812100c450400c411480c2001100c00d0040742170205103581c0070400140024100d46950700c203407a1038904807901200e6000589000c1d815501c40b0060f2022521100903005003000d208000503e40c00072014038860025a590062641e4105a0b0410703502d80d41c0c0000d42d07503d40041c0c1080c5640b96104000c20b402e40c8190741005134000e10210300407039460740c0011401e00340d910590031080041c07101d503400b06180c0545002503900000c2000188003164010300507066696130441120b8180c5031206400050741c101da007220800b2a81c90003907942c2d10754100f00c0f003600510705034201841d006d42c0740ca0080d04e91096024000340d040390003c1c140c0e0f5000031030100c0001000b01c2030540f40c0724100040d140024240e0b40081500c913040607618240c900c019810a0702544000600106070580392000354805500300e0a001d036840b2881070304c00501d6000c2444441d0400c50002441c40d0784141d5460710600140c1d40d40c0104041101b000070704120114005002900942e1 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 71730236 1250 71728986 71728999
    0x706020613050109050d0206041203020f0403030c30090b0313030c050f0607090e07020c03060708060d1401060608130308010509100312020105070909090b0a020702030307020a080f0d0801060509 85
    0x4003400d10501601304401c000f01540b080a0714015801d90104c0ca850043d0300c80c1c41c81d5068001258011000e170b0041c89221604900c04002c01c20000c2e000d030165401251040d00e450303618a5100b29100761003070001880c50b40910503020000246980580018040d01c0003c03403003070030350070130011500d0788155145004003404868604642804801c1000354616095101241c109240007000148101858070403010004c40d28004903000c00e002040da58003450000d00202500d944030744c41182c00c0c0c2d0010702220340000f510790341100443c4415501490008003840081452807500d1401000440001c00c1d0031003504401e05090006a03000b40d0045c1110002c0311140219100c010100629800310340c401007651003400207030405541c040d089540308900710745070a99295901c1c141c40094603e507480c01040034621000180300c0c0c22041d80a820841c1c0060300712418015036501003880300d1780c107401410059204a026504030b90003000a00c8506240d45030500c000e5241c1180035255000c0d0312072051040c035 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 71731486 1250 71730236 71730271
    0x3013092904060b0304021005041a0d060509070f08150d0f0506010e0f07030504030e13050402210d0309140f07031104020f030a0f0e12070605220210030605091e0907060206 75
    0x18231400590f00503000100c10300340004d40398035013084c40e0350250074030104007070034458000b1f07243c64804141c0d4031510f0f868440076580009050300312007400c03000f0148110155280c1c822201603e40040c0c4000e040e1041c59000d520805500f40b142c5071102c141e02030b094a00d451800c00100340b180c04da5064111509003000b040603100c1d8a810b54400410a0056030010250210f207055442d09401c2540158000d541c45040e8002c10f99199003441807490f070042e056441140f1b2a900c0b14803d520011040707018100f0b40c8010950580c0050614601e41000c1846510045e42441801804980044020300864045140c804140c02049050100414441d811580e4520121200c0401d0700704041c0340840c0700c1650200c00400c012954982c001c50810b07108685400c1c000b40c2c08a070084034000d00c15803848185540e00c9071035801c0002d0014080f40c14410180c40c1c000004442d1034060f40c2078000c94542c2022803524551101c03420001c80c1c005c0448119a01c031100400046070040354494110210285210004 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 71732736 1250 71731486 71731519
    0xa020a0c0f08071a0402040c0f09050f0a050901060f02061503060105042705010204150206131704030804060207032013021806070605093013092904060b030402 70
    0x14043c0c400c0140c40342040c100075034055551000b0140c4581d2084908215020441000b100d40d24049858040815075640c01440307546410465061032200081c50b54094507103501c00702d00c1801c020b92011008c00c5c2c210305010450707038050160b1503100030800c407511800d0407040c000a030b49820610601d4010703596102c9040c1c250b4000503188030301800400a0050008031894814004c1d403091052100c4640180e080e540803500c0030420b41c1c0118805815911050502d490b030040d1030001d04460b076442501000004001100d44000c0c20061040e81c0103485d20502d507080003020111071500110701007041c201e109405940744c0003d40280404407000503220300c62141e40180d943c41c03031a00291b02a4011400724100f045503040300740b01d000c072801502e0028540104089800c0e025030387d10b44600c0082140c54410484031405483c1c1114441c540140050b9034a00d5a0121030100f043c07600c00c180f4803001b80610380549084d10711401e409507130400c4901d1a11140407280c2c080600028400c140804100e400c0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 71733986 1250 71732736 71732753
    0x72103020f07030c0506010b1303062a1701090c051606020d0f05011409010605040605031f03030503040605070203090319021302040b030a0501050409080702040504030212040609030b0a020a0c0f 85
    0x1d04104804840d40d8106600b0040c0c071300203100768219007920541001107090071030b03102915106280d20b55401045415656030002410504903041048942e003420610b080c2c0d2030340207070500c0301c00c151034050a80f20181802014144c0580000344042d082c01c0321514110761290460714458405548a91000035514260000c1e1141058008840c0d0916000d0742698080380c3c0280d04986441910512401c03152092015030030b024442e40010032341c240010001a40210015640700c00d1550003000201d20034150b01900c505140c1054000500100030041044480e100782e64100c80507000442c00c001a40b00083d40c1e881c18050004860840d04840c001152030f4051001c0051110000c1076484507122249a156030f001103c411001c24103050000403a030074a8410b0070145500003140b2031030049c003502408046c00380038100301d007140b041c404d50004c0380541c240504090403190341e410f80d03981d14600f08100310030307405040c80c06150300c101300c03452040382c11082c540020f9a21494140d100c5006082080c070 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 71735236 1250 71733986 71733997
    0xa08010204090b040509120f0a0c02101d040b030715020708070e040309090209010203070305091809011b1707030c23070606060c0b01050f06160b1b07210302 69
    0x102580003040c08600c800050700074010002043d00d0030001940d0740c25600f561041c0501c80941d19a0f810010003000500e40b40041698008a08050750401896404210880c41c0d19841070001404040c0881075000c0c0c18044400c0e00204883c1881080c0700000003036290b800c180710b000e400d81c0ca030b4011070403141c4c002c2c000070000300f03000415141c0342c4d0750b1220b090758682c400300d40840010343c14110114101400344280c64070840c040e0f004500700143c543d4240e42990041f007030740c2d50040040200040c1c1110128580d480303894044004a03044018010000d4070510030340e492828481e1120383c2603100d110740c5090590000c1c0740e2401040070300c02203005032040e2079000c100000f503052020480c1c000c0c000c04001030581c3ea00c0f40204016007560b445003111400c4079450010b00e81c1204100400241c81d0140403a00030220043c2800c0c54a2558903154501c070b100244110756010b00704040020884071030880ca44002005581c191812000c0c1d5258458030301c000008010b022158811a11014481d506641 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 71736486 1250 71735236 71735249
    0xa0b03010218091803090d03091e0e2a09061e030702070911030601030b01020f2a0a030f0803070903140f12090312030a020d0204030b010906081504030e0a 68
    0x660300d90140b08440c91220a42030024055240e4030041842505800380c2011200c40e004044c5040051401c00c2120313042d840041502001100f21001c03a044981550303003411a2050090551b100b840e00314400b804080091107081e004643e6a40ca40d0b6494802600d0481100303806641035940d19030340c000a0250048060b001020711544102c4140ca0800c5c04c0254081c1045400b1240d4480d5101c1c418000d03140c3d91030001138890000e0000c07403440c0d40680c00046201c181401558402d54961460342d00c0c0c441c0800000100210301c2503642220741500708500300340308013039808910150560f01d510002c070189100042c09090000001202c1da44580e0500d00030f0743c0c0c00f984051454010260240d039410b0001d04410b1140144425959044094070844841031009405840c11403c00081d0f40c4880d000244003000117902017000543c554003510043c00a540320301e000030102c1d4106007440045501c140c10408281e400011080e240d90003562003a940180d00d464406500303040080410406075460380045c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 71737736 1250 71736486 71736491
    0xa03050c0c0a14010509010b0d0f020d060203070203130f06020d080a0908070303050601020607020c0a0b0c03040504060f06120618050a1404030e040b010207030b040b07020307050706091404021306080a0b0301 91
    0x82c0c0801201c08903e254245030b00000340005e0f00d4104c0014225685c040106610401c2c0d0b41e90000010040d0090559040c0010322021107103015498800c02d03070340100ca804006800010345145001e1054220300c000d0450000c45400203410108044c0d03845800e41054402e001851000440c215140e80250f41d032180d000b801e031900d96506180140c0070f0318003611014007500808000601c554030004180740903040003001c1d461118909001803500c3e902203c00071241d0b0000b00300118181d00c890142100401d510b9a155002d54546a0000d0030440f1006200340c0c0107040050400140c41c6c0d071440503400d8030800c02d0015540c1c0740c0b262202c00030120506400c035045a0380e0200401e16401c0442d8038030310307841a1070900050154400481c1c6034002c2e400000d10b407820103404100443c05c1c01c030003a1b61182042c0100e03441c224890f2546850002545d0100c40028441001440b00744140790540e1400307941980e065007082c00000e8007c03040c44c1d240c0a86820088200006045509070350895225440068004c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 71738986 1250 71737736 71737753
    0x4060e120f0c0909030315060c100501030b040b010e07020c040209040b030d08091e06130311070b0403051207030e150d140a061203050d090512040e15030102040b0a03050c0c 76
    0x152904108040140f06040b000c0000704001d1002c0100d80c82440b0190040500b03824260802090750070030307520354881e8840c103084c6030b10756016803140e10301840c0601e9040c2258030700f07031074010b5a02405801c540041c40200f0306020070950002402401120111005a180c0302d508010800400701c84c0000c80d8140318000703150f0001900035009034020080c0d070302550317140c4403131492000106400c024444810b90160001541c0900c900d910260824400c6c070b044500e0346106904140382040e1604030650b100d030005401c204016041002ea8036100c0d8401c41c090514113135440181c4000303100030040d4010101c6a049220410a00c4220341d0642402e2004100c0d0701c000060500300c00104840034902c5901e0a10085142c2094200140109505a54651505424400e120043e1080711300c2201c45100e04600c0c0704480f10b00801400c00707854451428102458283c05400c004412001a10b0080e4410801446454000c40031100a03c41e5030401040540b07880804801c0c9103c1c1c036204043c1c0c2d0254601c03 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 71740236 1250 71738986 71739013
    0x30a0b070311032a0f0405010302090f0612100806010b0901030e0f01051315020702060f070f080307080601020d090501081f090204060906021e0c0f030c0306042a0b04060e12 76
    0xa18a020644c4e10034540c000305000040c41c1080d100302e8006803403101043c0700420841d03104c0d1b00108031005000e89842c0507034020a012507000d810800c402c00f9184058800c011000310000340301001800ba4100401301541f4048549506200310030265042680301c1d45180d0801c2c50070045809404ca03103d0007040030307103042000d116010b00c400d1011507040000d4801e1078410345a40c001c0c0d070040303900140401c3c42d08040c000140500d91040000700e90340501111a0008541c803070f0050341c4034408907124120185000c000081c20030304c00d000c161050141c0000144880c2e40c0c44a801341e4040b0700094030f55480d103030f280e41074000600c095001c00c00f410300006021400c0c1d41e02900c03a2007101c040e0340071544d02c14480c03805800d4900302512406130951009548154928000580020440020b000d89015220940200742030400072582030b5081039040402003910351450090400e14141d0032804034002c3d0424202e190103100d0351154104200348604142d40582c0ccd040c1100c0e8200000710116450044802c0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 71741486 1250 71740236 71740261
    0xb090702031c0b0325080a0c050f010c050604080901020109140102040602011b0c0b040606120606050307090c0e0d170703080a050709050609130609090c1e05030a0b07031103 76
    0x1001e11901d01842c4000c02034a000c180100f51011030000d000e00300b02c0b10011040007a603584140722440b42500c180c3c001515070000d00c442040e15000f4042070040500b407109100f0000c80030240a810408180c0120020680c003041840c1c000c6e6002903101e0391004003000403400f42c035020a0142140805501a0100d10415401030084580e680c000703110050140c40f410229900c80030700000407803001d001010001e1a81d80150781d00c188900c50004415032a003148601011445104030b45450b5194028446803401304414801800030900903c94103500b074038020701d4a1807404109004000400c1100708001080c004c0c0d0400208020341651901828180201194025640b400701d4524090204034650f215040c031505842d006400e03070745800003000510007172419800711b01c0e8903160342da10082420703401d60040d541c030340b805488121001c138140040b2141041107074a142220400414082184d920080380d03000c0300316001210445c2964640030150050941e21141802d959070001c1000034404100 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 71742736 1250 71741486 71741497
    0x4060509030c0907090603020a091a0909090d0e210f150106090308030c03070918090309050402030615070302030903011b020d0207060503060d1a040501140a0603020109090f0b09070203 81
    0x4400b207601e002a04024048941425626880054035007102400300030702940040001c62100c0c50405009551903098070112419444502c075081c01c000b4204403649080032071950412a818040c02000200c10000b4105a0701c2c9403005000d03522410b00114030320078444c8102000280c0da01945e9082c0d10203100c16031201101030001d11403840300c100210310300b071040001c030054030f500c04a4180356403205002e258903074000800d4442005090b841c0450780c3d880306140368584051145c40810b01441c0742c0340142000401d900028020b601c1401040620b40d00c8580306200080010840d940e07900c054141281503201d019a071f00d415600380703000b0303020000b80c41060b40c04c104040d038291b405950300e540703080342c441c09244606c0001800600c0440c010307181c1680440c103090301c1044008a501d09a08401d09950f1044509a0b4a03941d10184814603090b05940c45900c441c108900704103441c250fa001a0641c800ca001306240103a8130b5003507403440d0142d0ba0205181250091048840f444e0030440203649603c034 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 71743986 1250 71742736 71742739
    0x91410020712020d02060406020d0b030d050406090e04081b0a0602130e01060203120f060307030203010603140c0a031709040b04140412050408060408131508091507080a090804050604060509 83
    0x400700101903201050813114629030b640038041070744458690f840a074104500c8441c9155448900c0f213900e9404202042e4141c5e05920340c5920303039182400182c5800c465074080300c030502c505002c02002820110032620707003035048543c0c4000f141211075039a1910340200f80040142e07200080519140c45c4a5441c102244c003403140c5500b4583c0c0341c0c08100e0722402140034034100c003441c2a0220b242e4110140e21160321103800390807207500d5580c07a00001e00f554007592045e6048440342000c101a004c00744144d8203298030030384142c42950710316652100d49803184611108080340100c0c81015994a541105040b05001403050200e90204200c805000e80180d404689003190400f030311503502d000e417082e18101c58403c4040c020f550b485031a00d8031180d0200d00e0050500e41511404250920f440c2500010a04079540c0c00981d4030740440113a1801d10348a80c11488485640108000d50b80d110010b581d000010f44008101d1413424606000140078541002c0da0049000c038010500a0340440640f101210 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 71745236 1250 71743986 71744003
    0x40806040c0311011407060c030e030d050406060501080f18070302100203120601030e0705060f09120f0609030f1902070e13060b04050615071406040821060a0501030914100207 77
    0x43c100540c1e21100c107401300d900f200814030441c800314a9a41c445030500c0010308020910112011074641164021301040d10300550320024041032269a10910000d44170170708203200907090141c0c101c4a00c9030024428040d0502070b0b1038108240000b48400c00045901400c400101095a80041d499401c031500a208050700000082c072290722074081e421119900e040544069810070381801255841218800c90280003000100c5560703c07240d00340c0491003800c9003d040b01020080100d424100050490310841d8801c0c40141c14403106902210b80c00901110a000c84500d50382d070990030300750140e03c111100e01100003080101c00858016880c110700c00e4104000e051f0104041104031001613500640185041d1500c2d144229520000c2c202640a00030309001c0c000382c800e92600d09001110304032a1a400447e5460808240d9280403048131840c25004142c0e10b090000309518004510070141015183c90001c0c09001d03070040c00c0303804120301500340d40304d600d6001c1d6000065400881d040303030080c0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 71746486 1250 71745236 71745263
    0x305060907030c15031503050609100b0a06082a0901020f01060311090601090b0f0714010911130207050313031202030a050d0f14040f060e070803070b090102040806040c03 75
    0x103001048401c1a02d07070000311110007034100369000884402911100e01415a1000f0071b80c064014003030030b00021845500240b145160941d102400c3c040e85405c0300e02014100b200a1415a4844031b000c42521102e01d000b50b0380d91340f56a10100c1000200c0344820606904c0f0755075481441c9030300d000700807090081c1c0840b03141c0340c11000d101e8203c4e042440301400c0c010641c1000e6501d890503070740d090f4000c0e60502d0215001c5d42c46c2c001c8150360b030340038041945201400013030020800c0003455103a0070600c940300003041684441e486a084484074403005920461110b000d82d000c3c0c405a074141d500f129001401c43e9103a1400c140c0806150070180401d81700042d40201410035184000122100180142c3c0d41e0b9041c0040d0040c0c61001d852100403880015442d204003240d10360100450500c00d6000f40752403014200c0c20b0420508460408100103416000000b0901000b00000110703000381d5800204080c4030f54803518042d00902803600302103c180103e4081c88144152201c1d40001c0c0da0282002c14402c0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 71747736 1250 71746486 71746501
    0xb1f0e0d0203030d02130816030201140403050a12110f06010e01080706090b0304050709110702010306051507140a050a030906080a0c0801060e130c110606030c090609180601060801030506 82
    0x2100c86a000a50540c4104600d40011340035401402208518203603000466459064447c10203544003003424880b074140380100107560340044164825040a0380340740c5000d0454907416241d50041002a10310140f0010551a4078410040ca05800c0c0c180d60603204d1180203904200e480b03001c01c3c4110003121500b080003081c000340104401c4104c448544605480c94a40b03034a081c0c00d9040140181c0d40d6020b40c04000504041e240610401070140d188290780e183c5040c400942181c00b10340009000d03000442d440040b4071b01d40740840381c440d40c02c00304c481401714070700704482d2400e018102c00074847d0007000e855400f0107401a180600b99074568842c0305a07a52648451011504c01d219014002040000100a11401542d035455048405040004040d080e00c00440c00e44203103810311000680031090740d041180043c083e07203030000011005030268000030300c00a102c880c000f40140b4803a00d10500812844201821040d8500d0440300035917080e90786d95030300580716400034401941d45000740b07000036095 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 71748986 1250 71747736 71747749
    0x2060f07050712020304051504090e0a080901050702040b04060803030103051903350906090f010509030711060c010c0f030b100c08030c1210030201020c0603070503040210030b1f0e 79
    0x1804103035141428001d203602c440043c480a0a0354406600040001107116120000c13218005078020a015544a1401c1854012103010078070b84841034110500c000e000400f81421550500d40c2440e01c140c8803106400080d0040080c1090340d42d21500e8464000f0702c004001c00a541240d019005039660043c02852038821441855001000a0001a620348210202c203050181c141d00f00d46d08100b20b09a40404059002400d862260f0960322a0b8204030041c44200310386600c0b041000000c1c011810b21500b030955a02401100034881d210005407142c4580304c2d0810b90703003022946402440304e100240805000c15600c40c030102d0009042c03449250b500c1c10007007402d11440c01241c0d01c01006107032940700d5000303540001e4000c0a900c001008070010101005003400d018100b04042404030514602c0060b107840b031040500d80c00741c0404d1040213205c0350014142d07907000f5019a00030021015000040b4010301901c401c0f5580300a0300000139a101e455040c980300b40500d81c0c0c45e0118280004000c1009 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 71750236 1250 71748986 71748991
    0x105060d08040504050703140a090507060c0b0c0f090904061416080a090c0f0b0405040c08010e130609020d081207020303010b0d02070f08120712020301050a150207051207050102060f 80
    0x9000701084100481d0a2aa00c065445003891400250425814003a103032680001e0b40c520071240c0d200c0105205000b001d1008400424490a2100e00f09039942d5031040b0317144000f403100d0140c01000c12003080b9840f4101c12642156002040741303a040c98245030a60041480024411408101030001039000452880c0204241e03016161038049a5881880c0c90141c016030030101c644400b14040000c2006000022401401421119a031124280420b010481d02100f10002c00c00a010303004002c11201c101c040354005c070308140c5210000d0030b5410504083c0c081d07000e009410041002e840c0d401e100d8000050f208202400c0846c41c003548a00200701d9590100313000f07042c4072100400c01c5500d80c410f640e009022062140e40f40d64088596601e8540c643c0c0c1055200812180d41c2408000b13110b980428464071003040400d0440c11541001e010401202403401160380030010b810803803011710700800c550002007100603c0125a804107080154072044507210701d901500c5090041074071104040c00c05803 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 71751486 1250 71750236 71750243
    0x20606030109080d0f0605031006090e0601030c0308070302030408070f1d01030b13050a020307030501020306091006090504111b030c07050108040b13030c0f210f0c060506060d1404050105060d 84
    0x42c18130748800350610052254640380104d2943d81e40c80014251418400098500000c40e030001d401ca2800140c4010307603120811208058208400510004250800f90801d0b203402c13894154542c1c001707140c160300d540b055422042c410700c1410f200003041c2c000c2c5502031080e1181450150300c41c058003c0c03400000402800010155809040051203080300a80420815402034040b00d10b01e10503900464188000c541080e504c0e65000420003089040c031284c01a0448400c4a205030400e01e40740008140f03002d01d001d480e204541707803900e248100c07544905035442c44a150071032404e0809010201070b41e0394001d5122803040e001d04000090b581d070007660306900c0703940c0111990000f55101e0820b5409002c44180403414010400b00e070401050352030401c062094400c4a03041445140d040e450203150200c02c1c03840e002c0084c80b54402c01a00d9004d01b01c41700c85540400089625198030000030040c0c002c4141e041c00840c41c020449190005004285024038000c0e4002c0155480710010711034103c643d440e002d03 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 71752736 1250 71751486 71751503
    0x14060f070503100e1302150301030f12030605040513061a0f0f01020114240609031506030c0d0615060201020c07030b0603120c030a030c03050907170304030b090706020606030109 78
    0xc0c0040e010300021544051440107000005403100e03c2041482416038240c03252800a2036424114282800707000040c14842900b981036602d1035540e0300c00c0103400d507030080c000e5555802c40d400403402a0015009460020424010707841e0100300c1c09998130300c804055400702d09107900a04c41c222040d102c804442005002d540100d82d0344018003455042e01d800a604540da0380c1d454100380640210381a01030700e54107044d59044a01c0602451540b101404110301c20141040304102550b40010200009030000b4180791460341e6079000030707041c98400300200c1c0d0800385040884041104039400464501e1654049d549005e4a514080b0708034052541d42d00002d5000840071b00100301496081a840040281120b80d134052100030050590010040303503116910101e08500255094026030003018424a8204103e10b400c036452035480c4454496600d80d0b60348426041080d060500490b400703150040c0840310a824003a0300559600c005105620050150b2008a14140341c107011307000d045504100319 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 71753986 1250 71752736 71752741
    0x904081207052703030409050906090c03010212010302011b060204090c091e0e0c0f0a1205060d020f040c0903020d1b06080408040b1c0c080a0606080f040b070c0804080a14060f 77
    0x20f0711100e031005042e5032511041c00000380e448100d004051040790410058602420013403009842c005440001e1882a401800100f100b4003503441c0d21411640c091070441d144400034000d03106120700080c2c024000600000700410000442c0e000840101655078584294640d102c07078103200102c050b5101d0440d03e501510812088421207181500402c40740800f61501103501701d40d130100e610800f072a07408034400030088841b90016120b4a54001c106540c8001003980c80e50001c0d004012040c040e41c8180c0d600d2a1511110f8855403825000d10781c0580195010200d038106182006062224090351410130704e00031614500c00c401c0d4500480e840fa20b1541498101201c60040b50814401a45464940b41c500564072005006075880803607140c0f00d101540c00c00e1690072060741d815030003c1050209505c28000c81d60408104551b20a4112035404001d0300c03101000c03501c03205c180c50f018043d10404100490700c40000301710003060604c00c0c140c1c007040c0500c2d0304030603031150000c0b03d0f810395030001d030b800 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 71755236 1250 71753986 71754037
    0x6120a1b0819060c1119060f053d030b010f051c020609041103131e0309030602090d0f0c0e0a050705121503030c0f01050105011e030c0e090408120705 66
    0x1402c1d10070000d0804800f00b800601d4054078140c0e01b2018045600d6071101c8035000d101961003003d140307148400c0184828030709004284803900b44109141030344c49050900303906c004080c070038008e010801c0e00304231012a0b41d681010b0740c2545007030140d80e2039022014800252450821100c80c2a1b074002c0000041c80200c64007000295084040481e402a1300c81c1c01d08402c005115000b50b1023070314183c0180444c20840d0070308101d544101c119a02d1000380e2608040c01081d0445200350487c0e600c01000b40e91924030740003188a440600d07200600c44118900f450342000300f07040e0048140c8600702c00304a03c0343e880849100c2603130016500c0e040813a004201214142c1d003081c030750712b078003040740c04102a10380010b001080c1703540d000002e5054240c02a0005513120402030058600501c0c00346048800c1a440d02c44039200f4038a0702c0340301024507030307150340f080f0344940552074110214100400d172603140c0c030f0300d403c099980d40e00182219a03842c03054000564464068010b540704468044082e9890210400 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 71756486 1250 71755236 71755241
    0x50f19060b060412032609030d020d0f0617240f07020c1309020103140108061909021801061205010f170a0602070302070f0b03041a06120a1b081906 65
    0x10070464008104000104050203d0440c081d1158800d5884201d031948051454454600f6040d41d00da040c601c40e02400101c46000041c1c079019460480e005a40d1070325809c004009100800c8940ea256040480003d00d00d0219664142502982c0c03095410b003c4600140c3e02d001444007600d044656010804a005100c000e91170580c0640c1500446c0e0003403892000107640010761810401c0082c0c0c560304070204650780350107400120001d480303d0700741550500d603220f5240c000c0203004207500d81074051101e03031036802030708001d01d240d0f000303002146090710030075205843e68070901480021035880d0160b1095007100d480b5485c101c48800b0243c196490901e030000301517005070710020265114042c210300114100d84000c10100e442a001450258904021403541c2ca4595100415820041c810031020515842042250400d000300e00f00e600da45500c0010f8883c0b0f01190441007510840c5054801c02c000309060701115503200c2c6e004807615641c0d00746c1d01c0c0d540405001d80c8022280d0641c0072000220b058 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 71757736 1250 71756486 71756501
    0x1021203010f12080706050a06050f040209060702042301030501020a030b030a030e010807020102120c03040c050d0f021c2019030201050f0a03020405060a0215161e0327050f1906 78
    0x544005181a45c00d07114402581d209590118890740e60346000c000628100003800c102d0802620150f08100b4104001416405041740190091392501c1880113078106480d550202000c1c070440c0710465584a0400030b00075080b003164030001c01e10b08080c88000d403030b00158001034a9495603440c200300d191500116070251018181d8019990240017400055510300180d5200d400504102e41e224501800d1062003007945d540300500a090305014000071529802050081c41c1c0c040c1e41c07600c4071150150012510040c07529018000c902ea135015805228074800500400d800112040079000d015028007584090b401d2200901180042204120070004903000d401480043d040043c02c140e9558041000da91094203c540148c004e600c905140c814240290350b0851500441c40810300191031016042c070f41a002c14044082030600c3d142c080c144240c1244050816801c101542c0881e40040004407413400c10040b559030240340b00788401a88000380c00c41904c0405101e091041c0703003130b440d20801003804 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 71758986 1250 71757736 71757743
    0xb060a0c0503091309020f04110d09210c0201090501020c0102070603050a0908070312050a02041404051b0c0c0a080a030912050c10080411030106051f0c0f03090501021203010f12 78
    0x2440b032110f442e0b0301c940032030401803007454011400c20443d104000c40b2442c141119403040780341810880c0794440d544240c5a170160300c10f000086555103410322410300d40d128411066948840e1200e4040c0342c0c3c1c419a2400d582e8801c1e01e510050941350001a030311410350b100e405005a204880c1044414032982227690018904034000894012542311038240307500000301640800d8140e45036441d002e406110790f40e4031020303202d01182400e09000d040e826a0b2070844000744203d80b07402c089100c80341c004030606a188492020703265101d4015882c01d0300c80c80d8003440300344a8610740318006224100807550901d150b6243c2d13589410f841c10070265020003020312509540500c2449204151034a805e103006040c540180c5407043e8529081c904032100344115081203009905115003048135885451130030413081c09505404920b200c030a0000c41e1654403070100500340c000031540140600d5080300280f01070720310a0b800d942c04003841c010286d4251101380b044402da12112001040380c1051844c00f5640e00d0311 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 71760236 1250 71758986 71758993
    0x39020c011b02120102071208060d020904030e04091101030606020303090712031209051f020909041203140f07030507050304030e0d02120f060a0b0301150905060d020d031101060501030b060a0c05 85
    0x3030300468540783d011884260180e41c0007815009001c204000c0d5803081c015032620025038907251010806030b41c0728040080c06035011102040c1054041d0300c0b03594443c0b001800801103d9081e060581c840003940030054082480c02c5e1000c02c490b4400301c101c074421204030004040e81480c0000d00510503200c05401c0e4100a04d413007a07840294242d0190101d0b060040300100b40c3ea500c0040860b55401c0c444401c050801d00c1045000c9860720382440071f40d4404d07040309102a01e02d40d950010b8014040381450602d030b03d0440010008111a50034915000c1c003015074040000383d84001050303c6900c1f0030b48018002c20074a1b50f5000d054a07110700001344480c8041c00c000d2001154840d41490908507404072410341e0040c1040000e1486a0311558010700c00481c0244651750364005d04109640c3c15004803402141c407140007820584640c0195503107694050100c0904440b9400d0040801140f511100070329420094005102e6200780500032415800400452411908802c26102498075810466003400f = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 71761486 1250 71760236 71760287
    0x201020720010315180507020316080d050604050f01090f0f0e0a050c032e090803010b0310050901030c061101091721010b09190939020c01 61
    0x100703070003400c007140340c4400c4040060211800000d0241c07030810f6282e01c0100d103050342c01c2040c50001c02d003110044007180c90000307442e101c80340228113600c1124000100c200345203205004008041c801000c03040508403003006207403141010401074072416030708002203040400040c0a640350660041c8106030420070001503c0c02d00c020761f40203690061044401e1908a00000c1083c000e040c4a14060200210060300d142d041c0c03002010741ca11141d01c00801d42d0081c02141c0c0c0340900650f032206200a400103201526517075100303c020b005078030440c0c4d00d8100303c484510001d210300f00004a04c0c182c0ba80004109010b03824140112151000c0c54000200d0b5902d402203100481c04450403903d00d401c00c542259130f5503980a02440d644440b24840c007220f100305034010020303103070350001b0b07200d5520085514990b90070001c11032805c83c1d40180c000104151074508030011441001e43c18001107012440c2000c2161000100010070411241cbc1e584007503001030030740c05010341c401c40a81034050f0b0428006032050 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 71762592 1106 71761486 71761493
    0x41d04060f2f0c0714030d03020f030705070201050721320306010c06110702040e03090d030e06040f090212010e010609090f0b040207060605150a0e090702010207 71
    0x15641d460608185070700040300c4540181004841d08a81c0b103001030b00410350389650045c481d03c2441503400311580240240c0c1c403031880700c524103030542d41c40071000d40d490f0f44943b000f281000010015080040e00d0902e0042a603015403041280906e0b111001600341102100055a106207c503052400c0901d07410b0741921021801c03003125125150a80140e80b2940601d000400c640e0500c03188180600d4000c0140201c03070300844042c0322543c40c8500711512441038010301504451a00c0540010901032400042c1c0300340b01500b090b00d0a55207601410312244150085e202c20358002800d4200e80c40500312103800346c40c011204c10000d51411300058510003484c401c00030200d031250014400cac00c10503484001c0b41700001d40b040d90341da41c1a02d070100042c08203000e818805c60102601040007140c00054441140807074941c154410860420002082001040241199000c03c40d07403000 = true := by decide +kernel

theorem cover : BRFrame.Cov 71582736 71762592 := by
  have h0 := BRFrame.cov_init 71582736
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71582736 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71582736 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71582736 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71582736 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71582736 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71582736 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71582736 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71582736 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71582736 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71582736 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71582736 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71582736 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71582736 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71582736 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71582736 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71582736 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71582736 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71582736 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71582736 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71582736 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71582736 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71582736 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71582736 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71582736 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71582736 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71582736 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71582736 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71582736 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71582736 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71582736 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71582736 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71582736 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71582736 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71582736 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71582736 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71582736 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71582736 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71582736 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71582736 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71582736 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71582736 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71582736 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71582736 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71582736 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71582736 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71582736 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71582736 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71582736 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71582736 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71582736 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71582736 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71582736 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71582736 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71582736 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71582736 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71582736 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71582736 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71582736 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71582736 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71582736 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71582736 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71582736 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71582736 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71582736 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71582736 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71582736 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71582736 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71582736 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71582736 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71582736 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71582736 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71582736 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71582736 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71582736 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71582736 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71582736 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71582736 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71582736 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71582736 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71582736 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71582736 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71582736 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71582736 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71582736 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71582736 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71582736 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71582736 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71582736 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71582736 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71582736 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71582736 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71582736 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71582736 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71582736 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71582736 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71582736 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71582736 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71582736 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71582736 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71582736 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71582736 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71582736 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71582736 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71582736 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71582736 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71582736 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71582736 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71582736 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71582736 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71582736 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71582736 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71582736 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71582736 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71582736 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71582736 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71582736 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71582736 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71582736 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71582736 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71582736 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71582736 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71582736 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71582736 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71582736 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71582736 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71582736 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71582736 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71582736 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71582736 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71582736 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71582736 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71582736 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71582736 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71582736 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71582736 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71582736 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71582736 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71582736 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71582736 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71582736 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71582736 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71582736 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71582736 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71582736 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 71582736 ≤ n) (h2 : n < 71762592) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
