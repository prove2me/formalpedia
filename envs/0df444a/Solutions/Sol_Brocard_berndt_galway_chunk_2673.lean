-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2673
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:24:35.9842+00:00
-- url     : https://prove2.me/submissions/67e2b450-377b-4699-b96a-d70042558d58

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 480575539 ≤ n < 480755395 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 480576789 1250 480575539 480575551
    0x20102130609030b340c0614040f06022215020d09060e040c0c0f0f02120a0302070b0d11040801060e07030b060910110703030207140301060b04060c0510090b0f 70
    0x10750010284001508140520790080500301c5c2424600808003da005d9104c0481008240190920010345210f074440010418580905401e01c00503500c842c03d000e0140080724041d1a8002500d02036002a0300740d00105101c2d0740b01d0444107050500b01e00c0030381c4860000d03403100d412007507070320000308480c0d405018561121038141018180c0342c0c03030007074081c002c0f030821007000c0d00ca0399903200803100f402c0c0121100104103400910800b907242d440d00c8d00c2405040c0c01c90701640b16002501000c55002c3d00018152400395040c2d0141004600d8001d003068260491100e021078151074604512100344044040c100601d180750010038013901e0700c80c00242c05d04018152808150500510020507160841200c0e1b01c0141a248450703444242c5e00d041391601001c003c5402a40102c01c0d0000c24950300198040035225410040d0751a44181c000f01030072a01c3d80d1248081c081350601080213103501171008482c2e10b13400b480640f0210b03034070090081e088500300d00781195415070714414490014007c0c454654461 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 480578039 1250 480576789 480576797
    0xc010e061b03130f1b1217030105010e1201060314060f090a12050d0609050a02070302070509100317130e0121021302070602040e010f1d10120503190201021306 70
    0x3042070488050760403855900a801e0865003440381e410400059000020b0410005c5000c2c60300e510b81503c204c80c0c480c00c20f0180c440845008a800c103400180085074100c0f4016110740f1000311000382401044180c100d2140780c55544d510307000001c25420030340018001d400202810203890115440711851a024004401d194890944040003402403420084003030780c0c0e414016160503141030044d0281c081c0d81c020204141c24281031101c1c0101c6174011b802c8840c840e40a4a082503292010301211076012a0104444100814104003207001c9117520706440004117a03151800b00c0c2c40c00d0400030000e040c1c4c40500385111302c8004002d6044c1d000940b00000041861107040c524054001a10311001c1100f104c00041c0e0000b60300c010898150b049a004144040340c1c46450360b503a09901d260501a44502c207000050405542c40211010350f0151286010b44045490642820500003080400d41d204481034801040881d0601c400700341e404100102941c00980d1301d030002c8023001c13242401d50340040c040c4 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 480579289 1250 480578039 480578041
    0x20a02100807020c0904141002090a09050402060301030f140604050d080711070e06030f0709021201050a08120306060c010f06051014040909030504170304030605060a05030d11030c010e061b03 84
    0x10b6804204c20680400403142d6004503151828460326a2404e0520f0200910520000148039529500a46120181107820803113166540781d2100503100102c070300942c448000c20040c40068803140c5140b001e140282c940c0c0b07441441c2c590f03116280240c10345054540e84e00103000a501990300581a81e4007100d1840c09081580600929a5031803005008603071200c0c11800009050f900c0801409001c4070140e0200d440d0700d640d40080c84000d51000314002c10040044001284904012400d14115000708000f082080003018500a50340c00184c0415804642005040c120713203000d0007801492580c0050025020307140c4010001c580c002c2604240c14007000080403010341c00c10703005507421144d9114010445901b98941154980300d660001034000592103680360402e00000050425a072040004104135120341c0e08200f40d400441c80743c40d52651001341ca03080340d0346c45110030040f189114421a0b0600d03c6504440d829244500540c1e01d071544a5801c006080e0005103c84150095072510540382d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 480580539 1250 480579289 480579301
    0x6040f03020a0909050d0804030e0604090504060501120f030809010207061b0206160518030f01020a170c040311040c0c050712031b02010905060313060203010612291507080a020a021008 81
    0xc6d4601c84281e042440748140015081c103010311030311022040e0040030709a56a840704640c100410f0240c1e4160303189450507002041202c20851030070300d45a00f0608415801c0556030b8100c174144d80060030800b030340d5000e02810300003c445000f0740788104181c0146a03201d54103e0b00c02864030900030710130142c0e0b80b0f204400c41c200e160084112240c1171500c2440000304070700b240c04246018031b2400801c1c03044d0310014426003103d90100504083c4e5240d064a445192507400d019006806180009419160103103519240c07071038168400d4501c0e1440c4c1c200040b4140103a25620b040021a03031080744601100043d0000f0075501c0010f690301d00e007080442d12a01c21040e00001e280d0303120b50090901510000000c03400c0354a400410110107940210190b40d60740e10b5400040002c131a072a180a0780c00d040c50706821a8200101010804454000005c80444015000c105a910500d00412610b01f01082010b02180e0080018440c2440c590009d100d0003050784103101680070f08120031f03401c02c00010f00b8426 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 480581789 1250 480580539 480580543
    0x807061803120209030a050f0303061c0203031c0e0106150201142202060c06043806040f0605151806120f250903020915010e0d060b06040f03020a090905 67
    0xa5482d821a0058691503c01d010910300722001c2c5015155100f0650310fa24102d50000095205020a54045448070180100c4960307141458600a6041d001440250700c0042c043d00c8013140c00c5c24185001ca86003841280041c2100d10a81100ca00d02040368000205281c09015180ca42d00e605803c1d0940341c17074130303000d011422440c0311210388094507415040c409558941081c0c0301d1a0805a09940203401d06140c8450301400c1e400002500c94145000c184285506640107a8040d801803008007071540c0300c01c00c01c0f00500f86014010211650b07200007003616116110088900b05000b40c541d9940d51440142c0c04200c0384a40e074151184500301b026040c0c41b501004400d42010502030000560340b2035400100c079030010704100d1140074003441c0d20304414580c010321110449000382c80b02603c80c0c44e2280c0e4409107000402d00c0c1030202c0d081881c0f4048604105000020b01c0340076a1000a810480308000398103a170040d8000030a0500079001801940740c06c00d400030040c80c140701d040018000c5603441907 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 480583039 1250 480581789 480581807
    0x3090c170d0f0903022103040b18010807031406101211040e15130b0109090c080601080f01050a06110f2a0a0f0308130801020309010e100905060105060a0e0306040807061803 76
    0xb080c051b80d50704079250028000c000341c038041c00750086e1080d140e5091201c207404c1c203110885034500040c0c9840c0400c0119000c0d22a8012003427211014811540d100000d010641c15003102040800103880303103000390540740d07100300183c201110401d11780c6c40d4500000780300d00d044003a002400c1e60301100980c8641e42e4503101c2d15420300b500001c010406c1c09207540180d440d13001e954408100c842c1080b0300c1c2080c03503030f0000d0440e10540c4262104015910b84400140d000314007402411f03040b074000c010601242d405000161041c0358080d0881c1c80301e00441404500380380c0740303014000301c1580000750071030400c400c130f8480c1840f0081660407604041c9013504c0d0807030350009844080c121140004140c001c0311131049100025010850003075641c0e040c240c11940c02000c1d030080d500c1c01400ba400c482d4018900c18000c1c2c851050f00032000300866401c06c02040030329444038841c0400c4c066401d90720703011610140b000900c40c50040400c15158011400c140c0e003a5a03000059041565402001400084e0845101 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 480584289 1250 480583039 480583069
    0x604021303084015081618030b040218040816061b021501060206070e1c050601080d11031e030c04080a0302030318060f01170a020306040c0512060c070303090c170d0f090302 76
    0x306d50840540c016102c104e10721402c40507460f00b0200200501c086510241c0c000c601c00e607006608402c2150303034040900010b440061080038100451601d8000c40701d9207880d80390160f0000140c0ca4805000c40e902d0310311340b17441100540c201c3c4120300d54150b54000201e0050015001622051034860070080104489440c0d491103030054164004540500c06402c0106541c060202c0362513517110902c03603996150301e11003d070000b83c105040040c0e100d8040251801c110b030410fa00c40440c1c3e9503c80c4070300340345c10082c82d81140020900c4006062201004440c11150094014550b42d0a140c0b4403da802400f41d07080040c2a407200c0180058808007049050440d0320540b4105c1c0d030030108000d85807c03d2040300000c1c3d40762140ca0700384800d121602c0d10340c0d0100c074801c403602c0100c0b0548510b116140d030700032240014800740034440c0c20f01080c0640c00420900e03100e210030b03082480d00c0b20388521005c0044164941d055205400c982400398120318200310360101030034143c2c102855940000c11004080d1f200d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 480585539 1250 480584289 480584311
    0x31309050408160510180201050f0a030209061204120305010819081309060f05030106120605090a0210020309010908010e030904020c120a1205060402130308401508 72
    0x290a020441c410b6881402000b0403250354003d160800c190394048858224441c9864220b080d1140c0300d480c030340f0a86141d410b07101c550921172002c5452039550404100e50061540030041c03240582d4842d0003d207600c03407030408800c0c0d641c1020b0411000e5806d607285540189441c16006000c080c0d80018040a014582032071292031030514070700401c3c24000c042c10000810062000440e0703084a80e00250103460204520f808610303038a104050a1341d08521441140400c500020400301703c654104075031002000c0100c400016281e400b1509545403060f14000603000802c40b00480e61f4484403000c01030a21744024401030182003801c80d101d1081c5000d15115660000c0c0c0c0c00400e400038400000301d00c001c0c006e001c0c3c940e5889540a00440d0280b1030300c0f0b525074a030000040180c5042d101780c804041e40180000e042a0441d640d41c182075001e10b0350b2400140668210b0080761819011440700f200401410545125a10488041140f102d030490100703003412003154000260b10070b120a601114104c1 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 480586789 1250 480585539 480585541
    0x60d0c03050f253c0503060901020427090b012d0602030d020703090306051302090a020a02070605092206081506030c092805041a10180f14060109060203130905 70
    0x10500c400603813805680c3c184101c00580381c1010f9140c148124044a1055058842c981c1e0303035401140c200e100b00d000d40411100c46207407980c041c2c00c140404e004280c0070110002004c101640f284661070900340c0c040041ca4080b03101c01015028450380f11b982c202c01d0035032448400c038113142010351280a0711016103140e1740c0c042801828140300c2c1210400842d0012010015400e10003c24070040074640b40503401035201e04007040303a080040c400c032030200b80281c0c042c4c604141000b100b00e5141e484815680da22400644001c030000c2c083c10301020000000f03140004500b0f24103d80b490130900320800c03030094110000100142500c002c90b80a1000380111001c1c44503903904940110380c007483c100ca1824040d61903122004031240c5c4c0d88410f01441c01044900402c0880c031441603440c003000c98000080001c40281001007910422101d10600c191100100381c58044c080240112200100941c401c00710720790512110396045001500640b88034405185040900c3c48400000c0c100c5e845618215942c0d03070 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 480588039 1250 480586789 480586829
    0x41412070605090d200f01020a110f0a1509210c0e0406150b210103030c032f010b0f030106050a03080d0f02070809030d0908070e060d0c03050f25 64
    0x11665441d5900c401100185201070001c1da41741c001120384c0034000c003c099003030581503000040300501140d0001c042905107040c4401c1c422030356000450385410000c402008129040d00b2140b00310381d01c94541e50404641d00c6c040c000c896201e950b4000d8060403c102d142c0c0f1002c9501221b607041a0b0b0800e02004000340c407107142800042c2221421509400c3d46024007003600c180290040019000041003000c9844005004e810760260038070004011038480b01c403d50010740240442e846404006440c01072542d00c0c8ac1032402601c078902200b154596490700d1a24007442c01c00090448a141680200915070400e40810100303189400050701c03c0c0310203e60400d460703400d5007085044150504081d9165042031800d00c809412100985101c0c0c0145401c62001e148281011304c03c40d491300700200102403420480b01c9284001501041d009642000700f030000c00c0d641f14a401c0214401c50081c58185155a6001e00341400c05134000306032500450060ba4081c08240c041040c0e078030054051081c61070700307 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 480589289 1250 480588039 480588049
    0x5100c052508070503280e0103050a06172a060901120b03160302100c0503250209070203030709080604020607062c0c0a170d0311041a04141207060509 66
    0x200764010b20200c4009003074401c2081c088050090704400e028151302c10104482a1405a80700039903d10004248150318407881d80302e80c20458101b1213103a800102c07507464140f110a00f0260803038020032948003401407040d2001204080719071010010b45a01e8010008002031018485d203a0410304100034504140c42c102001e9100d6136000d000101124010804d409880c215844548030907445035410341c003201540c5000790304281c0c009511a019500e8009002c80707010000d540d01d0340e031242140c0c40e26440001a121130040034001c081301c2c1c0040d51070345403a0b88010240d501c14ac000e003c0d01d80011040c0801600c4507019240d50590001d000700781c03d0012420400e00001e60000101200000d003209102c40320b003c0b418bd165a4420340356950f016859107503042c00d0300c0c11504400c0b01c507444480d80540092103a40090305020014210070314140e65981c221290b010142c00c8443c44d00b02c0042c04200c0409111400a4142d5003501c50910b804070341d5656940b00c0400380f00e40070a10500144000c080d40ea0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 480590539 1250 480589289 480589357
    0x2120708070e150301020c120c030904050c0310050d0b07122a110c01080604020901090e070302220302010818010e0318130209100e130e0a05100c05 65
    0x29910440301d140350307a6041101008801d90300c140c070683c008a4007002e41e040c18000c403024406000b00810400d040030345c3e03007030141d0f111a1000d0124007040c80640402d948900031a409620309a091544074204900945c1d400e920a80c4101c0c4160002c00b01c0348002558850900d0b40030200e414085401c01854209202812070b84481035410000c21144101706080c07030f01d50b42e2002d210307580c07001d0040c1c0304090019525881c2039038607030104558000145a51415800034001803806151413001250380b16103070101030000b0f44200e00825004101c1e180c20491064102c03160200d103c01898850780b941d00041c0c002d050242904100128a01d2200c9604109400039901c1c101040103c89c0c0e609030768001c1c07544284034404241c0c8903001740c0c455603540440c07e000782c0380002d600a00190405040f984190b40045480103240d41054840c400c03c1c140802d54030400c3c1c1046100c2c40600341c60031300c0389021800c10407105222000103181100040074180d1180a5a0001c2e5a03004d00040f81c012500080907028a = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 480591789 1250 480590539 480590549
    0x3070e0705070f0321200711090103230a030c030804060605130e0f0c1804170304080a0f081014031203070509011803030e0d0305070606090617060f04021207 69
    0x140101c0c2d0800c1660044101c1c3e180c41420381091a0300314051800c8042e102d151000700002c1ca2041480148048a80c005003c0c0c0e500c108e55600b40c01c08802c002c03c1ca03402c42684292003a9000e800c5001071003400340d014441d0410110050145900305603070150bd02512024003908001c0118005000c000503940540003801c402400c60134000e1454003044050088544401e80c14001e41c42680085100000c2c40454803400410581c9422031100c2e100300045c000820507101014482c40c50011221a00c005502860142540650b10620f901002d1302d0341c0f4500c111300e41040900c400304500704003890b80c01019103098038448020004100d00292408200200201c1e80080002c01e00030381c3e0fa00a4018020702c202070f00c813410380c400300c0002103001c40c0d0184800b4000c01d1701d1603081002890090034070303031200c0e00c03d040542c2440e1090b2503400032100700fa0025400a07070307219800d110142e542000050103401c041c00606061074181010300840030007400090060702c03003900100c02c0c1ca40500014000d01 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 480593039 1250 480591789 480591803
    0x1e01090501051821041512020f070c050d1511040e090c01080612060c0a030e010f0c080a0b03100906111201060807030608061329060f03010204030203070e070507 71
    0xc1030182c201070742d14031441c0c0f5000b424824100981c05248102109076018045422040d003040c0c41c01030881500030060400c3c1c030411806005800316140203102802035600c45461845e00c42800b407500e000f42181039040b19104807000303403005000036004da864109880000700b01062003150400f108032a40510b802c80280c40040f80e0400225803400030304030104d03040998500c05251108418402c8444044645000b1038110400103105e0640c1c81d002816491070074500064035592001034207007110b4000a425046681341d82c860a042035014041a03045110040104071000403800041e0b96414040051000c06484480050520405510840805a04800607a65400710407140c0843c0c1c81700b4002c00b00400c0041000c24070441c400d124020503110301030006c050a44070703501d010340465036044040701c171034100d454a182c01c80300011040303000d0700124502c004641040420820a03804603040b0030700982c4144020809603400145a80488000c1d0b43c1c0d41081e45c51f0200202d80d180328003803020f0019 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 480594289 1250 480593039 480593041
    0x7060c020f07091a0d0308070302090f09070c0302010c080610030f062711070b0a180c0f0e01050d0309150302070b19050a0504020a050f220209010f050c1e0109050105 73
    0x103c0540e03000f000002d8160014800ca1942030010460210408200500012202c0c00018210350180c1d00405480710010708150000c0d07403907400280c4149084031b0303c00000d1150b40150b001c1517024041c018202121782040c000c50b00e4480d0101c1e082034107503180c00f8201502d689610041c60941d60104000e03094a14103c119a0b404910000c6d0340e10030784107003060451034043d00560310a4140240d40e581d942c800800386168540d64005006400d103000200840320780446028001031400070760200404d21091421141c07450091004070503a0142d21240c0141846581100004e5000c4901c2d400d5072502110030f1b404008502c4110005c0c010801d00034800c6a0f140d0900c5411003410b502802c100c401210140020356840c0b51031025070f6000d41d4005d4003c0346d686000e0005140907151a19003400240c0084400710555030352500c0c074070000f007a06001302c0d40060702c00d074030b544d0104001c0451503c50514515102000202d19500d01a0301403040703e0039410b2119070f5800601b034000084042d0810002e00c2a = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 480595539 1250 480594289 480594299
    0x10b15161104020c01090302060907051c1e12110601080703030f140a1701170706112404020a050105040311130e0102070b0a1521020f03070e042607060c020f07 70
    0x13024806c0040d800340c485c14001070a40c590018402c070588501902c9030000180030003495940700c1028004031100b50440c00f4060020510340d2001c1282030040d100900c14000148000d004001d035580c0002e4103421060043c001e0a9000589600b220f80c180780a4801d015001c2d03045501503404d0300609084840080e00b07580481e0312044c01c001c11400711074030610031f0742ea03015a121803c15001d0041500d800208040028030b004000c40502e10300c156003501c400e0200b2401240c1c4101d460a002c00000802d54103020035820408070031409080d080c28440d01c2d0604585030f07564031032030310100705105224014290029035030603040b032905405044000e5403a02528605062456011590288803600c2e0007a1800c1000740929400300300c0348900480030380c44003400003840002003000300c140c3e0802541da461101c10b490800c01600144043c5905401d241424a40401c943d500c0108103400c10000b5400c04903190151405ca0341c0c05a0f11100004021102036000da0911908410b62103040c01181e00010b0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 480596789 1250 480595539 480595541
    0x30a02090906070f080721060b071a06030a0c030b100e0106050c0c010905061e160b0403030f0504120e01140d063015020408030d0e010b15161104020c01 67
    0x409462281c4800c21510100f190480d8000021929400001c1f0a114211400140024406141e4040300301c0800c02035158240d800c1580d01861080301c40ca90000d00c05c520305442203001c25042201240603242401031625026500b0140d8000600a0010b08002c40c00c050385c1140e070312001b00036288254401e580d41e54800b510702d0300900100303c0760b8004c80c2c0104180b580b0500540c0142c4100070000787c24004000b45101c45148081400c000c00d0800300301c406042264500340314180c51081d801c500e6a80f615140041c141d9100e0b0f400400307200c2c01e200034000001c1d0b5604504481022a01c2d00741c4101c14106c004035100114030740b4900140c03000059400714407845c1d400c10000e0f42c8160368403858000c2d4042010f40c45c81100300746080401007824412000a40f440c420304d0103003054140c090706186e187e280749411644150354001006076124000f11100b00e0a00400400c2001201c121440007485408e82e85544515141400340083c500720a40402541c0380a4410951016000b103490b070246088540c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 480598039 1250 480596789 480596791
    0x30912033f07080f06101d0105040f0e09070911030601080903090405010323030c15041a070302070201030608190611070c2d0b0403110f0907031514010203120402030a02090906 77
    0x39004e01800010528103019000070a2010195550308145080040802c9900318089030281040003c00c07000030303a105940c3c0060050316124034038615070308100c40b44629151540d440300e91a6802c0078442e11021812105403503100500b82044c0d10269100440d140c1503104118900d07500503c3c0100100501045c1250401c800f6442d01c85d80c05407504158800e6940e00520058080e194024108004034600300d0220320303040340c4141e0603c4002c41400781c02c69a6104219a00e01c0000e5020442406640e41030040200421650307000c1c00020740c148400ca20f0402c0346141c017800300c1d80c0714901001f00c682920100d0380090740043d03c801c0b940d80c94901c00303552207582c0c0304004d68456500c01414408603011706517004030b0382c44008070307450645150348405810200c1b00489500c070218002e44080b5403164002c443c030900720f03650300040702c1401010f40d5112a545401c50394400852402c03078002a40c000040b11490f00600c0d1200d1a15a52440040d181c5a400c5000940003107a1034180002c503d00043e040d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 480599289 1250 480598039 480598051
    0xa050714540f0616050c1008070e040b090f061903030908010b01030e0a0b0a1d010b030d05090a0302010507080405180a051506070f170408030912033f0708 68
    0x5518060070008201c0350400c00021a540003400b0803070000200820301965890b184180c054900d03403118000000c0c00040320a41c11000700380c2c1e0b64100010194451302450200704110f40410040c2210000320700722200040c03160801c020f05a01040316a581c21240412126a290100c002c5c262280740c014080081407003515095804c1603c0000c2946c020b02481035a00d0802c0300900c21403007280c84080a41e180541410412541c80001401d0010301000c2e0217000032940d000800c52001305e000349890200303411411400c01500f13100802540da03070040e000040340e80901e000c83e00c1d090075041115441c4101d81c0030950080380a07820400b845460f00b2124400c50a09608104a0f0760700d80100402d40e03210030101e64010310400c024070003c0e0017011818400d41c0078803104404016100c21284055020345c0101c02c10703620109440c2803d2030010142804000404043e40c04c080404100d40c51110702040c46600c0100041c0c003a40c440b60728003910340307503014080403032120307506201201030202407042d40d813 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 480600539 1250 480599289 480599437
    0x20304030c0f0e04020d290f07030e0607120f05070e011205040b010302220515040e1b012006010e04060f050f0c03090a0803040b0a050714 61
    0x8005103000d412201c81040703501c01d54043c40241c1c1e0740e0b820819800b244550031102c250303d81c017803c080c0d41c0c41440c04500304002a02d05032031608110106651440005003c01c2c04c041c20701004051402000c1607407a04014641060004a07040d143d401d03002c6c0c042550b54116a80c98135040142c4960300c2403000c0200007003a22510502845091400d040c2c500c2290b011b030205442400410050500303040b014428030f51016042a0158840d1018055450556482d030902403070401d03a00107031406e03110301e86038008a0001070003600d501e4004040600811510716050100c078001c008012641f081c81d0b85c4420386070401b958615030712042c201621205c1545c0030b480083c07520007500d07450342c1d41d40f01e80740c00740e070201c881c6400f6030b41c460802c80c3c01640014a0b5003c0c41c000d1b90103141c0003c0c41540554050b610410841c2c03103d03d040ba50074022504000d02040070000c106c0b80e001c00403020041240c1101c20159100070030301291500044504007840544203030b4904140e66400e0610001e010b01405900301d0034 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 480601789 1250 480600539 480600563
    0x160210111c081303020607440a150e070207080f160b030705030a09021903050102091c0218091204151101061d1911040e01050d0c09020c010b0a0602030403 68
    0x207219080c1503c0403c000b00541c0c0068003041c07005000b0f8880d004040c40d0369810042800325040da82e00d81c045410940c0b0041c901440001c01e0318294584004d0388034504207010003000b0702e032104080b9425a01d02c10110f00043e59800b246a584c400d004800103011071a00f120084410a01d000d50340d0046c0000e1142e001c810114041101e03c01700003101d0084501c2d540390760071501d82404074001040424012a8400d524407a51006603004070810380c000d6009800068a4000360300c1404240f641991003440900178194a50b00181d40d040c0c1410341074419a4840c6070503580d0070900a1804081d1841002c0500b000310700003031240303442d2901d07100b045040c1d40c920108a184d4410a801d9852070300a240100004c0503070b4041200ca03020310103502040351000d2208008141040404503564410306441c1814006000d101d0007558094a90050000791060420400c40b0386881802811038014030030040d400140ba140c0c980000d4001d20000c401c000c040040e80c990b207007006562503005210854090340c0d009 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 480603039 1250 480601789 480601801
    0x1030b0c0304030806221b080a050405071203050702150910020601150c0201030204030b040c0e0c0405010c061d0f010618020304050c12100603060c090b160210111c08 73
    0x18003542c0c0a5a03168580c0220303600ca4030704000300d02c0c03554070410101100000c0c03c016941118000e81e08200d1001084284e039400c090740060031941e00800c8141202e0074042070100140001690b10210791000d8503914841c1c25600d02118640316102029501584071528108030740382660007401c05020031a0f4143d200c562440007643c91300024440c0d8809103400c0000ca200d19405101d074110072520514005141584070360301c5601a42c01981c05450f5200d280401744485e9003007403245604000101030142c28140343c080001d0040c2c43e80b0600400369903e622000c41441559420b60380e506124005560003840807d81d010b000b40024803600c2d149400041800141e0442403080740c1c000e0382c2120140c03100d0542c02c42072122800040c40c00350064800c0200d510328524280c4649409503124003c0411066091f540003010507184c2c2e0807030205694108055480c0116003d0021441130341600c001040da020000141d9600c3c80c9a040c2c40741d240030305100d043c603403407034081801c03524001c079150010321751030304 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 480604289 1250 480603039 480603061
    0x60206060f01080f0f06030a0c0906030c0f030c12150203150316050f061809070e0405060a0b1c06080d08090106080a0b0106080a1506020c010e01031b0c05010b1801030b 74
    0x948502244800920201700003c11200c2c1050380803101508072450280c031603441c107a4041300b40d400303100b480b40d85100c140100040c000d040d60051040c0003c24015a05544450109440503c6803001504640010b803040264044440034050031a0704211740b6464102c02d45042800040f030703840d00c203005004540356910700342445102520000b81c07a900410101c0720a001071903025500340407410f01500014180396480c0c4072032511640555603814000007070481031105656000c0c041d43e101d080d11900901880c1007140c03d452070b5102100540d0510002c0d80c1d00c1e0002046260410111801411801c00e2030faa00b022295010b0315280c1d000304245a0f580008903110f02500398000e00c2c4c3e107140001041090703c90307008a900440511000502011841d0060703441a010b0791000c40582c01c0320840c0d41c071541c1c0085003803030155401e003401d002804e00300c4440d04078161503110b04001d04c4442558038041c01400d41c000c00d00307104050000f14410b4241c80000c00e1916003407104440c0c0314410310000c2c0e015050 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 480605539 1250 480604289 480604291
    0x1314010b04080d0806040b0d080a02011a0d080a0c0501020a031d0105060918010b06041701150326070b04062c0c0d0f12051305041802061303050601060206060f0108 72
    0x1082e02403da41500c503003040703c0c0b042c80602072503445600d52042203682d42e03e502203441c801e442880c42941e911204a00a070a482c0a00f1180301051b050b00300340c0142e03844034010041c400c2e40c00b50700196a034941c2941038a89a0001d80f01400c2903101055011445030180c0c088500c84940f82c00300328800b03045611007400c0c0c80c4201c414640002d0900b0115015544d00880b1044c0e000c5400004501320880710f0105200382c0187d40701b0820300a00d0000083c0d03000c400c1c4508400e200c2c42c40412811507040d62210300070402c40d1050b10030a0036803151001e200e80c903420240c0b024690310224800250500c1e0030180d0282ca0006080700c545203402c05440301d14800010301900304081c00c001b078241400c100c0c00300407d5500e424000c0c1c0f2075940320b005050004400304100f01c20580a51201601d1321001280f400461000e500421300031450484c56120945080500c1c040c1c01c0c0d412109141d50300000090320342a41c400d544010050300ca154004160650040b441c0d03403090300291180e400560034140119440c4d00 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 480606789 1250 480605539 480605549
    0xf0504060e06031002130b0f1b06040c060f03150f0e070813060c1202070c1a090901140102010204050d03050c100b1c1e063306050702030c1314010b04 66
    0x1000d16116072034007240f81c028011b070140b40602c00d42071550390042c0281d25031100281ca040e043e400038a405036408184000a0904d500ea8000d01c168a050350b00c0981018041c00f80c00c050005092601281030b12039005a404e450b1403041e513800c0c455075828101c92104203801421801c0040c100014051b500c00c8134054480d01d42c185101d802081680c40300801042c1c215103001c10444050903080c00c0c0c0c4407600080100c41d01c83e0030134042c4a85041d0001107440c091003c1c801441004000c0300007556661407070307036041d24040c006a11401d4a0f450041c0d00a1045034441c0b50490304000380c0384e051580100c09408503070b03330200580f07105580340902e41d011102c00b0b148042d4440d0304980303100803841c040c04031540c2c168415440038280d548000520040013208a02c111a0103440e28104202c14194030710b20818010f0036210490b400910f5007418400e1f008a010352000c210300030502d0000c0d55001c00044407010009040c03003211074100307441e00c00a406403071511b40b59200020000590324050300100d5007152 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 480608039 1250 480606789 480606793
    0x51902030c03180112090812090d0c0204050612150108061003030507080703140301090608120c0303040b070212181f02070b090109030501020c010902030d05250f0b010f0504060e0603 80
    0x41006440c080840b41d03c401810444003030082940d50b8034603c81c3c84403d6010f040301544603103403418600b0034204003c000c0030581e0022a09503208607044109014995230464001ca0b056903000045a080003000e80000c02e184203c1c1d030280c1c903144140e075402d416240c032101910840c0d940e10114000c200001e1200500190741004600c000c41d4000e80500010b502c00d180c80003511941c0ca4504500707810030f170012212541d40e60020006101d007040040050003c21070380c1d178180084021900e4076400300800151004c8144400100c1261091200000c0840e8102c2003640f07610007000b40100220f801485240a0311340c1060b019400034001103085078401c03165005040c110f0802113000342d150420404181882072400c4080001a0b0030300241404e001c034080002049441130042614102401e408041403000c20407500034000000314031809520309108600034550110300c0c09002c0340030466000b90008820340d00109142103002e00003001c40d08200d40501002c1e81f500e031010220303001540c40641c15 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 480609289 1250 480608039 480608047
    0x1c0e0907180e09010e0a1b050d080d0b06040b0f070303110306090a0b061b0d0e09040b0708070509121b06130e060f130525050a0e0f10051902030c03 65
    0xb80c0300d2000019800020b4900120300f0706014606640343c0103110b0310494240c0c0149403060515100c0c81c001d80c0c002d100440300304111400607281c200d0b03140305409080d8402510b03440041484d48401e0201d42c001c000240d54507903111742e106180042c1e43c0002d60b08070006414600c1c01d004081e60ba8040da40500342c024940301c00303620307800701190081c0008400150411030034040b1742a800132480c80210440c0150014040e100c00e142802000c45003080070035840765088400b0b000100310720b1590b06500484505040703136162030b040320540309401144d0189500c03406c0624040841c00300031420b5001201e08003283d650030903103a010441207000360028200b1101140100b007001d80071803c10075800c24006000401c0c07180c02070001c504000702c901030094200c1e4940091000307035600342c840403041d000c40d44460000f01c1c441c007800400c180319105410040080445082c0300c19a12242c0032100c6440c014036400d0000440c402c0940a074010070100c0d01c0b214202030010520600100494410a032110061854 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 480610539 1250 480609289 480609299
    0x13090e0705041a01080901061a04080607020304061b021305010b09130c0c06112a0c0103020f03070f0e0616060e0610031b080601171c0906030207051c0e090718 70
    0x210107802041078001e523481e40d800107101240c652000150030040440c1070398982c140f185c41d61501c0400b03001c031021940f0401007001210750040781c07400038569021b401001082180001808081c015006001541c9001c00008240c0050310003070030403441c1030744c402c0d0400c04454181c2c01101c00100150000c41c48940b01c407400a00d040c0c0c070040e801e0b55810b914900b4240d40c001c5403001d041a0242c581c008001900e21200d201100300901d0302c1c106024607081d0301d0302c03813240e10244480c0800b910304020721103003d800444081c000c00200030170801c05000c182d143c41c0c02d040800c1a5a44404080c0e0310540760035000020000041502481080003031400010300d403460f034908440307980c80803078028015440e00010413400814020325008092046c030061042110751001424145c1e101040800d151790030440c0d07851190450950f1040b24014100161100028240036050102d820903100c110040c0c080c03580603032074000750310600510b0240c036282000c2c0d48100094414140580910404440103d41085 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 480611789 1250 480610539 480610547
    0x504110c0c040b061c2307081006050714031b0105010f050111070308030403020a05060708010f05120606010e130e06333c0405090111030a0b01030213090e0705041a01 73
    0x903084c6820f2000051b07030038145480f12040030f0400140402102c0075800d2008480d4480b00568001110400080803145054400f40c018860490014074241012412445120080c002d4032103080c04111000700b034050009100c1c0c0202424094404190040d00e0080340c90351241c02210000a880c00080904504549880326241c2004204404500c15010200006401840007074002d062a807104600355042c443c9404031401c03650030650040c109151101c00c50480050003075007018007030900090a00805010910241200c403d483c00c85050070380d03410181c18000b90141c070403118101040203510341c921341000751461190860f0a502a02c580c071501510f40b480c0009100d218048040c8400b80f445000300782c0c0701108058480300d140c105c0d0584d184506240c0580303a40308007068001c016803070301c90740201410f000107401c000c20aa80c840d004891039020350304440003108000141c1c010190348200700c4000e40701034030304c0405034000c80e0300c0041d660419000d800d402c115490050354200c80c00000450b = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 480613039 1250 480611789 480611827
    0xb01050403140a0c08010f0b0603060f0f062b0b0a030c0b0f090a15030c020601050a030b09030f0c07091b080f060406050a06020f060105030601080a020108100504110c0c040b06 77
    0xb400501440b1044400101c1c04424030000380260760000c690610448200c8040f1941d0000140c0208001c004200003561401c0200c4180401201c46265881540c1c000c039906000d40c0419403000c021401c0c7c800750004902d03000d0001c09a24080900c03004914106102406201b4880284040c2642c0814417080101e0f9002c0d0140944000b80c081c00d2130141f100154440c4840d900140700c0c0c0c00d080700d1145c00c09a060243d0545500540024003565242c00049403108005100181c00003000c10301007034081400384210f0318204100501e16031a80346d00208030b5200c1c030301031190541ea0751601c841038107004140c3e4900c868124541d1100100f668900b230004000c01d000030040340c3e02694440c004141999180e4201c005000c8642c02811b8007400100c03803038a81901a0015442a404403004001400000818514140d420718101c0340644501d036642454038001d030440e560040c2400079004601c000b0b07401414034140207008540040c00d07a0420b101c11510600e4000750804420003a068003030b100d41d1109 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 480614289 1250 480613039 480613073
    0x61407120b0d032a050a03050406020c0a0308030c070303020d05010806060123030f040204020c070b0a09080c09150303040906241718030d091b0e010b0703120905030a020f100b01050403 81
    0x104112000b980c0d034486c18100141400c07000300b00003090030b02030907a0420150840c0b07202554078800290650700e552040c1e00000303080840615000500030b080610a405982458512440030711076540c4600e0405d40340d00b0304840c0c40303000488801d001c580100011030080c002d05044d009d03003442c60300c6201108008aa0040090b80c00039020007111001c404204070100c01004809269900c880c154440100903012990202c0410b030b000420361022503a808555070f42014a43e103800004030b0100020078154040e40e0705c682178840c680500002da080c02444040ca03101c07025103c00102c41c10108040e2414421042d213010102071210024044e02e030b0030300000e40e0300ea250504403820f02c0c0b0407180000507030320b0040c0e0072540ca80300105404030501240044c50080c0c010495442815030500e202c50b8014003880c6000f44c200b2a02e2014072032100c402e60702c8006131603045010760390b803110310040107503444001940700a80c03849401000401c040c0144074000d00414140e5440d481d017851510780da9602c00c090500 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 480615539 1250 480614289 480614357
    0x1020f0a120c11180f0907080705090a09020604060305042918010609020d02040f060305040302101e090f0210030e0a0f06020903033001060813061407120b0d03 70
    0x50301401d81c2d1202254199441300c0d4100343c0076880d11195684102e030001d008510503a1203228240030088001c1910300598600f0b40380380c942951041c48080181501003c0070350010070004000c1552941a040716224501408151941011441009640811400341e804542c2d0307081021074450009090240079503066140041052612030000404a07441a20000c640d00d500140030400072a03840d00c000020803041c2003c000c82d281a440107900c60040c6810200e03c682d40f070030304850742d44104c001e0100080f20144100401e141621b00303014003421101041e07101300041c00702800940e1090050b0106402804068009a01e9559840c680340a0803802102d440740c01f0f003c1c01380ea5440c20001b030812596190307051203010b41301440c00540108401d000880552590005110650300f000d040d5030070900c01c590807400c92245082141c01071950070980188400300344180440780b903000038907101043d10a0800c100600500d010401054144080200410381800e94054031421000e17140c810071081d040 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 480616789 1250 480615539 480615563
    0x7021507030914161e080a0b06040e0a0503040b070f062d0b011e050d0f0b0a0506040e060d0f050f0a1e0c03061109120601030201020f0a120c 62
    0x511209600110303003250000369114618003d0064150500300c0c00c84401001d4440c1c1e90404002c40c103180d08070f00820160f00e00764421009000c8041c610140103188103420754901711041d03d40390380124805d035240c42c401d0741001d003104100170021500c050b805500800a40c6003920b4101c0700c1d4100c0d0007210090320348492090008001c14003a00403c00c82a44242194142c403410205450051020148120070140b81a0bc48886079800c5042c0d070249230f400380381ea0150311050010450b040c2c414001090b007103500340084980404003580281c07041d44401c031080c2540d141c03200c0c18061180100d115001c0040d2000d0301003601c0b402c001e003040c1401400b0b0741105540d9841602c81c1d518207050002111119400303810900b060003c00c0700c0104034294003800d0030403107407160b80b10f0503c00c00309400301a108076900d03810440340092240880c1c404807405001c542000b981968007a4481030240b0041c0d000d03001c3c04100c5800c00501140c0740401a0340000440c2c0c00c0310800d4021500319160f10706c12940124403003 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 480618039 1250 480616789 480616813
    0xf0501141b09102a0609020102010513030c080702040204180608070602010e280b040b04030207120305030604051008011e05062b030905090a0207030f02030405060a080a0f0c090e070513030b0702 85
    0x131404400d07080c001e207004507054006100080c21a140185011040c55501d155040020b03404101c011216803c01b001c42c3e19400107000142c000d1055501040360a41c414203204000081a00000200c071506419955403580c0c1f510103a080e250700c0303151441613802031401c41740c6600100205190000305516110345400640d0ba940c14100000d607000e0325900c98502c100802c050781009410301502440070003030000d5a003660050802d0201074001c61041da15030001458107283c50440314005d184000081c40082c440c0d1080c00c10301503441d00f030903007040c0c20000000d0003800c2085116010303014a1010352004440d6200406500b088620110200606100300144a94400a160340210010440141e450307a2a01d0302030210010281d000040d0340050000700442c1e5107120603640030701c0603418011080d640350079081c0000c0440c5003c2e1081c5c0e501d0106111780a80c5d00000c0304050700ca02e51005412515808000c0c1c5803406421160300c009940b0a0081c0000740600d124990020828011510840c1400b = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 480619289 1250 480618039 480618107
    0x319060803070c0f0b0406030b030a0b0c07030206150603060d050102040902031905060334030c0609080d02011e0f1e1a04051905040f0501141b0910 65
    0x15038809109035002103a40014051145208002402c5821001d00094078103200340020b07000324031420003810b981341b0034000c01ea02c040c4200c0600960081e91860075240207000f842c0c264000c03410550040c851000010104011600c103100d034400002c1c20070f0b00350395030341040100302c01c0581c034111a555002d00c00011003124900103140910391082004c1e18150504c0044021240003c0c04a803080d17018000011508a9280c0040c049008644403048242c0411510100c420156480240b00e01c00d1640000340c0c00d54000040780503541043d0a0b1210035102d540100d09a8040360b40d00701000f00e00f1004800443c500e6808216100065900810280080f0041d0340b40e48807402e06940e042ca407100d510740b84103140c1c030006202561048904010508025000511602010500c0c003182a81ca802003414042500b981812966000009100580118241c0020740c0030507140d03105031001010340840454500303801d07258000b40c06000f9140608042c0012520300030580c122940c0006544c908088101d03070 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 480620539 1250 480619289 480619301
    0xb0f09030c060702011a01080411040506030a02060c0a02031c0203030a0911060d060302030f0a0c0e0601030219091a03010312030c050409060305330a091a04050a05060127020319 78
    0xf243c0002a103030f40b02292030481d080040140303d04004010040100203a1181d801004000301030b180000c0b103a88520110349007441094011f0340c403c0002c2424640c08400007002d2840303e209070255140c01b2281d0740d41068140382030450f1400f5810520004041036069030100300d4007030040301d0b003640003c10400411015409854100c00c480c1e2034900030700c19030a04001004480b00c032240100000d0b8400c0c1c071040300c5000140a500c2e45c00000402103500c50788a50151032008001d0215490380359668a0301400782d116500c51a110512866056040007040b5000c0d40c0c1203d4118458184000c0c05860450003051000145001d2040c103000118405503144500d20246100d000200700d04100d400490a503455245c102da2845401421203c1154010b0700c0e15641211040700e0115060740d051610028030101010182e4000c1e1040c0d04000501100240b0405814020f0059604c0c3d07980702e203050703910042060101d001c071a9080c1e40c000c3c503400856000b503070300136040207040740d480e60501c0300c80060762030b = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 480621789 1250 480620539 480620551
    0x3170106050a08180705014401080c060f2b09030e030a020114071109040f030e030c010509012a060b100c0506070e122a0604030b0f09030c06 62
    0x14010402c4040b40303412030075450b080221803a000c80d4982103031140759070b594124011281004200004840070400d0b10010301881702c000030041e90001e034a41500c480542082c0031403101c6400501c000580d444010940d100c0d0303a240540b096183c02101e890b08581a80016010a88051001c0c0c5891303407074440f41043e10061002d810302292480c8103003801402d100d02c084d0310a00c607400c81080040180e070010040c0483d01c0d104c0c02120b40703030210340c01c1003104c0034401036049070030600391002c00080001c8545c801181611a07100c022100d14000185540c4c3c2e404110303800e01141e01003080801542c01b840d1070104a031074081035182d40c40683e00c818440342d03203031200c12100180c9503d8801401d01e0410356181600078503103816a81090306440365a90b800000d032008081c880080f030601d00075142c0100c0a040c00a40380115805001e5a48449540c03140d5865586a2410404006582850104c080354100c9030880401e4009494030640480881d0014140c11a01c0c4010030079138032014018080c05103d04 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 480623039 1250 480621789 480621797
    0x709020315090403051809010b0901030e031e0a0305223201020405010305090a0b0406150909120e0103111b150a0b01090f06120c0302093f03040b030403170106 70
    0x404441300a8070401806e0324514400c00203400184105140b03e007d854011509203800305a41c80c40c1c4200505601c9006c81d07006035400161080c003d0096684010320b00d000081c2d60401c0950307a03444e048200c60345034422401c420b940e4600d140000ca0081c0b68104d03101c0740e540c91320740301e400c80070481c0b07000d102e44030b11300701030941d4010408200e00e40c2c16100d41988101604094030f203400340c2d43c0e034251840da40140000c00789076480c4409240d10500c1c650a0300030342090203003040101513031b0408000c100d103401c07044000560140451050f5501c24002c2c418040c800942040c01c00380610303001003180a121070090f02e144101101c0c280300c1d40301c01610500803640403400181e0820401c000519071002038111070710107407201d0810086641e000280c0098250449800100540d844504130040c0c81401c841c1c1c0d50041e8407041071301c4069104800c0c143c9a04d5440ca08407012110410044158003540e40c1045040c2c2040c40f0070491500301000640c0e201d4803031f02c2c100070301e0002ca01070140079400031703040380c4009 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 480624289 1250 480623039 480623047
    0x1d0709090b0109050702061303030b10020102070b0604021312020402070b01031401050105060918060307051906021014042405160f0e100c020301020d110309160503070902031509040305 81
    0x444070904419015042155081c0710f245400e5101a41c3e59501074a01c46800021070300c0700c2c040c903120317030702c0340070310003030003811220300e519100c0c0020301079041404244c3e0a0400080403c20780c3ca885e10845042603242000b0150385440c050403402694894402a0f0b001a000c00c24000042c40b02e907038240c040d501c40c022700c40d580304110348401d0071180140c1155021740c80c1000b8900003030341c1d0494441c1c3d82000969140b030155a820000c6420031910381c0c032160700030024401c4204002280b490440698015034225040b002e446c2c08081c0964404030286a00e03084030102290102e01c15440820071390035055052200044101c590404580303040701d5000d03a0350518a41ea1070410ba002c400c1d1800c3c01040d140c4800b0030001880000d248040c002024000c0c0641d007600310301191000e405880c806d8800071010450f00100300c4d05182c80c0e5000301d8150f641400344e807803802c26034000145a40e0644170003a0007005403a0a05403400300a60010f040b5407e030903081100d980c0a81c0d1020b107401c0c800c5120b40e8460340c032 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 480625539 1250 480624289 480624293
    0xf0203251214030a0c050705150a110301051e1903030807080c0304020307261905150f0106120e061e28020d1d030712211d070909 57
    0x3060300e00d640900308001c032058510000c2d882080a403504004841c0d40005c0050220034292000e1041440082c05402581c183d51002940845a0f920030424404140581c650188241071644000d0203150303800400020000c450700354011040c0400e81c4054501072a000c4900c84051001c011a4000c8000031034410412203a039500181043d000324521a0181c01c50420341c1c0000d45900c2a8021250000c0076040010441d4003c5498500c507907240d0425903d400210710400d2200501c600c9044e5410300c200c001d05500f40b4488603245202d1641660101b24903402d100c000c0700d000c6298a114a83c45803100202c00c000c1c0390034804180107200403d04c45100c2c1030401c840181d0041b00900308010b00c04070b001203032001c402c041414020041c189034016a01d0604c5082c403001491b074840c4642d0304050700911064503440c0000200f141b41c0c00b500c451240c0c0380d100c550868600c2005030150511390007001c00b0f0b95003580315400504e218040b0700f080380020358080e200146080925480808010b85a07141d40c01 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 480626789 1250 480625539 480625553
    0xc0803090f06240d110d05030f0c0312060303070308010e0c040f0e06030708030a0c0308040218310c121a070203130503121c0207061b020d09060f0f020325 68
    0x10302c030030584400c524098541c0b204040e80b20307500a106c0c018052084000d04100c400e200701d4040782c018410064681141307550322542da410240e8180790703070500d901c0420748604d4000140c90050fa89a642c02703205138244403102800b070802400101e5021002c0c04042a202040041c0d08042c050f00c01b100702162030524209031a10074542c3c04407440d41c00030410038000340e50028500780301e07039018102680180c841d4404620843c04008542140c2d0080b8020721401900c00b40705101c0c1c1000c00030a8a80020011011a946102010009002c03042d854410408400300720101082c4501030b090003102aa040b040320f001c0d481d01261035000680000a03240c0d000b9031011120000f078101600100302c14111218880214030070180c40242d0301118250325981c00040f03804603201d40d1b5001f24280070003045500a0b03000b154440e040040903000b02c145102c1030600c5090010f040761003030b0342c442072003189441c4140c5401522017285021400704000030b000c40e080c00340c060301103002401c18400480f685414040 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 480628039 1250 480626789 480626851
    0x1502071209030507210501020a030e160b09120f0d03061503060e0f060303040b07150e060709061d0a08060109060e28060e071205160c0803090f06 64
    0x44103124105000b07101003800002d116007951303030344006a040c0c04071040103c0b0390454600401444c1e503000040c0700e0410342d41070700b000689204d03000071120001c100007035480e1030131040d011b4041c00503420f201075811403404500400d070008107030007030360241c11008203072034100722019407800301103511550100040c4a03200d070304280d61030161900300300341414030b0814500920050a44050459084041030490760140110340c0182032045000340c1e504c44900c1c0c5161031400498a00b60340c20310f003031a120343e8020041030103840b8100503500c0c00c2d000da04048040e5141c45914400b40e14959404030790401944503ea80304020f000740c0710050a2641c901144030f41680c0468200340c128801c00814000b444850203040540700b0003440b13080710301e030b1010b50540004100c25441105400c006c00e06100c201c42d0042d0002640d81c3c44544140180d0769100381d44078144034040184030005807440200404507078081c01a50700402e032101a12440b0100145051425200f0754600035005d4156655604010010000c1 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 480629289 1250 480628039 480628073
    0x1921090203060916090903050f0a1805061903050c0d06170f0106080604030c210f0914010c1e080301030819030b0f0919110c0709060b0714010207150207 67
    0x1445003503000040c00c5001d0b040c601c184e040903034407261101c01f0140120181da04001300206044c0c0c540c4c501140040050404050500c8084480b00000c61710782010303411140d000300441c4101212205490303080b030042c00300911404c0102d8040c080d8250880060040304000e004e202c851008500c0d03100c2841d400d055503038101602c0c5030724044040054110114400340d00582604110001110700e060816071702000452240741c4220748500003488503008209404c40c091180e84d4959107944400f1000180d10300d8a06040c0408c0c032050142d40015480f00038040c031450b120b69480200401b5079240c1c0380a40080e0401c0364515030125400481144c1010550001c9809280c01d00404050340003040c440301e43c401030240079504001c00240d0120317200610810740d190900003001511120780c2c0015168228049100301401419070009165005003d1407083d20105116070b07291000303594512222071010110105295000c0c40000003040f002d1094551115104401603031314869490041a04840c18504c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 480630539 1250 480629289 480629293
    0x10b040204080d0c1b0914070c0b2a030a02030f0f01050901030305310602010608061005041d01141801090b0c03090a08030103061d030403030519210902030609 70
    0x2080128801c0010100c2143d4514208864500d2441c100746402410107080002112480240010180c409500a43d0301000c118000380c120741302e08104461000780d880010704881c1d032007400700b10f010f007102c2c04010354100218031003928500c041914085d203400c200c40c400300181c3d0100c10026041c11020505a108400203010b20140d810003000a90b0600f040c00080c040081c04138000150495410071140c804100d00c6040c50040310b0069581c0c2d814266026040055003060303800142d00c940010014000e5400090040000d030400060100624644a064581c880c4241c08948a00c1080c813070590084842016881249000d49201000854042d02e841d03080e807400d1300150204615201c03164112903c0c02d0981c6d80c075126040c6003460320f110110040d01c2400000000400c01260b540b00302c0c0000a44040c90008015036201c084e201c1c0620710020f00172540810124030b0068401d00c4032116462203003000341c039030702c004001e0780c81442d1074180140040e940c64805205510782041001d0307004404d000 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 480631789 1250 480630539 480630547
    0xc13080a0c300c0f210b0a0204090e01050105010318021e031c09140a0e0a0509010e0f010e010606111009330501050603100e040206040e070f030c080402220905030a11010b0402 77
    0x810014003400d105c0001d0001c41c0104040303001d0b120550104c1d0010441d07680140201c803500d0790024028202031159a021901d040209910100c00340c881e051907030307002080051461009400c0c0780e001104e0100d041c0e030500462174400c48100109291504210080e59268885418102140c04074247c0e549031510458540000b0480d001200381c0b41580455112030116507500d94440450150400905032080d80c025501c1003005c041b0154845124180c0d404003e0114556520303058890b80140c081104186e0082c02c01500c030390314a87c1141c01001d02c03450024003841c5125050704a99080d100c001000200140c0080051f6841401010b001d013200304d540d50300c6c42c11304224400941c4803e201d002d40b1090050005000e5540d40411354004100c000c0d10b15000b8a803451000b06401075440c0030f00c001c01c1c0b515113010800c9210390b5080d171259a0107003042d6001e01d1740011b4254502144414650070300e442d50740c5200000c40a00144c01c00814070b840c3c40c1401e9106a64050070341e08422040e9014610601c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 480633039 1250 480631789 480631829
    0x21206040c1e170f06070c02090105040b030319110d05070614090304051908030301090213120221010b1f021504051b01050d050c13080a0c300c0f 64
    0x5000c402c1100e600140054082d66880354403418410b07240700b0b00ca01070050104101710035402c030a1100d412442100d86038003076a2034104202c03c0312483e402094269000740301c4440300c0904110b42c00c00450081c01c0c4a00300412010b40b0500d00074030940a00002a00442ca5030100300060080c40414188040d41c40300038a4030f401d04a03902d0265103c4c070b0303208000300c030800d211174445c810600024080c0201565501d68450302040040d5100300c2461001100350000020b81c510051103400416500070403402950070004c000084248022504102035513950010400c0c582d6400034104407480b003140c1010117030100040180c00c010903401805147c40e003203420000028000f107950020500300d48148440c0580000040f0740d903000710280300c00c5042c0b07040181b01c1d94800c508081d0540b0503c0400c019a506e440c0c025035a102c048100c0020284407003801c0034031440143c09019066400040c1c95070305041c520140e007012100c0e07801401d5503001690700c1c0030300043e0821007490700680881802c02c007203d0908 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 480634289 1250 480633039 480633089
    0x3020c0604030e12060f0103110a2102060f070f0605071b08030a0b0604030302010204031b0b1204140111040f080708060c16060c02010209090703150902090409021206040c 75
    0x10300050030812968801c0d000b50713035804c000007403a21080040381c03154640342c2400360407100c0a000584503414660740d240c2582ca4601c3c4020240c4141043c141041038402a22000040c00c041c02280d00100c207004442c2c9604040780030f00300c181d000306071285408682e030070000100e4a02170515410080400c40240700040306d107a1b2a088141c0c415040c680d01d0340c0b40b03800000103040800075203a00140000700041810b50540180003540e0094000c2e809005000c0141c070901d400c04c0c8200200400d06001b41184100720070203040d4464040c0005000c441752541c0004d007140c61614102c7c01840c0007007014003482c40701040d48070280800e000184542030401d524190345801c010b0407110b0030100002d4410b984021103540950301a807002c0c06002d81004060f0180c044e4001c5c0c0001c60250704d400c8002841c080c860300462020141c0010303902d55403800c0103180d002031750260951641054641c00c000005880d800f525580090b44800a81071074103213450f012041034010f601c6900c848045c050502c644841c0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 480635539 1250 480634289 480634291
    0x26060609010503130209011e0602060610180b042304050c16060e0d05120a1505100c08121008030309060f07120f020c0f0102211b03070c1203020c06 65
    0x100742440703500c0b036130340034440c00c4001d0001ea00213402c80c1c094800000c162142210310707417012140342d8210411315281c0c00101d03507400046803059407200d1421a01518907014410040c0c041d880c58240c4c118568580e556403416502a9005000c10103841303204a204407031300c0c9221459424112402d021a04025103c03602500038840818403540800042104025103540708141c10301b41c000a0300c594030500100a89140c024404180001500c103002030840e40051045503003140720559100c00c0b190030a0705000040520001c06001c1c00071296682002c10100006401d0300700448001c9e056a1408082c020307904081a441901d403680b0038000c0c04070400001c1440381d0b2010040c0c8034400d05650388881120000500c2c00c68880740b07407509400301c2d00010590000d10404290340125121140043c5a4038201d205101900545000c043c6000343c0f001080c0c44003036004074501002070707410b55449160000031b6106481c103402180005400404200c0e400310200a0b030310350360800b141450516441e050315094 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 480636789 1250 480635539 480635557
    0x24040e060f0915090a0b0702010b030a0305030a290a0515030606090a0312020105060a0f0303020a1506030812090d08010b1b0f010e0109170a09091e050403260606 71
    0x4040005841c501c08100541c20340310f1450940c8480d041c501c1d00f040d10f415944006032040e00a41c000039240d43d005002e04528610040d0040c500c006960b1000c903201d41020b881030305015110800340500c401c402505940c031183c0c00700d941d10030300400030070019007510a9206174003840c6625004210b00c07001c101503940c4158183c5410395070b0700080000941402464000801855000500200195055000f18031840c42900c0c54a00700d5169615044045054400140140d1100b954440019058444140341e1015508040b811a44907542d080c090b4000c2103003424a42c07003080811008080030800615041c0d140d05022290f5410506803116030310405c000c540ba8244481200580341e0800c02c0403610444d83d40c00200246000401840d0280048a00680712000c800700880c2c5c00c4212081290300f800201c3e183c0341007542c9452000d5000d4150021500700513880300300c030503120140c54021350b4411840b90f6070703d414400d03c01201c800c40c1907683c108894118414800c00c452611064110b1301440 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 480638039 1250 480636789 480636811
    0x1e010b0105030403030f022104060e19060902120a031206060c0305040302040903020c19050109140a050d0f0c0b0307021b0a090213080a0c03050f010212040209060d05010524040e06 79
    0x10f000c02030180a2301c81c1c41090704c140502c40c41070120b6003020a100a00a0380300c1e04040c892900e850900e41c0c1d6451000c0a423103070f1000c518501c04001103059121100d907520140c1000c030103400c4843d543d0304000c0f203440c096010400382c1c90b9a065500062040c14003800c40c5041020011080361802402c034090390100901a0383c0e0b60502005141c0200803503011060020700d5412161060002c04800a8480c4201c9001c2502d2a501041c0300d40800c3c2d00510706200030b003100c8141840e000c104007200d07170400b009594400380481e101e8041900c1500d07510113040135036049a52400c21040013868001010b51401481900c40c1d5903a0050b5104403030740e8111000c402001d6141c0340380381e0348083d0a0099600c1043d50344074006a103010040c20a61305022a0701500c2607912011010120600380d01c9a140c11040c4606008009001850070158103074000130040c20144005569585d03e41c210366081d96035a0303078280041480201c400392104010004441035600b03010342c5200d0715800b59900c002900d048440 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 480639289 1250 480638039 480638051
    0xc090504140712320a081306081509130803070f1b120f0302210f060a030f1e0203030c0717070e160e0306040f1a0603030d090516081e010b010503040303 67
    0x43c4d5920030100034440b20141950858941ca24014109510542c1c4800120112020010314103000e80000c0d40314007070b50a0300c4c8004900060800011050080c100c410f4803106450490210751084081d520500c45a2900c01000300c8481003d02000450706c0e00f11012404010782500080100c0e12003194203805040503050240500d0040e0b000e4052501005550a4800b044500c81d04d200c00b440d5001d2007e8256601098540d0000c0c8003002e42c1070b0001402c81c1c0d0903902c081000625a0741c900300060320f040480003e600311035000034103560081e0a0303d4896404040c3c280403800c40300c0c61400152108a00a0642c180340c900540c7c599100200010521030000c0004582d040c011840603440201c004c055481615103440c100340013185046058912111209240200c8288540524024a4020b000714107000740d40e00d05201905040e5801c465501660180d8000c40c07000c0500302c40a0700a0700003400951403007464035240301e0724040c02411644e0504080c024281d030410102d0340c020350540303404500c03 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 480640539 1250 480639289 480639353
    0x10509071b032001021c1b0c060209061b010c110d140d09030504080609071d18070603060311040203100b030a14101508010807050d0c090504140712 65
    0x40004209030210030480e5946414102c0f51040d4002c0084020b0710070514800f00134101c00c80300b21031000c422034100e00600d454552015004200d0800003507c1141c02601d03212042010800c15081111405140031400070302600140c001c2c090400c1c90416898056840700c0c02070303112a9030300c0700701443c0c0051140c298050200c4480c484212120f034000000c1c180300c4071f00706160040281d070052082d00118010800465401000841e08038100c5255000d074400080060029001c0d40401501c3da10880d0800050190b80c0007040c0a02d00c014000d40d100040c9e42485c5042c0745445860b680b00b1580305510400803c55012603400d003180c00c4d03817000d01e085500d81ea0350044550040458046403e0104400740030404164403005010041d1490100c103a0101d1070780304400e03a4021403c0c001ca9030980c1108a091006050612951b81c440f805241c04d07081c041d640d044140100c403c00c0d01d0590782600031105011101c00f04114a41c020300304400450310f0b195103a160121921000d9240000c4840703481c07040a2 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 480641789 1250 480640539 480640547
    0x90b190b100c030f0504120308070302160b0a0c0509060313050f060103060b0f030105040c090c051b0303100f031101050304020f03010c110f070608041719090e010509071b03 76
    0x1100d460081e051100c50640c01070040c10300aa4000e0440c0016640707000c80d505544500162412140003806540094005075400d0f101d248000300040308055007400b0030f6551070300215081c0380c400d0017480200d41c541450b054001c10f803031074081a0000d11908010403100b6458480440307074071070800340d0710b040c0480340341c50141d0900d0041251019544504400401400407941c094100750404a8000c80c52051840030301d030aa800454000c0c204010024040190313021303582081b01c005585e8036000749440c2c0601400300b42001401c0060350315503c04810002d070180c410f240c18000e03040c80c0070070101c86c0f031842c0d660380c032030b0060107903954108100400424110344554502d540c142c00010020300460b2443c00c401030517100e00243c0d1807120b00c0340c009082c001103800f00d906425101950390f03078801c694490303c4280300c1e03002d11018008030b800c041000252480b50460310f0003201c2d50541d503120b9803615209000540b028180c02c07240c41505c0820510a0003034003e2807002e00e078540801d400300d0842d0107003801c0d1 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 480643039 1250 480641789 480641801
    0x50904030207180209041407050702151b0304051e061603030f09030e030c0109080a080f07081c0e01110d09150c03020a120b0604031b080d05040302010e04090b19 71
    0xf6503030425802c030564161000c0c0c014054007402600c0c1042618a03581803d0400c040903204030020034010801d0b0b101504084080403040d001c0041c600b803800c0c6035401c840441408480074282c0ca03400202d010b2200346045d031441c945440300220039002c11b80240d40003c0d03551240d00112084061b01d21201000c050090704400715102e80039004128110246c11f001e40001855042c1c2442030045004400c4d856001d003036640281ca403c1c000510710100c06c0e6807503d910303034400005405640024810000000d031324400806030300380c0031440d11000422095520060714501d0808010391390602c4c2282e6054403040c0261400307130900b8180030074591001e00300344043e1070005001c49070490030b16188c2400c40390560010803c113400360366884d803000042c4500004440b210801c0c0c0c3d03880131042000300046010741000c00e001d070480d0503240320350720740e240310161500c41d2000c50203000c9540400c041041d580c021400041c00842030301c09001c10f844d20343e038140300303000018a89045140f4103c4003641440342c03507102e1 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 480644289 1250 480643039 480643049
    0x5090616110a050106090606080a090b0a09050a0609050a14030a050a080a1503050106170106050d080309030d15150e090105040f0603080d02040305010c09080c060a030b030307060f0f15050904030207 87
    0x200130103506d80a600c03001e00850f006100c081129000031820381c029030b11034015500d0300b2811178821a100c0ea040100504861b9200307848520038419084040385041c881d54410a00ca00d00a00c6c145c01b413442d1000c0e1241d0450013240b88d0b0b42050110381c044503000341c00c03204640200c1c6801c01d0541d85000e00c890090149a0302a14034002180022081150562012043c0c0f032240004210307090369150460308be103c0398000c1c250041c4503803c6410019200304051500107820405503070601c00b00080e4241141e0000f0a9008649400f0360100100e894003990f40000362800c0c503044a001c030340380740070840c0450f040c801d007405140d907220320b003038900100d41c41a07004d1980003040944d218000c0304990042c2d0443e000030b9840c0d510340303502101428022554281114080e401400c900041c003400c1014a0708800807010034107460742c9101c50300b95030a000528602d48a4540000c210b21070340c191038100d41c4180c03050090301e4602103906400d0050034107424201c903011150242d90b03503641c0c54103c0c14246141d03c0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 480645539 1250 480644289 480644291
    0x4090c080f0106060e040e030f0a0c020d050a020f0609280b0c0f1002030402090f0c07080a03020703120501050109050405090c03070303021e07120f23070905090616110a0501 76
    0x2210080401c1900110110707a0a035440040b507421403800c001c02c43d4400d000c140b0b51030380b00b001410101100b46020380707854001400c00244070086900454a130120021303003290207810081d00030b011072a100072010109101681d4045c20040010003241241004010000c040b0035081030f5117141002c11444003001d0714000c4180c980b5010503d4645641c3c01581c400811640690300f00e07890420b8040c03003928410b980050450080361103540080b00550409402a0380400c01003086001103440040103004814843d5001603a030451824000c05c0008000310803140c05040000420407680e0180e44042515000c0f500002c403626200d501c0c03880d10603200c1748941c2600845600000f8990040f601c0c0050380c490389002c80b0300b8008004801d44130f444500694a6171400050b444001c148000c0740891014030039400c04111011000c00f0f049413017103a442444807035010080501400704640101900100c90f9001000b80d030506120182071030000b650140c042007010004100120780400c60704054940202c0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 480646789 1250 480645539 480645553
    0x304020904210f2007050904030908010218090609190b01051603213b011a040b04060b030a020c250f0b0703020a031b14060403170405070504090c08 65
    0x1000383c40400152005004140400c10015132003c000554210f410085400b0b0500213062400700400104080d1003a020030581050210300c524007440106292080c010440b450494003100b00500f5030303002003400d80159103d1090040c00d04111002c2003604030403507400f02e64603c807000101c40074040d1b031050000c10055581c02505040c0c0004039062031107450703407124801140300d0f2000825106003504400000000c00a40b0304204c502c61000d0407542080c036565000c202c1c84514071401e6510020031034480460b5103c1d150030600d024465060301e00403c2e1000d0008a10300f40810b403841c0002031a00321100d40000d000180c002d001d0000c6c2c14602c4000c0b4601030b2442e8560020b40e40c41c0224059030b10140d264500c0811242d054100b980c2d42581d066004000030812a80c1c1210980c1c1500c01055011629504000c00109440c41400721a844c450017400e20349000d0500518401c01d40101074004071555007800003042c00402d80e41c003a40c1080d1030114094115190028030300015500c00d007a00e002d159 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 480648039 1250 480646789 480646853
    0xa060c140f0c240103080702060c01020a080105040e070b04052701150f141b0c0406031a100620150702010203160e030a0b0907050303070f05060c040b0304020904 71
    0x14010345202c1031403074100c41c00c1c4066500b06075a80542441d40510b81140c260042000410321001017a0603840039200904010b04102094260b8100081100106030500014000e50825200700b107d0801248001c00310180b4081c0d009486102d075014042c0a00402da04a03030240b41c50b884002000381b407465040c40e1540c0e4405a1410034002110000c00003401c14052000c40761051110911b0303c14100344092801042089940110144c050044024007800f81d010b16280da8178401c0f0701c0150700441030f58402050908824800440042990604000341402842000d5020742c00a5400300300d0ba00440c0008a80c401c00742c80c004590b044248440043d00c104001240d064000e5070041c621550f699000f81e2078414203403001c14201003055010780c02001c521000c41c1c0b43e4103125801118803020b4500650b00c0da008039007140d102c0d44040e10450f05c61842c21007005420840b8541c04940e0b490a142080c0c03c006104080d444040d0002e8414600100800c00744824109200400b4011b12554000c3c3c030850 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 480649289 1250 480648039 480648067
    0x601081b0d0b0414190b060f0301140d0b090d081e0103030507150507030b10080108100b040b1f0813020a060503070e0a140310090515090312071206050f030a060c14 72
    0x54000c181c800c1b401d003030300ca210600b81032040d108007080c411101c500350380c248085402862225078985a0001c0514050404a4450700d00700b40030714409005030501d08603070300b4040c0c90182c0c00380100c000300704501100c0b10030403100ca082d1415254189804c942d6181c141c00d15094800855502540b04c926000c00d201c101500f5501c5502011015075042210041c4144160368498091150702466001050300801116031640300f003400280c0140b00080c2c0c010b501d400309140694074000001803070303d41000b441046c0d40042d4442d0303003e41c00c0d0680f019081b0b590f9003c10001162845501c00303001c03000c804141c01c1ca001d020300d04d00301a405403600c0320869680b104941e15035210103015000c1d01038000340c03000a00e2140034803107050750003c004180104c0c0c180015807001f000281002004d0100f0b0191003640c40c0000c6001d801480036650304025402640708140c111119a80080d204003100014500e10b92008114240d045da0011000100186400710a440d000405040c280510000240c1c0704010750344 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 480650539 1250 480649289 480649321
    0x736060905060a050105030402131104030b010b220f063b0112060b03130c1d04060606050306031522050303100f031a0402130203040b0601081b0d0b0414 67
    0x400c42d83c1a00c20b0355104019181d84c4003e070350207504070714070500c5040d1000e8503410080181e20703500850381c60565070f911043c04961003a0081407408400003284141400071580b2007514840c0c150002da803040ca05122241407002d14031484042c041d030340540c600681a12101d684a070101c2c0b501d580c120340390a0b002245080000740c4443d000c03420540c81d6000503c00c51098005651a9911030351071511010b140c00130403421001d00302c405070b0710003002149104079400b1650007603600c9060103010341030526180003079900603003186041010500412401d50b600160803403050300d40a050f50343c1600c9031025000e0640001111025070360690100004000c40000110321448c052441200d180351209601c2d030703001c46a80300191400300085010000c000d6006039003600944003c01030402d158000e020076099810443e401c0d41d034190900100030340c1d5600b104286078000310300d080407142c1842c000300e5080300d0f009403641c1e450a01d50310310487c00a501e90354031982040c1c000305041c400030700c0d02c41002c1151540c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 480651789 1250 480650539 480650551
    0x314032a1507020a060e2d0309040c08010918020108040210140a020312010e0702070308130914011401030c122c0d021b090c0a1803080c0f0736060905 66
    0xb15244e03003010301c10782c0485c02c00954070742d1801c487d0140120030f0190519030040c19410f0741c0d40c081003000b6900c9503610f10034450105c4190f21070210307540c5030218000480c0d61a015058845145402442c0180e84c803043c455440707507045641001c42c48404030216482543c1c1c40c03a00150b840300150444400d50000301170710b003e5400800e10400d503a2107900e040b105030803d075405000b40c2e00c03040b0140001140500a084141c0024142c2c850440d603072680c50044c2c0350386001120380080c0c2d840c010f01c00405003400d0b014848400303003400d020248089600030700c500c80d8500b0184019540f42000c05007008214203c0354414508440c0c54840718000584540b1200c40c00300200140c40f440e00c030355a404500b00703005080c812004010030b06540e40c5000da42e8140d4450b80c910010000145140c1040110250004004e940500d810648034000c100c0e00030325044181d9501c000070750011008000448034605600402c4a02003103400800c3d84e1a0140c0c501d905002552001590411001055805ca10b510940c4108 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 480653039 1250 480651789 480651791
    0x105150a080106030803010501051c020d021801030207020108191d03030a05060a1520030a0c020f0103020f040902091207061e1103030f04110604030c0314032a1507020a06 75
    0x6541d140c105080740c01034800181034600c1880100319035030141c400b40c419194001c1081407200321042459003240d000380c8010f18140ea0120701903444c148600c80c0b0841e1002c003824114580600c41d0006003801d1001030000301000c11503c0c41c03101a40b000c0d00201500840d21410805034019121142c0e240e810448a40011518180008030b2901d0702c0380c1e0340310071651941d244411040240b0021201e5850303040b18032900228018040c00b0411080006141c80c4d10595a003144e02e20a40c8108115240000d400504150041c44003100c2944500f040740e0490b07402100050f41d44c9030300c40c0072070200c0070381c810061030b54011158002007540e0414070306c0e4a880c015414030040c074160201c091f14a401d100c04040c41940c02400021803548110781d12a421600850310820340740d6402c030006481e03900c15082103a05d2402ca000c10410451007038203031540e02400d000610b0800100d2080707a00004c18966596049012225001c03400700c0003804241c0d0b482c1c41420b0445018a01400040d40d50817101d54111016 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 480654289 1250 480653039 480653059
    0xc110a080a03111c051204020d0206030708100b04050f011d09090706090e15011803150b030708010e06130303180b07021603030207353306130e010515 66
    0x15040c100b0400e1200c0c04c054840303505080c1448410203001c900200120b800c009030640e55009a5a5440034502c070b81c103140e0300d0203814a44043d203a10015803a43c450401c00000f4002440b03642d0b99244260440c40c3c0a18062281a4000f185c00842c86801c501082c0c001000c50140491502c010030840c0540c0e00544800e41c00c965215001c3e017080390119060114040c1000d5452015031103160000140854921296609070302c1ea124403102c4031604d0001003040303584988a0501d4141446480c0090011030003c2003540310802d8100d407a030000800400c0000c91100300c4404250081d40580010480342a01102c03910300c0d032520b0507559109075000400362040541500040312441854410303130707905501601a99140034028219840c5001d0082c846942c0018a024410301404080003c542a00c0043c44011700200c2d021004045451810241102d0003500e0b4140d189211105038000c2170a490300d115154088100b80300a026024401000e5403d10040c03000000e0b0244021681701c0d82220000d40c6 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 480655539 1250 480654289 480654313
    0x130509070c0b0c0304030519030b040507031b0512010b03090a05100501060314270f031611180c07020d0b151c03080c0304020402041e060815010c110a080a0311 70
    0x203d8003045500900003401040300d06804662070303403040c41e03450381802c01141012041d00090140e030f00440c2c00c030300001e640f50a11110902c8480011454910901b080391910241729030000c0102c82c140142d42c0010f4000000c5801210f081000038429034203c0c1c02d84412002084803030018003000c1c852400002e00700341e1284585008007075441e005100203691400d03e0010458048055244858010711a001d6030a03000c2d100c5030705100511008403115940b5440c1d24881c500541318003a040f900d07a000b022080b1154000d9082d80040da608220305031195a2200342c81c0c40081d40c0b82880400050490f9400000d20540311415a00002d0403e421200c100400404200312402018070400c080c00149103580401c048080310b0000315007081c00500701603d055107a00031401045000c030310080d0703241030300001000400d5100c1c1300541c000f05140401d40c14070802c580008d040382c6d00d01001070100c08401d0b4990302e295441c4104030f030003444518160f501c0d0000c03a080242070000f40d05c40030300f024061082c1940d5 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 480656789 1250 480655539 480655561
    0x70b0703022401050d02040506030c04230109140103063216050f0a1202210a0f1404021003060f140a050306130b100332060705040b130509070c0b 64
    0x1044e40c1000e803000e03940c8185074081001510b03015014580600900540b031045460b64095900f28a40700410000408080c070f901d0411050305902109109280070720b407aa01c8001000014116030304808045501050040d10903100c000e80c100c5a0485200c20700d046000400c0b5400340340c4201e2a440040400588035401595a88908a600c03487e5100401040410707034021701d40d8840e6550301102c01814038402e000b207a01004200c4400000c042c0c500d4040140c03111042c010229403102000302403160881c42c4801c18009040504028411401c8000610320b09129a000100401c10705d034911141507a113503425540070329480e030b1240c01920613500c045070314140003994600540b4042c04500a1080c540c90700085060050305151180442802c000081062203142845c803034502c0850308840d0810702500b00703070300c0d642001001441c4c20102c10407207005d40101c02d0b1800c031603c541c0722955848404080800c8611160412548002e509080c0b00391b0503481048410142d102d4010044661120346c1918 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 480658039 1250 480656789 480656791
    0x30504020915090c0c030d09030c0c090b0a211203151a04060f020a05011a01082d0a06030b0f07080f0c040506070602040e04060510060c0305030f09070b07030224 71
    0xb50402c1c00f10000c54105881c1000030030102184070142c90802c204101030500b80c0318a01b80c00c3c1c0003e02010b09000c00d2080c40d0079084010b10343c41104101ea41241030101d40d440100d4405c80304ad00118000c00b40b515070460824110306544040705c419541042d01c0058010084055201083c1c20704c40720220b03100e28030188038a40000e4400e1003a08051604c0c0044800040c106099400c50103401503510004109000b00c4001403038403401e085681e041d96000420412b401841740e05c0120b960061802e21003600302d802c800c1c80314440205e407200c0c0d848800000141415a0004003104480010850780e00c40b50709982d400788020369216034658642410024601c102915241d540301810001000185005001001c1c25840b8203405803c007a030b226040c1000350000c88003030700e606840d60100000548020a060003070b251a04180300004c000d920b0051aa0000130b209180d0711800714082020080200700a1008202c0608400d0741d8481c01c0c98001c0d1101c0c01748451074080000100e207000201c8513880b0403 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 480659289 1250 480658039 480658081
    0xe1906140609040c0e060301092405180403091a0705011407080c09041401080303090c0411250210020d0215190504110301110a08090a3503070305040209 67
    0x9542054032200c10000101307009001e11041c00341d0403800c3c1e1041e0b100c013800b460080c40040e20008504a009544820843d08031600724141689030390103101c10b030380390f820081c09003003d120341e100c00383e90303074901501da102e03080d005440001e4a40d80f40b038440c20401801070160328484c8009011016001410710300d400070503500d5030041015407000951001c2c0b07407006000c103c04000e0020031201c4a240f0303151011308080e001003c49800000400a40c01020001c1441034402501c0401600002540340c1c10716001f20400f4004a05508505110b100354190264103002d400a0104240e030030080d401a544001900b448409400741c080d00c4646050451713181031080140790620f0359116526a4001c0003408001d1045409000802c04810f03242c40900c42c0041103005400301e55601c1485420280c4050303002040b0140d00e60081c09584000f03031400003601000c90107510850300540c96489030a0382a80641141e0080c0100401000002649a0480b0307005500030f0302c24070455200d080b54051004040420 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 480660539 1250 480659289 480659299
    0x30402061c090c140315011404090f0803090a0218060904060905011b090602010f02040b1b030f0d020d11160209090c06040305150601050a021002130e190614 69
    0x1d54050300d407015240390080a41030100045068950799080490a0306400c0307400141c1011400000d2400e0030042003220a0005079800c019615100720f4a040d07810407980c00d402162210305410030030000c0f2a03000c031401e610820681d101c0c41e017103402031780d04c001d1610240c0c480c02059480850084008a01502402019010a18a41d215194007010700755020341100c2b1503580310030031071031001c08030031286002009076a50f5502ca46040002802d4070201082e08a641c2e104000400c6484034050858071100200342660000b030141a02070b50540c0161b0348070100750400042c084502070301a600a044456441c0d0040007170035a100b00d600414080e041c501144a03480001e200c026141c4100e80e242d108001d04100c420a622880204806400903032003101c99a00ca840d6800d201300c0100b60f0709a1080081c40c11a05050580d40300079a00c000c6089804001c540c0054884100795038000128060f140b548040b5602d070828500000c00080c4100302001940d123403460200c0c2003540b100200d65402d0303000308 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 480661789 1250 480660539 480660547
    0x2010c140301030305090d060f0507180e0612030c0f030304050d030e06060904061e09020a0504110a1116140306070f1709010b090403020d08010e0402130f090c080a02130203040206 79
    0x140a4605c0c0d0301541d02660711403416001d60b40010042e019511140c12a200c000c101410464405060505500c0c500c248001d24403905208030620700c40801d60185041319070508601ea001c12141c15440b40602c880b255001303004c0e0032400c10f800000114005c82c822411030baa0110000021822180300c0f04110381e4030b400000100b0410b10740803203520340140c0a00f1000a00a81d02402c808000d486040100140ba80750320348a420b5140840c6580700038002902c041c0040c414212008006120307012201050000714000c44660130701c10080034141900c00318074042d01c0c64441c40c0900f9a440c0c40c1c1200b034400c1c82a0f400244105128802c1031602c158152103103441103040b0101010f0003000100078404666032103007240a40c5e5aa801030500845c06a000b401e0749080404c0f00030840e5605800c0300b0700c80c1190300103210040c1c8a07040403600340c60b040040041e004002c850210b004d406000d40151907003103040404200c040011039405201882200c070150802100c205107400d07800704407406980302c1d4040c0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 480663039 1250 480661789 480661793
    0x5070501090f060f091503090201090b030403080c0307030e010501120b090c0303161b03030e0306090a170c160b04211a06031e0a060f0e06060f0a051f02010c14030103 73
    0x40c1213514182075604103448100d0300d0700b815021400c4000e2004000070b4403030301d150042d541c10200020251000085403407451500b03031005000f25001820208803c1000000100420b220b94090401f0003030b440300034081565a1404812050b0380868243c03040910003003c914032030740c0015003010911014000d582800940e0200c800ca0080c1c9640580301c804943c1499440b100b40c0380201d2010318030030384455902d94030301020f141c40c05000424420040c1d00c501171200c04280c01004649000ca40f2005c459030b903a0303840c07040750705055034080c15001c40c0c4098180800d00300102c0001c0c205030303a09c1c1c48030000d814004000c0b028501c003840b6030103000c0d0794002040d0456204454080c0e81c1c0800b014046440181c0c05641c0a0801c6052004e22084c1e600003103200003c200190198414010071a40305100c030205885220341c58001c040d10f814410600b418072503a4546500c1524402044010a41c1c28481c1a40101e8101b4403900c6100c04c005520301100000c0d4580641490b101c1c500c094007103030713095a00755 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 480664289 1250 480663039 480663047
    0x231207031506170106090c020607020309060304060f0216020108070c56010b18190b0c0708010e030c070e090c1c1a15010c060f050108070305070501090f06 68
    0x8026008940c0c44040200d0f10401c0d03001e11459403c0d0f0640001181484d001c3e144e4100c6103560000d004542101092005441d800816540180c10485d4180d44d62f44481c9011002840c0e07004200151070b0000c2280340040b0800e5201070ba0b03070f500070b803580056039031001c0c4c003103910304140840148610742c4140e42e42c403036001c0740f80403404243d01803a0030074441c81c100d48210301070181004080d055462031601c050100003a100d00030300620403510110b007420b416500c0040092001e42180c0d00030800500c030841c090105882a00090080314401951080e41041e8241c407082d003805020348031f6003044500c558041c030000454a054000801405803e0305001e0041d100c01c0c0090035a00041c860990100d90035590b8151100006050007200c0b14500c6240c0341c2402d01ca00000c2d46107517402d42030b80400074044417030a03000b20040f0003481c00c22805040f40c9442801031013900e0030746400702d24040001c189c03e00001006016170f0300800c00c60360007907036a00046440c4d44240c01031400c44c0c440344204201041c02 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 480665539 1250 480664289 480664313
    0x1c0b091617100819120201020a0503010b0919060e030f0a0218180d0507030806010305010b090409050a0c0b0405130e0c01030b010507060911120c030703080a09080723120703 76
    0x3000c2956003410b581c0d00e500c0d92800040402c510b034010000040507042103e80f881c800a6042c17903000035410a10303507150191490005118030725421800240318046503940e81c42860f982c8800803003400d4201e80f00c55000b007090703007040c10b21070091003007c41d42d09600f900094004155580205480034000001c0c100d8562a030015191111110007000b506810400500520440c0d042c1c03030750b503291a480c0a00b0700510130032025141745e041c1440c0800511000c0c003a0821102e4003071080e640070940c8049440c2c134074036000107202c000e441c220200d40080398040d4240018000c407101100d03102000d501d81d00e044c00460701c030307545d6003030f020741c000c0d0320003001c0c2d50013034200f1710101c0014140503082c1038a40d1604002d44401c07104c203c03284010b800350001036180c69007581240e9007040e0010f2401000c0b4002290382c91055020140c4540004a030003662107210b00b20950240c0395900540d0b15640e66041c8210b044443c400c801010401c3c07006100260381421503181010107000c2c0300400c003a88c5142c81345503030742e08 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 480666789 1250 480665539 480665551
    0x6070c0206070b150a09201b1c090503030a0c170405030312041b030812090316060608010b311803020a020310020f03070f03021c0b091617 61
    0x70050105001041118a0052182080c09a03e100140504040000303c2c0083d412040405280142a094140c4226035050007034042d0010b082c0d50750801502e500602c407074080180c010303104a0140404403400100c442861035501d407240c0802c0c585440c101038507030041c10320450010702d206080002107000c0300101c1845100300b00307031a4a0641c903100803d0850380800c002110341030384c3c01c09000802000071416030500c038081d0954645141503070b9804100f4481c411a5104407c103080104020240610031145c2d0101401c400740720311a414507020001e00b050b403107810225483c01000c00d4860502c0360010401000e03d06070030f00400340d01020729242642804d00302e82555540d07880ca040d80484081c41c26001c1d4000d0b00202080700240c030425140c40718000c0d42055082c01844042044880750066a4000c2150305101050001c0100214020300400940c40d0b80c01ca807070f40700c40c2c0d119a040c0d0310009200700c058406c201c05580c0d410400410122821082c00054255284540c05240010103150044 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 480668039 1250 480666789 480666799
    0x1115010e13030903020409030804140111090d11060304050601080d08010b0a031521170c2805060a06060305100305120a03020906030702010c0f02060609132603010f0b07020306070c02 80
    0xc0c1c417038001c1002c44000c00d4045011840b09800d0100744240148215031440d1200003c1c01020300c00c0c004020380d0b0195480780f900820111a110b004c0054210402ca00c10201416440d1079107002d091040c1d80c0e074802e11400010340214081070003042d01c07e40c04141a541c1d1100c2592420b00c0142013200107200b00d54084200f0360b602000450880300300d150035211049121130802c01c49001d4203002200e01400710384c0c1024000d042043d415040c4010481e100d49114060b0302514081d6a0764019403180d10980c0001c096009940801c08407988980c0014180e424643d401c001540e81c110f112003d01126000240075680f04440a20b1480c45074001030040003514070300076041941031004a52507400507685040543d441d07000c0f002c203040d80024101c83c1d201140c030042c0603a080c070602044c000c140c040c00000c0d841c80352203034420500c90b510030740310075042e000604070890101400c6c210410340c0081c015408070182c401000184d01040400341e40c405034004000c1e08207615a0003050329000c071140000c90b004 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 480669289 1250 480668039 480668057
    0x15011203140d02370201150b0a050c010906060e0603030313140a061109010f09030b04111c06150f1a1305060d050118090807060902040213061115010e1303 68
    0x89200502c007800078010100350071380d2116410450f0000c0e01e110401c1c00045a1418005580f05424802800211020a40c00c90703503c00480108a078203104c2e115003064a50308041c02e07030007080607660241080b6030b4185180302c540e46902c410180c070303448244d4401b10407503000c0c0e24007400304401d410825005105002125505034880c0c0c0c501c1c040c0e9020144a8100820200b414070359940c00034104104549245060900310f82183d075500b164400c044d01c0239114840540218003d900d586141c04400b10010110903c6044c00d403030420060040d080700d4041c02e500b0b03903800141e2007001800200990780124156503820881326a0111160450308804000d107403115800200d940340c07100106400140d4001c00b0490b981050601c00d002603010402540080c13501c0c0440010500d0942610f203138640c00000403685a40600024010303000d4500c1c1a002c00e11240c000044003500050805a032411a01c10340e003a010340305e4540c41103040300740b05190103849904009070001d10902d90000300e40e44a82005008 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 480670539 1250 480669289 480669307
    0x605060f10080916031205030604020702061909050301020a0c1e0b1801181718091e0c0a0207181104090504020118051302070204140915011203140d02 66
    0x580e070100341e40000c00e081200740140e600c1c0500c8800d03003100c00075a100c0c0469203140d40d6010b100c0f030310f01c040382c1c100240400032800c140c1d07581d0104ca88040d002050a521440c4164122820019007107243c2c000c1455030b0000100c6080600a50320b07000c60503141e0040c943c034162035002100c0403a00000000c2c4948504210014403c203142901400100803d031004515081c1401d08603100c2003009049114002c200c6000500b110380d1103030381000000084c1e9100c80c9001e19558004405120301a804a840400c00010000d494444061080c90004510300342e00d440540d201c880c0b18113040d401c0113802c03c12080c0b100740a121812195004802d6000505983c4150030002c0d0390010707040480ca1984800621081d0f41e80104008101c00071150030440742d42c50980020741a110180d01100901c2c2c01140e4003041d590703103034001c0000d519005104815441d11010154460000c905480c0385014098004130f0401448081500815455103800c2d070954298000709038035802180103011216020000d41c20 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 480671789 1250 480670539 480670549
    0x1e03030b0925050304050703030f020f0d030c1b020307050603060112061e060518011b0c0b030103020a080d140d0603061b08010b0903060402060f0c0316150c020a0605060f 75
    0x1125a103108800400c0c90070010101c4030300d5502d40395810030440c0034400e0101040b030200f000d8003180c0d4941003030342080c49140e2041c1d041800081c61101f00d405041c14890605405412424024443c0d0392029020480301ca44a0b414142d40c030303000394065014010078026030405c03900a6400a0b81410030304980c824205c104403e030350007a00040d80c40340c0c8040b1091080c3c0a142d008070007404550800302e0030b00c900d800c080b00003411905440b45c100003c1a82807c0807043e004100c060311030304091028811500e501e000d400c0e82e0300a2104a00031b8940200006240b0008190302c00c2412142ea20203404550640f0340c8030b640d400041c0e2040c02285e440c0c82c00030000300786110310f010700010500c0b01c0070010007511014100101c164000b9900d540c08102e000010f6401084440c1d01550403202d441d1030b1840d151101c0303420700403441e41c030000e0b102c0004d4103c505010090214007491040c0b0415903035584401021003618011107405025910658012002450a0300066805a4080c1c081d903035059060000803 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 480673039 1250 480671789 480671791
    0x302060304030225050f100f1d03010603030e03160312080402010e090109140702010507020a02090903040312020a060c03110307120f1d0c0306040f0b04031b0c080105131e03030b09 79
    0xba13007451100c10000d03030800001103842c0076012905240c50994040b0b000d480c0d000c400b0200c6080003089032409a1b08502e00d0744104081d000030303000f0014140c4905d00905508032903075035a03100340f15400c284a2031017011103184040d01d92120380f004007110100c1003600e101e03101600c01c0b03041c015035524848072a25250407541c0201221440820700c81038a444800203d0000780c401c808590400d001c0080041d000100a0000da0341070310042c6040d0381d040481410350155400c01011076400004100c0007550010700006031a01403807040000d944140415012240130a4000d80440404c0c40002c00041c000c0c104400d0035100e1480c04034107003c1c490000e8040b02c2007000d03242030b8403950000080400008110341121002c00382c00400c00ca09050f114104030b0009a2402441c064001c40020200362242c96009020480c10080c04118191443c200340e581440b0300581c41c0c50f61030700e4001780d003035580d00008422450f0003a800001c0d41d0000441c40200d022188419820325840d0000591242c540111003 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 480674289 1250 480673039 480673093
    0x5010f03020a0b0f093c10110f0d08010e0a020301140607020310090c14030f1005060117040f120f211e0902030705010504081009062705071e03020603040302 69
    0x241b05000e0070512140c602541081c14900110040980f00000d1b180c101d24512401c4c894280200020304201240f482d02c241410a0203440c014900480c0256410081003410780d01c10b0710603108250390301e404a0040380403d10a000d078042000705000c0b10744c28580000c1108a002805440c0308602d01076254091342da5441048907907203003400040000a440d03c00c5180c00c514202c014140c200d003000384055840da80000e01030100d07070f610350200303400ba130041d10220540c0c004003401010514240c245032000b2903484400f81e40683c0034541e03e04010b441800305201544c01503c410359500b40c6034500600c10505165800b40480da1000c03d442800c038502050003640307281000202c2c1e000120703c103040c04c001da40c0d4805810322405110034002d040c408070303071130240004140000942d07280e542000310103002542c160403400e034102150b00038070580403038482c01c07043e00030000c070707808580eaa1042d520300315a2124407019104d4011424801450b0280066412170700034412038800c0c15a9a000707080741c3e402d407110 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 480675539 1250 480674289 480674329
    0x201031a06120105030c0a1215060503060108070815130b07020115090b0a05011704060203130213050a0617250b0a05190203040302060f0306131b0305010f03020a0b0f09 74
    0x1001145410400040030325015900d0642c0c452401918480c0780c1c08014005003001802702c0103034400352060f44100014003006086601c2565683c20194582210703000f1b250690154050130b00034101c4014507280542e0f5890450302c2c00d112a502c4054844002034190f40841d526800d0500b000b80d064913051000d09440fa000250513644c3c07104000880d03d16074030140c103200301440b13905440340340112030f2a841504880b0241c0d5075910700700b81d04041003000d400294007000303145a100c0358102c07d900c41d510981d00200104001901c7e524103d10140c03070222840c241d54040c11411410043c4041e56031090b81012040210f8940c5502400c01242c12001c0300100068001c00d41c00c0000f900159006020031060018510300f5080d41c000c83c203907120740d0108140301100000070901c00d442d20001030a6051500d0420404030903900545034844000f2040200040d00f4000081f0707048810303003d01011a0381c01001c581440d490901d004440390083d544107425100103101c0065070352a110320600c005072500c04 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 480676789 1250 480675539 480675541
    0x21603140306130504210e0906030a0c15170f0a0e010b06040605070f0507080307230a0f240506040b040605090f0912040b040e01090213050616141c110a0201031a0612 73
    0x14031102340c00c000e0415129074400301009021850300070b001c0d41616000b0100903500003410109560202740480118400081c000070819040000d00c407980c05590300d2441070001d950360b100c0c06070986000c248a076a0140c420801081068080d000404801d0b04c50000c007410300070300e510391500f00031160340600c025400002d040300c100904645140c40e09441c003843c641d40302a10740b5603156240d40e900c0780100226002c0c001ea20903c5081401501d40200c1e40400c0a03644501202c0500a05410344189010341c3c14141c078000380d443d113400b4600554001900310307401c90740da00c800603410b072030050051001402042685030350301080c100288050000c5810213030740d81d0b01c1c0034440b2400d020141e2005c120603205011002d1480040041ca008681045409540342c2c11a4070001c2e0148481030300043c42c0c5403009004000400020a88104ea03444021401484041040c0150f80070140410360448542020503107400660195000d0419803800c0000e0410f450110030201e8400d41c00590800400842e1358 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 480678039 1250 480676789 480676817
    0x1202010815281d04240e0f011506050c06040209100b0309160f05130905070b043c17031207030b0906102001020c0102160314030613050421 61
    0x1d0300f1464803440302c151100c201e160584401211950151800d9a00c108200d0560980c001d550052101c4c11502d00556803406102908607000300001d10314141100000f07080010300c0d80c01a000d4030100180a0084c1010307a680e0360070000780c1a0024010740c09102c2040000c2042c2c92080082c511411002c0d0003840349000d1900c5c1d40c16410322580c801c40d0700c481c40d100140010303155103c5c010100c200c4600c02003423681451500e07034109070180d00b045a03907100100c1c0008448145544281c2e900341c90010b1420007100b10360882c1040007040300508000d2030705100c00c00c6031017400008202c03e036690034141c0e41447c0d039940301c0e030f892200c044c0c4101001944500510941d0700e003484a40c1d401080807124a56000c06031031005e8951344007113184000044020700d9000101100390107c43d20311000100841da40d60100300030800072080900705a000078190840d01228103018012030f40912002000c940000d50901100d8003d80801001102c0703000c1c007142c000d02d1000441410400760022502c1d0829018000 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 480679289 1250 480678039 480678059
    0x1602031b010f092f06070b130b0c041e060801150e060f4504090b040803090f0102030c070206070204090f060e0c0105072a030f1b120201081528 63
    0x42e00140d40002c1c80325454902542d59001110301c0e09512014040c181d0786d40c103107403528204000d0f8001e0031609d0080b01b00001710f10301d0f00080054801040b208c401d00c5a41540c00101d22655020b8600854034240051140c0070031001d4840c54030f011460038081448032000030440c1070700702d01c00d0004032501c0030600200c0d0507a035501400446400340309140744c00d890464028034847d9890521218041030030448422a141d0740c004a03006a00702a4030704280c245441c0460503580b048800c180385020350280160341407018002c0b40c2c058624082c84e281404c40e0741d02080019031000d04200d03481652920040000345414909158981c0500030001d400d91031441380c40d0500d140414058100201040458001841c4070720105898664010720050401c2d40c3d1140e0314590303120341028060044686603201040141d15400c0341500c3c41c090a0072300e840d80c2d09802100e599410300d000b80441c0958001400d0301003c1c0d05c040e4001030004003034044201c1310b0a10500c4245100040c4e52240c030368507600b40082454 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 480680539 1250 480679289 480679343
    0xd151a1806010909020c0705030f060907050a08060a0f1d1f06051e0109050d0503130e0106050a2f01230405030a050309010b0604060e091602031b010f09 67
    0xa1403048a81c0c9030007400200400304034002d003480294081401c00603280104140005428064100c0d4080784c6000c4804d6511201100c07450340e50701c01c00002190314101341803d0070440d0381c82001030140f9141e030095200603015100c84241070aa940b01d207900d5444055000d284030740c489070041d042d040000101010300540c0451005909418804100803985896139440d040680104161040e408510300485e48001c4a602c02c586c0305148040701400d012000c401042805009641c2c0c03007030141d480041440540c024450007010601c2440022001401030844140d400408055940e06001140700b201e006d00210407410141da6449030314080c1c1206240d00500345c0c0d00607441451041c940f44d0350b01940e074810480700500f00100400490b440c0f4001350405144504014100d60720f03191200001403101c0c003c140010b10565804e004101c01005555801600540c5503014515001c1ca403081c9501d488030584840d001b940d070f0b80103031600a40152041e8030002c0c0c4074141007000003080740078034040710704 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 480681789 1250 480680539 480680569
    0x1b080702031519020f0d02070b0f0708061309050111040b04090f020906250605040807020102060a050c0a111507020d0f170106120b0306070e10031a0d151a 68
    0x14540b06120107030158688000c00f2205501e005a0b80d170400080d0340b00030f400f0b1100749001c1603002081c2d050420a05070741a62041c0c81a44031200c2c3c5950700d12084901d2a82078805507006418900300b8a100d05c003d4020380d030440d00943c004100a200103100710303100e074460f50014542d81c50110342840800a0390181e400b18488554095040044400001c1c00c1c5114014010341003199003000c103840201400790801030a500072008120318909410f0401d800e80c403284041b1b006001b85400144500d0707041c03280314040d802150042c5d003132115641c801e035200303132008490b0301680c40340c80040310040400c1c0340410b10030303102980503095100c0b0000c006886010022031075824081a0712121140380c8000e500103044034000d00e02503d0b480400c800b400010582100066058026041080b80c01904285040e010510030360b41c0c107140ca01c80180440071a181041444240071110800c1962481c014038107060040c05620410384001400b03005108907154081c00803510a21510420180d01d40100c80380301ca02 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 480683039 1250 480681789 480681823
    0xb160e040b060307051b0d0302040302010e100e040f020412110a060f020303160302040305150106080a06050f0906120d031401050111061f0803120105120a020109090c1b08070203 78
    0xc04948001502c6000040c044800c000002c14034841d1452109075090554034103c0956030040c0303c40500038041e40c098007059001c035103451074640399800c1c2410011000d80080c0c0c3c49413000c03080413003040090302400642070440c4d50203000210b0080d540040090000e0b20800754800d81c00e4040003880380c0345929500c80000c0c4940c0e07003d505c0c0920340120480707600000c021024808400d007000c05900038000d030b400c09000c500c110003203810a8030040000505a54007038451000c113a94917a5003c0c155260383c02495007005d25010310320200d08041b010340740c00100007402905004405406076181c8105041c031800060744031f000319008202503036002c43c0980b9080c60310207158040003050513030301d80000d05610070004540b145d00046801c5201c849000e401d101007540e03980c440c102554140302c4001e02500c0c0c0f00e40480068510704001c00035041000560607118840050f280110040050284052000520007484214004d40200009024681b0701c103071241c5864404a0060500e4110800e606150034 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 480684289 1250 480683039 480683051
    0x6030f0307080f0307140a0513080c060f030901230a0c0c030e010c140d030b09100f18091b0305010e0106030b0c0c0f15091204050604031e0b160e04 65
    0x45007440c022110000840d080311031366a101c4a03021500311030fa0281201d058100407401c00082c1d6480002020030140340d4000942d40b0740c03038500041d199020302030340690120040102100820607000910b82c8901e040000046401050510001c50801c8603d440b42e100322002c02c0140000d046e100701902480c4901d060303101b109603540c02520005020702041d041c0300c1100801002c1048143c0c2890309a8441410349441015803032014000d4803100d0b010300d10408800002440314180e40030440c00711403421b0718205610746840603140c0a18001c4001c41d20703d603115031103400801d20b504070301000714046000380b5180328a542016800c4825211032415140d050000800100307c480380e0359500848601c0341c065485aa517800c180c84c000030341d8a119660300034042070549810041070124401c03001039040ea200c1410410005506104502802d580804103220038004546c60020101811158001c4d1020614460700c1e449000d0380225009080d034400035400500301503012400c851541d000391418044 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 480685539 1250 480684289 480684293
    0x3150103031b080d0e030903010605010e150c0a0c2c060a0306020a0507051e0c0a03080406120e0a20040b030a060f0b0907090504110a020a03110c100806030f0307 71
    0x54201052200480b008400003a2418001110125001021440c070108010300c20030448039280d401400a80c1d01c07951804000182c254081d0111a2002030300614441025a00c1802984150007500c0c0300301c070b01e00c9003a0018002501040da050090031f142d01c0c0c081d0f0100c14040c0702d01e14a01180071900641e000010611000b83c0355020782030300b41e83c4c0c80080540c403443e2440c01205c85002d44000500342d40700c3e248050001d0450f4640029244502400755881c50310050284610482d052000070040e070403c100400071544181410141e13808040c0001c1100b0541460035440c0c0344103208242c644c1004560883c108548030a1034800c07401c000e0750144000d040c0100041d484444945c405010306460310580b03021400c02d0b40c00b0360126030740205085c3c00d5080c03c4000902c504413600840b4042c07031402c20768000141146003520802403150340103003041026960103c8808888406481481c401e0900c440f04660303803082086c505d40803642d15030501d45485020180b51491040c0d04042c103070820400040 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 480686789 1250 480685539 480685547
    0x1903050625080a020f040e04020306090f07350d080907050f0f0402190503040611030103020a42020127030c11060a080415110313030509040507020a020315010303 71
    0x4403501e2903041c0072450796554940c40000c0c1c402c0451300064880001808582c1c07080000c0041d01982c020360031505640e45160340030340c0e100c1700c05070001043e82c0035020400a03103c00c000ca1105180c40401580e0344030800c4e01c0340001c107501d40422404c0320b80020b4010804075512007a0f080c3e21940140003044198a41000f18102e81d0441e9040b5001e00d8100f1307248211900c0d29012284004079a080303101203544500002001c0d5001917804843c804d050424500014208500340c0341a40c0c0c000700846909440c08030f024450307501d181820341e644015103a941036000105840c480c061680028035102d10b1755044402803c54010000100b00c40c00040100480e0088000752200000d902d81032101d234020450806d48940b41c2d8a14102e41e00990000354038900c00d602c20702c2180a1407084441c03010200d941c48801080d580351600401c0020030920010342c00210860940c00c074207000381409450850988003040030740304220b5000c2c0140e8890741ca40310450800308002001c030441c0800c403040c1035042d690010 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 480688039 1250 480686789 480686851
    0xf0607050307050d11040611060a15060507110d0b01080d1805060f040909060f0b030a02090a1d0105040f0c320109080d0e03070501030204240e19030506 67
    0x80d007000f00215603c80c1d007100660200d046041c10032482a1525554a4003c203945841c0c00c0c43c4c03105010b0400462401c0301d0900402201ca032002c0303603601c4040d04046c0200d4903500401c0c41074031460a1040d01000039200c02c4d40d01c2c0341070303400307003145545660504074440c0c80c1c140628852002c011148442040004e8507030b03001e6007a114121003107991020781c402c90f10424041c940000c00c005284c20540000c00465038048004616200000d00c0030039000810151650843c00300650000c1e940c1e40010651052a0f0290030046101c02107040c2c040c0ca2041c9440c00c641c01210100c1c0d8048587c882c901c240142c1c003200390003c00302e005032910502c402c0070200b5018015003c1d80e000c01c2c00c04090589440c0c1c0240410000350224404a501507038242c1c000410000d03003913101e40d0003405541030104e01544280202d07002e80c0d2000f18000b003c03620789100001c000b45c18a400008010b440c050100305680c03100794011404900c82d4800c010f8070f04509020382020005009001c80d8030500001c0d12a41480302e003c0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 480689289 1250 480688039 480688051
    0xe01020d0e1c0b0f16050a08070c0c120507051206010302010f120603082808010b25050303010b03071b020d02040f0e061602210301051c05010507030e0f06070503 71
    0x1e4031072510401070310030100111075402000c030548442088803000e0030f056807a00c41c2c42c1c3e545c01c6420755040c110090b41c0c83d104981090002600203000207101c0c40c001d00303403185084e01c41c10302c040e16a9900c1030040b44c3e0884900003115107400200f8200130500e440c1c8403819060b50118090075171945194000781600a07044610014018105a07401a038081940710342c4c000c6800980a5540300300c107540038058411313852041d004514004981701c0342a4841c03d20345041c0e40f07541d800799180c1741800645042003d0340300403038031041241d00b9000c2c00085041c40618000c0c000030f03083c1912400c1c03c0001074a400018030100014a90407201640565514108039030711540584001a146610000900c06860200c41c00140d6100703100600080880241d0520300d610000d500ba6481500783c0d07143c046400864110800c0100d0062005024a140c03c603c0210000300b0b04d00280e440741e02a94036035080d91022103001001caa503801c40440061001c3c8000004031900c41c001d0100e0740b52035040a412408082c0c15 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 480690539 1250 480689289 480689299
    0x2103070209070c050d030b120723060403020604031a130c0306020a0c0501060308031906180b06120403030212071e030c0e0a090f0e06040309060e0f1309030e01020d0e 73
    0x205078001d0091030040d43c00d98100d81926072208900c04003070080d01104001500034110080d0700c600500300410442c0039500381e503400e02000c03c1d8220461030340c00326040d16990720405c1041700100590700c1c9001803005610400340d89810550b6070102902c00d0000401401020b412424400002000703403060300103072580030800685a52056408560412915130010444e42c03030403070003005200343c1c2000b540c4528411040f40401c030506030041c6069414601c9101d03903140d4500761250019206070021841c08501601f41c07414280401c1f00700404400545080d40803a0740010340594032204112410b910035100d00749030f0b4000c00030b80b40b0240c03852078940c5a1820540d4072115072032210300c58001030285820042096142c91344400c0000000d01e00c860710151039615000e0303500c0303c2100c0465594444c54040d241c54810700d1402c4410340f89202404240c640c840d00070f47c4ca02400d690381250501e43e1014078240061016081d1a0152403825450b03891419940104624071b0015801100e11044070b1050f10 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 480691789 1250 480690539 480690541
    0x1409030f1c110c010f0509010204050a0e091f060305010b12062701060314010506010c050307060c030f0203040f020a0e1306021b0321060f0a1401020703050313052103070209 76
    0x1908200804580c880e4804145001a10800f44a015040090103660348182000f080d111514072500701d1241303115280c1c208204000c2081b0384d20740c1000b1640d02030a90420f0f03607818402d03003900d41003640e100503207180c5080c1c1e9090140203020f4244103054035441c081e40c02c0080b48412080156079150000c1601c17032050302d03825410320b00c400402000301180154000912005d40c8900d4000919680b501c1138242c03079132030000054201d40c418024082002e8001014502d0301c44180c441d2809000c00c1115001811b0302c2d00c0084492580c584000c51103140600710103102c2c0c00c00380c070400c0801b12141e0b00c00c450641c510710070b002603040c00e1081d9180e01d5030f00040040e603e441c0d0544244407840ba0040c510b12a000110f20741e000104c10281212940c140304c980c41e1001da54147c01c0020032103207010041d40202450006010510000040000c5040140120380d40e00d560b955400d0f243d0780c07148071480b002c1d40100500300542d00f89800300c845070000c990940e0802104a4000e155680900c4034081d22034160340c0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 480693039 1250 480691789 480691837
    0x1e1403150a050a0909030e0402070807080d06081603140607021e0c0306040c0f08010608030313110d080d110c0a0f03230301060e0d20011202030a1409030f 68
    0x310310301000b414098440050503540c1c05101c0c1c01801d81040036400301d241898080707500d01d042e00c00c88041580c892041410401d0300d0300c44503610b401544540c0c140c1070b03482901088100c03041007500303114401c49034030b41005804d40c07070200340020113054226419440310041c05022900407414850b8420780500e42d4004110140407503151100c0c0080c41601400b900c3e00788424040c151010400b520700411400e2481552400514226032051240301055041400840e41d414031114031065858028851540080030420010390380c000c034884c044071302080020b032440c05100140160018495103003445810010f01c02d103a90340750405c0400080801085249100826014419140d126a05450704036100da100e403100b0788042c4c0c028000d40021030b150383c0074420640b505103103004080340e02680d00059a900003400c500444c800807803950601c038445040084400380c52029601c120191000818560f400d001c1c04a00703440003500c002040c0d00b08200404060b81c1300f10459034207100c0a00010340c0d2011030 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 480694289 1250 480693039 480693049
    0x290301200a0903060f0b01140a05030103170d0c0c15060e2e030f03021903050d110f0a0206010f150804030f090506070807061a100518090103031e140315 67
    0xa400044c602440c00111680290080d8400311022200b038884404c00f010243c905696030081211401c00128100300520000c0c03102d901c6d259114040b01c43d81403d054003041803000317a03046140c41c507000a52400300300e010710203421302115400388061010040e030740c184100000910801000303540c01040039100c4141000340c044501c4130034182c403500e0129654407803404410302c0180c040150010700c0344000c80e02034004440301c48851990300d5120304c1d281c0f851102000000c1d201c00d0024645088c001e20030120002211002040c6000b100d901400d80d96040641c2c0b1f42c00c0c00100d800c882901c0660349140542c03030f6003190040750082d030141050b01e003141c90030340300311202c540c181c001a03044900440c080080103a4a805000d2151241509001c00d641d4a0752010001c0f000c0000654046909000004214024801040c11b00c049c500000440c02e10800461031028080c2d10490019180c240c041495011000c00c0204900003854609a584042a5a80c0c41804003904aa540b1030742e04420b16541e84c3d503 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 480695539 1250 480694289 480694307
    0x304091505031504050f01060f18060902040b0d050108030405060a05220f1d1605180943030e1903050d0e031303060504080c01290301200a 61
    0x10101c4445190000c03030f400811409980840c3c00740b1450082002900041c002c81003555480e50030107404c80c1c82c01c041d1b1118428a41c44012419943d80c00201d07070700da140d0000344040c00800504641d1000006130004c04c4a1b8140e00ca80c403588c106202c1480300340e403040e0854081c2c1405203803141e120195524844e4401024840490003502007800001d40303920400a17207001c8450303c0c907485001e200d5500c8100e621083c2191901a1850403040312044140210041c0002d011381a00020540a1210100301c00c4081070761088400000c0c41001d64140e01000d41d9022000d400514015030b20203000b018a0281074520191002d05840320440c0b12070308006c01c52302800c820344101a1400014500307010703040d0780c824110701000e1424085d03800e800c5100002110001400c842c0400034071855919404000e003409002110308440c00c2080d560307144000d000d0104250040d0b00704c0c400404450405031208296003040c1070190b410310361109940c048060320b4240458140c04c446542d0f0007130810844403a25 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 480696789 1250 480695539 480695549
    0x20306060f07050d0f020d0827030c100c050f030105101412010603181518080408030307030b040b0f090718140a06020319050d0615020303040c090e03040915 69
    0x10000c240e14051160001c4c8070502c44030503850320f0681e03044002e82262551010700f8140003140224001c0b601c0001d036282c04481403581400e00c000a03c428111107411580005a2000940d01c624000308400b112485a19210b0001e0305002c2c2c43c19081101d41c580c5130005106940c410b03000e0145071715004d801034204240031a40c1d0080c2956592605041c07411050080c021000040e02e810200089000b44a2494081f190810b444040030790440490b40040c0078444c0c6245910390501c50390ba000582c103000176002400141020f1341e16032030000c00c0282111005c2200b60701c22400c0c110821015118950006602d41084d80c0380c4201e5a5031000607240003c2c1150103800310b282c1520001001c603410303c0c20501c0d190044840c0140d860740c484040341d50b80251484400301001070000043c06034041c00061503950100c0c20081800d42e0b80794081c040030034101e000d120160700008100020000200e4062010303100b82c98081040650440b91580e40b0f010700e000d001e0100307580b40204941100c0052103440104 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 480698039 1250 480696789 480696817
    0x709020f1303060203040606091a040207060608070e090105160c0b2e050913050d08150405040b090c0a030305040b0f0d0e0109031803241d011a0109030c030602030606 73
    0x20ba580e1070600f000f50300480d02600c45d00c2c544030011402a6050080d1410b0301d2001c9a0200c2c138052100c02c003c001d6100210440e80d690b507034040000c00c0d18041c01083c0003003040b00d00d130004a242440c5120b0075110000d122602c1d18804482410f081500b25490300140d5800c0b036880d4520340d4580044944408804040c0e444c1d09509040c400d500c801c004142c0c8058031415154040103442e4000840e10036101c00000038240d401c09540003280600c01d001c4160320500c481040c0c4a5040054081003c5803c181e42c01e440e60308104040141e520310400c0b40c0e1602c48001d42d4034144003891918006c00701c0c022402542e4066800044170801e821030003042d50801031051404200502001d03000500034503182c00c086010a18001c1484203404000200e00b00b00da800203407103114004080780307058401504040c1e41d880d4a50f11030808446010310103681030206811000002c0070b01541007801c400701c65550b8030703d0400480503000e100050b030031400f040407a030f4061400f5072680c44400010340240103400301c0480d08 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 480699289 1250 480698039 480698077
    0x20a060e011d010e010605030a0206070f02030712030203211605090409150b190f06050a2706022a04020901030b06070318090203160c03020f0109030c20030709020f 72
    0x1d0b072010350280300c6191040d4000c1050175950000d064440e0902c01e03020f98055014050b05c008641c0045664650380c0c4020255003280303441d4000303000d21600050042d00103a10101d45041445180610100f070700c8554868001039240128007140c101c422181d65400700600070036401050307104c41e0032106856a1020a81c202006088040002000c490601510508603508280004c551008031141540c508241010b4050705100d000d5031180c1c880701c00c0034200401c1c12082d001c00c5611403003200d1911080e8010f000e010b840e08a00a1414503002032600c2d8640070440059184581100c058805020950380540c48007241001a0010900801061380107200054144101740c0c0c0961a5041f8403455070f0002415616809505c0803404100d440f0100342605080301c5031498011000304a805209104446843c55840c2405081d9000b1413801c902051030030305d04804018501002d24810f0003c05c41da003076081c40380310010346d6416181c840d0510590740022070780600b00700a0111a820f03d00e00c8500e5103c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 480700539 1250 480699289 480699341
    0x605090105010c35220501080405030a052109010510080102030603190507030501020a051b0c01080a0b0a1e0810140105010503040303020d05010b0715050108120c10050108060712050106020a060e01 86
    0x140f070021841c05c80340b0011010900e90300485040b40a00d4029004600b091244c4505a4696001c503104110b02d80014180c815000a500724891003007a6100021605040c4580441c550219940002400b0707401401040030541380010a030006540003107840b00c04101030308145003018400d410190035540001003038000150030500030004c1008003501e42e41c01019003403200703841c0d1a00520144c0000c440d0400310741032030a207400155400034000d114000305540c0c2c0390204500070142c4140c00c00c41140076010004007609208108010050781000d06c1550042c1c68000d03c240e105000f450b050260200110341410701c01c1d41615402100b6010030040b0b540c64064900e0f413a0003550f800c90740040031441b206010000c60068034100d4849000510f4886d0b0300007901e0940c4d4108514509482c491100310500d00ea0281c00340030300929124015003400e0802110007000082d6102e940e955480c1030a0040002ca0744c0000c04010343e41c3c01400015a2880a42210307000d0000c0c10318110313081164040701c5c10 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 480701789 1250 480700539 480700567
    0x60309010204150e03100b01050d090b010602120913050c0c070f0f08010c1e020f010501180b031603060902040f0c08010e01090606050304061d030304060605090105010c35 75
    0x60b512800541c040540090f0350880310000031441e0345416800c0020081316000607034001c1c2d115602c050420900305003e4180c07000885428203c140c4144103080c00401006405200a50300049089012307441d0a1000c004101c141c118018240c04541d62074001a82044101007510168801c284c1500c141c0c542d2165034804c403d81e54010501512072424002546560512504010140548494803084101c0c8141d00700340d0600c080030400c2d4000c04583c0c01c0540c0081c480c59010b80b22458050fa1111072441d00c0c07400302c1c3d1029440d68003d9000107a00641940c400008004132540540085444251072000c5005060341401c602500380c1405a82560b041d0003030020741c1a1010802d541286a0780c0c0c60054007030701c3d401d2051002154040010901090341900150b01180c055003100d00204034082c0030301d10355271044074251406540c3c0c5c0014401d41c50000c14803030041c0401d00c0c1844010240d900ca40005012501d0303e40b140c400e4000a500702c0c5007420301b459110741d03c40d0300302caa04c1c0e09455040c11 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 480703039 1250 480701789 480701797
    0x102011806051e0610030b0a151206150219030c060509150a02041a16210e04050f0c0c07030203061603051f0b0c07050d030c050115031e020f0603090102 67
    0x241034000d4840f4114100c2d400020000d12841000741900030914040d1019002803105a101540010340c040c0003040c140d100f108056214440341d076808002c810007810490071140c06030419024061a130000001035a400501f241c0c081c408410349108940452900b80c42d07100c60240000c14203800c000c10807401000108006035441d0151040c01c0d141d42e07900316514203e1080c1e001d20768850b600450f2801400034440007600990a042c2d806085400d070780e445800002555500d0741c1600e18003407180144140e0310000c0d82414030001d880a01181c00e00a04540c80800c0080038103a15880204001c035080008114850045401900303585281c1419400091002d6a201e10140801d013003101181048010241000c80d42d4001c0c82e4a0b01c00b28108074007800c4980c4000158041e41c401d51401194940d14410381240303052090311640c0100e00b5501d061825500d4074010400a0002008104007058035081c035280501040c041801c00300c4141d100140e654142c00410540140c0d02000300040c00310154010 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 480704289 1250 480703039 480703051
    0x30a08040e0a23010e0f010305281406160c111302090a1e120b04080a020f07140a0602010e071a0d1a150319090c0305060709170723010201180605 64
    0x1256240e55042c8806c2020702e000c3c070000303059511860b031514007400089503000f001041e800d0002140141d40c2c4600340982500c0c43c05075100d4011b4000d000151070030400c580d0040ca520b00b0454480340564503944d44c403041001200f03001345e405055903000010144d04035070198038024024101c1980319402e0f080d0b4a0080300e40060442c4640d0340100d86840302407a141c0d851640b03c040012517a0302c0340d8031098542c20042c02001035110b54200d0002c1030324103120350760243c039103c0064660800d0b18001c110414105a00150543e403418805501c035800c041181c0040e904400741c09405015100d0241403a840360000c180c505030700d018039503464545401120720914504442c0b08141d5100180c1c061010f100560f4200c2450000c031941000582d03283e00319407422405801402d58180c0d582c1c45160a000b0100c2c1e015000960f41102880700003c80b2000e0051010000010261641006d90302407101c804c8107400b03080482c003526507030081c1e03200b500650b81c000b0815001e04041c0303502e0b150400c080d00b000e5030700c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 480705539 1250 480704289 480704309
    0x40b060f130f0f0e0307060f021606020901020c06090f010c150606110f0601051804050a020402070503091003050c09010309051c0903030e040b0a090921020a020f030a08040e0a2301 79
    0x101003043e490754084c0c201c15000d0b19020f58030345100d90391041c0052031b550320070718065178081c8185201080d82c3c442902c121030003944090f9854040500090a007110841c001c0e108407424007042080da243c283c030b00340e0046000e00b40301d000b4908600344170050b04200c2c01310205480c107101010502c280d00c100c0840510200b03000301c941c0220705801c1503483d10000d00410703801002411440e010460031207000c940040c040d106070350348458960081341c166440a10b080e07445620000e000c1456040802502d8002c8080c0d180030011400e02d020311b40824810010074504240c0c8030710008050020034002c10040312108482c6941c03c10800d01c002c0c00c0400e4507c000d80100d10702c00c07007030791581c1820b00803c0310900d0001c02c803519150401c25420000d00f5503485c240c48600d55001a80d030000242200f182c00c400e5550010102c04640344108120300302c00c40b000d5400b035008220101c001a03101c1060310161003c101020b0720700e0b43c4080c0c0e04002044146200840c0e0300c9020b0814010541c8031814034162110580 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 480706789 1250 480705539 480705551
    0x91003020f0409030e0d060e0601030b0402010e120c04020703022d070803030f240d081b0a020d03050306150301150327150204180c11060906040b060f130f 68
    0x104002c11500e0b07600c805004111040501d2aa40c1781c002501c8a1041c41030400045a41e00c0307401240c9000e200360012650140103200f804159a001507880c03100d8442200c0020802d00c0e05042a5110702000000718016a00031030507104142c000c2c440c08003403504884481c081003608184d840c800c142c0f190100821401218400724600c040401240d1181d02400100d04203138980c00b400944035a8030811440742c0c0003050007100550380d9441406c0b04401d00686074a80c40c1e0390f04d007020428440000c808001c0c5640000d02160058890900307824a2340d4160411903140d5803520003041c191841400c0c0d480713011400000200e01d0024242c4607003810b40c0290b078200030000c052060780014900080c41c0d042c200368030314801c0000031801001d00d0405941520090300f881d90350b00b000e0110001d400801100c0075100c082920410b64000242c1c0407080c0c0981c01403140d07090040119889601c040d1000d08043c05420028049465000011000007130281c17881001024031840c401c0146031840d450401107040034 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 480708039 1250 480706789 480706819
    0x40f110a112e0204170105070e040606170402030f0a03051206010f020c04050c04080d23030c03010b03040303110d021e041a090a050a030b010f05150405040203070e09100302 76
    0x80c0364003104407a4062903101e001200350300050040082d03900c4804039004c002c0890244410b500420341d800015001040900300188060a80150401c2003070041e0724006042160591020426110340c1804030b55603120b444034008a41000030b40000c0b02218444e804d442000c05510400914500f480d00792484510741f502001146c114100c0b189900050740710000109031440c042c0c2c0400e0b0401d00090509286c284e59403119802d100780342000d9000b08e2402914040c803800740340d040c092280d0340c036204103245103005004d0413824001809080c0d00914048001000c15001e0f80c0000c042003009480640c4a81500c941c2e41e01951004503465034402144071344983d81b900c604c2c1030310b0542d40c65081e605104d8100007058415500003020719640500803041c00111034603490008005540510098665581801544944170304181d01560180e0010900c41c14070407082001e580580b4821600581c3e60303150640111402456401160f6001c5c03615014000c4030b1840051f22800c0740e00c01d445a20a540d40d00e = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 480709289 1250 480708039 480708043
    0x70e010503010c0f05030901060515090108010b03130807060e1204031406041e170406020a2604051201091703060a0603022d0c1020091e040f110a11 65
    0x50f510302002c1058245800c151138003400285030b015114a00004642c0e680d4000690301121200305d41920440c001214039895921a8906014184480070070f49141441d0419514014114030b0240010f980844c1040c2003041e1504201101c40c02002110340100001c3c1a07041c01d81c0c40307840200da6a0008a02c0c070310b581100070039958840d58100c0d810420443c440650201910021181114401042034144080c000c0907805800580b41c0c1c0d900070005001c032460010a00c10510781e070202c1c4006000140107a00701040e04071801d444042d03510501d65003c1810890150200b00c000401d42802640d141020178040005188201000c5969042840d550718080d4100e109215001000128244c0075820016031a44884103441e0540c44c05850012070800301410b15501d104407103c000d40300c2070b00241c000c00880141720310b203480700b44192030403008000091441c0c0601c1e00c2070500d20500303440174149568030340c000d200800c00b0302c405020200340880d9401496010100810129154620600a0b9180 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 480710539 1250 480709289 480709301
    0x20414011b1a090f0109050c040c0816031a092509030803010902070c0b19090e010602300c0106030204050c0702030a0f0602160f0b070f050d0203040c0b0c070e01050301 74
    0x4914603049610a000301082c94100604a145a1003080e039604030550091280440311401400a448401c40d0901084156203001c5c400c1420083d002050004400300b142c540700c4200718504002850100b00b0741003200d0341d00044a0f10798051711900421000d028000c141161504801c49100401903040206448603c01e03070101034034140b814001030240c054554010620702e40a6952240c0c0030b5620041c80712654490207010074109001848008159004204040030b42081040098198100100207549100045841650741011110a0800c0d07071152000002d285000f8a00d50f900e06202842e24064220782c481280281d2800001414078405e00c41500c4c3c0450307009000d010102445d4883e40394a4000c030000b0303207105a0800580c81d40881003080c219002d40b0403440321611001a05055010250003445042403020480e162110b099011048440b602c5901c0320040e16074031981090003022100390400601c00c200084c1000d0902c90015035101100d41142003590240e072502d06143c280d0f45 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 480711789 1250 480710539 480710543
    0x3020d080a0510031b030204092a1505030a090c08010624050403150f0501030b0f060f0a1502030c2b030b010206011215110910080114150706020414011b 67
    0x4003c00920005211a285800d090f9100c0c01001c1c00c9074594000178200c41850341c04603122001e100c0891a688040304941d99040d040c15070000300140b4100c821000034440c959140204400080081c0d17184202d9400041e02a410203010388509445480c2c1d40c0c000c04aa00884004642002c6d1a80a290007040b4860f180c44581c1e44a90820785150340e214081012452a42c807140c2e01e44c20b02c2d00e00003034184500b034000c50003580050128180b0303902c25030458201a0809000d40c1031141105003a840b200102405c0310342035422030903001c040010803400c41c007070344800e04041d010340310729a00840915158408940701c0440c07100301f500ba001605a08452030301c50040c0c0541c11080040004480901201681e640180d291584c00a03150f100d600480d00480d905e003042c0880419901d055084c0841c41904c2d0003081d007850340a42d41400d104464210ba01c10001c1e01c11025400165005050f490581c1c83e440c1e4004d20030364541d92140c8400030603011440021f40042c180c10039400c01280da00c0c6907202e0701c607 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 480713039 1250 480711789 480711811
    0xf0d0908120a050703110d02480609041109030606010c0309061d03010c09030320071a0f030a140c1218010e0d050409061a0a0c02030a0f03020d080a05 66
    0x50b641070030595207a0440a4240c0030300001c0c20940c01e54001c140b00c2548000050341c05840940b00c50004002c1100702d00c04106e19103800110b01c40075400a0400c441e502100c90715110020411180000e01a8414520305070303000f034181044540d60901c04400360070340c00000c8040d11480da48a00c011942c030721208401500180e540c11040100c00e00910841040351400b003240c1c1c1410340d01101103803d40303107a0f403149800611040c504105243e401150700c08008900c0300003540c2e4074500850a0f94500850049102c1030b00148030151401b4642c108071078484110190743d907102d14003880114018000391108c078021b101e01c000020301e042014411036100100c0441165000e40340c040c05062803102403801400705650741e0042000d599130410441a0268156039215030b0340d803c20001c1c0c420b4034541d5001685409400301000900180704090b0f81c1c10b54494a0051218206800000d2824281a00c0680840700c0640c1c40d109265000c111400d0044213a2501c07207260300d400780e50008440d4111810b1b003041c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 480714289 1250 480713039 480713047
    0x9011406150d060f030308041101052a030d05100306060504050727050a090b0f0409020f27070504060305091605010e01035a0b030f0f0d090812 63
    0x4104a009002c81105980c4005409030301c0313502c0704028140d950420f6010070105070400c8200100c00c200c11843c41000e203001414444851204400e40442c044006000c420091107490406010000d5560f41c2d491280140b0146c100700d0f10101095110f0300050315058100000802c4504040c05240d0045103a40e07550094010040240300d5035484002144102ca1903034400040c0b07550700c0c4072401000d0b0110110004105c05040c0c1042104080c09412034043d03401c219080c409a03440c000d001444aa0035104040408040541e5064881c005010120045019000e01a056500001500640300300742c4003040f481c0c5860840641d600030110806d0510350307800e030f018043c55116540c0804010410304000c40d185240c2000110054031030340061490320703610030542141c00c44441415003511102d1580c0700103c0303c60310300d68000c42681891159280c1d1a800e1582494804108541e030090345801610040c141c00340065444910385207880303001609020010405980110300c040c0704072540440c00d854 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 480715539 1250 480714289 480714319
    0x306100b191b030e030c12070303080c04170105070f0c0507030620030f060f220203040f02040207030c15020c1b0613030308060a0e090627070e09011406 67
    0x3a8248500303214100480b141215026a9a01c411492507502c04c2d114140041c0002081c1480c0c01c503000315192040b040d4004e41300c4e0780038000c1900b005a07130301880c140d14a03940e0044412031510540d07101e10044149141203008400041d4009400760030704e07603590b00203400340a800715401444280068001c0d08560020000140e0550020461180c000010704200d050058a1146600300711203040030b021a02042020624202d4040c111424045402c0000c000a640802c0f04005201c150214200d600202007000d00203040781ca940c02a90040085d940d0356041d1070020407440d00000116454a84184500303418000380c0265150810507a00910030080d4001e0300308002c40010b010650460b00070003040c401d5852455100f0080e50098940200c0c0d81441d000f400040e1042da409a0440a0202e0512017650300204215410018a00310078001c0103003400c10340b105c4140c00e1800c1145125072440019015607001180f4030900c8050b00821180c0c0078901040c0b608403040361a19842065100d1584c8 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 480716789 1250 480715539 480715567
    0x10f080c090613060b071a190b031203070f0e030c0f010503100308070c030506070504031109091c02010e1b1c0f0b0123032107060b19050306100b 64
    0x29002c48018801c6102043c030000600440d14a030300000b0740305200003600c20510a0000c40e0440002e2090401e29142c0f40501d84100c8950b11000000251a1034020711091940c080241d0940905240c0d65103a59040c807590240042514030100000715070342042038080303841c020800e8241e13020040c11240820b0001001191143d00040c06490b20382848500440071a1248024002a921648403604960b0540c1012031070550014112000c00a0400007130000501d102c01c00c254107081560503c41603101c104000b42400e04070211070b08000040c01c404031550358150844900d480b91801134032000e030142ca000007a22100f446001d03800c00c0300c0c0b101c00c09040030f03100c08942405000da02142802d00283d5112030681c0400c1c0d00401c103240c64050280c440646070a00c800350000d00b20b0007407804101e03c1400354035410031074100300d2907450040b0340d010602166800000c444040100802c00400e072030b903105403000b0440d00480c0c0c001d101e8500050380c0c01c450b0007041c40682d20060303100e5082140c1691200d03 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 480718039 1250 480716789 480716791
    0x204020f2d040b130909030201090308011202060409020d1803020d171501080403090e07090527070f0905040e060103030933050c060a0e0d0507030c06051b0708070b010f080c09 77
    0x13805100f080034001840306054402e038924544203a0010071820711504000300410410381001c003107040d14600810050f40c3d4041150122a0b0074040541c48030803a840a000803d21102c5c2d070318100c0080e50780f05040650105040d00145155154120564500341c00e1403e00d41c01194440c03002d00d046040b80c84030b9130080c5043d0360b00510070301e8498081a203465064001020503122103011540a10f0300380001d151408401c0b0704c00d0003440d640d01100e00700041c8040c0c40c12001c0c155006100140322085011b82c428090700c80500030141081c031582c0c2c61203102d01c1c3d80702c0c0309210540010f2094070004c100752a20036004000c1d01c000c81c900c2540c810041b080c00c8001c0001c0b0300c08400713210003009484c1900c1d0b41031200c1031003015001000076420441401d45801d188040d2103000401108001900009410404030082e10b0303000342c0009403540e5a00540c00700c412251014141982d408500c08040141aa0081c81000c1c030955095129990342c2440c406041100d0095072583e4100e01504001410841700f55 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 480719289 1250 480718039 480718057
    0x19020d0b10030c060215060d050a12090f0320010e01020607210f0b01030b0f060a0503060301020c0102030c07110d23070f091a06070209060910030204020f2d040b 71
    0x8081c1c80381c0e40d94a1602c01240b6610900158000052040000ca0b12000309079028000f511003081010096660544401c0030b240020314019104020011700b42c4a417080c14040d103002240040229100c4c02c03c40c40141041079004e54180f004080300c034403035100e19051b105845c8181c00407c41c82e15030060503070b1701c03c5000038001d00510a0301d030f9004158180d4010880c9600f2403010004180d200c0c08001030503191011a40c074000c480c8641d0350b03415034907240c08403002607409180c400d880c0d444280029000e80308420104240d58004401d000203151548001e084c41c0340700c0c00b03460f00084601e40c14841580c003e228094200c030040b045171452142c007088031180e10b0500d50269903405844410f00080529140c00c81d072015941c511300055401c10900b040208000c0071955903040981d00d42c00240c00520041060f4001c0ca414000316940644074800c800186d80d009001f59110701940c227030030340303290062030320501d40d004481e0a015041c81c0761803404c00c40c002038200c2d0ba850a824031140e0501a8405055 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 480720539 1250 480719289 480719311
    0x619050d050c030316110108042307030b0901240b03010303031d2d010509061803040f0603020702040b040203090a02091b0f040305010501050a080a030e040f05040501090519020d0b 79
    0x82154a0fa5090009000100d10136000c0724031078000d03082900c225807800c0301090510440c0418003000c581c48601d00c3c800c2c22904050f9040140818110a0400750ba50780014408090281031081d00c49064022505c034040000d0030200003201e03520780c00088110b03403023035000802d0308100500119210340c00180c003001d01c8811480e00d0480e010122803506135004514060704100310009800000403131071480c65424400006d01403424441c5000d51112009000310441441c0c0003801e17411010305100f910000c2c0210401c1c40d181954170580035000c0c1d80400c204034490f5140003680c15039441c1c14801d0fa40554007210007030409800507400e00821000242c4501d100190024942043ca0490001030004031204503001f074665141d450441e09540040e000140714407154481840903407400122244550b8152404488204030a8003090090018902d602d6183d801e10041000b0b019054004d400050700c100125004052a0a249000072280c203400a60001c104d84013440803440c14243c0176001200525 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 480721789 1250 480720539 480720553
    0xc031c270828020601050108070228060e07060c030216270605130e0f0a0206030c0304081218070e190209120a0b070f020d052203021302070b0619050d05 67
    0x2001c40307640c0310b80c0300160712010042c00b05582c44815203800207114002040e040039601710150007440c11710140902661500744420a01416070000fa104821050540d05200d1719440010a44030354103009601500c24110100d0b460807881c26900d04550605034861907000c031080000e542002d0031070404072a0394880c0d601149650b503a404000442c0ca0ba040005035040c0000841c509107040d010341c407041900502915070150710740d00200d96100720000800c40e500d80d15890301d11410700445201c142036071800d00c00c2080c440d00c0c002c54401068007038401c5a10055403040e051540d0801254082840600d000da880d030900c54036009054007503002080784086c1c00030380b41ea00d460000308420644024000c81c041c400c07442d0704503401c41142c256a2000d030442d608082c0b0080c00d20b04c1031170780080350a9529842c200c1103100001072200995070090031200c81c911840f030680701a410080701601c0d04d003115808a1514076010000c2c0303021290f0b130300300e16100303c1c034260800c100041030500c25074540c001d80e1 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 480723039 1250 480721789 480721837
    0x9030322060f0e0a030e0301020f03040305070302010f0c0804060f06080c012d052203050303040b09010b0a030602040801060b04030c0501051c051312171b0c031c2708 73
    0x4040d4880c224180d00c004c1803200d2540c01c00421110000b1503003400707030348100a40c0f054492408122548190941041c41d90746001d40703001c81c0142024810380103a146003ca030300b030800e40e101101d0b0303010354000c42c41404240a410740c00030465060384030380358056029014041c0d0950260004c82c0700040031105d1051090969807540000510180e5003000160300040d03030340b11070301020444001203212084115040c0b03056503581ea0f80d910014001900020148002400004094004840320500a01809440c4e99207180c600c001e500207004003d415400c05001003410601481070380e00701c80e002081210446e01d020015503030b5600242c002000e01034090300f407030313010305150043c54054048481038440681321820010254034804a00303204002c860007004405502c00014290455520307a10201d40e981d20000346280c91244040105050001207100050301a07209458074408841000500c0300381c400c980c613040d9144411a011030076244c21030510b80800c28083c040d040d503140381820a00e00e20002 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 480724289 1250 480723039 480723041
    0x60a1e0209030d1233060c0b01030201080a0e0f06090606010c050307062309030c1006061d010504180506090708060d12031e0c270603020d0b060c1509030322060f 71
    0x1002451580180070b140d11041780254001e03000c000c06062810b240ba064050343c42d503205500611002c8d0411008a01041c203912072540712a0800c807100c001c5416031000c8510082d1101c40441f1481594022003000824a5005030446803d07154810302843c542815035903601b005114413036031600c145810100b0420f03100d0310034824a01a034440c0e00215151248184068905110017130704200050402200300809904040840303041408144c03060161805980101c81c58003455201580c1c1003001203080c20314100940c4500d001d08010307920344072240d03146941680d001d80260360560704182ca099944000c510680070702c05809451780360105542c03441000d0040004807200240d81e4660341c40c182d2841d869041401003050b00c03880c0b011640c0c00c560440180c444c0c01014031449051540005001002c0c04242e4400000140000c103d240c5401c3e00d21415682c44400d594240020b00180c000319040c00400401d03a849600c0031251b1068030340b8041d039814180a008107003100c0d40e81e01c80304050105842 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 480725539 1250 480724289 480724331
    0x1806090b01080d0e1509030c1e0909070602030f0a02010608070e2a04140a030b1008100902092e0305030901140705210c060a1e0209030d12 61
    0x38030500e0265410201154206103c00400c80c061029040702003c503601c07081100d0100080f211602c548550007039020a007000c01540f0f50301e60218000450341c11003591014440a00c1000751281e65907599490351865840040e0b000d04400b69105101030389112030b050000b4180074105200205240c0d54401010303140c840f10703400001030300c1040d0041025403044000e064442107030390020510048e48070079801030903110768010010f812010007082002c644038109020029988a401c8141d1440c0c4903a00d140100303118006d085107801207011103640003005001d05201c0580082200c544c584615900f04d541c01000c2e00040910020754580c0b0100743d1424413490025402000a5a5211002d00005003841d40030160b4030000f44040c0030190120300005500340491203950840040c81803202c10160030341c0101c10040c2d41d00e1241104100140301c0e29041a0b02c03008081c00c0b020607400c40281004240e000760031030b42d0340560083e80700245051142d20881040c4c41d06480c0090a60b0040031501c200d21a = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 480726789 1250 480725539 480725543
    0x1e0b03040f03030c08061003022104050f160b2502041b0906022b0504120c082b0804170414120307050304090b01020712050a03170c090103180609 64
    0x1d880d00d030718092541600580360600030b24a0403240c98038140d0b002a10521400d1140c108040c2d000c6039002e5011201d8400c0400c4208040d20603007640b50514080e507880e070002179010124001c00c032040c1d582001111540c801d403103050324451f05007002d058465905048001c841c8082003038110207000942c85a1281c4c4165003e103045490400d24162406010000315a00a0086600072340195800418030080e1a1501106c207040d804207001c1d210048465002c1c0b50440f80b8120322581c042c05c104140b0102581c2241c000c10240c0701e84507020080c0010001c412414072400024145050250320700c500312950780f261040e40c0c841b2035001d416040b07055030b8001e60410100541c1001440c1101d19020584004400d0000c2c011450620155945034407401603105984026131182400040350b03000340041270192140006040344040641001595081540740a5000c00e00b20088078441d40641c2900301c1c40b42180607102c2d458881400011402400a5907031146810b0981d200100002c02901449804034 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 480728039 1250 480726789 480726803
    0xa08041202090601111b0a050a08030a0207060810030308101802040828140c0d030e09180601060c06020c0312070f050315010806030a05070e100506090a1e0b0304 71
    0x46820320502c644100054101810700a41644289082d200061405401e405040103000c03058100785c045031698030700c3d81142c2d82c820700c4040d001c104450000003a000c0c00c601030342280c1c14165030b8013050320703007120660b50311070032142c006010300221740520b01141e0811682110710810b03d079500c85548152482004881d22660001400c0150900802000c07085091840d8202c1c000c03800420002c2c040205c0040080150b0f0070582c800d02c4d4000d0070b1002189210010b0140a071072455454001d29446100d04824440c040300c1c00800d40141066407402c50349803c500042050342d0070800c0c20759042040c0b40080f40e90315001c00403e01301c41c01c00e10140240d02200074004400d414050005030603203249147d00d0341001800c2c010044074405492600142c95020300b859280364440d24046400c191a404001d4000e2203001c0000416070740c1c4886c10391240106d0103040303041c940ca4508202d103600c583c00620340d020914003070034030086116801c3d8114801380800c22071401a507480d45c5044e10f400031103007034a0346 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 480729289 1250 480728039 480728069
    0x50c0105090f0f16050f0a180b0414100e0c04050607050304050a06080928050a12090609081b0d1502180d12080403050c121306090b0f07050a0804 64
    0x1000800007104a50783e0304020780400400c404159641003060b2049900c60031861012522540302d13800ca050140010000d481881165215803c01500340e002d1400d004500c3c2c82010107592181425442c00361050804e04502d151401400c880101c0000d4409908020100f100084595806004000711171040005e50b490b13902e03080030089451200d80c464070238440402d0400a10b500302244082c40409810806081080740708284518140106402840c2c0d10590b102c1d0000c0c082d98100c00e41d064901a510361052a403200c404032900302e8584210522680061032520080c03980101c225000000076004003030710312041e225219082e004000f80340781c1580c0002c08481c10a90120070040c078581c16a1200000c0c0f41c2c603541c4040b8a01c0200c080020041d51070040380401d4459030855013041c03000022a00950041a075a140e0b41c1c0c010031b8281c0902410440c0003417003a005500e03180c22150944020390900510080100603035100b444100c401c3e024a10001000441107805040608a051840c280d9 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 480730539 1250 480729289 480729313
    0x715110c010f0c24020f0c06010b130e04172205040b0a06030515030d09080c0319021203040e0109060302031504020a140d02090403020303040201090f06080412050c010509 75
    0x28003108400160400003400b18181500d9000303611403944581c407901580704102102030401c9602603200a9005490000400c10b0170070140b40050540360040700d050394042e980e18482c08201d84a403a01d01d00305aa00804100300700003142c40c07541e6015005000ca510305030001000c881169205500c8840c10f0344024018503590100007640030041c06050341d08200c4511007500041c014510713842040c0405884030000388071103030052154921a04041c04990300b4100c6c2a80c00b03040c0d04043e001c0c3c024940b0403a00b4007e860301c1e0000d0245004c0030132071400d11524400e5000d00044112007200c1b09186d1108001c0000c07144500b00b00070b0300822017040000b0702d55045204040c100021401403006818562050202590314209840e080302c19080548844050800c00b1075902c0049020103940716814500300300615070007000951186100340c0c0c1c0d552102d0380b0b031036061480c01b225008a000103207441c0c000400090849000503018070080c00c20310304010000d40e540d429a1801c0341c1d025135075003209140c4a1 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 480731789 1250 480730539 480730543
    0x120304050a0311070b07081b0f011a0904080706111209060403170403270509040807030e030304030b06040906060e042f0108130f02101d01050c0a14071511 68
    0x43c01c1c03503400500301061400b440348456000700180605466800200720049405001700c3d000030136040c42c2075506e0300c281120707014020b10040101c603101c0d11002c00d80c15900d103802c9215a1003150311001c0181001c890703031614001440740d2054101d0f000d10401038140304131541c0400d27501c208500801020300745098500281f11080c09514440e0300380da4041840f0009403c0701d600d02d0000c01c140e01c4040000319002d01c0028240d4598007254100b04810705100621040d40001e1003024000c4d201d51680400c0750060650320f104910003d05400030820104605142c41d8119046035400360700041441d5461315070380c0d6001e050580d8120b4480e100c1c030322520040c201804808a0040d00d9202c13a10406940500103807590760014501d40d44070720344030314280800084103c03107510260091b115030b100205c588806000f00d048082d90038440c010700d5200444035031181040384d2072201d41c1800f40030340c08002d0342c034540440240d11001669003c0e40da030104449c0000e0480c0850b84441e65610410300b4103c440e918 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 480733039 1250 480731789 480731807
    0x6040c06030c05091210020403050105091b0d080d020d0501080109061d07050f03030d3e0702060d0b131e090c051905060a050405031006180e120304050a03 68
    0x906080c00301c441c040b9904042a1100182e05849000804030400011130502c4a07403038081e0641880494048184103055010510500408003181c86201088105c40c0001c1140340e24a640400b202e9600800224803001130006407105003400f6041144103600141581c2090300200816992805084103000c3c00d03026214820030750f8280101302e8824450032a03147c00281c082c1a00840c40e540d0414042c1c0c0b805c0044441d02107e1040400c4020a00c603d82038200c0d2040040407002503160301400703a8410f040d04400c2d1401140d00146190001355400c0c41201d800025112801c2c0e6916402804280c27502401c2441400c4120030018000c0c1c0350200740c050485184201c8040a40f800151100041c848401c80c1d0564200b110403a0386001041c81c400115440c0707811841d00b046d408651007000c160090301400c180d800c11801e5840040c0a024084216002441032008280c041e500a142007501c503400481c40d043c02d24195806449100e48002c0264015a400c8419078801d131000014140d10001d80 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 480734289 1250 480733039 480733049
    0xf0f210f06120601050d0218100f08030301060215070e09010f05040e06040b040822060f1218060c05070221070605070818010905030a050607030c0203130902131706040c 74
    0x50410001e40710582e540ea02c0305000c0e240c020f03581c2c000e4410a5550728516424416004614109249028000d541210307a40307104040e6003402070800416420301c00310a0368162040c0768010400e15403c0c0882c81c020490160018060001d10414a6001c0d21401d1003140030704980141c10403001c0ca00801d11040b0b51181e240341c4904c0d0480303824000060704e5981540c0c4c100c2e0300540c0982c0c8402c514903101492401c4803505801d0342401c004001003082d0840d44030640e207150b94030384000030143c140d401001d0b505c0000c45070319044501209900020310301d034070480c0d50003031a14000d4100f06981c1c1c089141c1101020450308014040258040d8441c41004514058403031803603e24280b00031641c0700746260241d01540d10314034000f03014800c1240d200d90780c80d4004080040849000150340d00f002d42d00c410081d500340c400079081ca49040c60321400081102c00000c0882c108106103490a0305550082d08180b4420303094640f00d082c00101c019558502000b04404c070030290a2a060528251020422652007 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 480735539 1250 480734289 480734299
    0xd0e1b0a0b09041d0303101a03060f01140f0c030301090b030a080a141309020c0d0801050102070302040e150403050c010501140a1e1a0d051b0f0f210f06 67
    0xa10040d0441d8060700e09031001690041a1070070312549000c1c444030560715841c41e500c00402040003000c0204418000c8601440401c0418240111540158401102c2164001c0584202c94515510401071410301e0740c0c4c0f0182040c1810352040080103181c1c410124035080d6800440180309214080c455410250003c900a00846503da51041c00c035000c2d44c81032b41d052103074035080d411441d9000d004940310040c5190081c580e60352a101d21703400035040003003812404e02c1501d800011560082500a05a80701600208032561a40e802c0201600040c030811641c1d004113191600060200c0d044107000c1d9200340c0b203250321247c800401c1c2d82102c0050340000e4218540e1520191036481d8801000c0c00d81d417900f1102040345051240315091a4031503400300a80c00320810700c4030980c0a000c000b400400744408000d1099844c0d8445080360301c1e05c000c0b034403104560300300002070110303410a0080814035240c0c1d000302d0610040003000505400d03c1e2000d98481001c07001045030010308415050f81c000001c40d0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 480736789 1250 480735539 480735559
    0xe21060c030f130c120804090f0b220e0105090a0209070305070c02010311090d03050c120f190c0803010609060801080105090a0803090a1e020102010e150f04080d0e1b 73
    0x514000340c00000d07190120603400031a411040c013054544c02c80241c075183c0d0161404c4580c514010140c0da003d403050184803441c10050065800841c00380e500034003c01414103c13120715440c00403041511204010100a585241e07504504400f801221311614807040038218001041c0144400d030f5400600c071004241c905000c00c1501e542050324502025020729000802c20b40c025440701d0588502880c081d4800a44c10140c0201039100006108000a0005803081500f5218004607580204100759403001b401f4055030303800321030112848108038114a07010001488603122150035600070b80102e00040c401000a115590708a40e50a0044c94030200800003468507008003520784024141c020310b1981c1c00000f09034128002c120100e00e40e81c102c920341003414003540d81410020b009160880c095400c01c101c00407103000120750300001056640c41c105840d81d4191040140c1c04001b402282c68610a010040643d21107110340c891200403940142a00c2104148010652a407440310a01c6026640c2d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 480738039 1250 480736789 480736801
    0x70905130914071a03181902010905060a05180a0b04090b040b010f0e01140c07080313060206060d0f06021204080711030d140f19051809040b0c0702010e21060c03 71
    0x131000c450300c00429280c20b442e030301ca010042e0400700340300510140d588503030003d0085c200e11049061011503c01d0300c034441803d5a80c2c0c14001c60340602c445400200d1001e0100e072000f640f00c0403c031043d00000a003403c641c20307291038540780c0540080e086606a01d903101c4800d0340034200303131150340261403003420018081080014000e02d80c82c402a9075904104040002c803d1400c3c1d018243c68405840105850405403621501952030300311401c0c043c40000740240018110b0300200e01c05004200103408144044466102e603010840c3d0080e00f140c015508000019001402d2000c10b40107511442c2c005030703604041c0c140100b031444290340c15846a00301c04d0240300000c0d00158500701000c0d1000c0f142d6110300d524100c0000b035021308e883e0100640e00502c2101291070780704000300700010805000410301c1400100740094850200e0303000701024502c3e0042182c00140c2e802901d0600d1052500396a003000009c0492006107207200d019038200005030f5404100e51040c840f4070341c0a2a50036002e030a52420f0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 480739289 1250 480738039 480738059
    0x100c1407030f02100905040618141006051309060b0405031005150111070e0c131509060e03012019020a08070f050a080a0e090a020c0c010807090513091407 68
    0x128402071040b40101c0014131400e0142024000400c0c00030410454035039210341465020345617a08408041e440c24120420381c0403030341030842c090b04000c0401c4980504041041c0c50540c0901200001c1d056651790004851440e0b00503d0064915404526103440c9440103240c54210b4124210704161308140400021450844100d9503150091034200554803c1c0d21205007482e802ea040752021034005410002e903807030328500034980000140202e59440c1e640e01409220b20038031102c0c400c00a0b0310031908020a902c0b8035005062094020000103801e004229282d8100204841e4500d1340075000c581415142180800c650030b02e4041e00161480807040d0707990000912502600403c0b0400301662501030003400c0194005090780128000e6070795080310006400b5146070028a40302c1c0d214000081c81d46241e50099680481c3ca24004120140c42c0700c005684080380140f10710101304c40c1c0b450001e080c0d40e840060f00c040a1407100001002a680e04141d01c81605881400100380d00403101001b80e203400b = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 480740539 1250 480739289 480739313
    0x150501050c0d1b060f0522030503040b0406021207030914030403080f03070c0b15030610030209070e010516110301050615180d0b010801140906090d1d100c140703 71
    0x5503282403104060401d085000880204901505052a280034428014486c3c2e108901401c1012404900340d024610881c200c0803600e140200000c4060010400140d550300007250010f00c0b07690003505201c00889820039001c0200c0e030f0720740001d8444d0152010b206069007580e2903500e100d00610f10f00350440d00c4010492041200040e00c0d04000000117000030b200d0402880403640c4a030003d070f840d041c4213484102c9034005a0f1541e101340100404146554a41c0e02c1510459074041c12241145d5212802034811034414070384141841802c000300c2800f02d500a052001142c0328200184020b07610030203060840324014015401010042001000074a075203040d03e4460000043c1071070a4a84013001c0744444000890080414041d0780000c1025001034000c903050303042c0030b1384445e5180d50b00c00959543e440140c0d24210160081304804203510b10a64500701a08e500d110300200303d280312000700e420300142c0514a4000b07403141010308200281015a030050190f004014107544d03041d92941010440 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 480741789 1250 480740539 480740563
    0x50607060b010e180a2919120c23100305060a05090915011e0b0706060509040c0801050a0c09060e0316170d090315050403030f1103180304030f02010e0307080d03150501050c 76
    0x62147c0f01246602d8800c1e40016000f1000345144520b19443c150714071048500509207450b648a0b400c205100c2d014050900401004200c0080f500895900b07800502d0042c0400f034116280100100d040c0e00c5108c442c6000d64240c100805110f81010398101e05024180c203c0c0381084007110060302448011208074090707480410310b4994888d1a8904580241542e91000f9080071000e02000140010031044034225040f41001b84010b59a220b000310840d14006030400104905241c148042d03842500b902104090140c2162100d14850704c0d0001000e00d26485a03540200062039460740318010702a400a803501410100040d50445c3c2d6810078001a980341b14408030394070340006003810310036005a1441d0b030b03102c6401c01c50381c5d86251a860143d84112840c2a0342d82c0103030010200c3c1c42c4000300710303402c40f500010140c207542581e40c0110798240944244e04d81c148501e00340483ca2010911440302c1c16522a20006a09180740742000c8a035405644501d05211051050341108640030820568a007 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 480743039 1250 480741789 480741799
    0x4020a060503071716090605120a0b0103060504111e071511160c030605130b0c1605030d0606080c0c1c050c0114040b090106050607060b010e180a29 65
    0x782e00c0c2c250450784d03003804401241c88070a140080c4000ca018007840c0051144140e0380703d459640d250003003134034144100b0740c2c8404018079241c009040b4001c0c4d54450080d82e481450046403e55540f80018151000741d031940412140000d03200f155040e070070b41924400c0b103481e0162810140ea0b030b19666400e50b038104a9031407254580c01107601c020880001c40d000c09111003003c400b10900c80c14039500d4005107000c00c480c003900d0300001c20f481c02384200d144d1651a500092800040d520400c00c0b00203600912a0210014040700c51003000880c2030000e00940d000f007801c006030003407070148010a8000c000d0304800c0994010003086442480100d1200070300307440d112200060805160040359180708041c11500103510b0314080071481682401041d0140703000d1044a0714580b100c0100501300c0d001442260350000041100308001b482035001407050070814189240003642c11404264480414442e0040a0020704108417940314140b03c0c040050a0b1201d24441f031560761044107900600704900300b4407603 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 480744289 1250 480743039 480743041
    0x60b040b091b161a04060509012f0d1e0515010c0f0f0209070504080115081c050409060b03011d04051f020c07082803020d0c1a0903030a0c020604020a060503 69
    0x11a0141c40b1080f03030307076610518030a07a030446103101c0000e50700c0560342100d695052a000c140000014000c4101d95035404a418181903003503100c44c0345442c109a24028440000e108100e84245c1501c201135034081c1e030040500090008205406c100c81c001488800c061740c828035500c2c80740c0d80c0000d0943c0c1d00da601030140382e40d080040c28115808404160003e601c90341410070800030690280240c011664041d000340b20a90117105403042d420520b00400d4480d60101c0c00800c281440307601c408900d1070140c10200d14190700c5140d608151011500002e1075100c0000042102901240d03002c0021038803070750032110a0031b007652400d88640c05851800244074000011614400455040704c08901107402106d000945e1174002d151104401d0440300c1281b070604010020904242c81e020142030740c558050001881da06005039003032410300704281c0300c421485128071910301010780c3c04d50007100301600031610381c0b42c003003100403d45050603074030401c41d00040180b01c0140c4402c1415016940039041240c1c40e = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 480745539 1250 480744289 480744307
    0x20a05031506120712060b040b030c090a03150903090501110601140301140108011401081c0507030c020d1b05040204060507020d02120a1110051c0b0402090d060b040b091b 75
    0x1007801610f000c40404101d10b424815507a030072041c1c54400300303000b4000303012884c0d50343d104082c68002c0d44142d0180420800000d440c1046840080c01d4800c4001e110000041e06c1c0d3b124250b0f01c0010448080c03880b40d60721502c0080c10b41003035210005240c2468101ca4410001c804652126010306c04c1680c02080070303176080b0701d80c3c0e000e4100902d00f4420441d01070f02e961707560780b0480c01b0340b07400e008a0000d11802d000100380c400c404190041d0403040d240c4540c0c009020400108c0c0d03142d0000405038100919010400b0050b070312914145072407401022028180c0099500380d40e0202c4072584064425072040200b048910b402009440c4213640448250480c4e485d00d00200304481000150850603004452603d01045040c07000741c4c1441c2c03c10764100c1441ea2b100c6400703561601c20003c8448001c006d00c9038000001d001608040004007002e0005400d00d60b90340f0105540030350581007203039a5912030031040c80c01d0401e07120300e03058540c0440780300a0301d0400342d070f030300011050740c1d0f8844c1c0050800203800c0c3c10b = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 480746789 1250 480745539 480745549
    0x30d1a012c12031309050403020d0819021809090705221119020d03092307030b010b0a020c03190308130f060209190e180f0709060e0a020a050315 64
    0x6203090251450040d202e520640a440794032420518807403152030f0320080380065044c40760f01c0c070455043d00100007440142c038054600d9200100050120312452088180608040c00031b095006481c07400c145000c030328001002004600105032060f0b50b80945c00c10401a0b031050040b0314600d00c240000520491402d0094000c0c101021510f120040001a00c00c4864104102c6206e410240e600341c0b241a00c210346d0441c00d071118440e01034101800c00032101c619607004203603100c00400590484054940c6c0e41e4400c40515001d80c004e540c007800220f411003100350140141810050202c000c0c0911011401000710032683d041c5001e01080303101400141542e901007262000940c00640020182d0207600d0100082d5002c19030160140117604100307403c094003214014103580c06280c0c030306440c1d9136103030f42c00110160b04141c25200d44200c3e0341a082100040c0400f82c050f2075a50408210b1030705041502180c840c0140000c0c45031441000942061b9611074241c941000c01080d03500064046000014 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 480748039 1250 480746789 480746867
    0x2010e030a021e030f07080d080a05010e2206060e061302040e0705250606031e02010f2a050706081b0d150312090305070503150432030d1a01 62
    0x7614920034071b20045103030302d400280305030941041d40d81c10003a03a0320b608451094407400c1c071030403451a039010003041f80f102290700b00031079810215030305895419598aa000c1520340640c0200804502002400140d05150a03400c954145246041d4a41481c0a0040048400080c0403030108640403580060f400c0100e05950765004a84050500c5000135090070740c000d04080c1300031280f4946e59a404441e40315450060704025805848000307140c030344082e094540c200190440007014010043c01d41106104440d560b0300c0c1800342009111070b41c01c2501c00781a030b5501520556002c800c01f48214288501581210b8400c1d02c40c50300070540c018080c0c0114440e0030b0300e8000030000140c681900250f554858154412240600101c0301a02d681e401410384a4401030b039528400d082100018000c600c07203014035540056141042034a100300000c6402c0b48510041101115820000306810843d0b141d0051003407840040030251520141c039000a041460680c00c05007c412214030340c2000009810a81 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 480749289 1250 480748039 480748063
    0x6040503070801020c0601090b03060a090303020412030c0605071701030813090204060309021807140c0307140a03080f0630030a030c03110405240c0307060902010e030a021e03 77
    0x40300000d4a40c0350b0107010307412582c03190303c4610540c400081c1004076030007003481c20071001d405030040d525400044406070000107000d6044c03580800002803540d0040034003101e07280c00ba0ba502c4255071498a010700c1038910150041c03080180074511b91004102841200d4116076101c0305040d0342d030110b066180c901c1e9940f42c0c40401c0301d500c0850b00003480d58041d00080c00091080380d80c200091100c00c01d0b040c0c00142920a900020494011510317095002d00003403815000c071034222130620803540d861505200c40800d1240d403d421a200500405802c149201d400031400c908a007074600e0610041009980380039500c00550b0fa074054900d6080b140710600300c000b4181306081e80d82c0c9048405010340900050064100042c1c6401e042080e01101070040d501510001403080745a40101d2000b0000840b171074130b01c031a104100f00043c0305030340c2c805c00c02012030b148a03810100e4401550700002d080890207009a50194102c9810f52006940e07407101440000c0c030304d01d6500e000349403440200f440d0411520704 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 480750539 1250 480749289 480749293
    0xd0804060f0504140c1504090e03070501090602091207051807031b0e10020708030403110a0801090c05130203040210030e070b13080706261b2b020c0304090b06040503 73
    0xf4041031000b035510f4005035803400300885500d0840c000c24003095481c0d803444520550402d000c02e001c28129030b00036a0106442302c003100e06080b42601c0311421900740403c200e544c60740c0012000038600f00300d03200681c8241d00304082c02e070052409022404083d50324807240d02e0a0300d030100065019000b03034011000c00a03542801d5040d6413000b44040d1107180c0ca040303902d1155106c0f00c160601c15100241a400350742054024605080c65a5915071204624030585580100d00c84800b20300b0141c01d1141d048050300410489280b07a15000c01d1010031101c54003417500305801041000003503140d50130354507110039562500251200d00500303101c0c10103c80744c0014034039a0380015003030b0300c082081444e1826158918107903000590354100030f81c0d0100c665034402400c81114680310302103014070380c60b0070341c40809180c03030380708000f910300501c2c6043d848001c0c0e0900b0300c0b00d5600d884050f140c6058540e046803101550442c902010310000903528001c2d807080754105074907409040c1d5107480d044180e800a06004e01 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 480751789 1250 480750539 480750541
    0x1602030d0b01120e060702160f120302011410090b0f010e010e030c06070609150501080703030807170408190503010f05040504060902150711010e0607120903050d21060302030d0804060f05 82
    0x10390715100c5c20706950400c0188100e4001d68904e1061100c50011200050100190b562900c8040c8006820a2905030295540c0d0341c4a1001d11004142c41c03841003042070a2a20400e04007070b080811500300c054681d006480c05540310a103640c0110044207420000d082000c460190240028601543d400e80b040c1c1180020404500700480340e0007090071380344246000d41c94804100c4085088400074841c0f012a50701c106820800709020b0329600381c01c81c00d40d142c201c9a0368402e04c900d03007600710b0541c2d04542071940028120301800c0300504450004485207001844c651602c6816446001c60740107681c4160740d103c001c2810441d1552158011070740c0a0182c40009900b403a40f00280d412403c0242c80f00343e011058a00950f200383d9891070004001041d05090107015100c4004404032110140b040c000214008800b01c1e1080000c0c000c0451070f5078400000e40126000f9207510700361811114841801c000003807005982c0450f070407003900c1301d03498400426621802c1413800750012040141481c0e02c2c002c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 480753039 1250 480751789 480751811
    0xe070305060316121703060105030412030237080708060103110c101b0305010b0d05060f220c020f0d030507051201090f05010e1303030c05040e0a0605091602030d0b0112 74
    0x42c00600c403ca0207000d0003031102001703540c25201840229001d40c001101000040c0000f020050f000c3d144c10520324005041c8809040301c00d142481d0448001d401c04010040c5074000d05003600e035600b0040086c5040d88250800da04054182ca80c09461030341031540794243701041d62400429241045040d0b4101d44902e5100c0b10400e0080c080c908440d150b0019105440c400e560007400b800b4100d804040c0040d04d401c1201b2030182c010070020704201d074403c0c01000c0f800c03915a80ca070f80b007810804a078401c0384044803051040d4003c48400c05498020340d0480c074000c0382e941e2004584d500b01306205080110351035035500350840d640d100d820040550607212100200f14091154040300228100880410a60744c9600c03041d40400782c02c40c0e10070450304251030440d0000b071107908000071240d10390500c0da04280d1504010384542c40110389030f85019903505400c00c09072400349500d581128240341108080f011981009403207100da00c007840c201c692501c06481503644501611982c3d1040c0d0032080011178420 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 480754289 1250 480753039 480753059
    0x414030109020a14240414010918050402120607031a01030b03100e120c071802030105061912020d0e12090904060b01050d060b0904060b18121204150207060201060e070305060316 78
    0x5001f002120700d4505030340340c0254000d24555055911840005504090440604c0d0241c040108102c0e00404034540c1c2c804415010400140a1182070300c002c03a9014841d040001114a849641030403d41018003e4541d42c9011079200070034600c0c400081210100440440d02c0c050992010405000c0e00188400d40c550003c00c080c0d090f110500c0c10004290203040a01c0b0070790100b8050242d21050403c02210f603030801c10400c034550719003030901041700307600b016240003281c01c1f101291581031b4554a505c12022418030000d07524042446595041c081e40c20082082014004c1c0300400307441d030b1001c10640d10380c0500309030740064078603040912241d40c8a02409102d0340103254018021400d1000c0421040d00c20780540343c000307540e900304051441d102c608000703004521240344802401120180c0303d1851400c00280040c0c0400c2441a401800548000707280400ca6800701046902d0080140490003146484581051003458041030701e4550400003810300c404030341a0181010b00c1000003c010b015 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 480755395 1106 480754289 480754297
    0x7080105100e0f09070c02090c07030e060d1e0e01200f070c030f061b0305090c040c17040b01090c05090306040b1308040305030414030109020a1424 65
    0x1588010913500a4140c0d0b00600040c0580403060641c05d01c00404c0d40c01c41c095000d490f24094240d1402020341c0c1d00c140e02d00c3d100344000920320b0441005074004291040c0c6010900b02d1004ca03044990005001c80d64020351a54200040038815150f0b400300e01c16690001d0140074038040d5040b1407040c09038040d40040361440445040400441c04942d4000001442130300009504c0c03000b000001012001c02600f6402c05040a0802010304000700c2d1072900c10805980c08508200900019158511100c40101e500c007444070070001401100c503000c0703040380da580e4000c02200c030318500c0031a0a44904070f103080e0554404404207000402c4c032080c255010030510640e10420445644a000a51250b801580c041e8000304007802403207412a02d5507a41242107000b0400181d245d401324010711642d200f608140d051079100716900e5140c0c403d82031001003108447d007800760b0b511489209030f504 = true := by decide +kernel

theorem cover : BRFrame.Cov 480575539 480755395 := by
  have h0 := BRFrame.cov_init 480575539
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480575539 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480575539 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480575539 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480575539 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480575539 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480575539 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480575539 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480575539 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480575539 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480575539 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480575539 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480575539 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480575539 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480575539 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480575539 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480575539 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480575539 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480575539 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480575539 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480575539 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480575539 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480575539 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480575539 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480575539 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480575539 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480575539 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480575539 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480575539 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480575539 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480575539 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480575539 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480575539 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480575539 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480575539 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480575539 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480575539 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480575539 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480575539 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480575539 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480575539 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480575539 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480575539 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480575539 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480575539 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480575539 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480575539 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480575539 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480575539 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480575539 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480575539 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480575539 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480575539 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480575539 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480575539 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480575539 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480575539 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480575539 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480575539 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480575539 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480575539 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480575539 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480575539 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480575539 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480575539 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480575539 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480575539 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480575539 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480575539 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480575539 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480575539 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480575539 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480575539 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480575539 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480575539 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480575539 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480575539 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480575539 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480575539 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480575539 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480575539 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480575539 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480575539 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480575539 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480575539 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480575539 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480575539 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480575539 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480575539 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480575539 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480575539 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480575539 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480575539 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480575539 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480575539 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480575539 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480575539 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480575539 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480575539 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480575539 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480575539 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480575539 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480575539 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480575539 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480575539 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480575539 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480575539 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480575539 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480575539 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480575539 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480575539 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480575539 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480575539 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480575539 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480575539 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480575539 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480575539 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480575539 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480575539 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480575539 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480575539 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480575539 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480575539 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480575539 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480575539 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480575539 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480575539 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480575539 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480575539 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480575539 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480575539 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480575539 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480575539 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480575539 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480575539 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480575539 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480575539 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480575539 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480575539 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480575539 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480575539 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480575539 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480575539 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480575539 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480575539 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 480575539 ≤ n) (h2 : n < 480755395) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
