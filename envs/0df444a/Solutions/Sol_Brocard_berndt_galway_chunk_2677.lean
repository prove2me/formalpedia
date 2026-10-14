-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2677
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:24:57.956454+00:00
-- url     : https://prove2.me/submissions/543c481c-a7f5-498e-89b4-8fc943a71832

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 481294964 ≤ n < 481474820 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 481296214 1250 481294964 481294999
    0x20309040f0515040506120a080a0207152c04060f0f0b0403030813030e0d061e15090906020d060b030103120309020102032505010c0e03070504020403080a030507170a0b010e 76
    0x10252503102e40700d285ca85001c81d8465465120080f0320b03000c2c0c081580c601d46014a0440c500742e003c4641c0c41c0140c091010300182e21046107103280749040c126200e112420b00c203062881d001c00307004075808440003d80c10441c10683c8442c81040040d01046204162050800405000742801c40d4817100300d460003040103100107607200c0f0000b504101ca4074903109002060b4901074400610007401a50807a400d004d4800510800780c110a00c0310b8400b11402c804860282c0f00071007074900d56203000d0401c441814041185012560200c0302c00b074010b010050038050211a0501039a88551042500202c040014014000c0c3c2401c0114818204c0c00c08000041d80381d40080e461340150011085981c940c0d590b0750700c41036200901034980070340c440020450b00c41c0403100501424500c0b80314030300a02c0792900205050030984200c40589400400c0700f0300385101d0280c21006000700804031010000504118805e0101c40c24a40e40600c1c58800017103900082c54000408500b07510022a01c036000c10364070700c0500c6 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 481297464 1250 481296214 481296241
    0x1509020406090f1202090402130903050d050708091e030d020c0705010f050a0e1903060f0501080607211a060406050702040b06120a0b010216030b192018040c020309040f05 75
    0x1a80c2c10345d04d04410b5647c41c000152142c0030b182034038603140d0038000d0103010180d001c03000701554500c55604004030b44400804540440b8229130601041d800f000480034107000d42008607440b640440121381c5450a82e460350410b0340c0081c0c03070f07402e01544003010902940d0f0b0007800007282900103150183c10810800c5e4010700804040d04058010100c1061085861075044140d2000c2e40d00b1a0040c030000c1c802c00f50f00d4009090911130501c090240c10b000c1200c00e48981c51240841c3c0030840d280c00200d0581d04c0703c0e0010f01301c002d109000c00341d0320002103500e500d403031000d03100806045c1c407281d844010074018002500c284008091086000300704100045c240405050b0304480e2a0b00002192605240140e25095010a4074000c03040300ca580001000340542c41c461280c0003010300c0350707050b000420b80700c403c0c0c2c0d0240c20f82c5281d581c000702d0020011207000000d0a100007000ca294084048100003280c1258400b000403001a00f00241d15941c0781030500800940b1508944204042c0c90300c0509074010 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 481298714 1250 481297464 481297499
    0xf0303270d030e03040902032d0601140c1603120806040c05041509180b03010b030d2304050a0e0f1003050709020f091302040e1e040809041509020406090f 68
    0xd0560f01c620112683c142041954090082d03450300710f40d00c1c102039961020140319602942050009000d20309800e00b0103181d89809071074103850368001c1d0380c1041d4524140d80c11850b4074100c2e40c42006014652064440c02210003940105105800540c8083c0c006101f428000c0940380928146107103a8900b0b0360000032541283c207840d10700449505560000c1f02e21099a1b80107850030900c44601c00e0301c09519500c0904d4010b4100c00030011041e0520605488520301a00d2001040709000340d000d03134001c0b00c166006842c902e05540d5145c680c035280003403405011500b0a4034802c1c0d4800c104000300c04902d03c90f42c0c010282d00310040020f80303980d4605544800b94090001c042c1e4010483d0458051a18240c41c40401e00a0030501c14440d10503910703009400c603100b41c000d8017a000001c120541100290b0b070b00c047e9400c480c0d404107543c41da180e889081c2d1003417548617003241d07070f41d40710462000b40c40006801a007000c0001607a5a4900240102040d501d5048520301803101c00381045480d2403030592100 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 481299964 1250 481298714 481298717
    0xa05010503191407240905090a150e040308061203030f011a04030203190308070c0b0f22050a030e061213080f040e0703060f14010309060209030f0303270d 68
    0x902d1081440c020040100c032005001c018407520740041801c80075000641082e40741e0102660540b00d0480044912404c903216a5030040e5441000c00c0b56091660005d00862199580b004203e0380d44031704144c55200b003128164009040360040c00802d02d040382c81d240040203020011820340c1040b003918560000107110751104552000c01e11004114040d0507035004580080588400c0510050140c80c101c44408080740001ca0004c00155614012440703054880e0f040f0110241c4c0369500c3e003500f0f008a00c090100c0c08210102921030740048204c0e0914050303a4820000f81412141502c0c02500100d01140514407078041480004c0d101142000c0e9507510204a2080c03000c4840b150a0500051169a980d0596244001408586100d80240160280b4000d640c10040a5940e40716000e000c8203034014030344200d4a8900042903584242c110011250068900604e00152503000030702c1c0c0024500030740a160808810040c0c0145c28005261030400c4040101d81606100021940c8602a07002c003c030 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 481301214 1250 481299964 481300003
    0x203030d09051203040b15011b080408010b2403090a0606080c152502060904062306122a04140f0906030c0d050106090c03020903100b0105180d050a03050a080a05010503 74
    0x82a1700c070300b004c003103990b800030359449d603040d11404e10400d16403081c040c80d0095800c103810004c46050120136000c049000400b004151824408020300381d50015042d01c44a10a5500440104000340300b0070005140000003070800c030310240c05020000e05030020717503c0716540c1401600b2034054402c500f90700a400482c846036104210340b0005e900360040d891b016800915003a0003142c1c2d149280c0c00307000b000f03403051440810b95900c1c0c800c10503d031250794100807000071041c012500540b0303980708107404801d141e2003a80901e001c000007910290040c2e80300302d6084c1125140340b40c540c01d120341544038162066a01c242c02c1d149c400702190743c0310001c40c1124018800fa074004010321400398482c5000e4000d648050103003062042c0001c000e0340224100c544240522180250b0214807032240c80340b46801a140c00741401844511400450700c00c0403125000340d45109504000358090280340e07000d601c0381d12003d882d60081c0318002d11b2054001c00142000c0e1510006000b00c0d5000250304928010545414 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 481302464 1250 481301214 481301251
    0x60909140f1513020711011106090307080d0b0d031206090b031c05071401090209090a030f03020a09030602031e0903030108030f130915031202160513090203030d09051203040b 77
    0x2880e10380c0c5200140403e584086490340c10800850141c20b40030409070b840801c02c2d2150030405458210076601c000d029401044103500090a8501501e407095622034002000002d400104000c504146411030004240074035400c5003003514865a400360190800402c9016000740c0841e80d81c0190420f80c410304100541444d400620800449424170b520907000b15030100076418a9000c4c10203c442244611f00312800541e060000250302d4036119050760703590b502c8100c140c00507402544101c0800040100804002c000702d0650f00003180181c91084094401c0d10301303149001d100080c00740c98003001380c104000401c03003400c0c000250b4507856000f0560f2552041003d000079000310303031f580c040c29103503041c00729061041010585031421240204004500640c0140d0200e855007aa40c454041d1112001c806000c0c40c10420080130706052001000540c982d081d0700000c0c80c40d00078402501d030003600e40100200f001014800059a02220000b1718111704150342c5d100440c040c000d0400244d14a803c014 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 481303714 1250 481302464 481302469
    0x15090406051201020d0c05070809090405191b060c0209010b03130f150c03020903191a0108060709050604030f0f050109083004020a15030e07060909140f15 68
    0x1050040000500741014000000e1042d4082c0d0004222202007500d81099400198010022030b00038a80c04000d80c0c0c541004142002a1150090800d5860303101e0074610354460ba030b000046100d01070240300e42904003031083d5030107240188640c01000400c0300011158006840c2e200a0394150790364981195165038034440d00b42840203540741d020700b0703161501e6003040c00e00603080d04a480b800656841031001201080d000e80c1644151052141c06034071a41c0300c1d10000d001610a032454a21600c140114002c07112141c210581080e0820856504800244507103503410142010040c9810703213406040034030b1034032a03030024400c00c2030180c042a0400401d900f0404203501c81480b41360321040f443c0d15403140d180090b920b07200c004034003c50015a490302210881c81e202580d84074903802485482c2e1581071024200c4607145080050041c161030340c6245144034401d1203800050700195445402c6c0e103103403201820075100124090400b04146400303002c0c071b00110f444024bd1202c01e9080c24504644c09401 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 481304964 1250 481303714 481303721
    0x601080f0a0828030c18050906010e03010b030307062301061e02100c120b030105090316080d051501091d0606090a0803070b06031e1c0903020303030910050a0902150904 74
    0x1032800055541d012a0010f044e0140d0260105062030f03641e09400c0c820713032246982d20014174018190311910550004020390b02c80c0308002c09009010300003140140038400440c0c9981c00c6603804482d06525110394a00200b46032140520a01c0207805824071381d49072480c06010003070038520101104040034090b00d45ca130300170442030a0031100b08404101c08404200028604c9114988004146062240001d80303444c05008035400f80f220003010318a0410324942e04040740c00c940000f200e04075424004104540002d1007a203108082a07190007011074510400148003000341d40200c0d61800880300039244e527800101e810756000380c0c2511510b50b1116010001000d24070542d10107080c500c000100f21007007052041482e80034003c180c0c04c44100640400e0103520101d540903000c14540c1c007004080341d40a000c01c034140c02801440c00e0504960f516600401d083d0340c41140c3d511006c2d80024000d508101092141a6100781303030300410070088460340d00180300c8801d0107121103040715001c00d60070b00b20b90f40d0342d0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 481306214 1250 481304964 481305007
    0x8070318051801080105010f050a0905060a030f050f060f0f130303060801020c030c15090604030309020a0b07030206160e0a030f0c1203091805011202090910021b0601080f0a08 77
    0x2403282d00340300000318100d00012400d001d10310a9500704000054034841e071035001400c0d100001c224288150402c898040200301c01000c260340a00e0b01c1000101183d602110303140114000c8022304005044441d501e850103001074445000d41070801d003041480485078182c66002100c407455900d01070301c5400d040707020b4001074004034990b510008400819680000007003119119001c183c81c08012035410000b1070801c101c8403c3d02d55040000050000391181c2d00003075005100829014000351a049050f84030f801164003100540e011310140000301c408402c2e05190000c071850b11002050319000428581003461200a01010450249204210380d000e00e07170018101c843c810f40340c0b010417820300400840320303442a2000400c2d4006402c0d4000b5041c00f66905031154940c4080040c0f565500b40200010000c01d28400c6d030090048503059200d8a000900b031407109440313000b0307aa120002c0e00c2410316406034030107411503015142c0d481c021807010401000031600120300c0f0f40c0314041205003036508038005 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 481307464 1250 481306214 481306219
    0x6070c0c060309141603210203040509041a100914040c1202040e0d1701230d03030207050d030518060f06040228050a080117100c1710090e03070807031805 68
    0x2130b441782e41d501180c0c2040800c0728040d4100e4604001c0003256085403900c03000b1182c0041e001000180010700302111400e0b00584034840031803202c5412104540c002c0340030f07505045034068125003040315100d43c3c01040c20000070302c1d80103041800d180d55100d032308140911072214800383c2c64080e00e0540d40d440d0f01000001c1c44100a070f07050340c0b08510006158111045011003220b0304034002188103500706460a01c3c0ca003009030010030540c010310800c450401c1c0c0c103100b01d042503001c00044001440620078601c0781109500e0208041c00c1030b50300c00804100345076004280303601200c104916840340c0703000c985d08000b0554005039214036285800d600c06003503400c07031078624000d1001c139446143e01c10f009006a0402c0c2d40e900c141641c80b000518000c040d081c4c148a1f00303034050100d040c80f11203030b54010480c0491031705080d85580c50903c4200130100c800ca0f0580200541c282081080380c0280c007d503040541d45401031441c2101c0c5940d41800d03070040800c0a002c1051202034520065130048011000d050300 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 481308714 1250 481307464 481307473
    0x140405090a06030b090708210c030a020a03030b060a0e0d110a0e07030c0309030503071d13020c0609030f04030b06210a03030c050427021e03070206070c0c06030914 72
    0x20000000503020303a1004440b607100e03010009411710b20115000b0280c0314803001426402e0a26101c240c0c004180340c01c2240c032008104060348403501c0810042c03480d2483c1c0c0e005040880400c0c20050304035440030580a0144074208000c1c100e140d07014810714503580044a060b07000303075214100b514800703403044211a000508a000813466001d4600c4c0a03105203010350b024482c54807400412825a004003034028003040c03041c40031480443c0110307400105189440001c1d040b0b4040c820002d030001c02c1c5508032024490b400564031600441c240300700b907400903911300298581281003592003100d1003030f440003500303401004010130780c0c2d9a1000410b17818084d0f14400100c08080c400310803030707c4451840303080300030910781241185600e0081c0c05680032a000d080302c0540780440040c0c529008d0750300f0b80507600c90503804c001c40000100f408900c405c4e011010b8188030f40320719250602911301207001d4481c0d4148542103190b9400034243c030401c10140d803001e24021034407030359510b884014041081080b0085e07009 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 481309964 1250 481308714 481308721
    0x50303090a1401060f03080a030b100507140d02060103230105070905040b010815010c02040b0909070305071403120c0a0c1410081e060102030408030a090e0109150614040509 76
    0x60015084092901907124140d0390000142518204c500d01e12406140c040b100d007041001c1111a03003d08610b09240c02c002c94013856150004081d04084144900814030201e244014004003604030403618403008000d0911052403680030f5510b84052000821410084a81e244000e81003407510103d001c4c03410003804942001d08015090f00c0d03950241e076011b14508100d4491a40c1706840241c00f0302c5500c480f0040214146004603000e4100e4002aa00140c07160070161040d2100340c15144100c1c3d204002c3c0c5051411480d00d1130602074950300010a40040b510020740e155400b140410403103444d046065a96402e1164490906074940ea024182c0a54203100003102c070340e44007105004201c00c40f042c04113550541015076500c3c0068ae508080c1c00903400401c090619079001190300840c05004990070030b5500c2106905e9a44080a4800060b101c0740c020400c8045103203115001d407543c2c59060080c140341030b0920307008800c50f04c1010208081481e00781d0034645000212005800040c0c803036545c40c0f8 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 481311214 1250 481309964 481309981
    0x302060c0f032a1f05181002090910031a04140a050c09010b130348050a05181f06020c030705090c0a0f0203090a03032d1713050303 58
    0x44032071603c40d01c0803461031003036011407000c1031281d141034244807601e10000d080100e280042a000740b14080b00c414800340d032411542c0030098a00b0030030302e014016a440782010140b041503100900080d00b52800c5020500004d141c075068600c08001c0030006481566860802c01c682c0354000c86010701e0780c0221001041485008183d50246807415118000300e6640e4981490491040441180074240c003004248005454a60845000042c1c080d130610160141800d05404895000a46c00700c42c0a060000300315042d4814030000415048034071518980c42c0074045a956003018035000720030041d12000560000c4000081100c8891a04415044940300d2101a60380c205040300d26201c0c0c8111000060342d80760a2603501c0c45805840c0d030540c10310045260556944950050b11000d6010901000645031501814a00114000e0307552840c124100e0403002000e20301904d032110107510090801090350f0b080402c19403d0010044441506d40c0c85e40076401c10003801e1103005082d40800024441d222 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 481312464 1250 481311214 481311247
    0xf0c12030c0507140109090b0f060a090906050303270123040603060e2a1c2a050a0c0f0b04060b1207151b0606150e03160302060c0f03 59
    0x491090b0101c4070107079103440c2011440c0e8189003030b5900103130011106008501060700300c0500c0310000341803c00413032189000902c03103800400410740000c5a440003041851124003e00f001004103034042d520b014010741020f049621000c0d880c41a501041380e031500540d00c98104250007100c0e80c0c81c8104103148007003d0a605a0281c403414002030304024012038004100d03401280034406d50f44158901640702001e1406070000400c104100903000d00001108041c01d0030380304003100030340400040382d1000043c1080011042d00d2415801640400540c00302c0350403d00f1071750706070303c00d042900020700c80713203403031055410007280040201482109000400825401950030800c04591004041e000c480b070840e52110584a1494200d080300ca07899456402101c5194410340101d000d040d4001f0740d621030707a0a40b2202d6005d100c80c8a032402005c2001030b4028224111204110701a2110069090a001e42207200c0d01010384102307400605200c0503a01004042d0100024030140d03070711410150340c0d0000c030 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 481313714 1250 481312464 481312487
    0x30b07030b010806090703150909060b10050a0903140106091806050609070903030e060408030705100f09050606060a0203090a08010c140c0d030f02090a030606050a0503030f0301030f0c1203 83
    0x3007400c128070081558010780040b44680340140c42c0782c0613591461403c40142400b03a800c400104511000450050414090441c015004034004528000030f003003448603260015403201d08200c01800500c48407070703001c000801103e4100071b1102d07608100d0f50702c035401480c240c0c0c0b01394000c074030b4441000c591840340c86020351211301074441000b281c1e86810034418141c404031b03030000006250000600c00680650038680c0365510181c0210300b030546a0300303081e02d540d100030001e403002d6210050300e00c4000e8660042d80154250000c00b8415512207a54040e070700c580180840e8843c034400316640c0d42c000d100b007040c0c510141c1d00820941986590f014414024190110048005076000c0301840c01c04800b401110414050322005001820346800304600910341d442d140d9580a40070803a01c115540d030726485c00b000e9030060300c0010b0494904410008030392019800786000f60010f100c0030150340018800d480c11281c0011400321880c205282c03840416540d0780200c144901100c600c00103040d44500301654 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 481314964 1250 481313714 481313717
    0x20a020d05240f070f080f09120403060e0d0e060d0f0b092401082205070b0f0c010e16050d060608010515103e101b080c0d05150a030b07 60
    0x40c1901d41c0b00b0201d03441c5c00591580c0010800d40c4000c02c403408401140c0c2039000050b041900d8200c600701ca5a440a03604ca07910544505e5219980408880800d0221302c181c0c0920b4241007c50000d8a000304203e4020082210429651004420200901a001514903c030700038900955440c1c00842c801c0c6603d44100c1418580d50180d0442d08154019001ca0703004004103403440c02e0082d01b00020302682d4160702c00880d454010380b00e00092020852001c0c2c1040d61800f4071094903a071032414254216241180140b115503c05400d620300300807180e072010240c4000b61041d52482c051801e02901a01003a40400c0d0903601c0d1204221001801e03d022007511403080390414200b41e07405900702c8005243c54196000c640ca0725940341c140203000e0300880d101a20b0807401c40020700340e986000c1e04040001c01300003000c0780c0f00e04c0f00e0ba004000208903250a10300f14103000f140c0703061481c2851500d0183c081c00140c0b00759030300f000c80c0010342000040074954a00400e2051703002e407249003035488041c085e01c0880 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 481316214 1250 481314964 481314991
    0xb0a0302042c0c18091510091509051e060f040e06041107052d0a050c1507080306060703030b030307061e02070809040b120601061716020a020d0524 65
    0x3102d5207286811504c104004026448081c6101820444108805400c51300714400545200006803103044681c07000d070b502070b00d61104070380c5004000c4118000210001d8100b104009082c485943d80c06a60412140003a4100c2c0c201e000650108500d4441e0255003001c24002090005110000300402c6115103815501840207020041c08049280224403008203e9080f882455200c0d081c0800c0b4800820654002903090700c0d4030750440f50502100b10f1003540c8540103403034602a035080c48a0303140c90300012030f1b1445c0d2400d141c2d41c0314551076000152900348204000074180084c5440380c4c02068022500605603035036450307680742040c01040001d90780403e40030610702c4081015201e2003642d030440d4111400e0781c5005a600100030081190a540070351058514004000c446010003080740030300b074191101111000149882c500ca140e0090601444003920080392641645c0401d40c01d51881e41520104070004061030700c0c0d802c107154041000898040c003918020514074901c116402000d0a08508 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 481317464 1250 481316214 481316221
    0x1a0a090c05220e010f02130906060e091501091a18010306051c0602040312110105060603100e0711010c180b0c060103080c0f0607030f051503070b0a0302042c 69
    0xc90600e0800c10b003a20014502a40d034500c4940c650409050024010000603000040182e8401243c10000100d0042a40355009029080783d510403000900424103000440010100004042840081c00c51210301461000c00c4041d0740900072080181050f001190042c50100ca442071094002d01c5402c100086040c0c4400e000e94081d1003418141d403805004208408100f44105011a14071402200c0c000c0d070802c000004501c1c83d0b81036880c0e0842d15680e102c8003000074040c1500303480c00a0314041c8503040c100309020180000384a058220380356010143e00c15a0307100000d0f01e4007030f1310500040d003e500707042c01140d2060303124040c12040b0a111203044040398071411000380c0c5000340c00e80c210a581c012001800450f4a10019041e200885412030749845115485541080003c0d070340c00f0046070710f45510807030f40b2200d13001d16070307108030700003014044602c540d00005d47c0c480d00d0b4810485030100c000341c45001d440c803e8040b200940b014462180d9055560352444d41d40741200300e0141610264913010 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 481318714 1250 481317464 481317469
    0x190507031803170c0a0c0e0907170604030813060501030501060501020f2d12180901050418020909010617240c0a1b051905010b0f09040b041a0a090c05 66
    0x18006690b001504410600d0f10000301c410254800700c02d01d500c51080d100010001850b090304035010b4034000d604161982402c2c521280b41800580003450502051f4807001411000002c1d5251712581500c0c00944649520240900750001007001510850401001009000054100301c0455100b80d0031151070718940c3c9000d589946140c108400e468003000f03418091000c5078a69420a191a41c0544004212441c02ca001340d0b44031541e80d20502c8892000ca00d41c0d1300d401c500d014014034041ea02406518002d51410401c092038402c0284104110b0000c5560280254003400180003203510310b4407500c01040c2d03403030381c0c414030784d020b40601915407901040608189084c0600401140c00000d00b0420758802c285c60007900c40040e4801a4010a01c0300c000c070b40e0402081c4006014091000b0700d0001c1d905003c2d09444142c88841c2c0590203231500100e01e82c0300d59007010703880b58014903409455112454103900b0031841070182f4000c6a5014180854402c2702e070b200c1c0384020f101e150407202c166901c4c020b = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 481319964 1250 481318714 481318757
    0x1060e01020a12170f15010c0201080a05071101061410090303091205150703050411030c030a0303020c0f0d050d0e0a0804060815060f0d0b040501030c15020319050703 73
    0x1580e0050304102c44180004103c0c452003940030520f07007032215014004402803500c0080844000003180710300f03014800403d02011024841603001e20b00988000e581381c0000c0c1c401400509480d040d60f41d00c500142485102e40e1006030601641c40080c042d07207950380781c028180a844895030f031040b0094107a0300b04480c0070740b03650000c80e68103441d00c84116117403103404210b0804030141a900e901801a10035540b150b039141da01d00c951300c9510005078030300701401d00010340e06001c0d10301c034006e1b48070124040981d600010407024003a41840c01680d44c0d004064241e05121022a54805030310400e00ca0f0b500840d0001d014044000c1356040410401d1050220f255a6011410010384003c000308030038000e151003640115030203001c1810002e03120b6014408198070307038031030740390800321240c041924807120282c3c0c0100340013801c0840d8244410f504548070715158440d03d1080100101c40100f40c140114028825140c07050f011003070700966404d0914020b0241c0d404400220b0004410141d1002150304410 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 481321214 1250 481319964 481319987
    0x1209060e16170705060d090b01121a040308060d050a050f0303190b090c0a0302070b15010f030608060a02070c0b030a051e15041d0a06090311060408120601030209130b01080106 77
    0x18010450f00d45024103202c3c1540c0000141002c8680b689030b041d003c14000141203000b01000500d40254a5030b0f401d02044030013046c0c044001003107011003800701082e48915855082075048441d9440d002c3d4920704549801c5a0900c020168000c822146900400100280d8072038040529090308018104000600300c1e04c00c0712800e5403188060b80810be41c1e02440307020b051303106814100141b030400991214030401c88100c90840c2c00c0d0690015034121541d0055030364100903800e00701030002c2c50034042029203a0304010100603075190301203600814008804003010051225643c2c40b981e82c18410240ca000d004121002c1402c4065000862003180300d51030220311848502d03414960f030310b02e1074003000050183c07d40200803030484101c0c034550104d400d2145040e054840c0c040020307101603518001c3c05100c42089000c0091308110200008100282d0440ea0090b001c22094285541c40d680141c000f801640c40064100c1100300413028010260f901c600d04050098882c403150340e0340c44008803036100aa1 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 481322464 1250 481321214 481321259
    0x1e0610050a0602031e070f0f1401150b2b0203010807170a06151706040b10080706081e01090e0c060f040b1602040c050a030e030909071209060e16 64
    0xc02c44c8058030171004210103a1500d00100140c0340c1030007034648075031280c03070a05c041c0e541514020444080003a401e1100c010165220000d110f80b1041001c0d52400440c2c0380305200001c800010210714902000300030955103501441038035034034846580014002d400034042c000d8a4883e2080105010b03a001000981038500d0000034001c04a140d641c030009403e401c2c03030060405401200100d0700d203440b842d041e210040c25a0040005103081e08141300007000140082403584500e031018481c8410204480c016150f1608010241d91184c50003692100b0308544120070407507a0700b0012915a000c0d41280c42c404103124100e48103004010704203c11032040c049043c40000c2d040104108082e1508040c10081140b0015020102c00640100301030342d0036000310900180700080d180d030b00d080c3c0612034007500000c4c0704020360600c14440049800f103400a000c51081c88910702039504480070310342281441580c4544184003607036001c0a410340d1500305030060b0750b400305c0ac900041a0f44401c5000c4440e00c0c003d8 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 481323714 1250 481322464 481322467
    0x406030b01050d02040b1e090c13060c1110090e070315050f03120d0209090a0e0a020409050f0a0605100b1806031f030c0302040501080118141e0610050a060203 70
    0xc20b42000300b14040150102c0c0c000307031107072690107281e42c440300140300b64001440c010200c50303840000c2000010300202810040c1c602440f00c3c941c3c600225078808191240c1d030411310425103440c100740e07241101041e42c0503442001c600701486030f2540b25241400715a030400e02303a0003a840c0c900f0250103a90b4000f081d080c5856049130100150b245c5219490754020000c0d09503051407c112040c00344a621135003c5040254000420f4040360415524459001e0310503281080480002c801303207512540785204c043e00c5241c486940d1818005c05000940301ca10820084846a4031146001c1c000b4120443d604c203803884d1501c00001d09101c1e400e048034580b440c513a41d18002c2e5100c003c20041e030f681029043c089000c0741c00c00032442911050391140003444c0149444006103285204100c2a10740507005454541d040141041080240304070840d211644141703031407040440c8400c018a41070428903103c03039005403102c0da61508039000c0f8115000f84603208494110a445400384076140e2414403030355005a10 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 481324964 1250 481323714 481323719
    0xf11030915030a0e011a0a0807080606131b0f0f21051806040f05060a0c0516140318040b090603030316120e030a020106090509030a1d060705070e060406030b01 70
    0x80702001140e100115100c00100803602c90700c46821158180c40c1840c200480000981184ca090f03031805004164240003404040d08121a02d43c4458000d400c0034060401113540e54840440c41d004120803034002008441006620784005141e02d00c0d4032180c40203c1d411000e04000359200713900c5640302c050011080c0c0040c0701032280300e0000304001810540851b2504110b44070380d003004d00065018070300910300c0c1401e60b070340c03401c1882c200f84000e004000010f1034800018032054002054511000040284403401251401c050001c0c03c842c01844240c1e020008020138119a803052009500c1c100b41ca003042060524410301400400540740340303500d9481480016400c102e807194a103800301031450005140c821695034030091740c403801240002c07031304081580d084540e82445040018100c054082c040b90a00c0003034903449118ac1c14080042003507404842071081c0c8180343c00100424040d040f69a03d80e041c6c05d22540b58025070080c480c140c0c602d000890541c0c40e06000710710540ba044000690981d2 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 481326214 1250 481324964 481324999
    0x6050a050715060b12010e010f060e03150711010e030403020108041506030f0f03020c01090510050a23031e0c04050913050609010e07120b070e0105040305010c0f110309 74
    0x400120341207079010b08400d11502441e4032401001c00512003820324948030f01c003088100103108030513086044903488a40040041c80e80380e045200c03c075042402d100c0703004d500b0103020034207040c03051807003104110408050000c015844156065103004081c0200f00e0754003c0b2001c2ca4803889984800b0780000c00c02e43c045408220352901070004500380e4200017910950740d554400280c80c4110f8145d0f0702c051260900018150140f06008001e0350900c1c01540990902000840c00c0c040041c080c000c00c040890404903e9014103100c042d2240720301040e0341d243c001401c052003580e00844200a40030320003d182084200d00b80346050190703410064541c1090304000074403441d468010250044503084c001a103000c01c1082c44094014040c3c0800440c4200d5010811340c94003c40340c0c02030101d0003082e404400030942c1c610090790411050303d0b1103043c0c0e07004400100c0f201d0040e90000b030860b52030000600c001940000d4050008055a1204901021510800342d203d010300d903d202e40110f5074100f01244030 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 481327464 1250 481326214 481326217
    0x1230103020f06250b151503091005040f030221070b070e060d0606270902030714160605010504050c0a0f020102131202030f0703051902010201021b01090c080706050a05 74
    0xa40c0b015003c5801c1c0326641c242c000207000320107481c0040c00b6504142c2403d0064240a1642c0710940d010111721407880203000c039111020300818500100408008640c00351014004000746410001042c4914185030914001400303030128100d0140c0b06544510402001c3c42c240c08091441c003c90b00ea080201e5500c0710389840d00002c4c032440c00c00c05102c000541d550b813240c0150036600c290740340015426040c00d03030140200c00a2002c0890404e4961040a01113083c80d00700001c0d1201b840c4096166154100207a070310040c2071040d441000000304821040c2d0051081c03844610307008040602169030781300c05002c11980141c0b40c129034810104003440c0d05601565482d21075550f244001850708820180420b8a0b81c429001150300c503040c00c20030410f41ca02000016041c00ca41c80241c10101d05e5956159682c4002c0903014980641581c1c180055a0003076043e80d90159040c003100d80103c1c0803090850080400f80b41c210380201035904081242c4000113152801c1e11400c0e2961072501414510981c0e0702e = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 481328714 1250 481327464 481327489
    0x605010903061509020d0b04050a02161103070806090a03030b06130b0913050a0b0307090e0303013c05010f0f14220801020909070509090c0f070b090f0123010302 71
    0x14503c100340004540030b8070b20050040f80d11040f40040d840c04a00100000d4510107420014500e006000803280100660100301406500c01000700c054a03120020034100361040c0e00030001d5020380c2d800c103c8400c0740413902981082c0709503002c0012030203000810102e0b008900d442c0c101e4a40e40321040c08114994001070140440c0149107031003d503003525a000c190b62007295054101a203801032030049090410221028125a860a2085075442184d003a941e00051140e00403960480a500e410078402040c40040350021000360b0003008070076200b0140c8500103108040c0020340078200398940c0391088118410419041e5150050725010039926660f5400c007041204003200c4251040981c00d201e42103540041602c07400158030342407000f0800403c030100400003030038040e003000601c40c40c0d0b0319034102c45e500403950500d00340c07104441103501c40940074401d40103114a280b9030034400c02500000c0c0207a50044500020700499058a0300c5200c8443d58040980b561003107040144011f00d003004480c4c40 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 481329964 1250 481328714 481328741
    0x302030a0b090412020f010b0609060f0706020d1a090f07050a0203220504140114041a06071a1305060604050901020705072c04053a0e040f060501090306 67
    0xd01c80c1d64400060382e0524255011552404c400d9003080d12140c0600c22981003405160080003044070b0f50000c5407182c410107020b2803140b140095041c0f240f550700816150455003100045440e101d0045403400102007454000c50060725401441129141010280b4803580c41442403020036190840d00350307160340116015a055000512a50241300d0700c12a15004c050322041201401c2c500d080107010445901c84420f030764a1002d400140325003826402141e00100042d1000240c85103400300c444043ea0350380142580c0507034002000c0b0184040c10009151480c102100840617882d800c2d02c148401e003200c034006105800c0032000900500d010391007540d100c20b01c0300000d490450180c0d05ca60a00017079400041c481d031140d90007c4254034100c01340d50240404d144400c106802d150711401d6681d008903403441030b0a2548400c00102450501b6098a0340950780820000c5034102840901021580609540907134607129031500f88035198060f150844a040c0c650101490940e26041c0c0a84022000301c1c5 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 481331214 1250 481329964 481329971
    0xe0a09081605070b0a03060e0601030e030703080405100504060c200a0201030e0a050f1005011d010e070905060d0c03050a14070804080f041404181709040b130207050f0604050a02010302030a 83
    0xd450012800100110031440d600000c50b070b402d0238042d50144401912460406203004038200346000008200c8480d941c00d0706000320f840d503c42ca0418500000240d40208040c01c00042c401002025081400d801c4095180e8904e001c40c00c441c1e080c04101061740801c5554080c0c620038025500980c400001320704980242c8060544646465242c4070100120403401d501500440d4040c201d144200f50243c0034070505140603108000801c450200180901c1810b01000c10109080e1801800c02c4402040040c04140c3c0f40c0b600e0012200c020300c021088600402c0c140000180740c09614464900c1076010303e1202101c9485850003140c1d110001002190551000c20590040956240c0500005d01b041244d072440c10300035405004c2039603c0441d0b41100050f00640b00c1001400602c4d0020307a107008500d445485400600024021380307940c21403280c010418981b51440b403d01c0d9001040ca10303010b1400c4940080300c95401c0d50f0381d0902150302034002e400c416580c1e40150711a800441d0800d02048010 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 481332464 1250 481331214 481331219
    0x30112110907020601080613020a0314190b0709210f032d0909051b030a0b0d300816090e13020109081f0f1103040c0e0a0908160507 58
    0x312101800d850302e20160b400301004000354071003040419031001c10080d1440c0035403031960124031420740f28000108030a004191082402da0204050503a090403045280484030700c45c14400781c810701c1a520341d00051314150021a00d40d0f021805044200e12070442c0c02c00c4192143c5074419030312400042201008292129104203020b04144440010108101c07180c04c441c05600140558202d9807061052038101020007280c2d0600703010004a01640081c126078942d181d04a07074009210f000000750380700078806199028402c3d65040001d000b00b005140c0030024040341007151140034850461070019500200144440d080c84a11841401c401c0c10100d0700940ca503032409a00c13440468074441002402d103002800d542c2d006801034020050b04002d0005100008140c803203c1c4030069112a10640780c24a11100740c5a50340f0403005500c07154031a680345c3c04c151504c3d40304002a0f01c1100103080b9101c001c2120000148941c007103d03580b010ba21458a158900680001d015414085c1e6441c040e20500 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 481333714 1250 481332464 481332469
    0xe01020c09100e10061b030f0c080c01020a050c012406030c090504090f0302011103090a0807020310110711060a090509090a060c0302090103060f06080619080d0e01020c0904030503011211 82
    0x720f9000d400e00e003030000912030400c0307001130a182180f002c400e010700c410304540780401d40040c01c02c0c0415000c0e00d00b00600fa40541010040e0703114010081d40e00e50710004454080c543e2003c003504082e05441d0082c051020b0810400340c01c0041741c0310901410840600c04c12060340241d201800402c194200441540d580d07500080c103d891407a0180c5544007071100c401c04159080c400c1c505c03400c1510800700d045081407030886a44011482000300303a11030000d01582550380030024401c4408174400e00303200050249412400c0398016040c1250850304031400300034180b815005481c030701d541a540d5000102c0c41c001c2001003000c3c01a2100c540c500800c03244001048460144c03481d04c0780340d41c070090782c0e48404d400018100c1e0026842417030701c01c11001c000d00c40194440b84e200c0d048281140c4007400300386a20829643c030301069224004d640b0070b4007502001d03550028000b0b105200240c0070381c1d840fa10480c1c1884422401250001c0000d04c00300010f21040c00400c81c000640341c000c0c02c4501011590901 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 481334964 1250 481333714 481333739
    0xc270301060b0712090b0316031407021509060906070c2102030a181404021c0c090f0801200d090510060e0105060a02030d0f0e0d03060303030c0e01020c0910 69
    0x1146040b48006010801c0c0302c88103409644003000c9260080c0064a803414902e0180400f03404640c07200c030b0200b0012245480398000d1440701c018543d402d0300906080401950b100e400c080000da01000080015604001c00304003248101c64000282416682c0c1340c1d0100c803184070301c0c1e00c121114064052501c1590340c0440240c103140300c1c241c000b1541d540c2d0b4140013030300034900c1815416002040881c00d22401401070709900b207020f01501c01580303035074080108081e014482d11b241d40b20f6500d0504d1210100b41c2c8040b41c40d04407084c00c250031000a88615106080e22041c040141c08059607490205941007904010412070700c800f03500140b003010740d5907642c1c1880843c101c0c03030810302c0e02c844061000c522032070556401010300b10f980b03a19002003490003a450340150080c8051403540c418911500800780d03046408107440d62029500e50b5050910090014001804185c0c000b80c03401541c40c0006011711208180508140c0080c6a0300b920030040042040c4014460b2085010580c0001442c1e01c10700c0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 481336214 1250 481334964 481334969
    0x5010f11030a180503010903020307020402030402060408030d0f05070806030a02090712062706030b0711010902040c031a030d0c08031806091e03070206030c21130c0803030c27030106 80
    0x1e0703803e50103501046519841032466046244a83d00d00001c01c00000d40001c00c0781d10703144c2d040e20b0150302c0703664900000d145400f4503031140055000000e00401c0c2110141c0c0700c44600041040200116100c0700e00031503e5410445080380c0681c4140c0508015280c0515038561004c10b40ca090a01c0c1880d402d000410b0b1000e40c3d2000500e00c02d17841d01020822802401e07c2e0810707958820401c2201e01c0c544800411100c0038100506100e807482400f40201d00039040b0302140394011308240300c00c01c4030745001002482e00c44141c0700d81c00c00c4401160441d26000c12242c2c1c00c0581560750042444013515562115403014102405980110703200448920060114601c10303a444c4002d083c07101082080ca5a0410300b412501020ba0810001000142d0760038098940100f0a5800c82c0e071030307c0c40e18150080300c40c0f1032100000e003042c0c90b20405c51a428621a0480c80030310900c018807903507540d030740b900d03907203000580344441004000c0c8080c1d02c0c141c8403141000086401c9481c01040e1081400109084841030b4 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 481337464 1250 481336214 481336217
    0x1e0e04091b0503100218011809020a0507031815050d0f05090f15010f0909141e1501300c090c0e0d1203021305150d05180705010f11030a 60
    0x70304108101e1030107001e0403501d642c14020543c50b22514444403682e40756001d001c3d605000d900040c8440b9008040e1058024180b0000210f40c2d461042e080070340650030480307080300084c4a07c040b143e03403041000c21600882d40c9a1020013030481d41040e051b201b80c0c114202000c0c1c00c075079881c94010f0014490251a004100f500042e00460720b400380c450381004030707240f2071000010301a4010450380764403910720f4046514401000507a00d019140640fa00c09a29030902c81074401d02081c400d03810700400001090a4881e002c41c0c03210040c0201ea580c80070024481c0082e902084609001f504c0c490002c3c0c120310880c4034146044200c0d041d0f842c3d0801c42c4881e00041006a03480b005042ca46400820300c0e440c404003103600b0200c5030000d40c3c4195680207003943c07007000c064020940d04060107151480300040d00d4001c0c02030700d002001400e119095080074a03416103031800c1001040e100c0ca0034007500348026640c0c8015040b400d00b01001034800d425284603500c2004000c121000c40d138a418009062501c102c0d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 481338714 1250 481337464 481337513
    0xc080705181e04052d0c0705100b0f1c0807170f0d061d04120207321c0b090a020607120e0a080d03050a09080a0216061e0e0409 56
    0x9403810b000c21210700802071a181c0308111014000d56a5651005e1140c42106603240348594444070284030030700074850000d0441c4a0741d50b22141d0400b60b5002840078540c1601d0b81a0203036000d10400c10900046a000c03944407040394001000f1404280040103154000d06841c9058880c903910642107a00000e43c1c8124081c001c41c1e200001402030040c8801489540145070400964500520030303024050f01c020300c0981e0703907501490114000d11910000381b04100301c6024604005007401c103c3c11403060f615540225160b5603603030620308400f80c038046200d04422800c580750281d4401241810240c03000e02d2a100d0344903090016602c440042040902c00c109c0c248899003503c0b0003a1042c00203284c8140b0814561000b80710514001501814441180c40c0116450b01ca07a94004020b16010001410560002409180c00e0fa0005454100c04804480e480c11050ba07404c0112030b200c0d0503a01c0b140100402a040c060464410003e66070640c4000b0030004810f280740c4c1c0c42c005002500a500304490f800d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 481339964 1250 481338714 481338769
    0x20a051c060f111206010c051204030c24050c0a02031e0c012c011b03050309100902010917011d1006050301020c2d0105010905060a0501030c08070518 66
    0x100e020321020700614640c103010058443c00d000d04180a101c440d502002800f00000751aa84145505441d40340c00c84281d0700f04158105110025a1013804241e03008524081c000039084031040e00782600146209480c8005800107004582560020303000c40030501c02d0020303038809680e003403268490100701c8404500b21480715000d214100100030584a040c09001040319281018640c00500e01040e041504112442e0010042c0c401d014484900039074503419202010070550088010343c0a00448401c0703a9030300c2200c22003a030644d108003000900060072940d0811400200e000e01c1c0c4443d4803140000b14008075403141e815800a04c203800180150b00044203004004404e00c6988080d1009900a504d0020148259551041100140320742d880e169070600704510f42c0b1070000209460700b01c00a01072541d555004d00007804082e6040c0303118038140c01c40011258001d108842c014001c50b15084082d640d0740307001ba183d03500040c00f0021542054146401c450b5550364009107a040c80010340d204445 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 481341214 1250 481339964 481339973
    0x1f200c040c0c02010806010503060a0f0b07050c03060103080712140703030f0e0c09010506031e0c091903020d030e0f1306090f06032022141f060804020a051c 69
    0x2103074540148148600d5490403005030342e0294029500804c28202240c0d25207030b0f400030846000f016030208072a800036560114502d04403034002c20301140903404a42601d002c1c1404c05440d04020301c001004a141008400002102d0244044041d1860309000b0700030552203248441319400641e04071b0000f50b85180c21180e4203100c0c894641c042c900c5800a22150b00300c00c0203d80740c042d06014061103804d0100c00160554003090a4103034580d5020743e900c449050412004040e5000041d07035a118038105460702c500c40004103007000c02c40350020700e0010040c0b00341d201074408141c1100c40b1038001c8002c40c0b0608031600c0d000070074800c0303c0c0d140c4000a04141b0703040401c3d0031100c00b600041e06c1141085810004254004000300300d804442001c81c60803200b0300700266101140c10403042c0c804150f1141c1010300961948030200c00e140719500f2820719641e40c0c0544d4500700070700141c0341004421030410f226480c0310b140103507030140c40070b458030140680741c0c0e0004481500d04204d805040c0362000c545070400 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 481342464 1250 481341214 481341221
    0x2406140a080705010f0c080d1103010314010515010c0219120c05040204060509011101140a0903110f0319020a06020c061b07081213021f0e010e1f200c04 67
    0x285005009440380c14140f0000030000240e4001540c20480c191000b1030600624800b00c034032080801d0710070030144040c82c0c60f1501b203410034841940c204c041600e0300a080c0106014031881031441d038103034104440c403501c0159081c000010b81642c10414610307112100c00c0c1820401805082c140c03071603040e40c06040c074207a034020446800c03142c01b450046c0410000c054010090302d0010742c0900b40300840d00440406a40100704a4200344024103009017801410500f030780c0064550f0703000b0380c1c5120096005072041566109002410340841c0c1c410001c104186400e0413258030085034600c140c1d60740406c5502e49100b42d80101f041c80300542c01070030501c0621805900c036411b03010154840710b4142001901d40c2c00c082c1c0603030210351640001040c00561071a4100342c5803003811754002c1c048401d50b2842107a0034101c136448802c2c100826200d50b007800d002c0d0f004040700400880d00074160f00c0524503024074001084000900b803818003180c40e828518110f0b01011204520031440001c004000003402080250b = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 481343714 1250 481342464 481342469
    0x105070f020307050c012a140d0e030601050405280213060c0b0612070305030c0303071b081c0f020d0b030c120705040c050c0703030e100c05033103050102030a2301032406140a 77
    0x6103c0403010b4041c070bc4e2004280a030444d01c0440b00002c07543c1d00d99040e4404009104075410b4042002c191400e083c10050340a044403454507413000200c141c650f034003a242246007420107441030300361000203482850240c10601000352a4419501e05135940e50303070a440c5030420040040c00d81c0011041041160744400240e20010304030240c0108880305840c0d06c006031107121409500c245c1a60203080960301030b034010005c0c49400e65011135507901608075000003080d01418661107030203203911407019460328607240b11012a843c0e010b85003240c5003108010040c610040314105100040c0082c1c820040240710f50320041d0301136191080100b100320f0800c20500b044082d904140134000b910b20000c500d0000c1900c880b80c44594840e182070200c002000038090000742002104032102d030001c02002010b4019600501a0305414010040c8184015590861104480d14050802070040012510b41007000d40540c44405109510900c80302d00203040d1040ba4101c5213540408000c0c5402a080c81c210740b000 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 481344964 1250 481343714 481343717
    0xd0204060509122404020d150e0d0e0102102016030e060a050a030c0905060408010e011a01020a0807080d0903050c0c030a0c1401200105070f020307050c012a140d 71
    0x78526a41c540760340c4ca007440f0307900c840701002c190004085481e1004851036064000c44000d041d2811500540050405605041d4140c010740079000d54071405000004071849c1d058000d00701d60103014003880b00030035003110818400c034940d149040002100c00c0c010544044060282c0300c946a803810050240ea10304907816006400c104051201700c7d83c40400c0c0ca5032101c844c03401190041d2200002c4503081516002140d2001000600003109101580b005881100c0c4400a2217041d0050321270040b600410164a40541c000400500c0060b200d80300034240306115425090500c11402d54503070490301e04080440104000142c0480000401c008000340c8001c100c001f00140140d603610030008034003600c944032402d00c0042d040d0002d07038080c000184450101032910b661144005140c0f5019103002e0300d41201052506006501907131003c400c40b005150071400901d6500264030044402408103000c45200c0052410210344000701d41c1081103907240a2a0550700c06070109003070070f040c103036034006c40c10 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 481346214 1250 481344964 481344973
    0xa080705042106021c06090b0909071e080f06150d05100209060f030a150b131406190815040209030a1211060907030510061212050d020406050912 64
    0x4604103040d0304415414041c1600355040700c2440c0b43c914040c0c010044102c00c0b003203650500c00c09040550784117804aa9400c5d40c18420044e81000340000f180040d1210a010303040903d00b84a0f20003032001c49040d890515481d9180107590f14841401c00e500d80d0303007407441034100c02c0c02e00c00310300d03081903091150200448210034108510755409550350a0780c41c004091039004a8521200c0d41c810302621301a0010060180d5240f0f003e0302a1002801038810390030f050f9813040c20110300241600c0a40d90718004100c28084400c0c01c14403400e201d03c410b030030708a920002c10050300c2c440f4600402e10040041054803403800c40c4c1000c1d04420b443c45003810025000b00c2c41480400196500080c802240a8100307207c80140860002c0c201c030080b0391950180090b102d04e00a0001d003210011300c520499000300c2c1a43d9040b41c40c03180040035903420b0701c110008000c016900b080400d6540095400c683c140c1d040092401c1e4902c0102001e9801a504c0a00403800101d003546031030400b502e001004810400250 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 481347464 1250 481346214 481346219
    0x903030f020f07030c0c1e1701090203060403031a0a03110103060b0c0318040e030310031101020106060804021c0c0807090b040204030804170f031b010f0b030309010c0c0512030a08070504 82
    0x341d0300380a03d0502404004140800009000003251000017401c1c0d0710400c04030030807810b003002c02101201e108400006441c2d0300d588900d0f08042c429115a1580100508129152500c0c00c5002d1304c6055041e464243c0001e80c00303c41a501c0800ca84002c40c451145100c01070b502d03034009070486605a005030030110381003080400074400441103a5813104001000c48407aa1000c0c00700d0014903520841c3e001602c00041803010000000b01b0083c00c80784940d21a00185103400c0049003030700c003144202d802003a0103a012900502d03001c900c9411542c200701c01c0c10075102c000e4a0390a5000f03450f501c0410107070482d00e0141701400a81c042d01c2d059503000d440662409146a68440c0984624803509010300b202c218940040d85007400070750005104102240d03107407088000d0300d460b040559100750700b040d0320342007000a0400d0203000301600000014040d500b0003415a00542d13038518048412135900049080215032643c544124a9408090741d0080d030300c032101948060610040945090203012050104 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 481348714 1250 481347464 481347487
    0x3030209181f180e030705010c271a07081204031d060f0d110408070e010e180c0f040f0e0c012a0303020f0909041401050604021810110a060903030f02 66
    0x2000b421980080001d03e03131043c0d2401c40c00d5014102c0014080d50800c2041044140c1c0180c1e183c0d800b030b1180010034120483c440205814505600c104005a12000444200a0b0000026005c92406949418039003101c40194240402007110100d010505540000c441d84c1c1142408510311340098031701516111484007441c6403809000a520121030b1292807c1541807200d40c20740340244800c1c0704450300c0e5500d9140b0300c280c02d6800d00a03000c0c500100800111100240303a410b0001540d103001a040b20901a03091000c3d4140700404540c0241c2c41d5010030004c81c4c41881810010440007014106010044000502050742d4040400e5070199200e040a820300000003034441c0746505003801039440b10b00c40c444003928000d440b40d003680700c402c2c00700701f000f40000c0304080341e40c00074080000c00c02683c980d0204030480c003442d80704042c40110310714058210f08140a01c54441c1c0c07214109009180c41000c0c8141c0380c100022021104e9a4440c0304290070583c02d80542c490140243c003080d8100280c5418 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 481349964 1250 481348714 481348739
    0x60109120b0f070c08091c0203031c05150d020d06020405120708011103010620070b04080a150c1704051011130905010501080a091401050106111203060105070f03030209181f 76
    0x80c6c61050028042d5044040c80c0c0311031b0302d19090b078041c0542781c4070030340280030420103061404020541800c1000040f110100fa0800315044c80c0c00414924140e012902440500c03a0240000c0703032403950800c03009c00d65581c2d068001741d00d007140c10010804a814241c80e6425101446203c5107250000e00040c41010b0700718296680c0d1509000c41044404281902d240c98220303168008030298070300090104180354003044801126009210150035582554400030841c0c2e090000310000074080b824140c411a210021290410f0281d403c4840d01f06907103499504030340c5045001d1075010750004581142840a05140005291a031810040d0750716060010b0f00c4503200528040c021940c034444c400402044400c10009401080020005580c580700c0141008144490ac6c098a10803002d210101250705001c0700d04c28041030351200e04105031541c805505940107402141815001c1c0049586901c90000880c00300000c002c582c0103601746030008c0100014480941030741c1804034802071040d001d5240 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 481351214 1250 481349964 481349977
    0x5010e0307150203010e040305031f060e0906010801180b060c10230f011206150605040f0b0f07020616051207021002060402030a1202010b090c0304050c09040c0b03060109120b0f070c08 81
    0x1c022b40c1d07076910038403401a0052004000051512107041c0401e02c2984140701184500d0141c881c0070240e2110401500c41107424850002182000350740050700307403602e82112503600c1c009445142000d141c0b19481d0b003001180500150680d03a1034290030780d100401d030202c07011940840d10801c49070600100e041c0c48403805019890740e860b46250b824040148503402189024984241c9100550300c0700e800611940c85489105220010302e100456040704103421610403001c580d6016241815075030074025250080080f10600c64500d404400218006120340c054203141100503913034a8443e4410002e00d240c52480c458210360040080200584002a4890445410203424440508802d004901416031072001c0c42c2c01c1104d040900c568251160045d41c010b610a50944a100e00700f0814440010b00c1101c0c0940011070f8100c041000c5001c43c402550800030614055401c0350302c0d070b07980701154116401d0458100640c4802c110145042c403920355004181c0e40f03405403401c050340d150100c00d4040c05 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 481352464 1250 481351214 481351217
    0x1b3f180807030305270d0e030c0d0f0602040f0b0a020d030c0f0e121b1305061302070c270c09060e04020f16030804050c310905010e0307150203010e0403 67
    0x1310701041c0c1802c50303c50003520301440c40070010071001140b0201038546500551010120303178242109130031403402180902c940b1001502c01d468040464075541c011154000040c0d0301c1c030764200000f040240c0441540c5014007580f40c2159a908800e07040240780110742041c0104052400101610990f031210003c10400410b107401d4100c4450b1500045c0d40c2008444090361901c2903801507084962075803800340c40304801310703030040e030464200c071088003921403c503013507684031460784000400c3c03a050b6070140860078003d5610100c8103843d44a000741c010002307101480c3d002c1e880d441000081c052409205541a00c5140404600745048000790078040d600d1000c0e44035a40101e803256240f8002d200760348080000c10001070080425050242400a00761010307240b501900444240c1030820340d01c1c0d0012202aaa03c803035a01c00707800d5256030f003c60b203104448109a2961203c1380494030074051550010803210141d45c1d5403209107000201e480e22914503c52240c01840104000c080300710490354000e130103 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 481353714 1250 481352464 481352471
    0x8060c0307171024090f050306010e0a0b090103150c02010b010822050d03020c121c0c03090b04080c0c120c0d03090b0f030f060102011b3f1808070303 66
    0x2140d41d8225002010b13004251101c5400e0402581004005503c519100064440c14525900c0d004a101a4500c0d405000d4040e8042401001401d04414000e80c0c4820900c000240521040002950b401000e0703009490001041c1d1090b00d11080601c16403851400c540020441204000300207801c040d0000c118085213060010403c060b6880c2ea00401e03c010f60041c10b48030107006039034000d402034200351a80c00c118401c0420504d0076075294411948280309598481d8000f100e0116681d0250802ca50070700c0030903889050920015a180800c28011403142c080740da00c0e4040401568904606484110302c1202600000d0400003000b045002d0710000030345201d91044403508003071301d400b81c01c3c0c0c0c810352142c54000344542404003200c0255001d49030413486950300e0b460702d00c012800d0385d01c0e02c6002101403224118a60000e8060340e03c0c3c00c00d0348003040c034680300303140c04280c044c514510402c1400c9002a00300b81880405041d0b02c581000e16040200c1098508241c1d20b4100032400ba044004042c9581d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 481354964 1250 481353714 481353721
    0xf02071a13033203011d04260f0c0c04150b0906070305091905040b0d02090f06030715030603050705010507030f080c070807031d01140a1b06060602060108060c030717 73
    0x72000700201c003044500760018032103148070210007060362091056010301c851008401c24484841046d075402160007030036101c11121801d46024042d0514007912080e90783c104240915000d8400c0034021444000020307080c02c80c0c1801c18002500c140700007c402c0050450828030450400c181a1010b080c1c0542c4d190b610761040d49002c0d00c0f02c2c45211841075110141d01e820701c117816500e600550960310251028000c20800c40d050024803001c0c500c00940c40001d4200203089100140521030780325100900b1213500c0c0c3c4e41e5166060210301401203001c00651a28018001d02004100341002000203192092a155040c3c0b0f0081c00b26402680d407108100d0321101003071841c11070000380d40d0713019042000d1a541d21818a80a070085500307890301e5201c0000000c0a900542c0260f04041d060400040c44a29200c17500c141100d03804081d40f000441e80b20080c64603400301c2e10300d201d040003a2105400411035541030400e01c0c8c2c50240001c1141c0041740c0e081040040090740900101210400041103039010348 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 481356214 1250 481354964 481354997
    0x80d0204080708070305011a0105040302042f0705070b0702090609180304090608010c020f071404060e0a0b0901080303191d0109030e0a0b2106060c010f02071a1303 72
    0x315a41c0405000c0c4522400428a800301089000403a80700700001c104002a4045404954803c13010791030104005100810250605411025503110303000b04441d44250681c850707060b00842030481910405022441c001048001c1190382c0c003414005805d607062158581c0051042c482c010946800b03a401403002c901c038000484510a02d0340f551b0800c1d00d450369280d00505e40100503034401c80e5195030804c4c075185485400411141c286941e19000340103a41d05140609490743e090f080c100741c2017581d580b8000b511041e00d03184180164180f40700410b030658124208004003c06800065140d0001c0042c48003060201120342084a925000401d8442c500754080e0034502d440450b12100e5403d0400040405034003001900130300908848032400d450f00e902801c04507014044003443c1603d00c0c1400646541041410f00c1d6100300014035003450012001c0c1850300b03440d00c2d101c240071440d40104407102000089408202207544c0e004040310a441c2120001c00d030303000c81308800703814000d11510f00304010 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 481357464 1250 481356214 481356217
    0x9060a09150801090b0a0f0c0206160e060d060f060503240a09051501020f07050a09110c0f07080c0103050412080712091a0a02030106121a090c090a090e0a080d02 71
    0x34003000001304103100640c180038100b2401207602404051600c85010016220345c807951a03040140c1d8002d103d603a513288240442d84042c160701c00d003484401c2e03014030500d540710401404484150003000c12858a000300c1c14003510034a402080507c101030041280c0f0380907924a4440c08114034041d240502c80c5c04001c01e50707116041d0070801e20941014104014142d15800700800f41ca070a900b242d6811044400c041c4d29020780303020b0164001020102001000d0701e90f00314404483c2072188035072611031003a400300c4c508100414680059001028204161181484801c2142c00203003020b101038074059a40f001012a15200001403040e098080707111544102c400384500146520100140182820142418450400d0300c3e08800ca2280000341c15640a0003602d04035401c03600c8001001c183c450207440a05050b0662a158003009030080342e0980c0d840071410f01039184840c1c0c250303407820038070240900200e2030703003110016a0400c12505c1c0070b5040041c40c2c0204a8005140503100c50710042010041d = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 481358714 1250 481357464 481357469
    0x30307031d09040609021206220501150806040303050a050c07080304050a02060c0c0406050d030e1c020d061b030b01050a0e0d060501030606060f09030f11010c06050f1509060a0915 79
    0xc1100b100400040011503070090440a008807a018001428200d01d00d90720401114051510000f50030403c1c07090701d081c130700b9510003413050001144004c2040d60054000c800d90b400240f2550002084c00185074040c0b00b12a0811402d000a1210340b501c06620040b41c400c03c10004c005040001c00034042c05014040142d130320340d00522984d40c0d00388400c1301d143d89000f900c410034811031421000148a1a241c1c401c4c02c40160300d9203400208004071420001405034480380000400e802903210700c0169a51200c441015200b00030001d525498050002019440305900c5414945001c001403074680e00201980c3c9016020324020301c01801120200c0d61015a02d000248540d0500c000442000b04a410800a0b14400c0e52190040c1c030741220704440c10f40c4c0500c03010701404103260440c00400e803c41c040b01c001c0ca806061202c3d9160842d079643c0101e84003100c88080e101180d0081c803203a420b008580c1c80300c103001120480a01d06040c03000a20300780161003408007645e5103807610f140c0c107141c0d40c141e03000 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 481359964 1250 481358714 481358719
    0x209040303180c06182313020c0120070302100f020405030a050c01030b0109030c06050a050c0a030f08090708030f0c070e010f0626070806060c010c0c12030209030307031d 75
    0x241c2d0301c15454214140030b018050b00c408515442d140c1081080c48070f205008444105030396041c03290304c000c2e5401c9540804000c0f650041c90702e0442410343d1000e40004c241c880e000c840001425140740a11060880c0c07503200003004200200091004658001000c5c3c280003921080054040c0080d90494028401ea40c400d40e05409410314070024448081605c68050000380c070184035420641004403000a80e0f070100500008540310706101c11840340c3c010b048004860b0915618040a44548034601400e89500b1000140b000b000e8800e2031b43c0c080700954200c82614010000c07681084039454030b0b03024101040d100901c0103c0d500354001e00c2003245100401085c42c00b4100c55860704001003040040703010b240041580c41e00d08000d1043d0751141708020907101102c000c099166100200c80c540d07800342c05907910000c24001c0b441c190100b8070903800c281a1390780700c09540001c00c2c50441d01031500b000030302003814814000d019258401201f1140380951628014a00040203601102900b2a4110141c2c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 481361214 1250 481359964 481360001
    0xa060c0306080a0c030506130c09020715051306060519170307020a08160609060c20211605011b140313061b020a05062109060403091202030303040209040303 69
    0xc040c003c00c1c0d034913802513a0180050311010360303030011050800d01110000170000b2440c2c030420450046154050600d0b1882000c0419a51955001340b9050b50b10640311800070510350070040c020843c25204002c01880150f0b00c040e01d50f5901d080c8182d0b42801d40c0711b13054429035000c0360355004032400d0040710262a4000d02e90303255a41c552a50603a00c85201c810040c0200410401083c0140500054070884149036107420100d4200e564034240c012911038035035804c0301c0480c40d21486c0c0ea0360805061582604140103034080d541080b20f20b1401c1c6100c00301558104d0141d00a01980e64040303079000030008040d4846035281c0a40c944910764102540b51007000d8000458088110050103211000b141d180e581c88914561100304480c0386003800c400000d40c461850306041106040100140041070038200c0c0d046854040719040c940e0a80040b84d60307040307541044c010001010741081000d4080c05500780c1404814040381c2c0482d980e880b001d00301134826a107040009013018802d400a40c0d40d0319044071a203 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 481362464 1250 481361214 481361233
    0x309060d020c071205030f0c010213060e03010c051206010503040f0f030c0215131a0706065a0302032d030a09030204020c0c150c010f0204080a060c030608 68
    0x344025004255481e41c20b006403400021100d862105034104950005c002d140380503000c0450304c00c40d41c01411200e00554080c0300401c4804a01042d0200900854555202c590503010405003125810307441d170803e0000501c101c1d4001a40c405a030790b80154207080c056030b2602d0340e003020510419100700061a411103580b4060806510607801da00e040e109494003084181c182d0562882801400e10130b2140b030704030240c100300318085d44419005a14070104050f161a0302511010155111904803050003810345035610034a021500c031004681c94904c00d003c44103079484000340c50300c00d04c58031000e0344018040b122040000c4003502d00340c0216030007000c03103103241840c0c00300c42c11060b12140304001d001d030b00d110030400842010040b64050386150b6100c01c07038641150b00700002034214941c0b56030301d40b007010101d03415030301d81c0800d0f5500c40b40d80728000303070300c039070220000d54252074100107048191401408100291600010390445003a0302c518045200c41c01503c08400500c2198844079052084a007039 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 481363714 1250 481362464 481362487
    0x7060204030f080a021c0e040b0a1716050d02010504090c090b0d0504141915140705072d020d050f190c090507090b0d0209061908070819020a02030906 66
    0x180400041a02607922110400c1c4103000c1c050601850385007c40e91f2203041004610b000c0e406041743c898000d003164040c0d42c4407205c03007041400032107a040c5d056010038a800c0e0300d940d10646540007010111050b20915041e680000e0550040d8810701060503212000c0d4413a83d4020390a0038054003900440c00d4403100201ca101001d0801a00c00340c5400d28910808107400c00003203420718044075001c0e03805010740f160381d80c0e801510070f0050000b100142d84200996101e250011000d000303141c1a1780301e41d00d5407440d00301549000e001c400000d455915502c1407069202c1e90700015440190100d9220183c0905410400c1c01c12924030344144c0f83d40601f1041001d882c00c9070181500c13a80c01884050034503521110003c088a200340d0786203001c01c80d403c1003044600070203c01000710b08d05001005d42006409804640190452201e002640c0440b14680395129841075400f0b901400d81e1400d8443c0b401c4c000110300e62140740780cd6100101e43c00148000519000304115902c80c24042c00c0c0c03d07030300d8003850340 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 481364964 1250 481363714 481363717
    0xc120f0702091023010c0804080c0307060201060315091b0b030a0f050c18210c130506011d1c0b0402040507230901110a030309031803031407060204030f08 68
    0x241244214004000f043d02e200003820300c0802d440c10300c40031442400021009140e040c2404a51034108101e4100f00b400040401001d04010211040200201514a4105403c042c1d45810000031a80350650401c0806c10f40607046c400440b1100f0002101195401c1002d4000b0720350740360102d500c206400c009101000300300258402c0f00c0c0034004101100c0703803809150542da01950a401c0d1048107000c95051482146080303148148002c281000500f481d900c3c01200115060f88914203400200c80810795003400e085424410528500c100308607e40740002800020702d10402e40074022003c4042e1003240c40c1c4035007190300d1036480200c0d01071940f220710b0614144c49040750201d00460605011500e0580a990050246203038a085140e01e1b000100c119013494204008032410030840d00c50002100c0400c1c03004022035406581c01240165003800c7c060000d541a00c0b85a4411410803810008203500001386441038042d0311407240d0b140700034103101c4080d0140c2e03000980000c40e803200351400c1003207410 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 481366214 1250 481364964 481364977
    0x1920060307022107081c0608070e010503060f010503150612012c0703050a140a08030717091b01031a0a181401060905040203070c140a0201140c03040b0c120f 69
    0x104031400c080300b40102061301941303134000d145213000e00001107180d00308080c0e09901c000d100000200b0b950759920083c5031060590110007803650600040c402800c0901140742d120144c1c1041105a51601d0b01180d501c1c141a407681e041d180200e80441c00070b654100b51204030540240c020300260b103004a424040021440f0304000b15078948110b9080d00700c02203000e50031245c000010344100e05844d00c1d03c00741c020039034000d2000c40c01091100c40c001405031f03020f0350250100380d8580040c4d1020f2074004184142c00340041060707510504880710b803144200c03146c0b200380301c2c00e18001c250752541e004658544942000780680c46040b1002c04564150010f000c1921540c010400348036144104840121861013809072000140d102c4006108a0078150011a00310a103840d0410440c21070b515603e2441d0204200032081c0c4e0400307240300056690000010320703d20b42150210780b60941030030701199240f01d180304504202d20041101c01c80c441061242e0100700e01c40480316a070340d80052000c92100d40c03004 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 481367464 1250 481366214 481366243
    0x10c021002011a09040803070507030306090501150e0a08060c0706060f1520060a0905160f090c0203030f06010f11030706050103060c0302091503150a090f060503192006030702 77
    0x183c1c01501528003185014000e941180c5042d18581f6680c504940315401b07280107406054503001d000800c90f0041c27240d01e0003041649051450010340510050401c4c15101c180f901c119440c110902c01d1002c0450312035081103241076099a15405481c08a020381404e034030001c0d194444180c00540c0d100303034242c503621000044c0d50340103300140e590140008805c00c02440c0b46540301d800000c210300f9460f03100d0000c1034010800c41340f2260701e401c22a50307070b0314080d000440a4205a8002c014080c00e60007480e0501c03640d80041c5007146082d00b502002280000c088504100da0709810500c102c0c0a003c03400c4a000c04041600d59451440c18003c7c0030700001c1c401295040e03c3d25858401c85842442520b0f03464030000d041040c21074124850039003c2c0c0010b8810b00180068401c011115524008000d00070300f403221012030150021401708040f100141e00280c041d03045440c40b5101e03400b900b10f449151f141d0019080e00300020314214100000d580380141e640100002041c803050913000100e021107007298 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 481368714 1250 481367464 481367501
    0x5150d1401050c2d250507050301060308030417040b07110109050405090309040e07050303040f05030d050306060d09110621090d020307080309120f031f0302060d0506010c02100201 79
    0x40c0c5085607110f100303c62070302d02644d01034812404812107a400610041c03820100850030254a042410149091001c403201808500c2c582801040000e1107428000d0101310020040d503840e680301c0c84000c3c8401040213100c3c0500d4601c41d40e03081d1011054502401c05003091030f803a80c032a0701c1c1017030110310229a000e0201d8500c1d14001000c0c0f0300390054921519000c0c0c0075508000300c040074403020301036034450742d501070240700000b04140d101000540028106480301c802050710303000a0504002c0d4000c101e0040040400c02c1011907112001100c0e00100c00b400000381c180120305002000f00601c2c0d45a40d8816000545001e000010b80d00e050f40c0101c200000ea4840d442e40d01c07480c1d80c0c50002000740e00160b0010f10261000c02c030300c080950341c0080c3c8002901e0302c209104044403141d074080340100040c0a004410f0014101c11030743c51402c1c1c1007900303910140060442c3c0020701240540511001420780702c06c0064400e07486441950103803036014001d02040c5000040203406072000c8000d4403520401c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 481369964 1250 481368714 481368721
    0x90301091e060f05010f090b030703140d080c2a160e01090b030604111207080303090f1b0d1203140c03150904120804050f0d020706080a021c05150d140105 68
    0x45511035036040754a03c00c243e501140c6441c1c1d0240c09801c6c2002300359414055002c000010801d0000d000030340c07040380c03800b030184075841810150400c0805824000d89080910450b05441c144c0b40451031391086d030900030b1032400d901c046420302d096102d120305462500d05820000e003815480003d035050b00e072045001c0c45694444014103995050454000c1e080c003441402c880c0c11800e05840e5020303400340300826160815109c3c1070b41c0f80ba42d4815560005598009148014001401e0200d28003108015580c420718000b14000110202418040504041e04220640d030446020703074000600346440c640011100d00c0c01c01c03800c0400c2e400c11907140c05508010b0303180d04104e24000300302d10310680d4044180718040d683c80c0403c0350700c404005c1045076103220b0f8450040c5000302c1004200c0d5040c1c07a07540100b600768240f00d8002d090003009047c0e68401d50040c007901603180261031005070703560a003040018617503581d1043c44178509902c402a941101d1410110000c0c8510459804841e100d103000034440d42d107 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 481371214 1250 481369964 481369991
    0x1119170c120a0f0e1801031106131403010e0a11041d061003020a0f1a0309030903120315120d030e010b060a03020301080712051c0210020a0c0c0524090301091e06 71
    0x48178101d080b40c1c0001c2410040c030000308202d00c41602407501504143c14100c440303580e95242c0c05150041049400302130303600fa03164682409035401c0c00c00c004010340042810b941c0e500c10f04d1005a1a064803842e2204040c00c040806110103000f542039000451b0001d04204081d569090b0240c0000d80c001c410850700881c4041c010704203541191103c2d070b404035601e20411201c407542d410103801500d035404200104442c65504202d001400d9034801c1036075590781005000b44000e1200407961074003412442d900e2402c2401d000c45c1c55050700406c0d003004210640e48980c1c17107005107441d86105912900101e0030340001c0c0e078540c0c0070398140d5034000200d1ba149074803090024402607014000800a5110341b54034070000c4040b6141c6051180180121005001060484016038104401240010384a800d28009001c4007051590080a01723030b0310461094030441440543c00c1e1110400b41c40160000b17840034060720250311031003800343c000401415032645040744180e0304a04250580c3c80a0810100c812402e = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 481372464 1250 481371214 481371229
    0x60207121206171209060930070506161b06030c020601080c030d050f1201090b090a0b0325080f01050f01091a01080c07121119170c120a0f0e 62
    0x210ba003c0d0040044a140728540800d540c40502c5854000109008844070780d1201e80694100c503400e400c8000c052030b40f0f00d107054016584680050f0183c0c0c0316001c1000702d81c64440c110703840300003280320342d803604040c034280042c400400061841121f86c88100000d5201c1d490b5100342100d1074294240c07240750341d99540190381e88255002c001c2d07168101000000e046401440105000038204502d00d052290b448802000501d09078000e050081e00d07007608950614148600c1c40e40030085840421480c00c10300c0102e0f0340d5949600c40b1008038444016121443c0c101803e4541c000c04240048500c00805a440240039140603180f03010610f004400120b100e51590180907890b1491005000f00081542c4c01100c00d0540640030422100b030401a803030101e0111044041000d21945505011005a00c84249803148281c0d0201c1d615034200b00030400070350500702c00221100c0001e111900c4c0c81c0c0d0700100505080c0c8003805040d4a0000041c070780306e21600151040e40c000541e450b44100580c4520902ca0300 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 481373714 1250 481372464 481372499
    0x103050303070f02160b120702030310090b060417010f06050102030a0c470109060b07080325090608060604240e030a03050409060906050a03060504060207121206 71
    0x9810520014940c81d00c42c81c84043d40343c0842c412111400250400c41010101c00e800404820700006503c01c06480c001700b00f5900015684025407540c0307480c1c940e001030141d1902400c07d1840d207902c5501b035551380704016180078004010800ca080f01102c61140e000384142d640d10580b0038280180051598008400e0313030341e025205d0f200d80c40d49250603590b40014000000d1440a884500c0388101030218540c8403000e100c2504880750034442014906400840c40705a01c5a000c2904012051207031344404410744803c2c0d030348030301d0f1287c076602c0d880011a041d034005c82e041c290621281d4202100c1d154030014a10485400e9114080b071b0303445440034410b461080e405100d840340c07550f54a008070404481000140444249003407013100540300002818490032480680008501150510545802c1d00c580701c001d1040f420104442460312000c40ca0700c092a10004e00031035641c0d40001c1c1070001c25011030310b646074040000c0e094281103500c0589003481903d007a09903d4078001d00410580e6610125840 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 481374964 1250 481373714 481373723
    0x204050901060509010f1214011d220b0a0b061204121404050904050a0210050a110705090f071b0807120906020c0f01021c0503190c0909110918090d03050103 69
    0x1010840300c4001c7c0c96401042039000a034907076076103c01e54000c0d40341e02200c2c080c00d9078000c10303a01b007501445601110203000e8040c071070300e140c175402c0d001085a000c40302100d0541c3c807801070040c0c1c3ea10980790350010100f806202e40c00c85c100043e40b0090031503c6100904c40c030320545122010500c2064200c8840b8186000d0b1541448204001e0081c0d00d0f00142a0303a005100300c0455542c59500e50228806111070003080e40803070300100d0600c00300790308402c8500d0307050401002840743c41e16003000100c413682d01808001e0702024500220318000c3c450340421400c49416803a0a070391095501e804102d6502050f02940d41007912841003083c1c0380314000b080e0464140d42d005000c000d510760200300d450b42003643e032a03040d88290402150b00c1c00703141507112000d051a40f07a164030b0341b038900303000021400d20040f44034510349490351007170001e90000c12840540700710b500001040c090b0740301e41c1c00442c814180040d910143c0d400b400407100d203020358650700c2001880241c81d0014034140042c0c042e02d0f0203000080 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 481376214 1250 481374964 481374977
    0xa02060a0908070f060f0c02030a030606050c07031113060605040e0c070b010b0d1503200a0b03070e0604090e1f140c0d060f0e0402180c0304110301060810020405090106050901 77
    0x301144d00d0748a1002c8081c0038645c0041c800e8400e00070081100d51168055000d80c001040b000e01441e094071450004100f6818558640076800c50398686400e0b0900000700707608111080300e0b41d00e40728450780c00c4041004140070808030751038220245c81c50b0010310581d81d0103040d180c0010b6510400310181d51945034884c0303958582da400e14195880c0c0303070010b4050800750703507582e00d02586c100c0c8485d14440c0110300030a01c1540114880c3e00c4880484402c1d062030340904550b800822281c0300d040104c035400b00661134400c08040d0580f001032114402d0340d000c40101c0d0b003000c41508810310081002c3c042c08041c0300c11400780c5815000150300b0348010702d0950000c00c2d4084000f40d522002c5000401c000244d40c1d000041c842d03185e0344203082d01034881c4c0001003180802c40406c0b0860030320800c3c4083d80c4104402c000c0003440c020a00071418070005000030645920364400112175282500003c02034050710307041e00da245118109003c0250028801d4900c200300351800040c0c402e0081040728103100d8180c5d11503 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 481377464 1250 481376214 481376227
    0x90302060904050c0f0f0403020307061b0605090705150c0628050a0e0a12111501050d0611190e09010609030f05070902070f050f07060813081e0a02060a0908 69
    0xb00083c003000b05203000d850020000c410398407021000514601410110541e115030540c0145860309000d5000301d4184a42c807103002900740034184100e001d50764042c8000c102903550300d2085013400100d0f8003d80d0408800320fa0806c1c0c40250102130040c0d02c3c40b58044808c10342d070345c0c000800003040802030300601201c1401c4180700840c05821055010000c250b010036000030003c040c62502e01c0c1d64000340c40320300800c400c041c016a84684008080301d040300c014400042c040309180c00c10b240600c00c1781e100f10003040001c820001d183d084034401801001d071554650a802c0207466401451901c840d00007041c01600349040d1901240b2031381a1906c642d01e404043d415541d500e5440c40e820441940c4503c650039002030442c5e807a00040107034901c10601800c0000041c80c05510304401c2010b03045954103c0c01007448581d620003c0c4680c4681100c0d1b150050b8452800d01b0319862050b000300c2060180c101c101c5415558002d801040c00701038640c210380b41d503070740c1c82020000c03600a0b0200421650040202 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 481378714 1250 481377464 481377469
    0x12030d023f0118090c030c0602060106080c120a1401060f0210050408030f190204030303020a0306050303030f0609070509090c1902030f072306150f010f080a090c0e010f150903020609 80
    0x1c600345031003c01000075100c00e05841d03a020b001d50a0b8400c55056000c1c900c01e02041e5810301400b401031105041400203802c185608564500400d04014428820000000d00252007a003000b0014040462006136551311240001d0811541603500c101601c5000040c002c40e050510030707244650382200c62a41962034018400707000a10261000b62040843c5080c002c5c14045803008200441c402c0d00e005075601b00f40a40a000d40e2280c1e40585c0c4650424030422140d060030008040e84208102d400300c0032a0358542c401e544500540030000c0c2c110401030104a18149210010308485840b002000c0051410300701c120b80d41e202d88048481019018407500000914410207407204000c020101c1d8090384440c850f007481c2a40480b1004141c04503116209074604142c00f082d55560390a181c5001859500407000d000b2031405040b0103411a5104c4404081c4214454a403003c0c206010201340256036484a00312a66014001c80c646000614080c48800f40148e00c2141200d038081e14141c10070f40312108 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 481379964 1250 481378714 481378739
    0x6040504030c050d0305100f05010e040914100209040509012f040e0903090f010f0c0201050310030c0608180109030f12061e1e030308010512030d023f01 67
    0x401c40c248111030241c00e0000d0010f0144541000c41036800280c2860044440c0051509542c4880b01d010030644c02449980d80c01000000c0442c0300707444c0801c42c1941460050211141d202d116011402188802c00c1c400100d500100fa40c01000c460501ca2600ca4550f4103080703c1394a48076040c809801c50b40c410003c5c42c90141c94001685481c07a0700e04182d51480c444131429400c4620968541001903000c48500c0c4c01000300c000c000d820f00e04030710400003e06020340107605600019061101c0400011040305180b03c1c1c1d172000c1d551010400346925a2000040c2070100140c0e25910101d184143e10a0586414800c5140c4113130155141101d10b0600702d01610f0f044107140880d0400340e201d280101e04020821070014030b008202c0c6040c0c040740d2400c11500100d0000304888441241c1c0388000704040b070303845081141965001c544448003407000c1c0214a145106131070040b402e039030020031190401c0b1001ca225440250609030070741d0001a030010002c0054050201e00c016041e00c400040c8a071696541 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 481381214 1250 481379964 481379971
    0x5030a140f0607081e0c0a03090f0609050309360c0c070605040906060905030714280f0b0a02060406050709180e070b0c0d050901031112041403070308060405 69
    0x25503060700746a001c0c2a06120084940c1e0011400d02c0042c041d107218020f48005428451442d0341849060803c881e400070b108a0220800709501c030507a06040c001a10828104140d0000040100500c03500d49541ca1340c2005a5442c45140604040354648623454480e48104201101e4500e507050941e2641684210181031a90200d43c1400f50f000b00700c00800441020f4002e5403540e0f038446213860781e1402a035000d0340055080101c4150100a65140015008207581080b403d26030041c1001020410001c059440004481010301054240c4000d00d50f0b010144d4411144075809162503148400f010b2007110107040050340400001400b0540340c1d40b10681101032854054001591003460074015a07170501c070348030b986580309481c46990720f040080c00020306d041c100a5060205501c01141c4840d409802e0209008000079400e02aa12070b6000c0030070b004905503080d4584220622405084104440032501e4450420030350444038000801e9494140d81030b50341c02040e03512201030001820024 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 481382464 1250 481381214 481381253
    0x90f12030c190e040513030c0f0206270112022a010b040222060c0203030403060c0302090a090c140328060e0403020a06140402010503040803060a230f060405030a 71
    0x2d000c0c072240d1035403032440790b03080c4101503441e045a60ba45004003c216040074003010440e100760400c0700000ba4208511484960300001e980400d07403240c1c00400c80a01c2142e644041060410a40a507030000e5000d1101d91000d007039950303440242403d14860220301c0b038144090403109144565a000c10f000c02d40c0c01d610515140c001258001c01d84002c5000e980281c03032100da1800208914000b0001e00a0002005219600d004008401103030046903d0744501e010141600c0c0d2180c0346907130024080d270101d40500201501e42a40c499031205098000c1c040c1040d03c000040c07201c8030303034841d034600031050300c7c0500c9c4004d29000d21400496150444052090600c11455894201c0014034481c0c003a81d1612407800707500500784203005880d0110450758114081f0424029000505c40541d034001c05403079000f980080020b44e130b40c5904001880701d50550744a050300900d040c0d41ea144d0403400306034580c101c0c0000c0d140b40f043e04008030100304090045000e91a05544012661000b18549801c0c250030070104 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 481383714 1250 481382464 481382467
    0x227030705030102040f061409240c060c03040b0901110a18031502040302030f010c050702010813050f011a092a0f07060203060f01030b030c1212070b0f090f12030c 72
    0x1c0307502003400e81c0c1056000843e40c0b0003110040049540203200c95100800d1386000c10700c1c002d00d840024025240c408120600304d01c507501c41d10303006001c0c4800c862403c20441d0454105180c0380c50ba80d6843d50040714200d0708068a1004103150791030501507651202c086240031030405280e00c4040b540b403c0c4a1240324201d0030000000004501400410349038000815000341e501c0d419401854507000c06550780d17100c42ea2415800c4075100d540701054400444d030919040c91035846071020000e103a03040341c80c040d005006070302c400e80d01680c0540c00142c440c482c078030045201000310010094100822201a500400141a51400000442590889560804c4481d41000c0e46030144000390f400c4034100b15030b401da001042c070645140500142c00449001d180070300140d002080840d440c2c4000b020494050031001501034500301050044c81400c8000c48941034903540c15081c01c0c01d103a4010b6a032000902d228101141c03042c00b010030484855003d540082610308404040c94415610051040703030150310 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 481384964 1250 481383714 481383719
    0xf0e01140706110403021002030703020a11130f0507020d0e1c2103022502280b0c010f050c03070804030e030c060c0606040b041a04091403040e011802270307 69
    0x5110f180514545004816102c44c01c42c030603c602552400509404d43d80705000c00e4001035800120080103592140c0c1ea280c0112903500402c511100c140c61484005080000c0c0e0425000254403482c4079003044c4e030895a40e1107070758070243d4000c220240341a400c00040062142d03951000ea0300004658450400b000300c440303c440c0310b680e041d0340300303110180040c0d0001146204607043c24001046204100c001200e050200e5000500030480401e900f00c8514159001c0d14500340c0d9104508010400b0701b1100c1d80d82c6070303014881c0b802400d2002201d15018036000c0031600400501060341c1c4100000d031249186901c0d40c0c0c4090361201e00801072150300d849060805021600c80e0380203092081c4100004140340d04000041105032122488081c4c040c0785441d0700746800101121320082000c0c0181da000505184506100b90108001003460f0b00a11002a00069004004020504940540780502140c0720140c11107070581c801c2488001000443c00e00540b480741008e6a110b443c000014100c1e01c2c05903 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 481386214 1250 481384964 481384973
    0x17030a0305130b0f010e100b03070e04060806010906030c24053a0c03090809010e0315090f060c122403010c020102030a15050312071a04080a030c0f0e011407 69
    0x200c1241d90380004d12816004010101c0741100307460b04996a04050f501c014105903001c0081c2c00024130041c20419000c032840744a440c0c560029018095010541d401c0307603102c48200d0060301b100d22003207410b003010000002d00c5c1d81c0706142000400b61014001102281c04080884650704510391003401140c100740070b41c01c2e0300d1101c20f03082c00b01d68000c030804243c0c8211504000448564240c54030505040030014000910700d0012140c43d20001d0070030052691181b0b001c03034030703001e03019130484c103401102c1c8140441940001214418801c4280c2201e00c0d83d40c44c0900c00c0803500038103521104c80a0f0440118101d08c1460929078081e40f1021011650200180d000a003542c5009480c003002d81d50000500c0b2440300702c0d01401780d0107004845000c0d03040d454140403a50302c0314640030241c4492000b040307580c1000715a8492100c81c02e51880ca501403814241010202640080611001320b46843c0203400860b00820801403100c0d03658482c0b00c0b000c3d11880040d9545140f00001c00481e0004222440c00103 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 481387464 1250 481386214 481386233
    0x6070c1127070e010e242511010f0e0108071205040809030d021b0409020409050a1b0b0f07060b0301150305060a060e0405030901030e1603060605090601080c03011421031317030a030513 81
    0x7c2451020200c51140781031a000444081d251070307040190f0407181c0b81039280c02400080b5042004e113056041a501e64400319050180f107100c0c0b00403242040c092005006510018000c1c4000031000da8a0030030745640c050b0303615081041030200007044021350300381c6450240d1040d801140080c1000c10034014507038507a41855140c40c000c40d0000c09038403001c5048440d15242802802c141c52070703c1c1c50241513420340b01d0140540403009244036183c0951150548081d0041d0002d541482c0e1981c00244d12450156210b06080fa45032041078030300f007000180000014041c50046400401841c5042c1102004502411201201c1c030001d120341d41c0c0c80e80b0308089401c21100150701901d00014964104001c011804d8005022039041000300c509003c0e8126002085a046601c0e81c035040c00e140c015403002c40d161218008000c1d0100b1700140070a0189900800280a2440c0e0f00361300000e05515080c0c40c901d074040d4001014a00e61043c810112441d0099024680000d842e2201402d0007050f55105080b0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 481388714 1250 481387464 481387507
    0x5030310090501061b0816081201080d0e0d05211b0c100e010c0c0f060305130b060d151109210613020a030209040503071406070c1127070e010e24 64
    0x28a002410134807109d40300c0d034040c1c050010000070340743c026034103880100b00b20043c0400a206002c03052841c01004010008451030f9400c2c4040f650001700000700d0800543c101100c240d81c107240041802c0c18a81c40424200207200009060741d61445640c002160191044c109407030600c100304055101054491600000400440008140701c034140030004080e14005404c40000e051911240030000b26004c120719400201558100600e500500b0807000004450b41124030300b500c1d100300711760a40c103070200030120094150307030309500d624014501c02c030112480c0700010110342124000c500b07409000362a120465000409080102c1e4881c2c0000b80e95410a440c22203099000182010410054814405540e01c0e00ba01502151914400c00b03072034500103440051000000398404c99441d41c0b202e540088041141d480303004000d451500b51042084260740003004100703d90b1807a2071541c400d01c080a101030000e41034600d041c07034040b10014401031030812040840d20038081c03030407540c12a0400185 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 481389964 1250 481388714 481388723
    0x7030b091614040f061802090d0b1003200d0b0709080f01060e0f010f210b04030906270e09010617060406050609090c0f06130305030310090501061b0816 67
    0x1c1185000b410801194410981d5407003040c1030180c108030703112802c200000d0035016264050381e940c0c1003400094100045240041c1401c038190144182c43d4614003151080d40e2255250030405a03442c3da0500705880d02c80c507181e9102e19615410b00000c0d419006158004800e41840011291100889414020704044901c420380d940ca50400c4003031904250240c004515640740d61295040c4007d182c00c180050058841035282e14148000c10407100012110040e041041c11240f800d192500411001c828441e92001a410040801c01a000b490301403054a118201a4051a20302000700152040090801c10503543c0d03408000341703891005d0382d11884505504040e1401c0c2c582071500c0380c01c485002c1d1500c0d00541000c000c10402400004181202207000c80e0000f81c44d12741c040c0003032828481c0c03980d125441018a0030000801c2000806903000e01212620859110b46540042040714006d01ca0071000901082d1480d4640041c0350350161034070700a5002c04d180028030044410300490201003143d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 481391214 1250 481389964 481389989
    0x30d0201140718090203041104050a02091f0f1409060a023403020d1704080109030305061c02060a050705011b020d02062a04050406120b1807030b0916 66
    0x72401192001580d032040c5103041c0650005028810102d489045004034807485a000010030140004640181d82d403400c000c10034442c6140000e5640702139082030391000d008010840000580304161fa651420750314440e13071030340d0403a042500c04849605001000325024401000032692a0b01d0319002441c0d0240b04e5001007010303400c5204644095041c0c3c020000a00c4040c0c0d107144000014904540d0417260100e581000b85032132424044280140368100510030600003c00203882e580c19000060001c0c001d44082080f0342e80c0c0c5080c0001c04400094900d00b40380e00307425103801440d003500641040c04041c0b41c2142007200540d1090f003101d00082c0450411710540800d40200d85c2d0401ca1400da0b01168070103061a41010803082c1c1007103042020595004c00e030b240c4881c41c16803140d02510000c26005005006660b5a041c404074644400c110a903140d040100004603503003c0401a8a00450414000c084443c51074803100f202c00c80160407000035008107a0951030300c482403041000909801601003 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 481392464 1250 481391214 481391231
    0x91203070309150203030601080a0c0e0a031b09060308090d03021e011a0d0b061302090306130c08060c042c160f0e1c030306050a0306150504110a1805030d0201 70
    0x824400003c502850115401001041542c0c2d81c0018140c0e00241800c1c2e0118200350f482c201030360218403441c2107640089240900100f88a04035000c2c0c1c1083c200c0d4031141c00201d4071003e404042e51858000600b50040412140c042ca0030070400742d41f400350080c41603d82d01e0541300107031144004510078030715080e0344641007004500c2040c541d1030300c0e0010031103d51600355103e035250006240010030403886a4030141041031300110301c1c1c040301c0101f080201683e45030310f000144640a50070216080d155110f0419010895800000d102405174030000320300390074586803844903200c0c014603190301201c0b0301c5540306111964040b003200900803401b03a911079001070040e07100204080c0682041000308904111060110384440701c00350700703400c0b08901c180d0300e2004c50704041c1e019101c00da015680001c800300c0c0000501c90b41d5441918604809035031020b000d60344104000590b04511060080746000300004501903004020a42c481c4005503050058581e60343d00107400d10306a1040c0c200035035142c0354203 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 481393714 1250 481392464 481392479
    0x507080a0905221b080a05090304090e1c0f0207140103020d05090a0302102003062b120e06030105010509151801110d08010308030405010605040204090c0305161202091203070309 78
    0x55207013901030401c803c6800840840c000b01744005c003514100800e580c3da0045107050406008580250a05030400e004a4450061090751f03024030810500d0ba0440d400c07111820a88140114548203480394010a01c5c18101084845007002a400c01c1d414540d080000d2440002c150080501c1441c610020b80304101941c1806800e12601c1140c002c14a480c0074404542c5ca808c2801c16140c1803200d4032000d880e6650240840e0307803c00c42c140003074040200d201400540d10303049803102460501c212100c5802c60f1440340305442d004801c1c074020358045070a00062080794425006041e030000000e10b01640507400c01c0c0071a40c00d42c025807011300c00c0d101d4646020510f58101c145001c0303042c074a40c000c240010740e86800400d41041808018800c0070000003080921109400040107008020300c111340d00d0703684c1c0c92a0b400030701100200c4070210782807900003244a0380400d520407010342c0c551100380180580c1404030000758041103c650707001003851101e400f5007500708050418513100e40c84080280f400c3c19407 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 481394964 1250 481393714 481393721
    0x1204030209060103050606160f051501050a090c0f080a14070801091a0d1704240f021f0b01020a0c0311190311090601030e0a030c0c050102030a0507080a090522 70
    0x42c49052600b00300500115803651011501c1801000e86042000a41c514013550480e02a4202810901c41e0044000c000c0700701ea603100d4101d5030200e43c1d0388101980c0d00e28040a65a001040201050800980e6140170f4012500d19500080680001030a100020252240c2d0b00f011f8805000090301d030070042c400160688900c04035102590203801c0c103c1d100c000020403d09005a00a000603813010b5800d010328403240984000d0100303180300340c890766940c0c51a003003c854100e02c00d00c001001c00c8203202e1164008500010414031205640305401881c010000240482030146411441000c801c13002182654044601541c856511007101a0900d810018181000307030120400c4188400100f00040112740841900035040da0000c0b4107a0b1203000603001000040c080914038080c0c0c0c0c5400080540c00b00102e084544a62a4849040d0f22100126520b005042405012035020021040460542c42c050710314089189000d020494030b0710b02140b4500030500004050440b502c072200c000120a00 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 481396214 1250 481394964 481394971
    0xf150515060c03041e0b030406020c0c010809190305040b12091b03060a05062e03060603060f090f1d1b040207020a050f040b04050903040807210b10081204030209 71
    0x450942c100205001000c1c1c9074410b0f84904030251080e415a100349a031028550343c000d203001708032651640340c5030601c00c0203580400c030320b0260303405603860009082d0700944046005001d400300030700543e42c1c900d4100c84140b2444906809008044c4000114021880300500b80c4400e100804030807800c22420303103490201009540080001100210b015030f0324000340c070300d6205607a07007404a01e503203401c004100705140148100009518010208cc84802405071a4000d4000e65130f081050b02e64800c011021108140100b0030320340c05811007040921600c0d0003188401010500001e1081c0c0030340c0325a81001500d0162544076003184a42001d00d61200052004c842400d850070362802010f0342c00603c0100850044c1441041890003014131030f1035550186225a5010b8030400403424107040350f6540c1c0c0c00c00d100e1900d071807288900c0031820a01201d0b0015840d2000c0d80074010004450b91014bd001c1c400070401e01d0845400300e00002c0c0c0000070050b90f402140c00c0e441c03947e0b9803410750060091b1500c004 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 481397464 1250 481396214 481396219
    0x807020d151d0f150f040c0312050a11070e01091a0d0c03020109060f0903080d0f051f0f03050c0906010c1704150516020103051902040b0c060108280f150515 69
    0x241074200b03030000704078900d591000c4480b41402451b0340e14034012044040c01c0d000075140c030100c61200c60309503412070000c00c49111552078407001d000c00c131915660f9a080a00494101e2941080100881600b9805c09612504034202d1202480d20000c04103030302c60682e0b60300380d03242d001100b4204207650300890080064181d07840c00b00350700c00d16170201908403400b506c802004c510740028a82004046a0710840050803952818001806c18110020750258403800210301c0030754985002510300c0c01101104100c9501001502d2034144080412076840402405181400441c056500c000350480c500030741840c800c121020b07229410014011100000d0020741814040308106401d40020f24000c076801a580c2441d0105065603003103c40a1a03085607001050aa0b001040220b1107440310300181101854000840d1001da0b43d5088003aa80c42d41200c071090006803540300080b03c0c881c003058004495003e0610405e0040241d9113846160b280e003001400c040350303564148040380d102844070702100c1104 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 481398714 1250 481397464 481397473
    0x10c1103070506060105030414030c070302010905190909050f0d03140f130609060f1a03010c14040b09061207030209120705130b03010902030a1a060402070807020d151d0f 75
    0x80d50b03569075400c0007804090622801100240801802080c010368041034502034948071070004411956551480c0412404212023440214607800c200d02801c400100581140000b28907040d0750f01e00400c100c0409495501422141c4da030f41d0f0008100007095240643d4000890480e4501c280d1490b210151080c4c2d11940343c84240007107140b487c1450000260400800900d403085071030403e0040030040c0080701e038035003803c0302c8021031149001c1c0000c1070307032040d0000d00040d8880d6000322882c0211400f100c10860003803105100c1400c180001e0f140c88200545514030b031807070b00c84883d21851401c441810000390006a0004c039802e105185c0802c621950005084003402d03c000141503e10356208041540c0d0744001c03d43c95607409400103c495600134051392101e80240c105036101d00102001e01109150200101700f581c00c0c540b003140c602541100d10241025035550800c41d182e61860800d90780011564413894911704180300301d11110701c052003000110911155001d007403e00780760b440d8095400 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 481399964 1250 481398714 481398727
    0x40b0f09060705071b0305011803021209031f110d0902040f0c020c010309050a020d0b07020706020606010f0c03020c1503100806040f060905070f09020a110102130303030b06070212010c1103 83
    0x2c010b015204e0140c0e0001d00540c11030401c881500040d903213503002802544c24050455244000700d580c200c8454000d40c29607003c0300c121000c18580e4414130800503010b5104116401c48040d44210540001011940101d0340d0310307141130070f641c03650066209884519659103c540440ca028030070303102c1e000a408000e01140e8611135002e5290244450060305041d240c174440002c20509011030302c840395000781092a4180241450b10003039004451130409480386210100d482400042c0e00d52007404140e65016408582c0d9074112660003a6403422015071040c0035080c8819942d22100a801d4150900403d03203901e0010004c1d00001200d074040f40003508090103100208062017480c02d46182c1046022840c02c0141c54060700d800d08680c000301c040c4400001c00324100780340741c0091240c94020b542c0c0500c4100c5581140e802c03032164100000a200b403a80d0204000707030080d00003090064000380684e0030a400c2d500860f0080f04c0c862900c0595035503c407001c0d0f42c540e4101c3c10708610148080001c506052 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 481401214 1250 481399964 481399967
    0x106080106110616080603010e03160b130c0603020f1603020c040506040b01080f0c04050d030e03010b1f0e150f270a0b0306030c040627051506070812040b0f090607 72
    0x1218002804c08004203580002d80a0301c09401540a11072001d08803541c50380d40c0040409000d4809804442d100c0050022a490b0350440840e01445030704a00709100d002e2078507500354020350086080c444c0c0114140f2038610100e00c2104450030b9180250080c2401d440c0020400045402c010715491140c1d1078541d0007001641e002c001d995021410002d801c3c1c15071036000c900d070958004c80c0d00c03542c0c0c021641c0c6060070400d68840c0a01d408100c0503802800385003401020421000f00000c940c52900c119170100e0340c0c02d0f43c0700d24503044910b500a000710341456918003001c64a64080102040c12040c0060204070b2404c5806081030000d45403800c0480c0c405a40c13000131200941c44c862010a8400400895650f95090100c0a54140c00400402845640300900112801c551800005000c0f91038202c480c5000d0b00d01a0030700c60041c10034201d0400d03191004001d20b607080880d090380c0400301484060081c0040030303125400780e809100c0300401458001010603449070010610221a0040300602c102507 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 481402464 1250 481401214 481401241
    0x11503050a0615201e07061407020f010e0603180601150f050c03040b07060e011a0303040512070b04091e15061d0a0b1e2703030c030301060801061106 66
    0x21003450094114044802002415a03114a400940e4029000c02c001a20000d83c003010507880e00d1000c3d40d44447d41c4160985088000c01c0c51000b20301c40030083d01005141c01c0350511601141410250142c48100c0c02041941c1c1044550654440328514000504081001010b0040060203c640840508000f000740750854016901c0103001000c83c4201e000e0409100361405040300043d503907100c80d1300b824020060145090340c2c00d000d510340b03407041010349250b600c50340304c41074041e0007035181902d010b0620100c10340304180d8154501590340b020031840300020061005002c810b5002ca0000142c1a03003010340255060f03411092803510030704030384141c4404804e001300c6080d4100f90000090a4040c48100f000c90300c089644448200000300b40700004401814814a561800c4510b914071003030701200300c1c403c00001c0a9109d600e9105950300d50702c501c2c3e01c2a070100001e01500c0c1012a848900c9285410a81006012503200c40051000b1070340020703d1040c01c4c941d032004102c207080c1304904c2d4103807 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 481403714 1250 481402464 481402499
    0x71208070b07050d050a0623150c19050607020115030b04231903020705040b2d0d052803050a0e0102010213090218030606032a09011503050a06 63
    0x1035040d200040800380994141c0b40d05007040041403001b85080c801130fa00414503800360711100940c4010340490042c00800c0d0388030003500036014521001c03540c8901b00c801e0300007166086541c810300e000d00b146061030707c4070345100c82d01c100d00416050901e407074040d095a141c40c95420310200308500c10000300d958030075801e0304907403c0707030300840c3c0105c068003003076650307452007662103078034410148003040800074440c0602416000b50b007547e60035600c1c0e030104001d44082c8601160300c002250310f000008121501c5e421580d11a94513040e1880e6021703c0460800c42c0c05550035070741600715100304440341e0b0000305400040c1c034121392910b0812050355005880c81c0202000c080411080a0000702c081c0d000754100d8411908490042013034a0740eaa040b100654070810307803400243c3c1003283c22091404c0025815015000050140c400c600490301c61030f4500441d080c00102c0b5103054400c210f81501c0d8450000c3c040d01403018030704005003090b5005800c0d98406070803044510702d0520100034036800701800850 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 481404964 1250 481403714 481403723
    0x1a060306070c0f0c031b0e0c0f0309071d090106240e0a09110912030403030503010b03041b301110050c1c0f21020904140a0e07120807 59
    0x4414205050100443c15121030092102034102004400c3c003a1500c840394401c107107520b21141e82038480d00068207150058135102d80951040c011805216001005143d00c201100215508141ea549180314100710607594004101c00c45814042c21480a0150300040c2c8001d000300402c03524448c200015409042c54a00204169051001e400d80e40c4e1150700c60051400000510080320400c0c404071440c0e00c240c142034807a604854002c0e00d0080080151811030350035880300b03815a03192000e4408550720051046444414503070201c001104c01001e6030028000780d051008040420481f002006103148070302e00e80707000302540d00c10300144000c125480b000b0b805460104841020850603102400381c803031141424001d0200c000c024404900311080511403543e15488140c01500090707a140c0c102000c40e900c03181e0305883e507000d01e0190b034000b00030610000c0c00c001400d040c00341a52408500c01d0302d65042171611020000c103800000c0083c40090840c0b04051005200159606021482420300082c03 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 481406214 1250 481404964 481404977
    0x220e0c0d0908190206011401080c040311010507150b040b040209031f090501021602150a0203030a0b0105070f050a110f09060d0f050717010c030c1d0f030109030c1a06030607 76
    0x1040094082c1a60240b040c1c003a40000310012044001e920307044240108001c07503140300380400003503100b00d84190203404104144e81c40c0a05544580c611125141d0006040c403800304001000121855600750400109a200040000c180003c003c2030f01d480c5541544154010702001509940c00700c0c1c008030200f0041201400300001ca81a940603011400001d4855407021074905c80003500f030415019554802c40c0d080c602024690881c80d44ca000d15140350380140d10500015416500503030016a0111307050402c41d0038080c003035403042d01c084031880040f101900403201c28000c0101042d0103040310390702100d06030343d43e603090320105456480040c2550711a506500034001408100d80114400c50313046002e4400b01505d0304110004441c106840300d0180d840c0491180e001803003031040c0b1410803003d55420189003610040001001c503600003d96000c1031194415030300344c0d401d2007504045c1d44a515070300c2e403c6890303042002007040040010184044040104000d660f00800d02030b40c40f04890030b109 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 481407464 1250 481406214 481406231
    0xb0907080c121f0609060e0a0b014401060314012102060306120f0d08061801050907031d0a031205072705061833070501020906220e0c0d 60
    0x44c00165100c0c442261a0000c0403c5001240f5100c1307104508040c014400141404011281d90f480c0c5200441d020151000d40c4280140902550540c4160402140170120403e4490f0416490a9201c440803c0d69000810110040d41c4031040c0109030022504084e1101d91101100c000c4e02214020302c90f042c0040001c0c02541c41c011001000e503048000c80c1c14680520358007950300d446407081c071000304000c20000340907844c02d1410701806462246c008400c50f46810700f40401920050882400d15807980325612821507035042010303054403590000c00155009007409003020f45035042401d1014200f4040003445500800341020403840313030140101d00a11b1900000214529400860340190700143c4004ac010f42440c0415588408641c03100c8034a41c0421101d000440142e0020310f00e100c0801074160307400940b00640400d070700810026260001400008425a01901c03001c003203040c1508890441c0c08141c0c40c0d882c09820704401007456402c10001c200a58002c84040e07400300d0b41c444ae0107 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 481408714 1250 481407464 481407523
    0x90810020a1b0506100b0c070b031302030d0819231009060303020105010315051006030b010207050d140607050a140706060e070305010312020d0819090b0907080c12 72
    0xc1c0c06514150000361448410b60320f480c03920b81406540362000b070070a240000c1060b40e002003c690001c45004002c008e001c0c640100301140383c00c020840c5400c010710300c03040000750b201400000750b00d640b02d40e600030380d514104014503400c0c9803a8645804e4280350161010520340164150203510f410014641501d0384d40c0c9150f070340c0101417500302c02101400e00078008105501500564142c903c00c1078241203039141d80e004907080b50f03000c031291002d1088081c0108160f50080d4048040001c0610559143e10344400102e40d04161400085501c84005c41606244034400d0000c01c1d00403100746401890030000701d90007456407105d201000b200c030900082c010200030456005400a1949142c81d24140c54900000340040c4000d120a81d4080500c0c41007030315072480410000441c2155482d030600c161294030340708400d241103101c0b007801303196580c2d039582c0811070480615201d44000d60040007241d00380b04513903081000d120303034041c010168084240307e070b0180850301840400d442111109600e551284 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 481409964 1250 481408714 481408727
    0x9060812121816140607030e040f111605061f03030f051209160506030c0703110307060203090a050c01020d08010e0403030b060c0724140a020a12080103050607090810020a 75
    0x4108030380f403085002e00282422030142610403070b644401108811200c0714148681c0c0d10401100500141144a103080c0c3d80c07419900103118081e040c0000540701d800400000050f40c0000189500c11000d0400c010800a040000c1c0c3e03840140c888100603a4541400b4261a0440e1400700030b040c0300006000900c0341c1e110300c080c1d0391106020504d030400c6082c554025078030b504000911403104119490040b0346420000122401140c007010700a00c1d052280d14100d92022020002c04801c0c0000c1040e01d01040c0580003035405814500090591a2000c1c074100e45040b1411441c10f06542100000b050b006410805176811100c4220f017a044a940d9803800314002c11551303803100e0b0701280115800e611b20380e000803140141c460005d80e0480d0895009400b940c10030481c003140000602020f090151400b2070005050007022030300448800e401103176034070b0194141d50740401d00000d0342c02c4010000e1000030820380b5000070140c200b03218014100b81003562200069418031038259000501318041c54403440 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 481411214 1250 481409964 481410001
    0x19020d150f091223030a0914010c0228080a0e030a06050702060a11120103120c0503040902070605010603020313060b010905030709060906060822170c070906081212 72
    0xa410003030b403070083c5400040748031182008000540c082002c0010f040b41081603800200100e0041e90540e0b68914040014000c0700104a0301e0a41c40018800c0b48070003401241502000c5802811076292404040049000d82c0d1001c00c403132119841d840340200c0c03807803011124070b21010b03e0074072450324503440403a107442c118440040c081480c1000f00103c0c140d0204045000d00d22000d0140500c008802000f2428000d80c840c00002445c00e500420000c0c5021605c40d01c0e40302c00d03050070101c075950340d110103046801c80d03405107002540006004040214610030b181c00740c00607003000c40c2113003049103140c02000d40e002c1c3c004005d0b40c3e075680ca029490780031306a604c000300350040031641d445c1e131980e920a000d48501d1003142c50483c01c2c14008501c3c0c0d40030b4454103104001c20f50007000790b485a00085040d0340d000704010380f103140341c5100d19028a24000000c148000c0e001005064051403c00d030f403030460b80307594010179158006000c114014014a801c83e0401c01000781841d00e02c4d191070b481460002c104a = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 481412464 1250 481411214 481411241
    0x4050604060816090c090303090b1308030d050417040e0a0f151202040506100c06020307140d09122606030304051915090e01230a1719020d15 62
    0x101401ca0703c0048031200140d074a030900070701200d484500c080e61082a01c0c040200411500c2e41c080c0100a151030190890940480740e01c10b19559509641d4103540c41042884131150300c07a0100024486034071403441d400e1303a0004056241a1410500100704a006000701c038080b80c99451000c0290003a402128801c0c152980814100340e5a10340342020b20000b000032805241030074009007080c540b00c5407200140ad615110104d50082669614000b0751005007680305201800f4004c0800c0b842c018040c0404c2c401624002883c9804c2d810222601003a0001c40400c026529401c4070b0014001d04040c000703c0100c150803007564850000103410b60046810050b000140020055213062000408030b04481d214a035400c01840d101a080303840c161130b40208503444c2070034001004586030300070311510618910074041d211247c03030b080004c10788440d945c0600d107400d10048001414503c00e00100c103161180300205d400328005070f03001c14412490444042c00540c6404003101c3d032102c132034014400b0741d00c00 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 481413714 1250 481412464 481412473
    0x1401030e100510030b0a050c0703120e06130615062708030a050301030c06080c180d0b0702031c1a04020a020703081330060b1c0606050f010c03080402040506040608 72
    0x30f41a06400c291244030580391260701d10080b822640580c844c660281c000304422916140d0161015138a505540c15405180f940d1622a000c0c00001405450b00a441c040c0251040c581c240c14000280d0341c0c15008600424504078040016603080403001c5108144600100003500c1c54140da4020300136140d000e2099400002290140c42d035102c40154140d901c1502041d01094907800b044517a80022120790601c40420041d68542c840760801c0041400001441c0c09000250741d91103d901030310551300700c0c001d41e1020075107850320589006c1041c0e6100700b09000f008640c9403d03841004c0381c0130390307800c5601403503001441c01e0b400b613c2032100201450b00545400e80c0e901022031a5003210520788222190200b95032351090135031000c00c10745100d0440f44002d074610903180d910b40800801c000041d0590000c0c01c615070340c1c03450040c0ca80020400c2c0c0515030001e5880e1070101407143e0b644d07210010341d0402c0300e141d5040002036001503400d82c1083e01560006500d54540c0e0108004241a40000300981725 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 481414964 1250 481413714 481413721
    0x7032402130503070b130e19020c0c09070e03071701150308090307050f060304060c120c030204051c0807110102160306020c151e04020423090d091401030e1005 70
    0x100c1801c4003250415011694481d40d103050140c6039002e42d0808105e00120440200031004420302c510b40c010035203109440880c55125000e404a0340581001250b40c0c201d4103880d0b00038544500b40c1a480042d81c02c011707030100140030010352144840d014001d100070740100180300344030096100081300000481c13100c0126403203080c0502d960304440901131003445019004201341c1071550a00d03000d490003800312821521140d860001038092001c03060b0801c5554007442402c06c0d0301e03000d580c03411103486c1c40041c2d8a609142c207015510104101705c46504101040400008150004540d4582d4206010311200711003140100e0901240580e440110035844201000f0710910364024408442800704881d01d00400c05400e03007070141c0440f4a2580600e41c9a05401c1e001a80c020595019100030000140f025580488000b603040210814034044036400412030172501c00c210103101030030f580c1061489a07160914100900102041103410540c44407000206000100034160050f00d07070360000d020301d29 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 481416214 1250 481414964 481414987
    0x10110702100c0506010b0f0a0c0204201c05040f0206180604030c061d151809010f06080a2c0a0203010f05060301060603180303021b01090515090f07032402 68
    0x1000542640c19024104c000184a04c2910440740b903510241c00140c1007188000f019900b1203680d00c8184d82150300c44220b15520040398403208040a2503a01540c0c070b0b060f495110001800041c2c41070000d03546440144801728400802c01141c19030304070340d0740c0d9903a000f44141100d0510105030407a00040b0101d80442000758803d100c20544034913540d540c001c3e40c030301e17001480c1d9402da0409403500b08591540001000780054024800e4010500340c0340c400140f1100801c1c11002c1c261b20111310782c60306070030a02100b6440f082464004003502414084035400c4110010314011464042c262a180010704001108003800210744854006008000c40040f5500103005084101c860038401d500e040c0b004220280a845081035071081c20307035510429035060380c09034029840318000c08078401440d445224044024014501064450009484400c0030444850881c22005c4c0c040346551700001c0e00e20f4002c00b0f0018000d000c4a40010783c01480310009444904183d4000038241c1006000054001c41b05 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 481417464 1250 481416214 481416227
    0x3042904060f0e06061f0905030f0307060c080118050601120f0c030c050c07140d0804060f030606091202090402300d0825030b091302011404081011070210 68
    0x41c02c2d21020300001c440c81c0c920940303c1c4000c0740e03a03551080441010200504c0c0e103003260603034480c29080c1903a600b078480001a181510800306070305590305c00940102004028081e0b0043c01e04603007800718587d4186540005800509a4040b464a13642c20014100e81c0c8240b00004115545407410410f907000418000003402e48191018082410800c098841d1071240d000c440c10500b408000c1c2828908003115503281001007841164005084002c1d60301041000004200070425034076814600c1000500190541d038a0798440401c2c0215501d0402006661001c0c8900195040380e08004554482c400107841c43c4140180291051040c03e2540700d01491141400d0840180700031039007030a00b0340c0d070100c40405e01151101e042c000903e03a11080c100014100610404c050b040100c0c4481c042c8000c0360301d64004a583c8001d003840c1c16503100c190b503003041001d0900300e884a400c0389002d0401d9600342e50303828190b4900d840b076a43c5100d50f502c0d01d200304060311041c50303009102841c8040718100c001c001 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 481418714 1250 481417464 481417481
    0x10092d021002061302060c16061106060a05150306011701080d0207080a030e01080c090d030921170702041107050105010e0c04031a0603011b080711060c0304290406 72
    0x140280c448107031511800003528500c5900303003061a003000c0c0301c0c580c00c2c454942c200420100851141c40c4001e80030300180141e00014000c241e40b00040044030782c5c191852710102900b09030080b1000c0000344859100c62802c8042d05180050055030380d00e85d01c0c0120380c1050070000c00ca00842c403090011400a00105281310715540031343c2115040da44071028075440d40c0140300c000740420801d004180465003e56400c0d58811101c6003040d007080c00c1c3c41c0214000d80d2200070124001031514006010905085c05190b407000c04c0500c505818104c20356130001c078840034065540031031034041444400c6507601d800c4038960800041c042d40d220001840c28502a000a006169a10a807100024585402c0340c0030703a4222034202d0058201021000519040c03480c000d8516078240d525480307444400e080055108034030007903e40d41c6070210f1400c040000c0c05007030241d064010582203801800035450001003901d4100f90400c4841180400c86618050b66400e0403690065605001c8100024458a54003003001c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 481419964 1250 481418714 481418719
    0x70603061401053c0a020a021206040215031807030b0109061703040b0f0c060f0609010605070c091a13020306152104140a1407090e10092d02 62
    0x11060000740055445002d00c40145040312807100f9a2400d500c0c40d190307010081d25504c82e2040301c1c41c110713000d03444071640f001380094056030291818a0440c113081020070f2204444c6005895035040581c0069000b02d0721080701d42d503141020010800e007030030301c01d0b9061180003c40126440503959251580000c5400d22030409007a00d412000100321b003004841842e80286800554034290070540c00030b140f0380040100102c262028446018000810000180500079a1007400c14510302a010484900416001a010400305201d5017000844220081c815902500808200e01404070054040c008190184640c083ca0310319494840542c41e600131405100700b5a12032014141c0401142e0711880384140728500e80d1201c0012024540c00d02c1d103601c0d00b2600c034107241501e90402400f11840d1035440202035404403a4031100349401e81041101200504a10f00144004041f031861251100701a022948100d5140d1305018100004562580ea603140f4a01d125401c4401c6c4500001862064801c12030 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 481421214 1250 481419964 481419989
    0x30605060a032307050f070303060e091c0509061209030706050c0a09050607030815010c151d0d022806020f0a0e09160e031005041208100807091d07060306 68
    0x2031402040f2050a20074001341c0c58403032410200c01ca17032210039807043c101a410580d48500212799050b2591207075004009400090000362303418002c1c807403450744005030070040c01420000c3c28242e032105d4050b5401c14048118250250307a038035588508512800400804030ba246c001042000044400601030452495a0b503226090301e0300d0a10110b4410000040c1c003040102d000030b02c00c1307940781c0811000d140c8185013102008000703540380034038140d400300c010b440740d6100d140c034112100820070380e9410b83e40014001d007049203200b1800794070342d03180c4401d84101000c800c03284019410009003100f205c56004c2001c40d6601c0301000f402c40c003078104242000028803101d9643c82c441c90469000e6009540b07040d00c092401030400c409603038070764041e1081e90f0140280302c00384021070f146114031841140548134a9414407032140c00200980300041104419a507548030a001c0140c00280391010380791510b2001031040d003003221180c0c81d140c00b00c08142041c40368540100b20640d043e04100111004104143c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 481422464 1250 481421214 481421261
    0x3060510021e0f06040b1312020f1009110108090a0c03031707020d090b0d23010f150504060806010e040e071a0a1d04020405090708090d05030106051207030605060a03 73
    0x251500040c2c0d000f110150b1000f404180400d4201c040250030941000c080c0424030f11543c1e0303486407006010f1000015030000f03a00c452401006102c0c019510302580f500f00038030b42599640600c04c1c2d02142416040181102c0001d0814008014083c20640c00117101003c5a83d03034a8002e02c03182e0550b04814040c080000880d0565000040d200308118254032442191420a8501030f926000302184a07034072900da003200481c401881052041131407400529107825810b1186241181d0f4280c0e21203940704150a03500078107141c0c00410f44040d42e4081c41d100015444080048600d061041d2000354031a2410021003801c140000700d6000b107840d0714210028055a01058001c58050240f0490105810b448a90310707a58440c0d200620a100c001c0c0010b0600340c50780d002c200354400894800c03011400130406e1203081c1c01d01300b121508038042450118655810f004004100380120119404914403d80c007007903003140241c100c20040c000c054161303526100c01e040c009000c0c203103d1114074427116440046 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 481423714 1250 481422464 481422523
    0x509090c0a120b21100e10150605030f060109150305090d180509040f06021911120403060905010e03031306140f06090a020c06010306020d0b10080c07030306051002 72
    0x400c0f10b20349006000402040f030354010b50781021186004d042d402d0003401200080f400c50741c8201c003441910342d0020003891400d454508101c3c1d102e52040746074028103410030000141d1107011290f001d2880d0301c005407980c540000584000d62190483c80c4200b0150b014104540ea056110610030484542107500d08000301c030302943d42c0c04045165030300040202c1c00a204c941000c12400340c025101c0c40d804031300211252244000c9070400c00000c0c0e0b0020040303410348000341d4070000034007102201d580507041c400700b90304107009648203070b2200501c5036032500810301c24000c0070361003031410180c0d074030580e6038034a0400c03c02140100200c4c41100c3c0e180c074045003000815100d4003c40d1151084051040950305c0e5a401c200320820010010074005408001c10308081c4401e02906009620a807009a21050620284410b581a9902c040c1c011030126a900c40b0700da611003050741d0083c200d50840360341d401081c00c08030083c00ca076400070364102d52250110404a60f00061512402d40146441400342015402 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 481424964 1250 481423714 481423721
    0x11031b25080d051305071412241e01090507110a0c091d0d050c0708070303080115051207030c022e0e1f02090a05030d0f0f020a051c0509090c0a12 64
    0x3800e02c1c0d01c83c0304140940007d2101500490900030310302414249400b41040c500138010301038405640c0c035030b8501e49515030000304158002d1440599603a0004c912100d2005c8018140b042c0040c60392a503004c03d8a1600821441c440c0040d5402940d0f1a01c03c0b90401f050710100f107105004445207081440813500c01041344005813981d190001e0461404440002c03101a000b4001d90300c01d40c0101d240015181000300310ba40029031080e25084a5503162401c9166881c2825542c0f4040c040c0c1000744040c801c6010703c0d410741c014401e00f80000c5050f0b20402c200e1820821011507a01c245042c2d088141d18082c07100300501000d00751205001c5000303074080b25601e400c3c1c0110040400d0700c4080308001400c4503074002c0c0c050410f02525a42000d0307925000640703400340b00400e000215007901030078041036503c103050100e903040900081403020a559a810743d203456049800b035410300d9040100e0b003000d1054040381c0849100420762002e504101c564503000781c1c030109408000c6404081d0b6415410950702 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 481426214 1250 481424964 481425001
    0x7081008010b090c03040201050f041206050705041d07120f060801110a0203070809060d0f1b0e060f0d060803070309140906060702060304150e0309030111031b25080d05 74
    0x1d14246403529405042c41985e0030140c8101e050000c03c0c00b404c0180560b503000f034001052004000c12302d090041c1011001c40300301601341400c0120400050243c80a01000d0100c04aa402e075000821786e50604119101c600c64020288414102120032803810000d030881400e44e07500718001c01c0700d0751800e83c03980312900c207082c02e00015820074809140860030032030180002d982d000c1e200d40c5ca4001d403080c0312400c88241403540a10a0b03540e00058801d920b61501d0004c0132041c504200310001c0864000503054010f0641422000034000f890308822011604403100404010085036140e034020725000d4034140c1d0314091040080c0212010f8503440c41c003400d1044c05040041d01145c80c001e11034080c0429a0f20081042d10072002d6240300c3d8085405900c07400003400302d09005580c5402c3c0d141c04050948007120101c80e440c107402e00030f01c001c0049142c440342000c028502180d903070b4100180c1d09018244624591048112101c91682c24424820003d2044001e0a0343c10043d559138608540c10005004 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 481427464 1250 481426214 481426219
    0x10b0405270a230705040f0c1101091e0204140106051209062a0c1b0a0801020304080a11120301031a010803130504020a14040306091415071b050607081008010b 70
    0x20405018500c2030000504202e8a500f0030b0311485522800802c099600c50a1003000d001c2d91911110300c1d2603171000d00c5021254259000707108050726038640071a0003084c0e00e102c1c4c0c0c5000101ca2804115540e070740c000d00c1c1d101c0404020b20410741c0d4500c00581181c0100743c4604203c0385c56000150769000100c0d59510681c8030f181030154020702240c06040040c489010441c800d541042031f400d00f12410028071004800c0c44501c620302c1c60840c02401807500060380035100c1031f8018018480003508003004da50303000f0b41a00e806500b03058000c1101c0d04c0c008e4000241e06400000000100c00d000340085d01c407980c0400503a41c0803540e6603034528107070f40e4420500c290004072400c501c240407a15084c0c0080560180c45c0c44c1c03891000401041d10001d0340d100351700c112070582d5149005010000b6130b0144c039000c030300070001070852680714010340342004c2c00c0104420104942511001022681c00281c18205074100c011600300b0300e080c0c840030f8000402510030b45d8045040c039800190190b0140950b00d0341c3c842c003 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 481428714 1250 481427464 481427483
    0x120f0b0709061707210c030608010204060818010912050705010c09082a030f0304140405190f021b0c04050612030a05030c0403020612010603050c1e0705010b0405270a 73
    0x480c1600b41003900c050301c10b008100c4501490ba642c5c415424040d80400a10b1000190011141102038101d9000e984803010780d03401808200310464111150340d41c009660040ca84040c0400b054036070040c2113010740104074005003440030343c00b130340c4c00005064020b101d100200451b4400d000c050300d03d20f165229000715a8040c1102e0001c0b01604520308403075020003076902d455918040000b80c10701c00009a02003680d42702203010481050a842242003028060307800300840d003054981108201161401e0141e21030b1502c1c004541c1d0501681161005a40d4030003441441d07685e844a02d8440044c4003840303100c0d07410a40480e031145014282194801d4801000b1481d204030008283c0d00e5410003401205081e800348000000750f200d250041002e00665042844190b051001c042c040321000f5128549080080c0310041051070440320a81c09002310111658480415180803070162202c0003020b0b80007800c01080c480d0721886500010fa40c503503d0b1211180c03440c40002c68070790726000698003910041c1c9 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 481429964 1250 481428714 481428737
    0x31f0602071d011211010e090c0c21191101090b012405030601030c020f0a03020a0311030703020a031b0f05010609060503010b031018050f0624150a0504120f0b070906 73
    0x41e030041071203074030181428400680c7c440005400305604882a0b04010030000b0b4402149105012100c04030000d59240b01401800e5841c04100c1e029a0864440300501500110101c600403003601c2c043d5400d900003880311000619012420b8a002e201e66a40d48948244850100c02e0050280581c1234550f6500c0b400c42c0c2c0d568004402a020316561041540640d420b020324030b103424032656004602a400a1000c824607140c003c02c245982001d00109410034824640000d901192101c44036070507143c40007502d01c5203026044115100e40f40100010704265210f0708000040d0001001c039064904d0400015a6035030600d03003a11107101c00103505400c007420068400c000c1d6440600c614412101c2c0d100644403998806151000404507a030301b541c006001c001c00c01030402c3d65541078000140b2201c03000210000480d01407124000e0901c1400000724548405c148900240e400502160351824070070b1080d420b045d0411030000300c0c1651030078005400510914040e40b1803508607445995000030144 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 481431214 1250 481429964 481429973
    0xf03100e011508010c080c0f04050306010e09071e1e090207061a010201090f290c04091a0904030f030e0a0309180902030a0602090d060507030c02060129031f0602071d0112 75
    0x44c005043c1d0008c03441b0030700010400c0c0c1c5080040038083d020b0f00050100c2418400f80e03e52400d042940560400704413040c00c00e0611030741d482c1c80c0b000c8070384000021403004900200d0a00380c4440c0d03000b03100c0300340c4003007614014041282c02c200301440740c2c1c90b480c01081c601d400049080e20f003400405801000b440240302c00182d041c0384000710750640c8107050040000d00c0020b10b03ca440040e2000d50f90303148081802d00030320469110700c1c001c8810151100070f40003048404038441d22002000038060000c2d84c0580c0340b03010302903003010109000708001da4554400524002d0945466030207110b04140700f241080032400c44a03c00c1c03a0099030000c00811580c02d840e41c070390010758005280c203a0000201000700000031034078055540600096100031600e4040e41c98000c1c50003c05902c02501011512440303810391400c901c440b125441100c0f902952a61241c5000d111000c800d00d00f002e01c036100300c0c80003500e550b0118110713064410369400e24480140300240090f0151003030003108134440c401c00c009070004 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 481432464 1250 481431214 481431217
    0x807020705030d0e0604030b010609090b090615090a17072301140a020c0a1d0604090c0504090c0f030606081e030a080a2315040204140f03100e011508010c080c 70
    0x100805d854075054490341d8000d401002a0b208401089007424180032649050148580907001078407000c880e4134140b0300044c100050b0205413095040006480b50041d00e88501d00c40280102a2410100c4030480c040b140c2d4901842c451403038590342c0c4243d840d100700ca55100c2150b00e20816511b0f1066000c1500c00030281d07034402d0b0060400e5100b4003d0f002c0710340c1c440c1c000e02002403540d141502c0c90255802001021604c005007040c0c1f155181592410000d0301100743c22042c0c52050302c0001b024056441e00060601b00c5401031a40c07803001d4003001003084800c1d0080402d4844000c180c4a81062040d610040c80765904400c000d142c0080c0701c1030300030a11a03040f550340440c1742940440c0c0103410305600c0100f03c103864502e103415000d103410052803000c64440034283c01d0055400b10b1803c0e1414080c1c8070b00b00d21081140c0d01c110101321150100350307001c2001e504041d079003e40400c00c051960406c1070007007500003070348400c112582100090075481231081c840084a0341d11903080581e151103210005 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 481433714 1250 481432464 481432487
    0x6031006182c011a01020303131e060e0604050f0723010c0210122016030c021009140402070b07030f18051018080d0e0304120809010807020705030d 65
    0x3404400704444440034107003501c50703141d0b51040d40000384442150581801202d00040d0b41815903004009004100e00d00e41280d101982c5c02c940c02c1e8825642c2042c41c000c0d0741211510140403141010a0785141410100d09140141e11031401c440484581211654881c2401e1007154a0100762510303460b442c25290000741d681082c140341030b8a032811142d00250340d44038071810501c00508840c03040344400750948a84418402c0b00c0d503400b101803c8880300b080c514070031000c1900444803003401c1802014000c16010130302c5e9500400e440060840d082004043c05a14841d2082402016400703907840c1c1018030842c1c500030342102c41d008240c2e642c0300040e030150615100d500d0641d40e6070080b000c02c16059610301d90704a440b900180c40099030608002047c1e501200e00d03800c1180c845441c14001407004d6046544425240c50045094110520700a0850059520010550007104484010007050b4002000c104000340c0b14a1884d03191500100d0380e0300b42e207000d010340682c800409010042d005000b001e28 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 481434964 1250 481433714 481433741
    0x181501090620120f0711010203040807050d1a0c0d0c0f0c06180506150906120703021c060612050d030b030d180b0408011e0c08010e06060c070b030603100618 69
    0x41080c000c00d0a0703032013603206280250340b04078013154180030481e240e01a090144024030007141041e08000d03401d500c0d41260320809210b81a45070f0018108140014003192403501500304d06154500280d072015a0760249160114045c900003112a14a0243d0340c401088101e5a49004071080c141d681e50006107026092650505010610000000c00800c1704c07c3c801c50001d035140340c00a100300d05210310a4400303499107204c0c0100706808600e04600140c0c01c0e04a0740c0480c2c04c040745003001c04a40c00c21901d401e070090481818408045803010032041e00f220003c0c850803c44844100d40c100840c121840c8081095040e0071075200551450320402d0940f00d288183c070420501d030f82d03652034041b0084d80143d2000c001079440c2d10000450750301490702c4402e2700750146018440d0750020480104608130500030504080081070100d8181d40320b8000741c4038100f5850f0b040311201170b1200400011a0800c42d03e81e84a0701c203032190044507401c1400b8800448561075010f180c92644036016401070040c603403c990 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 481436214 1250 481434964 481434973
    0x601021009050102040501020f0703201f08041a0402091b09060304120216060206060618030a050619020403170a1b121d01050a030c020705181501090620 67
    0x450030490344240310046100b41c0005a8642ca44000641864014202c6c00e00b95042030b90700f0170200d040c000c1c07000e101840a116140c091008540061711091454407650b041160345c1101105071703500150244d011f58055900c0e0b815880011048490f165404c40b0000e412030000d002240510500f00200c03200b281001840b03e04140055002c1421030300111000d4030300700c203a40c2c00c450340c032a014052902d8410b55a11080d605506000011396541d40140560380544800104052400704c19061b040165100505840c13030303002c03c1e01302165503500039101d01c15007000c500d187d28080f030514801c640450b41d03c8580c0c102981c10a910401490b042801490140401100c0c1002c0346600b82c2c0c1c410b4101032003805100c1c00807602000c02080031628000c1d1961070201890003c03400c0c1c3e0821b054a0741a0041c1c50041010340c81d40710102e0800e140c2c3d80c030954000005542000401000c0d140c15481001e9181405039461a020011501a8081e21805c004144100f007080001c1c8403145070302803480704c60b40444 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 481437464 1250 481436214 481436233
    0xe040204050d0605010e090a020612091203010b19020d0c201c1104020301050a14040e0714010e061312050703020307060f0807031b05130b18030d0f05070803060102 72
    0x1540c4154801003100d540b07640b10018046e0380700c00d400d0190002d55100042a03445030a41c04141c4030311410805041ea81071200015920305010042c00100f002d0940049880356550041140b5641100115162001c1c00050070f032401c1c4d20010700380c0e50424847d40c56203480020780d01c031040203c0055000c01c0303100702c03c10200e222545131801f44610860040d2000318560085091501c070303004048000c0d5100b14010001042259500100003055400030130380c8008011382400014001c00044910840d0f50040300c3e4000303546c8002e0751880c100141d003a20341904079412402004020b100d5000c550b00b441d100d0400520490340c21220550885124204860045407070381c0001e0b18003d002c1e070200000820190680e5039540c1e021550940106690030b0030700c41d07403d00b10000300c040080e0340010780c20000c001c10150001c520207180d02d00184864500316649444800c070550314449460010340c0a03101e500c0d04c211006200f041d4640c6a0346c034640d507072800c01c0e01d150764100441d840945814118494048034 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 481438714 1250 481437464 481437469
    0x604060311160f02150c030f1b06010905270319020f1f0b030606100305060109030f08091203040f140f03061f05040b13180c0305070306110a0e010e04020405 69
    0x1c00215400340d1100680c43d43c4920412030307200c8045c8051000694244405551448008160b5019056aa0b12a600d41d038448040100c0f07013210001100c014170404000045241040d400540074807944030030f640103000d030040854201e51140c0d1140710343d988100000210b00d03041d1401050002c1451042d503850481a0108500e171100c018081d0560b9045502010120322040c4500d007a0160180e01900c2c1d280b80040000d9620b81070b084170001807584070702c00100903a10841d203030000f8581c007028020400e03d240c20b00300180e42044103218010070010318018042070300001518201e030122940c640b403036800c002c13820508004070342c02560403040039403112140303583c180001441142e4102007104d0301c540307944d01e600d0001503d0740030600030392a11041062548500d0440e10800c2140100403d03403101001d0648122402001c024242d441d81c0c020102c100710340416110100c07406050b042c052000200804c07500c1e40308010071a400b21b030f800501804194040e41d0a0a94480000d1005007401d40d00c402 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 481439964 1250 481438714 481438747
    0x4110f0603040503091f0c02090709080f01050105030f01060317071502160606060908030406180e010e0708101d04230102120108070f0b0310030f2001020c0604060311 73
    0x400312001d8101080000715401c1c586841281b402954280000706500034a01a1806a8000002c0d00402c0310a0009240e03a01440d0490300406002e8222a0405000b0308464020300d4203008003032090083d0a800083d0b888140112403d82e9001840c1e030640d01c1c2e56601c0b03210140c2c001c1301d044582c4a100d4130f10070b802c20030610103461020f00001c82601641101c1c5080d5040b5a0950041020701a05c2c4c2e43c14480b42d1f000006540030754196007807102c19000f8001040c0c0e2210b10503401071000034042c0001146292450350440d000310030a49a6000c41c2c0c84198038882c3e40c103118090328071680c42e0800c0c0031043c003221203d0503400c0303405100d101042c100807041484100b44175038070000e043e030740001d045019503404801c00303401010702c08050029a0304007402c9450072505481141945080880804c5002ba1030740c0f5200c0041d540001e196000034102c1c034014005083c0e0185802c011070310840d9008544d4008105a4040b1301c0041409180c54240141600105a119070200c090383c02070040b504481d00624 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 481441214 1250 481439964 481439971
    0x110307030b030d140405040207050106050303181318020d140d110f15060607031202071a0c03040f020405090106081207230d030507210519020c030304110f0603 70
    0x66000c2400c03050101403610b003107008082d60f81000716500710300e6140b4116200b41c4085d9041200c0243e5942c81d41c2c100700d8050452a00700544c507000c006050000c40c0407207141130b00401003c4e6042c010b4a030b0889019400c4418040162060001e95055500145800c00003e04041d1203080205089c140074490707a450f00006c0342059010a440f00140054001d042140d11031182c101001080441c0202c040d517501020050410390107010041410000c15006130340740034900003540d02c01c6465016500300a05060483e281d402102500c010224200c14440310840f44a46c2c2c101840c000041d0f07040d030a100c0202002040c4031803d560764900803491100911543c0c048101c0ba4030300c1501c0d0b4030203045c21750b000d94110385400303800c0704130315442210500041b54801ea450001d0400052594036504151640b580081c0761a64400c990070016184083c95032046004485607010340d905680042c245074220310608080075690741c020b1000900081ca8104c200c140c26901900e540720f0504400007155103900240c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 481442464 1250 481441214 481441217
    0x1519020c040f060518040c030b13031206060c2d06140f0103170c10020c0f0d02030405010504030212010608031908090a0807030315180903230307080406110307 70
    0x4044a440351500740103081c03488006080801c50b9502c0d0a00280c0b414241400c800d040c1d0400f400000c040c00b5040207990011508594411003510341a0001d9103515049032045000c5042e04aa021b000801d41c4a1801a1090f41e1105801c4076003a0700c400040136a0701c91150141040c00d000c03001e0803001d008050209511030440428010100080d08070201402403400c445201244010004541c000c45184250103a0325003059031401040c100c0c07800d0801070562280054000aa2480f1040002914181c075400c20070036a0074001c1a10812602c80c1305500c00c40e0700248050106002515010b05802c5540b03c103003000043c116607944000d41181c10503000d02c40700d22a51854484e0b450340180740242e00c500c9440160034204016590343c10180924030700641010303607c0c4480303040f00320404041809808083c00780d00d06500541700100141024641c2140002c0c860b10341d10392030040c00c550001680f2001103c0c10b0855494070421220800000c2c01030f45c404e612070380c990717100c1c101107401503010724040d = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 481443714 1250 481442464 481442473
    0x18120507031e05040e090106030606030b010503160b19050403050a031701140607150e10270507060809210406170f041e0b010902030a0b010914151902 66
    0xd414040d00307001d0506034189003070400c40d2841104582c004221810b842c00c00703134a6180c80d10380030789180c0100b0b4103402c01811a40740080c00300910210f02429412a4021401c80b4044011103803480c00c0c08007076105442034148240518000200c1d0000078200c1503846107800c9090a9883c0c4130035251401c800016001301d954041e090040001c3c08030a203001d49a08503050180304004404201188210500a40240c1c44a2800c5da0340c424a6084107081480b502e044420004182209000805521104040c82d07918a2004d50355846c4190003141100e0300900500502840c1c600d0078ce894450084c40003540c0c1c0990030b0b90958880081c0a4402c030a120500c6e0183c88900b4040c0203080d0141c004842c0c044c050166003004803110000300c00c1d580c016030140c020104c041301380c84111484d0b26203110041c1070009d148004500e10501c0d602444c0b2900d40c1c110144140103600c001582c1c60040c601031080c0384070302c800b0040742c01c1c242480481411403038624107501c1c024022081030400d000070500503006811 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 481444964 1250 481443714 481443727
    0x5090d150c020c180c030a1107050c03010f0e0c060703090506070819030203011206090203071802090a140102060a0c020a08040e06030111030c1b010e1903020607030915181205 77
    0x1e04101c2103090388404d032441d0b990001d0034550403180082c01050010f80038400800107040b07a00c2900540c40e42c0c0c2c00920240d440c3c5485280a0f0f03140e41030748120501a40c40e010088030651000d00410002066a8010788282e1908009215150b800303000d0030f400780801107000080c5501d82d41c00400700c05015a919945036080301d80f800c060440c1c012524070425005000503c010302c49180c0714a035107030388a24001611041c51002c241070450940c002c200701121251140309400079900140500d40d012200b031003120380c46201c02c000c046001c4148500603406040010b40310700325980302e0441d00324a4011254412080c0c1c0e60026603a0080d041008000800700901585007002d02414030610f554540081c250b19000c40726030301c1e6001d1a0f6078441482090000c11440e650203501c400c840000301004e480d0b114802048240e5000034000301100180304150010309010b1181c800e403a2110b034400b000684150254803131102078408040f0079400e04071502c220308001380c0c072807030551000d40490b11070301c4d100e00e17 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 481446214 1250 481444964 481444967
    0x50622091a0403230f0a0e10031e050412230304080d0c020c0105190504050d050703020114030f07140d0501060207080f031207030504080f12060f06090904020105090d150c 75
    0x100c2c2111113820212034501d0b08000322694a0586130300f6009150b040c2d03120a0801011501090710780507942d0060b91886021103044d40c542c010800f00e8429104025214444c1104034040b210f0807640504500300c2120340280c038a210300500d402c5c03c1c610468000810105800203441940241d504980c032a000040207110740c4800d0154420b007010b03038000b902300c41c2d03906800a0902d10030343c41001c0e000080401e2180009001e0350035103014200141c100089a042490b09036900c000c540400c0e40400c201d40302001000100c50202c911841c01400000c40a03241c6201c10f4502043c0400e89216891042c45650b501c503c0c50310401d402000150b00401e04a8075081c0210f00744500315843c461507410402011001c020004105a00421640b800003103039941d5040c11a014003e08190760a02c3e02c000802d1280c200030f01c2c1e1a2402054100c411003051a00c480c00c01c1681d20070000c070260001d145100090140d0b0064003e0250f41c803010740110b154040c16503a1100240380302c0303d03034001207540b0076036036014a = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 481447464 1250 481446214 481446227
    0x7052b0807110c09090f011a0415060905220f060311060a020a0b06030f100c02060601090e0604050703020f0408070e130510150e0403051c050622091a0403 68
    0x50040e0412040420203010b805440b4442e0f007032007a0040c0c1e8000041020000300700950101c0034901002001000c00c0ca0309402c01503101034180c3c610860a2803c1e4050041e09400c01e80c01b207810075141d03442c8103483d03c0103000c4007040554540c5801f401c00e00441c00f801e91103004880004644c9440001c40300c2c20b5250003240c1400c2240e5440c003c00c000e002003800a40c001550030782032900a22204d030b03180d8034980005d1800e070560514401d103028a442078850249150803048245007241c090350300582e14640115040f488510031581c43d4bd5403040810f95504203540a140c0002843c603000d032605a0406100000c1d0740150300a8410340c1c0540e03800c000c2441c1403181e8a4114a4411484a40c10555150b95a6a02c203094202981703a5942d4000401e210b1072078205801409107054801b098035090502134503a42182000d128504248845511010034500c51644074240041280d214a159a103c17494405101c051203885166541d002a01044404150b4810b040c80c049200302c4900c2c0a19000307150 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 481448714 1250 481447464 481447471
    0x1a040605070206060d020f04110c0d0e2205040f08041d0603030901020303040b070903173106031a04110a1418010f03020d060e060301110f03010b07052b08 68
    0x2150000400d04c2070568410101d0801c080c3c0440b82c1144580001c0f000800426021032000d060030000074098004607400702d80044564500e17240e0b40b60038a01e21050040700f92003820980c03004c001e40742c2c545644031119445650014003d18403402c0240d0583d441c0192940250481c8d285642c0b649101d0114108185425a112030705802550a03d144800082d544c1e00010740b00600154500d00000d0440d032043c5d000038015034124218948442d0460f044120541c40702584a412900c1000c450100075100c02d000380f143c40050032001c0e4000e10f4800c084009090082d00751246e65080c84da0060180d03214020051446003082c2041c0c0c3d141b43c40e500240224008030344d400c020440a1180301c6107414140140c9a6012081c00c2454401070900d1080b4003c1c0720b010b80074040145440f50114000f9203103901c0034840d41d000c0d8000c2043c128402c01c292014014145503800c007400030001400612800e4019066103840741088490403040500080d00503900c0310200e0000801100c0c980c44550f500c02c5c002a013 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 481449964 1250 481448714 481448717
    0x60f063f0c100c0f020603060d0b040f0204140910051005030f0c0315010b0d09031103030f1503150a0b0d05070806040201120605010806040b010908010e0f0114060108070c0c031a04060507 82
    0x2450090303071800001c4c01280c8010380714002c084009110781c1c03107240144c2016948245103050510b05031400c002140c0000000340d0080d803900041390701c1c1c00c2448618a003d01102d80040c619501d0000c02c220261000a0009003400c550150020f8991420018590540032890103801a43c40b04028180f410509040f802900588100100040745a210448030140b81240e404111460356050070b603403145543c03201811a04c0000100940e10f10821001402880e8402c00305201e100940e0805a640811540c50170111842d8030200741e960307072198080001da41001c2e080200810103038450030b003001c0b000e9201102a400c104104070856030b00c020001000b0098110030042c03c3d04003c002841040c0043c1124019507071407507000d40c0350b802018000300030002a0700a020226100d50040d40b035012001071070141e5130800c00b035019103001e00500c26106031410303511840c0b40da9079248105c65a0728002c03c2611040e07090303040840490120004102841d8200c00600300c00c3c140313442d10310202c50000707120304c0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 481451214 1250 481449964 481449977
    0x60402090604030803040816060905070501030c200c09070906080709030f02010c02130203070903060b0307051f03060e0c191707120204090204090905060f063f0c10 72
    0x15003a60350300090300c0a80344c100309000d449584078a001c001522400a003408071905013150b1400b00000394005204652140094611007656940103400707890703d42c9002c802142442c4038000c26415822002c955221031039080f200ac103145800860511b03207042d0303080300002e05101c10920000390014081c640024003403522505891444e102ca5042100c0410b00038100400c0010080544d9078807140a17103c013a0f052811540d0303080c0100d018110a005100440d0500c1c1803000310801c502d03003c5030798412074a014040d410707440f180c2c90107011350780078011200c8181599044085042407581c030f2250300c101030a0002d00c4d5100040301103a91100f440d14241004c12a0032400c00c8041c8100d2880c0c9600a450740c1000284610010304200103406250006810180b01080016201940e50896103105000c0c5065130300941302d0001d41c001d010002c44a0507044029036288400c07140050401c4020340030000c11082000c003041011208294a0180100c2c499001c1c01c42c0c0790362460a18080085c5406c00c1c1450b5 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 481452464 1250 481451214 481451227
    0x60f1c1b0503010513050705071203020c010f02070206030103060c110307030215010503011e02090a1206051b030408030402060a1b140105091908070203032a16050f1011070b03040b060402 82
    0x1401c00170044580c005841c3d20b0b4404242c2c41401401034030701c2c056004c0056080b0f1040300070700034025004134000707114960900c610805850418800c0351411034020306000e1a6a095440314009044080340b41c8040045003014254000c13414405829107134030982c0684887c2d64440b040d40502901030b000603209914100000c40c0030421180c0c801c291440f1280c1c0507850f281c402e000078900c06001d0307115003521849004010100007180d80b20500c6034820b400c000a03113000720035940030580802c4030000e05010003040440c1c00b40c54240007800c1d00d40e181d4601002d441d00c82258041c074035442d02c6c0c81200c91031141420016060001e0145950144068000300941107050f10300741c400111851000c1c0020b1800243c900030764900384211101c40c115080a0304031184090b4424003855600c0c500110b21380900ba500c1c0c0e28070885a00c15104a031001010b072000c14050100b00700c8440088041e000500c4203e5542c0a03030b201051003074038000d24107118110307140d1500e410801201c002c01400e5038815881000274 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 481453714 1250 481452464 481452469
    0x30103060f05090a03030c0905120114090d02031602150a05030f1501140304020a09060f14150a030510051002030a1b0503070b07140712030f09030509060f1c1b05030105 74
    0x20f2507138503505443c02062140c80c04005560803031035500302d1500120248136101c50ba6805421454004000c0320000c13200342d8914200c0c5440f01c6080d45641c0050304100129141e454030b1202e1814154001080071340340149001c41880c0641c000e881c0f40001c0390300802089520b40e010083c6070741c021300c000110100d0348100300000f03080309200c2c0c1042890703000100106082d900d4034031118014100712482000516100c6803003c41c01091441144000d08034102107465508002d0802d1454116101307440b41044030703c82098014200c01001201c041000034000682d5a45e4410903034180800341e000b07140d41e2014414002d00500881a0b0f9456000c889007507200020000000c4032181030300b000080c41d064940c0401241c002070380c0b4075400c40d084001b1800f08103214240c02480310400854500300704141d0b0080705102910070380704010b4003040007400710340b030a41461001442c00c81c4018000a2801451a04043c0540090340350f85d0021950780900e42003500583c24160b1325109035040150556240000 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 481454964 1250 481453714 481453723
    0x609010c0813050d0b01261908070605041407082a040e07030b07170f04021203070f150509061611030d02030c03060f1509060d061d040c060c030c1202070b03010902030103060f0509 79
    0x200e60619002288c03800301400005420f0310501c5a1050041c886410942051a09000311080e018628000c8030340005134144005040883c20b9011014048003480154420580c00c0412a01e00d40243c2c6406442408500900c140b20285104c6c0c103444005050520006040031032080080301403014400c180540c8000500303409070b1096040358071804d0400201072580c114042d074500100110482280002005072501070703c2c41d50340c800c0c0820007080d51100091a901d0000b5035141d05503841400758201c1e510310401c0c0903054a01d0150840380740030600b50803203049074422a4181080080031040c030040e4688088104a6400100e90003d407152424071250064072680c41d250340b00d1000062540540c00307003034110400030280800740403122907079140c0e6403409660884044070707213000c810f10100b5000d0242c651781200703030b400d596590000580741c0d8039841d000c480e00224406622500d00c002442d11501401107018001039100907840e07515510b445010b42d00500d407000317100c9080904003e030003240000e = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 481456214 1250 481454964 481454983
    0x30102070c090b0d0206030c182d03010204350102030f0705031005060a0507060c08010b1b0705090415180201052a010c0f0801050609010c0813050d0b0126 68
    0x7600060300c00c990b03030010300c804c20145002500204040204801c40c414000906120b0500e401941940070600d020032560b00d483c01e01031040b40c201c0150890003800e541c460f81100007005000181b5042d11021303c0400b4035004107003150f03944180800c110340c0c00200000a820701030072a00a43c21818102d07181820584010b201030100134010000a6055481803103400c0104005000182d807140700c103800402c503600c034007000d4414034184440d0100d0b40e4840c0c00d5003812112030017407050401600410100c09042d0b0080f2240d6144151200441c142c0d64a0852500862040081d490081c44d020150070030b40b6241c4801c003005602c15581d201c05070340c02c407003140d2003c00381c07501900e81e01302e00d4000000c4801c403211100d046076282c8500c455000c1e070400074000c0c101c2d1007500c501c1d02aa0faa081006590b219111a181c0003030505050b910000e0200350180c010002d8920089078050303110702c04540303034840801040e00c0c4503022400410084920098210f0200e0310b0740011503a018041c0359450b985c1c042035 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 481457464 1250 481456214 481456229
    0x1504260f0715030b09010303083403020f1201080d0f02030f04051c05010f0f0b0607081207110a0f140c01141617030105030106050108090c01081302032a030102070c 72
    0x5818250b01a2090703011622031140207102201ca940c5030704000301b60201c11580c2e42103109003d030b040c50303990000c4000d40d0011504038407c03829407142075204401079080400c11a03801c500030721520029068400c04603018140810041c4400b000c80b000080c5180c0000050406640040110011658148007243c00307603007060700c100085481403c007a0006000030a400741007940303014880003401d141600f00074884030701400c0c240040c118400802115208812005101e080d0400c211240c24600f0780910354401981e00b040c0880c0015144540c0c10700d41000b00440c3e882946036900000c0101c1d03240082103c040700e40090407094280c10010300b0044071030a214481c110086141d0000c4803a400c3d03180540b5501c0003140e240504000141115a00300303000c0e43e03200c1d508001300031403907501c2202842c0c80707000224000c01344021200015070b00d020028010007602c0c0c81e1340e1075480c056201007114088109001c1b41c001c0c05881c5003018100c840107020f607400e00c80d900410400002c10300e1030b400310007982c031103 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 481458714 1250 481457464 481457489
    0xc0c030b040213050a090204060b160213140a150e041a0406020903030c0309041b30110309010b12030714010f062405091e1504260f07 59
    0x7240005404482d6001e618a00c00d403c10702080380300003142e001003041074800c2d2000e12586842e0545143d8a000d01c47c15900c9400000c28518003503e4046d290703241d42000c3d40030000303403810002490319804008030f503030083c56038a031105200c141005210500040482c071041480302d080907925101c0701c10300900c103c250300000c0750101d001e00001c0d034121420008024122607940096200311505e90f049038107020301c141c1c0b070b22000603c403031031040e01407401c1101942d030100e081060600b9842c42c403200044500b0103c007000b82e13804690925100f441013161030501c856480b4500a01001d0039560a42c2459020300100c01c0e4030040000000145c6002c1d990080420790500c08615042c0c1c01030002c04d2101072a01e0408400090100c5c0903220100d569039015060381020340e54000030350300e170701c0340b11441034100103c0e0031b8400c1c510000301c25050044e840100b056200303c80007100c500464000d41c0061040301109114880c4540307030380840c0466074001c2d0029080307006130128000c3c7c80d50035910034580303038554 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 481459964 1250 481458714 481458721
    0x803250201030b27010b0a0c120311040b0705100b031009030c17034204020d060801020904060501080c040608060316060206070e06070f02011407020319120c0c030b 72
    0x81c1d0030030400740d0800f03040c035031403c03904d0018013002045440b040c2d90800c20410010a060140c0001c8484446580d290540d159055648107045c242c0013041000800d035907602078451400c55040100010065952656180c800c1ca05006090151600301d41443c20710f4041156116180880c00c0110720800000006040c0c160b404d09558400304088014441410300c1d0b06c06030740702d882102440c05140e00d04a40e5607900410b00e440004240e8204002000203140000901010034500062481010107440503007800e4002000c10140d07111b6400044072079401007254803813030906200b0200104400d02c0c0003a0b039410006196450351003680907000812000100050b100d032420855507403051101400c00c003c059035500300a4507404155000c000003060391070181c0c01072921a06440340d43d60014001c05045102c0c1d070041d074400c129030301c00c90744510042c05010056034050001031180c5e0248400c141940d031080c9031403030412079143c1642085c4403000a94030041410750741c050050f070390710601d00d00301501c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 481461214 1250 481459964 481459967
    0xe060301060803070803040309060f090312090b0c1506040603081b031b030c060c030705030f0619090b0f04090b040f0201030b04021909060201110f1b0105040503040f0803250201 78
    0x100768002d9411031100203011400c201511004505c524069543e50080548a100480e40307041402501c9000950380081807002c245042c07e803454802c2e07507042403070310555141301402540d04204e5051841c0c0e00040f290110801c14484541c0e4880811a4108806400c50352000c080b030060b14080c803040b840d07020a00346400000c100300c4290480c881501040d0020240340b081c0d4a50041070144100d0080c1d00210f03d6003403c00d82524024806600e810341141c0d100101041c0000008001950280c080c403180892100c0090001011748550040030440788010b100b4040c445416106541c0124505660840820b2880c0c44040e00503600c1860780044820074001240681308040701e0b2139200788002002d0400601c615850100c0c11280d840e0f032002300d556050140d003241e0303803030312541c0466408001c50101c0003018801020190f004264002d0354030303103856825003111003c87d4100c801d0350001409004c50b81e40000b0040080c501c00c4003c500d8000c1c20b5600d0040c040c81c100000c4054003242c078601e011603 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 481462464 1250 481461214 481461221
    0x120203160327080712020703080a0507020a050603090f06061f1d060f0403060b030a03050a0e0d050102070b0f0c041d0c070209100501030b03060f011707150305100b0c070e060301 78
    0x2d503080d449407081c403000c43c1000d8225070302020341150801ca009094201c2c907030010800c44100c0741c01060440c242100c0312402c0e100d60740a16030890344111181e4011415581b8980554024200134000701503140034021101d04d401760203400d00d07200c0c140310700740d4088040101c019150894120b1a00c1d038010721450010b00d220300c069402490b802100071841219442c81a4040c0c801c0301c0c0240b00a100e10481401416141d013208070014000640400203070248a015540007110040040d04089020589484140c00ca03000480101c0780740d02501c06020314110f040100b50b41005040c400c0701d242c07910b00f001c6001444000e4038101c200702c0640300043c24000800041d107503c1500900f26410750301e0300e000311804114aa0041901192401a10b100241030009075640703d25030300190841ea40c1d00703200000f4500b04401401e60800e109166010031003011100740140c4682c3e86840100300f504080b0317043d40160086070000c04900c070050001040c076400001c1c46a040390202a5040c1c0951500004179014 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 481463714 1250 481462464 481462511
    0xf0f04090203010b0a0f051e0a0912050105040c0f0b0316120c0c0611040e150607050f0706020717030a03050402060f071118010e0f07020a0b0f071202031603 69
    0x492002c0000190306030200001d08941c205581c9280840e41004400d440c42d0054003803c40c2a40d40e019580030858541000604200c54207062601c03405681d01b94651680303031484800c68240e51503005102c208800b4000740700180500101d10905541040300c00506070000400d0040300c0c5900c1800403071254020f810070b10054074041c42c14002c02441c01806030800343c90341801c862062a1000c14000a50054260b0b4282c034060b1000e142142c442c0a00b900c0b030034040324000b80e40000100040c000040f8200900403942d040e00000d02200c07031130000081d00303120300b0ba800007419498010b0500d00041e40801103401d00512400c00103040c0c0c5841c0023140c540d02810803012a29140000c0100500008018005144000715072103018042c102440c1d0440c46420300c201c0342d41c6400100890000c07100c2080d0039511140e02c1c811507920171025107484400640c03c1d940103504640034414017a0542c0e10400403850801591780652a42c180fa05100d80e4140c0301c00290070401d9550755021605201d0304180c604c4 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 481464964 1250 481463714 481463729
    0xc010f08040f0803040f0b010b1e0903012406120506010905040513080a020c09100510050703030e01050a0203090114040203070b0a200c0316050f150918070f0c05030f0f04 75
    0x212860540342c841c03204081b00780180c2d46039550300000101c44120f00100e0303000c20f101e4004075159a6003a103031010190026842c85601d5502c0d4018189001511601c4d04440034110ba0001d0100d1328114000d42118100080750701c0c0345040c001004003590300910708204886d81aa8000f070686d5400302c2502d1080386c10080200a220000344082c607190340000c542041807002c803172072030241c0c0b20050081c00e004051700c11260400d910076000d40203103001d00040c00030b0314040d017030100f8000700c26024182103c604464040001c0c0e4003000f4801000002d1245209000301c08400c2840340c10035800290f03681c2298400c01340708082c000f0f4107030581c0d44101c4100040d21090a184050b8004c0c51020740e03100e2074000c0107a400b80c41000d8100342054425540702c01150b074050440c00015074004117000c0001200380e080004164108413039030007929020049a2591204140e40c40d060234003da00802c1c0c0c004070505401000100010342010510100131101c400d000b82007800e54030250f1400c24503031802030b64010103 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 481466214 1250 481464964 481464967
    0xa23091509031e012306150f0409060b0d14041a06011202042306040f0504021614060414030403021f0c020d080c01060b03010605180303040519090e0c010f08040f08 72
    0x9a8403415044101000345e5403404000d100c155104043c0e001d83c080300e03c03030761142c50380c810030800156103001800025903030b00b030080ca010b848204080030b5980342d600401c0702510005400050382400d208120081d065280c0481d660708051711380c041c01c9240d81454100001042c1d0220f6810381c010040a01c2150340c1e0b10b025501c55503100c075003010b80092081002400c262907041c022080c51321000f21400d8640c1302d403820405500b81010320000b034004401c202e0f841000104848046040d0115581d8a1440c600080c4100e1402c1d10305034520399610305101c9002d40c0140418001a981c800c60070030a00070410304211035a281440071140309940040194106100349800428401900000c2100d582050001c0c0805681c41d1030030800391200740b03d914001030042c40180c407403010452000d07000840060459007490780f5080094000c5414044045441820800401540613580034820041401340098000103040e240064aa0b0a00355010740400504400240030000181d540d20072550b084402203 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 481467464 1250 481466214 481466263
    0x30a1b050409050a02030f0307051005100e040503031b0f0a0c0c05060c2a01141b120c37080c0102070f03030b040b130c140a2309150903 60
    0x161904131031401640039005583d02220345020000460b821981d0240c028a07581c0506040d1a0003040d0241c008602605910400220b91505040c082c0c05240100d0180d40c1c2e81c101038216001601c00019024212030082c05034034103180114058818030070003818160700300b42c25854410044046a04401d6210b1350108403801d00f03201c00200e0b40c071a25040c005800340d10402010000303055615031001030008443c0c10705041d8002c1d940c4068819000701502011000a404030410700308040c41040407520040843e0f82c6011800030811840e001381a07001e0021001013910184076000520500c404440d50b0090511040000000407030322101c410070000c64030345582d89080341e0050b40304501a000039080a640192a00d01403142c0304101d00010680d01d00c9400e1030001c400039058540403001800b100c45106070950310032a00400d1200310b030b96100074000f001141c44069006c51018440d001d80b005000320640d0b51203040d01543c411100740b0030103899801d80d80c00286000c2040050504503002c25650 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 481468714 1250 481467464 481467473
    0x3070615031203150302040902041503050105070e0a031203020a02030d050a09031d0a15020316050604230327040f06181116020f030a03020d031406030a1b050409 71
    0x80c0080c0ca10804100302c0b1101150011015920700a0030124100b41d460820401031a0592000d02c1480c0b001e0000300e40c9514440c001c0d00c031402540c1c030a4604e65100c4041042103a840600c001c82003004403401002d40b402c50f21481040b00d10010882c050640c00603407492280c1c020025941c0b03c50040905200c1c91602102c0d24001d007903804002c40103c5c06294400c01c1d1640701840052940720b02130310070140c591410301880541c0f036030b007100c0c4010350000700240041c5401c403008012070306004000515490409107800c030301401001c540840300301000110b0401c05480401200c10309101040402035481c1c2001041c0000031150424070f1b0300625080c1d035090400e880340c0110040700c4088a01d1290305009c41c0c1c03141e0655103403a1709241442410401010083c071110304001c0240e0014021185115000001c43d140036485001980941d01010107514000d50500801e600c980c0d40c3c101610150601001107650b9824480d0010103140034a00301800140140e0210802010010020300c40711040c0d040 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 481469964 1250 481468714 481468751
    0x1503020a06180902040b22150306080f06040f03050a2c1002010e0a0215041505030406061509030b15060f0c0c0f01050301030b0702120703080f06010906091502030706 73
    0x1000403001401c020001443c298620035181155032483d40f031803420340c022240d0020040519511030815000350408030307620500400d00320342d418150714001449030800c00310b03c2c41d000000b40803003502c0d440780c02000f0001d0303050002d2014059060a110317445480d19042656105e041c0754003013003610b4450b45888000d55030108020001c000c00c0e42c408000200503070f412030070390f0750801c088082640318003541801410200040c030704400c00c020099080645403001c0305d1310050640494400101d020092209201c0b191041400030400c5031101908040000b4020b003524160388000390101080000007940d0041003401c00c01c01501c020301a690310700001101000b2600300c903900c2669489032850306106410500301c00c00c0d504005846540c11607185a071604074030400200208110302a510061780601071140c0600b190a00c01c3e1181201864240c152110464009114504210401c80204105500848003005403901c5180900982c03039241416450b40c4540b00c40100700038540159211100b01901 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 481471214 1250 481469964 481469987
    0x1508100603051c1218020f04060f1202061c0b011206030201020c011103130b0a030e0f03030406090f0f06060306051e180f030c01061401020a0c0e04060605060c010b10110c041503020a06 81
    0x200c60f042c0d4401f0400610046078101c2c09070102181482e041840b00300700001304440118401441c01c2d1500c4004489041c054100c4000b10f48c40a0f1204c420345401c0d0382120340c02c3c00d552a400e0081006d2407840e00000c1d900c9443c204000d044c8228403140e124894014000c5a649d02552280138052a50b50174042210b40d1082090b100042d00d0001101c05401c3c0108055111324401c900030b41c115280d035141d0030001d0008070022544102d400d61030b0f40c000707586518907940b624040c040c0007402d46e19506221060760002007400c0401075200b044078205010004400343c000c494104102d00c182e025840b800d1404880000744c1c180c40c0700c0410100b02d01101500580c064400c11482a00300c100d1210041e030792105450402083c04003110700c1408000c1220621541c02800781502051065440c00851000c0e407060306403890302d075180c5a030310383e0702c0c140156040740c914114601942ea18180c00405d584440544005500c625280c6401110100d600c282ca4005150008d001c1c12001d41d4a04d40602002c0750f40 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 481472464 1250 481471214 481471219
    0xb06090705280f030612170c072d0302100c02190311030106080c01050a1419030207050624040b0a030602030c040e0f1b0309010905011508100603051c121802 69
    0xf00200205680300b405003004440d03055044001c004059520046201d050700301100e9840307814800e081501c9004c11500b0000c10552002e805038111300c1810460900c5a42c10351100005101d0007003005071148010590409950f207080c040f214000e1001a021900d030b081c3c20030000c035131208044140020b01503618000c21003100208860f954078902503460300703401c0020a0104034180f00c2003040f82e0084540304d60b040d9580c0d80e91840c0c0f000c1e44c801c5c0607680109610050010b0340c042000701c1042010040c00742c1083c0000410724443d03400030f0032081105410022140641d4640364014600d0301c070040954080d42e44441c055440b40740ca1a400c04050304244a0426030b02101004524540b02c50b0207064052405055056401c21084126110391741c0080e0040c07103959038a54120001c11000c1c0328040102d107444001c0e412480c07801842c2458080b40340e00c0400d00740c0c98044200700182c00040c01c00c1100c4001858100c0c02c0c4100e0f00295a043c49101d40d03001c00a003040c00035403c42d040880e6540342c85108 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 481473714 1250 481472464 481472477
    0x31e0204050a0e1303110c0a060e0102060a0e0712020103060e0403080f0106080c07030c0f02090a0e010e03090d03030b13051906060e0108061507050f060109060506070b0609070528 79
    0x59042d680d5100c01c007516004c09502c0b0040740c0602092040660196030700956040b10400b0145a0109a02c0704403a44030301c000074201542180e156034184940c03900700500720001e00132101d8039008680c8848052013100541c18245000038216400380e08520010b00740010860801c1c0b82900b0090308880c030485102c0d007a517183d0000469140e004049190051140c003070131504100290b54151143e092009017135a4051201c401100107030748112055100c0c1d040003101241e01c021041c0501e0944008007240003041d00b0502001055455080541007510380500c1d020031003020032400720b4044080780309050340381f03030901e02040350701c030302c0c1140c42c44c0b03002141ca02c1000140e42d100011180c00c64861691400a03c4540c082074451900607003140110a0140c80c840c945080340d52240d00e401c0d4003c4615900e41c00c0940104180b01240c40f0f040700411090319980d15102d1710355200c40e1543d400405480c81142e018000c038807098815010b4403102240c0c246084103400c84034480b11640c030b840a0507000061031 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 481474820 1106 481473714 481473719
    0x60b03091506030f03030f070513030305071511090d08210609010806010e07120b12012c1b04020702040c080108060901050403080106080601031e0204050a 68
    0x5100c000c10700560051082088460010a250302c01d800c00b090b505401350010044960020092405503c40d03610200b05903068054080041c2000e0340e86000030040680100041400f02e02422190201c0e1758075002c103000f40c610000321032001c0d51060091a05a0520800009000e0b00c0340782402e003400d03045110b05114204400011006108410a000c1c49003841d400560140001801a001d2907042001040e041c00c000350400007000f04100028002c1682035010490004000701140f401c13040c120f16040c0030780f8a100d082595048622407607451103031814800500d07500c16001a250081d03024245a0951050582e0349030016020001000140c0d181d01c1000c1c0c4c80704443d00e030740509504001c0090701c0c02074005c1c000f01250785480c040c040820b80111000d8112251403401c2c10700c40c0c0d10000102c02038410a01d0844442107075108540c19031000b41c001d03006566003611900d14055 = true := by decide +kernel

theorem cover : BRFrame.Cov 481294964 481474820 := by
  have h0 := BRFrame.cov_init 481294964
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481294964 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481294964 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481294964 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481294964 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481294964 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481294964 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481294964 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481294964 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481294964 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481294964 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481294964 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481294964 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481294964 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481294964 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481294964 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481294964 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481294964 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481294964 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481294964 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481294964 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481294964 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481294964 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481294964 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481294964 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481294964 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481294964 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481294964 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481294964 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481294964 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481294964 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481294964 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481294964 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481294964 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481294964 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481294964 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481294964 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481294964 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481294964 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481294964 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481294964 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481294964 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481294964 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481294964 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481294964 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481294964 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481294964 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481294964 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481294964 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481294964 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481294964 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481294964 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481294964 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481294964 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481294964 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481294964 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481294964 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481294964 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481294964 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481294964 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481294964 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481294964 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481294964 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481294964 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481294964 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481294964 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481294964 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481294964 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481294964 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481294964 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481294964 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481294964 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481294964 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481294964 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481294964 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481294964 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481294964 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481294964 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481294964 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481294964 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481294964 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481294964 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481294964 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481294964 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481294964 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481294964 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481294964 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481294964 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481294964 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481294964 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481294964 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481294964 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481294964 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481294964 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481294964 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481294964 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481294964 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481294964 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481294964 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481294964 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481294964 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481294964 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481294964 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481294964 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481294964 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481294964 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481294964 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481294964 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481294964 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481294964 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481294964 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481294964 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481294964 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481294964 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481294964 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481294964 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481294964 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481294964 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481294964 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481294964 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481294964 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481294964 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481294964 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481294964 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481294964 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481294964 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481294964 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481294964 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481294964 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481294964 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481294964 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481294964 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481294964 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481294964 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481294964 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481294964 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481294964 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481294964 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481294964 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481294964 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481294964 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481294964 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481294964 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481294964 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481294964 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 481294964 ≤ n) (h2 : n < 481474820) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
