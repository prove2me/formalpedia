-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3216
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:00:30.884984+00:00
-- url     : https://prove2.me/submissions/62e18e30-f5d6-4091-81d4-19b8e6820ce6

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 578237410 ≤ n < 578417266 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 578238660 1250 578237410 578237489
    0x6190f0509060c07050f060f09010804030306051002070305060115081302030a0503070b060f0405040302060402240d02040806070804120302090301110d0c030e1c0c0f230115 76
    0x70300041034952101904407008190000c0c00d0031480c0005006401040d81750807401090b08016042540d1400c4c0d0480d41882c0702031030580c1503651641400c030000d00f5560009a030100104046040380e65000500c1010b07280108241d030526603a40c104040c250740c880088602140e80840084e071140e40156115122500140984c0c10100180e1303a03d90955115401c100d40141c22001446840c3c00c03c1480c100c1407a205850421041c10030740c8010796103000041c8000d102e401b1113800f02e64006204a00a002c002008541c2074980e200c60030701e540a0741050041c084507100da00000348945109542090145411407030301c104400071014210040d503c1100a203406641700d80100607038038003590082c081e0030407009001076180441c4030300400380d4401c41031030391301c5612038012000010501c904c003800041182c24458581070151070407060200c9103c0b40580007d5404095001c400b180d00300400c107078552200200300b6091201c0c620b0140744071902817455500300c9171095945000782c0340100e8072040100c18 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 578239910 1250 578238660 578238667
    0xe0105030c071b0801060602070308030c0309011b0302210601140a0509130b0f010201060b0910020109171b1c030b03030d0911130905100b010c120305010f0506190f05 73
    0x4880003000303504048803031603c0c2010301040059500c01c1c0b0485c405002544050007850f461621244650b000c081c2200d90309520000100340d0400d400d5015a000164181c02c00a2455030601c0150007034004040415803200029020300030651760221740c2d031082e0030507100d50403455850b000c46007844d0080c0720014148802040340900c42c0c0e848141030f82ca5601142804507000e1000d81c20b1001c3c030555242103505680c14590180000000038083c0c540c1f421050301c04200c07140b010313482240901a80030002c1d006c3c40001003031080b41c0404c43c004003281d145030420703910004e14108455a895030040f14410b00c03900c103010b6207004188640c10289080100808990402c0d00c560443e508a51030203204585c130110b00880f4410301c4c1800503100390001700d041001c100b845060f0301d845403100d0180f10415042940d4150001c00d03a03004014001c0000d40064052828403040740004d0b008200c280a419106803008000103540d181200448080780383c128a6a0324550f209070098450400b01101c800c180032090 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 578241160 1250 578239910 578239913
    0x81609090305120108070612140601030b010201090606031b080a0b070804210c03021902010c06020702220e06130503120613020d06170d02150a1404030c020907030b010e0105030c07 79
    0x284a4045d01e0800060031a070f0340707080d5024020b62010441d043d4540e041911400d15505000740b0603500c00c1c0c080c2004200f03000442e004030b004110400e40140490303c2c0102c007009128003144007400001d020f00000310000d0300d42541e01e81d11001d500c4001d0401c9400000107588a06c03880205802a20880500c0e000065000321022514000150303a000500308a90300f100341541085411010041c51015400710361103070b00002c00d098004040900f40c140c000516104640703a408286214000401140048090011892000e0900300b5a9490507109040124215800d814025042c650380f0000441c9001107490741200e058800038803059001c010342d125a904c0c81c0c814002031107030f042c5002002881500b4249800b440b170394060501c0310b03558416201d5a84580e00018000d024004a5a0f81c4003250b071980c1c840300c06801c6a107040350f00d85c04460148010950810a251a6540b081390340340103540e1059030407004c03102402001800280300c4c5c0ca40700b1855002d20011074104003154102403410309a0b = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 578242410 1250 578241160 578241187
    0x106030f0603170304150c090324091202100213030f0320210909180f0d0305040b0622020a1116080f030f040b0f09090f0a06081609090305 61
    0x3d020543e000d000030800041110646504403402c0849004000310250041d00800c071503600e01000b0591a05140c0c0c00c0d941203412190014000c04000d4107002c060b8061030845901034071401c102c00984103d42010000a2131345c000d44803071f592040d44041d0402c0c0343d600e400000f00740c0c4140039418403803400c0c4460220401c03030307600c0c104e0302c135601000b809280b03501d120380b86c0c5d41c91100e50341d051a82c4c41800341c0404c81c0d850510150300213140521307883c003c100841381c07a070a00c2840301d039240ba10301c503090428075915095088180f195000d8500302c05565680024410950403440c002482c5c2d00440b12240c02c61a815405410510340501c0d0004440c40c5200c00240380804080442d03d450090303810070095800b04000d00c450180c2524055807d002d0108024462801075004800d2030000105010005200303c50075160000d40041030755141c2d080102c141412140142e4001038500e06002d0041a0b003200003d0b1020300486941070001e030a4600300c04200100070034803048040040801420480000c0d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 578243660 1250 578242410 578242433
    0x90f0215090a050109121202190b0f0a1802010f140708030a050106050705030d050c0708071203180302150c0906040f091811190f0806010f0f0506030106030f0603 71
    0x6000003103950341103000c2009071003006580018100040e01805004011407000c00413961641f0544101d0031b0020400e041e42000c0020303031107240143c90b08680101f0300c00c0080701d0701d000c2c2465031101d45058403840913070b00943c0c81c0c10720750341c3c1465500c00803c801540308641203c0c050009103001d1150840003488985568404007066404000200621910041034812140100f100b030510030314010090355030944174061014001d0f001d95607800041c143c40c11040c103e50205c0ea012140503a1811760f8034140c02c2603590440004002440c010b01040d06c40512081e07030401c103416800800c0b01c002141c8585e642140002c050f20030b1b4a40c103101848050311181c02400c0644800703001888800c0c241220081200c900c051300c00c2600c0c83c540306070303008070b00b031002010b029500070740300d1541050b903003079408910072010341c408114100c1d4004005414200460f20906076803010391484851555107007400d010207214026141e00c000104010441d15000f980701c00304142c041d0401080d01070741c0b502e8a800412 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 578244910 1250 578243660 578243689
    0x609120c080913020d020414030606102307060e0303040314040f03080c010603080a0908190c170f1014131e0501180308010918081e0c19141f090f02 65
    0x140c1a600b41d5600c0c0740c1485052f50002c0c05481c207010a02d10300c4001400c2c1c00410f0680006142442c03080705e0117582107011944502d0f0000e80500c56000d2001200da640d900403501540047c004103c2031002807540012201100d2444100460440c00e40d180c00b0309903401030350640d5256685240000025a40e80064401c4003d40c0d16510419032501200740c1c00d19041031191034000300050700b00000110b420515a007911a0422549003a50510107032500e001208034000f0749511404844251441c0a030304245021443c60800051070f4460349444402da100d240c130000e0170382e5513128400c07141c40d4850030003080e0740c0e00070300020848180c1c1408481c40c1d80407a15050700080e96147c0148036a0300c150181c145860700c0c00e03c288500c0419900d80c0010780c000c0d100000004956804c0c020890143e1310300b078410b10640c10060310501014032a0300440c44001940c200c90041048161130300414010452810084070000e000c2d4403040d883d01100d0007400317a00400c0796005c2d2100315080150b00e0b09003512501d038 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 578246160 1250 578244910 578244929
    0x201060e0f040309090b0d080711040e0f011d0a1202031207031517151005040e0102071b060912060608100c020f030a020307021c02030a0609120c080913020d0204 71
    0x1401c06040c0100103c4c1c16400642400b030400581c1d440c1619105100d0100581050026403518641c1c544002d07092a10612b40e035006007880c000c4070f0b0301c0c8408901058080040c038000c1002074003600c081044052244d0002405030040143c201c08103900480e00c00000f403907881540c1c5000d09541e03400600c2d1406840d8403001a6a4010724020800361420f03601c0580038070ba10407281d200b105040c01b0303610500c102d2078905074283c44003c00c60700303800e840401e009070000504c00d100c64a840c920040c004e4111440560b001144080710480000c150403130034065803815a91514a10300f031407600e200355140002d0848083d41e949400282040040c0891602540d404101045681c00a42e00900e8041000304020182e0400c00c81862481d03000000c03910416815034200c0c6440701c3c10b075003210035190317401c0c806500b5001e041c540c1d0080004540c8074201d07107441003084035400032603158221244404490014411102040410300c1d614104120942d1700703902e1000035107400c160804d007600f640c00c1503009440d007 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 578247410 1250 578246160 578246191
    0x11040f06030b0a050402010e3003130305010905060a090f0b07020a0b0f07020607020325020f030f10060b0307080c07110a140a090b0901060507050a0b0709081908090609010201060e 79
    0x11903900821182000400711250049800003040b19694a50009c0c03030030500040e10300043e44100c100340213444401070180d0301c001c006592402c005018080d41e0400310b80c0c6024490000e0551030013403103840b0b03d41c0d42010818000d451159601a4000380141c001e10543c454926000c000869025296203d64090400940c1d03904050b14041d15000000c7d01d10002d54100740100d18400c0da101900494000486a000b80c0580781400801c81760700d01c4d01c851503090b003d9144110202c11b80084c04880321152140108030031503a03564241e88600050350604005400d01d000304d00024443c0d009044506c0c05464007402c03103500e083c00941c144165038030203101c3c2b0b810395140c181d542c64550f40c0d40d030003000d422a0500111000c1e100041000707134140112f0060200110b411400d0040811458031080e0348980b200c4c54a00305040040c04252251140943e144500c2c80d040c03031441105001441c0069020020303a04183c00b0404228070381d0007500500f4119940c900c00010a40c18843c02d40703006100c6076078403400 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 578248660 1250 578247410 578247413
    0x9150102100504020f010c11030102030a05090609070e0a020906120a2403020a05220c0507020a15020c09090c131b09030809012303190b0a0311040f06030b0a0504 71
    0x1d060501c0c65a108251901e0208005a00d41c0680526050b1017482e260f07035a84061300e44030320f1081404000b00d4040d840482002a0072201e41c4c40750340141c4e00b483c200c0c1d00941d41c801404d03680760050b0082c03050030700d4410301203032075001e4680140c8805a002040f260a2001e207151b4499040340032111400c890f900e404d1103001c80c0b18031a075103644400c0b904911000d960306540219400505a10806002d52552401450808135a0740036420048075030500303020741a8000e50040c41034020080c1a4480c8001e01300025420340c80140081d14500c036a00940381019085041200d903881c010040d12040c01019201d041c0350b030381c0510f561100300462500081d40301c01804a00003100c81e103101d0000f408480344c01840070500301405d940483c1380919000408032007486221020001c01d2032401c42d8518080107000019045107841042c151a250040260003540810001e65050f64403000c0e102c46501c00750741c5641d0800d60019840c00144000201e42d1a950b9a02e02c080010100d0740080529a01d03000e000 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 578249910 1250 578248660 578248663
    0xc1b0405012108070302150109060f150f0e0303131215050702031e210a0e0115140d0c0f090606020303271e0a03080c07080a080406090209150102 64
    0x1d002d4621032210321150700686007110307012090903002030012040840c40b02e081610800598210442e10074030b504082d6074031190706010b042140038690103007500100105018582c1c4040041c0d041080c5d440901c0700b490a6001d0780d52100040310141c040c0400c010700c4d1a81d501400e0700c04000d14200004030440050b034104201050b0440c00500d00305400c0600f440f000d942d000069420349122070210100d0240340d80783c150400c0c0b040b000d80040c0000820710904a6006030300000344102c00c03541c1d0600a64154600b400c2c221070581c0809142054003120920200c00c020b0039200042d50041d088082d022216241c44100d06410b900100d69036140da801441a103010b80074000c0100036a00055085090007411310004182288800e401c182410700310410060013080015102c440345414502082d418500309901e40322007800583c0802c680304081104007610004886e940c0303030400400c81c03c2001d8000300301e61401020f00150780082e02c802402c4090b9990750041401500c11040411840c40503e001a = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 578251160 1250 578249910 578249921
    0x2031c12061e0e0a06030b010f03050c0406080619021201080a12050306010f0302030402030109020909061602070e0105060318030a1806050a0c08091804050a0c08070308120c0c1b04 79
    0xc0e000d09005040740c500510360180080607034811050305951130b541c120039000109015032015000b422050000104190134050746400c1d2802a0103071000b06001078248000d940091080c60b01c40c4d4021000190306082026691840c400c94010240c5802014400074000790b10a0300080a90b0b00b1580110040091312200c40400c25040d042080c00d6242c1200040c000c240e1926110040c544c00000080840da800e51154400c0c5900605608480c1000101d0359039502e41100d10307400009401151035100e41c0000b038098102c0340783c1e440464250b800c02045c01004c0c2c102401d07124a45540c061402d58042081c03016150500280c0d8a60000d032020500e6145810803a500c01401c0c440e0400c500b045a6034890300017043c0540204580342d036107440340c0c0030a032210344000c0a29001c003104000d10040140104080d01824042c0741c0101940341c44009607901d5201c0c078840108200d0007000882c3d49a000110202d0b0301ca4400301805d410320428030512410008007103030102d500744040d4111009072920344520b = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 578252410 1250 578251160 578251169
    0x6051f05031321110607020c01031e050411040501140a0515281d0d06091b03030e04050606041511010914150115020a02010c021311071101020d0e0d02031c1206 70
    0x45c00241010b850181d12860794620590400d034440d09054454400307101c10800c0c69210100400c20340ca4941069092844030400d0144100c0c2440c00008030360162a80030111120020205480545048100902c10710503006c7d102110b4020300078a10290b504051110382c661500c04104412010010f0040114010b20a0901c0d50081d0384c03a6805a80c498460102d0100e0744401d001540c46c0071070604685900e400000a00425642c10002c81095403100f50f085074000d050741d003030080b512181e0800006014034061143c0d1080303c41c8007803501c00d200322031691410384a07800002d00310341591a6445920a2516070346451341c8245071074044100c111540d54010180310084100020415800a480d40581d2001038100049884024159910703242d814001c4490000d04000c0b1155030041900c0a800070707371081d614510807180c400e400d94004035214540c0b20955450440e4001000204112507045075401e070380600c5825001d82e010350b04c00462600495840e02c802c0d126590103400380c030964003103420 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 578253660 1250 578252410 578252413
    0xf0d0b01152618030301080a05010b040c0e061e0d0c080603010902030706030218030706090609080a08030406090f061104090614090a0216050a11010306051f0503132111 74
    0x1410b07003101e0010448144403160000e08010340c680903403501115030312162403041d82c040003000144c4030200080582c0440d02c00c0000b0300200e8804010002156221032908011a0201002020031700d81a8002d000750303210500800d210388458401019980c100c010442e219942e00d0703080d0b240283c0c1101e28540d000401714002d000100490303000c2130300c0744182c1c801c540c241500820b644003010582c4814000c142409811125079a079200310080080f6041d20803017010941c80d11006c01c0400b004541d600c6020381107060689103885a95810f801809550003e840ca12160056000001d400e4025565201c0241d00303800d86850400003540300f06c0f0300c0c507800100c102212800c01d50036074450242d6554454084140103845074080e411078901141c001000030254001c0c0607001c0c1c00c210080c03e400c0c0700600c00fa682000425100d00500140420313402c001940722403110301311400c3c05d05c0340000b03542c80803d204010600d5a050307a988038a803003502c51495602405055035100c2ca55001c00d20482c0c0e000d0340b40 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 578254910 1250 578253660 578253677
    0x6061209120806030c0904050a0c0602070609180608061008101e150e040501020d050f0108031204030210141902031015020705150a08070e01090b03060f0d0b0115 71
    0xc1e038004500c0c1079500e144090024410000d582c0740d4062040c801c2c902c4000e000700041380382c00e2801944640c4014800c541103404ea02010544030b20000c2c092042e40c0c080d40783d8181c81ca040940c0040c0383d4254001401c0440c1e15200080f42481040c02206e00901c01013032031902c298181b000c0c15007002003189400030fa00e40790010a440c00d0034042c0401042402c1c8440014003043d44c0041d09082c008640c000c0c84e80300c11180d040c001000415402010355180200d410881c949442d403040340c03282420700c0f60b05850b43c824042004003141041206c0d030424403038011202a04000f003220002e0341c012402c402400c1c1c2d80c000400c44510f1030711084680200704010114034515103254540b40309080b600640400d2030b034003101c0f041000e008000c04000b4100090240860b10030071031360269a50700c03200c96800002c601e10082004180079a144400c0344105031566401203050135076054a9030002440144d0048603140084d551703448043c90780c0107890244072582d1444d810500380e01500200c91401000700090007 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 578256160 1250 578254910 578254913
    0x7110103020a050a0813020d0302100e0607050912150703020406090519180605041b0f0903030210020a2003040e1b0702010e0316090605130912050a2106061209 70
    0x1240c0d201d6135542403204158032608500d9244113141c0000a400c1035604941038145500094281d2000c0a0b41d8401d00490341e10398200c5849031002d40e0700300045003081c02100110714001659100110110045500b1103c4040c030381140ca80d01990b1040100343c0c001410b1200d40d038002040c4000d408141c0382c010120000100002845045204103803952031008072500031000c95170800d200400c8010300500581c14803a0782c18280500f04bd40c90008215400b60b03a104c50ba00400203242107a8164000e03180051108500c10080d41c452640c01c410441e881d10903140c1410056961409d40007c030b40219100e900344095160003000151203008485101c60304401c0d2900f00100315080d4584c2032a06e0307a8181883d5020a26002c1c2d0742c00030306585072425801140c0059507901900845204882d0040301d40342c00354080741202c000b0341010b00072424801d071b0b2240d00350107140103000c1c0004030300e00784100140d0840305110302c80b0100651003945132909410030040da03018844022000504c90f082040a065 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 578257410 1250 578256160 578256167
    0x20c1e130b091617190e0a0314160506090a0c0e1311010903140a0209061914240d06050a12020f0604050303070b01030b130c0303080402060d0c0507110103020a 70
    0x34007000310401c00310f4811500318410903041c0070707681d031160700a8880d0805280c0c040320b24007002d119041a0b842c088500d2503590000501554403a0543c80388054014610400074155010b007011800d8190603a040344001442001442d20070108140502100c04181c0b40199003205103511030b984084405042c04041183c3c4d0306c00080107944100b1560440703414400607143c50b840340c0d001500000ca9454035070248e0101084800829200f11542c540d160764072000c110464585440d00030f580b4841c01818004030800c26800e08103d500100310214248c6181d00500030460203103e00002d948010580b1840c082a50040c0b50250030100c500b80f0546040003017103800d4010780d00001c2d10400d0044a8414183c98010440307000d0300e0081c0079203940c0c180303600704074041400a20040310043e0206000441810040c2c59144038154490b581071081840c5031030407264410040c10907070388102c0400990101c07400e6440b030701504420a44900351202c1c030a080c0040300071100035219060600410039030300b203c0d50 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 578258660 1250 578257410 578257429
    0x6210f01150807060f090e09010c0e01032c07051c03020c060a080412140a18090501030521271008011404020d02120c0909100b0301060f020c1e130b 65
    0x2503900d0a4188044101c50451b0304c041150320000f540c0710840309022201d007041d008a0003955071a1111140c80100000440c00c4550300d601c80c010301e02841c01601caa40d0030140341288003020490484002c0ca46a0f400030300320b58003030074600c0c10020302403160004164042c1b00f070b041141e2080b1185403c009003000c0181c07000790700a1009244a0790a504400402d02501002c10001c1c020840d1a854007003000002c0c4c2a0b22031070301203017443c00032003500060b41c6959010b200d060382e520002a01416501342c80c80002500400540c0003c0442803101c0d4100031018041c0780b410425006114001e04030650230310801c0c002d811000e4017080680801845010b81d468510000002c043d1001a0384084581d90796009006d001c00e10201e814420b001d000348115040003414210008980c0c415140c1c0300d081c2142d002c94402c3c07107070b60341b0048240010440c0900603048203000038000e0055131745038001c20002940502c0c102d101c00024240c80c400000507403c02e03a0010401e055001420080315851400180700500c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 578259910 1250 578258660 578258669
    0x1080604051c03090506090f0c03010203010f0911070b16030c030c0815241201050d1a0402040b1002070305010e0c012a1a0603010f05070f0806210f01150807 69
    0x3181c1e4141007910503c25070003905040e030404250f440505001003440d03100c03459902003010a1052401d009450328062003101d040320303100d45000e500c1d0f62070001b140010b040212150585032100780036a00103e1002c00b00d42d8440c070303240c000c440b810401d20f0801070f0894007a15842000c2500e000c0b100e00358035070401c03803042d0000880e50315207400c4c0f650440040d81c00100d0010782200941e2a0b2030880c90000319002400c00c0c40c0a100300d800c0c940e0b0300c840c18072074181499000a030078040301d10003548607150800c100f61f41150024201007030001083c00800d4081e00142c40c00380040c1d020000820500a00784030301c0781600e0400c0e0180180b0089880020b00c0d803803800c10003841c8150b40f20340d03c42d03040c182006800c01c0c40e944501d1000d40c03840c01041540140e802151618000d508003031526107100303c50322800e480364400e40c42d180709004070032000b01c3d49440005c01d01c54101d60b20503e1208150b080300c112001490600c4020509402d940c140701d800e48200090344031905001600a00c5038050100b03220341a00c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 578261160 1250 578259910 578259943
    0x15030c080f060a080a14060c090a15030b0d081c0204050a0501110102090916020601120b190605150a110604030207030f0c03061b021b0306070c030210021206090108060405 75
    0x2502e0742400a00103001c9503000c11503034852882068200650300900503540210341d17060b00d0704c6030340340301d00744030703c0c0c410031074541d1b8040c0d0804414050306000039114800d0041034640000d0325503801c00480c90f003070035200e001d0351012404662000c4085090252101048074100c0550a052800c4007254003c1e4190040c0e60601c44010070000310f021095041c0c07040f486009011200134145045141c038260903809860303005020741400421240600007103404581d40c0401c20862a5071070961001c10b64101c04901507409803103040008042e9241184041640700c0262025911750f882800542030740e54801a03403003581c00c403108110109401041341c00c1220341082c00310b040141e080c81c10344611600d40e040102903d04d840941c13510220481c1400e41060050b4080700ca8038081d0500090314840e4004203e0340c503510030800100401c0c03141c040103e83d94403900484842164641d410420307600f00c2030030181c0c18010781082000610f82650741500424181c00030b4002030420303403541500c41034459040e0100 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 578262410 1250 578261160 578261191
    0x180b1309052b08070807020c01141303030801051003140114061b010212070509030a080901090e010b0a23030109020f0c010504050a111207151808030415030c08 70
    0x103000c810301c0428015102821401540e900340c4010841d00328004880b0030000b00e42d03e0001d02c25a00038034205005080c1038008041a0360854011585000c1c44a0010000b04091011070f400070140d045001c061427003a01e903610b5540c108805d000b40210800150700802d4103006840e241c20000c072800905449200003031304124442034010508502c40c6a140c03500701e02c400c14001001ca80c042d4040c00250a206604a90586500104071202e0140c208916856005052800e000903072044c01012415018144282c034a0b540306409184100c0076071011007001c00009440200d554410038144041002840301c2402240042255180e40414052800005d9000405a0741c400c0785c102550b0807000d5010090043d071806d803912585a1036000d0b411034030442c00b03655100c0d80b03140c064680c0c00d0b17103401e0000401e415031902e02030700c0c00143c03524200d40c184080c11600340d410b601e0410305600070307045980042d55500d14054480900041e0390400604061400d02c40d48503459001400541100c1d18102e409039 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 578263660 1250 578262410 578262413
    0xe0a0e06030a050f030703030f0b06030f07021c03060302030609030f180105040b180405090303090c040f020d09030809060a020a140d0f061806050f0f10110a0c180b1309 74
    0x544000400090441d04c0383c04010104244000024010300340b00ea134007400001c60100d03051060300c00520900350710a00601c0007035241090341c3e01280e07010140d44103d07a00c008104403130050b13011042c140200000d07104d0b1014401d50404001c0142c0001e500300065203019141181035145000d55001e0032034000901010810584c0b0800c00c0c0d40203031440c2e08a45548402c4201c0226a14145814040c013907410240010030001011003900c0c031840c4420080e0101120207800c0000034149a82c1111400741d00b440784000300409446010465842500c07501c40c1800d101c0c20300e9240c800b0041c611103400d4010400e074002c0d00e600c00c0d042c900c04100080500c0e00c072900f2121100140c0000004101d80c0c0703162550005000c4810789070900c2c9110200d804101031030f102e0007840001303241a403200d074200c80160b8031202903040c43d481d4100605c62605d8520001001140c01c00d040c4003040409482071400010148a01c840303041c802c0065160030a0100001c1e05688046403100700180e4041e941c85586140071320 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 578264910 1250 578263660 578263663
    0x5070e0915150414010501181a0a09090c05070516030c05090402041d06011a070506010501081f03320607300207030305060a0f05041505100309060c0e0a0e0603 70
    0x82c10400c0080041c0302000d41d1803a2003d00e80001d10800c1d0015220003220300f000307004110341e0015a14038245240500300412443d22150780f07c0b80c80301007004617400000401c0b40580c419943c038050581d46240c0d84aa071414100d25041c05804250100d000d044c40420001300d0356480c034401c0b220155005804c0e5521800010000c0902d10703403941482c015044168110800031030341506840c14501195034500101c0c03480150307030145200007001c0b640728100522240d03024000040d800040310201000b05550013120a03486a1658411113907407031110003050307440c039055640400f00311030404605021040c103240540d030303120040c0035041881648900190b044080c00e01d00068400c1c0381e01e0b2270304042440c40070b04000b0f41c031403072068000901c0c042c041000e515010964000300e4032a51034000c0d902c1d003000700304001070040f85030b55800c043e146240020182c86a0304148640131840c1c0f4006a204007030b0038250160f030a0201d864080044c088044034840e075400040e0000d5a280001422650ba140300119 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 578266160 1250 578264910 578264941
    0x7030506010c06050f071b150b0f10050325020c010c0804050316080d030b01021b0303090919050603031e09180408040305190c03031209140a05070e0915 67
    0x1403c102c2c1804100b00451101d41c40f154006c004640c1c071001050030310300681040c204121802800c80d00b0122041a2001c01504004400080100032000b4020300d08001540e42040d40c0e108004030310048200012a007040c0c1c000c258001001c6800d45010755507000c000d46407240c41a01c0b505000003001600d0600080c0400d5601602001d0100d40e544185a01a201ca20050384134041043c42481404040c072031090040c0300c1c149206800a1040d50f240002941c202e02400850581521092014401c181d03a480e000314064951941001896003229002d1001d0b0307200105640d0103580100650103500d0706101c000b84244500c07142494035400c0c00030010344400c0441e0042c0c82d08000d80c1e000c0c0010b01010200070000c491203042102c8a00d40341d041c3c46038a41e0301041020301081c3e540c84007040031034007136801c02c0c2d294402c409001400021590310500745120b00c80201a02e03034440030071001000410000e2030b026221111034000c60b850070349841c540d41c26841e0380c10805510503801080c44421044040c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 578267410 1250 578266160 578266163
    0x100f090308030c0705011d19060207050d0801090b0901030c06120624080f0f0f27010f0c02060c07060b01020708010f051005060306031015180c030c08090607030506010c 74
    0x580d890900c01040e1000707400c41c01d011746465290280c2c0c80040032050580d03031661a5400040c0904511140078400000d41d09641651140c3d000c0000301c00081044c0714910045085440b44116541040240c00c1101c0d821820180500304100062020034080400d070011103100f40b80040300403548030b2003076020744401c0d40000b9200d03454086403811005203071010641c060036a95200429a120302c0c400d0403100d400e5460b280030017102808501440650030445078011140141c0c402000c0c044a60040c00001075680805540d41d01d581c1c2c440318240d18044d148030b000170340c4020300c120300701800e0416840c402c41d5801481195107010081c2164020b00000c0e0050003650020005035400b441c2d44400380c10102e820714200111a05c01203040e2074a0415039002d0070018004041d0400e285626000030701e10890b400a407690740250010f42c140c0d6650300010008110700c0003055241c0021400b50a0710300086800081c05072800c20050411000079030107600041600c1c001c07a013500c4010060f122400340700c80 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 578268660 1250 578267410 578267423
    0x1290f091302041407080105012f0c0108090106213905010503090c1e0307080307061103190513140c09061e040509070503061014040b100f0903 63
    0x100603140702046481c070740d058025202031108046070583d41036104c000300d0b40c980118041200500565111341404121071804903440302080b04070101c0b0103009400b101102807150f120100e000c0343e55034810350a81e000703a00e080c0244420b60034292040e41c0418901c07141101c91002c0b8040100b80095072801e648a2007038078081d1510000000d8029081d441c1041125154000f214000141c95204204581c4544e907200b000d01a0380c200740040100e0480d4894801d0390001c00c3e00c031840100e07901840500010318611008682d21141403400000381d03102407803400e1101c10305004000701d10075604c8c050f0260b040d4013080020280d9903200c140d0740c440b00883d005080e82030b100c4000c54107058005401c1405903000c480418503580d40ca800c00181c840c2c0e0320040300001082c690701c04440d05040c1c2141d42c201c0d20100540e1795454940d400f02e0314041c81141e40320510341384090700300400c0000013402d2000300700560b8180042041e801c0410b10301c800c0500204c00304006004402c402a1048212101a5502c000c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 578269910 1250 578268660 578268679
    0xb030603100608030c07060e09040803150306011e0504110403030c05120a0e310e030c0607050325020601030b190603030e030d030b130203091002220801290f 69
    0x9400b541d00d17001140541d050307124401010407814002c070081044940010304241031959555100522500060180e4895180f0400f00e400c00740c1c1c042c480b81c0d0180c0340f200440d01c8987d2049208141d00c401c0c91f400940554039140d1481105819607003120262501030410520b51911854403034038005801c4c000e1180038a02203244520658058404081d04008032010300c0d620014030028099400d045505220701e80341e4403402c0300e01c10219000020603600038000d9030704104006403414109202140d203080000e03000005c00802c045c00c02040e00c140d408a004034041d00d14082e4010b5607410041c000500a030300d5403800101c1030b0190900101c4038401044051103c41d03664940a0300c2a00303840080b82c880d000d41b009400102d8407038882c9002803030000b442028103000501606000390b0010f0300c0000303107000d225420018041e950001301410a0104007940c100f203680d02100b0700840b011b8111140c2a41404c031004c81c522070101e07c0c24200301c035900c20540341000c5500000c180c0003031500d803180c2003c4e203503 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 578271160 1250 578269910 578269919
    0x501090f0212010506010c03030b060c01051914040b0609040609121e0c020f090a02070816020307060512070e030c33090a060c06090602040311190f0b0306031006 71
    0x85200048081c400d0b00c207038044100055080d4242ea80449203c2d00141e501ca0040004c684260401400704c8400340c0b9152419442d011071034251103044901061125060404500305a2140300c0e2120b0640113030343c044401d061980e216882108003800c418403424241000c181481200e600a659042e44910030b821a04c8200c078019010003a10701c408001d90028080300d55013f0700421401011941c003c00b02888030001ea400c00c8488180a088246101d40c02c1c03100e240002c16030802054182101903034483d00c0c3d1a248105071501100d03400000420009010030024040150307401500300d40541455203904141c000468980b80015090961000c00d81200e1480c804030581d00c2c084413001c43c00742030300102601c101300d052440f6046000342c1015131030b4000c100c5a842140c0c00703800684203110215115100c0d80b54803082c0d801640050b2410521441803402606d458078410f9071103544080f80e411400e142c001e403860b002a003441610414003002000400d140c6d81801300329075036070600a0400610340c54 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 578272410 1250 578271160 578271173
    0x1410020c06061e06040909051203071101060b120604052e0509010803040e010e13021005090f0a14040b060f0301060e190e0601121d0d09090203010e0c09010507050109 73
    0x7034805500484403c404402650300b980e61090000341c018104503d440c0c50028084014201010251071602a00b46803c4032450680000e5001e1030003503a40440b50003c401d20f103421650107502080c50030004004440304555400c62003507000c3e2040302e001440d03544080265100c11580030070109039508c580b280448889907ca0b601060300c005481c40303c6035a885070840395680c4914082c0510000005004000d242d960915045d440318102c0c12014030400e440c1d000c5603800f640c24000300003145020800000e1400c10329880c030388985080380e15451051405000c0030f002c508444990303001300e484071a51802a25a241155180c2022051155503581d4401e80200012a02d0301c0340c0303110b06074010103191407144c0004210140c0304203003422103507a1100310045d81c054100c1103014000c540c80d03484804a656840e03c07002c010034100400b5004000e144c1800034003c03d11074220034440d0b40705000600000c40c0031028180c0c0401280441581c50600500581d076501490200901c15800c0c040c0311000c0010 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 578273660 1250 578272410 578272423
    0x201020307050d0908010e0601080318012307140604170c15010803041a07110d150f0b100c030504050603060f0a08030406021009030f0e04150803070c120308041410020c 74
    0x1480f0000c03c000c04411480c5608d454081c411400540d00a1042141c1d10f8900030301035040301d0050400040e50111000320a0507400c6400480045100110f240b01c180900079100804507402240681041d141603a0f41c886402840c170751642e814840400c500d442d804041000150741c0000807001200d030f6940344581c903543d40c8503014000308059030007007154410005a0a07206060703840a03d51034115101014060b44804103141030713405a140c2400407402c007410340720342001003c400d00c02040c2c015104090006070070202c180e1b8001c20503881902d20100740e0100c19602540c00031201981c0c2d0b5141d1900203840b0003551040380340e0084445800203441d1f20000000e2003201c0080e005d4500c600541c551520440f580303074001801184c0140760300250140b0580060b280100020000030341e20848500c0084058800d421400c65a4800140342c01030080c0114224014800b41d403000f800481c15940c014803034400500010310008400c04403c3d04c0590a1004c003004280f40c0304119260108021426610b14 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 578274910 1250 578273660 578273669
    0xe04060314010e07030b0a0b0103021e031b040602030a050d0f1d100510050d0201031d010905070b031510051207050a03051602120d0e160518090601120201020307050d09 74
    0x6291450b0f21160b0040424141c003100c0d0000404a25a40e668034180c0290480e2080c190426508100c1500365001303105000d40b903100d080406a8a030b26150890f0f0340e41c0c03200928014901482030004100b103990000031500d83c014545410354030740b1610b100b20740c0031b8a440c02100c009181010100824400030000e03140081c50f003141100d01c014615070460007221001c4d122968000d01100b001d01c118100461501002c61041c900020303074035030280c07001c004212000700e030780702c1c50751115880c00511100704060b0300138040e6240c0080c5941040c8403010010508070035442e029124403010000e5180c020070a4413206041c02150244030318081c0d1009203142c2c0007608440c04a40b900011400301d841d41c9030101040e0b0000e800400209000246510858000d9207400701b00d51348410500420002c203004500c0e1084c618007881030071500f0700003044280d611000700ea8120b50600700c00c1158189001901e54115000101d0000d01c4060f00c0c00100d00703510603404060940e101c1c49030181c842c240e00c54102c60844 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 578276160 1250 578274910 578274913
    0x606030b040f0507090c09050103230a1517032d04060201020324101b082802060f13031214070f11060103171908062e08070e04060314 59
    0x185e01c4001e5181151603d81641d8009070341c221013400954026400300002104101001071240700341c60103000d0080c400c681c2005141d8540c0c9201410008400c4c0081c0030f0410410ba03460a588012040b555a0080c0000c0142c452441010411244c083c0c01c1e9000210610030007031580c4545403a4080e020707510581e1400d001000100107e481c000c10040c58040ca044018603080409404200032a143c06803c3e400415412602d4014000203c0c00c0c0020402010401800c0031071111014042032100700d018a0502175400070000c01c0b45000c500240d80f5072000011000f103070f0940603410201c0380d03c3e44440c128020305141c44880c00c140142c800c100780c450105540c440503850308481c1c046800a0b51414205419444100180001640341c03100c2403000303414005e4603040240c40585800c01c201032008000102d400d5038180302c00d030b017803850795240c90010f2056072554590a090b81200010440d0702100100304013000403801c91481000507241c1104020000d109254890a10307481c91210381c14111081d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 578277410 1250 578276160 578276173
    0x206060616030e120a03080f01051203121f03030305091c0e01030504260a030b1008011403010b0a08101b09060f020304030c0609210203190606030b040f05 68
    0x140c9011000c40d5000c9008440010394128155401c0c1e4883c0d2100d0503c552142221440003c0304008000c03003414035000c0e554200e45821321030300701d103c46101a0040e601030222812446042e540000c1143c2c0881c0e00c0070403a0312296603ca000c40c030450708c0002c82481140c11080004241541500000d000d881300b03500b80c4051060143c007409180450103190004030300c4c42203060340598007030b03444a030303001d03000d0000351104241c100302d81c010f204041450138281b02c502282c9098801e5141c8560352042a0640d080a00c2e041d18400c0506a031805110b0a6421711046605250360348081d00310410041006e008070142503181e511040d111030440010042c1d0602e8041c0700c3c12081c03440044600001d100d6265000386a08114046031100c81d6424081c066120411000002680d80c0c003a542c010300940c6d0324003043c80d007019036905d140e05a04401e0302201d6240c985a90150743d0110356805a0017401131a0b0020041c1c92404201504503135201602140c60b020411003070042c4a107420f10614415401e5445 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 578278660 1250 578277410 578277421
    0x7030215040203193002120a05070210030b0d26070b01050d02010c0b091c081905060f031c030c11060a020d0f0f0b040b04020f0708070317040c060206 66
    0x249850210341c06981a8402e061555105507001e07450f8440314012000d84040e210100790544084d030442201300101810318805d007288550521800e030380c81c1d002d15031052411040d4213008019000f8054040c0c03080043d0b8480f145907a000b80e000920304507000d00440300b814860b040200da12080104610070400081c0131004551000034220b50119074003001c1d20751141d08060911500c0340c2c031840101e0500000750691804503e084620910a071604401081c0390340c040001c0341c3e807141c04800c0207418803580d14113016000d090301080318240d0301c101d240010765644140000341d5042e4903100c0103415003d48810109400e420120069050149031424001104c0c030301421036a91140004150458010b500483e21003540391f00204220301900c54041150300c038034108501200c0400001040311580c54102d1400350800303010740080c84504540031809c0044541d034404e010310620368024440600040c400d02090300600300301200d203021070500d50441c130300307454040c050581a0040c0c40251044800083c0c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 578279910 1250 578278660 578278693
    0x7120f08100b04090509160806041b030521190503100e0121020607120c050d030204060207120602040906030305280c020f010228140106030302070308131802070302 72
    0x208980345680b409280034503000844000f840c010f092041d840c0501c01084a940d11501e56440184c45144041c2403241082d00d401100c0540d1241c1e004142c0102c0c050800104030040384c4402d42482140c2d25951581c1c0d50300406c07409204041c0c244041c00c0c0c48458450075543d105000c0c51003480803841300c40e6a1a01c804000c44a00c6c0244903101440c8100ca44c0c0d9003015064202021940d440075001c10300b00701282d641d204c4a042504001400900b8001c80342c014400c08100607010004a81400c619081c2090f0009484404901032280b82031104070b5000304000d04c80d41103400406010004002c180c1e124a801446d5600140d9004081e40f052900300011000402007074031840d2941d290f0305044503043d42406400059500c2c0a4158060036100359018040344172482c807114a4400070070420543d07841c1403400c00c4003042aa81d01d50380340100078030010b9000181102504c0d00308004540f6600940c1c9802807140f0107400102d0070711001c043d8200716090351b40241041c20b21a07025903442d41611030106 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 578281160 1250 578279910 578279941
    0x20409020a0201051807210b010905160e0102120a020a0b010b0318160501081f0603020919051011190303060509090c2b0204022703070e0411010507120f08 68
    0x1140c00d038101b032000b0000f448200d1000d1f0844503149103040c203600e05a0300c1d200b500c001d0981c0200e41041d00c40c41002100a0300801040207840c050800c02d09500312400000e5948012204003007040c0c0d00000e81c0940345000f000300034801913000d41341c6025036840701603401c041d82056030b000c0a0f03091460701540d2640800300d00c0742545404400400403a51a180044600d02000360003410703138200340e10003610b41858580d00f1202a14140e2400b50740e61280000313001c3d80850b40f0450000303111000c0380c1800303196558039424403003880c0b6190428040075500482e5040070001110000120b00c1c00d4105d000301900368000e038017100c0048a1070500c41d51000310355500c1d040c1a10394240d01c60501a94600700010000796040c101e444005814008500d550204040b80d001000c03c17411010212a5581c82e5000c282210040042c140c0160903064604411020402030262008140b4208500c3c0c16191ba4401c0b000c0e1240301740c1082400c080c054000c1c1c0c0142580c104910071800050002001804494907501c41 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 578282410 1250 578281160 578281201
    0x150908031e0a030f0207030e270f0702030c1507020607090605071b050307090b04060803070f080915040e07030b040e070e040c03080c03120f060f01030b030f01020409020a020105 78
    0x1061a07104031180e0039030240d401441d0100c181550b0f081581e01e4801284064503115109841d05810380c2100802c010f01140b41d02c103c496031814603a20840140d07103991000f90403081e001d110035402d44071240c0c01e13403c40c040d00c3c070344021912031150501c10400c10003451f6030041504bc2c0070307515161100c06040f2103c502e28051800825820000603000401c01841304501e0b0301100014500c1c41d0310b95000030b013080490307400510170716261104044c60746005e20a880042c001c5100a44c034043d142c0c1d43e088207500140c0c1000c0c04035980440c0d80d0102d82c840e1405072401c20400c56035148e4450b00c9800e0529031040c1603a074040000e16100d4030039420300305485400d40900585c1b0084c282c1034a41640703101c0703900c0b006100f110909218500040010f4640018118104180d0040c0d91141c0070000394400000000b001612070007014402e00440e61500b4140c42400c6c8420301e004100c607080a008240380034805e00c51000e26600c0000c0000d6030400a42c080d00d0701400c4c0394001d00560311200090386200308801c00 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 578283660 1250 578282410 578282437
    0x3030f040311010318120210050a02040945020a030818030d200f0d020705030f010507090306020a0302120708011e03120e0a030507031217100608090c04050115090803 73
    0x80b0301040020211046c1c2610900c101c8000100ca442c40a042e00d4050321041b8940d900820140302c03100c128000c803141c0c5840203c0280e41c1f0580c0d44c0d40c40c0c41220310000c00a00c2d10031080860402403805518402810fa0054180320009030340c0c1c80c00075140e0388003420302c41c42c0c03448414507048145800b2440c1c3c005021159140b0b1904040d45100f15541d075421600342d1040e1080d8800414078200612141070410966009083d040d0716004c10301d07080c446041b0030385050b64507010800c0001e030b030041401c0c1c00340e80d00a040180c44036450202a4001d01c1820316040b94400540c042008095002000350305854001580800049050580d1035084510b804010302e2203142000d01036000384078810b00c1010410062200d80c2c0c15540742c807040d00340a0182c00923682545560302d0451280d807c4150b0000340d43c0c2e8011101900d1520100c1c0840081c3c203030192400f00040390001c00d129840420845082507001001041103503926141001283c1d0103103404008150940000503000d08048180c650b5528a0007 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 578284910 1250 578283660 578283701
    0x150306010302120708010501030c05270c0f041d040c120201080a020a180b040e1501050a030e03040b0c031305030613030305040203100c0e01080115050a120b03030f0403110103 77
    0x90800402c104458103c24031482007000002d880c0000f4081d00e40214020000008454200360501c440d08131040390482200a410204071030004201c414a07512171804010681c9940d80205c20360464030641d0300581000c1030320f510340800004e000b04420300440c0701320001100950b0310108082c0300b110380280680400c134101c0c001141c2000039001081680020300d00944a02c0c00305000d0303414010990480008444049018011942c200140c00d4000000c048a80c080c0d6200b04002015482071010b000308040d21414180c41c0c140f4204203503005080c1040401c0c0d00c0d41c089681c0c2980e65085854484210001e440c40002d20741400301c0d41900480c0c0a42100100001d80d450a401a0102406c220780520802c111807117128003a00c988081e000055840b0350007280d03060700040c003824041e0005408035542c0310030302880c50741040860b070302c207091418035024444680c0c08140050140e8a14a50140000200031804070398260040058030701c280103174107039204c0400c01102229440034100325400c0001 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 578286160 1250 578284910 578284913
    0x30b18011b0c08090a0e070f0e04050103020901050d030306051003020d241710110a020f0d0f11100f053102010c0204020d0608010606390c08010e060604051503060103 73
    0x100040800d514042c103404881c43c1c0c3d0b042c52041206d0201ea91900103100c841160b9002075000c12003a14520b01242d0901855041d900011b82000b818031500381b16000507410202054000d4028000400d402488003c0c2100102c50180207507110b004a03401462510030100d8051f0100c0b801d221581103004c501e1015242454440c19141e4580c4101140d90310880d5200034007500310b0302031a056403400018050b264109404064501842920104440d800903075061082a6210034028105611440e00d1021003e1542c041402d00d0302400340305620f41e007019010081d050701c40e0099405140300a0001a070361041c0e24160b28800f1030307000c071486150705450211015600c64500440c0550004000510782032141016034225005a0310050b1265103c80c01040404e410074850b06002c542a03049980d03100f914030400300b0507000080f9000024240358052010b0050707000001d405000720074001c0101180c0d8200d029900d1030304440091049003002d0004080c203950b112000d011003405801864643d095 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 578287410 1250 578286160 578286173
    0xe0c090103020f07080a39081308060405060114030a0302070e0c1c06050906011409090c040f0306290f010c080c01020d0207060b011713020307030b18011b0c 69
    0x2c0302140034249020b00c0000045602100180600c00750350307d4007000004801030100340300018900100c131903081c0d9000025001542c01050400325070104100383d039089540c01020b2501c01c260002d010034811007007000204000001c98505032000102d031840d850080c80201562244c03113800040050300040e508200740c02806400c07070340140240038071606000c480000206100780c14082d900d019505c0310702c2000070342810045140c10003001c5c68083c3c60740c241d2403410105e602c212a5001d0103400340500080d038035400c841c16103000c1c0400c4001c04106958909000c2c01810261450103034001c0001c3d5110450507150030252042403002c0c0c801c440c510452001500c0c181c800740b0007610403a0040089105900c000c1c402801c080d00303a0707240142c44030701e541020002c4500035080c09050100b1482d049050392000e00c5140d5010780103202d6036007c404284003203820040a5030009041204100134060140ea6842503100c1e81007200c0e00800c032260407180120400c0014000100100740b10001903004140d4 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 578288660 1250 578287410 578287417
    0x501080c062b0903020a0b0c030606270301051e0c04052815030c080105040902030304120609020303070c03020f0405071e05040e070e090f011404021b010509070801060e0c09010302 79
    0x90310200000700a0b45160200241c490f2064200d0042c2c0101c21800c040110800e0a640c104020031f550600b5484d003040803c10354411180300d52501c01310740e1188500340100d068200c4103140301500a20150a1000c80c0380400d03070400c40e00d85800522507001404e00040c15041d036088600041c0440034110030507041d04901140b80c94400034115002001248984403041441c907030786240d030380000d80c86444420003418200c040c1c08c810300c00c0d07042103040b00140c1e40010940d4242c40e90b003813408401105625069004040e20309000790103010104000c418040e0313510448044078000e030751f40c00da9102c0352020001151022a403501c0410900495140003064110b100f01c407450381d90500f286056111100410110303c1164528005516008035402c44d051020b440303a00445401340c00c009039410816a003d46001d0300d11800e00480d03011503c01100c5480030306190400300124004c00990500c580641e03200c0c02c1078001e04a1540c200341c0002a0041919851440340700c2600038242850480401100a90f0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 578289910 1250 578288660 578288707
    0x120b0102011515020708010203090703112403060f01020a0302060a0c050403050f01020c0f0307030801151209050d0f0219021903080c0322051e0301020c031c0501080c06 74
    0x41d642c004828120910700c0103a0041c0c855500c40c030302c06211010303009191041c5600030002c81d03401441404950480010701e801a07a40c460004664200090b0101e011220143c0d2482540b41d00d491141001c00384c0e040055010b040c0982c1c840348600789960059907640003032900180147e02010000b100c682e01544003000e07401d02860070a01e003650f40c0d03c0d141e2400c0640005c0d481c480c2d500040000040c142000407040b50080d035000b0b142030201944004d0507480301441409034000c1404901069288203941d03625071404400020099042c1ea030520790b5441c0103c9003094041141c00c1e410041c403500003c0c1a01d0040c1d070601040b03111031041e07402e00401080c42d20074500c04800c184004400580d40a010b403102d104a04021910781d03420381c1d83c40c00403215030100d00480c02a59070051180e5250310b40303078100300007045542c1b1524034280300200c0e00a1180740001c05483c000881c84548081850101d4840b0f00d24041e402d001a90301c0c0c1c0d00c5143c442c4282c0358280e41c40070b010040481e118030181c0c0d0080446 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 578291160 1250 578289910 578289913
    0x606040e060f01120914160501090605130902210a06080d030b0328030e06040303080c1c0609020702210a0209130609111008090d051c1406100f120b0102 67
    0x48460302e101c011350b100301004468400c030250100b11480d008003e5000d0b00b02c2c003007c070000b000303140400207050720105000e80003c0000000d240302c14442ca01d1940001004041c3d070071941c4109050a400200103010403480000085e8408200e10307441c540107c4060341ca0070f002501003548402c80c103a004042c0e08136030b01d402d4012a00c0c0503078540178540714100840c1481b407200d801608036140050521000740c401c103208001c28041840030a40c065041c0c0e80c42141d0002d51903542c140b464407540b0803001119282c01e0242002d00200e00365880d500681580d0340f007551880c140b2031906107401901402a0148442d691260140002510381001e0b800e4100704620110105021b054030368100390b50180c00240d440c1e0100440b03902e85400c1607403541d03010710507619000070681005409076441d41c403020214810808040784140b800e010300b010360200d82462410800040c104482c1d101c2c1c1c004000c503540351040c526800c180092901500310107121103d42c0c0d0320f400750440e0040c003020003001706e400c049045 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 578292410 1250 578291160 578291177
    0x613050901180c082526070f0201180f110405041209091b080414030d1b020c01090303050c01061701050103030906020312040204020f07080313050601090c02030d09051501120b0606040e060f01 84
    0x46c1c0d60b5100c40403114944510303117400103240815024081100481c01d0904581c5800b109140000d03e20aa0703840080c3d0040e1010300004190a069500c0e106c03d00c1501c0d405844c0609210402101d507212908480f100e0301c40a52099540012004a410070004822820450101040614400d1551541c001d2140f45a1213000d5071900303100340f41da000726040c1080c10365514038018003101240d0b90810459070354401480101c803428002494880c0d20b220040500101090301c1644110a40100c40500b000007640070707411003040c86940c041c0000b8481900483c0c002c96021a40510110440b400106100810062911540c0c284002980308aa0080015600b800b52500042d00d06008501071800003d4800c02c15409050643c00e01006038084002d036450400501400b903000b0042d500d4000401d000040d01413035608056080203001601c07400c0c40d00010002181000b0f00304540c3c41c03502e0081039900c4255940e002441114440da00455000056802c006086840c14240380040b00d032041c0f406115 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 578293660 1250 578292410 578292437
    0x212003070b040905270307060b010e0402120117010c05040b0d060e090d030506031b0d060605030616030c05030c040504091a1305010e010207110613050901180c0825 72
    0x290381c1003500401c0b185625081400b690086000035184145001d001ea0408560340d180031756941d200e02117000300f1141e00c803401e020007680240d13140c002040c3c0c00740080d9550444032501a400031000d000f22480c0c0901111210101181407080700d445e040c013525981c1c070b4142055000a0140c20011064003070545075a404204401c01c10052801050310000419452140142c080d007030302c40003401c141c0254050f14560141000412400000c014291b40075680700003242480c0c0094281c81d0032a94052103a602030000c0d80c0f90910140b440c0c038010b0740d001c102001c001d1808031098802a00e036480d003032906200c1070156107007070790252100d603100d01a003181c031440200c9040145001218030f4469488508082c80a000c001e000b070301e9440e0300e41d034002c518144031303507848001c4a180706501900582c00451307800e520714454081e000162400420702c0d61650b0707440f01e940c181034460034841e41400d41800f6009508030701a240c114082e0241700d103c3e840d0444100b000180c00ca4550f0071140401045104c2c0e00c2 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 578294910 1250 578293660 578293679
    0x409080d0905101104170f0a0312051819020402071a010e0f010e0609070c1202011a040212280504050309040b010f0f050f040f1202030705030d0c06021b100621200307 73
    0x540a6200391140541c2408100c200410bc0b2401407100c03041402c50700f80c03110000000300d46000c101c0c495030300040320a10749001080090150313100080c102403445000030084a01100705604942c10f61000c0c1d00d440da40c10045200e40380080c41010b0f89a1100008540d17036140260102d03038800d5080c5030803840348a6680b903c01c480302c0f80c9048840941d6544507200c030228072211400c17148501c2a2019440c00700ca200c0c5c000103070ba4004203001d4600c41b12205581e41070303071101e403c09510110031800380210b04250814640b60f0313000d41d40c264800d0b441c00d16058103a5016034214114580340341c480d9044049641026542c907805054607005124007080041014601e990901000d0205500c03000307649003452060600e03114072600080d110341d2140e4071441c1019400500315044070707400304001d40c5415600500700306002071007408907542e008606260911500c2e41d80200101c1300e0310600c0008541c801c00d203030154060f0ba44030240c04020b018002c1407900500c208400c4080d9406000c03211100c0d600c40304d49 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 578296160 1250 578294910 578294923
    0x12040609060e16140a08030414011809020d0501090506130504210207030507140a15030f021602180c0a08041a0103030207090506031603110409080d0905101104170f 72
    0xa0703594289180c00f0300440d202504c80544108055a4440d4110b04011646590740550300c40d501d51040008507000c07c80e4400e1110a088150021081240702d48a68640c1c01a40144403500b181c54985000014200c0060103031600840002d4000e051441c104061035010346002481030b244003d020b01d5100380c8401c40702d40030b890303101c06074080d00c60203095140141c10601254090304035a036000f11130780d8503039692400d800100d901c5c000c240884d1051054054014103100207180040b284086200400039081d21202810315208980d9042d01a481c0501d1490980c410703100e00c20300403c180050200b880c050f01c4025005402003003141e010310b461505003400307070b0401d03001240180c0041e2010004c001d850300034039400c104100e0180c04013245034a80104d04640c24032000e030440420202401164860b0f41c072640c68150840d541568610140000c90040c0c02c03074040c11a418803800c00c1d0754189001d00d118128814240c0b030300740c0d0300d000d00d8140360141c051001c4003511843d0007000e8850b0340f0035004001c1c0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 578297410 1250 578296160 578296183
    0x9010e0628030201080f01050f2202030f0a0c080408031f05060a110f07080c0d24020c1908030c090a150806040612021f1101020f07110612040609060e 66
    0x78400d54504502c0010983c14000c0d014001034198100144110f40d1fa054082005450a80740c444c69400000900b90814080c4190407046610000610800b4400c01030940d110b41d26002c4c061000c1c00350000101c030b4480d000c54001d4240281071001c12490140c009548440c40d4800303498400366510354001868036840103c650012452a0009056070f6100b0b001208407144001d020b05584c0f40313044100b0f61112849241ca41c03103a02c5000c0c4a03000c0002d80c090030b9218140702c2e12110f8000004040180003903101d48280c40d84d620030541c40416080e64140940d1685a0000000b0300303584608440110ba42c010355610795002561440c0401d07541d0380707003240100c003000980d9550154240107082c4400c40b100781d0442400000c500c0b40c64009038850025101a0069010215000300b1200004903454400c0c0d101e1500c242d400040c0ca43d400500002c0508a80ca000300d10682030a0492020812248101c03030b180d00c40c001c200c0c00000c0118410344d00c985282e034041c480210300c1400084c8200d0034403010313078032 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 578298660 1250 578297410 578297479
    0x705090409050304150e06180409030516050601230f0d02120a030e04060902070206160201020708030a1709010c1d0604050a080f060a230603100516110102040509010e06 74
    0x185551711680031083d21503896054441c2c03407805150794280c1c00e5a5400d0321b000340c00b69440c0d882c0e040c201482881240c0e25814450500301d1034590b203103046034490310300784141081c400c10381c4800750400700c0c21218800c40203001001403010304800070a0101c1310b03042e0301741a42c0c001c201e1481d90341d02010074404110740a200b69a03402c90781e02c0040400c001c944054002d81d403414814070055005171241c0c000c560344180054110701030b02646100407454000140c116498901001c200e01c01d420350054188540a1060111800c2c0c81d41e500507018201e400e480780d4100040d41440d0034400f03401600521002e86503020f00310724035203511040811281000365101d40c845601c44d111070b1102c6401440b00c1d41c1c0103040180c00b407000c0306400785000140000400c3c003034210030405012424030703074040040070305611124605100500d48244070401e42040b00340e4080c0801d2402d400c1020640c01803084500740c644c01020600303c0e03400e003400c1c51000d6a0027010a5000410403900c030918141e40841d0469072491000c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 578299910 1250 578298660 578298689
    0x110f07060801090608030306090a18080c011401081203010b0f0904020a050409051024030b09040f020306010f0b0703080702010207020a031b090e07030b1b030f06090606070b0705090409050304 84
    0x490004c84105030b101c22400d820030b000348103113690796601803500903101240101c0c00e60048091224034001c1035600801c000c200007542204110306411000303040c00c0c0d048201450383c0e81c408013a40ca1740c80d10840018500400c10040c0201002c0340c01034803031103082c455041e04029400010400701e070711001040000c10000314003000322401500070140d014811300700d0030000c24a0408a44901001012060122604d01021943e03052095010042014009141c0c03d034034109410301113008801c0d120700364000d0241c0c400118150701da40c00280100e5482800f410b10786282618101c4000c0300140503041107540130032140b80540d8038003460401850090a071020041200401c5c0401c40400d503005042c07140c20319101028204c03000c6401d40440382c108860072100d58030300590038084551a280160321107004020f001882401070f54661042d08141d8840c002c5444505c00c01115008442004010792640c0c000034006030701c50005010415006070000c00d017580c0c80c1d5038050442d00150840c220351481c00 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 578301160 1250 578299910 578299919
    0x2a0604021002011b030b1203040e0610080103030c020d171c0506010c0503040b0a031503050d080109090f0f11060403060212070504030b0a02030c040905090d0e041b110f07060801 78
    0x90107512600001d40000c00003110703a01c4651002e068141321150506540703041820f00c07038a84041c00b91056a11805496499813500c0300c04046140503100107004480881c4000c001c1e45c000d02c1d81c0b038143d0382c05407504800c80c00c00740c0c01c100c5002074082c0200d603154000302d10020300c1c3c5841d10290026001044100c8030008010354468100d0354000c181c181001050040031003c83c40100031034050315501a0b0143d0b4400d0350380000d4019000407406170208075040d0300c0010601070081402064241c856858440e182d90300c1180d14244c81c621403025001c0d03800c2250040008900141d01048980f04504400360412160000740c03050300903600942c0caa0740c000808d900d05000d018000340d401041800e189051905503100d4241c4001c008018400c00e65001010403a0701a506c1c0503200107005c1c5030400d020340d02d09030340780310344889078141810f0100c2c0001e1011249884d05000d500e07030240070650601901d0442420440d40d0601003030301c0120030700500d941c030081e1141c14031415004e0a03283c6c23075410203540340 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 578302410 1250 578301160 578301169
    0x1808031312031803320406021006061b02041103190b030607210b030a0303020904050f04240e0109060603140105190b03190323040305122a060402 64
    0x100700741402c0518001c0d844810742220700c240c000e02d9815113804041000030307800313101010b001031809075101c12411400068004191000340b05480556003618100210903404205641e082d0243c04042000204400701c02c11103040003c54480c0020408240c01d401458801080e51080d5900c0c12810404411111825158020304000f100258010310f4203103482e00b80240542880b0350060042c1a00c81c150045420f49900100340540c2c004007071326010704107458098001d51029201a0140e4205000030f140c50387d0348012350f4450342c2c20042e16026001100101c0c000b001c503d2810b81e040a50301c80104e0b1414000b4070540402710711514001a80f0b5003941000401140b040400591681c108402c00005854692000064217444400410f060400f5000607083c1907421804280305d280c41c65203501416484040a60501c00201410b140c0e0249041404554410f500002e001c80c1d00c07280310107140080240080ca041e11003080c0e110303280e01421081580d4603280c3e002c6c00348103500c01401d01095150 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 578303660 1250 578302410 578302433
    0xb10080705030601031a100b0309070e2203080a020706050c0a1b03020c150409050f15010507020a05101b0f12030b09040b0702010608070f08160803040918080313 71
    0x4084009110f250703d1170faa0804505c014855040394804c0d80c0c0b02107940500c2e283d0f240e40c080c21400c00003d031a07181c1008079680d10135107442a00302039034070032012864882034620034071510422064142c000c03c449440541e107134603020300020b42c9a80d0030001440407550a126080c015844180384c5603503511051001800600d900c0c1c0741b45145d4400801d0480001c0e00001c034002181c0c07040da641c0503090005010003110740181d41c0050580b030305000c100002142003c041910403540809940040d50b02d0000448180c060104000c0d0054003459051045151484030000303080c0061809058400690700e50fa000d40c04204411103500003a0080d0034100f0001e00c507564041c01030707450100456440b4400040c40094041c0c4090508041d400224500d54400c0d08140064680001100c091583c7e031003148685610b280b050401c540101401500c00e805d501140b00c0413902c240740290304281c2080b9030040140784254003480c4070043c072180311000071359200165200c0e04001014040c1070209003400840d024 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 578304910 1250 578303660 578303669
    0x51e04080a03030e100522020a05090c0a030c050f0a030b13090506090606041a1309020306100f0e15120a390b0316030902030715140a140f070b100807 66
    0x3401d190030450307d003c00c60b4101381041030350502002c5906c5203001160314540b46405c100e0704214001d00300981c40c107051005003011031490340c1c20450142680000c03a440d0180e1074141034038100420050000c20300ca17400026410b40e00030400450200b20300e041c141210422202203034075800100c1045142e6206100180d40240182c4051002e0183c1d070788540b640541d000c96203845242910781041d45984542d019003c0c460303020342210801d0401c60705160035514240324101180d100401e0214020010380d101e01d008000502e80171565804036410083c0c150000d00311207000b44180340300c0710081040c001010740345222560502010641e502c0e40c8000d452280c12410b0f000040da81b000304a0080a00c045070b40c020321840f682207580303207448811800303420000406941441000c0c008140c520300c511000c0544450340d1501e881c0c004d0141e5030350a00e40142c40940700402c031441e00b44900140b0050052080e400c00100d8546008220f0b0340f8a40c0040d0191b45250004500c40030034421310b14100282d1002c0d1 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 578306160 1250 578304910 578304943
    0xb09060f1f1e18061103071b0f30050a0c09060e1612150e01260f0703030f1e0305090f0c090a090501060f150e040c051e04080a03030e 59
    0x240c4010f54482c0700b0318850385040001002100d2800f21080c415581910351040c1c0907884c038440c414181c4c0f405407050240300c80c10745041d03c00041a00004501e00c00c0401d010302910f45400102000c1c407442c0b03803203900564460081c0d400490010b81c10702d150401500c0c8940b000160241880201c40d03c40700300074006c21158400f030088030710664101104142c001c0341e1100c08a50852035040300701c10792072298170101c0e05115481c008038016020081c0c95074200080c0038480303103d40c07541d13866130340e074506041c0c45010700e8110b00c40c24404a84900011a5105c4107030404043e80c50f42240500c1000d0b8800d42e0780c100007551542403009000f402d1081d40101c1c90b00300700521156901000040c91904090320503190a1742d0351a8010400c031302900440020300c0ca40144040071030740c6d04038144c181403c2c042d2100004400c480251070238502413064003500100303a910380d400c044031809400e480381128031f0890a848814000014803400c1084000c000b14800d59011413151801b40030140307000c1c004800d91001 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 578307410 1250 578306160 578306177
    0x4081b1c02151e0601091e080d140a120b0a12020a080d0534050a1e12030903020a0b100906170a020d06090f0807020f040b09060f1f1e 59
    0x803a40e010a08906181403100c01c0c0c2c042d1315003400584c3c1305007156020b00890049120040001d03c0d50004c0300048400c41c134140c8070a503000f405c04980320301903c843c0800f040000e008000301e003441000c10682032089000c1c0011502c14002c00603d1145940d880b802c9480e504180302d40440c2450703403594000f044200700800c8450b010180c042c04d83c2c00792240c1ea1441c2c2d00c04000c200e407405807240c4a0b50b0f50724582d0742c0c01280e91400741000380e20f54121003001d40b0030100e20060801c0325800051410725840d00450162001440d15104802803d100300301035045204010072440410703404228207020310301c05010b01c40702e2403038009a001503a00503403000c46070090344001425040e42c04160240300550484e00700c09841202d00c0c02c200108101e100181c0288020a0f00c41708001441c0b005001d4180206c07079080c0c84240c22402c200980f07242005d400c1d00200e071240440c40347c0c10f011800d140f00030f00003400d0714a828a5000d08102c03e1402d4007114001400d041c1400441480b81c800c0e0540924051610205 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 578308660 1250 578307410 578307421
    0x30a0b070c050a02330f090405060f19080c030a0b040311341e03060e15041b050d0302060f0c04050303070302010c08010b04030b04081b1c0215 63
    0x410009058406006201414000b044010b109071003000754020b0001802c5030030781503400c1e40360002c00061a4541546103640c08510707010001e0301c180030052840c0c83d180c0000d1400340f2024010240101c2c0e005104240e0b860000d42e10500c42d44111608505007a183c00e1a01852070324059440789401e0003500a10340440104412460041d48240c0506000f00c0b0301d130a2800304c45c074002d04408c0320398400d1845100300c4a419951f804006901000c0c1e82d4449461f5201e42038011043c041000300d10030300103645020000078100740c02401c20f03e203540043c3c850010703000010310707a030503402c45045514181d018400c0300014800340591015020994620b5139500c48c968003e0b41c0d036100500314806a4071494005a500c004150480d8040c18000e8256625103000e440c02a02030b00713001c11207001146010001151030103c00040c2d03400c43e501b00d1606e220366162601c800d40d0310f5020047c40500e142c0960002c2c507000303904220340c190320b95103441c45a03140c0b108032000a043c00e0349030f106551000c007600203110 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 578309910 1250 578308660 578308673
    0x1005070f020d050a15060f050108013f11130209010504090506060706060b0a17090c012006010e041101021f0527010603050708010207021503070c080f0309010b030a 72
    0x241480d0781915501111103050900384e1402c9480c410007420307a084070188910400e1917402c4281124074480340503030349a44402c0195900c29003406440340280820501035110356a0321840040700c0308104a0b1101049041c51680a0031f64600013a10b41501c4d8480b811246c0c140300c0002150030100c3d070390840c208402400020464030840c800c80001a845001040181d0385039002c48409950042c402c0080a41c2c0b184585d0706178200c861420041031401580c94409801184194850901007000c1e103581c0d81200015540340000382c0e40c441d6038620150340540301800402110f400380a00d42d503050384c0d900e0186480301c4880882c00e04681113401c824074089102030a41043c541c01840102c000c5401e03a103582e8405401201014400450440003504210404042d0b10a0085e02d008000391080280ca4a800307500381c1c860708400a402110700281698100302e0710011f107411030b900740b40051075421035450b4910190044403042405880c00000e11507000424071035002898411b40c041d041508042e290b05 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 578311160 1250 578309910 578309933
    0x1b01060308120417030f041103010507020c061c020a020c13020702062709070822020d030819062301080708041203060803030901050406060608010803071205041d0402100507 76
    0x507000c51400750100c2d080040c40c1324200415030309032128680301c0c50400c51200708a00c0c2a42c0c1501c10003c0019500e40c1e50406006440c881d0708180c0050005a032050248030a0313a0004030302701034041c080c1c602d01c1154291800244000d11513035006041d0309201c401080013803000200c0007100f030351040181800507181c00c2e00740c40001440f0042005110030b440003030109072500907042648000031800300090503410001640c05840c0f1410b072905450106142d51504642d00140603500c6412150403000182c82040110b42c01100813005403090300c450342c0408280c43e03003900400e03580004030741ca00440242100c845401c4031824a01411f141c1840d0364082e102540140c4040d04080c07421001c000b003d03000b43c00010007082c84404483d034074035002d0300660003404183d4040b01c4c101c0c24084001103461051050b281a141001d002d946030502659a03880307000c1107550b05070184402032000007288601d2995000b0880e50105542c2d085140c28070402980d03810701035a41d070a10500780244404a14101034030b = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 578312410 1250 578311160 578311177
    0x40608010e060a080d030903080108010905030409020903160b09010212040533040b0301181407050c12041706070318061808031e010e06010f0f0e0603010603021b01060308 75
    0x81c00603544410700410548229600050400c2c400d0341003130a10954154404002c5900940d24100c070350341c0b00d1101d00d090b260040e601900580c004c0c0014812030406c0e07030090440000050440da5110072118007050030340d206034002041a200030440302c07102c0d40c041c04141170502ca40600c1ea032826040c140002c410007a4015000f1004075400d1402e001c2019000318100d0204900128030784072907841c0d420313130142d90090081c0062815881004d07000313010140994281c00521103100300d10383e519028200c40ca6008066a8030303880c415101342001c0606074000800183c00e80d100d06e0800701010034016440c04c9409841c80c4205460800c9581c01d00e111407003c441c600e5804040850004d101c82c5800c00704116861014161000000901406001e041c04015072400740042d82600b50b82d0b211140349020100321440c50226180712a090410f9100341d0840303200c81460300b08207880c130010781c0c00b20b811904240c01180120740d00003032200704480300206012103008010000d000306ca0955441010718000c54a0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 578313660 1250 578312410 578312429
    0x3010e040b0a2903161511070302130f1a09010614041502010902030706051204020d032606040612082a030c0a030f05090a0b0a020c0307140a080304060801 68
    0x1c03400080b05a00940d03007007403160f00c80418099440540316816910307544514400d20620400400c3d00e802d00c030380b90003101ca03241c0540408007101d200945403c40c640b1601042401054000b00042c0d84024000581c0b0080b1000091404881e4210400301c03000000c105107110750300e1500c0c0b821941c5866110341520200e140c40c2441d8130f03648445020a00aa40250052555840d090140700e60305500c488030ba10b00032001c90b603186503074410a4810b0710900041c0c250180c1c2c04c50004000d070610703000e030000ac40d21a02e86113110315401401e4065403601c5050894104042505202051606000e0000600300060741105408440d40e0755040c2d0b0f100e000c0d03103804220008444600350413541505002040669000e0301c2e90b5401c5515466280c0d0002c01c002c80200f0407060942c82d046109800f52040c074070028180d103031081c6c1400c00c500c046400c08100c00c2d003180304003c0c401c4031545082c072421004000400101075401e0aa0007000b82401c1150042500365100b40002c002d0b10354041b2459044075003461 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 578314910 1250 578313660 578313683
    0x913020f041401150807081006210f0e070b0a170604060e0703050a06090507052d0c0c0901050111030d0902130e1e0102160602090402040914091203010e04 68
    0x8010901405520300207640d007104079000010580a1304000440c80e01141e07940c58a65643e0800a490342c04c025203c3c4402e01130340c403205000c424011824101c49080c00046203030b090036090140300961781506124480182c4500b042c90519000f00403490142c09007096542c2440c2e00b0380001407550041c1c1d541800c05400748408592503407034650200c40a402484c0c4052800d00d402ea10103009418246c4807440034501c1e000c00010801e500c2c0c86428000c00166845500d4401d0411252200b03000a0000307a1682050005407050140280c0007003a0349000c0b10050140800c032a810402c1ca41e40c164400d5060061412042258070030100071101090740310040040d42d03241900126551024494044c7d1407107203007554854400100203441301101d1080d210078041c050300b840d01c05003030340a401d00c0c00c002030400d07419900c009103040e005401c85c0c00c1c0c00f600c0142401e41d51041d0005032681c107480300c49200900300c2400f0000e40240640c000c50035540c640203140d9494061006074280300144060301c01c800c04c6 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 578316160 1250 578314910 578314939
    0x15011401080a0e060103030c140a11120f16030c050405040b01051c02030a140d0915030e10110408160e070e011701030302070f0608010b030f07140a050405090105091302 74
    0x240d22800e01500b401c0f00f15415980c580c9005020015503490546274143c1c004a0110345c03090004681d000c0030741c4150703021200c005103010b2054004c4420004c102500640b4281c440c4003104120b2200700280c50812251980d1440c1403003c664030480d0845401207082c1400c000110341101510350441d03005540d81403408040d001c11039440d0040c01030081d49405010401002c2c403c0404100d020461100e041d281e9150300c010050350b0382c1001e0700c6007480701a03240805c201c01034041d500602e154107a4400307036901386141c0b480410483d06507034042c0660b5030001c50140032050301044203035418070a15a81e4651141800d000c40c600d1803000303001108200901d0903c0fa47c81e4418640400c0c80d00340514540708558591030040d403541d20300e0191001d600805040042c00d2849610642c0c1280c00c0c500d17036980b840c0c41c1c1104a0b4800d0000900010520104425803070301040408014181440d19941c0e95403a1030400042098280042e80401d00c6100800e00f8460117000c4005c0d40c0941c0c6070704a600d00002c2200 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 578317410 1250 578316160 578316181
    0x6130309030803190501090b0904110a170f0706110309090a09080d0624080a09020604050303070b070801060f080a0f060504090b0f0f011a0906041a0a021501140108 72
    0x5580004125207000300c01d006103130002c0c0d8860b0111a414000c01d20940ea01c90741e107801101e0407121f91036844642070010502140043d1a11880c488000e0000b40034107444800403158048902141d10f860750144401a00d500000d02405025201604c4c1010301007007110203140e503e00a2442e4030f442510f0220100d5a076010542c04240c81d554407041064480c0c0c4006541c000409481c4079545450301c0c1010307106c07031091300518445d0701c0110342d0f240d549541d116100300000510412000b10d0700200c08010104084e5010406400d8462041070685030034609004c000b8001001030384220140280b07450b03044d0705240c02c000040d40c8000720f4179000030f803403868034907050244c4416400b8a40007450001401c0620001c80403003489220429011034554450100c11255681c0034411001b00c0710803000e460002d0600c01005010b2004028416401c01c0c2d291400c00b11034860040c50313444030706e0000a103807050366010b01c010440c1c02d9003145c04481640c502070364942003d100454050405c220400040c0b90000c1 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 578318660 1250 578317410 578317427
    0x1020904051311060405150d02040803030f0901110f0a0e010221071e02090408070317010e1f08070b07050f0d080714090d03030e190b061011061303 65
    0x4000e100340141c0c18009980020840080001c0ea00150103281071400390410b10101c0e0f0032100c028001420244120700400d800750404804504040e408000000303203054200b0196009104120182e40c40d41817a480713880c2144c58942d54004c03014028060300318018650015109a48260b080c0441c6000d80440100d080510612203010b50351404150300302c0360140c0702d024011075403003220f13007100c0c40d405c4e90405003d101380c40c0c5000f50302400c501c0010b00003840600262801905c241000300b0107910003802502c0f0400300f40c01860b003403220701c1c00b080300048020540766410a03010201da50b04909001160362141c804e401350800c400d100103200d40030031804105880c04016458191f828045212500a01003039046d1031040014811044030b0054840c403c0440c0e005000040c00b203222403150b80e13070941c0a02030488000f600d034002c85a140c9804502c445074101a0792041c0d0707040d422881c2c00c008000c0b041d82c800041d40100640112044c054080024250350417100011641b00842d4a03413608645220 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 578319910 1250 578318660 578318677
    0x20c0612150d080d110306130908070c0305100605220e0f030d0b030c0102070602030a0c030917100e0102040e0c07020303041815050d022413080f0606040507050403140102 75
    0x18010b000050034072248602a0600e100d6004091050640d010800390f4240815180c0d990300802515070403d204040da0b114800c03107446981200d00b025007035241e407504210b40d40e006848540050b06c610500000320302c110707009010202e80003400c045400e680310304d60065014910407199625101502c1a1108201b1503c00c01c501070100e030360f41d001c28580407024185e8407410358080c0c4224030048900e98000b09984055510560045042403484d00b0120f84005000d134040d0140411604c003c1003000b230112101e0082c00801c8005c2c101651421211021240708800410440e4814042032001900c11b03400d0a41001c034003242592074000328000a41940b007a6070041c0e03e200c0d400c520070900e242c40d80c0c000244003280030b003442288030741c0c031170520000c00104c2c54000d40c8001c0608100700350910000407200e1000c803421032141062071160100d000c0039110341080b001a8401101604101d100f00b04441d03000e2010f503014011130814282c040e007140207a000061249008020b100701d00002541903c1414 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 578321160 1250 578319910 578319919
    0x3070204050a0c0e0f030f011812020c0d08090f100203031e010b04030605040501020f071a0702010204031e050715200712080a020316030e0108150f010c080c1002040e0106020c061215 80
    0x1d10441e642045100c0401c80c9c01c0702c0c4800b5080c0000d0307000d400415074148203400a84036440600759076842a60591021450035803284c40100d0301c00803a12480c524074008074550b001103540b42858000e00100c0c00109040c081411080d03401803020b0f8504906480c1101d91001010078591103903e02240a8000e0f4190b1448483d804260030043c0001e0800e08080385202c18030148072500c42681c200d0070303403249002c0941800610b1010038004a080c01700804074500640548000c01c1e141c030300c4440c941c8210b44103000043c4139032045020f0302d03681c9850540b07070f120910014003200d440c1c0b00390014024882c0304064030000c008034a2850087c02482182c81620b101c0042d1005550a40f0b4040d00040900001c0d0340054500c2c4005075043e4001d00841c6040c940041c00798040c01c136090011108004030301c90403520144240301c02100369104100151303141c082c010001d621a8100500750706481030590010085622102c0710304426201c50084070900b15001d540c1807c02c0c0e4500700c0c0541203810119a29412 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 578322410 1250 578321160 578321171
    0x51c140c0118050307290708090a020409030305160507020f0f011223160207150c0606080d1106040c0e06040603080d2a0212181203070204050a0c0e0f030f01 69
    0x801402000404405d4800e0749880c809081500c9000455000d104000f22091404030110b03ca850103641810b50200d52101141c03180700341680071034241d50300c50504078046500c5600744080c034502520b07a8500d8084901c0d2490800d44c60390005070441d8003804000d13008403450305142c50f19900c0341c00c3c030b080900324002081c00800b042514090703407101c201b6080100310b0810008100c807403104c07002d03d070381c205079550050001d07a0404100e01016182aa44002403000c0002100c00040c0140500002403210202a0005410f408009008680c0303003010074100740c200c0410440000e6190310410140d6001c0c0880030207030341d01d850100c1d004003131640001c2c02080c4e000c1401c120b0401a900f210810a010080c071841d2008100300d04a031104840b510319002d600a00340c4540300c420f058000d420b060b0189540200036012a1012a0604410301c00c0c0c038000d42c000142840560030300340207e50704142c04642c00c001440340ca2900812901030307840a01c0c41581d0403c1c40240e955030411440c0c1030481031030b001308030 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 578323660 1250 578322410 578322413
    0x1803020c1c0c0335040303080703050c0901032a03050402100801030b0a0902131103060a05030313050904020a120f050d020d0e060913150911040312110a0c12051c140c0118 75
    0x13207900540700480010300d03000d0000364968400c0c01403501803c00d0745a49810113a614005502419066066101c260f0f241c50740048200745101c0031946503074540d02c00107882d0600d401440a200c0e0203002840034048000c0c01080005c40125241e5409180e03084005403d40c813600c0001e050a000000c4160110f081c0810440c01003000d000840c09103004994040c04180e0360030606860b030007000082111010040c00400150034121090303a442072004062000c640c0d151510b0f50040e42d80c1d8074045e03d592440181501c01c2100c10049002c140105000500c80c28950304802080c441c40050700a00600000c80d010f849511001080c030507040602c1d50a0204011038540e1002c8906540701d01160641006906e40402160074112406e498100d200a04130300c241030025a020070f0040e020b010b491003a12032050209003001e40314400780c1b142d0001140c100c08903007800c40c648007809040c0c0d5100c0b60128001070750a600070190310702440301030055a803110303080c0000c50300418000c140360102400501c035550 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 578324910 1250 578323660 578323763
    0x9150306070908300a110105040b0f07020a230a1703090709140105090402030a1a060a0504180215040b0408071d0c07060506041803020c1c0c03 63
    0x20030358180804540d84003500c2000c03000300810800841d0302c00c81980c00c1c400380c0382c040704005009501160804400c00b07540215031b2070071035200700c9040d0340010000091042a41d918800641c22101e94401480e00200c1621841620703541d03800e117100f80752100c040108414505011342c0409139088074044c0014036441200c80d0059108941e42d4105006980022804000910030803102012254090b18182e0918003440303a02d0710040c5c0242d9140c0304410810f800a42030b900c01c4d41070611004850a05420b10005120704524903030001c0e4469400e0030424084030300d01070081243d10750100c445064402c0c042c440c0003500c0c0300e1034100280701140098045a00030f40081d1420446d2003107500500003184a000c6450000010388a01c211040d04108000c04286503400c0310740c02c107030001e10003c1d080603046604008403a4040c81140547c1160180e8a42e600d012114802400302e2145401c07075600705640c40902d1150a03010082c072045084400f854109081c02c941d592108614041c1d5003c40c00741c82001 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 578326160 1250 578324910 578324927
    0x70804111f020607030603030503010504150e0903091c021c06021905040824160207090504030e15160f140f0f010b0f0607020d031202031306290915030607 68
    0x768007500c6201e011800b02031107841040200c030f401d83c0d21b403411a42000108030180107250b111b40d071b454200040100b2600c1c00342511500840c1703440d0003195264090000d000c05a0741400e510401086421641400350311028103265004000303840000e0007441780c0c40c1c214002d0041807083e10b4840c0f40d0003008400c030341c0c11000504c240d80c484004c443d00503060007805a50072a0401400d103050a11001140c0340c44150803070340341d9010090064560703103610341d042202101c1c4100c03011350000309400140920340c21704081822110b641403c6440c030300401c00d01c280754508404600108480c40384500c8600b40700c4d1001034416044413103410b590019010710700e15075850000c2c142200c041d500c0c0c4160a03403a40341c1032105025410020388805e09010064003007100d14100ba0b0011340910151400344e5100503480e2005610035200307004000304500d42c0e41010011125103280380f090030400850b000c0080e0f60031408014228004452808441d5a80041a0509a98a105550140300d02c00503c00e14a4002080 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 578327410 1250 578326160 578326219
    0x1b080609010c11062502030706020d091202010501080309010c020a0503010207050c09070e030a080d020912010e0c0301050411041503140604030311130905130f0809151207080411 78
    0x1d0382d501c104000e1041c0d855200654032581d450342418250004a209549040d01d005c2032401a04c0c205905a00e0b210140d83c041c0759003080c480c1c3c0d10300f0588100305020321b007002001102c0c1700802096040c41441c9a480c411302e00200d042c041401c0d00c0b04115501c500042c0c3c040c10018000355281d14603490b007955107200d004140c5101d4400b81c00040e00640c881d101244c8074840080041012070181d840e44180c0e0b5003c83e907103011498080284903902e481d20703124070101c1f50700c02000190042a00000c50b04080c85801c025100340d040c1000d1002090140e00814900c00007140d002480d1040004861217448080e480204409900328010781141c40200e41284282d00a4506200710b20004030160190720609034100c2c4100ca80d03072010301c462000d0742c2c0025400075280d4400d80c030819160300d4000001081d200215100080040d448905007058982d0403d50b14690030b206080400c1d10001c101c40c000011703c410708002c261400541417250f0b1007445607002401401c0700015003e01020300c11440340d100e24 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 578328660 1250 578327410 578327417
    0x70e0a0f1e062306070602071a1008070605180612040b040c0501030903050d0b04110c0109050f0a050709090206120f04140c0604171e070806010b13031b080609010c 72
    0x140001c8814040203806580c3e41c54500b80502d400524007001032640100f48203841d442e038203000803000580c3d841e1050452042010701401c40e89070604840f10010040d03007008699800401080084d641c000c015140404481c0085172020200700005c00c51078049d0440d2642415145018401400341300c600f042c0c0078502444d0141d0600d030b151801503050310220313040100021420000b000c26120b10768003030b8002801c0100082100b042070703091100250003040f01c1e1403241c0d641c0d10038142000403c003d800b544c800d03482e0281841014540b00c0903184c000510443e44440e4540c044c610031566000c007264840800740c0854000c07810105032061403904201e0301210520102c200036504680c000400034200b400043c10945454141074100c1c8041c0f0a070101000244108000c0d40d465074580f2080201201119004008451410702403d1406406a1110607030711010054913850f402c0c4000b00d002036940005500c0d0f507207480000c002411002541c07201c1c0c01d0340903450034044c400ca810340240410600075034 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 578329910 1250 578328660 578328671
    0x106030b03030304020616050a02041b0912020108070f0201060e100510020703150b030c1809070e010501230c0f030a2307030e18090a021011070e0a0f1e 67
    0xc1816582e100a45010f5405981440100d21200c1c2d40c07821454042c0c4540700740c52400080d54041015100220500c040786030f00e03455a01c00e0a0341c080b80ca0002005103200100c9281d80f60f80028160720401b03132440040002c82c2c0c0342d03809054001d4002000515866012150304e15201a0140c040619405168440d42e02c01e04096206840002c200301130303e400c4845844018807003245980107000c120030041e014025000004c2c550782c0d92800c0e11400b1182c8a103200b07c83e1400300a0103007004003540083c1c856a45c500c00511007a43d010002c80da100740ba400309100f00c06441100c02c0b0503070107406d03100081c40c402c08440240808001c406041d40380001e03101c2c0c0b07001d4000450b007034292402e400311860030755400f40504008a441140c1070f0310341d420040c048081c01104400046420340c01100c0b0350310070340c0c0318000a10441c01e00101d205010031043c13030060403c040c2c0640c1c2c1500d075205882510500b040003c04135062580d5640f00380c82404a1030000c0000460140108201c2e0080440d070203803030761400 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 578331160 1250 578329910 578329931
    0x30e01140106050a09080703060608060711030d0c030b1f02010e0c150d2310170c15090612060312090d0602070606120b06150c0a0305032d010603 64
    0x140240e0200120328610030526a003807000440d0207811a099420410000b0600050340b48010310030742c40614011480840c080c1d04100d5103d190003400350003c800c204d2100581c4442003404400c0c0c4918680c5407401181102b0305403800c4000d04070b50600b143e403041c41c0041900380c0c1e00d07510309070780c2100050350000e0054800d00d14650391074816000d0f55503003001c1c02c0d075160030344d00d040704008148551032114001200c0200030001c040040200324001c0040400c0c1040c04100c4400804000040544030148500323076400088590310303122600795407402405e021060b207540018000644590403405031603d6140d842808603808500030130b6400038080d009118042c0d0307074804100d0455100f40400b80c0985e00c1200207540c0c0300300a5000c803e0a80300690741d44000704100b00d9018224200324020403800c4000d041c15804c000c2d2825908110b000c031098204100f401c4000041584180141c15040158503030b0340d0341003000900100f01c03c600030b45115404203507040300411001941600c06c2541c0070003240840c2d = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 578332410 1250 578331160 578331163
    0xa02010c02061005060318010905030a1719150b160b151f020f1507181503020c030c0d020607090909080301050d020402070b090601170127020d0b010303050a030e 71
    0x1901e504543c031543d05018002030034254019504148100c0071411403400f201020707421240080c004031041e40000449110f20782d88004030307c1031680c5c00300c0840c00302d0420300c0c0b01018130703d03001000b0008144c407403400b01121503503001c0900050606052140e51448200d1080118900c04601100c82c0e104031400b09910b00400c008605e040200034042a041d02300100410600304c0c0004401c1c001c52040c082001d803100003e0028829540312840303000302c682030010700030b018080d8400c001d2101c2504150200b103001c8890b2110240122507060059a8441c1c00080b44d04601c102044c0141c40d1040d809210382240c1d00041c00c82c40f4410950702d10800c10f44440e03c1c502954002080505412014070060241d890074000c07034141030788010710041c58144079a9072a00d4510080300e50f900748d604440c0040040c041103c42c008040241d52000700403c842100030840c40b00b4010b08078201d00101d1780c90312821500c59007270f0001c1458102108111a40e564540101140e10001c6144c00290501141c0e8442550 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 578333660 1250 578332410 578332423
    0x1501030f03030504022b060c0507050d080606040f030b010f08030c060a0c09180b1011121617030105041407020a15110f0405030d02030f0a08060f1003020a02010c02 72
    0xe120008102850040c1c5046010b010090000e903444220385400f8040d520301195803100701c06007484414070805040c00c2140c1102c51141000050040c100b01c03900001c0c20105080da8800e0050030510700940324480815030502444e0444440464018004800c0c021600d0080b03048400c0c0d5680d1030080c50f01c801950b9141d000e0500c400742c05600c80c001041201c0302c01e8118030b07003200c45840c3ca031044075643c0c03880700c064144616405d08030360313900c0e103c0c00c0c0d06042c85111400be04403103080400503060f002148550301c2c03078aa5070807000c401c0f007c1010311051110740d240440158111917420813400824003000242c1c1d0081c46a41d01c15854494591004203000f00000e01c20145a000b4010415181d2a0b20460301408070413503048642e40c00c0507501c0500e000c005410400d0755540d00e5921760b0b00b804241440c00b08980c04070020755100340240603051600d642101c1c104000c0e440c080e28580c40740b00100da41e100d5910010359011000c0940368400c968168040d1010041550003403222034010801039031180c4 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 578334910 1250 578333660 578333663
    0x20c0f160501091818080a0e01020105181f060308040602060717061813120c020f0303030114060a02100218011701080709090f06050411010809010c05030a11090a17150103 75
    0x503c0103140c04c2e207103815500030f042880040b4807202c4110210b035034102141d4081440032010034040031400340300e0b5a092150f568040014101c103481c2100130302885549140002500d10813074040d04204c41d8640c12504484000c503400300c401c1c2d4940340c591401075201d84c002c0700d03010700240344200f0f0440c68507100211540164005000d81c43d110f101c180703140384e060343d00a03ca0000e00c41e440c108800003075000003161b0f00324665070b92404400c1c111031040101d041d01455055210394000d1006100c1c40040e48d040c80030085049405d540d50b0101d16406034200300c10510084040c1e4400b0812200a035100e002c40b214111090342c9030034071880360211030108036030207000382d100642c4132450a1010a00355405000c420f40113203481e00c200586a81e52905032003040f03901302e07412a405134003010b141d6003084409410041d4071000b400304413946440144240001030812032003545820f0411001200601164074604010700343c120460b4a5240700d0b80c0341c40340c00d01502e00038400c2500942030741042d0111039041c0ca = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 578336160 1250 578334910 578334929
    0xa08070e0607200918010c0201050c0d1806060f21030906120603020a181404050c06091813110f031207020f060c010507030c0c0b19020c0f16050109 65
    0x2580b07890300c44128600b10404070841088183d03200569842180582c402c03411004046440d1006040250a40364186803200640e0304001c02e120740b0785440c00554800110b1030400046030361203100040b01120040380003a098a18102001c00d8030413508034150140e030b03045100c030055408010000c0603030398120100500003812580090003518494248160b001003071b0f0002280158498000605016503948a003040d500350808240024005028a1309813007a1614408030711300c2d01c1d840c0c0c1c6440341d0301d140d00365202e09400120444542d031100d20404448104111142040ca01202e609035416403c510584103169602e82211003850312030813464264178042c000d41500d00d01c2500512060b00801401c82e840701c0080080849503c410014000c0c0d50100c0001180070305041070007404440c201810941001690200f000105500c240c4040d0400b41c4e1046c2c2d030505042c0215508001d0042810b018075a010b40822841012000509818010006180c00325816965401580c03000728510038818207 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 578337410 1250 578336160 578336167
    0x50f0a0b03070e031e100b040501081c02100c08090c1f120906050405150121030e03151e01080f060105061303060f0504110103050c09120708120a08070e06 68
    0x203043c400d014000c20080082c04603101007400c03070000d6050041c007002d0b401c0c2d10303403004480180152103070080840046055070104100d504068900e61034104403c440780740c43d02a600d650050a00c200f00c0007280d070242c0403041102046000c0000c00d0070400307070340103c2c1a1140b0f2401813003d25202c0300d074461110054600881c8050b40078020384801c1c102d00132035540d040d0b4803503130400403501d5400340d02c0c412032140001d03000340241e001c5000140030041c0c001d003841c000d034401c0c0303112020510307a0381c400c195805042100507e6800d100091600d81c04030aa04420040c3d54280480b0200c00e0303194240035100d40c05003c15980c3c0320102d41c2da03160020895501240d01060041041d8109140100a030f41c84c0301d00610021901c0752961070980b0b010088801071700356600d003044240448004c00d5402038400340390920141c20504006034031805a00c40340c03417081854800c203d41d034040070400080141524001e031494070680c541e0a0b01c1d40c0d04020080d03c041840300b0000f810f03661284200c81c1d8195002000c0a04 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 578338660 1250 578337410 578337421
    0x18191503050c182202040602071d040201030b0409120302180603160f3018020a09150320031c0c06050a0f15170309090f06011413050f0a0b03 62
    0x42d099829000f043d00b01c0880c0c02090741c0040d04ca280c003003074009603100260b038861415030000c0c07601080754094202c00e150100d0700f02c444100501c00640054091a01040c55540200021f008100e0080b0081103682036903203401c5140d0305078010703040229040c082001702c0503054060248910040b80c0c0080c40034000600d100c4842c0c0a51010a000318207490030700f0404010040c2e500c20307180004500704003202250540303800d051540c0910b215441c1070540e080707150340855010802008036400354203103640c0c480c424924400c101082085c000d64001181c448409804031803070002c20061041c480c000e010300c40c298800d00940480b02d81e04501c2c143c0c0da08a00d540d40351103d00040c00d0140c901028203449a41540c421002405075074141c081013002d40c2d07803041c6000988003030011030504403102c039001030000c1d07411656024074159000c03c0c1a1001c1c05103913a0840104d4425450381c00021444101041044841c641d0492103401d556040d42d0078002c40a0304c5042021050040c8a40c1c400407408000040 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 578339910 1250 578338660 578338687
    0x51b061207050c0708070e0709080616031112040209010b090603130204020405150d06090c120e0705090f010e06010215070f020109080301091406060403050d0518191503050c 76
    0x2540301400345069070901036400212410900c49501007401ca1b0b11200c028810a844804101e07002241410b10056036442c0021540c0c48401c000c10b080e403c4006500100c100c68000d030002d039480d4403c550400d90302e4020103225900707a00c041e00c05901441c0302000200e2140011000c88948080040c02c503810340e030b6160001030707022594001c12600581c0a020000301601d9000c00751060364200c406442e10b4485010044080350060b034002c8203801e041c0f007000782c9000e4000038010012201d402004c1801800e0300c0c41030b40740100700e500190b04000da540800804040442400c1e0503174030a0545110a034079000012681c1d0169000c1d40a41c00d070001003c550801d020318210103005a0600011030f28810316158908550803d034006140c50352507146120140c00312083d45541f0550840b6400d04041c2180c0751260f41c0da80c40309807842403050014100714044071600d17030300c0c0c01c2c0360004041984140c01107018a00020842c4503204182109840c0c0150310742c02030046511507003500049a040c000e80c1c50541 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 578341160 1250 578339910 578339947
    0xf1b030a0c150b1005031806061c020409050f0a030f0c0809040e0a020301050103231209090907090c1d010201230c040806130c06020d0207090b0616050109051b06 71
    0x1c81d40c1c0c3d42c0e841e80442c940e11852090903a50341c460301ea0700d40b01d1a00d001c031080d00b07003400c00c4040119004002000402c2d40c0b040c491025030000c005500000540c0380c070108004041d91903015007284288061030258000008010400ca40f00780d940e08040c1002290030740310100c0082c00244107550500c11103003107043c00c1d0301c00d5800d03440200460b41e000020f0b0700072908456081e0015500e40d9410443d00c99840100c04084000c415510010440c0148002609445d4080c10300c840380700f20381c2c140118006110421034100a08240c5c03804000342141c494028002070001510a004d2080343d10001809600610800d0f0040152000000034183d135101c54801c1240000d020710300d2000d044c03002142c8510304000c0d062280e0814800820380c9112400c2040d0b0301940c4d6880802158005500c1d02d54241c0d001ca80d2504460389140080358400c0030000186141c001c0c14102c01802402e01d80b50014002c05410514944d0702440c15240c140302040c8942c0c1802d0500104d198106804116117150300c000d10144 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 578342410 1250 578341160 578341193
    0x2190e0102121e04170604030e370e0c070501050a050c0a030e030c01091a011a0d1503141606020606010906050c030403230111090a0603050612030f1b030a0c 69
    0x10189819241d01000c0c4619007405c9403001c0a5006004200416400040110004408580709984100b103520003c08101c464140c0d0251006620442404503080341002c101810416181c54070710721300460300c0c0b030701c50b00004070956103036080901058141c1042d10aa5014690b2440e0180c81c0808a00742a00505030424031480030344401c105d00000c080081c80f0f00b0b24000d104024003441042900310a403003070b0354180c104048940b40c0e480a2207144011302d013100d100011040340401e000d1011404203032000929800581130004010140e92500030101c1c04a04020040c40102c4030b168070f4607001c0342c0e10301d8120707500c5003c00c14011040c440940a2400b60401c01c1d0301e05c04503468141c0301d0740c9840d002a8485504408040e403000c0c88068144280240480040954029800c110742100080c1380307072200740700d40f000b855030b01d201240c00390701d803d1070040c1102030220407640c0d40c0449400601e00b07684401d10290200720111450b8848500210451300c00905035624a010b0070382c940ca41c140d01c984010305 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 578343660 1250 578342410 578342467
    0xa0e040b0f060a0c080c07230307030b090307063605031c110f090108090316020922030203031b04030c0b0f071b15030902030a030e060d02190e010212 66
    0x42d2840000d02c010000c01c01d20109802815a25140c000380d030048c9002e002c01600741020a01c00d1380010f490004401d01200d8201d00485640d07140e543d9000c4c11403050040c00f0b0101414006081e070a06070b450f10601c50080e00c454510307a41d600c1c0d8545500d030003e031341030020081d03041041403040903484000609171405050340009140030b4004052180c40d0b00510350307980085d001042002c80756802c24205c1c0d03440b1070114061480d05810a4219050001c4c81c0b00080c86401d08001184091b0300c02c4451041c45010402154200301300703420003950360f820417100d000108080c0040704a040c00d590717064900301d13a402864108581d0170000049100d402502c502d00c02d0310001d00c044008205100303850002c080d81c800e85151004d0030410390030200880d1550050901d41004041001a10005910180f040c3c2500d007000740c0d004010b0009030320380704640440c40b409001003080303d41002904c5112902420076114614101c0a120059898860416481e40d01d00030520045030340c0e100d9000c410020010058 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 578344910 1250 578343660 578343677
    0x1109060319031227021504060207050411070b040f06050a020406050324181006050f070f0804180501051c02060406141e0901030f3b120a0e040b0f060a 66
    0x5030b410310024107542c0130f44001a800c0b050b0019400d12800080c0d01d80d118006951600c2d00740740c40699511020702c1401d01803680d031000d8101c18030b440010783e44600e500410304021400c050070903a11b0640f00040a0302d01302d280a0100e10748002a00c201c0e0101c51841d12130354116039031a05801150001c0015511015019130054005659480a03441c2103040520543c0001d040110b41e00d03000a1942d0440c1060001c2017010122105003032003555040c07544500301c01c2000c00980341400081c080c95024110100c2010b84808480d090703901b045c1d040c2e45041d01c0071900006c001da000e0404014201c4041d410030400c02043c440f4600c1800c50140d21111411114501405256070200c0f004034449c425200300d401080c640100d681c11700849240d03000c1b0300c2043c0701c0d0011a40080c0d071135403090350010300442554900240c030944000d01c185a010f8041c4150740c401c0465030000c5409a20002d03240b00040c1c03074881d4035205450107101c0c001100340040c0c051022101e58805100141e8441d20240d01804a200b = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 578346160 1250 578344910 578344931
    0xd030915050c070c0906120206130b1b160608040f03020c06070b07110a020907030e010e01110901080f241f09080712050d050a1202040311090603190312 67
    0x50040301e000780381e06024642e031035100d400c0480803113003035403c41c2489506200c000c01040203624000b00d00306030115001640d0344d00600711810b042410784c0c0018484000800d0300310324111603180c9060702410a0042d07a210311407410448610a001d4042c46000c56541c0001c82c0214001080100c10284240101c8481c51000d10025040e83c006c810100d40d240b81c04820051050ba103d026508203007555001080c3c404959400620384e803000030b021104155445040340d140c0182500510400c0c0100002000032000180761020a64406c4170428046240382021402100c4c3e0481060f20410341408030100701060702720084650b00c1591071a590012449848054904040e003a104603007032640c403a824100d103080c2c146070801d01580e110701c070240e08030b4400c180881d801050842040406203442641d50283c46020b42d501410111410400d604c082004420085540202c112500d400ca031000103581e0703007804040d55015180703d1307c5d100e1911131003800006400fa00d483d02403001c2c15000404e40f041c21 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 578347410 1250 578346160 578346203
    0x60b0417160f180e0c0f010c08030a02030f01060c050a170d0e070513090c031103071203021513150506040b03010e102a0513030804060e0307050306090d0309 69
    0xa4008035004810324508100070f40306400812034101c09090240b0481448092458035403030040400c50080e03441050700c1c40245e02c00c000d0542540d601c15143c5840c0e0820b004603900a41040300e0642e000c20583c000854528050307800765080680c48001040340516507503c910b101c07d031a070010b08007a00d0a000007800058940103000403640303010001d1081619100411004509810341a85620320300454000070401905806003683e0b0000000403805c43e4090100b440c001e941da01c904408041060a0000c2560100b442c0e42c9403018146443c2040e2034401418201c10816040142000620600c03625000c10076004580c0c40a402807001614401c1720300441c3c251049011100c0490b004034039111a400154490b800091103144501100c11440c030040d03400711802c2002e50814082c021441c184440c0e8403442d440060b544c446403440e1110b6491001910a8403010b944900c40d0103030b05404a0a4140001d4503481025050300520380c0c1c42103138070306400900182200ba0390780052120398074013200c0c8 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 578348660 1250 578347410 578347453
    0x503090901150f0e1302091c0f060e0d08010e0a0e0106090204081225141e0f06070207050d020609191d07050306040e010b0909030d0c03060b0417 64
    0x1c001c5040c51003806548006210803030342100e1409000c060800000245c843e10003110202c0088440142e5852485001500d41c040180c0656a0304c02002400701c100720105004103802d078400c44d024401c441000d4840b548070307280060b150002803a000010850103040102c15600102d02ca81c00140702009000040e00391030030350300181d0005030002000c0181103400c0041030070b55207100040c1410800c81500030300d554503481c02c03101c842211581801090000e06110300b0003096200d1708503855507140440e10700c400450340c002e110360350051400d03002c62070b0800303d10540b0500081c4e010b04109802c01c0100500c4059034681039030400424007800e0b0300741c1c0315105454010200410817602c00e41c50710f04081c0d201d408000c4003040412001c81403100460b084001c0d41d40107101160049055400040c0715401006084012a4021018824400807443c08401401080c10340c000500c10080c16581c10b5041d14803510880320b03400801c210800c2901841c0364915500320b055011345000000300d0307a41055205 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 578349910 1250 578348660 578348669
    0xd080108031c0e0f0615040204140609011b0506010e0901020702280b040b120121030309480e16050c100b01030b150703200a050a0c090b1c0503090901 66
    0x180304401b0300c146000c500650103440502181d05515180c00c0c00e07203041e650710650020601454022848581c2c680c003a40061600300340100c01c20032950102c5c1429542c4817420b20030a0141109180480c2d80781c0c0060085450190b000703480c1d0340f1480c449200d8855120030514905100702c842c0c0d600891040a403000901c0184480c0b50030030344901400b10700c0ba0040708103030b000800302c40700901c01c0602041c400903c1050a030705414001031844045c240b10b840100c210280c20310001c0e4a1844228034a54440c45e101034141d644100c121041c0c00f10401410503505000c7c5d4a0800c0c0c04000003182c0303d906c100349400c1280e0a00e17103141000c5240c0c0d401d5242402c1400e1095140303860781c1900d4480c0d41c1c540710320118440112000166203140c40c0031101144544403000c0c08101910b120324070b82200151032046144080341c100c030110311190415540755001c1c2d40007221a010b0b80c00002580340c64601402c0040740000b4260105010190712404140000b1002150140410f2045060b03a64031844201d0092 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 578351160 1250 578349910 578349913
    0x70501020c0105011203200307062406110304090509100608251404091a0c0a032004050105030709090903050c15010b160212030a0306080d080108031c0e0f 68
    0x1501c05096150940307005800102160580f00c4403400401d1380100b81d03030062001c1c860410300349000c51003c02e0840c89225005007155041070704800020900402d0382c1480e49505600885854071210115100c030784040c9415801d600c1888188010307d00d507880280c21407000000c40790614503101d0f61400381c40725948000081d800c003107181110905085000345944071002d04009856040142c0c0c88080d01140c20050300403a82e0382d00081c200708190000001580190a90a841d403a2070462062a07500c140d1481c03000a003411101c64200c0d51880701981841441003d0710704142c104001103660307420080006042141c120070000d42c1361080c0c0301c4c03509003134025640c1541e1562110b10780d40c40d0000d480c02908902c141381004000d03456007102a01e60028180074818400d40d030034000070f070040b0045c40b000b5441d4000091411034240c2c05900c440e044807486001da4440b00d524140560b00c0d8a024402c80519402c10007480c480203115800003e200541ca103c0012074a21a004a40c50b00e0380002c03405546 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 578352410 1250 578351160 578351167
    0x903150902090108010903080106030c050d0f15050a050a1428061b11090c0c1005011409040f030c0c080a0b07020f072d0810060e16051204050106090207050102 70
    0x25401c01500490141c820040241b00c0004a9600100000c3d4140300b124205a55140ca0310211341c1718904440188104070703400e001198003003110350000d103140d00035595061402c1e01d0006444c00c100d045002100c0d0014406d064183c540140d4514402100e00300c503500010a01070403102d4440003030085003010b00149001285820904003902c54020200074800030007001c02058005550b901d1502c0325400d054400c400151036031035a140260003518445007803400352941c441925005036016078101e88510b01d0114066601c0020721611000c2510080c0840c04810420f4005c40c2c040c4107100603130381c4260404070a10b941c0d18215800c05c3e8007001d04907440620007040c0100c02d6810800c00045140040181041c5454040b6410301662103101c6480100406200030801d44200d8030020000d12003030b010746243d550800c5c0c0c41d4000780003a00a50b4010490440030030400010807407809100e140030f0310f0341441c0080d904201950b6103802407080344e4641d00c4030000f00f84400c13180040c1c840284a08005a00c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 578353660 1250 578352410 578352413
    0x110607020d0b01080d03141603020903071e1734080c0109050603091b03010605120706080f06101b021009090f1b050d06240201200d0c09031509 63
    0xc00d0304440c048820103040c2081d038100d404039031502c41d0b0232280f034881c00d902040c207886041d400385c0250101103901d400307904000584040481c015200d8100d211003150a0140c4800c0180c1c4101e41e1404400720302e5000c0201c44100171082c4003807081403007406151480c80c0044200b035180c0a00550080001d5400c008005680740d60866050b10240204540c40d5040d8502405015030710a6400200c40445c9107801112503030b0780b0294001000782c00054040c0300410a415a11540d90b1998450800001c030480009804a11502d00c1c40d4007502006280307900c0e5074540242100c820400c101d8107100c0c0806001414016944c2000c1540c0d9000d07552110260701d441c151a04007290345e2403100b5040f850074031068400c50360440400c28944540e80c08d009455401301102c1c81c000341540e40011501c0c02a000000d80304a007001c4141d8a0b00c0c0c01640240003050054022441c00032414428812020040c80b1035082c10070150084d003481e04041c60403000c1a40da07901c0304424a5544c00c0002403040d0b95059040 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 578354910 1250 578353660 578353663
    0x705010c0302070510030204360b06040302180103020102060c0406080402060c0f010509010e0d110a0201051b010218130b0d030f020c13060501020706080106051621021e0a020607110607020d0b0108 86
    0x32340c40703150900c1050002010270b541c00100c1a48001a40f22580c07030600360115a1904207580246801400f079941388420480306240c1403000b070005074007504c80d074000601c0c041415411038042da50644e558403c1c503110b03903090081540081c6410350040c09001072505100c60240f00f854425072000e00040b039607a460f840024245800003004100b00036000155214500000600103140c0354286481c6030344440c031325610110010000c00d1880554000100e45490040710106c0b0006580300310b03040c0c01c03180c13a080070750012900046903031504222900f43c403a021034058030343c2d03203407520b041d0040da89000029000141c252031603007202c0012a50f02c070005d00055a04115940151000d41800b080e030354140071010b0820f0258400d803145204940d01503204202c0420706103e262981e0054001c50103204090180d100c040e030440d00c1440001d500e8066801c4500040d4014040d40c000c0e00d410326201440e102c11074103a1950803070a03002041000040c00686401c505113078400c2c00361030704290650403d0201d6 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 578356160 1250 578354910 578354939
    0xa140603032104060905030703020a2907120b0d031701080c060418020906030a0f1415011b08120405010501050a0b16060f060b1201090903020705010c0302070510030204 74
    0x3402603105010080c4842c1407a640c000403a0000c005640c4560381e18500200a4058900010030074040403648000f090303000681c02c0e100520403e0030815003c0c11000b0744101c030841e03003a0005282c0720840840c0c2c0c45400346503148140c1001c4600411050000303000304034889510303c0c003140050402c045020821a020356402c3c054000040a080e2050b10b030800605680154001c0c21008178440052032100500b5a0450f00c4111016260544031303d0a0510035009160311602c8145030350070300955001c0b071481c5118440c881c1441d21030b1030154503007160044512083e0101e450722051840c80741c5001041c030380000f501c46e454000030170815a15040c130380203094490683c05140507180b42c2e0000d2080c5900d16007900c08940c9410400011340340346040002c06481c90340d8400300f00034039218000c078260781e849008040440900380301e0030482c0d0b030300d0007034108843e0307214000b0380140c101c0700c42800f041d840b8048d4402428001d00c12070305299101e4000074000044008000040b0303a00045c1000401c0403844070 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 578357410 1250 578356160 578356171
    0x21602011404060206010b0f070c12050f06190905030d060b0c0d080405030a050a20100c09120f081b030d0c110607201207020127060c1104050a14 64
    0x2040c10140f80000296440d681030244ca40102008181540c4000c0c07100f0540c0c410136041030040080d280d844c60325813103030103100000751290f00442d08081a21040095040d004007418440f40219403210741c902d80060501d40c004490602042001010350781c124026100a00340c2074070f0a6035a22107003510145418440e000081c14041100200404984080251805503929042c036039030740c902a40c0e04031600e40600842c0d00342d04e0b22403842c0d660340c06000a42104669154001000000c14000f030554403a04644101c54034a5801c0b022100020040c280c0242400d00c900b100500348544c14041400c001c202c2c40310b02150b9880490303c03420300a801d015000704071201d820000d151012212100d511220003c198a0a0042d02070300c8d10042c21062042c1c03030f103600203181a0340d81c0011a0315404401c2e804400140d001405d0303003041c2e00106c0c65a004000c0310707041e9a049040744502e40711041d2440c100e0a141a5050403c0d4105400242c41d075004562081032a5400010500308a0307405080c0e150f80032f0603 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 578358660 1250 578357410 578357447
    0x301180b150a14040506060904050f0106080c040b180303090603040b101a190207210c1a0703081009050124031104050f0307091e0501061d06180402160201 68
    0x820245060090f1460340319825200844c0076034035280416194801c806a80d030304107141c84e00300841d5100103200d040c10384060b0340c3e64601c0c1c5d0706d4003188004940114020790103008003c0001c0c01441611240c50b540b0307000090162800c0bc450301c1c0018642d900202c0d02524501509401c00c202c5000765200c49018141400241103000e4001c10804801d0203030340864420390200715039031000c050082204c03c004080118409000c441d12505207245160054400c031449210540c0104a911140c0c9840c3c103080c5c403c0d0750703003070402800d510100c542c244007030b2050f09213a4181e0b40100b010b401500803a4060f041c0d414101310000c011020031500340c8c08070000c15003010720709002e50180d0400407040310100c4004440ca2140c029078680042e0420085602ca098801d10b4440044c462020035078411042c00742010080041c0eaa03541070031b03500341e0340f100c1080011100c2d50945034540d140085c041c0221321401820f226000c0c1c40711000c10103e81c401001d16856407030300004081150703800441c42502c1c280500303 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 578359910 1250 578358660 578358679
    0x1b1809100b01050319200d0b010315080d0f0e2d03061b09010306090212060a1205150919080d0c1701030b04021504030b011805160302090301180b15 65
    0x2030301041703000c0e60020490180d110b081d020082805000c8418520321412001580d91f0020b140c00b1000f040c41c02500c0d80480e0400300e02c0c0d05c0d00b85c200f001c1d4a08071050100541642800c0550403191501c143d40144107009050310040c00680741d001b1100520002901c41041818101208031100040580414840e5001da402c02004100304545180001c40140c1c0d02611820540e0050300640442e03008501a40d1002c01c0700c1000c0200586503a0007a00180e40c2410480d4503402c1c5050b02c006620006051b503442518102d407103084103d0741942c0250028240c810102100300345000552480c0c2042c0d42c1034001141c61900d489483c85000c1e03076040c4c9814603441c8010a101e005142100512000d000071440200246c25034442052140e4180082244d03941d0703943e00c03483d04c100c041d9000c0c09800400c03800324031102c490a8a03441520b0181c100017441403030f5800100c034218003950080081d1a01552160320100100c011a00031021152044d8401a8145003c0a540944d40301c0d8800c0184182c01c0b00c3c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 578361160 1250 578359910 578359921
    0xe27030901020714030f03030a020310080d020c0d020d0f0b010f060f0207090c140403050d020c04020f1e2b051b0a03020d1508010207050615031b1809100b010503 71
    0x10300001321402d03066070a0680800c840001d044c115100c2d607505c050f002c00420054540781c1a802544130340486050f40c41c415031641c00c280c1d030380e4141c4840080980d1040a007041c50707140809030048420310042401148580a50302c201584000180440f05488960300501c01c91102d102103c02500311854850325400c09403d00135a201028403422114542c1e40600f4007495208000d03003120703285003c00c2d40759510340e28540075907512160030744507005004214802d0007914103030080307516902001d86040d00380040c0000e805401d91030391100b07020080f0100607940002c4030715128882d10f0075202140544001e44540600141c40004190040c1c0c42c06d080108210400e1380b200f501c5811509140c0103031103203841d0381c8140040c121140e603040003188544000590190540003091868812420345040e0740307940042c0c0a00d48880c0c00001d603d900050882e070001800f050441140580080102080e20540402c3e02c000000646682410741c01c00c00600d44018003a01900200b00001e1070210f1452428 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 578362410 1250 578361160 578361163
    0xe0415060807081b0d021b01020c1c0305010f1418070e0312040303020a1b120c080c1207051003020d020a0306060801120b010b070f20040b060304051203040c0e2703090102 75
    0xd407502078240030390100d0703001981b18142d401f144c41c601021000f15070f217800c4880300d29604c4190003000c1045901114149244500c00e0013418102c038880c00100140380e0400700a00d05149442e101039400c1070301e0042038045040e062110302d0003000c0946505021b07200c40c00038141406142038a161500c6010001000040c1e4009000f120064210300c0040119000d41e00c0f03a00c2000c00f50384415486100b105c00d5400340103020f5455030803103801000704c0e544100f002003400014500a844298070760000c03030007001141411054103c9203a854500145041c511814410890f040020003000090303544a06002c2540c0154925001d4105d401e40c0d64844015991101d0000341c0501031190003000101d00c403030800081e04211041c0d1a4404481d00981075000c1112070341b44504a01244a60b091480d0034400c2d080c0581124052600070340585403030886000b911500ba0f00141c011158829041c0d0000b490600d8104c1280c021420030780b003920f07a04110005030614103040381c1d80e402c09400c10001901543c0c0c0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 578363660 1250 578362410 578362417
    0x90e0307020a06052203020f04090f080319050f1e060103020409020f0702030c2b1703070e010201050a021303120c0209070903020301050f0105010f08060127150905030d0e0415060807081b 82
    0x7c03c4030042b4a003642c03464000c16507144030710010301072403000c0140b1011079145010001017a5281d0402c004540d508950700c50000400d49150802d0602d058010755002c028182c903039481134041c14003608d401e686110345001c0381c0c052040c200006201041d05802c510703060110214022088600800c00003001001040b90011010000c40c00e6100d921042c04000c505041c9440d41030741000c10a40b00e20340914050490400500701d0f074015440d04c03000032b04c3e19417540700382c8034500d0b00034181c40c07901ca0a540c1e92907400200c0b80a14000e000e541e40c5000c3c01a40c900301c0d001c1c400c00003a0b460110003880d41c03040c54250380e07000e04085c0d0440000401400380342d92040102d080004185811001030300c811006980030041000ca146d000d008030300380c548054800c4640c880490303d2a0103850b1f8600c0034a0702c21104641a801869450b821002e00043c02d207101b80d0500401c2040140005604943c01307102a00b0000e1360391100002ca00c4860400c1152500b240c0c005030b000b5215003401c0036015004555074031611 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 578364910 1250 578363660 578363689
    0x7050c010513210803090114090f030f030a0603060227010504050603061e0a060c030909050106050a08041506030f140d14070c0503061314120301090e0307020a0605220302 75
    0x902044184030300c040258108550544c006443c0c941e00d0034031520b0203002e080281a40c4102090040200b040c0190014402c6801c1503000013030360421031088500d80007580040c01c030780903139616441d0201c0801d1040c8014800221604c04c4140022480790925180344154480c003814030205000401c80c5840c1e1000320703039020408859220620141051203822840c101c140d035500142600300c0410f025401469802c03819000e52100e03028699100703091426100309010720400500203000590485000b2002903400c188101c0e56680d07003c0180d000340f01210001e91094400101e48802c480c140020f0740f4240c929601e20070082c0c50380290010029000142c6100441d000e00d500003118001c0c00520340c1c600c07011f0080141510100e0074418003010207100515000d55480c0c010110400342402d00240ba616845e20142c9000c1c116880c1110510041c4001c241c07104850104121040c01a80c0d4150040b01034140f948405440e59601a14400540072501110981c0540210280302590b1000000784112 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 578366160 1250 578364910 578364929
    0x9141c0204090f060204051302070809040b060409021201060e0402070c0e070513090203010602010c0206091b1807091a090123070f0b09060a090f061a030d030207050c010513 76
    0x2604184040390040c40b61000c040d01e400612642c0408014442e0003c00898408855801110100542c124100d20800c0c000808440c0d0070000c584250400d600040c00c0403100402c45800c040e9244100c10aa034003203045c884e14000940010f00c01507400c9007154003003000c280c8045051480c2ca03a21001402420b01034210710182010004180340c0c0304408075400a03d100c1c51114602c1d6640d80c219003e500700b80200c0016500b442c2c02e440e007446c8006440c600c5040f0f90401080c62801040c002d001d43c0050b14003840e0000d02e500b03440410143c582c414903000356041d555003540c0518002da80c2042804413070106051510800030014180c0c2e002c00741c5010942c03200d440d000200e000c1020109544102d0500900486e445496842131100700702043c2d201c2c100700d006459a07583d40800f00b00448000000051011180c498400d021817040d9102140e1168400303580c1c441911024000b0b03180c05202c240540020340c0010311041044001e00210503a090b080c01e000f818987d4040c21fa03520391410307001d881c40c007 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 578367410 1250 578366160 578366209
    0x6050702061e0409020408060a06120b040b0c0d09320c0f0609030a0305070b09060601140309070806010f051212030103021909090c03120c03020d11071d0103030914 72
    0x2e8030515400c07a001000c410300110b40d155591054039450780002c41d641c0d07283d03174038190300000c031821202640782406500855841c202c0e43c07a5603401710030b081c024024240c030341824041c0542e50314152166101d01e0380102e845483c101c1c1c2643c00c81c2d103400c0f226020031014200c40900c0ea01403003400a03c45075464021105040c00c045902c001c20310b54010b5500080e0300d48a001e15040505030840300412029001d45a01c0c442070790f400404694034642a11824001040031030461400803000014540001c40601076034070703442d601c2000a240a8081e0402e11714800c00300001c105500e005180d10a801c140000505410b1030416071030307d124081440042d024203903002d00010b100c05400004000303004504000c20015555040010400515001c03c5a80e10074880c031404460b40148040791120358540d0043c0f1450080c07290440d0110f0803030f00503116034803d0000101d03002e400c2304080d1900c042c1a219220142d0b1460500400307948260703000340b140c3c0b00284801c03034503a00c0d403441349049c00201c0700c0500f0b207 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 578368660 1250 578367410 578367457
    0x120c0f050d06090f050f07022a130504110316031203090f0c0602010c0f03090b04230f03090109050405090604020609040e0102030103320303070c11040504030c0c0503010b09040b04140307050a020a0605070206 91
    0xc0ad08040e680c1c8104185070000300800c1048070809031380000c9040d400c03940803401050141c041884180006400c2034514224410454881d030461409a03228809801c610035181d540c3c444e001e4019001000076035154420f12800c2d5600c1110f0100e501180d190512428240d5240c07004150000303040500b54031280360200005a540c41c5800c40420002001c60340000c00640300d2544030f400032001c0324001540103000054920b01801402d001d10940c4010b030809860716030030842c0a0f4819050030303030055210760b0320018041c8284003441c001e600620580a8120007984a0145403164201c2040211185c04181c8040300000099079800000380c04c00c800b443c801402d21a802c1d01500310a56401410002003204055002201180440c451070b00b07808001d45a00800d400d83c0c801c0840c2c01d4018006d800001d000c03401e08846241c110b4068469483d0002e07034142c40d541103901400d402d8900782d100d00b50b03c10031424808481c0000301000d1805508100b010350018030300d40b00d0111022a8040c44002111 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 578369910 1250 578368660 578368669
    0x80703020313080d1b0302100c030e1515101b0203010204030f0f02030708010203160311040f0f08120a121a060406030c120c0f050d06090f050f07022a 66
    0x30798140b5401140d410940d03680d035040390703181118100c034400906a981031040e00d401d481d004c509050350503006494061198090344c1c00510742c1e82030500c1059280d40b9424128801480100c21002d10306410190900d82410003014110076000c40c00d001d201400300e4a40141d42c0480e40d2102109401e20f030199a1405000007070280c003d54101411076001e42003180100315824443c4140c55102b541a203a801e07590302140ca00700e000441c1d02250741081070300001c0603a4820341c0141441998010f0b49800c06845184a00c4491002d0300100030504d90000c080c003c40c44100800c4d6000c1900c184010318048140703000900022090f10040c5c041a1500c56030a00040c000c1d100300000f40004d403409481342e540b90401000303086c584450030041800c0300d00100c0000403600a040103400c26840e40c0c4106541500708a4a50748004141074801703561b040042110000390103034541005546d0404561424901d0920a040c0400352030071017554064010329100071038081040e150080960b0001c8280d0340201d0119 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 578371160 1250 578369910 578369917
    0x20c100b0f0f06070f1b150f1d01020304030506090a0510020705030a111f0f150e0711160602011a01050a091712070f1202061b03190c080105030105220807030203 71
    0x14009003640c4c0300e92400383c0c00440110308440603590000c41c0501d0b1f002042d60240103107104500040c0b1452917030b1800c100c14100d41403000c84184112803074980d0b04d480f0541029000e59140640360404030500c4180041007080010b4150314a10451820703100303540d0b00e66244100404a0700740640a04107040c13442d000c1c08003029030700c500035113404010300c0c007481d8000600c0700000c254821417414880034443e080f0090994207903412050b145104d500c844400b038914020907040c103030441c415808101425002c103c40070000704102d4001089401c100c004a4280d401c0303a072402c0d410005c09014100c0c1180c1e03c9900d050844030f1076840300b00107000300c07010941080c2c4100030f50001110009080f0040003106800c1c142c540c0d0103030705100070400718200d0480c2c441d041510110103d04d03682c1c0700300441800b00c80c02507070002c1741000c5085040415121410958241781e00c010b005c11040e03c010412401e081c004e0303582c4020300c41100305018042480080c15081000b0b00038080341c5004c248401014002c0044 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 578372410 1250 578371160 578371163
    0x2032e0c030e0a23010b0a1a07020d0503030103021305160c080c120c010c05030610080601031401180e010e034f0b0711100c06020c100b0f0f06070f 65
    0x1070f00d100140e5810b119a03507290100c504c000010548540007803c80c0107104d1504c4c001d000a1803078682502d8030194480d4080c0c25080a00818400c0004400607581c078400f01d00b1961065014584a41c0345004101e401118502401412030a1404201408064080e0000002a581022010b210550516070098040d0107000b1000e44100d0000560210341000a080008440d400a0005600c2074034121094007080e10300c1600140d0700880000e80c039000d40201680301c6018540001c00075002c40b41d000e141c071004c1c0e00c95100403070110704448030000a401201036040c1c01000038040d018002d560650740340300f109084c0c074001841d00810125902c5450601090341d076858001e82c46075040807001e50061001001340b40d0150083e02d00041d0968000c1c05580156401c02c0da10b42c0301410a0090011501403510648208051109014002546480601400e800c0d100042004403400d201410071102c203110b00034800c0310103107445038150703449502801c49040e00359105511a803051070141004042c9100 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 578373660 1250 578372410 578372413
    0x916030b07090803130918050703081b100b010f171b0f03010f0602100902090606070201050918060109120506160c140a02090f060a05011b06020c060402032e0c030e 72
    0x5485c1c0c04441ca0032401d400b91885598100000d192586100d0300f042401c4400410642010808001017013200001e40042100101c480000c500045e4040d0b040407504010100e0341941c54281c1c5045590101c0c010841001d01e09281108440c00c84045201c079100407d072103199108451035445440c1c150b0165031000d04c1c0d4589198070795840d2140141810f4007801000014841c0d40d1180d002c1c1c00c1d580c05420341a03a00a05401000d0f2a8141407010741d900800040e418050104064071860b104c1d01504614034012882011103420b01134001442d50301154044180d83d684002c0150114502085503a048a002c0c1c401e903201c4e40c5180d86c00e803451000c04c1d034080c0034a00807030141e00036800c01061040c080d603c201e0f440940c82c1d03140d01c2480400f003002c1c0d84858011504045c1032041e5401030864040d420300266040307991f008a6525034007641d00850040070580c03c90014001103003010003807140d50000340080e00246e20b0301e281c0024400e00030003102c02c090030b40302e03401c1c00704c524025800703603c8042c0c0340030 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 578374910 1250 578373660 578373667
    0x1218010e061306152409080615041805100e0109020901090204060e010c03020c151608040306060504020c0604030f0c2a06090506040311060f031306050916030b07090803 74
    0x200300389000b6000040558400381020307201c0d07001001d040c8440040d82c0c600203a00150b04400c840712940184070000c210180048003e000c1101001048214415059413506401c8003420382e05010a880502c840c0c0442c4800c51a103410005d10081140003a0b00302c0340500084d03030821104142d01510001c18040d400c2400381d4000b188040c2150018020f5034060b84901c1c010581d4000119071810440c40d000c2d005801200c4408520f103007001c2e0707261030190380041d59810000c000c2b1081000c401000800c07038140900050401c10000c2a00036480100011542182490b5040c6010364580100500c003c0802a5003a48840c2c07442c0030b403d082c0681ca030480c4446842010401c03101d01d5010710350b1298440c4000704100055020b100b0307c10042581d901030f21060406107183e80d03103c28240115142d0f0340c01802846099022503180000d14440c08140d07031903070304a11041c1001011a480508894070982055907000c0c085035901001030210703903009032000c4250751150710840311014130382c0100b010340c000003 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 578376160 1250 578374910 578374921
    0x10509190e0718050f12071503020711031b090a0f0f020301210c06200a0c050907140405010c03030902041d0c01090317031f08030d111218010e06 64
    0x1c088034490030a6072646800004038500c1c14900884910842d0b6018561001a10290074030f510000a51400e00c1d0899910b40d0f196110300301c03000c0c0307054042c40000c0e07404900706051100508016403444819800f402050b0030760b801d1601c240603500e0942d801480407001003203040c1d140382d10608411941c504204412400d041d0040043e50080c4607061105000c901340382ca00c035641d0050406015400017800003402c0c9040c0703007914440b11035040314500c1800c0e0590900096024050840c545100713040b102c10a5040604101e007001016158004001500f1100d01e41d4044040c100c40a44e802428216007000700c51400b28042d040014000b9041428a0700820f1042280c0fa420502c807a201c809031010610314070011907040d20184409040000c11003900c0a500021800031600010980251900e800382900d180201c5403461f44482c46640c0009005904103c0d503120701001c1500d28056281750410b1030394480803501020380314401a8000101e51400b4000944c4107003441840f050a0300d5651814 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 578377410 1250 578376160 578376179
    0x902010903051504020a210b0711060a0c1701080c01050d0209061206030705010509090f0705070206030c0409051b0702310e0c040c140304150608030a120b0d0201050919 74
    0x1903d049000c6c20010038042000c0b15a0b0701007a80c403041d0880100304210960b111030004134000341218080c0280022401045001400344174403070200442c0c08583c1d606d9644004001c0070b901002c028010114100500c0b2403440440c0c181082c01003403800580302c0b2010102c00000b4400c0070340f115449880020300c100ca10303010075100c1d0305c6440c084095035007407555000156041d22900c0d1110b0b602103444400100d07000c0001344d0241d08000e0ba071420724240038641c3c1c0810400d0b0301c15a603104154501180810000c0018000c0b1940602608a0514600d04619101c0ea40d401120130091041c007011170a1148100500d02181120740380b854118000c600036412a4020700e440e0100c1d4540c1d01480c000040c0c1800c00380101150502c01c1c3e83d80c1803040a0b1011610030b1900040d00c201d5034018803008a01640a2a016940150803500040c0d40d46040b15140a02520191008400d295041000c98081980c80003810f110842c5c0a08001d80d031205a83d001440003d603444401c1c401c41645a408500c4010 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 578378660 1250 578377410 578377453
    0x501020c3f0f0c1021020c030f04082e051515180f0306040320010c08091c08010603090204060e040503030f0f10090f18030e0102010606091503090201090305 69
    0x14840143c402d40020f1006010841164a0707059010134400140f15046000300100300b40d019107070910045c14040c2c411804c1d03045a01040304101000000f0074103104030b650501030041120240c410070401e000701c00b8007040c5c081e45640c295201d0b240d40c0d10000f5028195414a4003065070005001119100403ca0801219001050f428560400c84000d845460414240344490b0440040c010301260365243c0e4101c0c0e00c0c02402c010780a80d4180d20001640f400d100b4019a000c500c0c032516540c2c8280392010702c0514100b9030501c0b6140180c0c021041c0c02409402107002410344400d440c001c5a48084c42c0040b5000d80041e6000d911104a15001c00c4180000400914003422150b100800d450316031140f03000342070707405980c0c00107070084010041041450503130143d038025268078004078081001c0da022100100440380305901282100705150015a82071040e440a04241d083c4407480504103242610500310190025090554910043c41560b021b05400700003986d0040407103002400c50500d01c8070209 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 578379910 1250 578378660 578378683
    0x5032205010e0120040e09120c070e090d090306150305100b0906180a05040f0206270a0305060606030403021c121503051506040f0204031b0501020c3f 66
    0x14a44203520a40609080810503241e403490f81c81170030a07050180c21035a03000080c0c01c0d032440c1e01c10701d04c40c0441814481c0240098000880c003401c1c01c0e42c42e154002c0c1c3c400400800b10312507504103420040ca081c0e000440642580d030000d800145007901d49a07070918013102908046d0843c4107445030000790f1a1036411a1030b0070081603e0b05913075500d6803001e0214000c680e44001aa92040d100082c6003094280d102035417050040d2010b001006442e0045a515845402c0c0d0840c1b080d40d20252600900c0d40709900d000a140a403071051095245480d810b4031880b002c2c0403980300707240001c0441c0a15108104140b2042d01a40c41e60854000088001c5c12402c1c0c840300f1000d006040440c282c206d8a034144126080700d03042030280c03e461004500715841810002e05841e40550b80318404800510b1034809800554800c180441c0d00c484075070481030400440350300c107904661020310307050034070b88803603519004006030000343c0610229020180c0c00150f150000e024085001c12404001c09600000c1c80064071 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 578381160 1250 578379910 578379913
    0x1201021c0e070f06030b0613290f040501050708090a060f09080109080a3f0b0303040807051507050a03080402040f051014030102041e030b0a0501060e0105032205010e 73
    0x1c0e4803900d00075849011034860000400641001008198000c0d04030615100b401065180303420140000f04440150780d03006500541c90fa000f4200fa00035a45481c69102d504200801d4109003601802c003409210301d0050364100800800c000c02003000607000d032503080c4030080c031202c0880d403280d5009056040340289500016442e010010f4400c0c07062040d40c8202c1c0e0804c9540f072421500c0c0f9010b8501d0b10040c803070b04403403c0c04042c1c000b040a101c0c10303c0e05501c170040d140d10800c01005126603c186c58105031907501c00c3d00b0400c4100481080001e0010454100303507442051481884090107240c011041e02402c6070060003a03007410194001d10a1b031040717100b1601045000b030401c01c01c0084900868110035699046182400b02400c024034500c0d50420050001d4645521020010310300d0319484810003130304014041c1401044500c424680c0e100c00040f00030022507150000040120905814850600c0400070209402c1c501074203615600c00d5039120703000c010140ba0710b0454020503203184082d046 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 578382410 1250 578381160 578381171
    0x304030206180606040506131113050f1003150305010e03030f070c0209061210020f1e070c120212030a020f01050105040c0e04230a150e0103020913021201021c 70
    0x2a640c81500d10141501c4842c0180403540d10401030000401001e02995400f0086643c0c0c0a4045064012005031a006481890f20744100250721120010503401c800e10030a501b0110004944920042d000420313074902d004a00400220404c4001c0440c90304003400550810030308007001c060000c002d5000d6010503610032400d54418100702c0d800d00140c1002540401e00310003155040c039101c00e2600980d41c5010641d8101038210811000306d07444445513504585002c03407841000910800341d666070400401ca100e290517415940c112272020240100030b4002c410118050554495903440700c0507103075501c2100c0d80d503c1c40c604080c4d175441941c49241d240d5801c141c00802c05007014002c48080784030300c0d1110089200290104406046012201840880c0c0708051029084e00c18504601840d484480010700404d00610404070380840d8000d0304012005900410044e29911100c41e40580e00000b08401c3c010b0030310010782d00c0b00302488c25285940c00030442e00c401d03104c806220601c483c41e440c400c000 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 578383660 1250 578382410 578382421
    0x1e0702180f0a05040506040210021e06060f040e0d0c060204030606180506040c050d050613060f03050601061b11030a0203010c030213090c20010603020603010312020d081b070303090c09020304030206 87
    0x640c3c804076801441d640042010a005041c0002c88913004440d030b0040e01c138454501200c144031960702030074100b43c41e40501c0c00c0c410300381040c0e89500400001130742c0910400220100c00c568650110060904000c49c503410741081c042d0a0781a038020303650102d400c0c411543d07030302201e01c1071016541404a08619000c00302d00d40f45402c1c81002c0105e481910340c5401c0424126010000f4180184815049503000380300e01c00c0010790b44915800360070780c1d07065403d0b01c0e801d604091389450b40581048050080f95007000840c84000f0044210195000e183c41010243c0d8501003410a14040c80094066003025003074491b07650160080c01c1006d04003152040f2041e030b658485070648810f000c00c180856141a25a40040e040010810191041c0400804c65659a0340803550550099006552041e54003d100d0310690741405200200e00051402d808903080a1030844d18003422038220072100f10740040d00d101050300a410900205404c4603107400d105a8944280000c1c0d0300480d01180180620310000701c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 578384910 1250 578383660 578383681
    0x3051621031401050607020117010f060f0e0102152706060112090c09021303050709050a05010504052712130312020d08010e130b1005241e0702180f 65
    0x1450001400b448540c1a4604402e1000c5c1e5408a541607041001005405003800d0842022500a00e02c510266201510b4100001d100e03110380e5044000b04028100c00508680c1d002910600342c00c60844403a426448800700d8051405584000c0024400044c00d0503400c1c0001148403441031600380c030741041d2066595103200440e07650480090080760a500d090050000d503601034804000706502202009480ea10f42500d8100e8541c44140e410361074070108003449040b070003414010702c025141031080d0306100011208424100c13102c02281001c40b4001424160308001186d4011003920034556600c02154105030b01c40343c41e010507a0311500154200c0d07500c2d0f20010310030f0381c40e07040740e5280398659092600010800c80e02401105603002a1850000401c0e0019501d5000e0100c1c0454802c2151400043c8640f041d0356440741d01c15882d4000c110700500d110701c0103c8080e03000440c0c0c03003ca61104620200c0310307801803800103900201c00602c20b1034110b1100300c050340a0368211524074015039450306101c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 578386160 1250 578384910 578384921
    0x130e0706050f032202090a15090b091f15020a02030729130302060a0806150c0a06020c0f03031f0f03030c060903020a1b030611030709120305162103 65
    0x1404694100000f03116140e403030380140510650381c0c07130f4107100b140320b03400164944006889101d0426035403c02030602d0321003034042c0801401c4910040c800f05031150300150034420005c04031891039200300c60511240303030740c05040c2010308140302c9985072508588030002d6662040150480c040d11581e0004129108481d24104035081800c0001c3d038140003002e440d030101e81110411444482c14100040010703900c100c06440d0050043c0d8031241f0714501901000309041071070800054041007003003980980c04010510b410f040d504080c0150b0350b5010400d41e41e03d4500a07103419145400040b09000241c0f40954041b030240c010351088440b440c0c0c3b110000b0700203010b1440001c01060a084c00c80002071170541003410341d1070107401a01ca262245803180718280b41c03040754517800c10181d07480a0040144502c241000c001d03540081d00d00390701c0c010b44060070b81480790007050340303403500c4042a104240c89081201c800e01d0f00c440d02443c0700c0019261618010016080c00c20000c601e407295500c0107442031084 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 578387410 1250 578386160 578386177
    0x1a0709060215060a0b0f130611010b090c09060702030312040f05101104061d090103081e0906070b09100207030e0906030a150c02101d0c011701060e010e130e070605 72
    0x11200350900d0000c10017850350120741481c65002083c4003c00d14501c0c40d07501180104403a0b160804c0c044050100079003150806c2920034414070303202040c030602c0405a4141c1d10746078020740e180e55444080c2e00000c1d16500405000444a03d08401004104120a144000306500c601c04a80d5084400c2c0a494159807200c801800c00903018401041000c1c8101d0061580d400201a02490000354802084903641d09802c1614419000581140c0308020b83d0060783c882100307504004d0411f4800030002c2c03854414614080e241c0d007890340108060303a405014051600d000c110045584001e103240103800c80062400840c0f007110050000b8066050106074810f4260780640c1c510154000c28000400034011924948110701c00c00f0000304140d040d80c0301d0b915038070301c665503422041c2e42c9042026241a10280400c3c1c1003002c0d20590a02c0d00c0072502b40340d1306441c0d035800c140d040c100120b00102e0340c1810030600319070701083ca0254a440f2003010360100081c0700c10481070f1000135071228020b560910a5842 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 578388660 1250 578387410 578387419
    0x20309100c0c02131d06071d01030b0324070302090312070204140a1a041103040b0403020f070f080c060705030f0306241305060901050702011d0d1b0503160506071a070906021506 78
    0x400c62309143d03152080051405041c0010b03100721396404646041c04185140c801010f0702c0400748094845140915030201e541c1c03400b50701e460ba18401007500c40d10900041802e160020132101c0455565400450100e08180d03401001480c0c1000104042e0640360320f90003e070040c7c109075200382c0c01d060007004d2030301450070700507451600d0ba55291760a0040081c02502140113021491083c03001c2031080c10002d141840900140c1820b0030000340c106484800240d110381020800c6000050b004001d81c0e02003c845000c039622036440202141403250b0b40d40c45500306030348122011440c021590f0203045003c0e0410190b00b2940d4980702401613078880d44410074049a814444a00150700c645c4140342458141908001c40c5610703000456200d1155001c212944d64220000728031403001200858001c0208800070042000701c88102014100280107040c040d4400103a01c90910a010664400510b40305001d120580341030703040117115440b5805041e00501411203001d090343c2a006005004690007070 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 578389910 1250 578388660 578388677
    0xc051306030b0109031103070803030702030901020601081b0603070e0406060f0806010c020a14040b0301050f0711070302100813020a0b0d0f05010e0a230a05040209060301020309100c0c02131d0607 86
    0x6c0740c2c8161094a01406585841821804214200c00b4005035010700c2040d0025625641d00000290400d0016000041b065200e51041c0a4181041a01942a40d425690b29030759448202040340c160086035403840d005820103900040041d0302402607662507429036207003840d540b00c20004580c501c050500c00380d80034070508814040020801c040f08081d4800500000b642c03d074020110f425140111105c0302502c86031020022069001200b0820918030728006c1c0c00060700b1540001c00b00c50340191250100000c40c0005074042086020800c4003a03001001c4105036591000d80118a50001e846103d0050918102c22407502031802000c0c103032000340c007016040340e8a103507a02c00140704102e03030007141007101d0803c0f461001c0d00c0000c0d540154604840030642d0300e8207005001100101402040c040da104000700080484089207450400580c6003012411625006003256145a0804040d510000c3c1400d402003058172580054003480700000800703080304110071803e440314811a1550081403034072 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 578391160 1250 578389910 578389913
    0xd051501080a0c0201090b0112020a0b03070807050304020121050a0e0115140315041a0708060607060e070f0b1b070506121b07051e01061a0318010c051306030b010903 73
    0xa07000aa43c0d250b2510000a01440d69214a180c8941c01e034030040c0c0707148190352030109600f04a10b030903010380382d401481491030410890080c00084002c10040800101101007030031a0701c03aa035500704601d229544001d045003405004001046e0544510142616010a0240f4104180240e0922290211445030361f00d03d80700004800c41100e512456150140030060301d101104640d15034011801044611740c00c4482c610720902204010f03040b2420302c41c18400300300107696008212110182e0001c0301149a28148040615224140c0c020b214281000c00b804100c2c01c40c18000f0302030307985200419004401d458036060b910303076015014080c1c00100800c9100f1801d00500c40f8150019411051522224144901d04500341c00401d003c503059002900d10026252501080c20b0320b042c0c940000304000d5181140c0b41c5043d4051441c1c65108400100000d00300c45d00d04031000150001e000028055000705000090482e4071000c0041c407001c0d542403011500314424410303d001c502040e1103125000c0c0c01c5 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 578392410 1250 578391160 578391181
    0xf010915110c0405130b090a0b01050d060605041a090609090a0825060605010210050f18030f0d09120c0b06010503090309031204060905030303090a020906030f120d05150108 76
    0x1011030203244560360403640c090f1500c1c40b070644034015800342000c00d41c01c980b81640030f00e1405064003190340c0c41003d0010101d60491510ae0460704100c0300c0c0f03d401411071911001a045950003d940035181c02d009101c01c2402c803901203120300e001c81d06d9000c0c581e150420070542410980d12440d059016004901c00100050010704507080c0c0c503074144107500141c1c40701e220901c40000048407002c0c0c442e802080296010408080501d10004040c001c502d40048162a264402480f200445542c4034411600c52018411105240e00000c0c820f980c800c6194188805404a698105d07200c0040b1082c80001030700c0b68030f4007146541d002007070070211384541004460b641c2000c0e00c0035883d0b000412440c7c4003540c04005030740d40e160541c01d10649541c64403001410100184e801503000340c108008200c110400807509000040d41201c6048003521032402184c60100c80082c072882078800e01d0950010821418040d01010829000a210980e114108111403041e98602c107404510100c011520360800c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 578393660 1250 578392410 578392427
    0x501090b12090a080c1f0c120b010c080f09010801121a280c030e2e0b060711041a180c0c030f030105151e1303060e010203060f010915 59
    0x311404a030161441521906041d51001c441760700168010244412a4000000300e007000f0900301d0402c0100b09043ca5000d8034042c420011001d0403680c07800a01810380c0140403095005801600107911051a440c188095501a0300d0180c04a20b107503000044541c4c80780c00c4d0701403103540301400502096150800503440e0001505a005e20900a0101c02e800c0d0451050014880d0b003045011400c900d00c1d500180454490902d80c2800d0303040505c0c1240c44100c0c20b010400d080303199503282101c18001400c07003002000249110b65104a0002e40b800a000c44e030540340248000c100c0d8104580b4012100007001d074250400311a03084a030801c40500b0106603030807950b500c000842410362030f040d001000c503400c551003501e86070340d45240800140128100f041f5070b42c0500c0a0601d510746000d00781ca6054800d86808001641100380004050031480d160b6100758000b158085401e00459140e128024080e4008a8040c0e02440203010161020342c402c1c090001100c07040320079420800d00c0c00504440007907 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 578394910 1250 578393660 578393671
    0x611030c0711010905040f02090a0602390a030b07141305010e03010b031c08010b210405030403021005070201030e070608070c0f0f03090f0b0c03091002250f0501090b12 74
    0xb0304040005c031038556001d0340038848000310f00140d0f12922a0104142080c032500107000b15445540304040101e147ea0b80d42080a0004001058144840c0e001d41e2201e124007032825005800d0440000c104a040081540900510744802e1192145230006500e0380c0281d20007801004054001007200d5405440c2c4d0810320f000150000c41c98113158004246003408624025198070640c10128400035440480726000d00010880549002071150907050b0b400941c3d4000f04076101202e0105007003101c100101d800456020b006040001c40651018040703420402c401c0c1c2c0440d06212101c0c0310044c000c21072409680040d100c4400945540354115040340280d1012201c00b0f1601040c4000302e9185405800360a200c1e6548030b40c0142030a50482008141e540440c40c105024800d0b844c10302c03808030550380840000c0c1e5269000e00c1c26000124642107010117001008070310780348003550181120300c2c800c050f1150220200f40c040d640e071004584001c0c00d44500014004180074807900506a07034107568020 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 578396160 1250 578394910 578394917
    0x120c050702040501031121030307030b0a0f0609090e0a32010510090b0a1a072307030c050a08060411030a0210030902030c010f02060a05070909090309030611030c071101 74
    0x390080d40420125a0284c00c140c0d50805d41802940052400d20b5400e0040c41c6500b0984c80d103820290001680c071b00010700008241611061000c046072a01d07000d08008121021401696a907905030281501450340990701c2c40a050890b106164100010891002c5901c18104c400014032481c14003480c140040041d05181f100800ca2442803d0074001c50b409403542c41d00d071403001407400c01c94004441e869003c0314029884244200709002d560841144554814440c030b9681d1f101900d050400111540103c640610b030148660b9103681d8001040000e4070312032013a08d0025903c82080201c406000c1c400c010b6550300c50070001c3e00007841c210141c100140090225030405480c0c7d800204003600c03000c0300200182d03840b400141076160801c841c0c03080010078201110042c1d60745d80e009440e80030080c581180c4c152104046040301e44a520140c1c001d01e03c8040420407420740c2e2030b004051301400c0c801507034494102007004106a042e031048a001e0061542c01c6454189641e0303442e204200f0000c4507a060 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 578397410 1250 578396160 578396167
    0x5060307080102040b03010e07140412020303130909020316140112200a03050c09181812131e051005070813030221030307050d06031e03080708040201120c05 69
    0x5a0302400a00040c102d85d4a42da40c403581001c0c6242e8100000510420801290101c0e41640004e490b08581c00c2d10f004640368400c8407240c3c00480d00e50320811201441e40704182c040003401c00659800700b41e00e544210144d4030b6601c1803407280c0f00c61400e00c1c041e0400044035061420280d6000c3c100703d88100c20b40b0100403800e690080e1182a038400d404641c0b810349000054018003107035152040c4c1d9480204031695070308007001c29021814003e01401c0e8405d4a01102e40491840079411804001c520380e15030441d00408120100369040d0b80065110000360107807507002007844542c00c82d004c04988e0320703540000d00d050b00d85802c000025245800c1c4d001800010090035020070003500040c00c4280b101c1c00c0402a070352070761044c0710b1b00c01082407070b54198110304103070004000760110489811200c00d00d401c685a442c400341c00401066161300003007800904a6480c11003400012100301c00c18060b854502e00c0e50307034030102a5400c000445000b80003800c41820340300240d1680d0301501000300030b071424504 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 578398660 1250 578397410 578397419
    0xe120709090b0601120608030d0b0f030d020d030c1e080705070605010b091203090a0306050a0b1c02010206010f1406030711010c110f01060e01030b06042306040501060e031005060307 80
    0x101e501c1e085082d9180d00a410400649503000540d2400000c02010104030440c5060300160b128080c1e05c2010054946600303003140f5541d5000000c6250381c10007400d581f200c0801c404082c2d030b552406809600881d040511001201d40101200107040c003620f881d0a0007514804811500310000a0007103091080c244540d90229442c0d100f4039002e8000110160307524200d40003005541031591100c24072980c0b042040d6a2243c444444050407264095000320312601c580c22440c02904c4281c0780160040c1c01c03440c408580b20440096081c1640c003c4e02a10702503602c030440c80c0c4058109000b00c0c81010481d0341d20380d4450074040001c50b8851036524001e0501d000402140382550b91036903040c0c0014580c800c464400003002d00c101200c040c04400200005850072862071814a01444068407003840d00d00000d40c07649a5800c10780e007021100802030260301c410780d0144a43c07041695100e008916020000c50540c0c000c4490100c076400041c020240f00c00182c0d09200a0480201f00c04c5d054000c5480004 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 578399910 1250 578398660 578398679
    0x1501182d0303020c0f060406020d030b1224011410052d0a020609010501050d03030b12012408070506070b070306150309031106010f03030503071b060b10030c0e1207 72
    0x300514403d50240101d07491a204021a5003400803a0b144183c2c0c007040108109600013032190200d400b01d00300407682c00c440d00001000900c0940d030140160055008030207070400540d80f00700f0703142e42d241c181c424507980358440846904010070f0700a40007100544c004e411503000741c0240080e042c1400011086802c020861f201403022040300700040100410802c0c190382d01404616805200403000b001690315013000507000030382440010701410390302d10540d28103841c0c81526021007000080288224420501b081c005151075403903200700d164003100d01146014011480f0030486000404407418009a5164022549000740150040c0740d520140041d000d0801c0a91080400d0b1076200050f120040707041c007601440c01c42d80c80b010302e0340240c40103010780e0f5500c01c620701c2566050320340070ba1a0b81d031300c03102610041c01e19070ba110081c001c40900e1401f0030100c0d800c10121072a0070364540c0300004c0c80c0d50055080d26207803946070022403d524880750050611070807070714600e480d0804803603e1583d122183e4 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 578401160 1250 578399910 578399999
    0x71b0b0f07050f0a0b0105131506080601020d0807090302090c1204050609010c031122090f06090606020102070b1f09230601021204270e06150118 64
    0x368019034000c201d141c00d00200780306001030a410003028203581c1800781e41d500c00341c903414090a845591061440030004925034403540300030740401980d203021501d0f450054980f0000b202c0290051240b1f00c5030071802846046803034064a665218404040d0540d401c11481c127030000d0800c842c50500f44188030080840c80c008138000c0340100b001e000d81e4280180d045082d45d9010302c60009150509908082a841100c110356420042104000c0002064443c000440000e0380c8007402d42410302840d446180499403141c012540d00c10002c02030f00e544c4100c2039090380500200070384031190240000700d04c091400e01103502c600620b628080c0b01d54407900c006040340d180c1c07200c01d081c1e14030a595070301900540d02005500071a0900017814800b03030340612030445201c0c40c020903a50344848030118041455409a1580190794100b090140a02c06541b040e0b03103200c04c0300c1380d01024000c901c41151a5000701010001ca43c440f045682c41d40c1d081c4007101c249c2075000c0c81c0280100412150910505c404000301 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 578402410 1250 578401160 578401177
    0x905030d06030620090f0103090209070e0103140702030a12060504140603150115050a0c140d1d0a0e102c09011802011b0512090102010509010e03071b0b 67
    0x1070014158105801111045601d448000c0040f80f050308229011100b900e203684030446495110220300c800403800b03810008802500b01d000c0b44140300c40c41da04000061090942030764200078103c2180c03a00c40c0259000c2d80c0002c0503030010030035820200c0c0b080000703000840c1044400316400f030b038031030105044030100d40481030011030140500c2185d14041c400400200d0110008402d030b54146803161502070000da49a10500c02d002a0001803240605072004c0740d04d401c00013404041c081d050b40346440b0181030000d6000118440c80216040280c0003003502205400361012042c503003407011341003403108054119450b941c00a90001a0300c3d240401d6060000c20b050018a0070204480d2020385100000e041110b05905280302a0b0b032150300e0900040f202da80920780b141900c0743c0102d004a0b000e02400d405030050080200481c10101d03c0001400200002e034000c008642c1d0300c1a0b198221400e1341211001c6400c01c1000d034012405034800000114605014080c00c01d5072907140402c1c60b03022400 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 578403660 1250 578402410 578402437
    0xc1814010f14120d1803050613022d040905030c06090307200f1302070b2511150601110a0c05090106031a010809030f04080703021011030d0f090503 65
    0x18140440d0031000495600da0304182e400c0100c1c40060769250b611641e030160402e007001510a00d0300c1400c686075411200554020042d00c4050506271404054010201e0050380107007901e41580d4200c40540c80006041c01141d6048803010344c0e103204000240c00c0c4034005442d140700600c5802007800e01401a00d00031034203e40110707030f2204186401041c8841003140d00101c55032140003600591070b2418500702c56a011503c40d51036051114803a8000c0c0600d02006e003100c1002003c009042040040c0311102c0900403101100004030440c08980d825106c6403041b1482d00309072410415459902c5005d508048141440d61901d0411003800b80340c44d00c1454141c0b0351014800e403c100c00e0402d003040074094030142c601844040d000b40700c10000c5510410800d81084260b00000f48040d0041c030590340507441c4902d210350b0312030341c0d500e22a40d00c06030380c04141e100d000c4106d94450f65500070080d042c0303040c0e1003501850411100702d81d11401881c1065030308003402c0d1101c1181000070380600013031218000010 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 578404910 1250 578403660 578403689
    0xc09240b04150216030201120906020d0605040e0106050d12031116030801050a031a0c090a08030712030b090a090f0204021b0d1103220807061d0109030c181401 70
    0x1003425078250000b003820301950041000b0711602810318075001d00b604d40a00f00354540c5809002c400c4c00070860080b016100901c0403c8150ba581002d4004804556040310f09005441c7d17031700c40c81822038040340304940e0b0009002d003030800020183e03801d4660088840c1400070f80002214042485a8011203005914801c0040d45c1c03010950051162400362034240c1d523480c566815503681d80103d140c044109100440b00600181e0305d00d0281085501c190341c0903045201a03581c40c59119501d40001c10102c614091000e02614918400c2c80f07603008003030006000e802d0680720095a000184110301c0f05440b0203071a11101320140c0c1b2540020011004111500003280c1010240541003002d0310782d151082000b00400031040c1d240000030307941207040c9080114a2600ca00090800c203941d654490f510500642000085190f0054602e0b080d6055100c4031003007000460004481d80317180760200804c4500828070500500e0b403403030075122014401400c00244040c60340280f03803c03032409034019000364201d807 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 578406160 1250 578404910 578404919
    0xb062116082a2407410c1c020f0405070519020a050d0f1707140901200c0910080d050a050903010f0b0a0902040e0a090c030c0902040e0f040c09240b04 66
    0x40350041410b1462013401495000c91100c80f44201084005d50702c3d2001c0d040d850352007400070a0164141580000f8401140c08000d0141d06a80d180c0303e0000341d21801e0044010100f0342494000d040c07050300d0599131a4903000207000303401d4550440d0305507502144100c0310100009002040600c0448189483d104ca240d050302400410900b02405000500310141e01400403250700520901d00d400301e1200303116200c0d2a003600495078841032020402c201e070740c03050b44c800d441c46021a01c030503055400d076080740d50b56490450751005001207103d03000f5a03a1104c00309000f454803800203080510348903d0310300c1c80d08a900d00040d0070348000c1e03151011555500c805800032843c0c98058400180307015203040d410a0300e00400029100002003001000c1912180d54004002800d0b8030040a15031281d48000c0c2c0c0360f01c41080328000c0d005409030b04800d40201000ca4503803440d02850790701c21948079010003001418201c1e41d03c00b42004030001440032803401100e00145840d80c103840040c0c40d03042c044c10744503481c0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 578407410 1250 578406160 578406173
    0x20118030512130b090d0b1509010f03060b011d010f05090607050c2b0f0302031c1b0309050d2f010504150204080a0b062116082a2407 59
    0x4640c080c845580040107000040d807240394046d0301c0710360010300341d40695550000d80c501806800c4d0690707a00c059000000700d014a40700301ca440c256070044000b040700f09203a03001560380c5010051100702652209103000344642c030881140303800d1100c6103841c0d03003008d20b01d4002c120300c0d4000a904890a401041c40e5521301e0070a00c042c0c0000c191842000018951129281144103000d07001c0940b2052452005005160080084443c1d40504200740203903501c08030440c0b4018421525a90540c00341c0d5580701402e50b11901514004541080290030300f810114010340e0300412407900c14000720711401c5507800a6100002d900340102c0080700106482c64907250440c44148030011243d0b4042c03051005020f6000d0008120302c5840d8404410102a11000d001502000d0742c5500c000b1030032030346290b4601140e40490f0503160b0749244200070343c40c03c0c0c40701e8509846655203160104010b5030300c4180041880460582e84480001502c041390f0440300841907640742e0f041e40b081d0304a400c0000f07041c4042052 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 578408660 1250 578407410 578407447
    0x5060408101401060509040e07030f0f05010b1009140a0312020c0310090b180109081918060e130209030a030903021503040b0a0902030f0115091104080307020118030512 74
    0x9582c14001466040910241260240e8054603000d107689a10f00010764008008075009160058011a11003005140c0107c80d042c0440040381d01d5402c00d149a4260b0420f0513003da0003030b0003629545559818520000c000c04128810710354002090070707001000c20700c0410702d24244c025a5000d4002c10550342c05140c50400b818401d421311500d803101010200f94401044c41d0082d5100303001c0140c03250205c03030550140140c0c20000d0708100300090324540f414440f0041c6100f0035110b45881c80010142813441450040340d100311804507082ca08000000c4c9080080e483c00101d4044005050001050101e0320b072200100c0110007081d9041000e000707620b40714540c071040c4281e054071149907280a85d10364800300d202404c09081c0a8648031034004540c0e09001c81507143c50340400030003007640480d01c1400781c114142b047c011550310780106007180c40c40d400304940666640d54001c0d80740c20055030044a90b2a1224004810706540304000b00025406100304664020140007403a02ca4486403012500c224 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 578409910 1250 578408660 578408681
    0x20a031107050c0907050d0501080a0308060102010203101e0807090b041b020a060507110303070801170304121b170a0204140403020c1203090402070f060b0405061f090506040810 78
    0x5028004031000400004003e0040881600d48560a07207a40320b060ba0b403805400742c41080301e0304040c004114500f0015844c05918005c1d03850f000c80c1d8540f0b00042e0308174401038a101c0e1101c1c0580d48144040a020003034040441c100040d41d808995803200100d061194070b4116190031616440309065914281c0a910020103c240d144a445079224401075642c00704080010301c0540c60b54001031486009038040441c02c4039030780c10340e0341c0ca01e4200c200600550003406520824030b04055031068250000007a03805559841118811000c0c5540310107190b0402246850001c1d000b06001141c0d4150442000103034001d00310007000803410764410002030310040300c0301c610071103200010040401d0380000d01e007090701741c10349002c00d4404900f22614118826060050707001030001400b0410007072940d0380c405100d40a010204000601d00d01004240c41c810340b80141d20152648040444900b00300f03075001507140d00c2c2400540c0303554030008114140c119501900a5070009000501801c0c4607004610145 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 578411160 1250 578409910 578409941
    0x3050c013e0a120b2101060b03010f0b030c0c01090f0c081c0f03090503160b1524161a0907080d050f09090c070c0b0a05030402040504060b13020a03 65
    0x10031491401d0105401009a000d0800034010b01c0c1c02601210b60748400d00300b03200a001d00180d0f803030041040f1411419482400000d600c0e110001803006100003d0700d060b04c0a800b03510358568507001003144d00f50006418030710800810081440440001d11843c091107101c0c3c0d1042c0318203a01d40c24102c415143c03036480f0f65002d0700240344004103c42001210508140c035410008540050800c00718018070f0b400c88000c0452000060038160091015a100b910611401c4082030715a60303101d075881003c80c1c034204a0b42002016000a40d4440e2111154100c0e07200700c600c40e07042c0741003a000d200d01544d10301d0054803034030786070944100c80400014015602110305030003403c0491906940f03a5464000c1b29a20003049804038001b15204681d0040341c96030301c2c005201003114244031000d07094590001100b240c0d0020034a0001403d0360f416400d4580c030703100eaa00c0710f904543d5660240320280100800c21940c840c0e80702040c841c5c96807422401d49081103c16401a01d4070135a03a80541168400e1130140c000 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 578412410 1250 578411160 578411261
    0xf0c0206090307231905010f0c0912120c060609061403010509060606030a1409071707030b0106081b0d0c080601030b1c08041a0c01050109090b06040903050c01 70
    0x13042c8042442c004245000000c600c420107400b49581c1080c0500350321124007001d501001040c020150010703074550718040010444034210310340c2613400402c11710a001c00c820700c4001840204000035540107003040241041c0140400f584c0e6004100c034403940004031010742e1504244580c2229100f140e203000350580c020411401c200c0c0f02651354040c02400c85108560010001d04981c865410154a548240c04240000e00303004031102d440c3d0006008900741c842c0b4001c8282003030100050517004a9410041440059091800445500000070301c45c0481c1c42d0180b84c00c20784d601d1504024010950030100016102a5070080144034100c0640170504060500340030486a9a80b8080c103000303251030031080b040d01541e81c40d25020600840e444883d0510342c1c03408120303c02c041f420092201c558004000c01c00b42c4e80351500310701220404617000e03144079030b02c00006a80742060350109043c0e0b800b03410018108170ba8007141c40d007922a98400000e5140f910514120300c1c1c900003800000e242031140c1c0b079011 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 578413660 1250 578412410 578412413
    0x4080d060b120a181a150301090302211e0307020a020d12080a0b1e03070e040309030510020f0d020a09090218041109181b04030c17060105030705041a040f0c0206090307 74
    0x2103e18101740300d0429131000002c00c4514005581c07255149401034004d0105141d40d082c040c0d140e03801c1c8220080a00340041c842c12005210380110364600b105001503400c088842e01580b201030300020030601c01d52045480c1300380540e44801803c0b01041c402e94280e900820f003c203009250710000b419600610b420408600015500c0a00ba0821003034406245003c0384600d00010340342600c01d03406610418400300031300051550010381c41d42507a00a008984900c04070080d00812481143d03010b201c6848144500301260403140c006000c09042881c0c8944117a440e0001603089030301c55071109010111a1058a946040c24050406507080041c0c00d00c3c1050310003c003003080700010240d2a1815002140052000d11485d080000d81d0b203070600c0220b032160b480b46881c641240d914001e101d1a40f622416800c05c8140000d4054180c0c3c17000b90141240724034140c203000c09000100d581c840341464202181d84942c0f0365200e81864540c01200100d00060b20810190410001400141264104001410 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 578414910 1250 578413660 578413673
    0x925081006140112061a041e0f05060c01140a0507140304020604050d140303040f030905030c0f01050c1203100603150e0c07060603060203040f02040501170604080d060b120a18 77
    0x307000040c2802c2130b9807142c00380040a0000c21068206044109640d17080764109050b02c030180050798102003103241c0c008134a11540d070360707200306114065141506170070074046030515101414819480300d00104544040f0400900442400c0b2100d40644d070744c5d0020804d03810780c40612541e20440c1c469600c1d1440c1065008200f0910840c000d690090b170082100800700710101c5c1e1100a1621500c0980e5202e00302860310300340440ac441e00c2540014628200403070360b46008208801c1c0854018040319481d4a41401911245c00c502c0060040b400765014240d01c0c071100c90001c1d0710450500410001d040e0500a0190032501c1c40c036a8041c03000c01c001824000907040200b02070304062a01210764580201d41341000191840d0b03000109910b0002c02408104016072540e60800e44c800c44050015a0321400442034045004a000000354020030214000c21043c20003881203000c1100b002c01c00b0b50300c4070030a84503035000b0348181c02d40b008240300300000d446640c0304501e41c008400300490341d207003041c0c0c5451 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 578416160 1250 578414910 578414939
    0x305040314122d13030909021c09060e07030515011d070309241d01110d020d060b040602070609061d040509070e010803040e090c0d03080925081006 65
    0x310001400b00320a40764890143c110003076400100b510358000c0c0d1410550214840300e500310218045820807038003040113400c0d402070752103100c55000d0500d1510383e41c901410242c04020020390340c2c60381d10b0343c01d698801300500c42ca2010394018001401d40d02200107a02420080507444410403100c000d00c94070520701c4445901da0810700364940400c0c0798000d0706000101001d0722950ba8525040e0004540c03946e203194222034500b00d05031b03e661400c1d80755400c4075030903150707656210741d0102c2c4200040601d80c1941c2c1d000d00b04040e130305040041e0301c54031840200a0740c0d100341c11001c007690218004201059200c0c2d041c0d40a803542e4074098100e02c030710000e500f500c03110b01040140320f80c0c1c441001900c84c96042216400500b2198140e908550392803484036100c0e481400340e11a211380030b0000495502d00091108181c0a02030810108002c003a02c0440714403070090709a002d04d0141d1380344111519641785c036090701010b4012000902c0c030f182803c0103141c0902e05101a12180c2001020007131101c2c092002e = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 578417266 1106 578416160 578416171
    0xd0f091e020306011a040312111006050604050d1e1506050123070201090b0307080a06080c0d1106090d08070c0f150f05090d03030504031412 62
    0x1000c02860510406074042d4008801000003e43c072502c1d010724040c20075030450a01c2d45903540c0080113005402d039000010291340080c80c0c02d0b00144500841c40401c2d85040005510b0b007404103809008600c9100d1181028010703800601807240114200c0504060040030b62001074500710ba000340d82e22401c4801c8614110000c075055005082003511141100c41101e8041550fa681c031001d03902c0407004138104480b40a0006610340b011011318011406611840c07140d1418070060790803207c2a61141d400c07035008120000194a605104100b25a044104400d000c000e20700810078901c1007001303c9801041030407042c0c00780007014020300042ca2003145044d0005556860040d2051450f00500c1c00c5005060300000c0014007034000072040c00000d0820780e0500948000149060200d2401070380442e840e0030802c003c0503844124500c0b01c0001c00c2059045c920095041a2030b500b00070132 = true := by decide +kernel

theorem cover : BRFrame.Cov 578237410 578417266 := by
  have h0 := BRFrame.cov_init 578237410
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578237410 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578237410 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578237410 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578237410 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578237410 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578237410 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578237410 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578237410 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578237410 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578237410 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578237410 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578237410 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578237410 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578237410 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578237410 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578237410 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578237410 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578237410 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578237410 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578237410 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578237410 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578237410 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578237410 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578237410 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578237410 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578237410 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578237410 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578237410 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578237410 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578237410 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578237410 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578237410 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578237410 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578237410 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578237410 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578237410 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578237410 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578237410 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578237410 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578237410 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578237410 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578237410 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578237410 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578237410 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578237410 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578237410 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578237410 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578237410 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578237410 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578237410 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578237410 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578237410 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578237410 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578237410 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578237410 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578237410 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578237410 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578237410 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578237410 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578237410 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578237410 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578237410 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578237410 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578237410 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578237410 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578237410 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578237410 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578237410 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578237410 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578237410 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578237410 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578237410 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578237410 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578237410 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578237410 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578237410 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578237410 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578237410 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578237410 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578237410 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578237410 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578237410 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578237410 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578237410 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578237410 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578237410 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578237410 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578237410 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578237410 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578237410 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578237410 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578237410 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578237410 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578237410 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578237410 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578237410 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578237410 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578237410 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578237410 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578237410 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578237410 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578237410 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578237410 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578237410 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578237410 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578237410 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578237410 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578237410 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578237410 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578237410 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578237410 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578237410 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578237410 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578237410 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578237410 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578237410 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578237410 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578237410 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578237410 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578237410 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578237410 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578237410 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578237410 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578237410 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578237410 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578237410 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578237410 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578237410 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578237410 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578237410 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578237410 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578237410 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578237410 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578237410 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578237410 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578237410 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578237410 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578237410 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578237410 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578237410 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578237410 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578237410 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578237410 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578237410 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 578237410 ≤ n) (h2 : n < 578417266) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
