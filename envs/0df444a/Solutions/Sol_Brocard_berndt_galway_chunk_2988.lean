-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2988
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:19:59.563808+00:00
-- url     : https://prove2.me/submissions/ffbb9871-1836-4f25-93d0-5bea93b235e0

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 537230215 ≤ n < 537410071 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 537231465 1250 537230215 537230227
    0x100902090606070305030a020a03020c0d02010c110c0603012c091f02090319080d09030e180402032505060a21050603030a0c020609040213240f0c0f1205 67
    0x40440382030000c1880d0300540c0c0810000d004a034004090380d5001c10294805652203078504c900310040c1c028020588414451142241201601074000d4806041d441c2d071400c1510150303642082d661111407070602e0f00000b04000504c11300d069039140521001e4910f207044044500303075003440c0c1c003807031b003141c0c0e607036064002c582c0c0c14880102150700360541c03180d6644258241014100025101c59171038494010715410495190f0800001100351801d070185c400003001420401d042c042c251614684142d4403030642c0f950080c80081d0111485400390760050010064046180140c190407004410070989006d100b00d07000519650302e800410307008a0075039a004803510200380c001e503440031240134012501d080c242080440d450000c1994010050b42c500141c6103e902e0021400a00c101d0400e02c0e00140001143e09020b90ac01611303030125500c02040004003104243c07d1003a48200b440035000040c00c0c24100c4c00050710412100e504c9500402090700c0d01196170713540568041c211601900405c5011800c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 537232715 1250 537231465 537231469
    0x80f07030f020c03150114040f020a050a09081c0518041d10060602030a18050409050c0315071704240501050a080a0b0a0519020c0106030c05190b0a02030705100902 72
    0xc3e036288040158018040360801048248051205001e0080c0825025007040b0369551150006041c4200e41c040840d603410291234010311580c412517024010606810000400010008500291500c401d1101c49100039012007100c40e58000b0140305200a03c40b0221002e681e1144200c4624190158250040710088500141045801440204150710b007160070403040c0c0d0040125400b01c4202d00c0c180003038035141255a44503410640019030000d00c0c00c1e184004000c0c000031420740c400003c80480b8001c4003d041c94070f04144003213404000056491003400c05188042001940003885060b11011080c0c01d0b802240c0c0c6001c034482e2000d00300d61120010031090030301540e814003422205003e80000d41554940c507460250142c04012015511000503080c0c1c140c04210101082824000359034858400280074068a11030000751207481000b40c1c00540d80c40c0115420950040f660021405103280c03205e0080c081c0c0203581c9290540c0400c1080100141c0c0500402003030004200c00002c0412403401 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 537233965 1250 537232715 537232723
    0x20d020d050a05042103020c010e07060809060c070f03050906030703060e010518040209070e0306040c030606050406120303090501180f050706030c1d010c0c06050909090d1704080f07030f02 83
    0x4808a100743c5020140008251110b8988100e000c020111400e216503010045000344105d0381110080c3d403a10312502d400c0c0c400410b68408490241d954201c03036072140244a078840c0001d480c01940c141d07080142e1000158400220209940242021820480f41c440401da040d4000c4405c280000d0365003805004800e0002c0303203a0302410044c2ca0f503003034014060202880120000d84064415080600060300640c4515102e0681e041c1c0501a110107040c540750a00c00c02c03a040c001102c40c90b0900c20040b8a0741410300c500030071694101611900741199072402ea0090403411410f49165489800c0381d08011103062000f1102c905c41d0050384040c0446042c003e08058481d0804406c060402c10030013a107aa001100b06c501c951b00e8802418804420001a5000d518020006180004140001401c5604180a406985020303200407655960b200f498944545429980c00003007030f074200d5030708010101480d071240c1c401d00c00c0d90303c41d203842480052140f540c0c20050b01140051603c540c00d840c803581c140 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 537235215 1250 537233965 537233971
    0x30207030906020105090d0804080705030a1d040b063915090303280e060408030702160b1909030204020f04060f092403020732070806060105090a09020d020d05 70
    0x80f008100b02e0500c940349503144c180210181040000a201150034010120200d40090b50301400702c0740d91782d810100140a840020f11103003d401206c0e00501c5041c1070a005200e00d84100230001803504004020040010075144200e007484a80444148014044140b2030102480904000c00000481191000d8100402002c3d01c29070b8005106018450030008200c0c013010b000310101d11201c10400c607041009208032503d0b801517200b0f6800784801e00001100035800b40003243e084c0d4120758052500d05541144074428900d81800802a58000c40005840381025075070350b1806d07080180c1d40740c000a05036080f54002e1100c10400080070400150050400c0d94140420304100c09942d207004811141e40004111440d0501d1a1003e1044c056210350304070368651380c1c808062900003410002c00030a5500080a0500c0a07070b1b2071180000c1032100003000c000319101c15000b01100c0e03407074000464983d0800b000c00390300001100c8000c01d45e1503e5001416120745ca4041c0142c07070782001c6055600380c400c05 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 537236465 1250 537235215 537235217
    0x1b031905152404030f031e0503060f1e0112111321032307021207050102120c061308070221010b0f0f010c0c170309040b1f1419030207030906 62
    0x1403101000c2502c82d5003541c1c203c0c2d0300030240c40c160f003149003000d880c04005a240d00c0a6003420403036112501e034001d009103018000503500e21405107040380500924800241061076940c5030441c0c543d440350304c80c110840c03c0643c084000300b1041400701c9004800c1d00420380340300192101180902000520620b40c00500b01c5a15220000c030344540c80c040c25a45040520084010031401e8101003441100200e0f1381c005d07400f0300030b0030029400341e000301e495805a004071070050242d0903150f180340f40c2c58003e6840c0385070000003400c66506c8442c0070001d0003400d50002c41c1d0410f810f0040d0400340e41c0d0317451180c0140400c1c4030b074208468070b20380c4610b0031100343e0001c0e03e100350070041d062070b4140c4a82e10f900c401d40e8400e00303000364842e01c43d0800061004980e4454000305407100c0c1e50486c0340e4400f10245c01c0b40c04080c1d0301440104146e40400000320000f01800001a03902509035800a100e80442c5038440d000310a044e03d0111480b03007156000201c194404042074001600504041d84a02200014461 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 537237715 1250 537236465 537236509
    0x3010506010f0f03020309120f070b0c1305040207050f1603050706080f0703050a1b1101050f01080604030c080c0625091a09041b030b0112051b03190515 67
    0x41060b000e00801201c0340000d0425a0100c002860114104a242106080c0d01c082544541d98003200d001d29500a900484090302458013060044040c1015030700ca0390301da01740c00b2048605000501000b508038130300030740d80c0b482061041409c640b401d02018000341421892010014103509100707152004680c4114200903000f01041540c251413050135410400da81707004185a1520600c0001800300c1d03210b4100d00c2600f1441002045030820000301c1c440c9444e10007405035660304886120030309401d210f014020f40180700054002441075403082000c40c0708040981c104604040000d00d807440c2240c8030306025a01080061031180007909051240c94a0302e40b0307081150910300644010118000415180070011490043d250f5172034102001c80384008801c036081b00c00d480c4005014000e05031410f400303c0c444448000302c2608030301405106846100c4640c1c0d000b94108d40c0301500390300c010300c140041010301c2e10004500301d0700e020300750203841010341a00d003132072012042102c0f04007083c807081c0340180 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 537238965 1250 537237715 537237737
    0x140a0f06020c011b0c090c111603030f02070308162f0915040203150901060f0f050904180f02040b0406080c0d02191205010f110d2412020301050601 65
    0x9400a6403001948003881c1c00307541c18034240d008041d04002004000c000c4400c0d03417404502c4109550001c50104560340c0e46035152050b808030a078440008800b8491090390a01d82400880c0c040c0000700030f180482d1048404c00360341ca8845021542000c40c0010344822408242c0007405045001c940704d1245061007000380d90f186000d110392000707890140318000e0090314000f0f45d030100071a800084000f00603000b595a03181c0303401c111a10324101088130780b02d07440e000300115807e4130480700e00900503801d403a10b0040103408a01500c03142c01902ca42036100b9141d07040324103015096426181c5045c0304401190b00c0002074170402090b9032046500314021413610300708000189001404007103c1d1004c0d02c1c26a503a20160004c1840185104000b181080807900c00003100281e103001d124041c5e016400070000004a0400a001e40d0280010745400c50b405008200d60224030f6482a000001201c8000d0a4078130718038200001030072107521008000892201c0720044d8142806a80d6010900340fa04428083e = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 537240215 1250 537238965 537238967
    0x506060d0e0f011503050105010602120d020f0d020703030203041a0919051204030c08071514090316061d04051b0a0c05070f03151509110904020301140a0f06 69
    0x4014400c0090485803100d400e10400c4105019008141480c1c030001d0280c90a1940c00548450341031204840c03030341c41d10000103151381c40450844840c000482e00c00c1d140c40000c0f44c1d1940607401c084aa0303444054100100708200760284001c01038a486500e0268591800d0b0a0000740d6107100000d83c54095074110820001c200d001c01d41c41e4000e030b102100c0d00c19201d6517081c01450246500300141c502e4000140c003100b44a15204076108442d0b440342210717421900e40320403002100c0c5c0300f420f401c00300b00180e031842512040803024003201c1e0b0000e8100c50380c050301c240041040303c00341c7d4004400b040c2d80441c10141840c0c4841c0e00010007406a400b030040e800d05414284409048a049084000c00440c2c080e020b81e11030114080d41c150001d080710503140d250a0380c0c280012541c030040f02c5403c0e400c2d020200d600c3d203a001d5101281d00100d84214221315024144001d000140c021a02000d41046005419a1140f003d1800392603030040b46a030010100e4148000c1d2686904a80b043d803044100402c141 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 537241465 1250 537240215 537240217
    0x90507110f0309060a021608030712030c050a350a240504090201050706320601080414031b030a0e0109080c0d1106030a0e0d0e030715020309060301060207030213050606 74
    0x680015904d079a076820010908905007680210000714030207030a0000955294004050080607000742400c8940366031705502501150026144e010104006010395036001d401490500100001e580c1c0c01d40200c4150b070307400d2940c1c9840310701804481140c0702c02d03c1480801c40c072503010000082d1048448800c407510701898807010301d1081c4d0f4440c41d1580f14103011644140141e5512580c42038050204603194848208104000700c0240c4040d49403500068580010700c20b818090a01030716200c600d5121500e500040c003408580007070a501c410405c1c0c07080c204001d008100300441c0d02010315103844403c2801441e2605680e1054104103a002c0300b8460794401185205000c1403c403000c050b034001510344080d2122400c0030059205001004011800c450b5400c0508c04e0424582522403030314583c64207580e503184a811041e05540700e000280460540e402c490307201004240112400c000b21000052400d030301c240c200e54010f8004003c10411401d2075120b0100c0c03010000300a104500d8404041849 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 537242715 1250 537241465 537241477
    0x1302030f152214070b070b0702010f060e19110d051909210e040c0806040b10091e050a0803120f0c0702131509090b09010917130f090507110f03 63
    0x420388a0f0301c0450b4040d402005140014520200345030b480300501e0400c04a01c850440300070015500301401c0100c107803614892101500c0a80050003885e4407803a850401d80100d512104480300d1340d0b80d00c10400c204966000e00f020b01d15800010442e807408071810b018155600241c0c2184504150106c80001e81803044140280310142204094402c0503508980c2c0c0ca4034010b4440e0003501c1d06500c01400c0da4805021803151006590a000461021090000c25804805c1010001d01d1002082c46004c0782180400d010a51540103608241e440b0303c00a91102e502d540074214550000405100c04c0e0040446c1c0c541c04103109d404071104e4901201e03180788610072194001c0c86a1520740305040b40344010ba10905250090300305640707074039403103409240003041200c0041d1031000040c00040c03144041401091451035020560712040507030350440c91141c0e0000101082e17001d9001c0e00c00300c2c080000c04003420080400c07820100721801d0510019080700122400c81c0400d410200400d0100350000048541c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 537243965 1250 537242715 537242723
    0x303120209091f0b280f080118020702150405030607020f1903111c030e0606180c0f191704020a03080d0b1f080108030304030e091302030f1522 63
    0x218619030390703e80c00c0030418150041d90852101003001c0e5010000503002410080c0f4400d20803450089501c000d480d070301c02640c41007000810040c01480140120b40c4954100041031034090300300a020350000b480d00c140c0007050401802c02040400c0b00e07241c00c00c52160026505d00250010b000c2071907840b616110729244829004414140580400d4031a59002001020040c00d80305109851140710000c21446c44007440001d0801c00c241030810800300302c2d42d00600c8020100c000d01c82d071400808052203402005801c1000c0c041c4080700d02d803203065004202d91b1030411a2408090b83d80b00019001004040e102c40340406440c04000060320355940b09010740740c0100010303444900d02100e11000d401c3d8001e446810080040441d502504100309072104181c140c0c440c64400d0703884215240c3d40b0b01085601600040030f50b4030500040c00c5c21000f488c0c00c081c40d80011007a84410383c0200c2d2524242ca10820619404103540c003240600700f040c440d03040080030440c04210799104540b05440300310310708060 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 537245215 1250 537243965 537243991
    0x1060b031b210a0501051f1e051306020a020a0b0c150621061b03220204060f1d01060f200705030607090305010e0309060a0e0f040f06030312020909 65
    0xb00255401c540c03480304003094418194041c0341c52085071010740310078498031b4044d04d40f00c40007403519500c1034101505c10354543c0d20401c1040c0000171043c10000c840716414103001040105004d40582c500c0f0b102c3c05072070036800410200b5a18418408001945e603c0102d054009020b02c1070520070204004200030880e01118100341c481c100050010110403000207222003800522041c40640855441d20a1144c01191140c0010910684419110441d1140f60b1341540502c1040c00511800d108000d5500144c0002840d1341c59591046281c201600030004d001c0c982c841000e010754400911901426051600002c800c6481c1d1015080030560314040c11800468024a0200181007101a00401d0300904449581c00d002e4005405c080d0180025561542045456002000004120b1751036401c0613004c0c0f4a4801d8040c0111500f03084414171690020001e80741036150758840c000c4402421045200284080c03540c9000380102940000b0060f949005100c2d041159850440295010410380085 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 537246465 1250 537245215 537245227
    0xf02060a1406010c110a060f081303020a1b031211010f06030b071b1205090307152019060e0c0f0a05040506180705030106080106050910050a090803040905040501060b031b 75
    0x30518545c0d01110140c1c1100c800c18001034500c0d840300c1c03045002c01058a82c00321a0f10b0f01614882501011070024001d070340010040000580c050300011000403101e88403140355900d03595500c3c00901d500340040001608040c1178200302e0000c0c07240e401001000041045800e240d076440680c40380005010f80c00b8444002000d240202c40202c24654060f4002d01d135035610540d4000241180e0040e8500390b009100303603070022170284060004840c031600c07076803542000f0304045440c071031540300340400c40030b02ea0044d03484001c140403c1c0c0b1001c070306940c03081001007000207102c00c000d89403068010000d44600c0f03042c0028015500e4045401c2c043d9802650045101e80d00c0c00f0100744075480d003146040d0030000d4841001015540400554181d9400360350b20041070b680c548084815000e0a003260f80d201740589070120010740290010204414035007000e80f4542c1e03560001904540081c0d02000d0003035120010082001030a109950252001d01e40003400d42c1000c80251030801d9084103000c48001c400511 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 537247715 1250 537246465 537246473
    0x2090105040e130b0603030c0613020d02090f040201020609030f0301090b010216031a06011103090405180706121103090703060b01030914030a081b1608070507060f02060a1406010c 79
    0x1260090b0245018012190070f02d0310743e0088204984500fa41c83c5a8244086000d601d4040704440301d2890140c028907a94071115242003001441c0c2a080740e00000c0103102a00507101d114480e0301c02d90140309807684030714050001a082040081c03d01215410410074403c6884034441520706403030800e18002101040e400040c1c1c5410240c51514400455020300082040f070160001c0e250351b040383c1d80700c2c10291105c1006680c01c00b404021041a070700f06102c0303030925043c02e81c0030b150b01544140501d1007100403401c000307080020b190803000c009990310b80c407108041c500d400b880b203001d004460181e10310718142625688898a070702004100c0383d200c0c6441555a84a0b41002800c65008442030b000c222140000c0c550341d51000d80b01d140400d264900280d120308000c3d03000c1c40006e243c0a034051600101050b00c0301c481e41c09031400c8070691010310184000c14800c11034280541a02d0702c0d2655003120b01080030349000c01c001e02549565041c44c81c0080c00c410906002c0760055420300b05007494194a00e0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 537248965 1250 537247715 537247717
    0x30c020d0c060f1b030f05220f0602190e030606090708151e10030b1f050c0303040b010f0e01050d331b11060f0414010e0a0327060302090105 62
    0x494211880c2407000b10207a4281070100c1241c09105501d08004809440c00c1c01e03416100211542001c6611400480c5e13a0b582c03031900000c0c8d03054420220790300d450f0380e81d03940c2200300e030007504074070290400300e000703a950164002100014142c0100c0c014000c5107060390000c3d0440c000240f8040801080f10045000036a8841ea60206d400c401445502d0f580c0110300f00901700142501c1c100d00c104c2580100c0b0640e02c0c000d124588030b00c04003500e080324a1180b16151110b010a00c4440003c00c14200400c8001c9901030021f18002c502c20026070740d841d40f5050b4100764405079508580150f41192004004907a66000790200881d402500d010407668000211504804c180c640408103844596803030754084410b138407940d260040f4201c2100c104102e028200ca1954004200025951042c00810140340090000c942e00910852280300c07068540904107094802007030038004154000c203503090400d50000c000c40800c00008404030304c4d00c0d00c02280b190b1407801c1481103a040c50742c00035640b2002c0c1d00c114 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 537250215 1250 537248965 537248981
    0x30207030c0f0b100e0708010303110f01090b060f06030106020a02090a240312020a05120f040b040902030f0f09060f07050c01060f091505030a031209060c030f0c030c020d0c06 77
    0x29003000c9941c1c0c160401c00714a0a0407601c0072200c0d0080074020440c0c03001542c0c1940645080e81c3d0315215603081d0f03602980c2c0c403512f1507001030240c440d9207002d56511809024020006116480707203201410004c00780042c2000c211982031080d201030005110302039000502c0d801c550f4044600328055119968028010440400e6102d450440300300740c1d2000300d13a010700207412a84a020024401c03490300104903114122480c00402a4004500c0810007602d000003600009121a4000d440c06076120009100b07a40240d01c0b0344c40a42d000f00820409228085959a00221100786901640b0701440110344541008018640030465030002c141c40f00d1107481a190507004d80c0008009040d11900c02c1e0b0a9903006105802c1010b00300030207009200034500414080701c0300a0028188548190303001c4d1100c1c1c2212500d840815611184100400c5d00c0b4020b241351550240c41c00101c41041109940558802d1a050b41c181800c29403401e5210703500141d649003440712464052102411454500c014040314 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 537251465 1250 537250215 537250223
    0x60604090e011a0306010b0d02180405130515060117090f16050a3602070c06030603030e04090c06050705030f03090601080f1b0d03110f010510080715030207030c 71
    0x400c0e41022203030300543c0700050412000981d402142c88001c10556035490034080c600701401d00f8818881005a9a0050200040d1800304c400e07555846401003407c43c0c10443e07003801e0340022101820b05101042c0818220188140000900d910303001700040d11440c60001182801d5180c5000520f04c01014451a000360719400e0030748400070301481840024081c3d40c05105c0c8500b00315900021400c0c880800409080140c008000c4c186500ba42c0f03020380302c8100321081c8241d54003040100e0000f041604d407903014005a0b140011003504500f00203040300304112007a801145011280d9001c5024040074004035880303450426642c00113803174071500b140100e01c0e03032070b1f4620b0000c0f040c400380d0403010031801c3c140e58408040b11812640b182d881540c0320440c049a003070429941070165814107051307012411240c0a4141035800d0020a07044603c0d050341000e900480d40d540e641800844903501c03804c14010540c9500510134603003010003a140c01055000749409040d80050300001305401008a070741c0b46a04 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 537252715 1250 537251465 537251471
    0x2030106030c080d0e03060f04050703050706030504060509030306031b0a030204020c01050402012c010309031b03022109280b0301090203070f030204151101020d020c070f0501090305030a0806060409 87
    0x7903441d007650442102d00610035107010382d038400030210780b1036519030340f981030003c00074a00c54a80000348484420050020368042c058440c0100100700c00708038100050400e079500040c185020700b8442c0803540c016000740c49941040061100954002540e046c4650190140c00d0440100c1c40c0098101a102e50000350000d0010810404041041d03218510a034000c2e00d98100c81c1c0452000e86602010342030b140002c1ca140b80b12500700035403089d80003c0545201e414841c20301c0004600240c0d180040301011001039000e4100d80340900c41e140c0d613542142d01c0080d00c85040c42c503800d0024001401c1d032012090030406040c803081c28441a9007501009040c0303412510b80c0c0b56140c01e240000380d44220350150200c0d0307106504a5190340b1910880b0100e60641c206000e040c00f10780002c550b03100035411031032460b40d003d00140012080ca4030050000400040c02000031520748008142c412403681e02903810303c601c0040c03c101203507001c01202c24014451a203a0410743e1030400081c1c0ba40125080b003401c441c6 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 537253965 1250 537252715 537252719
    0x30201151d07181205010b0306010609030602030c090409050c03010e030418150f0303050315091605160c17070506040602070b0a0311070303052e090e07081204241b03050702030106 79
    0x1c80710f1080c013100360082c0000d122035203644050588d075050031b104030030000341e40040800110712a03030b0186411100c50042185040c8002c00060196062030340292a04e4011214540340c3d0320f400d100c1c02d40c171149800041d50919261030b94251500c07850f451012085603c441902d01203210841041010703066243d0f000300a50344a040080ca0750b00115154448074507607100078035161030000c4d03410b440790041015034400f01045150440e0300740c02026000611994040c44000015190000704010b80954030348202d0008440e500b031403500c49a640018050309040000703100301c0d40d0100c3c1410035182c2e041122652024030600c110010400001c41030312a42d004030b02c3d1000c06034180c02207030140b0050890303181c8104041a800c0c03000801490204940c074030300c050400000c1305613002040040b0010003a50070300c0743d03a01c4149052107442400011407800014050160074040c0d00b0554183e104040660004106500054420103202c003280aa4150550103d01014450411a498983d018000b0b00030a6 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 537255215 1250 537253965 537253979
    0x6040e07032315010f030213020d09080901030609021306030b01020f061f0503030903150a020c1c030c1e360f06141204050c0a030807030201151d0718 66
    0x841c82e80d5065954020b0319414442c2211000c900c0f81070782c510b07002e844115481d5500304901084100d0118a03025024058011261413500c200c01d030b0780e4041d1440d59952200c2000040442d1b10381c0d006044010300c1401608085190380880c07500740c80751820001a4120341a00507460010400b0550314684112010010040b50882109440c00040001c18540d10340780c4080603102d0040c4910f1981642c0f10180b482e60800081c80900d0300b22026010041c03401658442260500c15005442c014403090280c0745a01a9414170503a06c01e46064602a50a800a100360403032514110324024200f100e136a1520703c9606690304000190310b40f24110340320301036204030300c01c404d00c4651040b03d2540c050344500040c114010080303a08542040c0011034500700c0c2003003518011a6024105a40318400c4a120f407806480303124001000c1c40c0110082d40d1602224640207003918412502100504001241044005060300061449540007a071154a590300d03101c00b1140c20000c0e41400c01c803480110703c001015 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 537256465 1250 537255215 537255263
    0x30b0403171f1502030a230d1e02041220120a050708030f041a0408070303121b0f110a1b06080109060501050a050d09020d081903060e06040e0703 64
    0x40040101034225642c446082840410f02d00b4040050f800811030b04e140107100705c1001c8409081c3e034080140c800c2c01c0f41072180d003640100c2e01105040350348211030140826160380c0d0304640c4450440135842c01d0301b41101d00c003421801c058010018401d1490702544581c83c13000c0c0c20620348014018912414005035002e03619019132506a40c60b01850b100400c4146010049038490102405101d1034903180642c80c1560b80f040d900b007140f8003441884042925081489030a0055000743c1c5c5034648031016a100c542100c000e54280c102d03018000d09079107941604165004042c0c02603042103038034055544145401c0c07850f2001e00034104055001e44001c2c01e608100c1c2d000c207651700b582d07446070160b03203c8805404585641c040c10f40414024000c00300800e108100034254407002d03a00202d50341c0c0003540400c3ca50081c1c65021a107108012400200e58098a01410804903880c603040c01040d00d03191a04204030f10190416014907140ca220365420a004c004a0008542c401b030000460a84403a0540d00 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 537257715 1250 537256465 537256501
    0x170d05250b0f060d050d0c111306061107030b0109050c22080c0102010e060f0403021e010c030b090708070305101208090f1e0907112b021501030b040317 67
    0x9804200804618607042425030104c00b03580c4140100704145000300251201420b4010445241002c043d41e00e8190716809180e4642c84030b44e8201145040c20008090549480300090001e15400520308201041e590b039916811201d051600240e943c8a031180c1030351b140f2552000c024100c5508000c4c400048000c01050100d840e40410703109040300c44030049081c0c480da80a40200fa602c4080403810200590850703507009403090048440304110752168581540d02d01500600f2079550352000000303141c26002d480e0307142c0400c58a02945140008014202c03072009894030040540c2c50001581310070007482454060460b1103070070b048550a83c9010701880d0b1016048500501e01d00050400c00d04084440300940500086055450701c1035600744070403010020400c2c02041070910b44c41c8440c01e000d000724440c00c0500c103140c850380c201d5250116040000c4000c040304640c09540100007130840007182c0c0c0d054035444540e4206c20b86490504a45c05c2c911a144000424078072020711224204501950359 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 537258965 1250 537257715 537257731
    0x1e0c0d030b0f0d02040e0115270c020d0f0228020f0301050c03181005090a05010510060203160c0506031306050604020712180803040605070b01170d05250b 68
    0x40069000c509002007007000d50303072050300070030076110b043d0043c50260010740c1c0e1185440d0000581e040a10062054503406070b000c809000c40011181c80101c42c003209000f07210801300e03001e00101400e1180255035003002c0c80813004120002c8840801700f8424841d1a11036408885948400300c80c95485c051542e900c0da80803442161817115802c0e403820103010b10b0384500390b09100c9901303503581c0003a0307180c60248503461010a4002c5245040200c1e5580c0302e80c3e802650040020201300650346020303421294003910072850107884039410007034640d00000700d803002001103948103e40030315803034a6a01120a40c20445d40400c000c01000100940280c1030042d550080509021036100c203400d0004038440c0850142c088101c80d140841e5050003400c0082404120725400407141daa100341e85415078000b40c00280001d0030002d03080082c8400d000078107014040c200130003d40e1100d15048180c0e120905090070040c0540030464644008821610440c07003c0203680c422108030262515040846d0304403903d43c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 537260215 1250 537258965 537258971
    0x10608060112020d03051c09030519032009040914030c071e14030c03070e071d0a1a04080105011e091406060f040306020c0c0102070806090307081e0c0d03 68
    0x810310740c54030720108010380151207a600070b19a80c17811640d59100a405070542100d90345508040b202d01d00c981307038845009030303115038881c100504001c0c0e400f07100f6100301040504111012418a0101003003c4083c0c0c6803220096884044002080c082d125585002e4103c40802081136500c4034048020161002d078a02074610142d26003180c1010040d4116440e443e004841d0424014400c444064041c542001001c4907006c08480c40043c0c600201904143c07804a524024041407039003000703403100706046440e006e030b48180704c000100791207142d80c0c81500e5003c04883c4101d800040c003441107502400c012030090000d0341c0c4440c0c014810000242c8131806a00b5801700008421020344140742000c0c00301c0c2c000c400103840e0b00d410000c80d0380015801c8500b6101c04c00001001038150f00c01020446046401b0b080c0c01002040007a080040c69481218150000410460094800300071224101c4e1303c4a4241d4440030a508020301800e14140d8101d205a00014054144000041c000340018540d56040c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 537261465 1250 537260215 537260219
    0x3120203030103150527010605040b0609030c04021b19051b09190e0102130806010b033313020d0e0c0f040b0d1b030623220b07020106080601 62
    0x8036540e1000b40710182280c0507603540700000c110503400c031070340002a07503c41240000c0e04c4100d92840c41c44441c00b101140e90348180402c5241040c0c0590b030203000b800c4507001e0500394580c01280c2c81d0082245003c0c030880d400248148282050b1000d030b03544d0b082c01c80407540018509040203002c0e06ca1503030141c410b803013050202c4c2c80d0050a01ca609001e0744c40644451070a0b101c241c10b0186800142c6005098113854064226201d1000d101810180081103c100758641c41d00e22040e05110741030300a0300151000300300300f0005494140c0d644800d66030075900c410800200c030064182d00200d171806550b00254629640c00740200c075401422400343e0059003000103860400c189555410700903442d42d0014607003219801240b030300c1e50040803d080041c1031035014080a5556660f10590b1446194006009038003d0081c40725a201c0c00814207042061110399a180500710361800800a007400d500c2450800c3d05040072002111030301c0e01d180c1c0007100b51000c5c186420040d020380540c0c05121142e00c505800 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 537262715 1250 537261465 537261467
    0x408031f03030e010f0215091e06040803040f05010e01020a030912090302030d0309060b090732030408030604020d15050f01081003080a051b150609060306010501051b0a0c0312 77
    0x10541140d90540302d403c0c014015030700554028201400100c103500a00b4144200b22490b44111445800d00c88058003004d0388080710700c5040b088050216a45070301000170040042c1824003102d07001034120070011106400d0b89045805001c0040b844140c5500200e20303492060740607000244924807440a5031610030032600100c4800c40d25101c0650f15070712164000911500a60045140c180161800328660950002240c11510709071a00400100c184032001221403408000018a22428140f4042d01740707000360181c918040030740050f041d0500040803400b00d9459078101c504101000300280803688040101985460947c42401d0081c143c0103e0404150302c102d0680f44248101103000c40c5407801e41e102c00349a504284d4520081c80400c10034000120481541c4c0c0d00c10f925140000d005694505282c4000a0720241c4218015500d00c81031107050303070340403400a040d00c500b03107455034a82150010032601c001480c0007100d258068008200188001801424161303070107100308200b040380c5408 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 537263965 1250 537262715 537262771
    0x2e0207030e0906120a030e0a0305010e0a03090e1009020d0204030506040606081c05030c090a0806040b1e0411010f12020c0309120a0201050301032405090d2709050a14040803 76
    0x106941301034120701c4580002074020000c0075459040030b00790b42000c1c4e443c4ea64042c00c40b220320303090103841d900c414070010825a000c108100500007000d0810385904200030500c50308041c6010390200707140c02040c020780d04036040d4142c8004641101c2115001d0802d03061403001000300b40511042400782a4284181118180d400c1c000107050303569141c69581e8204500b4001d8222480c86a84081811b20000310a40c0411442d401039003d044c1c217150740e023012108074051941c41042e081c460400503080102140d41400030701005602820400302c00081400c2c11900640034094160f40c291001ca480c08070760714000044e00c46c0395825541c00d00c5074004400e20b00c0d604c0c808480000d0005004000500010342c00032094103456500241c000007400c0e100d815201a118115031030703005070b402001034201203644900300844107910180b01540c5e01d10381d85080d40a61004d401030b9903506403200086051070016070f01640c6c1809104a0130502420f040c9817900480c2c4c01a00d0310103414005c0032040e01030b100486 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 537265215 1250 537263965 537263989
    0xc0207150207030b06030709110c061006090501030914010606050d15030209180f0a03031406090f0c0f040f09060e070503090304060804080702030d08272e0207030e0906 74
    0xa0001c180076403641e03942c4030604c40d00900d01a0540140380d400285042c550164038100040f44201070b880300c00c07601011b40380c074100406485444002d804108040c1e508108000180c0d035080ca40415510300500f0071002040d85407000c41025031800742c0004215900101803c0e08034800e4005000001040301c2d403a80c0d01034180006036229850308003054083d004100941031201d03800c8203550980600380c030020f05003e00d04009501090703c42c0019040c1500400031143c0c4804100d03110380e905d0400c0011400c158030018141e107540000000c2d607000b0380b142001aa4010440d03803001200d115198840e500107070404e80700784105101150b010460301b50084003a41d00c80d4820100035400e061601c0c03800c0f500d0071000340081d1540307a0208051400340c2c40c1800621180c20300c648880f001403c0400001030000111040d03480000c4022070740c0c1c0c80386980414000c1d00007000a0044854110084029a2103040d145180350300520000d2217408054001010080144c1c0c05c0340c8501c0d079a52200103101c2c8900c515 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 537266465 1250 537265215 537265217
    0x1707060801081917031e0105030f06072f07090c090326071505090d0c020109150509060d0b0f011103091e030a1a1807030b07020a150c020715 62
    0x854440d01c0310034801c0c0040c2d120700d01444425140344124040341c03416030300591b02801d070400e803c180180c040800740100c1e401460140c00411400c1d900070025621040058000c604200b81c600b1b04422103183c2210314681441d00440c601c030f480790040c6440f0b40d0740b0740a10402e603003a801d00120600084c0141501e5003101d400036500302d50780c40b942c051204100d042c00021a240c0c40d091146402081e0001500015204000c10016080c24103124403458445040d0280c400c01900007007110050b68044148400c032031a2515245441c00000d909030381c0b500130844081e421042c0403603600c41d0228075801000d0702c00c8041c3c0d500e914030b5a14000450700004115030503400340d841000407602030f088c004c050301c4907085080d9103e40e0018403200043d00303003031b46028103891070204961128100804000314035000650246001d401c416400e400584400b00c034030000c0e010301ca04a00261140e4020300c80c0e00141c2c0d03801001c100310a41080b5038400100641c0c00c41000600c2201004140b060f038441003e40c1e51005 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 537267715 1250 537266465 537266473
    0x150106021203041a04050a03181a090307151d0108040b150415060207030b0c040806010b03090c1f2319170a09140606010c0807031107170706080108 65
    0x880401c050a901c082e00c2203441c1128001c3c0c0943d000c2541004a004038031450240c070b4402181c0c00d00424a01c480c0710030301c2070f40380782050030014220501881c0c2a20306110b4945600c0e070742d10800080c10312402c0e42c41480582220b8286141c010350194510f40d40d0a1001940c1300c0c1780704030b8401124411000c807001841c001c810310200305810a031040b41855104000c201050007440341515262403003513580314401682c0907800c01c0c02000392918000e03a01c2000103080718101031814241d65941c1006126503650043c000021420205051080400e03c0e0f10140003190303a60302019090004d5070b17510301d0710b80c001043c94042d00c02251a0030704030400700d600341c0041030030a0b9481801e5040c9404155400003405591001c02e68000a43c4030702d00d10507010303014005160440390900181c8418600f80014243e00030030200b00ca240e80009911b0300450b04404001d445000b103140540d140103004402c40100e01ca640c1c000180e034400070a82983c030004c001c09640d60280d84001c01d4030580d42c01e028807922608 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 537268965 1250 537267715 537267733
    0x204030506010b030c1209011503051c020318060f160c050103050106022d0c04090606080d110604330c030e19020d0501110d02070c0b180108061207061115010602 71
    0x46c8000c0c868004501d00300000e1454010114007502400751340c8100c0c1e151700000f2182c030301c1c8020441300d5401681140051450030400790100d0905108130304001c5d100300c5d400300d680f0b020421110701351500358042c071554460101041c188043c10610350303c00d00f80060308140000c00c116101141103922250f0344514444210018109034150b90808001100c3c82c0c4501198012580e4aa02401520a01601c40000c10504005804d803c005800511f0b4092100c1c560703900c400c0b004000b800580c040c0d00041c900191400c0d00c2d03c000348a4452426030031034000f1191400d14100001e0780502c00d0450030f610104400c1a00c001165216041c1d414980e82ca03806144480002d4140700c401d1404180c4140c0c0001005524605808101e810000d90308200ca607000c540e010030010001c16950107088440f4000d400e1000c041e500000e4a110030010702e04008400c2c0105a1988998050004081040069546083d00c880e401000f08480c1d100c5481d29125031400344046000a90b042e030b0603500caa9003e080045 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 537270215 1250 537268965 537268987
    0xe010b0103110d1e020d0509010606080907170a14060a050601030b03101d01090b0f070804121d09010602010222033810090e060907090c11010903030204030506010b030c 74
    0x409442c811300200c01c205400c84a059861000700b121a000c000002054100000b4190071600560048414000810140700351400c00280500c200da00045502d011804205006800c006036210000c080006010302d10000080c045013140c42007169030410070055076001c0c0110252950500034942680017850103c3c0d129041381c1200c45008481030303100304541e00713948110b801c69008030819110b92070400c0910554000d000b6069403c072140c1d161515030381c14652034110440bd000c500c54002e100c611001044c6c1c11107111aa00000035000308601b1b12513030345040c041d0203584000710340c201060304030100c1d89081280024103001d90340c000103041c55030000085d1820b44600f040d0095510884448070f500101d541c09c034440c0b44200007016100b1041850100c5039025108444d80c000216004041001041d60300040e00174111a03021102003a4011501001c7d03c85c070a40c081003a40b194200002c40c414943c140d0014404c0f43e124008032107148c2e83e90540403405000903510100b208408000c450010 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 537271465 1250 537270215 537270221
    0x70c031b03031806050f21181c3009030503061009182003090c100804380a02180114040530010b0102100905030906030a0b030601090e010b0103110d 65
    0x25400090683c0c403400101d4580d07a1f01c01070115030b10303ca9620803003400398078400c0034003440380201d018200c90001100104809005030080803015001807100640300c1e803075141c1a55201014a501d090200010350032410010140c2d882210014020a1280e4100380c0c851305c240c504904450022254004c52101c145000010b42600541016034040c2c05045480214440d4000d50142202c10024410703100b12205001c8848030000103131080c00185001c000106402c921480c1c450400d0b08203e60344020003401041d00d0360201c80f595100c21045608002c00e100b0b103580103250f0161540b1541c58118440c1d001100e51241d031072020340b0032000912041045050a055005002404540b032080d0030003001c80040302146100d0550f40a80c0d1564026511560140a401da0008821806003c44c8010740c42d196520310600118a0080d00000009003244180c1e501407400c150300181030320030a5942c2d809903405010b00e0801610340b94070b007170082c20007036001e0700c00c600d400c500a803440c1b030500680205030802 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 537272715 1250 537271465 537271477
    0x312031504110a110c04050f0411030319200105090d030207030905040212070e062a010b09040b0709060215060d060e07180608070317070c031b03031806050f 69
    0x21030b0710b03071031040c10202d0040d000d0124180f2a03a54200026001032005141c0f04500440324003482c60901806501a1664043d681c060b0304285a1040c3c1061030303020901c1d611072820189550320384100b04c0c15109a12002c2e21568044901e0300c00d0008186a1002e03080340d00a59404045600c00340d00072007420f002c0c0e00a40940741c000c3c02d2003040c9503603d4020400b6640040d60180010480c6000c0001c0b96800070003280c24210b040e00d0081c2000c603810000708400408016030031806885007050074124009400c110780700070f40908030030014207040ca0410504041907803081301090704050b002c905644005188584c006c040e024004060320340005001074280d041d50305807001ca40350b444050124a04106010007440301400208020415248041c1101e010760402681500019810000b1450f054036814584d0038480715107030307525100e00c0c255482c41d44507400203107403a42221381813100104088407841168003d460b0110345013500d547e160001e03101c0d4098107021500505c9181e10b117003d140007900d1 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 537273965 1250 537272715 537272719
    0xc040f0b0f04030210020a15051f050307090b06070503040920090307051003020c15070201060b16021c0b0c131d07110f1c0e01050a05030f0a0f0c1d03120315 69
    0x520051580710040703c0e4230445090f03035125454006214500325a0030203c4181e540018103e50a1790409001070740340e14440c82119801501e40013003a05569400c2c0485441d5a8454100e0307989130340e02c000c040054150303903008980990550030414010751620044402111004014011440c00c010400c1062403002c40c0d000200341c0d0a11692403028400c2110000302d045016184480c0c3c03034019030090940b001034000c0007005509000300b10700c02181021480d0341c26411600400c5c0c124000c00d1500312684c4050001d40010100b0080c007000c03406240040c5102021210b00794042034444140303421454201c48005020b00701c80c00000e40c81e034400d250000030444a030701961039144daa00401860840e0b08e0409852407100b450058030955001590003d04040a0074000e003400f0480344003405a00000b400c415000d13050400250b041010303a0300a40b100c0054050401c88a03d400b84001d250a02d903011070402c034407119941005034540000c2e000c00314055952024910364400c030f4600000003081c10529 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 537275215 1250 537273965 537273973
    0x14130207020d0506010e0601090e0609040f02030a06020a03052d040204020d06080705040507021617010204030c030f0506070207080c0d060b0901080a0c050109120201030c090506030c040f0b0f0403021002 89
    0x10006039a4034031901506401080113101550420031034030035500e000b400381c5060280560f001c0003070614050310154403070001c588091080d40c50303041049101096140003907240c06a402d00804104096000d000c0450055404000903035403881c400c540c50141c22610110103a51050380d241050403400d41d2071340a0b00c040c10146c00c2040c01404042503c6403500302c4982172700031120174410390a1510500340c1c80001840280103401103a01801c8107101103029801a00c02d25030072000c1c0a0100b501260015980149580003041d642d0508106c800031071001118207008602c04298914800901c000a030b440007070150000d014160100f00f8514201075007124140e440300304040e0103691741c0c0040c60080008070090851944a460000b42031103a039001030341441401101031203613001710103104600c00d5082c00c0000c0c5050903258142c4845040e03500c2294403017000410030400d0544400500219940a403510100d01d449022540c1c06005204401001c10018031042026152000b15021007800a00540f = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 537276465 1250 537275215 537275227
    0x10309050d05070b060303130323031c0f0b101805030307030e01121a04240303051b01023109050901321b0c1b09060901141302 56
    0x1031400d000c6124050004030344081440c50903c4030840c0740315807140045020b14900200515072640b240e40b90300015009108440707003031381180d14481019043e50342e06130449403100c60036a40c0d46c403000c3c41e55400004441c106100e104a110403800341100b0200c00030f081001400d1900b008503008a812120303518803c0000100003036540f0180004c0080c2400b03580c46002207500a0009420f82c2c400c0c41e003c0c68141d18210b105c80c8140b078901c1251030024812100451007460200c0c00f25900e0601d0003101c0c060003002c050000c10160444d0003812017000540c10740f8801d03408150034900301d0040b4858400242200c0b004200795081d01503c204068003c03448070302840744c88480e2101118021a01460240c0d5645d0106030240300d2038004030554400783e4000b00703900100c0c40b900c0100280185c64158104441d0700c00100345201300b000d5480000e110340480700f001c0750000103880064018024280142208000b00d1401d00b070154403941a251003115021411008405115441a8030003c60100544c24810 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 537277715 1250 537276465 537276473
    0x9151210051501080c04060c020f0112051f06090e04060f090b0c090f06030105180a1805031206040603020102030a05070602121905160903140703050d0503010608060d02130b010309 79
    0x1d00e40a140c14030112990401440c002400300d00028046050301c090a01080080235489142c2c00384082d0b060300e40606045840300140c41c81010b40c4460100f00e1300304420030500030f0004004d501030801701c0706a0b1800d5a6145410741e074100b4203005803030808410070000b03008114944c000d28021400d60302e0011310040c1944807440301d0303e0700f0344a021010500160a4050b8580703c0301103444508121401c0b4915490400042c011080d8010520b0034100e8940c0010040b114907070003d116000e00042d000c0c5c8104151401d5a200d500c0044c007061096104d0012906509051060303209803503043c1c000b90b15202800a098030941c0103000c040751601e40821000c55005aa0012603006105400f454000d480d1421600016101300034104d00120b544080c000003c0e9900ca0807550489030000401e0340c441410bc0c1c0360a08100d55034001034400c0c8545485c07420506c4d44000203504840b05c50380d034a942070302d0315400c100306012440b5010758046014100040d0034480c07540000f4003035105042c000380d6901103a40b = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 537278965 1250 537277715 537277721
    0x7090f0311031002191e120513120f1b0b04080f270324010b0706020f0f0304140c010c121b0803100504060e04030f020f0307110f09151210 61
    0x1145c20704181450900c1030100e80c000c8026040002d07091a03034411021400d10042030020010305851032907494001060182500804203d000c0760070040f0b81d00e4007403000201a0860314504402ca0000d0700c050301042040e540c142d60404010342c0030140304025200c90301e4400c00c0303030890700701c180760741a0400031240c402da0941c13030b00e66848085240c540e40e0660044100344c149004c58001d11600c0d07030388048000c3c1450030482d6490564550000c015141c00050400c14024080c100c1040420740c0300040c0d104081c80d82c2e038041d602c80c40c441d01c01031400e61601042161540d4a150740180811002414130303001440c14000c2140302c892525150028010b680301c140300020b1640e6058561620010a000e404001e020882024190035a024440d052409030146207641e0001d101404008210303444800482c0300344005009105500c0440342c6501c3c1c0303030410030182440c46030113520412580c1e6003c00c07282000c030501e51042c407280d159503140724584c4043c42600b00780521000464091140d8801e01d60305a84 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 537280215 1250 537278965 537278977
    0x9021201062601020c100c090513050f0127020d180f0501050106020102040b070f0813081b01110d0309020613230a050a1203120203070302090907090f0311031002 71
    0xc41035045200704822803600b8a400d8549103075164010060749400900014038001038005401c800110780320251000c484d50300d00c68000d507920043c50f08806c41c5125050b003041c3d020745144040c0c1c2201d079aa503100481d20708007a12403103881443c0340003030980510440e80940124260400c0c0420b1084c103528242ca8482040b190489049444540c0340d0103201007445241d02400c2180001c610741410a8100350440c060440e000300400070409200c0b0400203480103850f203004080100c3c86080c0d1700c400b000354995035000852420b40da84400c40c2c1e9025841010750915600c03002026007044032080f0400c4015200c0002d0030380c0c1045e07042004c40b02c481950f0020200038842d1a031804140001240c41c5e41c10f111020705e00c248102d801d417109000554480d5901c004581c0d40c10703203451075078040d8602603440340502101d9103a20b900c080300700240703180c054005100d8000d0440300f5031800e03502d82000760303503400711800b6100407094200390503c00a00c0c81e01d01c03c2c21420004045a03680300b40280498181d81c407207 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 537281465 1250 537280215 537280229
    0x80708070c030f110a050604030f05071707060216060c0803040302071a0d390306080316020f0108091e1c110607050403051b1903120e0a0b04090902120106 68
    0x20002c40e409001a070140b60901c00003c030344a17229989080300040b414061800042c1a00240d41c1540302085010440c100c02820381044103862000000c070020f0700d80d4054498800540500d1b076110050340c4841100343d042c0c40080c2c4410001c40000c1d1500c04c1c00d500b00400031420761041420100e49500a0b80ea0b108845202060341075440d5002c0c4541d100355500c00e2100c101500c0741c540740c1a110b05940c074000304440c40d050340020039055011000c81c013920882e4080d0720340b8000052810f405072070380040d864030903001b07460302c1c96901c4c0603000440d980e00307048a4500d03098100c44c4500c00c11403140c025207055602c2003411078002245429070f09003024800510320000c100d140c0a0010a51802d00415501003810b0806a040c245551112a2102868440400c6590440e0f0b880f18030790f03503010541075403506180c00e1071100a0305c03841d01000918440f055a40401d1100782c02651600c2c0409041c016240d0080c80d040c1001e2810382010003a0402c60b00481e4000c42400b0a603280203000d10070340f0014814 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 537282715 1250 537281465 537281483
    0x50d110f03060c13050a1404180803040b01030b010506032802130b120f0702060601030c1b0b010608130302030f070606050d03081603020703022104091d0c0913080708070c03 76
    0x15920411990002d0745c881ca025a202e50020040107003180c1c284504440161008103002000105581180c1c10041d40200510b60101c24031080c40701c0281200d040c0d91250790a00000d90300c68042000c1400102c03021501c000303c0c491045041c0c0d0b0442e0845440645d481c1e0054180b906d208100c1d00320b070415401c00c007000100403501c904030b01c0b0222071541e00510113604802c014149810000e403a5100280130506040c0c90b00c140901291142011402c2c20650b071140380580700c220714101c44104803e204160011b46c0e08c00100709001c02040070f120b540d42d03058006602d000d01c2181d000e40341d50400101503030400d40d00c5000007a1900c4040110103414480d56420010b8074040442c3c0a001c0702c0b282c4824105481401400d000940006015440c029641c0c03612596080e03000e100d404a11a0f508410059400c1100c910045992041920400c0c0500803d0b03507034500025007070040f000e0b401c90341b0060905405020f0000700300d1175001810f0850098140354a0300042d80c4606e2012910342d8400c030f8501d58 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 537283965 1250 537282715 537282727
    0x5040614040c051204081e0f220b1b0304030f080c07061701090e161211042c12030403170901050402090106050903070e13020a060504050d110f03060c 66
    0x1074a8030030741d036034114241490303401c1c0b645541d5a000304c0200140014511880080d040319821083c03076260440c81200f611455460445030f0b0b1404250700000034241d0300b1034000c1300c4544002c41000d410001c0e90441d550071810001360264880c844005841d0300841400100400b0010030111050007204034003a41802ea6503401004800e49858a00d07400002040090f0701035604a000381c6002c1030442d950101c001c6141c086240310340d41001803500741712401c0c140c3d10b900058020034400310a26902c2c020165920729400e820b086c04191812010307180c5d000454907803400031440c10701d800f44030548518000c803001a014030640d10800d50083c2d5003500032031449140c00c442a080c1c10001540450100000d100702c0c1059404950140350600400c4144440498030b250f03191010449940109110f1140074128149000d800410740c1540704240c0c01a001540003040e601d0050044404071203000d031840c00309e0b1080e0b0310b465000d0242045c09513801103003081030f082c1e144e0303007040b10034082e030382900318565510 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 537285215 1250 537283965 537283969
    0x1203040312110d0c0204091e061506030b060403031404090c020606040e0c01080c03060d060603080309060618010b0714100c09060201090b0109020c0a02060c0c030127020d05030405040614 82
    0x20741e544241101a8403030803c80d080240d0005841d0b00040e811b48003c43c0b0700545140070020344002101c580e88403910302084009001254000d1401c034400b414100380000e40f00d0f08200d090790305503158203421403000c01040002030303c545601d072030703012004658506080e1110004030a403078009141c180143d1000c4240704140c68103110710807801036003000034448840000300103041040c0052040c03865080100c000303240ca80b40e04a06510050303005c10100002901c0e403030608825002954420420310440e40002c0f80e81c10b111402d2980700b1700c1078495410b03a170310b0b0240c04040e070382c081d01d0101c0740c641900000d40404001040200124a130011002c0f410301c0203039800408568080d801002161306100420000c6810920000d06440380b0020150307442c10311901641c94101c8260000303403c06000120003c0342203003c944143c00850450007072140d103802c8054602d480c1c6840307100d003416100c00e02e8401d00519003c11120003c62007402500e0a041e03441c000101152215400381c055580100c02404040c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 537286465 1250 537285215 537285227
    0x209040b01110a14070f08010204030c120f0b040f02090f070206090303011a0903011104080304140301110f1809100e0a0501060503040f0c0b2106030a020312091203040312 75
    0xc85003841c0c807507031410700c1c12007a50350b40c1a08080909010046114000480420b0000d40d02401140728050031003a074900d15a4000e6000d4030050b144c4040208000c2002494003845006c059046503480000d40040d032105644414041d1084400310710141f45480140c83e40d80c1958840c80d14001c0456852500395400707800c0150040c07445201da0420001441600410104c55500c035816880e0b941d21404142e011070300501310811258402c01000c140080c0f41c0c4d500100820a0741d5202d22021105c004920901d401d0703d107903658952115100b4005120304184280140500c2e9100c1c2c40b207141c2c5004c1c0c5e000400c025010541e0001c006000d00b800c05d008450f00e1108407600311180090070829585070103802000388c000944001d02501032000404140866a5001c5014050520640341d03542a0303026076509800003803200c4580c0640402c00944e0524020469401d07036a0007801412840700000d4031a030721540140025a4404503005554403007507800c04c0684041e503c50649045000994103000c0c02c4 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 537287715 1250 537286465 537286481
    0x11041b05160b01031a0a050708160c020415150309021c1a09011a0603040b15030a05030d091712150301021204060905010608060907060c06020c03161104140412020705030a06020904 79
    0x1031103080031b05000780127500003015503002c16521001d4104100d400c0f0101c40c440e4602401039407060800e4610314406844240c020206c43c0d480042d1925201c101da419401d850fa2404080d40c452100700550720388024142c1c030692014071598242481c5503410808c03e08042c0b0a461108490b9907904540c561403071024805030401c94212103c5046261540d903c450105d03004101145600d01d9050030550f54404002c500415035000c8203071780c0c952600d00c218100401e40f1500903105521001490304007600f0303490407221a40c0e00c40325030902a9550107418a25210305102c0a5010741d0b0800c07017100f00d2088030103818020384c03045901052900340342c1403090940c1c810340c000051941000f030074401051800070780d100468856007004203018141e410094002e00920980316140e010010f01101c010085a0601030101d2054030f802402d0f02445050000701d0741241c140d0b6440010031000b107808511140c3c12523202079428030440703003481d40311004242020700e0901c04690580d000b00d2882800d1500c2d01a03800 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 537288965 1250 537287715 537287731
    0x1e1e090c0c02031b0d05030408160603090b0a05060102030408070605280c110102150f06010305070806010c0807050a02040903170a02070b0a1505060a090311041b05160b01031a 77
    0x1106070000d400013500c1e90005000c001c3e441d15074048402050302e4400380c008841c3d410038103a98940b59504800c40d21500760380045034100c002c0705000f048503030081c130501010503003101004180ba034030740f10301000800c0003503c903905600c028000024040e200304090300152034181c7d2a00c1c1c03983c1603160f00b51000c4480d2a244030404141041c81c0c3d1200307512054500245401441c03e40f040380780940180c4c10800e59008401200d90820f0400000451542d4950b01900c02070380d00f00019507860b01c080740c090009450003400100c1d9000214082070b99a0f018144441c000d82c182d031500001c0d540001e0440d050194106e010440c81000030f00400300e000c58084d80100504c81c00c0d0314100656035180154440100324040c040d90300d00f0800e002034881c81810001d0322029080d603a031088143d8003c0c00700300d128841221039400c52030861902d030501d40a055691040c0540c40c00400650040590700e81e00456960080544030301940e030b021900c2c41003038a0007140600011900c00088528094081c0340c0107080003 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 537290215 1250 537288965 537288977
    0x6040903050a121407080601020c040501060f0c080408010c0e03120a0c0b0a02120901320423010f06030b06031f0b010c020d08040501020d02070f1e1e090c 68
    0x940441d4000c0102c0705000910300e82030810040b40c10341d00c40241813801d691454018003600300485213403c4807203140100c1c0e09800319401803501c00100015500240070350000500742d9110720701544d00820181c18814400c00f10a41896103560341d6a08445000441100007808280881401d050601140300560b0340000ba0301c3c581503e055010f40605042c80000304286440310019a02e0b003681d81c140d4240d4810350064541904008808a010340300c401c3d440968051300d00341d03621031100003c2c0d0b0507000d82031000745000315035501c1e1600718250509018240c007140b00b910684290500030701c14480380c400484400503c480c15824020380c0740d64000c1580d4000d0b031040310050111441c941d03400500428103600032400f51719450040703400c855a25030094205030302140200400000c0000780c01a1142a400c40d0746241c104101240d44410390f00c11503c01d6214880c044c0301154550039003c5d5040080004042e025030b5501c00030788641e0300320b00701100038002c01d40103004c0d03904170b07000d103615440681c0f0303100c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 537291465 1250 537290215 537290231
    0xc030c05190b0304060e060f0a0506040605150304030912050304060f09050102060a1a0a0603090516032f0d0501050a0c0e060906220321020313090515061b060604 71
    0x1484540059010b04185014048005420840541c01c95000e011400e400d44003d82000f1644042c01001580d041d0646800c120025085042501c00d11003203da000b4408142c1c1c2050102044403130344040c1007601000340324040420701400d414000012030b4807640041d6500d5240c03080060804042881c060704102160000f008103a80c001440b42c0c02c0f62800758005240500d140d001c1c01c00059180c20b2a1b0004904200010b1158055115906840c011829166450007003a110ba41a2515010082c10440d034101051894a104600303680e0b042c1e20204e090101c03a0341c00c800a50b07080182e00e001c031520303034607582002142d2120b80603c1c0b070b0110082c104451240809800140c15000d40c0701c80501508022138107070a0400440034000c002c20040302e1246a89840c1d003020340303500c81405070603440c80c00d0f02d804413400a840041140c01070ba00a080026640c0d05100b6100c019010140c0701d61300080c180b00300034031540d0342c3c2c20003001201802d032100103460340348981180c14903100801c40c5118502d06001 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 537292715 1250 537291465 537291499
    0xa0e0301140103080c0a150218030304031205030c070602030c1803070810110d0e0f06011203080103020d021311041d090601032d030e150304020f040c030b09040c030c05 74
    0x1810381542d904c00d542c0c0d030711046500100c40c80e040c0f0011000d07160b8142401803181d0055590b00410f070100408160180480700b10090540e00d10540c072000741001011050071076010700c50f10140d90071407030254846103081c4a43e01c414059820680748841d00b010006141c81541c40903100036004402e056020780750b00f52404072084c2e15041c0020000c1d2000e9110313201d10405617509001c45007030904131902000202c10341d041c5a907030f818008281ca03a04d4458440080350307240b030f481161440305a055031640740c640c2c02d542c01e2100410a14a040b40c100c50f01c0400118060120300500c01d4948920039403540f150310b040790309141013005c818030041e0710443c9014410002d03c0402c405054075000036103c0c1104102c141c904450307101120700d10280c8a0303144203030001c15506c03110901140100701c40800ca6801004880021032006a0f00254070029880e180f16403410a50002000d01d8107034140001c00500d0700c40403038400f150071a0b044981d000c200d41c0510030400315450602c041e003010f40c5e17014144914410 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 537293965 1250 537292715 537292751
    0x4150f0204062a030e01030b0d0f020a2106020901030608030a0c060b01210504031106071d010504060f0c060f0f02031e0606030f1510180614040501050306061e0a0e0301 74
    0x210140c2080322254280405d0b90203600300050001000e0500c0f0440005405c2c100c098031700c2d5481c01ca1107191503010000d9000980102c22030b13200149050968240d055650700c0000398456140c0c0d0f070506071070b500002400c4d0030a00241c03d0311040c5031212010322040d86041000c83d00ea2640c0c55040c450701660903444d0194600d0b5103001090003040014440d115810213a4007002c41e1307144020b40d4450340d01000001343c0e01ca0300000c68805d031441c1c0c5d816110b50100c010344060180340114000510006d05000d425031042005954540c014180061040c489482003000e03a00c041021403401600001440313038a001c201c1a403540384e0b070180030000c414180440015800c0c48060500844d49035110082000400d4410782e80d061440010415040074009120142c00c2600c0c0d03400702c2c078a94441c01c0d80051964010703030950b80d1440c0301c00484c91505080130010b40c1c00b500040c00c0c07240c1000e020300407086081c80000d02c110102e014058002d444140b4401c00904500881130514000e074100f03030407018a407a00764 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 537295215 1250 537293965 537294047
    0xf060c04031509210f02071d0414010e0309180403050316120912030e0c0a150306050604060305190e070501080703090209070e0117040b06010804150f020406 69
    0x121030548954202d0184202070201800d015101c502d081403a1001514900d8898024184540f15019600c046203803d03a03d5180d98442c81d6400c4051902c00d1144070f024003802688980f068080e0000d003500c480142d800c407807504d5280c000f5688005040b45840c42c00c0d500102e400351a861011034903151603076000340b150101409440d13514540c08901c00710940640030742810070081103001c00480c0010b09005840d060f0840001012030311b0102c0b4409900808a5003201f46c640180c01c07001001d03d0080301c4140c4000310303c100020550340c0d003000700d040e40c0da01c0e0040c4018040c84d03402154900305008500c0c42120ba030405510810701d0881130040d141c1000c40c0c04000c403042428001480d42e00c409055019104a240c029480a240d5041110302d6422030b111184299081c0e0385c200680030003041410b583c980544001d0124400d07000081c50540c49080a02c1c1c1c814820080140d91000e01c4480805683d4000c9841c035100303070081400c0c40100d60249004072108056540c1140d0010703415540d42c44c9041c50 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 537296465 1250 537295215 537295223
    0x120f1209052812050f060c180321090f0d0503030a05060a1a0906161a0610020307020d03111501090c03020a050703031508100b1306050a06050c1005070c03020f060c0403 74
    0x580070040600c941407041c40710f00170070715041c1c0d00707545485031096240341d1107500868000c0318900f00da80c0c200c6c03c0010b074523002100c0c0007024a01200301802480e0240c1c011401286e8000003050480d0160740741c00111860f19481a0700854490900703091310010745038001c0905d40102c5d0141420401034500c251910030140007901390b15030381c00400c40800c94503c111061040030380750282540e01042601a04d0801c0303a520341d5541d25994507040c0802c00e44181c0b811010006030b100303010000241c507084460089540c841e08025441c0c02d01a203000f400e21924048101a1003401e200401290415004039114242d252074114580000500c0182141c01025005420503984407203086030b184098006001402d944002c990104d50011144806011450007c0380200072003500d54040d034200e40240703004d44200424403280f90b420040c0440b1a50041601c0740038500c20f26a00304c2c031340f42035442a40d0040d0041d5490340071a00c03160401074030300f800340d41000042e6802300782003042c0c8468810503602500d0380 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 537297715 1250 537296465 537296489
    0x3060402180a0f0e0c130605060d0506030106050d0b011a0702090103030e010306081905010f050c07030f030b04021204110109151b0c0803071a0c0301120f12090528 72
    0xc0d01c0c950702c0042140301001007140340741c06811083c0b01e0002908800d0560200e805240f02c0769901122000d444062151070b40080c01840f114041182503041650b001202600005900b9502c80024000312060310f03081e154500020b006100424199032004803104104c12410310304941075010903142c1e401440060100414000320079807583c8030390022402080351408030fa00c8952030120900c21035082090840d0150702c1d0143c0350410b803000d402154403035102d0400f00c0c2d0615555850540c0c03c5000b030450001015541c0200b6500740d9140c0c070207000f076410007842901d501d1800b40f40c070030304860b13051803480d0501400d12010400c02e20b0514101c032117510a03207040842d0000f9540148003043c01940010300d0203026200102c1c91540c00030140100f40e0050640c1a641442c41200c2c01c840b18050b504c3c3c0000c15003c00060142071034601102c80d845100d100501c2c4545260f44842c85419816243c50000840304c0100300700358504035401c9294100344ca41900c2c18108041c80c081c03001400c5115507100c2c428 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 537298965 1250 537297715 537297721
    0x705040302031b0d02030f0133140d0f060207020a080615100212041707121106070201051c0c030e0c031b0409080c030415110a0209090c030f0f0c0306040218 69
    0x3101c00f044c1040d503074050100d400044591070243e018002e50900016070381c0d40507401c4030800140c50041c0c0072a0750072113100b0801130700f8203050b0003c0300b110b48545600402003501d003c00162801c890300c1c0049004610040e111a15881041059080d0703500c5200c26520030014040f0030804403400d241c0f006400c458071070182c42200400d034100407096012405841d0040390000d144aa814660b07041c1b200c040c81559509038035403442444904141c3c03009445c0c607010403459049411b100005007078060050424905001c4900400350801c5a1081241d11003070f203958603034584507054041c40100006000142110212403070120ba501e0100c5081502c40e14102910360304651610340c4418020b41d0006e0003541d0f10020900c28a81c5d0341c0c030601c103040010a00303031310300b240f0f861080d21085003039100300002e0113580185400f004062400070300700d0815801307442c461b800996002c008890903800c035440580041d0303c0c040e052505001e6490901f5001c2d07040b500402c4016503854043c02d403c1c2d0795425100740507032 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 537300215 1250 537298965 537298969
    0x5090a0917161712181f06030c0f0f171608010e0c1f080c09041401060809070e0f07120614010e1503010e0a06050d11040c1e030906020c0601060809060705040302031b 73
    0x2030f42d0021046c1c03000b1005201c0615103402600441c2c140c0f401009501c840300d40d5103598503100c130114404e03204a003185903004d02c2100b2402c0880d0750344062103000c030307030103030159001d2143d000340c059000c1081a035641c83c04107110002030151000f02c200c2100e40c04033443c40e2480a18180019002c0300003004044d00001d030211000d072064034101c000280c01004010361400e14a0fa0b40c810a00415000c20b0040300082c400c840c0000341042515000d87e0b081c05a910b0780000c0130002b40026006000340908180a2500310f01540700e1a40240040b95285405038001700000d040c410302403080307030700680001404032180c40c9420200c074111000364001100310b0b235507502004024605504101e601054010f200002e00c0310300600003100e0181280c1c10801381c0c0a00e8000d551300d481c0c815003482c0e0398095aaa24411130b020f03520042130a0b01400740503240000320740071182051030980011003c0707180d000a01082c9041001a9540092107052051606045400080c2d81d0381c0041b4032100d01c401890344108091b = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 537301465 1250 537300215 537300223
    0x417030d02030a14250c050312071206050102030906031f030510060306050c03040b0601050a0c08190f08040507120809211605090a091716171218 64
    0x15031000031912800d1071091000030345684034000d4210038400000c51604c044042e040e0300c1c0c1101e01d031804064543d071014151241c140e80d200584490005006921001d0150340c00c042c4540c8040e5902c0700380c2c1690705884412500d01e43c21080c11580140102000c980703500080f00d40040c680001c0d011401940030030704045050702d0300020301d540292100c46100e2240c07a044242030701e21a01d8203000307aa0b01e09954031a54041100c0142144100c0c0c00801c07121350241000348510b0796180391400700a0740b180c0b10b0610300c2d030020f00407001c0041c800d6501d05074242d0207402003041942500c1e000600c4c0c00c29842d459580c1d0440e01900c0b9824280c044102c0800641d002210990200909042080ca04103845d501344444907c0b0b00351818001c2d80007811444c50304c6401d00c0141d43c0010003002080d100c1040100003132400b0031044850500500515810350384d01070140580310f15100c2031030300d080b000b4500b048507940f28080819021000340503d03000c010f01c00b801190b00c8240c4100d500b5001da8600c9046241c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 537302715 1250 537301465 537301477
    0x5090a05070605091c050a0209180706080423030d02030c04052d040507171f0b0a0201060803032217030a0218031b130b1909150b041703 60
    0x1034422400000b0b0300356004005004868011549404010080741c10300c42000c5164200038044d13000a041d9100628041e03891542212240059206008050702e2144c03501000307401c804081039225082008002c40310b50b9403000400d4050102e06182d820303540e410354074003d09107031540c0660048000b620604a41d4140d07001814000c02207a0358901c0c244c0410b1444101114100300512139004040381410540100d6000f9030240ea078801c9898a0640503000710000039000c42c540485140c4030a02075041d054a82024140d0412010368a000040d0082c1c00c445460348040c2c0d940d042401000725a40f40b01030b860903c05080f038400a281c443d1341c50400a401d6001c080480880404010b100c1c0300c011130f0f4041e105d1280c42c0075060110340403510030503596a03441680d00341c40b40c050078806521410130780107080d4031034030382c0302c0c00b05800c00c107440000daa1484040d6000c3e8800500d0008120684650281001031448400e02180b024100710580b201d0340306600078241240051020700c00408010001c84113 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 537303965 1250 537302715 537302723
    0x150f0c03181701050a0c0e010c23010c020f0f0604030c140105010905060102010e010212070e060d090510061d010302010f050d02031608060306220206270418050a0605090a 75
    0x41c4651a941c0052400c06145000c8210758a0000050007402d600e21940c1e402001c036840e01c082204040b001181ea6880e00074088522000d2010000140c10003007002c20320032200400081010285e19400a191550019031140158000d20364041d440d0000b0511981042c7c141c0703444108010740c2d0074100b0f580c0101c2c00c0108459842e06c0000608606107503c9940642c109070b00030702503698041d036185d00b0707400f859400b04448202c090220700c0d001d00031007001c0300404010f4951400c044810300c10000300c504c1c80d0000e0344d058207c24884c00644e0060312071100548014100b62440c19104e17002d004841c041404001d041c062000c0c180b002140c011400e450a009041005541d285004940201c4130b1074500c03d50f4021486500200e4503514000c00e0f454070990a1204800840100c0000f41545560980e016a04000c0c100003041e864401c81401c0b54820301d1048078078001d800e808040c80100c0390031000c0d81060303154001c0004009200418803130304543d0400030220f000e880b4400c009003400c0c03a40384020 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 537305215 1250 537303965 537304007
    0x1090f0b030d0305100605040f0e04030228020a05040e0a020d060e0a111e03100207030509060417120c0a0b04062406020105011530020c0102070507150f0c03 69
    0x8401c82d036043d04105e21403050301150708140e50380ca060a50f12401a8060a0300e03012400e0b000b8802c965010740c3c130a5000c4e000388100d41402c690242481c80c09500241c1d02400245000110f40c1075080c40d142c0c803001013500381d508120001c429078110344c90341800d410091142c243c0e14441c41c00e20599411055015103a4401e40f011100c01e440e100f1511981001c00d03034003d51a01c020054420034100407100310300800f0b40540f016041c0008200000d6200320b6046051001c00d00c0417042d00c1d00c03400c018101130300052405c1c46204209030400d41c41c141500d51303148007010082103c0240180701003550300e0410ba00810100c880c0e111840c2c5207010f03203588201c1e11846070452101718000e104000305101110519002000566225070318030b40c09101e015800b1002c10388510003e1091008905004c0c1214804a121070900c001c0c0015031081ea0b2007032405003896900413402c0828403031f0030f0001400408601e500300d00c2042e20b00c44040e0032803c000c0115010b01a440110105240c01400f9203003090034401c55107 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 537306465 1250 537305215 537305233
    0x10609030614060a0e09011b080a150b22050607031e090803071709030a0606051503042a0312080411101403060a0801020c0616080f01090f0b03 63
    0x18501401440306480d02814002c4095408007407084140c001c6802811442041c0e0401c00c0e0541030070b0001c0c000105a659034540b5100406014a1030000c3d00603568450015003000d01c980d400b60781641103006142c12503a203041020103e000100c1352040c202c104210403418280420f0b40380251154002070308054005907480c1096800303544810000e0b80a4046014074440800403900040d1901600c0f484d41c0c400c00588011500c0303c5249502030aa80703e020345070410220201c0e041ca0229441100c0143d00c40d0407d01c8a450000c840e070081202c00398106003507107050380710001ca80d00300e10280303e600039012282c606050301b80301d00f11020f1134101e05030003400080d0307500003820440100c406079854600c60b000782c51240b6002d40300d10003114031075882200c102000c03511506154005030006501504032840001c0001c401e0000d040b0540d030382c40217070405191401c5845540041010100100030211081150081018410301d054950b0110001180d1084039044402800c4008801d540b502c281c61070 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 537307715 1250 537306465 537306467
    0x1501030c050904050415110c0a0201050306040b1908062824030809040b010f080601030518161401080c040b070203070b0409020c0106060e01020d23030705030f0624070c0e0106 77
    0x10100e811706c4108420459039034100004d0841e40901c000f00745050300b100550601543c400d0300995080710000700001080312000300000d00710703030764801c42000c96100844204230440040c00590390015038181680387c1d03410303040001500c1d51890705503115a20356512064259580d064100c039940c0c90100013001c05a44c9905103035010ba0002000b903845a0300300009c5040c07035441040c2c0c0c958620820f071a000c3c425110180190050000103000c1e007050030456803940448101080505800c580c84140c200c0018181007a02c40507482842a10341440046000e002c6007140b0441118101c03404148901d449541c1880040e0a101881c1d001965102003c82c011680741703d503500816602d45084002c1000b159140f03401c0c0c841040071070300b480c05a00a842440025400749088140750860340711082403e0030903440c2880c283e0415140100060700100c10401140c10104480f0b410400072503030f1078011101e5080c00301c00010440d13200076182202203403140811411032105805801d6202c40c0900c29a182c0300 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 537308965 1250 537307715 537307733
    0x51315090b0f1603060312030f0e030f2805070b0709090912121509090f021003020a0f09050d031d031005100b130308071a01030318050102061501030c0509040504 71
    0x148500d5420100c043c1c82400c41d010f4824003049070740c4030300e40c0751000c400b60400381c1c01042c04211420007141c5603900d200d030b10703e0144028543c844e0010b40060b11411890a4030300e00300031102001d010002d0184001e1542e503000070540391129400f010298440d41c89600854170200e10b5401541d440e0304050060b801c0003034484920108a40702d540e6140c028841001d18019079024000035907056141210510000b10a900014040750003111140d081a01d01d030f0204081d00c072407101c2000065030204c1d11515042d809801c0c08010519071a000400c00d040800250600c07003560001001c0c000055000385110755901d60300c07002120003e040c0c4203c0740fa8103c03c4806800100c03182d003e83d41c00b0050206080000005071540300c80c201340b0740210b107411a80c8622284d4004c582c00e440342c200b000140c41088503803209460203140310f541c4403a07120b4ac881c0022041844950400350564107c0f0040091030000d0382c83d400440002480c010607038040c0000181e400d44168201c254119040504010034071860103 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 537310215 1250 537308965 537308971
    0xe10050709150201051501030e1f06030c0f06051c0b060705162c07090e010312021c08131103010c021b0f010212250b0402030d03051315090b0f 63
    0x40444455024203100720300b00c45c401c650300b600c1419501058407941d44603600c004001c2c04090b040382e4245180c002482c50745990b0014680b0407580345c02090081058401d4130301c0040141c0003410395010704150005e051360080c4503195170204c21014650b00c110403160009003042c0d40280ca0b143d983c003501d0500c692100c418415101c0190f2201500041540310021004104410003690030b8807514007450300190301d2800340c0204100b00060702c0c0420b03070102e4448414020b5100307105541c2c010341c20010180c104142460150010112019200d1449801c003c00075440001c170703030405001d21004d00c3c0131014581d50303605040c0c0641c44c046003000c25a0b00000c480d183c0a00c2010040317804040701c404c001c89544400e2181d801600102e003415002803807180074200c0c03001e00c0c4240d07a10448000c0c541e41d10075226081d05890780080c060078401941002d01041d40f142c1e245140510044c80c02502e292034488072500000c1140480e403035441c1401c1c2d16030780401d515079842082108607003064030307c4508580f419 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 537311465 1250 537310215 537310229
    0x304230405090d02070506030903040801110a020c0306060f060307020f030a18050a121e050109030c1b030507140d0f11090c0304030806040203041109160e040603080306040e10050709 80
    0x4200442c0b101c01c40042c0c5511811425401441d01da400d2009000c0c03250000b4010000f00d01c010310000c2101e07102070180c5451082c0d0840d400d41c8401206400916103807040000d40c4c02900700c84144070300741e110f520081481c540c069820f03640e6511178020881c034089880f501007034107000200d5409103440c0c2c0502040d42e250360720001280c40c181c85404000c5440042d1045180710508a031000d40000d4010004001d40d4160b00702810085066886481c01d40f078512004500040e5210030010820903846002020000c003407a004403024150742e41c3c0340d601d0601d400b1341d50301410988a104000e64802070b40d500c9443c2d106031202980580740c908171000c24050401c280c4141c0c0140c0c001503109040200781c1e4401d54065945a919884100501c0001c4d403000d0b00549151045075038030406516107440c054001c09004005503600551400018560090750040740d10890411004002280701c40040e80d400c64812a0009110030706481418074082c10001003060036030600c81006403403a00010040220303550 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 537312715 1250 537311465 537311471
    0x140703110d09080310050303030906040f02270a29040e030706060902070605060306040b0106030b0d060207030e030f010b24130b09090a0209030a0b0703023a02071509020303042304 79
    0x1b42d4080680700d01040354080c4281e4005c1c00041c002c074007286200a42c10f800070300a0f4000c1d01c06440d0740200d000d480500c0703001e400b42100a010a0071414071807414507411810000410180e00062201c011603006140c504c180d0300c0d00c0d0740c00841c81040c4120307415a54041d60404c056640c40805002035000030b041a0380b41460480056074508001c1641c03440750f13901445d6200380740c0c02c1c424140d00406424040c9a040003040c0d4170302d000070706584020103009001e91141e807031840e03641080500e0601c0301403508680743d0501c0228500c0d030315050ba00700086013507a000b00c07003041c4091041c19054000c4030f10350070a500300350100040084180c4010b040c0d002064541c03140a540d825400010391050040e015016808840d64802207001c50910036040041403901525010710a80f110628071027210f03032100200c2440c0344000300c580500034001d040e1064a1825420034140307031615000b201ca03082540c14400c0d200c03200d0204658080c0201c03408bc01c070b14080100301c0c600b0821007800c5102c9200e130300d034000d0385 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 537313965 1250 537312715 537312719
    0xf0806060103020f04150212032e06020307060e030702031f150e010314011401060201060f0e0114010c0c15081801060b1602120a0803040302070603140703110d09080310 74
    0x102c6402121400306119604518141c50150102c5201c000d80040c142140240120b20418200410007103006401c07103441c500710650701c60365611081429400da851104c0c80f226003000310903004015a43c40f290005000039501001d41d00d642c0c02c40c4204400250f040c0038018842864020215511280500f80241084101144a000301108416020700861401d60100410024003108010b0452110b041d00206118400011885003c0c40a0f0005030140c2d444800500c0035a0388110080e0003000100900100382d45000c003841062002c0140460401241504903001d2040c01c08070340b802010a4400c8103030a8100a8000b0030b00d103810350700d8841d030300300c41007603a244c014050182030151034140008514160b00e14010448201d510001280c01481e01519070010000a00c8001d4400340100c820356941d1506103402810301169800c4ac50a0500e400040e49500300e00c00c0c25903070f0201c03880c20000303407110741611884018010200d82c151104d080240e883d0402c61103a000e03502800541405150080e = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 537315215 1250 537313965 537313967
    0x30e07030b100605030c04051e0405010905070f0206060604121b030510110c0c0126090a06050c070c1503091b0303090b0705030919180e060a050402180a060f0f08060601 74
    0x884241c5800c01854030910082c0072368505091400c4070101414003501100f8006000300b02074501c00d0f88880b14050fa41c0c1c04220712035400000a40140200d4400b414203413501e080000c0c00c2c1d004a02403907a0000703841d143c0350304021304040002d0300c035006854015404e65403868101d59a40208107003040907400c000080b00c0720046141954504148040074103008500c1d2401150b000050b40072513121000c1400d00e45013542c3c001c00300e65018030b1664000e0716588009003000025650b0203402c80c459004200311040100300064083e4098542508482c0b40045854504401521007101c015250080028841ca4001c45450000c000c0b60300c261a40d441d556500c020044250144220223449038004000101d0649404081c140a100d079081c12151800c0e100d43e60081b641c0c8082c2c540140082d601c15600c90b51101c20000281c2c1f2404000b0244690300d8940c5c0459980b180c0c280d10382030b42c00c104602040c010f01c420307003002000c2d0031880401480c80f5a0b03800b564105d41402d10641c40039000b080e000c03514039 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 537316465 1250 537315215 537315217
    0x1305010801230a05150d03090305190b040305090d020418030e0a08121b030408070e09010b06040311131b12020309070510020307230d0e01120b01030e07030b100605 72
    0x5141d4040382d805965865550001c064880200154400140c0503880e581c01d5450700d42c0c060500c0d0180c1d80b5001c00d1820761a14a00d840b05008414440c021800103d800040c42c10308101ea12a91603e4100e0b10783e041c1001050026041200084d88541020000b01c4240350500d4501c00b000d0007940c2d110000700d591028003801021500034410660405009074080740d188200420000344600d02e88210040302d01e003294210b401c960444042c5800c040c81c20041101013022954000b52464000c11168000e030000600a204603c002002c3c003428040520031030b5100805410380f803880c0035003070000040e0003a41c194885046030300b581c04224481e5050810000070720940e81f298004800a0000c20304000801c648080348000b01ea0441c130007000000e00041c280741c032100402c1562407560000c2a8100069401c00707040a40e140101700400400300501d03039114000b540e9a03d682c42000074610186401200604035680e0982d1321031180b440000100041010030358810320280395100c2d584d50719101c0441d11 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 537317715 1250 537316465 537316511
    0xb04030f0c050a0e04050d0e010f0e0d0803090601060f0e090402040c120c0302031e011d04020d14061603020c0703020f030a0b042a0f06050a0306150e030d05070c1806051305010801 79
    0x520300780b12062541d0042f210313041e03000401003c502d0203084c1d5680340101940103c40c000c2a642103000104096500100011121801c0341080c0c0103032158000482c0f00104000c001070b02c1940c0340c107898036010303000360b00314030860b401141c003030007400c00c5650302a01950003550803807000c690407400e4410f400c040b000d90905a6070207203001d009400200c0310008075190080c10a80e400768a00c40c810000a1201d05440024a441805400c0500d001559086400011079542061500420080602100104180c420f8030750440382c3c40c00290741d10b404a840c08038058002028000300e0b50500c42030018000030150200c03081c42e02d44052a80b800f500a044107444d102e11807014450b0762090000d135002354043d00e0920843c0c50005041c2e90707900309515541d5000d5401502083c0041103505103424140190394001490b42032962600c002a51883c00040311480380e80210b0b140c5501001c484002d580101e40206001440c41807130185050029009000070700c00d00d02551320340301240d8500d82c000081200 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 537318965 1250 537317715 537317717
    0x706050903060a02070203011503030c1505070e0d030201020904020f22030203030f0d0b100c060e03270f1504080114060d08130b040f030b010f0b04030f0c050a0e04050d0e01 76
    0x741c2c540b508104078000c1e4100c0042260b140d500c40c01100c1544121000000065009584000845141e4180102c04240d20080210340e03d0401041241d2541c1204c03840d40c2d06034040d50108800030803410105d00900400141c0d9512a00018480000d452014041c14000d0071804604c81f050004029200b070351030130f0f484025016002031000c0c8400f102c411002e403080c00300401e0081a01805080082c90050682400300041942e9034002c00500449119816011221000451502d10341403000713621500c0c8008070100c524015034015415172a425030b440200100688088408450170300c0c001001d4116001c0d02c81d0700e40c80c0103104070202956400326401441c0140c54101c400840ea16400490f50040202240510300da50340002c0850b039590082c0300400305042040085400e500e0305c03401000c0181d004490641c0d882d41c013840718841c1c400460742283e50208402032070f2101c174649a1422100740d0712069124000d0440010740c244140709441c465445103007943d00c0f425150505488980301120018 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 537320215 1250 537318965 537318973
    0xf1a0307030b19020d020703020c03060906060d050111030c09130209010c230a0615090b0303030c070515011d06030109031d03010f1d070503070b0d27030c02030706050903 75
    0x400eaa030700b00d850300b1500c41111800c1d0001c01d40481c4050340d010003107603488207500103149401d259060002c041c00740c4045002d45010304090078907568802d405081039100309030418181040000c01d500851600007400c0e00da503200e20304401803503001d40021800c140501c2604407044c0c4820014400c69601800503110100d005032035407919001c860303a01c0029082c2d900b80210004a0300010003201034020710692020031000e0040d500c41052822603404100501d00341078881e1501c0e0350102c141c83e8407405103080d40ea21000035051482c0b6080108614002958200c00003060440004903a00d82c0041400101d000545591050608844617100094002012640b542c07000c0f1000c0c041d0000076910040010940321140314500040b03511480c2d0781c83e80440c0350103a9100d45001030010800800013100038020851400c04202c00510850750f041c6846582e0307500c4140032040c1a044d0462490104000cc030a403902d030325001d0200103000700c09038800d2240ea0b000044c000d03c54011658641c82c080d0241c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 537321465 1250 537320215 537320219
    0x1c0e0607050706140d0e010c1e080408030604060317040302011805031c0210020a0c02101106040f020a0e0103031205010b0a020712050316051f0c080402010f0e030601090f1a0307 78
    0x101c6400080e100c0f4604c4002d000c00c500440142540240d980600c0d1310380c00000c46a9900a02800c1036905820603003151140c0c00032805450b400c4100c0d20790007500107a240b590b80c2e407083c0004005041ca0340006208102003590031061344026000341050ba8030070388070b805054002e4041007909460f907128056065021810700b0102070340c9000209041003a9004842042c2403d600c3e100907a0055021040054040e2071002c00b0351510950024070049507060010030400d40d141d99a8841c80018405001e44660103600811501c1e4040c05c00c1c0207082c0303001884190b584903e0000d21211440000352160341c2000c00100d4070b40c0480084070340280c49a00107118240c81c200c40c6495445002400b81c0b5540028005884408030b458114010140314001a194488034080300764a010100410340c5411464211103039429508600c5854000360242844000064010780864404407071a40c00d0790140154400000c2030500394200c412244503929050184c00c10310001e1000c03a5000040e1541d05a002c4441 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 537322715 1250 537321465 537321467
    0x406020904110408060f0f060d0311120a2d110a0f0609030e0906060d1d011107030f030605180a2408010617060f07050d020a05030f0109051006030509010902031c0e0607050706 77
    0x10000409100b0b0404241221890100500740080c0701f0100c00c0c0c1140008048885550103b040d030503030b0050600c03666068030810750100c01c05c25940c0d10401070007007075080300d0b4201c50108040001076501091103141c802941c034103040135091041003240400d103c48602841c900e03003a9410341c0302c0d41c000f401d80340c20b00d01303002c1840010300218100c1600440341c070500860740d001c0a000311441041524840344d658001441d0042020107400b070342c0e404040c68801c0600c41075407010aa10178206051840700c00e03a8440712181c0c802000310003032201c2940c4131540d0038207d0900b02c04240c001c4a0700780c0d000b0440f00f0740e1003d010a401c030038060991080d421450010300028001000b440c1c110030ba901e8003900704540300700004100da01240e075400200340007208000c08101d205040724098900e60100744443d0802d88100295100280181420f040c1c8032800203007000002d45c003045035207400400f1561154001d21605070070a80d01307601c180000301d00110052a0342001e00c1190002540300c001426121703d4144 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 537323965 1250 537322715 537322729
    0x60306170a1112070b09010908150406090303061d0405070f270e0f07230f01030b041808030a050108061303180e0106020102030f160c03080406020904110408060f0f06 73
    0x8401540032142a11680100f18104800710182075055a00c0c1e07600d207a10400034040504680c401180303070303110020759207403480c02004658215600842c045180703c2146001c0d005040a500401c0081d1100003840008419101c02540654090416207803225150300300d0603198101809070324102080b551100400c410400030107404038005842c00202025100103d50070900b00c0f0200f00c200d0b900c500c00901074201c1010a1584465003014080000d440c0702003c664000380d034950850505a541c07200a1131034940703412100a803035080403e80c42e076000c0b900d0300d030300a9001559001c2596142000100e402003000034198010f0503030384e40d040d00c00d0403281d5003102c080828940e00c4082c140c00400c0040c19088000d011800303410943c0000d0303144e20300001001c1d0b60503001004200d4610101801c984240d40014032070261940624081c201a07669040c44400380c4516004950080d290514949001040300701030300580d81c000b411b4404e162240ca02d80c17100304030165500b420380c55031203010500500d0405 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 537325215 1250 537323965 537323993
    0x30c01230f0406020a03121a2709070905100303140f0409020304030903050115050105030a0b0a031b06080a0603050606010305091528050915070c0602040303020304060306170a 77
    0x84800e628000c0681480545604503522810141e4410000b5100700360300f242c5404900003460703404020b150b014521003804019030310540742c000d558a6908251103035001640403941c00c1c030b00d42c01c1e041c68180442410703600ca03817038840e50030400c2c85e220200f030800c44006034090481e1b8059440d0544401d4214900c410b40d440b040081c003401c2020000000c0040050001c1c1d44a2400382d1a40c0120610f5400c01a081d0340010303155020305425401c0500c01a80c0100583c5d40162000000003101d10030480425444581900003502c581c41260303580d0105c0c89803011520507140180d5407000d6a84503080f0400596000e404000c2064000c0d00c0068003d500c01c1d0b0185600030802821070301c0d00501c1c080b84028241081e592540300c6010b252a08440c15000d99860f488061500c6c0c0c10041d0340341a24185440300ca00000c050b038000c80420114801c1e41c4203e90805005400800855031140d485c94080d41e25801407203201c012030709210700010041c010154900f08051103501800894941d541d03070780d20850080c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 537326465 1250 537325215 537325277
    0x20c0f07060906051930050a05090309090f070201110423030d050a03050a02090915010e01051809060d150608061005130b06040803040e1807061d0409060509031305030c01 75
    0x24903603503115030181c240c200f40424030110000900e8101007188c0070680300c0013020240035a00030442c011440d06d41030035081d40700c031014114196503140d1182c02c83c054100c111940c0c3d61903401040200321905800722007a0060100c1101403100000c900a040c0c6800d058080000441d200344564401c0c03038002d420159100c422400010715001c24800012006107095a50000040c005000780c401941c000e900704400c05000d003041c500306486058402c03203a1180244082c01101e030a004650b4548550101406c03442c0c6c49115400541e07095920766000700200d2090710824440d0030049160404072491410079a1070107030140319100c0c0e000a0240240220302d815a0300300d0001c100c001a84034007840a00003400d110f0000d1282420312001c0c035050710705044540c40d0180c124813020803685810003c8222241021421441e5100051001030001c08074140f010381014182400c00c058810044002c14402e0000d81101c9051929401850750b2800a12441804228507190b02031107403070082020f00c802c2d800d03 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 537327715 1250 537326465 537326507
    0x1803090e071202070809101427030f210702061213060c020109020f0402040f0510020a050a030924051803010207050f0309091b0a030c0201020c0f070609060519 70
    0x10b400391403049a200d990241c0d20318002140320300080c82c03c10b1241d07204007030610b8013042c82e0a400403010414403e0310341050599802605190b08a103200c50050350036803008013a44c02084801c2241901c407220071b8184143c1c078041e0954040d0b1810035800b510003858000c0e1641e03042601e020f000740d11035000640822051100d0f0482c4000040c081d004031403001c807850380041104102403051014484032940000d11480c0144410b011080c4010521812120203c4100046003000e15040e802d0288004d0f001d04103015521004080c16007020740181150518400c10119000b42e805a108000d1650b076150700186c010007c0e10b00c00009004411351041c00100014904021035523014502500f111035056035400c08103001c00e4524080804a600480440e03a807000f100769030b03091240c00d104034410141030503038a001224506100b5819141506400c0080300c14107142d0280943c2d403605203103e188006208850045007051051090b81d4001c01c566086500032008518140c414286004c0c1d10240021 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 537328965 1250 537327715 537327737
    0x20d0c0201050a1b08043b27060103020f01020610031119080c030f190b040609020d0c03021903020d1101140409020405030712021309050313030302101803090e07 71
    0x150300e01580340344c441c0c0e178456a21803803d645c4c1c041035640c6500c814000210300500c1c0034401350122000f812500c29070f00c0070400b540c486540e05800d401000b0101550a8412140131140c1000601d03181a64000c0301c4003401144800012031340c41500725030710240050020302c01c000040c140007821031100c01c0140030070750890244005500c042916880305c427103580900115186810148078003120f07071000c00003a0080c040e007512000d505c0100048001d1032003c00400090900040340d100c08086903004242c0803e43c94141003480301007a003400180d10900e4448202c1c0b010304044800c1d0001c581e40070307102c1102001346e42c45a001711048550000e0610030744011070b00070000804001c02c090110090016129030803c400c1c0741c074150b0303150002e100d6101044000f00246c0d4950280310046488410081802005460301e01e065004490f01003101d5500c4c032101200701034011407808004500e50504022080c800d40380954420500d070005008240c580c0d00c00c1c0702c046010762240358070540c03508014003c40 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 537330215 1250 537328965 537328997
    0x40b0112020a030203040c060806030319120e010207020108071e0e06090405090f070605031b09012706030b1c020108100f061205180d23040b0c0d020d0c0201050a 71
    0x1900255500b000240d000042004001e800032200000d008a882c00c120145000c8021a54a200b4148500e070000ca4034030260580b2445034000861040150b0018801c41d4a40784c07040b4081d4104440c1207000c01d05040c0050f01040c42181000f610b1401c402003501a4845020181c40300e01e139040f9503070f8011307000700600a56500c403405082c0c0105502c000070031140034000041407d080e950380042040140030401c0c4080085440101046c404a42c014140c3d603c0826006840003117441840031055510000219107901003104840121801a10300340700268413601005880080b60038010b50000d160b410620140d40304a14246e44041408900b42c4c0907900c81002d01c0c10a88141c1c040d10004580d00c0310840b2560180c09520342010380c80145603403a03010000352a40300d03210100d40030708000b11003080100710107003140d040d5054030704407810344c0c1c0e15030329040003400c2c40d40000c45241c2e1903c00d2001d030400141c800280e40180d06029504c0b00d00340269603004503450307806820f81310208000d08170104808 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 537331465 1250 537330215 537330217
    0xc01030b060904140402130902210a060f020a140f0712090e0f07110d09050906150301150f08280912080a050106030c080606130e040606090609050c09040b011202 71
    0x80c03004d41520441c41e0a104002c02c0d041941c00f030340310582c24101c50400580701d23840505c01d030303841c29a070600c4807804120400346001034106000d0b15050601180c0b070322001c0140e00401c4008003559412102c13009004130850316101c0e2800c00f145003002001610041585109a800030449038509400e08030340d101906c400c218400d8074a28000740414040c4001a03401c650034500380900328015284801c0d04203005010795903a407003060701425000c0000b400c141e4a9061450703110101c1c21038241c0341d507141c0d5281106c00382c02c40190408035108010003c5414005c086141c800d0a1008898484c41c041d4010740e804200407078068582140c841362090009198402030103001e8a0f182c0e508441482c3c9162690181d85060380003005251400d16020f40050b44032010660240040d1f40c0555620a1581400c00c0070b0b1050340a4400e0f8201e0300203110800c10f0a800800c111050030b0b4041c490580ca48000030304880d005d480310901d2039010401551541059004404901300c1418101c00502845541a003a = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 537332715 1250 537331465 537331481
    0x30c0c03040e150a14090408090604060306050f090f0c070f0807080304061d03180a050406170609030f0706091b0611010e0c150d060f06030912020d020c01030b060904 73
    0x1c4009200400c000c004043c1e01c5000040b404842254200303151074600d640e1048604007141c094100680001c09120000007100e0b52010040c00840c0e9413566040e0050041c00302d805421320032a6415900105442c00440a60042c1e0741c1056200507074440800c11440c3d50b101e0303101126406004020000816560700281500d03d0007503000942d00d10382482c054040b205050300741c542000401c62044440034000050f106000080c19158082c031407c20006251451a03501440d40030f41010301c00300721000c454400d65841c0002004982440c0c603040740c09a1640102100325614000c14420030b00443d11035081400c2080c003c00c949403072401811700c030030080703840f0f6007041010444d600d00c0704605001c24030402c0b4200014901404c0003070303a00400a82040070742450b04605610100c1c83c1e001c82441c581c855001412002e108800703082e580d2174040d001d40700440b010b0b05c81c01d4044611264a5001055600310a44a03501500700b0869440065004040c402d0304c0981020061000881e5074a40b4826048 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 537333965 1250 537332715 537332729
    0x30c0905161103090d060207150e19260c010e0606030d110c01050906040e1e011403150a06050306040f060c02031608160206031305070b0703090902030c0c0304 70
    0xe800e1500c160860100345101038820100010004009840e41c0301206844031840d04a4038031749118540d06000d0041e002e42d080281900410151500e1842e0096020b050004620800d0b02c0b142c1d06409103c0271050019080900400781c0b02c040300e584c1c4062403a0000c404100d46203890b0601640c240f010f401c40e09506070a007200c1d8410000d0080301d207010410008407001610304082ca401d052424180c9030801041c0d00350503c1408508041c403581e403041580c001d468649083c603c40d1800290420200840b00d050b184205d00f100000318900c00c0040c3c80003036041c1e004e0003c11140b040c0581d01907659100400c00c60225680b040041781036901801018002c40c001d840c42c55100c5401c0c10244221881c5c1c2c1c000c2000e56008102410f111400b8030880d10096400c00001d9031a11500a04115034951900c4000d41c4410f0000c00c20450000c08001e405142780284120b4030040e40300c00150500e8441d0800c06030110b034225008008110554004590241007005100d04004030941000d1841d002604505 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 537335215 1250 537333965 537333971
    0x409020a031d0d020f1204050603040602041802070b0c041d0a290a0807060c030c03120c0c062909040f051905100b060910090e09070e0a09021810030c09 67
    0x302c040c0d810002c17540240e00310b501510840075014145240c0d403241d4070880c0d0081c034000c0005001c0c85590350550f00108010881100d40e00b12000d00c48000b94001901228440100000300d50240c0301e61090b2015101e250300c3c1d84c00d801e54a1380d205c1e4109000142001441a00c2c5c2c8204991000106140d505a0b00c01c100f860700800c1c002c404004078018286c100103107507401000100141ca03404043c10042640608010200711803d090441c1c41c080d24691a54040f8140704d042d00503960b0000100400f43d00a400c00c00c280e000c0b80365003a50034985001681d42003200c065009820b8607140e503556800c24410650442c0c1c503551a65010b0500350740311102c5000c0708160b20b903041481024880e01070a00701d030240800c03140c00e0031340001d130107402002041805154007424201a40e405585084091b202c0c840c844101460300304811b980d00c0190f80101c441250617507000c1215401c450280106a0303038010900403448602581c2c9274000300c0d0040506038402c4410000101040b81260854040d018145002c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 537336465 1250 537335215 537335233
    0xf1b030609050f04050c060a0512160f021614030c1809071a040b0d0b04060f0626010506070305160809120303060d1401110414030105070c080409020a031d 68
    0x40412208014040c610b0038244204000005401045101284101f140e030300d40c40b00c101050443d054020b107400140c040090b0f1051104000b01c601704407000b50000d60740c40155680e203400491300c40380c00e05c44904482084140a200c40690320b480740c40030100103000c4030001c40102001030002003404410400c0680c220b030512646983c144919030150240b248018602401280c41ca9401d00c0b5038895140340142c0030800c500c80300c00a0308000306540300204240612500c5103283d2017101d50a12034900468010045500303a080e034040c3d41824914000746001c00d40c0c0c41d107014008207070300091080707081100801141ca105299400b44075201c3d8040c0165640b200c0071501840b150700700c54074112150f5030040c02000400e9440510281d07520364407100e034107012828841202d02408030300100204040c3c02040104003164907030010600207070210028003482e15455800da41d6100b901c50050f041410800081c00800000d400410840030f032440d0000e41200340b01da880b424510040c0c1d9190321b03a0820806 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 537337715 1250 537336465 537336479
    0x70b030402150403110f0d020301090b06190b0318010605060f07050706140307030e01110706020c0d090825210b06090702030d11190207151805040f1b0306 68
    0x801c101d852030b04214545800d40e103444907142c1c0802c002c1c0344035002d881c071280c280303403610500c5020b02c81c1d02074001d010421241ca043d41a000003190030b14000e61108001400000d039140c60801241e1154513000d1071900c3c0c0c2701980720403011021100203207640f1140c0000d13950b101c440092a172510001c824546560300c030f103070640c00c0c6a25644403108110408904141d0300305074004890700031550307041c0003804548052445014040e80c58030a0085070000c0b07528418080b0755002801d00020a2066030100103009600f070b6001c502500134201540d20018502005c1e602c0c0101c0b441c1c4142c440011400c94540d0340000212400021031003040f03862940481d0700400c10302d00c4095800242c2212445050300e8602002552030140c440720800d01a22144000c076086414012102034002090496030f0803081c000d4007039a03941051042e4642e14640414000c001392142d0038401c0510818004903608500e0101088050500306007429941592004040c003005402e810a400580650714003181d11032410752 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 537338965 1250 537337715 537337729
    0x70503070e01020304030c05091905010611060f090a030c110d290601080a18170301170309150a021614010e01080405100908070c09050114010c260c070b030402 70
    0x4100c2c15548107100520005041c08010401e48100307841c2010141d9403904001c3da43c07801d10482e201501d14190000c01c0081d03010000c54288013200c0101e5801c1c0d2200524400c51320360840e02140302e904000381e4000000d100320b10a0926a001c1c032a03d103c0b180c00840080c2622400c0c103000c8519403014440c00c1c00740619008202d07030004c0a42d0b82d0b661545010b0f80060100b603402022401903559603100d01902116110801080c603801c4210070f0b00031100040e040621f64030030300036001d01d08002c81300c0380740510001045449040001d0240540b224802c00c50181980110f4040d0301540240c007415554015008400e400600440142c007030000650000504010040e800a80c1007203010703001c000108000007a10b28a40101400000e00c0c0511803c04901502904100500c10f80540c0000034103804140c04c21416904200d0920705c2807502c61005551107c4109802000c0412400114150044514200c004050309442c128a00b401442c0c445042c45900c1e007159030002004010700c000d5081141c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 537340215 1250 537338965 537338987
    0x703090f1d0108031903021e2109060112030e0a0503030c010f0c11280209090601180b09040209101d0a0b010908070909030e100509090c04051e150307050307 69
    0x102071803600081c0780800c0341103158845d810f02816000100544d00c009060013203448607051058203601c921414668100092508254803d00d074130100100365401d0010030118100e03210f40305140500e0080360b4040e1041041082c2070360703015041080010711134800b400102840380d0003800005100c883d00c40e00c5002c440d484d480d60b408001c45807041c036248030700005011500c4800b14844c00c0c07400e031080c580c50038425060031000350081d00d54010302039207440c0046c43d0b42c16075280c8502200001078a00750401201c081c07801550707100c1034900c04507001d13061502100c3e80261109c0c2e200c14075983c48a104014105c5d0b41c0040301e03514140da40402140c10340b5481524850b202c03d10b421510203140820703c80d0740307040714020140020b0307803450700000305401746680d00c070104030242040c1d4901d8800c1601400340d410020307000d4051415000080ca140c02000111810f80b140209555082c0c6440c004400ca10719051100d00d4000c005903902040308402c0801540c0f141d510f90380d0701507403071030308900c010000326800c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 537341465 1250 537340215 537340229
    0x50606040c02010c0207090f0605060f070b0c0a0c1b03061107061407050714010b03160e0601030506060406110f0102191403010e0a05090a120e041d070603020703090f1d01 75
    0x1108240c0310b1940414210304540303a8102c0032034a104404232903070082c10f09a0015500c1400000d0ba0b002d8101800040d0410601405883c006541d40d0060403041d480744403800000140e84030300080010b642e40250f45140070020b005404055200e94031703802101d130354020705064500c2c007103070ba90100301a070701403200140e50315450000c59081110000d04a4002d10ba0010040200c042c1c2d0105055025071040314514002811660f140c0d0050b12102c0800046004240d8000115800500d855009000725070140201608403442c00c0e1038944100d0f051011404001c450f400f0315080c80800c41e07000d0001d410f00e00b09075002c801c014811001c0243c808042e4000c0c880c1c8030305c81130004021400c001e2180d00c0e40f20545a01c0498580c5d0364002003403c0032039a400091444200c05178001d60b40791b201ca050408124159420451a0444a002007084518030204034180c1e10116062000e54482e17009003001d81c2c480d04064156944a1480b443c410055410851200c0c681c1e0010000800c0c0c0340070b5440c010824 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 537342715 1250 537341465 537341471
    0xc0c030102040320031227240d1e0b0a170a020108070c02040c0306080c2e0903150f0c0503040317071101020a021c0305010617060a0b07050606040c0201 67
    0xc1c41c1d58200240300c0064450785012000c0b000610b40361824401c011030f442c046e82c0038541d00c0c441000d003031021044024030014906203840c100f050b541400301351241e15151254203400440380401c882c14817544030707420050b1f803070352902d15095a0300c1c41088010414425100085044d0440d0028000502e9450f4803104030161320703000c40002c2143c08180540c0b4580c080c83d00d4801641c8249003559041c030b0701d120094100e8580b80b107a40304c0b80d9042d0300410954103200b066444020b2a03d04001810001e1400c0c041580301d1a500c0320316000520f4112000310901c0d007050020142d407502e0340e01d064400742c022507580e5911507a5406408045210b88400c14115060281c20b40c2417507180146405d451201160b81510b00a0204400c0340c02010110303103400c80b401c000c2d9900c4030800f2000b52184c080c125448154a022240708850b83d00034002c1da41a00c5840ea61201012b9211054080040f005070900c1e820005814000c80c080c00308200900d0468042c20007031802e4205030080c40100c8150b00b61402c11645 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 537343965 1250 537342715 537342719
    0x702090610050708131d0a0b060f0d180804031203051b0906070510050112020109050607171c0c080601110d090915051f090603020a0807140d0c050c0c03010204 70
    0x1c0c10206443c5884d401c0700034261224003010164030041d0040c0c0283c070140d1880c111541820840d02d40c124807130b100850f030900c801ea0000702031141ca80100c0c0041400c600c018411140b99071100d90100d10503264940c5407002c40c43c600d448101995106030400e0b20940302e100003102d0440d03014090703e900405149a2450100448104440346004541c2c909100d0100041c10313005012080007003c030110803810b0204082c1d40d44860b04060041c3d1032504071b010485110000070391340303020010740300d03125000004100c0610f4265000d2030f2a0341300c20b010311800c1c1d07c0340c1c16a044000291180d4004d08a040e21204410706020340090444404c0351307811403103030f44006e0040700020fa10100d17003400c840e209007000c0368cc850341e4115403500c00e640382c000c0313500900344501c00c5c1d411150042c03914914140940301c1c049006e80392142181a0710602500401140c509000700708214410b130020050035042c0245141444000001007094035901444000042c2c8007148842c04810248080d40707001504a00841ca818 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 537345215 1250 537343965 537343967
    0x10b04080a0b1306140907060e03030a080403020723040501090e0a081e0313060b09091b01050408010e012405010c1704050d0807050c0901031e050c030706050702090610 74
    0x90301c100030040c0426030040b480307001091041844259000d482030007404202c1d482d408003102c0c103c80c1000540b190000016030140a0b00f24198001c0000d400345280103500041070f05c00720b1000e08120110701c691440020524141c0314410480070310286161040b040e2102000103075801038000700ca2252421010307100300003000425449550780000303d5515114141d03201c3c4003c8030080c4001e414480300008001c49034442ca803486000c00c0c4614010001102c0450602601502c01ca94180c0254054080c4100d601c012040c1450b00307410501d0314601d400d0f00c960b01642511070003644040b20382e44075465800c4070f0101a0040d03a040e000414425603680c50100001c248211000c0003600410f03081c11900d40002012040b503001d4070002d803504d8014203841c9401c1e1625400308074280d402c3e0040c06510203042c60120885c40c101c0340c1126625240c0c18108191410348070032890115194800e644080541d42c40a000c0c420040050741c40b100c0c1c55201a0042c80052b00c07008152a120327903282540b0703c04035 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 537346465 1250 537345215 537345223
    0x801031703070c030f051b06090105130206030a020f0d02041520030a030203061f0c0c0801050112030f030b102304080706050c010906090b0a0e0601030519030e1008070206010b0408 79
    0x800d03050b19155510303d66000065401f4803400030b1180c1c0c22400e203a074400fa224000144503005184020003000103545a42d035400d41c41d10f6039200294000d03810004100e03a406d0b40e030003401944980d258260300d000b01c1509488202c0c1c0c03040c0c0c4220400d80c041c0040c1900e9513040f00c0300500d40d5614048420780381d20803081d00fa84a104d1100440181640400858400e07241d03e01c008201c41e21442041401c0d4a070305401502c0302110444c03c035520800c2ca04003144004c01070160904940190203200301561442d9010344034030420036005000c05a807110399000f60756950110307505440c1b03581c50b03580740c120340000748400c0c0031580342401004400030441008842800507040e41254228509591114204444103000d0443c002000d041941052050803c1c45541c401981c00342d10284010010812103500785030302c402c82480301500a8005c1c10101c210480b40c10f10048055110740740405008106500040041540000d40d500245204042211a81d01042000e001d003503040a1a03003007a1a040801da0341e = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 537347715 1250 537346465 537346487
    0x5040b0720041e1508030c03190e010f050706090c14010e1f0e060415080a0c03180803060402090405010801051006080114061c090f0204060902040b092b03080103170307 74
    0x10381c2e643c0b010f07201e11404060404c07001800e4680d059a40c0d0304012003665a0300c2c2c00000314000f0f0507030410401500750f4021083c100045c0d0044c0c507078040c0b844444000741e4a94100b50005c1d07403030756114400c00c030000303890452041c040e08080c40500501807409000514110243c2d02c1075000e14201d03100390b0704220405081c1402000285000c0d030144040c000424024000d96000c004001c040d419188a07403504104910302c1107200c0c0e01c0401480c107060350100c040e6140303504510491035a61455501240028004503403144002d0000b51074080604085400c0f60026800760790541d55a50030310000c945551a1000200614909103100d9410480a41c140601184c205841000005182c4010866605d9401d51242041408008015445c18000000707240030604a1144d85032103000304190602d40700355800d45090b590400c1c20010844144034550420703500c00501041402e5994900c148940e01d0b4003a007501c2030791060400d500d0b602e081c0345006d01310b0481140c500d0041c020404007607400b4000041c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 537348965 1250 537347715 537347771
    0x12d03080304050a050a03024e0c070602100b0402031e04150606020d030c021b0111030702060f04030b0a1107031808060a151a1905040b072004 63
    0x741d69215840c0080c81c02c58003c01c0141140100445c0000781034001c01c0c80301705010103040c41c8080c0d551220b58100d0441c0788002000e1600fa5140b0580107140c440b02010b07641c006490502c625118403506298909080307a8070200050f8041d00a40041c3c1000d0300921200c2d01c3d081d103040d401d40c1007034081d00b558000074000c100250700341c52002900340580d10f41c0340381040380d65401c04c02c8100d44840b030081d101c004000c7d40001081c00c21a5801c0000e2000441048174103801140020300d08100b001100d41802d189143ea8251209100000c0540d841c0030040020881030b03800a81c2c0d840c59031a001c40e10340f800030465a500c81c50301c80d85201e00000c1d4802c0f20303851035140c5405010210104020740300b001140d008082e0a00c180420070003419110351200303c001c1c00e1015201082030762480f0b031a10110920b40185220f80081c0186100f18410507002c80c55104c5906199041c1030300c2e400640400e40140d40240d440e40340e5501949a04105145501c40e041c406441c10f000d42d5080884c2100c4125007400140 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 537350215 1250 537348965 537348967
    0x1b0609010c0c090c050405090603061506090a0e09060718061d04021201060503060a1212031e020d06050f03010504260405041d0d110a0b0c0d0c0206012d0308 69
    0x1c0e0811034256094005810021000c0151840b440070040c1030390054015140030380d00540210704103180c0017a18611035540c1380c010000c810039100c04d024568019205d6690400000d50002c14942c81c03898003140310700801c0c002004241340415006000c60f01d0750421035108182c0715000d1204941c0880c402d90700707c04d200313012101480c11401040081c465212a000741c403101c40c0001c10a45d502000550090504883d40742e000d98588004000c07a00b510b1000411654140700400451070103504031801d16401d0303480c0c01207450814044402030380e01049401d05020794800040c00940b40c007000701d00c0305a105600030441803805036a110581a07a44114a020a102154004815400300700726006024082c0060003c403088101c07103040d4150031006556540100c00d01100000d201e408141116a19000104500b0450b919005201171001d8440c402c58201042614000e9205e402004460350443c1d00034216580b40c8030102c801204900c0c0c02d1026521215a4012540305014003c8246e980244202d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 537351465 1250 537350215 537350237
    0x3031d0402032a36030a050a15020918090c100e0301060906060c0609061e05060f030606030d030203060d0c060507050c01020c01090302091e0c0a030e06060901090507020a080c010c021b060901 84
    0x413528000c440d0319030b0754540704024000003044404103022000d01d00c01d0001004e41c6061141c0d980c164014001516044035000c100760794054650702c256a0000703da2420b44e802044000c001c90f410320504000b210102d00000d03002061424240b20b284024054000c04000807418107600405541030164094007a035141c48038402406000d901405014508940300059564050320480103040c00f00d855502c500d0301c140608120b410086042449040000d01800a2680d81d0340140e00940000d070007d130f00280c004448000082e019036601c1c0141405032201d070b0303c03403403646000d500c0c1121000039141150000306505219036009031603c1305895044841c8802c960320603001d110380402100051107209140b606020401d0340100040102c1e0482b95020b108140c01400010b54031380c030558159401c84a01401084024419840f21b5008880f92069038520034a680f134102480e04840720300aa030365074800451344565010810b4488030f1403070030100440030000100203003490158640c6641808240500 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 537352715 1250 537351465 537351547
    0x9081908040c063608010e0c150706090f110306060d1e03030b040c05190207032111010e0606030f07030b0c0c0f0307061a01030207050703031d0402032a 67
    0x10b5100c540506412680e40c0c80c40010180c000c00e04c2c540324009080d442c0540d170940319140030a1030300c848040038190909041400441c04242d600600c0f06480c01955400132200050040c034141600a00070092400051202c2c01014144a005070100c0e120308108040c002c000762140003038041b01041070701218102c40d000d080540180c521141500d030300c54a44914100d19680200181030010040b01552121184450f0184d0381c1c0c172200d0002902c200c00814115401545c50750341d455040d20079280035117200c100754040b2402d444018080d814035800c084204591800e041082c840c0409500005141088c41c0d5114080303074000141000b03400c3e1500041400c100b500c02c0240b0200d100540040320703580c3c94142484002030980043c10a403c01e49a80c1c07130421907201e4020781d00d005800c0300140c40520b282d40e405170791803502c42528200054003142e11003015611407000e0f6104e1800e00b0702000802d150700c080038510000c3c0c096980c2008900713000d905580100366404092404a0a841c0034011444402d = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 537353965 1250 537352715 537352757
    0xa0206090f04090f1a0f060f0112020706060524090603090c0904030c060b06070201051602040b060c100605011e0f020a08180f0a0b0909130609081908040c06 69
    0x940980c0280c1001000380c01c2042c80d082e024501c50241501030720049111790800110401600c2c44010000f104021412900d0314a2140341000070504124440301c461713940da4020b036080100207403002540c0710010440703070500d0726006804800c04805410a800320840d01c803442c7c0210311109000341004400251946801c004000c906100101201c045103460f01c0c0c020554101250100c501600346000ca100c40c0c201b40701943e0f80300d58141c41d20f0381002e0700308209072030f8243c00d040700f660300580703500d41440d10303072240d5004110440345070b00600f0b110007070665060180d030101c0d401342d41006032007032030b00814040003046168041c05c10700e00941c0100c4040070880c0f80402c07950f0042c1091400140b003803030100304000c0c000300440e4207842c016101042202000401d0701e17075101e601c240c01c40c01c02c00035a003441c0a41115501a181d001d010b0b441ca4581d03214501100c101e114221781c0b80b80300060314001040041612003c1444902e41410a07141c17503a02e0802c0d000071445050140300c0801458484111464 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 537355215 1250 537353965 537353989
    0xe0105131814010e0403180302010c021e060313030801080a11060309010204031e021014030711010207050f0c0a090b0307030b070c050d0e010e03010204031e1401021305210a020609 79
    0x22421050703503181c000303402c8000010303102280030601014000c00d1048042c400c4030102c0303070140c64420310bd101e0b6409000c1030311320041c3e005c0e460348049a441c04171541d03458003840c041e64418504039011030709494003414001c010f80000c4400d030b00c0741444100003503080a032003005801c140d800c0340e104d40b60048140c1c003a0240fa04020700301002000710740908141c1c41070034000769000301c1d011500d002d141d140548088000103041420740c0c40c200000348105000e804003c0b68500b00100041ca070143c251185418054a41022003030f98211001140007843c200c0184d401504603602d0820210383d0010020f0764440180c80300405402ea4034000444060080d106000010f800506642494500c200014051020042d806020844c01e8244030541d080510075201901c0d802051980311401d100120789a041d21150103d0b000031a200a44621800a0010705489408000200401403c1404200f03207071a0381004000710441020244640040c0001c2400035990155003c5595886003004106006418 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 537356465 1250 537355215 537355241
    0x506030406150b18150c100c1404030b0f010807150c230d080c0a05090d0c12050d030605040b03100c110102070302030c010509011404031b170702010e01051318 70
    0x81002004c0ca040e520142d10442c20803544e02c010180d44110104c8580600303422401e003580300650f0411002d03440c0d44065501e070b03d6400d1402c41040c81c111842595809500211908141c0d04240000e0403007407041c4030b01608203003025001e01030130440380700079084c0b003a4901c3c0104500340c1564410b1011418258150aa802c0142c25142e01c2174540c00355070f4081c0b03031640800281ba490002d5032040020041e146266001c3e0754151401c125901004800c02c908001035440d255441d50003d1002c0440c0001903900c0c2c4250080c281500d440180501110620b40c4082e00a42c1804410903856901180301c188002d07000000080102e0021800c940806041c105020030b9072002a40206168001014100c0603002c0ba00030710040d41d5110340c035400e0302d081001041e1040c4030040810002400780c608444052507411f040507011119482c4e4284a40c5803e1941841110000300c880541d60b00c01032421492200382130603440c1038804005248415014450f201815005480c5071114403140d41140d07000d0124 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 537357715 1250 537356465 537356467
    0x3080a2102041e08071404020d020f0a0c0b0f0402090106050c070911071106210702030d050f0412020601140d020a1d190605030a0605070c0c0b0301060f03060506030406150b 76
    0x66800c0c009101c040c0d11480c410010b0f640ca0f002428038000180c0034140e07170300e883d40c0b51404030b003510500003e9040000d42111458007405605c0702c40070000e0243c2500445a80c50160140c82c03070401c1d586e2400d000d0041d0841c002900100700c017580b101001c20341105c1d601c2c80c040344d4602c0710340e0240b410504660050180a402c2c80e00882048071f01801502e05c1c0c41c0a014900c055507224004c0007035501ca0140702d2410001c10b108122404914250000c1e8403880e0b80c0107480c0b4191890310100122441154841086240c4500707002c00d015403409002c10f0f04009000400c420b504003c07008040181c00d4a520340315010249203242151600c03d041d000a201041b07e001070f246c04403c0000c4810f80840341d887c140130490b09000d07080c681900400c004c4500c090054112035440d0b40303452001c0e1200030204001d00c98150056030000c0c8610140c04020319807030103155101e50500e00018403d0b00d00100762000c0604082041c407250b50344000300c0790000c0d448100000c0b250015080d1030041032075a4090084854 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 537358965 1250 537357715 537357719
    0x10b0a0503090f06160e0301020403050714191e090c02060103110609090f0f09030427090807141b03121e120603150c090405061c1a010603050103080a210204 69
    0x170000700c80c000c203030450b00d42c182083d01d402c05041c00c0303000310f1201800350b43c0008810000180014145607440340c0c05070000c03c0c0190040003072079031000750b40e0003038200e001c803c450030072841c0f1660054805016168414400e000044800075600d0006010103070100002ca028407200d5641d00d42181c81d002000350880d011781c54000c5480b5580340007183c918034402c2114000841c102c001004803400c6c3c584090740e085510002a403001c480c0403d01c44a035561a946500c3d14000c1400c0201500c080c6101d0002d981d0088014030840e810040f1824030500c10f1022400c20f0800e40d9004500c0000d0502511144c507100ea15590810010001c10100e014030f5060019001e4180315945814511400701138080701c2415055401030b101a10701180d4482020000f0b102490f00c5203016000b0503040b000082c54400e815041d0220b02008809142d000c64040c10070103501c50030907900c9540c0c0b0707005040c0760508022075899070721030450341e2041c031b82c2c00c0c2c0070460109a03c841440e003030240e0620340c400b048800c40d1078607 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 537360215 1250 537358965 537358981
    0x4080715120e0f0a0822030c140303040b040806060f060301050d031419080f091612030905150702042f0f040317091f0e060d0204030605280203010b0a0503090f06 71
    0x580010080c3c01002c1c644510615101b103d980908105d036805282c50700664034199410306901e00d0320081a070b140c0001c01000540c0c100980140010303000d050040e1615090160070401101900210580252400c0c0010440781e598409050a040d4050404c911030341840f480c281058821200e600c82c000309280c0607001041d82c403034000782c4100c41c910009800358640f5950b0964414841a031805c4010302c80070144128030741c4000400d0110b12900700300407c1034031038000500500c0344a22050805102003a064294905805071f8a07411010903800c400d00b9000c0440d640f04105041c0c8040340401e000507900e000402018101d800450300013255105e180f00359140d028641c0e00c0040c0c22846000e402200e1481d1406e201c10050071450991554408803030708005002e46a00141c0702e01440c1030b403c1c00000082803160003241c0c071980710748030380241c0c24000d440003844180c5001c860031b108610600052280458200032a00792050600b0200d440741d4401540c0741c81c210108075a407813140965001d001d010 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 537361465 1250 537360215 537360217
    0x15031e0c271802090307050d081201030302030a0207050607020d02091902040906090f0c0e090604060b0c03041a030106020312183703020307060f2004080715120e0f0a08 74
    0x40c5001110054008039420900003e0707020b0021080d42c950025241000103182caa114007041c030344074403034840c10700042c1030001076404000d90056000d608000f901d01e0045a040c0b00500292034221a0300f410300c00c154012074035070f1541c44c000901071030b01100440c2c0c10303c01d20301290b50700d841170b0803080d1f40d203d0310b0700b00720300182905110702c41c101410721501588183c440c1c000c50030309494690b601c0d01c20002e41e2041056105c03021f448103130029522080440d0701060741e8000d008421380c0000565079a85804022580604d0200310082c8025050005001980e400300c06c031400c034102c2c506100724a4039500110a400c110002e00d42009101d4080c1749a02070680e01c0c2c4047c815030b0038101380b140460f480c03c07207508044a140e00040068108000c060002086039005440c84c03001c418001414040087c03981c2c1e2408070a81904100c2100440d04111610040200c0c20280c8500789244071801410340002e0083c8038140c00c0c0c4e98805803110041002002c0c10002d8500c001244811181074400070f080520381 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 537362715 1250 537361465 537361469
    0x5150c12031b072402030906070e01030f0f1d03032521092f010804060b2809110901030902030a021509190e0c0a110706080115031e0c27 60
    0x13596800c1a84168a02036803080d00d200d110038801800903655000c808680c036415050386c040c107156440300d41a1040001e842218941484010300080c4184c44e18110300c049911030040f42001c0d4010420411111000544802054400410a109029042020364280d18441e80e8503518043c1c0d15600c034428442d981000260a020305600a4401045c46000c030725494010780c01c0300c1404000352055010b51040312030f40d5101e406110000703110541e40001850540810340c148040d101905141041c092445402d10020701c0da6171010089101c6d6685403003481c0c002c4489950505540da03d005081d924180003403441c05600038021040e07507141d25203042e03068100c200181e000d0042403180304c0032080c00400c1c550a40c6c008070680081d41c2d449110a845c1d6034042d400305010410b446c120b00c201c84100700403d03000303407071f1946a844c1c00e5810300d2079055104550b010705070201800c10000300d44c5802200000500c0301625a0b01050a180c0b200782503480082a0780764100c03410500c440851404607062010b41 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 537363965 1250 537362715 537362753
    0x3080307030606030b030a0c1505120103060603052503030507150507030e0114010305210f03090c100215180c120102070c060f0806060a0e0306070905150c12031b07 72
    0x100c844500345540c50406d01f000401c560641c2c0700c14040a0032640280d0b140510301d142c185d140600703140480c078418500782e00c01c440c020348a0703c044c02044820300502502001251040f40380f250805480740c0003803803d20000d07041c01800030b40030050001c1703004070564a95103907000f446942401e450060042400d0300a4841e55440e01004002198503141d02604070bc0c0c002d00200848049400c0c650845120035200081221081007007240c00c0d40c0d00c402540c0700d030041da0060402c24100000744403148860400903011908003d075540c50504117480e5143c2c00203041c0011300410401c04a8180c038003051010002d502ca8101c01d04400c51050540050042a200d02140304c03080c1e41d5103c081d60040c880c1c40d075000208031110700052090030414040c21030803010b440c141c170340c601c100000700e810240150b920780001008180c0c00c0c8011304002441c000306100c0800f0f901d280915540703051341c80fa004810034040441000011071024242104480100402c440c2a595100242d2400c21442006034030003803 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 537365215 1250 537363965 537363971
    0x120c100b01270e060111030d0209030a050607030209010915050d090c051203030a0c23160c0308030604051b070b0a0b1809010b0a0303090302193b04020a06180308030703060603 77
    0x2c03101e52091b203041040d640c80000031810401c44410041c041d412a242e915054410310ba441e201040e03040021a0051900d602d0040e51a00c07024001070400c42680c00c810b6500301d41c44405090700da445022141d440685070070009444199250524041901d03510a6611540004c2d180d441c811003c03005600500001404000c4070300c0d86d410035a190f8081c1c101c0d000301816400610496001b4400050038442c03802042c1e0b82c0c55030810743e100e40080078070703030820741c1c11040100412009013868030801da040102d01c1c2169268010740b01022005100c0d200000702140141c40204210661581200c43c0c2408024142c8203000504036072641c440400b11030002c03081d824103424841c00c0c10100550300a4030341668562141038219003d021800301503174054206c10481910004080da81080c00f5915001c118900c040e07458100a12802880c0c0c11a44a2101048038020300c8016900d108101c4100c1f042410302c08462404880c4001c41e4032420b5002070003203c8000100807071964194018400c1c3c810b203071020 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 537366465 1250 537365215 537365221
    0x30b04060603061e030c0506030a230105030d0305010803030c0903011e0b1903080d0c02160f0602010b030102040e0103020907140c0114090f100e0a05031b120c100b01270e 75
    0x3c11a0a0105e01c0003030100d9802c00e1040c451130a19100440c2d106d219010003051528a00d8418895030041000019107180040010311407441c040c42a0840f09059180900944d4103013103865480c3e11001d807400040980014200a0945007034009610710042d40c400307419024014905040503204084105204582c0c0071810b000e4040f03e0500801070320f1708002e000c0d080c1198042c0d001d0050000c004410250310500c150344900200a0700010083c102820141d03560508e08000a03027075804a0301c24074420b0340140300c1803091560b4006040c6c116a0103c4c0c0c10300f01916003100c2a200554042c040080c80c040014034140540b005400c02511800480c0060406a81d41d40c001f507250401a5406611034111881040c120211030300b100031386031419000d469107203401d5a101882e5900c00c5107050301d8480c0342122040d172401c050140c00d02e90381005e8542c4d464800c80132a02031311024044810189039580e1204002c05920404004446082c565161952580c166003841c01e1982544103056115940d0000 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 537367715 1250 537366465 537366509
    0x613180605041b1209061d0c0405100e060f1203040e160c03020309010c02011b1a070c150c02030d050a02030f0c160b09210a02060702240601030b0406060306 69
    0x1403020456119504c0c1030340104000d4006002e842c400e074007034644545545d030455844244440005047c0b000100401d40341c6041c109100644034002c0082da8403c0e080c080c100460010400719961115003100c030128601c1505002405801142002d501188008a00859900555200c043c01020800d46800701c03032000d44400c8890440b00c0e04001c00580080c040450654016280304022910505000003c0400b5000c001d00c40040180309079a804180300d0000e000e02c43c0d400205402c01c10615004a00c1d2442c2d4644500214038848000000c1d41c1d920154454103200384140c1f061001c7c064070900040c10a406620043c2d00700390b0307040720311110060100d0301a8089a046600c140f0081600d8210f084007600c40d0300c0444002030050b42e0700c0c001c903052001d0092508100c2c6c4114180b560400b80c40e2940d240c1d000b46000c40080c00715044d58011804210040001041382c40044240c11040304995240001213010b40400b4801d160050b0402101180d059015000780d07003035801084810030351000c2c0d070350 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 537368965 1250 537367715 537367751
    0x906060f020c0a06121d060901150509070f0507081201060f0e091b1b0f011b0e0117131709040b04110a030b1903050c0901080102030f0105061318060504 67
    0x2280d1008110804071080c03e0410f0f5801a0b070003c02c00d002ca60032000e00001c000340c10312804541e51a040e075034070103682500c032b00c1c1c50785824041d09003a40c400c0e91501e40140c01525041e0b480e40302c5014410301040c2003081204140c00c840000400352901041541d55600c094600341300c5000e0000490340c515000101c03801c1c4078042900c1000407400003070144205009011603a8052002c4c510386409810b0841c411000400514502801c000c0001540041d0107103000da0904442c0c12000411031504240040d582e40030400b04080c3c3c001201c0c5004036111151014860410381030024203c000b92040c1e44202e01b400c6e80a0308549000343c8007444108003500410044858405240d0702001c024086004524400d5001004919004d011340c04400c01d481413040c42a0a00d0344122210b41c45004508803500340501001d0041484000a504509000c4811a8402414002c00c0c0c0034810118071840369070405814440100a003042a14151103a40e1070703640034100d240030b01806103040580e00d00070600c0c116 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 537370215 1250 537368965 537368969
    0x1703100b0909010b1b1609060f0833090607020f120f0d060f030f060b0111030928180518030a081510021b0a05280906060f020c0a 57
    0xa2000103980c3c20104101c0103500a170646245100e03030b607601c01c00809010001c44d24141e18407071021408610b802c000009071041900721000b114a1090100721031903000030040c1800300840c0601c98818405000d4642190340c0429019507610164240260b014020494500591003642581c4109604643c01c0740c1c0d520107000001a40e05040110824985007240030b808895101c000c0890425130303846070540448010740041d995030942d002820108405403050310b0a40d032003800c103104008002e0590503103d000350480c0c240902880d40c7c0c00c070a00c981c254201d011140848010840003500e40b40034807108000d41c05a41c00301454440031401203203102c031a150502419200851070410b901d80704460400e00545001290014007048084c02c5e600d5504100c080f0080e9402401e04041401602d0411018041118020200740c002400b280e12409082ca068811042400d1000721591040c605140070b203901035400c651605502103201c59001c1c504560102a036402c6138640c08000c0304001e0054803034 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 537371465 1250 537370215 537370219
    0x6080a05010f151412090d030513020a14031c0302070302010b0f1011030717030702150c0a0e0f063106020316020609130b040e01060f211703100b09 65
    0x441e4882c0314107200713900130a818204081c1d15030400303401d0fa5100c0c9801c2015201002560010741d074503c207103907140c030a0550110400041c40514217540e00807a1540425000709030000041d00c4408040c0d0f141000b1400e402609100682405211803000600035003000004400550030050760b403030103180c13400b00c42100d06001012041d25040484068032881d81d0840b081c94039010502c0780c4000b2680426001d50405a81c111055423860a280001e08010403000740111100a510500403040040801d6030003100c2541016040707508010001850f0b081c1c1100d0340703907000302d00090050200c070106d80d41661440200ca0780a0741e0001c1c9501e01c01d00b05c8054019600142d00c24071450720b000d00406200300240d8006001686000055404030b03000d003104c1249080d42070748554040c0103504080c0b144040c40564000200305603401c2980441407000248242d0b0805040380071400c94008101f0f000707141080d40011040104c4020300b80d80d0301d158004503070340c0b101e00b5000c9000003804c011501c00c4480e60800 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 537372715 1250 537371465 537371489
    0x80109110306090a091e05070311010302031311010c02190504060e04050604031805030a061413031715060406030501061403060108070c140d020c040605030a1511090a06080a05010f 79
    0x1a04c10240020f061181c800c1d1103003410908008800c0c14603121907013416000d0300103400a01d0071424051040c2004404807810180304008000d1000c003410003107508554070101c241320300c207040070040300c15107030b2048041d40c4260304071003a15100b150b440001c3c2c2226820f41d0288080342da0741c0c0886070403540c201d4005d0b183c2c1d0030400005000a1192020810500309038441198a5481c0c07004031780303004903007082102d0a9035a5418000c0e9000000311250744410358910400002403603541c020319050440120000001014010440c24004605140e14406005e0304464545588402c003c1c05410288140e40115942c6410000404800701c101c82c03241c0b106850710061900c4521040310398081040056580006a1841d00300702c000c180074500c1284503503401040410211420401140d0140e8002d0740310b41e2051841c0400547d110382d001ca4000c400c42c1c0c0014504a00f074001d6615481190005a13222041d0000401d0494014955500910301010204640d0307032580c2e13010242031228047c0081270f0351 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 537373965 1250 537372715 537372721
    0x4060f0f0b12152208070311010e06090327060a020322050a0e13050105100806060904050d050f04091e15050a0b0f0702040501060c121b0f0201030902030d08010911030609 75
    0x24003c0c01810614400c844144044c40240c5a00c142e03030f085800d040340080d0b900b10b401c03007907000c00740160040004400081c00b0b80e420700440003035070392083c804c4030809280c0c03101c400500d030403250740d071000003000c060251655a05076a80080d03c0c0d230301c1024a0200e200400d2400042a0f45402d101c0081d10000f4041c00803203400c10b04c0c9441a100c00804815100548142d65130000b4028004e0a008405155074071800c00e0401c4227442c140200104168011900d407020080442c500161b642c01d0190f207420041d5807060b603030000348220302c580d800604400b801c228003954100050b103030b40c0e0405030304544200175400038550f28080c0610300e4810a40d005409500500584003844000c0c00d4115030500081d1400c0f5241e40880c0070398209074002404902c2d2640c0d42030503c18004040b00c5911050307e45000300e01c072a580485920301c2c490b000a4a4255180305103000c69002e6030000c1100c5170010101c07540781c8103a075001000d05200340603101d40c2c24205a00300680e8800c001c2513034000d80d0700400500160b0303 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 537375215 1250 537373965 537373981
    0x14070215030402270714030f01050904050f0a0305030105090c0901090b16021201090b090a03170703020c060a0b0f010216032604090b1c120804060f0f0b1215 69
    0x24102801c1a41c1c040640c03130348160115502c11000340400501100e01c201c615000314090f1041d8124806070072401c4040003002806040d0b00700d01c0b415a00300b1901d1002c0f5840b142095481d20010034030394410740c410741603003e0a01d40c01201035070482d10125450001c0f40c2c1c6203840e440b0790740180100030b03000c10040362051041415034400b42541c503002100c4440c03c44103a400142d0305140940308140e042c0d640d0200102807128001c00d09601c500e02d50002d1551340442d40d001801c0021144104050088440c08503a00920940445640000190882e0f444e424a40929002852440745c9a4815446080911410350020801810291484206000c3e45285890701280d10815950200c21503140d41e0341040141c01102c06803019003940d0100040e406600010321941c50040d08400b4902612140d44100040b04a0400d8048050600d00b100c2c058645e8030704140a03000d80455100702500b031001c418982c0c0030b035501103581d1500460300405104c42c4070350840d842c0e4800840e00c203142819107000410103 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 537376465 1250 537375215 537375217
    0x915011205030316140d0b040b06030609040f0f06020414010e04050108031e0f070507090f11040b07060b1c0201090e07050403020607140633010816020f1c14070215 72
    0x4030304c03814010200d007060800071400d64032401401c8003c603510505500c10781860b2143d10062101585d8080c5103007404400145c500b5030040004108200800302d8a0400075501018040a035001c1003d64550f61922400041e0300c4810790454002085900c000440385440c4c06514121010400510320f030191044070000082d517141404d400c0184200000c07107241070721b07900a02c0100d029002070000c031070030020440c090360540007800d5012820309204001e0751804408032011504180c12540d0750301c04034a84000500110800d132036018200103114000c01c000c41258600d00b0f032013681e40710318a50b00d54550b100d46920648203c0e00168041c4030901c01030400318004c03c0800e028145030002e4a0800e981c662034a00c040301c6084072400300f0422621245d00450fa06140d84124083c2038210003942e1000804152000f851140d03220703010000700704400c3c002c0c410b09031a8a9004140c41076940310107000c20055030800c48200c0058603001030484a000c42d2001da4a010382d0040503901607008140030000341d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 537377715 1250 537376465 537376501
    0x10f031a04111009050a09052203020d05090409051c020d0503040507270f020a1106091f02043308130318091b0e0d080d0908070b09150112050303 64
    0x7484131001000c83c0e150b4070281000028441d0710340c00700f01c030f24204c40818110700c098020705800a96840d1020006500854203a05245442ca070ac0c42e2681d40d0300001802500b800003006d0034034001d0f206440102c0e024001c03207103e02d9406408542240c96001403c50f0316100440300030306142c006800c1400386000b091103402c1b90015010f002d40a140c680d030940c1049640410001000c0c650002c1c506800f00d80004075008020070030405000c0078540703200100d480f094080c007455031003007820484a04d01d1800360705071005804110311140000c0c00e40302060f8000b002d01201c40015174810150010540d2251100d5840740c21180c401c0c501da207409c4d07038064600341c1b1691030701c650114a42c0d07400701380030075a4032440e000140c41d841402d05c807104c0e0780b50141c641e0448188450080e14541d2204c804180c61100720703210503801c2c0200081a0000707003030468040c00350741802000c084444041c0803e407100056810b0b051801c50320100c03403d90740c40c0402642c0c84000d03c8020140d400500000300c0c00c403408200c00403 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 537378965 1250 537377715 537377717
    0x90d0b0c0f04150e1e0d050f010204080c1201050709090b010c1e0201080f070c080f090a061205010906240225030510060338010f031a041110 62
    0x400c00411201c01c100310781007a00b194143d5080740c1003e0024540c030140b401528841602c0300307038441203900702d070440f103c0c12803180c81d000d0382c1e2000143c01044000c00c481c1c2032201820f00215110364503009410b890300054002288114a0703000d00140b01001803080078040ca0302e94072841c0701c4a00d0030010303001402a80004a05122646044501040da40c00d02145403000e41080c404661510b80f002506d080d0b000303007030404000400d000b041060354000f00c02105080c0c01038412525425200480786661003000e03001504a80c0317150001800f0b0760020850764000f01070810501c4aaa21238102d1741c2101d02c01d105a0380c01c01110030400500000d922940541d1150500c182c2d0500e404000210300e185a83c41420161040113010030818030006016070001c08400c004203106403441e549503040310040c05000704018220750511100309060b950101e01c080340c80040e20060030742e52040c0008000300b40b48416110303000c20501042500e142e40d41c035248520b5202c12060760030711100d028440680c0c000c0d15060 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 537380215 1250 537378965 537378967
    0x30f04171b0d0812010b030702011a0a060c150c02010209031513020f2124103011010f050901080f060102010207050a0c0602070602120406031e0905060601080606090d0b0c 75
    0x2244e0f0510064202c1c041c0041500c055a01d0501842c024216030b1142018110003031030001c059481d0b40d4a6034148111611481c0c0280440264180007d945e04250321004e402440d01d450020b001e80c041d005480041011000d854003550a11858140c1d010100c402e514101003d43c01d0390010300c1c0000300f40f174803140050718121004184541c650310008009210a100da8804c1a440c52086004d01109000d042070121100390380c1003400c08045400301a0051035050034030455011001115100745074800d601f1541c070548142007608050b003030101e44039001c0d80007846120b8500c0b502400b65048172041501070b0345a500c0b030fa43d41d0741200d03045e1070080c11090440d5020481000800c0040044000841c00791102d480303101d160840282c0380002c81c0e409002590000202040c1490386c00e41a2011107241c0e0901046151401a0b441002c00135000e81000091400040c00c0502c24001100c600c02c0340b0a880d142c0280d1142810042e95014000e002d95011507803070300304000903800e04880c640103000c0b10206 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 537381465 1250 537380215 537380227
    0x50705010819020705100b040e031602032b1805030604020d021201091b062c150307030e2e1104030c03081206040903080402100e03030f04171b0d08 65
    0x1d0382c1641e00c440302c1a620781d03204040c42a2516010710039001d0111003210300f00820704019603115180d00a8144200c00281940328000664800303020282c0c1201030300c0360001c0000e045080001c0c58110988840300080e02c2040707083c0803101c10480000640d100140103080e190368903800c004071084800e07801c17604070ba1040880303e40307064240650510039100f201220344090300c01c4011901030300c56a0011042007603d098a80d00e81c113a0140c034440750b14600d105296190740040100b00f00f010307444a1950a0000042001314040d030650261702c60203c401c007940e00c1c80070411007207011640003844054080064580500040c01340354807085840d049804c02c141040d9480d1a1115429400e604c26594400b0000f00c030340395840c2c414417541d4420011582000402c5494500405480001300024058180a1040c281c0c0780e0140700c00c1104040c0c024100d9941d4812150440e11540040c49994070308a0814580410340b90b010580c9621002d0380100c82901c0202281008819444140700b80c0d002e4a08001e8 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 537382715 1250 537381465 537381511
    0xc0b0402120d02010e010b1f11010e1504061505010806040c140d06080f0a08160f14010204080d080103081e041a040303090504090c030201050f0f070f1e0507050108 72
    0x814007288640e40c0000440d03d0804414030301f901c0c40d6890b254482d0070702c2110301e4400d6203800040040900e0a260050007000b800368020300400c10818002c402c0d129003441ea0030000400c40400e0710440c800c060074002c05c1036041c00c00f0900301450043c04e012507003500019601c1d05103940700d1940b00a03107242c0716070303032083c3c007448540190f00214010080350785401051002c503204000d0307883c1d111560300080101001c0c0740c031003000501844007410001d040320b0340c145007444003100d10342d08000d401c418010b001320490700d11b00317001350f2203481044c48501625000440c01c40c0281d0a82e07040320b400c0010a85450300740840006ea000b800b0315811054082440b0100305000c1c000004060745015904081d80c850450401804020b40390384268416801c1159001c001255002c401c41220b0b820308009445000300c02c1c41070f10340e000340d81900404c010080780307076024010141102e07180c490041d20400f00791f105074600c2080742c201144c0094000d5000301000c02c115407140c1101d980c0a80120140003c01c0da284e11 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 537383965 1250 537382715 537382723
    0x21510030615050109150906050702060f0a11060106030905030702042c0106081002031e2a070605161709070f080c0a3204020403020315011809030c0b040212 69
    0x490b440310116298414406940c104e20901c02612000303000803148400068002d10041c014043c2c10b00700240403410380110345030101600e4041c0e0035114031580711381001c0002001c040407444000c3c0203124000002800d9406482801e80041c0c10001846c50616a40c0900001c0d00c14400700f030100e40e0031004900d82018005c1040300b6000d01c0d000021451038640441d0a2030b24102c031300c05250303561040050241940d0038031702e0505102c91007180d01030195201f66444d01541500707200003c1c2d541040036182d117014003070030040046034480c7d0020485502ca00605030031b4641520300000105814810742e082810703002c80e1543c0c2c002c5600c0111504952176130388a070781802c0389510485050384000011601840c0c9002c0c07590250118105000300e00d8000078022008028200c082c01344030081c841c8002c5140c48503011140030307640140444e01d407580340c451264650351092040004602c40381004004240e414080c200c10181c056461042403102034451504030403020300120b0380010b051112101c04030042c8 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 537385215 1250 537383965 537383981
    0x10050c070f050312060f010e100908030d020409060e06010c0f0f06020f0a020d230a1407050609060c0c0c151603092c0708070c0c0b1803030702010215100306 69
    0x40503540390140104440d200b108050175481c41840307158030305003072070741d00a00c803a001030b0044940f00351044161170251004401504005081e02001409111228480e0010000ca4200500c00c1050036500c0e140406070142c00d0341c185000610801c2450046484101c100d00514058904410521226076405089070f00007043d16042c40c0002c580d0800c03254041c00300c5148022780341861022210149182c808003200f128088044a50214004410038880c40c0c0306d00310001464603890355100c45050a0f9520346080380c802c10345114000004040308864000c1d9141400880000c100b404204030401c240007007100d240d4150040107108550880c02c84480c0145150700030b488481d929070915908200f183c400707440070717034524014a00c038068a0741c0110750942e02c1600d41c40c010005444a031812502280309a60144c00d00c83e090f00b0101e00311003400010008120580e041220155522003855140c1c00b0f03005019000d07800c00c080021518005440700c07903010024425410030315841c0d5071440c084410103 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 537386465 1250 537385215 537385223
    0x201050603100903210912020c031e070e01030521040f090507050904050a0906051501050702040e120a0e10030c020d0c020a12030e19081b041d2d10050c070f 69
    0x50035404043c880c03125460071f8804c0f02c5101401606c07840e28003295070346a410140b204013002104101800410500071034025151600100c190342d43e4a0400f2030707a420b00e410312001020f10500b40345800004034003c0380c04031260003280c81d01543c82c0420701c8008003401000501400300400285016a031144601440354508440008100606042030401c84200400d054500082451240d82980e04181901e0006604503002700303451581b002c4a90500c6545000000089408501c0301d4600d50841c250000c00003040d150703c0420440510102c00b9a94200e11000158005072001418a4824503145506500150419520b55035440310302484040c07120065000034500601c501c4180b40188162494085441030000e8540c24000300310344440a101c410302c030904840a000009840b540c101c07000007545d4601c06203041c0320941600d0b884a6032201d041c40e54086d6074031141500380e07118030071014001b20343c00280b000b500e030042024010038000d0000c205849042c004840020b4600c00b0511540740302e = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 537387715 1250 537386465 537386471
    0x90c0b07050114190605010e180a0902031c1b0b0c09030c060d140112110907030f180b07080c0a0f0c050d021f1107030323090715020105060310090321 66
    0x4813040c0400c5540340d800c014108400c94015590555030601c074540d030038030b248461401c651100c0719641c0042041c0c11000f50140110310002800061820b03030000c9105c60b64954600c404081c8a5540c2006084e4030014856a80c00000c50307010494600502032814010b403c8840c1c07409110001506030300318107001c0c0e500688480c400384030401e030414110300401103070305210454226541c4060501000e02005e50003032038818002000c00344a134200d4600d1107403001c8200000c4492900d2010145d071225016610040070b0300106020314030401c2102c2c840d550324052582050014481222003c0c480a460400c02059410300004190103010000b589240d64008003104a030f00300d0a8003000369800100c40b049841e054103803201d04441000c070340310b0700d0341031034005108404507040c41d19003044000e00c1c99100540200300012448000307480b00c1540c0340d90311019062a0040e204174241c910131102c498140d00031403459544a02d0b65040140d04178403904000907014104a408140341600740c81c481d1140d81c0b = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 537388965 1250 537387715 537387751
    0x304182705030301080120071b030614010609060e1018031b080c0a030c120c03120305010509090d021b010207180f060603232208030405010f090c0b07050114 69
    0x110900c50307510f011034007141f62042100384040100445c0540322002c3d11000c410080070401080482521000e5640500100202c0d01d005d20304070b44810003405103070041502030300d01240e0035000348405600d106d8002d051031500c80c0100c50840f4007400c01c03440b401c590b0360801008400140e00d040b501c20650741d42c2a803205428030b041d00d803d01d00244024603900036408000c040c8040b9005c441450b090700d1481c00d20b074241c10903a14102111005071380c0003602c1443c1c502c0e80d00701100d62603004503048481c00c031580c4a080e2901c560864495103824410300240c4d10400111032841a24003a180081e84140140c6d00c3d2681c0d0b50002042000c808458541504d544100c00034131001240b2600b00600a1072034104028081048002400034070b4408502e8840810320004807080c040d080c80b603580c0c3c00c1e0741c1e00303c031115041e910700b5843c2d0b07800954007120103508081c40d10900743d01911652004580020031100d0380e9140070b810903110350054400755160b548440341c2201c8a0050030324180542c20009140384024 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 537390215 1250 537388965 537388979
    0x533030f0114010605070210050309070504020a08040309050a12111302040e01081219200f031c05070921061d150106050307030c11010f1d0304182705030301 69
    0x710b058000c6020b01134180f02c1d100c0561500503021045a1190a12039983e4a50004803864044103501003070b486070001a44081c4507920225642c011442521000c10907900c680811244810300e00031146007032005c1002001142181200900e08040642103441070055582214281e81c426000b80424005a0300100f1060104000c41c01080604440150415008518100c00520385554a03400c0060001c980c58044002001000c01c2c1d050080442d100342c080d540e455612900108901034500d800c15000380140042c1e805000e10940e902da80382d039006401d00300d86840d00070b000380450f0f1030f0780701008c01100000c00038814009003000ea9106081c410030705d40d0714603140c020303a1010b8010002e15100100001c0341c0040a40ea0004a107050100b0110180081140c121400d42140c8400f90b003000102421010b4550010b0101b212080501791840d8184044c00c0c0d40c0d115511172091000c0341c101080d180c03e00550301075880f03083c5d0306d542c00740710841038201030880401f5628103840da0340000004202d02 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 537391465 1250 537390215 537390251
    0x1050702092701020901020c2209050601090e01110f07030c050f210720041e05100518040209040809061b010507170103021512040501020901030f0533030f01 69
    0x550030900a600d80021740d00000c0d1100b10043c5414001c0d0000c0c40c0300601c1e000c01140030030050031840c50420188140c0e0500940e54042842014201032030400b112140010600030240072900344450a860324070100c1c107000b2640d111000036000c001116a103100040c0d001c1c4001c6200305800340c01000c4003c0114091559000400302c511080ea004124060029088a02d00d0032014600c90a103146040000085400b40070001200c09000b42c104001003040e40141c0d0189001d81030b0700410312050b5407a003092161411140400c210b82e4440700d00000c0c0149814010954440c1c810425241800918004141e0a030040c07406429a0a003620034190350050900c202c40d440b60803860310304154032800300784070f50700c100601020340600d103158103514035021010100d400a40c50006554814501420410700079080003010a000a00f00300c100201100d03035001d854000c83e84403400380302500c0d60440c100b801d001041070300e000e03c2041c42c1c80d02a965805104064011466400202e90f00c0b503d00b0083c40c403 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 537392715 1250 537391465 537391531
    0x2010c03050405100905011104031a070507080414041506031e0b2407051609051e010b130b040b0c0106120f12021513050c040507050d09020105070209 66
    0x80510307140070040880c00c001004078003440e040d00e0004044074541001d90141c54020348221502c0c2c40028004100318a04e05002d10803005040c0845240c1c885010032511403154803400750840701c091000b40b010105ca40c000d175900082c02000040c49440f80400c440030b5401c181e010b540030a581d60010313001c0c0100e10075065a000711200b010006682c0d4000000d0b040c400b11440d40c1080c400100c804644459400122851700c4e0f0040c0440e03901005a10030602d1001841c003603e5001ea04280c042086061001034000e29086816121000350b800e00042d1003150b04592039942c40c0790704642e00080d00c01d0400b002030000c0c10300b039588035585015a400c6507003134850b2948841c140e5844034032110b02007108014030b44045580602038a0b0850004071049141410400350216003030301100c00c2c00590400f2440c090003d074030403c10b68030030044990400048a008680b1100821002c01c0701d44540c10341540704003503030381c81410428240b0001b90013040c003031807003140c40d030007440341d85040741884401c0c021500b40 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 537393965 1250 537392715 537392717
    0x3031b0d0606111c1b0606170f190308010e06240c010c0e030309150d06140405150d060c12060f06090e10050d060e0a03020c0f27070c1205090102010c 66
    0x22840071034800090540a40100d0075034041c07003a4035171508008241d0071020003081d07401d05241410300003c071401e403580002e10b44c03079089101e0a06080598035042c440040d40740d805440351a1103a1800c000943c1c00e00e0f00400c00c690001c0080c00050045d14030340b0400070700f00400051a03850f03d103a0822242159004561403041c044400a170000c0ca98001040b64030700c440941312490340400035001000c0d9070043e80c0380540c1241c2070210104040e000000c0064070307120200d406007d5034445c0c0900303410043c5200d1700182c0008075081c8660100c1c50315000344007031074002d2804034030b020905180641201d0058000a45d00403801e00d00308002a070040700c1001502c1c0301000c6800300d05000c040c1400142442c030075140103a003200780000603c41c180d40500c40380b03442082598460980b0785802500d60104c0600e0a1190f40111511201c6042551907a4030f0494400c20281880590a0b069440414000c003c0410000c030060100000344039170840b8041c0039a0303521455200e40c42c1350300186c01d5400044100e0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 537395215 1250 537393965 537394003
    0x1e130b090703080f090a0e0103030804020f0609011b140d050405030d0203030705070609020301020405060d021c1b030b0409021008160e21010b060f07020a0806060303031b0d060611 79
    0x21012402c2801104c0d046142d050080d50f5802030b00c070100d0b60458443d03200700b812421030f00001040c16007081469105038400c0b6801032810b500c0204100c41801002c24060019008500c0e960f030007aa8a07000c04050741c01180060016070070100028640460341e5824000990042070070032880c01e00700040c0c615100700f800654294649a400140385029401c03014001584500205081d5182941258040d14016012598a15007111480c0c040e51181c421092202e101c04680302d0310403083e106850410b50090000d040e2506090011000f40c152070300e40d2a03110f503848802ca00140e480e201d16810b20030140e124001036152400c02e0702d49040c0c80c03003000014403050303000300c0142d070f42e07007800c40e070841d00302041d40e00c48414161480500500e080702410782c00078130000e1403000c0d4807910300c0a80b022500c2198034000749610381c1d0405840720b00542d0b0040e0103905c03d202007401107801c41c40c120140c01c1518080350400c03c0031102a8240c85c46540b04401240348034103030313042c849018498405034a43d820094 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 537396465 1250 537395215 537395219
    0x90f0f062a1e06061502430f1508070e0d080a120903020c0f1509061b010507050d050106080f0c22030501060f0e010b0f031e130b0907 59
    0x1811000d504190010b0151004204008511014082c50140e2980104080000a0325140b021082404000399980540714000000382043c11050301e80d510000c04080b044c3c08818080c02101d0301d03891582071101d40c005244c81c042102002c403480100103051862100c900b50005103400b41444401810070002c0141040b01440e03076890b9120704244030750340300d81001d6440c058444216100c0c0e0080200d5520340341010800d000f815030010b0007408212040b00d04882e9400d00c002000000e02c018880d01a83c03940c01d201030b54817032401c0341c0506002d44454000c9011501d0128245003140c004441c504081080484c41d02c5072842180f08184c090050703418040112b040912030800c03080d0008001194015000a5042c50441044d40c603103015201d40c110247c01a4903481d1036406814680200341d6075062114001416400c10715a0904841a00410516221900440c031070294001010700c1042080804402c40f0341200c0c041603031013001203400000c110681840c2050849102034003a10a41d4040541 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 537397715 1250 537396465 537396527
    0x5030d050612030901080a0605030604141c140906041206060e070e0d06050901060f290306060703030b03010b1309021806210a06330605071101090f0f06 67
    0x813102102d000f420007a100fa82c80c07560f040013409450300721340d415000305010700c010403000303482007202c001ca01004e94400f007000e05203003920050412000030014985000c400e0702d00304404018aa9180c0107400180390680f2007a030f000521101100403182907564031001c010351840000b21640004c02072424000d065003020004074041c10300d420140640e5503900c007103101c01d00d095100900420054500c03500b240d41c3c0340d07115052035181c100039940601c01401c03036041c110081c50850781300e1035000301f0031410006e00b80c80c201c0007444480381458140d0b40e1040111441d94500300d080c02c54001d50000450f1008152043c8454030300e44000303801c00e070040c2509000321a40c034008070a4107102001c02400d660050865808e160210f9404060038182ca010440603c1c0c110348601a5004001001503034140e43c0f080020141c2ca5540788107407400240c1c288409000030312503c440c0c000c001e070b052516142d03290301c84401c1315030f0406551203844184c4135164100000c540001c034800d035403a071010010001d01825a1 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 537398965 1250 537397715 537397717
    0xc060c01140c031603110a080a0b0a081b040501050919061a09010e04060e062b08090a17120c010902030f0c01030b0405041101111f0501030c121a1b030405030d05061203 74
    0x501f240500826100107085145c41e9800001034070801000c2580c610b681d06010b83d01e400c1c020001d8903801c940000038412605181c040c550403070341c1c0581f004040346e03500e200c0c0585103814806134030380c241d49410000891003a6890f501c000d2040b00c1c070030380d0380da504040c002515003103ca80b46c8900890400c601002040c047e0b00c9816842501580c4000151ba40c20510021421070140103114a8034600044000d10281c200a050004030035900600b10a44039001035600e094103401d843c0141e4400105a113503420f14a000e0014651400c00105020040c1c1d40040d082124003417003580554001001c080b495a454001d800303100c2c2081c4c030b08000d0b9042c25150504104810f045090500503004042d1803507240800c030120800c0d80c28405802c12003064a91000a06400e100070740d03001b81c00f00307800b1409140c100c80b05c5020710762080b204100d00041c00c0482d00c0301074004011500f14065480c7c0c03000c161401d2001140314621450145a45000b002d043d03030111a4060100c6004016140341c4402e0154008 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 537400215 1250 537398965 537398977
    0x304060815101209050a1a10210c030b0f040605100b04050d022115012c07110a06050603060a090305030a021309060909051c020c060c01140c03160311 66
    0x4075242a0300301d0f4103080900503042d132500c010b14500c1016040003d0002c580c115100340415400159001d80710000340c00003842040c00707503020a0161445e0b802e503400f6010351406446105900d40c80754203641e515a0f000c5007001712081c0b801040380204000420500740301e500da02103042041e141000741403414036400d90140780a0103010300343c0c2400c4a429941c1706508c5004200340303010450420051381a007a5210020740400c050124408400880c089079003400341c030007005208000c0c100303003420340962136014070b40508002e090128642210680d46414001a5821800382e0f07404070b158144170050ad46480c1e4000c0c500500c1900c0c059140001940c410100c82e0402c01c0c903c0e0143e1124034410f400e034504e002c04d6101070f42c00c1d0b15088000554503415000b50360f10360300aa0540301040b071100b99590303c924201c4408401600421100d1000b0301d040c201912001d48482c0002804008040f232440445109070b9560181480c0401080440c20300040040c51011f110b00e0b061100214045250459020341c1c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 537401465 1250 537400215 537400217
    0x306120201110c030a0f12140f03071103030705070c050a0e1b0415110c181909050604060b03070b0c0309040b0102030c0a030f090b0909010302220e030406081510 71
    0x888030ba6000744070401141c041d02000600b5110160b0b002e01d42904079800c80c9000329125038030f003440b2212080c010400780c000c4061307000141c1d142c48603007840c04c103055000500f604141310700803489500152080001d184600c44a80390780e0740c0c0d94003c0c20300750b982c1a5030f90300c43c40c894909078030140880003403004c04903000b904e202d881000b910403018261100b400340e178109200940180410120182c1c4c00f801d030f0078004482034180d0b12030702180d5041c031416010701c80c406174000c0d603480081180200b40041e00540d000c0c4003240007a01d071200c0c1da00d4600b0a0001e880c241e6410751650800d0100345010b009110043c66140b00c21032401c4603561a540d1a03020340b4403024480ea0f03072585990701590007441291031500ea424162035001c030280c40c020700600c2141c80034038001056900041901003140c405c80710301110060204601d40e20b50340c200301111301e07405404141242001c0c030f00c14003246180038040814413080041c548603400d00d0070041c440c280080c6040080c3d181620550180e07250798005a8010311030b = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 537402715 1250 537401465 537401477
    0x9031216260a031508010e0d0e04090204060306020702040b06120a20070c06090501051309090c05060a0905040b04091110020120130504060e011211040221070306120201 74
    0x15211100305106030701c40080d054401c00040c80c41999605a0002008a00391000c00414030740b5042200d00300c3c1c0341911003071000c0d031040e00001045801842c01c04075052006102061190003640400d0a0f100268403c541e00340d00440e4800852406005801c1c1000c0300303461482c200490030019020101010b400861059541e856280a03041041820301c440c00401c5019641c61400b0314100c10540300d9807140c2d05c0014070006020a55610403012070303911400e40981d1240306420080d81000070316099030304440c2d40c00040b00029407521070102420f0110483c0c4c80355280c60f40b400c0240030a4480c0b180109115514000750720000440070003044c2d030700d80c00c10b407440d007004038a0030070036030040010100380025141140d000c21810020980203280c02c050041100c0506550340040c4810380d456802000401e8602c04018040103e1001030503002a000710f90030301c012100d10001c1412603010401400180c1e9400002500c06030000c06000e4000e2850320741009a54980b44003440d845a54120007810018 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 537403965 1250 537402715 537402743
    0x9011d160e0907080403090b090d03050d060f031209050d0819120515120d0807050c0c0405040b0727060e0d0b0c070308070f0906030c0507150209031216 67
    0x48181c040700410340002d02400d0181c101030308081c2221000300c030120005201c840003c50078131080415641d01100241002c01d407140da03580c058542d500000b144405180c0e540c80b001800072032440403040218003c1502120001051070000d1000800d03400040c000c010b01854a4002000002201c0380210a01603c4003040313803400c0d08072051503040800e07003040e0381000c0038002c00d202d116081052a0f0411691a0010b06d84507108980300c850f00813010012400102c001002c4c94010310041241c240c1510685440c500070900180440c0e40941c0c06442a000c0342042214094001c24110411048002c0120400030a0243c0d40b000d00001d0103800104081c84400d86802e8645400854000b031b407060709081039150641c4042c1d5035400242d400e400003a2880d010400b024043c0924849035110340da03801003042d003001d10a5021f429508c0c0c40c4410050108071110205050008419560b40d010760096901e55406040503c0d108070504051400340c0200310240f90398072200c0341d03180c81a6100050040d480303 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 537405215 1250 537403965 537403967
    0x9030201090c0e2202060a030504020d0b093306100c05030c0102070b1608010b070f1b03121d0d02040902031b0102010507110c041d03160209011d16 65
    0x4801103000410845407082c012032150140d060b944d100b244800380e070111200c895a041c0003030303102d11076020b07400c04402c2021410591281e00200d81c414000b60606500d11400d6884540305003040b42d02031000d070030a030110000526a160115840d901e207003501c058103100440a084240000b078602841003081c1010b8440f058007802d40580070913000001e60f0340700c24546140078082d40c40410121240540c0c6000662414120050101300351354a41c1d40341c402ea0308160700e15000b9400113000740c801080d91030022001034121007101068020425242c440545140342440700401c05074121030074009500546940c0000c0c43c1402d0312002c20403542c03100c6840990011500500e00e0700c00107901070054201e00a030001030ba2442d040000004c0c0c2c000c1113140d0703410400300c6907035a002c1002106a0011709150100b442c103038008050351080e0307450410310043c407034007030134070b5940292444072140010204541c190f00d4040c1c4994010300e6a0b04903c000480d400040c001803500040a1031b8401d030700d08103881981 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 537406465 1250 537405215 537405221
    0x5031b01120608150708040816030509060309010b0307170c0d15050c0a1b030c2913031205010b0f0a0e03010204060504090513030e0f030f060115080907050f0409030201 74
    0x19000940c01001626154088aa03c4859074214168114004c81c08110b00c544122059881540c1041d21242851040b80043c2170710f4003500c1003582005400c0c0400000342e645d000085020340348210001405200341d40505062100fa41d0044d03c681d5210303000b055048401094081c00440e088405490314180c916020401c5540c01007020b000501d400b00308030603003040100415030580140c42e0b41440454141019880380d40e001d60080028903214400302c00280007082070030701030402842042c0646101c2140b0440c850045510426070b8072158420001e0541014144099480030201402190f0403c0400d1465104407902c1c2e50401c18001425440a0b20800d640c45016038001c009542d80e41d80d81000515036005802583c04c2c413031078100420f00255918108210743c69150303c407902c141100404000302c421110b42882e070503000c0d01040b0500004180542c2d80a0300d143e0900918100c064203004100c44c0c0300a041c10803c0c1d1064a040c061075903190966110a0000c9801244040041c44c00303e000d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 537407715 1250 537406465 537406487
    0x90b01120203010f24090504050c090d080d1103010e01050f0109080f0a030e060c0706030b030c0a09020d0b031204090207111f0f02072601020c06070315050a05031b01 73
    0x190078408800803e5264080074403100b212402182c5030f40711081808000701d241407442c030040224000000410050915030041940640420b4159040c111000f010400300303048110100e41003c0c000400314140b5a0034400e000000c82001146d034115810003205489880042c0905482400105080081a8031501856010b041c0070341c1501e00708200b00f482c555603a120324a0460211384a4640580103051450075601080c0007000180b514a01e0040305030010034400207240e809d8040d44824011715280d000090000f4803a1001c0141d456004007520400c07128403c05142c800c1d00302d0340ba6181d203c0700803802d0302c0503a0050040140d0341d01480c640001e100700003810050304109402d040303050318000b084034488201911f40b201a0580e0068504036110318803801200c0785044d100b4401c031008144581105191481c0400061604035a030030400c1c0381040c1124600c0010b511188480e40440071000d55100904042d6600e10b0001c5c1024000703030702e5040340c046943d6030440006104011368071403c0b213001 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 537408965 1250 537407715 537407747
    0x40203040f051506010f05192d120b0a060504140d0f050a030212040b0d02070203070b2a060f151807030608011d19030203071707140c0604090b01 64
    0x504001400e0703030342c3c0d003104492590204c0d0310038000c048050700680448150900c13000c1e00e06000d07d40080169585003880352000e030321702051101d20309041e007080c2844045110315101d038410207210036220002d40d004080228007031601e000c2d04010300d98115003968203071504040700c1b0905542c07410105040341c0e10100c024101c0c512810f4941c041c840b01068140e1214003036805c0c1e5030110500c215a01c031910952013140c03011134003002640b44023102035000d8010944010103031480507544102c110700030b030041d000000d901726000c54884110310074584084105540c4070040c000358601041c03071040c0c1210007091844010003d1012994a03500c21003280c80d00001c0049401260410040c001d00030800c41c080c084c503941c40c08411200400c941002140f82034803a20042524803c5481074031080c0031110300403001c0d4801484140c00240c0c000f40d1400d40020308083c0c0c50388400607414034920000e4201c04890076900400066a00364031190200c0d0140e884500011800000e401c1c0101c501d02c1d00707860598 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 537410071 1106 537408965 537408973
    0x110d0b0910032003010e120405130b0d020d02030a0c0b0a031d030a0f110706210c0c170c031801030b0102030f042310181a0702040203040f05 62
    0x3c02c80f00c0301500210760011100541c0d46001c0c00c0f2151280744040100e018415414001030016403440d04401c103201c03510000c4040703808100d5525002c1d01507290002c0000964504000c1d9807a40c99001c445050030540d0380388944141d4100500303803400203041148051001c00e0b000000c03511a0f40d050041c40c03030003464690548049080a5248081c01301c110400d0000c500240702c040002c14058840328440341401321190147e805036000703410424a040d504869041d400301e0f4181856a1220103030040201c05140d07800c2c140a041c0c41445144400a0102000039125181600c2c1c0c1c1c00a80f000d1000b580c9000041e030304d0340074498262100da201808200108801069694903100c009413412880840001c040345580c01030402320000700e48460000b4264840b540e003e07400904005c0001c5181001c4c1d0543d0a0f083d10580e00041d11890300800410706000d500040d00c0710065000c0221 = true := by decide +kernel

theorem cover : BRFrame.Cov 537230215 537410071 := by
  have h0 := BRFrame.cov_init 537230215
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537230215 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537230215 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537230215 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537230215 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537230215 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537230215 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537230215 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537230215 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537230215 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537230215 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537230215 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537230215 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537230215 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537230215 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537230215 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537230215 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537230215 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537230215 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537230215 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537230215 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537230215 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537230215 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537230215 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537230215 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537230215 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537230215 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537230215 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537230215 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537230215 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537230215 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537230215 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537230215 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537230215 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537230215 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537230215 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537230215 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537230215 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537230215 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537230215 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537230215 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537230215 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537230215 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537230215 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537230215 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537230215 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537230215 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537230215 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537230215 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537230215 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537230215 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537230215 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537230215 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537230215 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537230215 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537230215 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537230215 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537230215 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537230215 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537230215 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537230215 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537230215 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537230215 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537230215 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537230215 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537230215 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537230215 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537230215 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537230215 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537230215 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537230215 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537230215 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537230215 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537230215 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537230215 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537230215 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537230215 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537230215 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537230215 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537230215 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537230215 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537230215 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537230215 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537230215 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537230215 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537230215 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537230215 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537230215 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537230215 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537230215 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537230215 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537230215 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537230215 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537230215 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537230215 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537230215 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537230215 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537230215 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537230215 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537230215 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537230215 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537230215 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537230215 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537230215 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537230215 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537230215 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537230215 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537230215 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537230215 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537230215 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537230215 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537230215 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537230215 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537230215 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537230215 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537230215 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537230215 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537230215 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537230215 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537230215 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537230215 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537230215 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537230215 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537230215 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537230215 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537230215 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537230215 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537230215 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537230215 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537230215 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537230215 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537230215 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537230215 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537230215 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537230215 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537230215 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537230215 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537230215 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537230215 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537230215 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537230215 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537230215 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537230215 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537230215 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537230215 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 537230215 ≤ n) (h2 : n < 537410071) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
