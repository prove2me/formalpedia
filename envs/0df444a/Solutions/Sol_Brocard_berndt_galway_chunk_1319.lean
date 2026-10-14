-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1319
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:21:03.031366+00:00
-- url     : https://prove2.me/submissions/17924aa2-5206-410a-bd0b-4b34ee718a8b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 237050359 ≤ n < 237230215 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 237051609 1250 237050359 237050369
    0x70501060801050108150403020309060d060e150405010f080c0d0302010b09070507020405150105031609080d03020d11040b1207020c090106050a030606021207061121040303060504020f1603020a020901 88
    0x10403d9030400054a00d002900a00c00381407084880c244000f180e004002c0701d0204a0903200999514a2440c0c043c0240c03c4661010b90480740100c10060441c4406004000310141280c0900050740d94617100c09a010ba180a0401c46400c0006801014a04500e003a01c280f44a40004144401c803080021000402114400c012407400075400d0214030b0300b482120740c864207008011f4103034034851000804c1c60000901030558011101e84c162502030047c4d806c140180540411a480001c80540040107500b0010403014558181200d03002c0c440740310819503060315004030516061011000301c502211001510001c25801007240c002034507141c162410303001c0e01b6a500c80c560340e00d800810041c110b4826500c02c0b01150040050702a12405690895403c42d40026000c07440e11401c9030203110300e205410305a4060800030101ea00c1511026100030710850090b10f0402c682e6070754405010903072103090320300a02c64078200f1400e02600301c262086c071080c1e07001e441125000c21480e8046101f005007030f005 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 237052859 1250 237051609 237051611
    0x213050a150305070503070c12021e0c010e0a050f01120b0303070f0201020d020109081603091229010e010902030c070b04050601140d08040b0c030705070902030708010509160311070501060801 84
    0x50360340c05000b0950800c4c050316100c0e02d035103001c44000308101d10711040181140410210b80440f40d04c20445c28000c41ea030700d175a80032050401c066441d1390750000d41d41c0300e0104e204200f0002c6c0b6441c041d540da90440b94041e101076a41401ca03001103c446140080002c038403a641e8140c1c125548040014280d024490900e21401c1c409500019290144004e0800304680c10206110005000c0c14141c4941d1680c4c1214544040030303c1c0b03800d445120b41500226040c6014207400c80034420904034180508602640552030303911206001140e43c2c6090103064010740c03100004201c00c08940e4015544208444030003820100c0c075941d4400d0911040e01d042d20564003800052010038210142c0c81034010084411524211240c0d0310f001c0d880c09584141090b0070804209060118401e000300c9010650240603592440e88803182840290400c0d42c141000401c020700100c1c0c142000c402d01405614501040e50100460a004502a007800400043c07528018805500041c0e000d01900c0050508240 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 237054109 1250 237052859 237052889
    0xf010605120307020a030303020c0c04050f0f0f070206041203110304031d1806190806071106070f0c0b0a2702040e0109150c0c080703030b030606100f030213050a 71
    0x40003040c200e10028507655800c20030002d0016035546030078a04a0307905050144c2c80f000c440b1941c0d400c04c11725600322600242004108002c8400b420703015031103032500d881840520b0301d46072500d050005d004c482c4c40e8003503130050002c54041181c2480d4a600300e05c1c94034000c0b40c01200000501180d40041d101200896002030414444c01031171061a42034200c2922045030180107072280c131125040c044c0a160080014017111804203500c00c1c842c8001d00350090071034850342040c07807000b082500e148072807140c10f001e80b0010807510740c0324031400541c4420a9403002c00d01942038444a0010340d0207404034810981d240300c00d55200185040a892052040b039040b14814143c4c014001510b2080c0040301c59a4035080cac40000099842403401d071343c41d401b0080000d030281200700546100440203800350602501140074020560f02d03070011401c0350800d6058900688034103013403022a100824030710020441a008035244a8403a82c058400f6a920f868403201a9a583c00802e2101c02c0e60b411124825003014 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 237055359 1250 237054109 237054119
    0x6080c030c120a031101090203032101060c0b010b0c0c0306090c0108011a040b03040312050c030603010b030a15110f04080304061725030906060e1005030f10020901110f0106 76
    0x408190700001058031582c03000c035480038203140c841880c2000201441503090590b5500d00e02584a0b281559014003141d40d290402c0c11400500c00000e204540d540d00743c4400801c00601c0b5200c100b203016407161183e04541d0825402134100d4100c2900c0d80c4c26071040304010680742d030f0100000c901408424003e0000058090001000e0344e0b016000b000c00c0c2034441210f84600b442c0794044400302c581070780d0b209482e515589401c40340704943c0034030340c0e40480c1042c05102c41c080002000b18000c040c100c3c0204583e064410034140c65800b005000340540b00702c3d4804d00ca0003082ca8011880400118200030314007000b820801a16401a4008075120341c004202071281c580c02c0641500045441c0030761003050300e0710038000400c4885001210151203200d0400319000b90194010315242a4800001d120440e1240c00315044c00e54101c40103842d0207030000c400074150501184450038101c2c5000500140c482912584d000b82d0720106c05241040003070138800b08408000c1c002c07942080b12000021510610380 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 237056609 1250 237055359 237055363
    0x5040f090209130b130510050a052202180a08010f06121709042a09051203041406040f0603051504061809020a0906030807121b08031906080c03 63
    0x150040c2540500c100b002040e55540d00b441c0b07a954400210001c00c0c288200c0c80440d0300301010b07880041d0304504140c140f0264143c128445010b449040c2c0710aa0401da0356820171040c8c0601c280c50054200300c100d200350703130000650024010124001444031a860700000071803d07241c0598007031000703650365040b007584007005801210014800200c4440210f25241c441c05060080c25005022060000805c400162070320b41210280601001c0c2901c1c0200e01c031a850b510046810f00040c00080042001007214a06004c0203410416040c00450a150810004e104041c072480c1d900e80e40301409000008625444880090161017295400f18090604c5801c00400c0258000c03103a101ba41000401e01098100301e250060405c0000f0700419200010300129100c261650462000a410f140c0c010081c40b07604c100401d0580e10840300118000c5146008031008035100103010031446920391060080795280300907603000460f4481c42c554986100211004448041d445a001a008184150304526003 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 237057859 1250 237056609 237056639
    0x605101101180215030a1103130201030b10090b070f0503030907031208010e0412110321010f0f0b0a18060306080c0103140c0c0a0804030b0402210607050304020315070504 75
    0x4402200b602c241503540090009503981d07203883c542003004000980126165007112440d00d10701345103281d49003042c03928494100d5080100740e001c00d0a1403140c15042c148402c1ca2094940d02d03640b2805071606084001d4440c1d40506004e461128402c03010901180b01800294047e03074010300200f001c50b1a606d883c1c0344500c050840703801800529401000f198442d0045550701c03650100030744504905454003030701c5183c0038010248051001090000302081880c011124a9401502d1038105a0303031032807110000da210307000303010002030642010010190010050841c1e6000c5080c819500d110101260308461016400400000d454400402c0081801d12165140c20f400786010301a10325400303409092084041c0090044410020318070b51201814041d0210456012020740ea44554900f000c164040c070a40d8142d10544042c4400944040c21845004440c0381140c064512076460a04c19a4136400080050f6094001c1c0048210204d0b010340d1024400d5025031100d50300c81e420420760100a805c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 237059109 1250 237057859 237057881
    0x14010f1e0608040206160b04120207080111160c17010b04140609060f0f120f06090313050105090a0b0d050a15030201020c06030a09150605040b09060603070804060605101101 76
    0x15040d4024405994411030166010350159a91030365a0781c120640484c9000c1010301038403d400450030700c0108203105148400320140341d4200d034003c0345c44881060884070500c28208400408214584500300001d03180f054441c0070300c00700c3c015165100c0408214607a46103a00903681d40d280300c4a1154a0144564076081c2d600d0307205180c45c0d00d01040400c04107000509071610a1070320080001150341c8080401e910010045d00707aa11422082c10425582c0c400002e0341420750040b400002c0c5803400002c00d50300d100ca114a0310084a903d070400540b02540039880d150740040e28000d01044a1603450000d00310f410000c1d100140918100641c0c0c1c08035104207074035030844903a407081000136070303030002d07581c05540c1707007207c1c2580d50751201c08014004040f00d090041032110703501e20520f1080982d0b4400401c982c0280e80500601d141082046104c91003111666030000050002c640d0a61181e24816406031003101c00107003c60712800080d12414044182c400054a1002e400201450a009940c2c2c5c1403 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 237060359 1250 237059109 237059159
    0x8060a14130218040606120b040c2405090f1804030f110c0105030a020712110f010204031a07020a0507080717030a0804020108040503040e0c22050306071214010f 71
    0x34158001603440da528032080d44460344103c046400d0010942c056070042c0303032440160020241d6441c0200921504580503950300441902c00640140307010240e80e40c6034154010fa0002d038a090f03606031540c0e0009035000350000d01510b0340080036101c000c0c188001c1d46c071032405966145030610313004107a00040d049410401000307800215041000240b14900180c0c00d00b0310070b480e555058440c074001d02034401d018080390000c00001c1506600428100075030b031041c0c4280d81000200021403030903446507100040c000d45002064405045444000580005640c41612803888041e03c9072854001c071a004404190001ea80030072040b1100b04c180601410803001444c1007540589000e80003440062010f03060002c51b200242c00c000e4180100c5000d4480c903030010601d800c080036170f881242c102651446904152110303005001480356034100845400400a04241e620020125007440c40c03030685002c3c880d00c1342ca0843c48810106a0b00340600441c4a400541601d40070041481c10b0200303111140d80 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 237061609 1250 237060359 237060391
    0x90d031b03032f0405010f0212070f0c0b0a051806130807050a050301270201051b0723030703030f02030c1005060f010503130f080d050a0f0506030c060d0c0908060a14 73
    0x10083c00a440c00c4a0007400c107001c04811981301070341010554243c2a00140000407030604028010100a50150051f06282e03500c0780c844842301c5941c4126010500880c005001c25004074078880303100d02c0c0c03a8201608450400140e603079644101b5000c0d4120700c1840c0c07c03188050181d8208080c0c4800200002c40083c0302503015142100c0807882d1541c540300302620341e0412001964016800c0780c40500345810004c156800c44000b05403184043d0083da0054444400c40b00300c001d40710282d45103d01c1004026101d4280766940a40701c120016444130f05601042c0100c0461230340610140401c081d400708003080324a4540300300b10f50100701d240c0e0241402810320a201d80c6400280c105500d1035070010350015015510b09014009019144200c10094240b40c00c2241006c620340100385d400c1c04c814010701c45c2e51988030406032030b165040502c6d0307005203041c02011440551a00210b1003618281802c0103541d48035144d1605042c0c7c00c42e00c41c6499074807015442d40034045400322a81c01000803502c0c100d0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 237062859 1250 237061609 237061691
    0x1009030b0907031515230907091422090308090d1812020301020d06030609060609060602030a0815030114011a040b04030f02040b030706230f090d031b0303 68
    0x1000052806240d805589280307543d900705e036a40c9080054001610b500d00712030051541c054907203010522281c041c94400c004244101e0056070220103031100e10084a0108000f20144032404090313483c0800031040c1913650380c0c4026482d10903403103240d010b0703980c0381410f1500007211450b05081c0700300a801c10148031901e030800103103100341e0407d40340030070900b0b0341d11009400080e002e40152021622824a800c50000401035594403202c1064428007061050030342e24102c0340704981e028890032000d40c001308840c50b0310714804c4508592001210060342021035124000c00d0031954050078608400c101c03038005000840040311890170000042d20300d54901803c007801d0345418051440000c080400800c1560110358698019554520001d411143c07015550140100b62103848000102d011210440d8407259814800071034580a001142c1d46207802941c90901401000b070301816030410191801d1644850581c04600740b00900a513404500c50b003455070700840c03241c41c82034003410b85030450a909003 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 237064109 1250 237062859 237062873
    0x30e0d090608090309060310050102010b150d090c1802030601110604030e0d0203010e01140121020d0311030d3210050907030f0603050a060b03030403080d0513021009030b090703 78
    0x7614420314141d4402d4503456500e83c82e5024003078515502080100820030121941c60b07843c42110000d90003400161488800d100c04080040741c221078551041102280c084010b8102089030f9210721030014465585900c0d941d044080d402100311321640000c1401515a8801180e401444850002d41500d0500d40c0e070151001402261042c024114074048009540d0b080d401705681d400c000000740700000c10281c50800c00d203001d0040903015201140101591003400124411440d4050b16191404074140c0742a266138560018030342d00d42c4401c00c0800c0414202e8007642d16805c0b03011614207521100d94044440c40c900722034070703c40d240c0e41c80020400341c840100120001c80301d00744c501c5041500c9007030040700680300d100e0804000c141024800400c000c000221000c02c40d00403002004600401c4003056143c0c4254400035050714020301590140851030fa00c5a900003440008030040c0d96815804a62003508513060035020454200042050060541a480d0b0082280001d803075400e0956032019 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 237065359 1250 237064109 237064127
    0x406050714091c080c06100801020f030109020c030408030406170c03130b0c160803040b07020303060a0306020f12010b071109130609110303031807050d0f02010e180a0c030e0d 77
    0xb40c810b030a06804003041c42c4544550341c000341e4001d0101c96450084082150b44c450094809100580c0000c0700050800010303c2610540300000d000645181d1030403500c14007a40111488901d13900080200007107082040006000800d008d444d00503039803418600c0307140e4601006001010b8920304008005100760070f040b030100d807075510000301c2c082620781c03540b8040b080c000c3c07400c0f0703601403000c0860483c03c1c800c1c1c2c0406507200394483c912818043e5a0354a04903101d000540310705820020300101800000d2860700500407044002c501c031414405e0451215140c03103800ea1162040250018812040c402d05005c038543d618815515400f40d4241012520b208186000c00602141e5803161100100b00703002044901001b4001c0803217840c1c0c14142207074141840c0504240810307104500000800f030514840140c015901302d540e5003c14401a001074440d2498075401591018941485086038140c442840d4040c0f89140000a6441c0350400060308890181c01068401d41c01400d001c8040342d840308a103 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 237066609 1250 237065359 237065377
    0x90109031e0e0a091d01090b01030f06020f0a1e0c020f010509040608010c03050601080906090601180b0a03060e0705060f0403020d03090810020a0f1112090111150406050714 76
    0x400700c0c2507210086039550900000268042c80e260000144041c807600003110741c2c4054501ca4131003030011910f0601700c81401c000100b45a1a610042010506003406441d20398015030000d4a0601d0501007075078164424500e20002c030302ca46c001d517074070b144540c820b10702881e200d4200b200980b42c2e9900000c48007801d01880b6410881c1c0000d406400d0303115a00640b0003000303000020710101640718005006000225880ba00091400f4000789420000040c4103008a0909000e04030f56400c140001d15000501d409480d401600c40c5210149901e480c1050300c0103600907000003d030001100301c003600380070352644036500c08c0c1030074007081907850129011501100c0e0304580e002e00f018030303a01d001c2e506071b0480d500107030007400b98416140b04644907230002c2904040c2c55030342d0f07900411030030b40640f0382114072031b640c552603845000030080c030072903101c020024000141000401030403014205c910345007881c84480c01c00900701301400200320843c010716070881c0c218200a20350107400000801980903040b81 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 237067859 1250 237066609 237066647
    0xb0105040c17130204050c19030b0402070f0b040c0602011505040e0f1006140603090d0806120d051b03070224090a0806180606060706110c071d09010903 67
    0x11981d801809800012400600c119036028a403800f08500c0c0d00307005440310113030700882c1480000380c80e648980c0100c2d030300c1d515109801103e88150190440007040706a0200b50004d60070042d81c800b00e07006083c5032000510800e001402c91800b81341043c00e9044960040c402e40e81030407ca04006c40101c1c9815003980c406460000341c1c2e0741c1640400d4680200040414041d0003120b281c55844025900900f00f0756900e4000b040d01200740a0a019251100b2101030b01c494010a9890a0542c8542001900483d000301102c2115004006d01801c041548200e0f4010420000e6030a40c420381810f4000b8200508d01d002d9800c005154011a20105103a142d40144803c080301120301c00c08081c0541e143c0450251035024403546071401140d03030700020313034030622205494413801451950001d0f5a07407007a60090851400e042150b1303100c01c040d04601e48080d8901c001802020140d140c00c2090f40001d003280c04041e208561440609040024050941082641042c4c21000400e4100756103031100890004 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 237069109 1250 237067859 237067871
    0xe03031014030a142a090f1801050a0905010f1112041407031101120b010516020a081002040f080f030a2d02030c01230708311106070b010504 62
    0x7000908040784018000e012410840c0007801c1d04000180c001d5141c021002c6910302c00100d030078030198038040951550703402444c0c14009801003003d1031105421038840480310641c9807200c1e14103420b5481c12905113002c00e60310301c030043c18807074240a050f0380c0c0307802500100043e00b1040c6108409100c0e00301c0d094601900c4801107010040c118000b5080d0401c000190b42015440385003484984083c0903075240050402c0045c5c0d00120220300c62015103803030503100d031740c5801000340d50401d0002120b64242e83c00000790300700040f40c00061040c2450790060401c0141d03110f0501d07940040141c220340200da07007a809200402810100082158507031106410007100f40d060400300c05600148810710840300c9051600b0962140d0340000c082c01c1d1f08a40c01c0c0003070002c44000035064080b56440c00101d440800c2032350120703600a020303004403604403904000c501803103e10a4000b84820702c440c48070f0384605809050550900903003200050f46900201c500c0ca180c03007415291481d9213403041c000e243c8295540c007 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 237070359 1250 237069109 237069149
    0x18040f0201020f150f07020f0a14150406050621060609041e030201050702070602031305191d0420010c02010807121410061106040303020a090e04080d0e030310 70
    0x424001000702c40e00c115107503041054918099550103981c404900700400d400300346c20302e001240038107844103031a00901240a4544031001103490b807461504403402a001c0341010040c010118030f21643c01000003240c00d0400005004020002300040800c0b4644c54440760880240803038026005441200c162034540c0303a50800e4000c4001c4000d4039419290411000404c02d5019040f20707104a0786070b001d40741990781da201c06a0f00c81c41409c0c004c610300c1119480611540c0ba02a10611040c888610f801502c03036225a05517410305036000c050725045030194100800c1080c00c80b8046050708002a03c0c140610340c110010309200c0740d054000741440460800205118440e0810002c244034104041c0f0008071583d05865040c1d805407507000c010705c80340c2400300314140a07059800c1d060242c90014480c1c5d41d55510110000d410920044c4100030b08950000741c51028024a1801356000e1440640d035046011200740c229414400070a500e504240304100700060348048070405c461411040c1c0c1d400704098 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 237071609 1250 237070359 237070363
    0x60a0b03160f02010b06070f0c081603120e01080112030215070306030b060d0803010b0f07170307020606040501050a06030c02010b04050f04020108070207231c0303150518040f020102 80
    0x540140288410210401c0358041c038540155104844644072040c4003140c000c0201d00f030350070844241d900440104060310014215500050203e40074140010b0720a444403007860a00703080078504058460081020f10501500002030744107c0030360b050000c11041820000303000c00c041403150100b01c2d61303386a124140740c000d1003480b02c01a030801121440703180c84c0401a00400c1a030005032243c3d51008001981414210700c0d0b402c00d40d4100c5c03441c42c00d607841d000b03c44031146d001c907181c0c03201c000d0107101603400a606641c281d004200064513058991505500003843c0540080030b107071040341420010441a02c4c3e022207102514a50700d8089000d091141043c2d01401401da803031500b0601c1c2204000d03169810020344c5000d107100340d96000f00303921404070480c0d8400e154007940055116907001003910459101d4000c4c10424040c013070121200d01d28242040b82d40c00c642d07041d808070ba262404ca10b0a070390546c064102a100442c0e0060900d400810000c01c0e1100c001c0000f051f040d1412030410641e03000b = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 237072859 1250 237071609 237071629
    0x1120f0602090a06030519050f040b07110a05010c031103100326030a0207030f020a0503090405150306040b010602010c02010e1b0d02060403050c040f06050f0d030504171b0402040303050a0806 84
    0x8042d2004003e65560703070001700180021503121011804060742840c00041c64003030203000c4c3c94500351622040d221500c2d801c110200142078402445040d0300c210110a10600500a199010341c000040c681042c84000c1e06442d400501440100f004000700030f204000d0918801c25a500441d00d0020680f002c0a580e42c042e02802035217026982c08020010030342284d4000304401e0340700c0e940d801c2085136040d4040c0e07602e00d0381000091280c2c1081c030460600c0c1c00c1c90352085500c6001d51010b0328110316180d0110b410141e0a9030140c540e0100000180306040e024065811880702500c001c216a00c4da071150149c946421225240240541d0200a4000c0e5101c0802038080c41c1c0060820b40ea6542d00c1c0b4010766541954007001b8000c90a007054100b080f0701c5841030350100c0302c018200340c0c4441d511808014048410707220480030300206000100346510b1603004c00c000f28126034000c01c5442614070345c5007440c00c0749e122460701c2940104010b10000364083c0645103008c200d4107021420341c4031400003c0030000 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 237074109 1250 237072859 237072877
    0xc050f04080f0c090121051e0105090105010b0a02070b090d02030706080103120302030f0708090a0b1302030601350a29090a0c1806080a030e030706030501120f0602 72
    0x10081000726210340040788115848400204035640441550300380404100f09129402c0700009008a000c4007062000340e0700700e6144190160fa403c0040e101c101d84414000d81890100c0d0b81d5580104512500240720f80c0c1d015080d01c0c2102070402c030100c03c0081d5580034074003500f4552200416035108a0310307410700c611072003580142540c0d03001d0b41700c03200203202100920003910700120b07800c40d9a0307040303010384200d90290340d201710110f40950741c60000340c40c1c10001500e40292403145510010109418800380c5024810b40d4540e44000030044c010075142400603040b4084040c04603501c640ca11005c819858885418660500f1443c4803c12000c0d0a080c5a56005804c0d684200802030310b11080d040070310040110100d40900702d0700c590104aa54408000d801410100d080c5821b0140f0071030511070502c0305118041c045504c54580d40c415041041c680c40490100c0c085501c402d01c2c0b85410f100907000313024607140802942d0b01d484159200c0c0740c00e81002904680c10140d22106000c4180c04941c1022 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 237075359 1250 237074109 237074137
    0x1090e061306081e10050106050403020f031e01020d0c080f0f0403092d140a21080c0c01020c09040f110402040918150c020304032a09020c0115180c05 66
    0xc84503009003c00d081e803421000a00500b000c0d0400c02a05201e200d050350a2075030b0f000d0038941036030b00348140c1c40782c0000ea0507030500c05c41c40c81500283e10074003011400e207078001c00980c40704815140b81040e162848804f00911002108002000c40e007004515031040b081030b5a0b080c01d03101c40c201581c80d001d0303e40100181c1ca2001e101d6808038030a44a2001c0303000356a0340350aa0296031403400709100e8000c11003031680720b44c95074010883d40320340741e014540e58000e5101100c81f11002c0d130745a1016900140d0fa0b00390503008161b1845281d07030140440141401c060b2154407880c136280c0c5c0e0780840a048000003c2607071006003100f28194036294103440c050300311503200300301e1400e10348e900000c0351180d010304450302c1494600d60488000c03070340520050805140c004504150843c0c0d03403518141d20382c0840402c44a04100c00500300344034051020001c0c0528040144d8a00f11034501c1400d641f950450140d0300c4110b90801c00075610700c0610600110f50306040040c81d050718100c219410311420144030942 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 237076609 1250 237075359 237075373
    0x30c0b15060a0216050904051c270f1a070f060f020304051f02040b0412061116032613050a170a020601090b01140f09061204020f01090e06130608 64
    0x803074002811103407a040025100044c00d03658410000024012074005203d500240d06e45c0400068803005a400d080850400e047c0160b0303a201c0340880d0500f0100c441d9a20206203c0810142e20a0b252080c050008407040c080c2940c2900d00000a0f40300b0703104000d18400740482540284212940003101400318210150350724207107030030a180d44060340c100300c1800419181c08020018541e2080740d0440324090721042c1498a0110941003103640c810040d28034076250381d250302c00c0d0b6000e04000c0c5000d1503105410203003005c180c10010100c00100303054a41c3c604580ca031500c581c80050000d070fa80001c401c99011142029860701034107041d01140001c0c40c3c560102c81a00b41e2440e810054907160003203a085615981e41e9034448420f88486204043c0030684036001e1640c8040004003c10184c5031251034940b40400c8080030881c143d2217031240c1c1c5c556580b640c081c0300451074004000c100062091905030343d00c5043c00b000d0421410042c0803144250360b450405a41500c03a0b0708000002c00c0c2da00151015 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 237077859 1250 237076609 237076627
    0x190e19020409020d05060111100b030c030601030b090708070608040609020f1503070f08041a040f0b070c03030b011719151d060a0e07081801020d0c1b030c0b1506 71
    0x394010445032800d04e4140320008915501c511009918260010010615801e14211201c0144000ba622a0301402801240b949988041003042d00079407044a0407203092170320360501c50038000f0700d80090400e5040a10204400c503071000603581c0142d0054400601109684001044140020700260704128018080c100c0c4441070300155125030002d46455042040014080f141c003801214020181c3c10009145051482e41403081c580c0944104251150644c0369103039101d610038112101000104040d08007420150316000b901070129003030810b1301a640044034101c0030050010305031039005031004112042c21007980c00401c100c000c1000829420b9884010021440c81e412455a4220302c0c1d200210798503040642001d01103422104900d0402d460783c0c08112440c000c00303000c4483c10040c4120700a18050203100801e031000241500060182255102030415179000080030320580b07d035012100826004458050003030750090f803200c0a651443c0003108084807000450b5006400400c1101d8 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 237079109 1250 237077859 237077861
    0x60411010318060519020702090103080a18080a1719030f0605121b09040213090503090907020a02030d030e031602041506110c03060c0f0a020c06030a06060e190e19020409 75
    0x1000d4204070b0403840303889055517203075016072007134480094004140c1c0d001000441c00c1c91000c2e11002c3d42520f80f00800d0407002810381d81d185a540c106403c680c00180c0500d08014034440c8811440000c5a604d03802c02c44c2007001c00d203581342d003521280289605c0746081508207080c1e80c407403c080d100c010700281c1034000c0c040f03c0c0741c2e940c900310704480b8405a01510840a520f80502158422640201101d98a0403103441100240c410448121590320051102c466240e4134400901c8c810000c0c1d0b801030140d0805401010303d0100001ca440d000d251a1888155420001000702c500d01e1410441c000311b02446072010600809a03814901c401100070400840d44941c8800208600702c0310004072020403400c43c0805807a01410b540300400c92a00300f1192442d41200b00c060200032a2500554446002c004081541c60703004450010141d503135410103000c041e4102002540c480d0341540c004203142101d880400210400d401024130000001c80052b020b0802403d2602c42550340500554403103607130300d8110b8 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 237080359 1250 237079109 237079111
    0x60b0a230a080c0a030807080705070b07150b03300c03040501180e01172103160207122307090c0908061005060c0c120c030c0604080604110103180605 66
    0x180700704031444000601200000f60003052400083c420070b90b951660380d0340946944100710480e641d85040c0490408160700303002140050219003502907560040e07240c90740b80c0c85001070000210a01e0149103401c02d890024900900008542035640c21010704040b81726080b18000b050b808030744001441e03090603103000c4003070301c2262401e884500d00030000d02c00701d162011003401108080c01107000104903000c3c4042c480308650303500c101510b03d01c00c4d201c0c41708181101c03217020550500710b000003800740600c44082d41d0100d803051880580401402c08545010744120780101816009414098545544d084401c46000078119070845a00c00e583e04082400341410020340c4002c289040b000184407000845c105100746640101440c42c50f040c8410000c0c29084102c00100c20302c900800c1c0c118079125031a4505003019828010803c0c0d175051010185000a10341c0703902e002d5070003031108115030b140009660b6045580010034215445460b40124000d1075180310010910741840202e0040c0300965101d5 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 237081609 1250 237080359 237080429
    0x21903020118080d050a030b06030717060604030b0c0d14090a20061605011e050a06060f0f0305040227041101030c0f08041a0f0906090c010c060b0a 65
    0x290942c46400511121480300e24481c10030f29400820303d90100f184030350001e0901382503078140011002001c002280700ca030001c844083c0894031445080b9480742c54450351a5000c00c04035915854181950f0710822440c0001e0452645550041000a10300a20340c01c86010000f5101c446901e40c64581220b03543d032a0320400950700c591b1002102c040744070640d01c00c0014040090040741c81e05255495451500c0303102030056449540e1041c4212140311403520304c1240407450840420341d410700c620340300304581c00713540200140841ca145c14502e45800c12a00340c542112810700203242c0d0340e5400451145200e21108035000c891a0f820140d043c00c01c5200780d4040d07401100c440302803540c0c000064080f1100450028040b540c503842010790b0350b2040c940540d1061003051018010100c1e1950007150002c103490509400080100308941043e0412100d035011071381100a0030890100000a4412030755500701815441d25803102e9141c0b9120794002a0090607000072100c00e0a1001007507403080d0b10b0380600 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 237082859 1250 237081609 237081617
    0x30f060e04030503070806010824030a061514040b030c01140906030a02030f09061524070602210423010e0d0e0414190c02070b040305060a050c1804180219030201 71
    0x307e09a544540c40d0340b0300c2142d81440000f20016000420001d41070b1000810390306108031800c400000349180250104280701090b160450790420810221411440055600031490090060b4050307400003041c2000c404282024000c070400b49001c00e01c00e00c180c554850304008004140314900207a41e000794810140c210a440340d41c0c030ba80c03540b5903c41d40c0540300c03d145100205405c02051a0442c80380e0000303007c03003051183e00b0540356000700380d40c1c00108054444a41c08200140321303001d00908007160b604040301c840b001e0f00c0c00c1c0c2d542000004504c0c0c0740d2400392900b0401100020000d603c0040c0c50b8800f40c0454840e03007000301d00105081148608140601d00b070230107032020b0300590705801e03014080140017540340b000740c20001c03001029444842000c512030704000040008280300203002440c0988041d21092400580381d90646901400596064204001580e56030000100c2c608a03008122004680380c018203540000c03480d00c07440045c0d4401a03001035810340103113509004003280d2007130302c0e = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 237084109 1250 237082859 237082861
    0xf030322020a090c0c02011b0c210c0b0a0206010f080303070c060204030b0f09010c0f1209020301090b100e01060e01051215040f0e0c040e060a0c05121f050a08030a030f060e040305030708 82
    0x40f80041342300304401005c000741c0007420700075200041e010300070411400d1402c10361003032240c856411307145644d40100b02a00001407458001035045c808540946540c0b44d10701c0794503140000302a46d0384001021241001841010348003007100301e4048600a54100b07007820034500301100780301602c0700260350040c80c3c0d41c60940f10b18105400350f5a0701070000c00703540340c41b01c89051103484800503201004007203034503541e1031004030b0002d07031105055401401031780514405079061045071115040181c00140610040391350040241e03a00804882c2200c0500c4e10180c484e845000b801030820080c8000d0b2540300e8140008000130555692001d044590020120b441c16500703001403000b11814455004102e42018000900280031038000107940300c010f1820034540a40301040c251040c0d825688000f400c140038410400e8141d07002d2503000540070450b030020314a40303403070440c1d9a00e208114401c410315440324100180a81c1d2548004000c00030100e20b14a80d03d403915000340158401c40e404030100d41e0b480 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 237085359 1250 237084109 237084137
    0xc0305031b0d0c020c0111070e041412030406050901060f0302102016120308010e090f030714010e0705010914030705040905010509101e0b0f040f0606020f030322020a090c0c0201 78
    0x1c0d0300c41f000c1c410800d000e022007a090004078208200002c0046c0c13000c0c0340065944401060811000300303894029908680c4030b041500c3d04909445000d000d52805a04088003482043e030095030740f5003101da0454200c81d0f40d2490705026106005c840c031486818604100503860580350200700ca810b100d100071804503d40b500c920600351480700c9020050000790314040180030352000e40340704940001210080f0f0754800c44a5407580c2c0f643d41304034030842d1070400034001222002c2c004d0244010103c41c0c1c8003e0302e4150b003404002410340e2518490022003c01d07600c443d10464a0501c15540034100c04ac00a0205011509005010b48000d9515000502c030390381e41120072101c03600c11200c440c0a040504c247c0301031032102c0d1030090070420154a41c801904404030400c3c4c1c0d541c1c8565402d04c02c0008003c107880d0b1802c074002c3d003016055141054590400c00810941d5003089070310015207400b800021503003140c540080751000030382d5000342c034205240105498a041c0c000c0741c081c41c4640300744d0790020109050b03 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 237086609 1250 237085359 237085367
    0x4505090f0d08090d051e040308121e0609061c0f0b06030d050708210901060801050c0a0203030609100308070506160c150b010509040c0509100503070c0305031b0d0c020c01 75
    0x121030f5410f03076070808140901040e118900030b100c484080d04070600c08441501c0c172210207600581c01250f10f01c01c005150301102a00b80340b119884104640e0b58850000940b03208100355000800d241c3c49040940009102680c0b40c161810b00e02e2640c03910820850402d15106140000c0004140c422020540000305c052500061071a101c10255486a040461568928403541c00c64a064407401007071044251004500a52251050401400101d909890180f02e40d08454014000b4070f00c000040101c01d0700c1540001c1202c0e0092000e0f101e41d00035030b450140b55a1540815003009004410000c1c0031804e01c13030001500303806000301402c8590070100c00c4005480e01400340070000e00e4a146054061071138800ca0340306c0003032801c040c1001881c2441c0003001a045a0f891010380020400c0403d851101d402e010b4410345068410342015465820094000b412442e200c803c010100400013000901c0050500c2410164828415540d5224054180306802805040004100503c900c0d2581c0040c0c2d840703 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 237087859 1250 237086609 237086611
    0x1603030909020c15191a0a0311040f090f0c0608040201120e07030c0b1201120b040f0f0206030106081801050f01061116030302010c08014505090f0d08 66
    0x85619203091103440c04012101a4020401000c02c501403107500d903900e0340d0003410035442410306900290a5515202c3c105003100c222490300c0701c001e007041c100c5901035211180d840c026281c02c0070f40114007450b840b00050203000070712400450035040441c0003081103500c3d40e03070710306043c8140944990b40e40c44a0f421941000c0458000c0d000901100e46800d110409a101c03180c1050719105603031640d85c036a268960030f1b181f04e034012001f002c400551461015120f11959000d0401004000c014070f0540c0c840b611034280203407001e441400c038001007404001c2d0703144080480302d81c0500390540b0b0b90303526200540f00703800481e801001340640b5039540250750818420944942e00481c030500b0180d0a00608603a0001c4004103c45c1074415190888440c802054046000714071070360020614100d00c0c100101018010b03402032041c401110030319680c6200c0368694104401007034125030001104c0031405031603001200e621151840c07424040c0248a08045001820f090702c407030456260301540c010845844b10 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 237089109 1250 237087859 237087863
    0x503100203061e031e07140d1205090a0e040807020109050d033504060b0f0604060f0c21030902091f0b030406020c030406021f0207110114040f08010209031603 70
    0x250181001d040031044001c1c1c40f841c004058100c61100c0010040044140d40c0c55040c11410f501120040000c5a1f088000110b088010707a403d442c001c17640d9549045407821071180c2802d002c0c001c2004400da443d403281102c010801105660321509090400000079840344509134001020420301060074101b0010048040f5490ba841c5501c4490708010818441101c0059404403005c40300034400750040c0452850082d0b01a0700d001691110171380400903041c4904010724042e070402c1c0002c0020300c0d000113482010f2082c42c208940c00070040d150100315440604104042040c5091079601d000390b15134080d04540340300b80c1c2c071b981c0b0342d4443d441d0206840c080e01e00c0410340104030300030901034884c00001071504988980d0025040640b1034002c141550015000300c40140c0c000c415480b0b40c48a40c411400481c034610300300f11700d040015164011084020180241032000704a60004c1c141a00700454004000418041c408682c844007028041c2d8030030030126120740310301c464020300e6510010b800c0084030303 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 237090359 1250 237089109 237089119
    0xd0f05011e0f110423010509130f06061103120712061206050705340203010e0d0e011701050d0309030605070c0c090606020319090e1302010f090f0b090411040609050310020306 77
    0x2c4172000410343c048140c59803050401c00c09020360545078a9100c469038030000c0e80100130508075802d40c00b640031290076038460f41c01c02a005151464502010046032418001410802d00390b0343c1d1840c0983d45d85a000d2400e80205180041c005010280b0303120703800c1014410a0140074a4880346411100341c081d00c202c4124414a00e941c006540d4007580c100307000c03000400e000d15006075903900003a08407100c0d2020301c0c140717070000c0710009407599015070782c2c2c0e040300c1003400e00780010202c100712070801c800c1c140101801303844041d903c2400d06018000315002168000014062403404100050100c940404d08545401c1c800c44041120225406503409540583d4001c40c102030041000c220031140350312182c0d051055402012800b417404036100d621684488400e10042002c9200040030082d80506c1c800400c0300e6101d00384500d200c003500d03401c1103c111401d41d544518a400000c0c00400019041f144600030000d40054555006940d80c01158411000e44071850781c060300c0e8000780d01c01142c8950303101c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 237091609 1250 237090359 237090389
    0x925050d0201021f060e180c0f030a060e0d18050f0423070c11032b021203011712041202010302030c040815061e0d0f05011e0f1104 58
    0x5090100c20241058014411200c09150004090450380a1141d0214804e9143d010902c0006802000190807182501000130044003400c00d140e15001442c0f6454460260b0480d04480c0344c0c0e04001c1c40038050f0708003d040203a40001d103602607a0f41d4031a040807011030b046100d449411f01ca0700d01040102d440180114135140c2d1240100001045089801d039a02000c007044007002aa451000754443c80841d101e4102c01042400c081d4442c01c292109544203900985138000310841d00d0004d5104450f0000090018000070107050781008070503c660013645202000000e254480340000d81c1c0703051582c00c141d991035200040610312a204500401104184003c0b1100065100c6d500442c0d016144c0e094142c2010b8542c4c100a05200e0f650050a924038162410f204440c0b400041c1040c580606030305014110a201022401101240101400440007060034005000083d0021071664007c0269503c03080a03b000341d60080c000141ca2001461402c0b841141074840c5408407000c0d118509001028 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 237092859 1250 237091609 237091619
    0x60509090c13050c1606060905010e0603030703030b030c030a05011512030807050a0207050a1401120203060d0605041b0806010609080c0d060c020f03030a02040816061e030e10050925 80
    0x40e0070060040801d241041050011060f41001d60700d40f03c0344151b0740401c4141c64280131000b942c1c010b802800b408501041842095600001112070543c1e1508001c00e410000c00c0000c1e0a001071700d000d86805000b020015020040103600140307409010303442d400c0c9015100d848501c40001d0201004000c20b13000307004034010b540a0805090141d14600c111408a61520082199418154442d0303104407078038159141d40d581c00036095090410300c540110304510700407001070070242d600b02002e42641d54070801308080c08489220040402d004000012101e80e6410f4416543ca509100d520005800e01401050030322010a9419a15000030320852403611691a01d0000386050441481544100340301b881d940c000070f00140d4415100598016100e515040c452820030003082c494200091100d0002c0c861143c00034110346000031410380b440c002e107031460001e030010b042041584145201b80100050070003600e4001c0c622440300ca0050f145410b090078981d04e0301c0700b17406c44043c9070f003080c180741801 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 237094109 1250 237092859 237092861
    0xa0203071b0306062310021902040204030b07110d18150302070c0803030106021e030d05220f060b0f030d03020c0111040b0705010b010c0b04060b040603060f060509090c13 75
    0x210342411480325985082d0780356900c0741150007941c041400c2503031454994108202000f80303c0e02850050b604d000e2107264010000b5251125111055202045042000107540b22a41924069548514600d803036080101014000e520827545c2412140301d15442c2000d114420711000c2c0d5820303480c2540e2010241480003000b10030010810002c20583d00340b00090120310b0310b64000c001007035208040c0d43e030380d4100507000f030620980031381e0841e800803c0141210303503100000c21107a00f1003507205c001a164441c0742051b035001d10710111007100c002e400e06004e001e20041e010240300e1144030306010040c041240007030000300b5019204c2664540c008176841ca1441d4001c0d0000c200c0303a01140000200c3c0c1040d08070741c0b1a99006a003042c8107104003c81c1c80010403100740f1640c4142103007402d11440f00850382d0b03038519407498000d0006010270388442c400ca9060701d41c0c0d0030610165038094414000d0506410034100201740611035603100d480c654000c10b14009010441c4c2d070302d111303019000113032080889040b58 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 237095359 1250 237094109 237094133
    0x12070809040915090c0501020c01030e0601090903110f01060504050f01050d03030e3a11030a230a030207020f041b050702150301230a1419030c090609060b0a020307 72
    0xe9001e1a620028050f259010700c11501d00600c42d0000004460500000900e00390f003100c505814140740c007122801c10301d00024400d046810000300442c04490300c0c075085410ba00b021100c01e030301e44200c2d00500065001034200d18141c8400340d90411080d5140018004800428400c0300d80028001c4d604001180c480c0c2c21003109440b603c022074402c64900c94809983c00c481e1240034080d2025a9160044001d081c03441d03502c800590f20302052441d05040115481340300d09202d40086c8848500700d048040b5000b401811044074007951292200e42e4041d001e4080d40c01001c040748120600c901c124071f6490316126031500072001452a41d180c80b105941a94a50b100c040260323485042908500070415110000354080e0040700d111000309803813070384240350507d2220801031050480354014817900ca440c41c200711000d01e0407582c085441401180108821907660405040d4039046803012401d0342d05900401c4c11504010820003810b40d480240d00d509000708945840160410820300c0082032040e0407035 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 237096609 1250 237095359 237095363
    0xf060810080303070f030e010b0f121c090302040b03150109020d06050603090a030224060103021b0601030615080106180b1c060903030e0a0b01031709040f060503120708090409 77
    0x803155003a19444041e00d5078104a501a0000341c4680c522070400390f00d802080440310140e0000d01021410100040c2204400702041e0f0090000e140ca442d0a44c6c010490003044010b00d034034582190b600c160004001c000103000580c0214100f400d5000c041c1000901010200001001b00c03440e40d0a114181019500c1000da041c030b266200c440205041d95850000c40c0100000c800a1580203514a0082e040801c1a404820f1500e001100440d40c3e151a0302c10940c040024a001699902d01e0080a02030034144c3d03041c2c60700ba1103520300100c1000a2507003c484c40010382001410400c1e9194401070a9680c18064a00b0074035407420300030140c01c071a0b0884104980c00424079280d14000020242c00202c145005441094444e00d6a03818585c041c805d46403690042c42c05040d218a00b6100e840c3c841070b06201c001c1c85429103a50601004200005484c2040801041402140800b6000314003814150169620a010b501c1c80c4404654160f402c541405600c08075090034000404100802850fa01a003 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 237097859 1250 237096609 237096631
    0x2060f2410030902090c03071434060c020f1b0a0504090309030215040f05010509010806090406060f03080408010e060105011205090a060f020316031811060702040c09090b01090f0608 80
    0x10140140e44900c0300354418030080c0c2c00242c030b9242c403400003084209c5d035020701610214100400b19460050300c0d0301f040440c4c182011119a140075121204003480408000780c27000e4030702141c541c0398a0340440d441444464141c00c5a115087c1100f20104a600e400703c25a88001014010000d81c103080d00018101d038000e045c4551070b641d0340d07004034036200b000d481b4071043c0500002d400d2003551a42502d02000e01402c2c41d0280c10840014000380c001a40580038901c14221000050b003045026003044d030140101a40c01802944e0313a11701103490390070074096158a5401e101d5081c06139540001c03407d040300c505941e40840000c0107080705004180281c03041c0c105008141c09100850040c3c00f443e80b011034491030050340c903e071905d0340e00522000303081440101400e100401d202030001030310500030b054001d0901ca100d291417400241003032080c004000d40150403c01c1c07090791640c001d03020a0881d24101c2007800201d4000e001101c2402840c02224100c000c04030041c0310b80c51051280d10352085807581 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 237099109 1250 237097859 237097871
    0x2091009060207030308060d0501020c06071101110406032f1b2113081209030c0301060e1b04090905011d070605040e0a240f120f060b060d0c02060f241003 68
    0x149c15007a40e01c110030381c00c41640004244405a0b501c44112000e0360b40c0c3c88000c201550101203010490b101d14461002059150b0404448100d5801b0048194442007030f0044400400c0c86074000036604800c11525005400004401c0c2c04680400c04041c80346c00c20701b00c0c1ea50400c5007581c0032103a40100311200384214030410003003101c003c20009400b088450f005c1082d10b030000d15040503e855070030b40300c00e8080d9042010401909031907104403500442e01013a014416102c9441400c0350380201d034000119071f82081c0d502c00c14010103501144407070248a194904100d141e000c3d45036607808500c5000c001640c10002000100c41390500c0a8104034179420102ea141c0c84c0422492615041e00310207150190b5100c070800045001c604484000e01c0c038110b8500303004000340c50300b00c190513403880e014041c99140c00b5440800d40c1c91408803008610b40000820541002001c000c1d59003c08560703020140c041c180100e030250381c81380900c0c00340244489800b03100a10300743c18010907821803021482415127400c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 237100359 1250 237099109 237099113
    0x60106110c0901173d0b0102060a0c050909101706130605070c21020c01031116030e121513080a0f0905030106030812010b0a050d05040c050901060302091009060207030308060d 77
    0x45415043d02c240d01700b08580c10b808141c900c610324100110840c1c4c40500e030420b0100140d0300450100e034000c12480001404d916040d6050303680e0310406c0e00c884c4d8080465401c010000309114070310015618041908152204000001c950310032040d124034038080303400d0700c9440c00144260011a480080d034035010480c3d952a598280c1d401d5a901ea44045d51072001c00400e402c1076040201440e48102482c0910007541000d4800e00c4a11506102c080d01c030809000120a25000342556a924400039041820074040c071a01192296001c1351289088400c0e01d000c03501818414050070344207a08490740c03030304d40302c00e010080e103004a0795282c40e014070024000c005074541d8284a13400056026111541d076035021044090460401600400c4241c041440b8000c1c3c0150b124080d501102540327000090152214182804030b100e4a9108550001d10200040354131a41900580264070003035500c41002d401601c01034540090602031000180d00110041010904c03400125800860242004070316400039 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 237101609 1250 237100359 237100393
    0xc03020607030804110405010b0f4009020a050301140a03061a0114041a0a0507120504050102150114060703030902091e0106030203040b070507050309030a05060106110c090117 77
    0x704070181c003c10150030402c420701c100e2442c000065101210100079641c101034003044240030b000c03c448022080840c0903146078040d241d801042c041009c43c10070b50b0603406140c3c100c1c08250307a02c0c0f130100560020000511159180240d480d81d94464030f500c4c0c00c0d40e0801902500c0c01c140e64580340d0384012280d00001c0492030911921500c04000c03d00e01c01c1c0c200714240050b02200340111640c6151000f00301c00c0003403000480b051444510f100f02016070350407035841c08440c903000c2c0311000341840c0051100e03040300c16040030040c4100c0d1001e80a80351251074804044005030400d214440708060071028859052800304020040f41d072180c1000504540b4640128a003d2804c80b010703081640041a1300d070503000390b680310302d0040890703182c2940b442c90a59a1114000000350509090050103da810108a000d00a803600b0f00f0010701100d402101c81c0c14603a6a81c1030031f00c140008a0b111403d40e4181420100c2e510407851805404003900d6403901c0700d010340018005207484414007507001d03079030710329410 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 237102859 1250 237101609 237101617
    0xb03130201141207030203011401080f060918070602011e09032001061d06031e07061d10120f06030c05060d09140d0e040b0d030806150c010207050f0a020102190c030206 74
    0xc4c2d540058603581094074400ca030b01c50343c02840b414000b0b03000800070448158000c1562008081d07a4916042c0c5915502403000002408000b802d07000340100404e8965055104840842454039800d07854a0141d0340c1008680441a000c0d0004041c0c00940000040015500401e4031584000090780350341c928017184036100d0700804601080e0060240540c51408012920b416040e05415003a080346003540e003591001d070b510038401440076040703001100d510f080d204030b000d600380a858400f6090010300001c5c03030101202c1c05c00e40d14514001c80c10b5030f0a9941d10484060f00c0c0d10020b000c511506020070094540c01140c0301c0c602e560748039158040050f0f80d490701c20500807030001c01041d008003981c001820b031035000c1c0060b6014a190040318000796507046192640c8035003500740b44d5801d84a9101059070303404d00c0500400070410006000c0d2010505600034482103020702c080d80e001d02805032006031a602c04682c047d00681c091443e60203468030801c018102c0d01c2c8241101e07030001e0380d00e134042030140e04 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 237104109 1250 237102859 237102871
    0xb0f06030601181701090b09060126012a020d0e01020d0e04020c0a1a06090c121e01081b04151809021009051f0503130602070209041b0b031302011412 66
    0x144501746c41c070802a4a0b458076400103c8030380548441e604003090303941c48090000e0501d0144a42000c0d904039517800790700c43d5006241c0e80f16080c401c45586003210051707114000c28280140b043c581e4100c032651084030b05072401c0301c05901526844000d500308072281040030b108070b54081d07420496402e44070800c22105031611f100740c0c40000e0102d080c1d40740306000c0c400240f0071401010b1100c100801140c50104441140049441001c110b0f02c82c0340e90030001c0e01607440c079121000103110001ca081500000c08082e8030001c490b11114100c09a01404240c540a24000380c3c0650712060501031590b0b206094070a0300010f040003e6903003104d03000901c0070380010b010b0700d0114101075824460342c10913a0f441c2c0a60482c1081071040c0c0504820020040e2100505082801b40d82c0a411801c1050745e40443c2c9132140c00600c0ca1495080038200a103690360742e0081c00e40000e841e20800240b42c0c00d46070641c3c3c4120074905800d0084c20305a00152240003802c6c2012940000411503c04800b8402c1c040c0c40c0075403 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 237105359 1250 237104109 237104111
    0x21903030c0219020d030c0501140c1914030f07050d110d060b09030606010815060d050f07181512020c010b03010f020705060c0d060b0a0809010b0f06030601181701 72
    0xc000e000303001e410400011908102070203c0ca03040300240c0c440098020b407182d890300e080c8454030a01d080c00381c01015034070345040a283c01c45c003d01407001c0c0c880e806400041a8040c40b000107807a8450300f6104c06007803909400e503681051000800c0407800b1404640e002209051451601c3d4684000c401261001d840d07901800744013254201100109100310009072202218461500ca10078000039624031000780098108022100081e442000c01d04400c04010800303012191a240c2c030224402c0640390407a801c0e600c810a4200081d1345901c00c00c258421000c0401040303080e2400c140800b100303d0000d03080c103010b000450304a40d106a07528801000101c071080c000041c001d4001c000c050070344e8140200201000d005000341004a42e020030502c0e008403561880c00c1c7da031541800310501409656002c0600d0901c0421080342c0680c101c0621882803105200810044042404005a11203400d10ba642c210409000141c4d9a502070102511308521503043c19554030346d21945080700030007008954082d6 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 237106609 1250 237105359 237105371
    0x210050304031e120c090f09051506130b09010201090804080a0c09060f09051009090c0303170403090306020901020f010e070e0f132409201002060a0b0102190303 71
    0x850703805243c600d00e4041e1941540c0000039030b544001c10380d60561026078030786039448a10f0b107056802120020300078843e0303081c0703004959640e51214008000c1102c1c426041c001981c665610741c500401110171118440c40c10b51081810301381105807517040001494155980c841600c404100c0c20030140004280160082000b007041d440c082a0030072050307010602d51070410b00248090182040d1030f0094070165000007030b1582d988882c7c500a201f00354440d000140c9450100b609001d03d40340e0050175a0b001c0c0e10360000340641c10410150100c0110b0f00034002992890381480003840640007800c40900500c111001c10711501000c90840e42050107801465001000410400546142080c1d1107444485041c986143c1030620074008000584002e2907500c41c1007000305104d41030556181000000348041000d05505e1800d01d140220200d10001020150300d410040c17481d09601c00884c680c03850f8050031194450f030b0f0006000e400700284e00c90546c0120a0020480001c0c6001e80e15424002c0d81c0220350 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 237107859 1250 237106609 237106613
    0x60c08041a0304050c0301090308060103091506031b06050a1d120d050a0e01020c0a03030e060c0d030902040f021801080604090203060a0b0406051008010312030e0a0f0c120209150d0210050304 84
    0x6000305d0000441d0082c1d0412592030b000c6500004242d61110303017820b02240a0b185442d0064000301c80a54071201e135032a154001c4180000030452105000140c84022115910340e141a5018003c1c900c01d980002e2000203038010000d0280d004066041016084040031200d0754085810501f42400110002c1c4002c2003810075a540003c401810310301c2030000e4803074942c448002c294800000e000103824458400314065480d210380b4115443c080f00441a20300d011640200240034084001059100314101454029600c90038400c40e55a0400802c00c0c9489200a40041d80c65034402461541e016684800140160b1808d11a403480350554600c000760039035481042008a0302a5013199026a1001c10580c4800b508082180d06503074208050020802203202c080b40505016180e001d20340c050098450b08200c07504403241c2c043d9215000c0911016121141c2401000b958000a51310000e45808611042034000c0d0705002000060002100d03414250081003d0181c151208030004e0000020082 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 237109109 1250 237107859 237107863
    0xd021603020f1207020303090913120e130c020c01082d04061503020901030809031606020309012304050d0c150c0507050301050f270d030f06140a060c08041a030405 72
    0xb102e5074003072880384c0c1041034540101c0d40d02d005544905000d03955503001306a2001d0106107014450b0f500c2040017503056940d0384020301090314207807128055440c0354032503004400c040c0280041c031281a4000e21100e01d0040044881002c00f0304005418212144032a0160307143d13001042000c135207903130013040c2401c1c0361800a044801015a0800c103102c04a0240016074424002d50704403030700a43e02980342d184110020741007103242d415083c03c89905440000c0c14075004030141c070320000c0c01d07280c00150030000200b020110300c0b983d5145402c030b81c040005106a10f006245140d03858000c0340ca00014913107a002030000c2035100d442c0440480c1d4401c07071034400c00c80d08100c810b024020560003405a401d0160039041c0b64280a031001d00c40d139800640e0055460004a003100c54200b5000c1100c0f1541600000038000302000c10040c40158108500468005608441c0f00c00881d030260000305900e1034101c049803022802d1000302d0383c1c0802040b00049070700910400f26803820703411000c00d9403820700e450924 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 237110359 1250 237109109 237109123
    0x30b18040215130e250807090f0905010810060f05010f0201060f081e070602150901020c070b1b061603020708130b0415020d120209010c0609050705090f0112080d021603020f 76
    0x1212980a8100c118800582c45d00038119074011410020f240d515100804d90307450015421002071880c1f0b0040c00514a10305400490494140c80190b9101080500b034000c203031003850041e001402904081040594411040c000000d41c0c01d04c00082c56589500b11342c20b0201d41640441381a61045c02d040c48204000d03e807083c604144100200003052030807c02a40b80e41c03003c904400c419001d41c000038840c00082d01206c2e2031004c0036042d20111510b40b20b02602c036800c055503540f00c03542c00500426220f0307400942c4070b0003400841c2c070410741c1ea02844422800396100003422140c5040602401e100e03070440e200c00b10080c0001c0d611141c0c44509002502130b412412441d03040856202200f40007000d40c00c440158510241c1c0c00025a480301d8a41c01615419049180204118034010651017480380200341001075460483c3c0b001d541c1d494203c2ca040078a1802c0c010000d9034810070038940d00080540004180c10038645a0241c1440780411042f0f901103000701c0c00760050b0300000024142400240414 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 237111609 1250 237110359 237110371
    0x213051c0c14120303071b0c090504050d08010906050d060b0d020306100e070503070e01231204150c020d0c030e090903030405010b03060903090105070507170a0302010c030b18040215130e 82
    0x4c60130b515212500600600095294806007801c40a1032010300628016a4020f0440074805000d01d0409240190b50340e42c550f0070b20030000762204008581401107014030b03030454500602150034200140c80345030082c02d002d8030307190744841410700410058406121481c80740721041503400415250024561300300b9070060600e03007000310030003c120a494004050401d551420b00c1c0060f40c3d00b800113100c9043c0c5020f4600c204060401142c0300342c1c0c50074180f01c40341c49075205a844070705900c8400c40d02010340383d903400f4440244c6c02c6a4200b9140030701c01d906c000c10701400303490001002040c00002c00c1819106540001098000004020511000b40204016400150000c0a00303144c021451510390240ea1020782c1046000640700741804030802541000d004482c42c1c04001c0040f41304d58542d41d4020203001c80265003000d80c601c03d143d01074400c805980da409419000400c0f030035441080c1c0e120000b80200d0344074220710010b2040c004148040d10342d00e000d1a1090601609080c04000052002060 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 237112859 1250 237111609 237111613
    0x515090418021503010612091a1b0301090603140c01050f0309120f0a170708130303060816050913020913061d070501090b090307060e13020d0c080a0213051c0c1412 72
    0x48e030b4006000c2c0b410401c00c0c2c20640840c02c1c1c094882c0c416110308200c90030410791104001200106180d40541e200c03008880c801c16101c0340c400010134038181c0380d40c0c094402501003402404540d4051030008002c680c003620350b400340d40040031803014051580e045a10090200040414003034052600104003c40503c4440714501c000c0c50030700700003051070300000d01104075000405101000c16029406c45c00150510b0304c2503654150f10003040201c060605d04c109885540c220000c9500b030b0a0000040c05907540250800740580e4607203400001c18099110b0450701e20742d0701e8441d5003410700d5924044e40c414413403001801d2030500c1c180c001001e81c85940c004804510302004030b89859a400a140c2c801c596180c24805c0300c0c2c11101c000110000352140303030b8403500341c0000782110f902800f0b0391002d16081d8103034841c081350783c640202403000c078081c0024146d9046401e8505000c1c51504492141e140c01e003503a4086109000c80d40e5080e040d0165611103598180c01100842c094946800885150084400 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 237114109 1250 237112859 237112871
    0x7061109100e030102070c0e06011e050405100c1209030c14060d05040204150f1a03190902031002210c07020a030314070c1d010515090418021503010612 67
    0x1034888400082450601600c85102c8085072402e40649445070340041d0407000141d0768103450703081403108694440c0040c645003d42620800c00100031805006e0a50b54203041074180001c2c00320042a00c1d501c1414800b041c01c45500003190059140150070940e507603069509e1462a00401845054000046030f1100038004481500c403402540c07440340541c1808546030322240042030040c1090440e00050301101d6002042038203800c0b10020444406010a04280002d612000d0107404184e690544200e2000440b0010040741c1d08900c4103940014141c03116503000c402c4440490b84202007103043c0c10f5100e04480c0c44105400070260b07100b0009803000f4075040c000d13400242d6030801c500004051207820004040b0340c0c2d00e208269803e0a9011030f410310340603100d82d10103031400c40d51301c0b038030310262456000070400c0c0c00c0030350000b10300c4000441c4082c10000030700c0c2080050701d50300e40c01c0000305241c00d1014015a03248d00ca10006401540a1345580303505222008203001c140d410000c40311800c141e = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 237115359 1250 237114109 237114127
    0x4090c14011701050d06020906070807080a020f010516030c020133050402091809150a0506040e0a05060721110c0d0309050c0438010215010e010b0c0f010c0302070611 73
    0x1400d09005030382c01032006a030f6125407070009d03000d805604400f520407140400c18034200310001d0b004111840d00d5408440388220b80c2c104043c03d80794229402100007114440e41c44403640250000a0f080409000118404000800c11049441d10203401400d00301405200392902c2840c80c03101c1c2c003a00050701e0542c90007100f80302103214200031150226802d070800c000142410401d1180306001c840b4200c403440c030b5092404400d4081c0c04240c0d4254401ca142c40028904030380002424894154000040c0410307a41d0071105880304444210103041e10303603900c2d4080e1281000e6106d4003505600040e001500d038481024841c1c42c1851b01107042050525240007080890300014404450303900486001c02c1140381409901c80681048c06480c00c4029541c401c45440482c88070480c1d0440c8080c0e007240c070300f0300e0400c0068244200031710640d032000100d4030061101b2420100205041101d22040f80c40140241242608550b1400d8000b00040d601180480c20051a4022005920591031840f418041c01d4 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 237116609 1250 237115359 237115369
    0x13060803070f0302100c0509040e0609060612011d060f010b07030918020409021602030f012903030909040c080105011a0307080415060303030506150301030b070c0204090c1401170105 80
    0x405400b030003101079616054100740c402c02000c00c18021500c41400440503038038000d44103800049016100d5030920700e45210f0654005480c500c501c07100c000810a030384a0409001c1a900d0000c4010440d5480b46095080b180c5900200c03445078007500c000780001c0c94251401c44005c0700613000201c1d96a800c1040d0408070354080c444000351003c40752421480800d0042c0e140080c41983c2c0012682d034000304581c2041c00144076220700a42c0250700769003030709608031041c500722810300300201101c0c4000382403880c101c840355401552002d8048c0c11246401040c400003000c0c030b0401c075021588050004014007800500b80241d0b4010007254204100780b10504807a0847c600000b4407403010420800c0001c1c09100c00e440c0c3d1020040702209042217140c1e10303828014050101110828010381b6280d502402c640c0456044038101c0c0e405c0b40840b892034407043c5c4200c4100d000010140e9002d0f484040320030108542032011801031040403c200b100305c442a0005d0302040020808050b6601c040340104060740b91 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 237117859 1250 237116609 237116617
    0x60c150901140103080a020c100c14060112061d0a12030b0609091501020a06020f040303090f0f0e070242190e190804060801140d020f0102011b080613060803 69
    0x2c000b00c940d844a0300214108d107001c101001a0758008504407540d103c49400c40c50403000d50b07008100c0952000d4a100c140369807641c0a214004045119021120100392690700035000884400c0c10507040d51020448913142801c207180a4898107017000807000f21640503c070b510741c0d040e825140c160500d240000000c4011000030f04d0341059030444501011168420300a012003e640490115164503421009008640040c0011001f0451900b004a44041b03042002b4046811070294a01030704e051003081d109680002d03000c070007503200d0b00034451940120800c00c501081040004000a8015080f500808d00041c51801c03d50102c0301040c49420115074400d1b0926401001e404640740604000382c6140c05601c2940c0c9603107912150414040020490081003290000d5607584907507603c4400d0405000c094402055200c4661940400103043c54422030310640c405000008035181ca241e01802000e4410183d01c0008142e40e00b0800307549448100b11800201c10002000703407a0030b12940c282e5900ca = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 237119109 1250 237117859 237117863
    0x15060105070308150909060a0c050304021c0c2103030f0902130c05090414010f05031b19120c030b0a02040f031104060b0f0d0f09080702130605060c150901140103 71
    0x40400c000340d400d82130504030445844028200c28000d1511840c100c0d1649019144e000c0c845003041c1a00300f00d80d200d50f041d02e0155030010009007100d5000000040c00801214040b030754550305040019404080302d880340c03102001006018254140ca160003030031652090b0041c03600360701c0d00d00310201684480e140b2100c46841d4110005507030001900c00e890030300170b0405031603009041c0b2150342c0089486218040c120340e01c4641003074105460300101910303040c00040c01ea01c0070800b07407240001e61400070300c0c2040d00311100e001d81c00310ba40c07116808900035803050016600d03001000400c10400c0706d41030040782e001c2108003045040c0b504007983d0303030401000303407002400b0641e207d04080b4680d40c0f61350090000b040308031030466490005050507565500412070107550703585400b501c1d06111056003c2c011034075512034485861321906908001e00e214009400c464a1995488082099150040142044642c0c8002005590b000780c00100040600502c0402d440e410007080c00c0c00500560b0446040d29 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 237120359 1250 237119109 237119117
    0x80109060315150503030a0c121103030403051c0c0201092307050f03031614070501020703032a0b0c1201090c050a1103070501090f020306181b042903150601050703 72
    0x4480c030003a41401105908200c1c0d0501001824207181504050236441b41c902c15031080e07500440b44501661401d04c1400b82801c035030002c000180000f44110700402d00c08202130b14044840313111103d140c0c12a000d600405025030740d5040c90034140280102542030b509440b03403a480e20311440703520f42e1fa00c50041d8031809028180700560500c85680c280150f809100300059451a03100f002e08007150b4484416040303240c20300802c10041a40c1d40f012a20100b0780c0d401d500c5414034004006903040104a51000309810180e8501a250001c0c96014100d40502d82481c1841e45034008240784a400081c107a024400c2c3c0351424001400003a005001d46034030780641d0030700312a20709402ca001d90443c89540c40060840d4a0030070a2802c0120016042143c14001d41c11100c03260b5600c80c004841510545140f14254010007907016403c1c1c46008074285800c1c0038201040f03d0100240c618014007954581907ea01c844100303400041c101000213000c000811202007000c2d040c4680068103900c6600c0000d4100 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 237121609 1250 237120359 237120371
    0x2030d0309020d060f0b010908190b1503011d0c06120406200a081501031503110111101a1905010e06041809030206010501170112110901090903080109060315 69
    0x503603100062040c00e160801801d101189640035105c0050404003811808201150000b04114500090000005182c503840201015860f150860445002080c00e2501c080c003004003002510203008954055111483c0021380f40d1020381101e0400d104441c0550043d40b06200b04010441e900202a0700582c1100300052149001003d107100160f110b2400c000d02c510008180b10019800141e83d40705c0c0310401d600019400000004405070741e03a41034000c004200114052000c250700c02c062085004050401201ca00b1060f0b03900c1381040b00704801079000b207558030b05c444060480c0030103000240c001200d10402c1c607403214a140444890a018840c10885944601007854a4480c2100c000e064208040100518000b4009000c0c2c604680304030018010000001041c0d4010100c0000c80e450306141c5454580c2000340d0080845117101c015101d001351244010034580b40c0280c064040e010400021442144030f0401408451040e442404004e00e000784c108049042511411659580301d40e010a42d = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 237122859 1250 237121609 237121613
    0x3070201020c031c1a03060f062d0a080d050f07020609041a041d07060c1514040507080706141b0102030a06051207050906010f021501060302030906100302030d0309 72
    0x20b000b4400010740b039210000e0201d4003141c0890340c104501d01d0f0070b0b1040c02403800050100422004c404450f03a003542c01040071800010411754015840500604582020f08002210705000c06009031400b0001d03018441460329401c010380060040c0003c3e400611703610f0360300b450041051242d01210100c2ca2800b142090455440c2c01c00c56203525002442030264444403410404001540c10f480c620131032030500b054003080024028a09070040070780107480824503000090300c0c07508c08502e0131122951440200b03d0800124480c40c1e00c000c000d400c07200345510b01481d04525007282a02b001d84c0990080c5800c00c000d40d4041d00c0000f10060300702c0803d1b00c855090304200038040498008000d10350010040000c07001840e8030003400ca81e4100d03120340d61040c1008607507072100c01038090240c220030318100044155004400100340a0042d104403a07c031070003000700101d40002038010303e00082c3c0020900280324ac0400002d03030410662071000c0255403443e0300081d568404400c01009250306c940f000f200b = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 237124109 1250 237122859 237122861
    0x40b220507030803011809020a060f0e0d0c060807030e0606061c141605030c0403020103050c0706051e090c01092c010b0a08010f0b0d1e0e010b0405060d0305070803070201 75
    0x52540d032110485105980b02d1030144080d070024040c0c6408080c581040d855845403900900502540103450303802d040b070500808450450b03448051a051052410741c4000a03180d1040c0091828002d4564213541c3c0c2c00c002008004035405030401d01014103101142d007213500c1c0410342d65004582200c055958520b840207207001d2420502004400c0303071908540d860341c82c41800d4407a1213805550202541d4400007801607170140010340e0031106920f0240000d2005502a40c00070750024104280d96040c19903642e110384c00d541c0201d500046c4402d03412290701401301e00003070290b0480c1c80c02e009001083c2c00400000c0561020381301c0c0c2d02c004103207440c0700d42c039005820890050a803803401703402070a50384403101d41e10254800e0750041d0000780041d0001408545201142041e212440d110314030741341c02c180d0110b016142060b6a616480041c040001c01c110480c41640c648800c04400070407503240801c104021188020481c50042244c2c064080020754054111408160700c41d4815840391180c0034124 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 237125359 1250 237124109 237124171
    0x609050115060e100503060405040606030b16090e040f0b0c0409090c0e090105010e160215070810060302250c030b0103080310090228031103011202010215040b 70
    0xa015540392100c1411034000c0c91180400355803960b102d200400000d0f50a00c0008440d1074003800010b0000d00c042000d81c54035401403504a4010302c0003140306512a2100c80e4101c505070340007600081d0b10703181000019041a00e800c001c00c00745105010343d03e40703501c1e009040b21000d81d000f45812035140c002486040c10b00182c901a005081040055100d00c1c44c01e50f480002c28000c480300c191040700000c541007814001c13241a00c00c3d440d01c040198688800f8509800042c841000c00d40c090200000551a41a0001803040c0303c1e43e5a00710b9241090083e8074000103403030300000109801009080e04101da49101d40302c5201021280114881d1241480740500c201604004e08103540c41000106000351070300a14012500c841c43d12460a6580032030340128410849100000c5002452050b80d1481440502c503500300b0700d040104250507c50b040340c890394800d801502c680040b88041c1800e5513810130038840d0f01041c441680126040984420360fa0398130003001f801ca6404484507180780704039281150 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 237126609 1250 237125359 237125363
    0x30709080316060506040603021507030203041a03190e06071b050a03050712090f0e190603201e101403091509030910050c070b040b0d20040b070609 65
    0xd00d445491403880c2c06044000004142e550904100c0828030703d142078031412040f60341c0103000008100c407a804000494000c0c91055081d030100307103c0080e104c051900c2400e0910180c2d100e41b5580c1c50010032140701000c84c40d0711040103030724000404185001c00950b26422044c80d0a0a0924004423141040311881250f00242280030b1a1000010550480090046140310701a24040c2009061f812100c105252040c55541680c03c80d0801000d40310a032020341101480d8014111407038500b0108003943c0301e5900c100d1b02103840c014840c0301015043c405645106d01100c25280c803030782210481c1c0744070701c0d550700c080c0c451a0b807400d20781891400391208130804000c1e891007503100c0c6410040c854444190b41802440c01c1c6d6a400001c02c248404011281e031158000c0c40041540c0c56540221103641001904000074030401001041048004e005840100320052807143d0724020030301c1200581d014010358860490104000310840d419980079103098841d54034425071104603600300341014145200e00 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 237127859 1250 237126609 237126613
    0x9061808190201032a0f1707020604030908010c12020c2a0307050604150c020a05030f0a0501110c0a030809031303150b032409031b03130603090f020603070908 70
    0x41d01a01c40e411456400c090390007628104401c2080c001120310300406110300004018003022040b0606004594031004002640b4090b0442d4509200e0440300c114203880c00c10140e0f11045c1003004256020740c4810140505800a0020702c00c040c9001e040001c1700c2d100005081c1e0040740820201c041001089542462034140c07500303007140c0d403141d4842c0291110700140240074440c4040b500b403c0c1141250201c03402105002d80304503070048200c90000001e02e040780d02100650002505680070840031000050000140010005a1403e9401c440061a01c00401e40040c082c82c02c0c2e040c00404e02200407a0103080c5008142d03500038520341503100d140048046046100d0020041c88007140d050300d5211041c0200b0020b08984c80c0c2059940c411300b212890180285544001c4030940c009900c68225444d442200c0c20174100c0801180003200144140003950f2011403064590030828900c0341c0240070a0508011500312520b40341d011243c9060080d01510000011403e59845001042c00400701070007 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 237129109 1250 237127859 237127873
    0x30f03010f09060f1404091104020409020a02010f0e06040f060e100b030f0a0b1501170405030c070b030702070b0a02031306080603120c060609060d0f0c060f03090309061808 76
    0x80c0440c44404240582e44106142c030384081004903242c00d1413000c3d5103441219140c4500308204004c00781c6205075084440c14181c41100c040c0b41c4650018001428001c4030160306c92030380010090031039810b00304108031a418102039002480d0081040707a00250005426030f12131109050040151044d41c038101d8040c80392840d0080c16140d10b40c41048441c0040301600c46002c070a6080c0c0381c2c0c500c81c264011f046135580c9804a10702e1b88444200e2401d0140604200c070a12031170200721100d00c501243c007680e258000040f55514171034180000409400303a4611141581040b000080d42e84100303001e1100e44800004803203154a00070810754801e000c03180e0310340c50300350340380e01c00100a15020345071f56010b07210f001140348903684464140d40005800000030499591501c00f00840350002902d099000424918200d010408a411806510b801903540c008460b2424400a00b0002c00034840e8041601d80440000040da010780440c0c200d03a070615106106c880c0c0781c25031803004d0b10310350700400c2c062140701d03 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 237130359 1250 237129109 237129119
    0x60503060a0608070801170109020a030b0103110108190b010e030a12020d0f020a020f2403090c01080408092209060515010201060b1903060302040e060402031b0d080309030f0301 78
    0x11889100c0540d9004001640c0d0701080d80d04142c01e48031040402c04450050001c50403001411114041c424004200c4824075000304110003080c0d08180c5098440500510070701641083c83c07604440c0a203080a001d140440450f6010340440e0110006c0c1512003000c00a160301c10882480d4442c2e0043c1036030141d0030b2030315000d402c625581d840318025000701c001c04c0100c1c500420f140008982c054024080c40c22180d03007000407201c2d41040752b81d070107103440c1d4030500100081d038240304c80c600500c00041d82d6070416441c020703d800a03550300c0504100080c4104000105a9002c2d1a0b100300e0507284203140c03c051a24030341c0c403d19401c400213040f5281c043d420040c000c441c1c002c0c0707004503104504801c011130240c1c012800d8440c3d03030140381400c140420200d6041c911000302d102c43d0100b10700d07000448a4895002600760ac940b5041d02000780d2201c424841035203001c1c00300c2c402c40562822a0481c1c4000341340810814115000080c0001c203001c4009010740740144101ca0070894040303a110b50700c0d07841d5 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 237131609 1250 237130359 237130367
    0xa0e07090f0b010e01090b07020108090111070c081b0d020f0d0b090c040608030307050301030b0c0d02040e0a18170a02030c0a0b01080d03050405120c0319020c040b031c080c040f06 79
    0x5042c10700d00060101c00c0132242d075405251001c013525113196400d880c1c420603400540d071900f400303410705101c5c5d1350741d40440d040349004401903d83c207032007151403030b0f501823418004502d40410f4800f96210501000b45a980a40d030352049041da990f8166044400310f41e0510025080031125071015049a021004014043c2c00109401014020031a0108415615005c50301d40e2804112081030203e601000103001141d403841300540d10a07020700b0245d10304031800140605a03089680021074440400c0c0900a002070f250240204e48002c07810120103a0f0482d40341d8103040f0061905440c6151000100c00108034401e0041f248281042e00031680409100d01d01220509424400c2d41914052120990b140c0d510078002c403409940c05c2402440d454101305080c48250744200003004685c032081004050091800580803d260503a4002e080c84038280d00038402580c007030841c140c0c4245c00c41c1c082030103000d82502454001084030b28090200f584e0300c180702540b40c070031a0008945803605500000d0f0765980 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 237132859 1250 237131609 237131621
    0x9100203070611030a06060302120601032007200603060a060e0102030702090906090712050307030e0f03010507020714010c0512030709080a080705010f0c020a0f06060b0408011b0e090a0e07090f 85
    0x1042c174100481d42d41c8032805c07400ca001e1514888140d01c15503010450940c03181d0811140101ea2586888a50410020311181a0b0015208503040b4411200c600c0f0301041e0034400307084080c0140d070003620f10b140550025440000300d014560a000300c2a42542e11a4803c0007a01c01d002d9024020301c0d001e00388404001c2d80c03202d08850f256003910aa0901141901030003d81b4145564080b00035030030301006917000d072000140c800e40701c0c2e0004030ba03030b58082c5181d809000f80e501828154000c2e103023007400c0c40c0e280c2e00301030a00001d00c2c1c1801000603508001071000074101d014100e10b00c211b50745075240e00350110380d4100340b5840301026105542203281171048240083c15803610400080188181c00c0601a050b03a0104000300013580155840401050f0b107016070941d901d02c00d1400107101c9403160780300c4600d80c001d034009000d56955004e8143e500780b40c056036000fa4040e03a091030071100400c180003d00100c0d0042070201025142c1003280c200040c02c00c030301e4014141c80351090282c280b003c0e03510f50080034 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 237134109 1250 237132859 237132871
    0x609050106050402091f021f1a0109180209042c071409040803070c0803010f0513050108070510030b060f180904020a0902090a030606030b040c09050106050910020307061103 76
    0x440c20700009401d240030b02c2280d212982c094081301c907081102d044040d080c40c02d10401d00540c0600d400014050720304400d0502001c1680070001500060001c8070415003079112511414809500005e118158000c0b42140030303c001c030f880241c1c2c1c500c88800410007a1008008001081b00500192100c24584d441400c000071040c0c41251306440c1d0700c4604826404408414980044440000c2004500d00c8030055521941d03504048128158030394401c0c0d034a9000f42c1c0040c0c00c0e001000d9040c800c91811404101c1c402854100901455041030360058442c1407910a1030b00c207449001c8620207090103500a0000000c00408140e11403403e015903100b80c3e880407100054200110794107071014585a40801d0065402070012150281480199402503000160482e07000fa0440800000644507001d040051886100d08195070308103458008811a407507007083d8002c0b03080900600050740d11000b13441917400203c7e64040c1c0008800c1c41642188901b45020307004604000446801c281140004c40c0215 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 237135359 1250 237134109 237134111
    0x70807031b030902030309090103080a120207080a0c140d050a030509030a0f080a0e1b09101202060a0c140c1201110304110307150201050402030c04062909060706090501 74
    0x551008000c404481e0380203501c01107403840c8100510a24400c1d4441201c00e44041d00316841c12101000190040100760b004680c01100002c219a000d43d00c2085203480914001e000d43c01c06126a684182d035001c1c04d00180200480000c1502c02c0c0004913900b0310700084003400f6240c054a90000c000c00d02e81c011019980443e05010114400b568000110b0782c00020a87c0d807441c0c0f4103403060040395030a0b80941000b0b100c1e91100d13a0141046030502260341c01580302c40c820303c007003103e0606100b642d10000304000b03104c00500004020292024003180d040b0f0b94101e49043c2c1d01c464150041e945040c00342400303000c444000406010101002402620880c41184c0d10b03020701160034102403d981ca80c00d81046040400e00100f0005142c1c0100800e0145008099911603030f108d00380c0081c00e070024004003005039116010300c0254101031000c05441c840a56003400030506000b543c04d01a1411a40b82d5420740d0f403021180a040011070075a11008002050180d50300a00c0c03d01401900480c0825647c40d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 237136609 1250 237135359 237135361
    0x51507030207270519021803070e131103011503050a032c040f09241118010c0201030917120c12011802160f0b06010825090512060708 59
    0x1041168210f01d0980040c4a100803884000301842000307008098039030307004004078840303403204601180003404808031300d0900350041b080e00d075041601e020342c80c3e4009015101d03510140a062048011623462a40e00909100031740c5030320102090041c510602c050094059010009c400c00c00d0229021040030b01990b41d20750a594400e200e1103408491000b207401035001c0c0100c0d548241025000000241805140043c1365541ca407100800d000b8040e84001c030805c003c9020100310081d500c905900d501101c2442d6013800d2038400e5005d0740c3d0032004246414055400c0c0b00d90210381c400e400c0410302c2c80d030050113120035200c110203058150300081082d1012000a80001d01c0d4070f90074200303846081c001154800301b180d00e0714842141e00c242c21003600f20b5294003040800801400750707900d043c040380b003071201095822060924203000c00d000b42070503040143d00002c1c0203040c103600000d002d03030b1400031100101c100c541040c20388911281da030000340c200c005506c44400d2040c1c0412228403603089612010b0359 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 237137859 1250 237136609 237136619
    0x1a010e090d020d2d020312100b0906031305070f050f04051b210c09040606051602010e0406080105190e0d020613030e0301091115070b010b07020a051507030207 70
    0x21200803000110040e4489900c1950307407440303801e200309000303140368004861306014041c1342c25030400b0984101c00350340001b81880280c050604107583c040000d0484007000c80c2482e00c484114491000c07594480e41002c00407444010140da100c1c180b41d588a000c4603100d80d5501190b0100e29954881e89110304d221850800c1c090610740151845465010042099001c0d40c1a031900603030001d202d0407151410004200c0256450030a00d0b0b030080815202a90303d54000708100000c0d2645500003104002041c44603d85102c5242071280300f075542400c000301342c541c140f000304006052541c440003956007080103110f110310404110784205241c8020520010401400a50b600c1c580c803810280140d001f1400210304222400401c0d499500c01c0c58001c3d40401c80700300103420340710450300503a0790032135907c0c20702e000307242c0344980180e4810307004140b90a1104a03140d507061f1010501c2100303d41d10001600500319615149440041d210040000501580e450001071150300031900c2280507104040d0b021907 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 237139109 1250 237137859 237137863
    0x10207060512041202120406020106050906040911091b0a0c02090903030405030a050a020114010627081911040504030c11060f07030e0a0b1605070b030903040b13031a010e09 76
    0x71a03030300380c20b0540707a00c0b41d54590740340c030304a501c0010440c000c2c3c1c2c884d4440c441c0307a0402440107040c1c5e035002041007824081013203031418025260900c1146010007450000c0e4280c2d00d0114140412604840c1d26540c950700185164003a4040701420b000019510806c25009640c4804060084e03910075441c0d40d65589450341d03031005a0f0043d14660080c0b1590b582c46d84038000400e1000107602c000f240c003250100312000030040a030004408680105000a00c00120100310000821220700c9010380c01d1422888580303440c1040d2000580d541c80f403420800b481a400314072091114041c00411040ca0242030040c54208415001c031541001c1659002d0186802026140c00414201900c0d00c1d008880e0f0f01130701c1c1d1503288038406412000b00703800041c2c0400081e014000001185000400c075408510b4070a08000d07203070b0016950342601344180040d0410020945040e5050325691982d24452112000f0030441584c0c00140821004049901d100006078074460488400107003188094940440581d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 237140359 1250 237139109 237139117
    0x1602060c0a050429030103061e0504021012020403050601060503040c0e01061202030a0b09090309040b030f03040b0703050c060a02120112030804150908030f041101090e010308030a0f15050102070605 87
    0x307000100144020300c20100e05980000c14415425410100e240002d61410410b41099005559503903071000c20080f03110807881468156140080100143d2505074009084010114042c1040003643c18444250010031360446000e50303000f0040b1015580e603001d0003807a540c0211001c4070001c03d03a00c000101c3e2004c40c069103058034000d07140c1c0b07501940c1122071000290001018450020703201d008e41c9403d61109003005002d101c402c40030356600e101e1071b401d0000751250110322030300a51100300856034001011040d2790a03a244040103903a12160f0782000c83d158000e200741c1030b02c0c60060f5828003044a18aa00426100400400b41d00703590703994408540c0301112400d40500801d08190009000540038020044010012640000c031140152909540741e08210303480f644990f20744007800148240e0740c1c00c458028900740b80200c00745041907002202410103100c0100041340120108030b0070071242d0010001c0800b246c8c0d0801c0403841c030303030140810a4180e21519025001d500c03804516548148116 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 237141609 1250 237140359 237140377
    0x109050f06070522030209090c011d01020601051e10080126030a030b011202070309140a03051207020a0b0c010f0b09150105070f0f0b100b0a0c120e030102031602060c 73
    0x490304000320100b0b00700f48520f400905401600c401e41340400141d4401d0101030140d214140103203085c01221001601044c640103031050035040ca44c4034074031035a9001903c80e065410980f80301044041100d56416514060703d11a81d0180007140d039400580c2d4087c841a0480320171401c04c0304403111440e41c000c0d01400c82c402051254008005045005000c1e41240c0440001894086802080d200c50a4201c0e00180802c40024200c10030400c0303807400c658066140307200110390400ca8285555200c80d65451448000c421030f8402140840541d900e0101041c0200003451101c0d60311491200c0590081c200c8007a003802040c130340f140270b030028109801610301c2008074040c140b82c0701c000c0000659268106180488503941d01c0104a00011100c6001e0720505116240d841c810b82801c03d0303240e44040c010303007269091100c00d02c5600503441c0d0180b68a1406a00511030280c40b842c0090200e54400f00040844d40560000080c88101c140a849a0180c01120360035070704507032035090400d041d5101d44514 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 237142859 1250 237141609 237141617
    0x5210f010303051303051006030311070806010611030909011205061503030912031903150602060714090f040509070f05090103170a02030c0106090501051305061f0509040e0109050f0607 81
    0x40c00001c0c0200020070001c46001d004c0304040f0b41d2070352198902112400d150410300d0311590200109078002401400940a83d4007400b2500d061191141e901e2605114810820111104a014200703041c0b00719841040e02400584032580c4030000d00d9459030040d24211410301c5035900055070300d42d0f10710b044083c1400c01000b0718600019002081081c00303894402c0555070004002400c84a43d1445404845200c40d8038040380c0c0c82d0440d20a1007501d00941d00004c19500310104202c0c0c90b60b030001082d0382281040c3d05c001d03181c070a4440130030180500b400109801c40d1a01060001000c800541802158088020480007507100d0090281c41142072200600202c4d101440181e81800000940b0401c030f680d104a07410b100d0303010803c41c02d5940651006440542d1392005000d607003441860390380c05405244040c80a410814081040c600350004040c03110903603d8110501c41303110314100d80310520001d00034080a889038480034003c000302d5071300301d495205205014440c020082552841070f6040d443e = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 237144109 1250 237142859 237142861
    0x120a0207020a18060807081608060f04020d08070f0b0108010b1e0d05010b09040f0b0a060b0a08040302010b0a090203101a04060e0a0308031e010803091e060702060a05210f 75
    0x1038004071010020040b80303ca55180c590100e001c1d0001c10500c0000d02020005001d00100c900d5000243d50194024140c40e41041040101c00c10350968036640095041c0c40f83c0400c0b60103414000d603207008442004110620818801e014842d256038800e040c0d418000080011079405d90030464a04008607400c02d80100d02c14010300035140240445407414002c100200350004000c000038000441210102d411054200c82c0f2000c1c040541b0100e40d2006040d0300400010381050600f038400e0103124180c2040107ca0000981054402e4008404c0c0c808068050340d800d90311071801c08080d4008440c194214004103c001030101035992003114286000c0d044075281600346041119404190142c43d03410400b040c50000002d09aa0010b40c070a02610301201242c03c449240c4003503056041c0c3c0304148591051005103000d0b03880c10103001c101c000d9031403004074404495010500c1030040d0a40a503101e440841c180710300c2034001c0700900c05410040126408603013020f2100000d0710b8180c1d000f00407900340314 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 237145359 1250 237144109 237144119
    0xf02030714030603010908160605012903190c05120c0708031902160c06110a021e01030e0d030c0807110304090506130f200c0c0d080c0102040605120a0207020a 70
    0xc000b0364003c0e40260020441602a89800305035a0224001104481110b6241d03014840c2500c101409004c20f044040141001e44620444d00c4e00e4256402e2440f00d0000301040a03c0d0a03101c0c09247d400c0e03251400d100c0ac243c3c844000c1c205402031440807100c0002800004c400f06060f4044540c040c0c0c6c091403860031038032030145189d03042117501c402400e11a070811044481d201070411600f0310ba4400c400903210281003050091150540ca4220426a8060340d440300c01030740c485a01960803500480900040d20b012401200a070190320140b0310b10340250904014803076403580000810380c0c1140c6844c00c607900c400300203e41c0081c0e10800b1103016002403106002d810303030a40046030019001005007200c5c81a40049404413440940d203091000c2e511003618000003050a0358030050502a008203060095284000d92a4082c0e84900703403040200002080800020609940683c0001c00017191038548441e8003074000d500400a000d460200c180014a41480030700841c1c2a9a40c081c0c15403000300e00d40 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 237146609 1250 237145359 237145397
    0x15041806121403070b0a15060309120503092d0c092206090b100807060509010e040b180a1e0b03030a0315081614010206070906080a110a02030307030f020307 69
    0x1403564283e00080000001069242d0301d0302e806201d020500256000c1003000c1e103421500640c1c0100c05050a00e04c18001050254114509e04461824000e03903a80d240c07010541096100b803944a41201c1d07413032130b4000252851252500302e08869049070b80c00c1e0b000308200010300e00e013180d0621203444003500d91a8401010403445254074422140030461030301c0740e038502c488480112244110700011140c2006802e0342000444010662801c040703181c0540c2d03d000800d6001c5e00b09401e0301a40d103d0901109a44070700c41441070382c0e0440504070b01d05081240028000d80b01c02d80d40301c210340401300c0800340350a40e28030841c944410010021880c240b42c03414181c0c00743c08016003012542c401181c0000b245103042c00414200881c01c444244207501740301c00840306032014442030341150b01000401c03000c0c680005204040c0c540c3d81c1440c0710540d44800c10000604001c106000c030101c8045802c603a01d6800002450040d401c98178240721049415421303800324041103c03c080080e100000781c403404610 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 237147859 1250 237146609 237146633
    0x20a022a1c06020d02070809090115200c040e161a041404060f0f050109090501080303010501051c0207110f0d080307031e02181903030e15091504180612 67
    0x31440e0b02504124100342090201d810040c400d0b10700c1000001c420085180011415014014000c200380c1008440c95008180781c55040c9040807201010082c040460400c00c00341e00c40b0f44000b4820b0010740d601c40101911081a60007600da00840302c040030540c1c1c0b51108480ca0240b04520905040501d00481c14481d4607542420503040383d03644c100031036203460080000d4044d01c080703030b81035003607510786000140f03450915400380d00c0c100d14040040c004400c0c013108032130445009107000c0780c643c44c03807034503415050110100140009100085a0080000341e640d4405420000c03500080c0d081c1c0e611080c400c40d902c035040c005011400820010381d40034025070004500c0202184120003d098034a069002c90380b15409580385014944001c94041c500514010310f084883d0907041d41d02c501c0c640d0050f002c2c0c1c01308000c081c810f003207840314124a45100f905460040b5002003080e06520032040003104544c3c0240940a00d054400c941108803121a006010071200c80e06081881001991605141390503 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 237149109 1250 237147859 237147863
    0x711060c0c0d0c0f1202030c0708010b06040b130f0806060103180507090c0c020a030809190608011a0702040914061005010815060f0307081005040e030304060902040e01020a022a1c 79
    0x1007a00c4024000c14013141c05e4580301c00240d0015643e803100740081503d0070030b190340b090035070303a0602115a61503280e110544003110100c520550b01c440001800403803a0340303160418903401840d4480021900300015429010301000c0c6c038108010071024a00842410b28040d0107401c1f43e1140004029014607170388400c070400305a01e0203240d000107542c006695a821759200f610280804200544245484c6400940101074034010340c111070300d01000641541c60511981071000c5040106040f4689548100e41c0d02130741c024410000310350280381c9401e0100c20203012040364032a00c80002e400c00e84110b0407a080d28016100c01c2069a2401c1c095020728001c0313894150840d009000a100c105501c0002d0750098400d9110500b20303140201442d825881c0f10380c003040c800d50905898455450303000c0200c1ea0405d42010700814180d40780e0000c1001f80160078041c058541c400135100e0300c8242d0200340c2d00a120701c1c030642c003824170b41c2c01034011852070b00c1b07581c140d13a000042e0201011005c082078909601c042c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 237150359 1250 237149109 237149123
    0xd03050415050c010605060301030b1503030412050a050706030e070b0309010209091611060106050412050a14010f2a0f02011803080612120409150504050711060c0c0d0c 74
    0xa912100111400501c004500e00400d6010840c250383e0a028003426010b00030503100716080d50b14540380c082840303801904030101182012481001918207201300d502a100c80704011801000300e2401c15a11000ca88065466003d02c9601103602e0307100c1d0040d600c0345100e00c2c005000d0386081080c1170381c640d40042e101103034940d401c02c0012000d443e14041140b141210380d0002010204640c8003800e01d119002c0e940940e0740142c0010700ca143d801800f81d90a6442d4100e191160400c5444d00301d103800c0c003540e8007501c2c8200e08408080c0a200541005007035100401017404003100343d051184070500c4644552480c1090541110b01c03040c400c02e5085941c807014400425404d5050703450001810388a03800b500043c03048400c212903070910b900c000d031005103a00b006001909141c0144101342c001c0d8003c51014a8a950842c21b20030304a0040b000034010040040001d8100b1090151070032400c804102d01c00e006101c006440400359000b91179464540c0c001905440210300c134101c4800403000000c990300 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 237151609 1250 237150359 237150367
    0xf030608121305150304150c05120705070209041b141c0c0b160b130f0b07030f0204080102030711070f05010507060207051b091803090d051e030a0305070801030b060d0305 75
    0x255a00401c0c1c040b0104d241d01400d540381420b051840ca40502070402c1e8440500380303003908e42c100382c1c860101c61039185d40d0100150b0f02e444171041142c40740f080d4036010354442115814401408103030311038610103600d04c130f00460000e5030301c00c178000194101d101c145030f0000c00d80d140f010803007500c47c64512a180c8500c141c0d0404507240c412005244d00003140489101e562a8842c2d002c2002e403006482e0009010800352071a200c0313682e141400728400510003401d50400300c011815450182c2c00604003400050f0b800d5450303a8540cc5094001c0d0811510240050300d046401010b44002040700826200110180302905041c40b0044d035040d071040c40111841a0308010240210703406200204400702100d0844040c601c0349000c101d081c5401820315155841c0240380f85104460000407640d00d807a007035034039940200c240c0c10a54104460344404081404844d001401500d40100c000c014030b14883e1410031a41e190501e0459036230701c090200416600011000c10014071b4007200d10080c41c1e2080c5082490 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 237152859 1250 237151609 237151619
    0x9090e070803040305070e061c170c1e12070312050405030f040909020f0603070c020d020f04050705040e0903120718050415080622140a080f0a0f0306081213 69
    0x2d9907000d07900541d4590080388083c02000c100526017a003040e01180d20314031528000144444100749090010105540e4998a94000900400f80c1e10766192a20540d41d281090603003001c6140456249800f0901841ca4505c08038002c1c80c098034119601907446602703000fa2a01c03014001c241c0544280c92610040c0840d0711100400740080c0080c1621440129a4502500c180701001285503600c40c4516818820808444c1d0302c030901c0350407070350102da8070302a112190011900480341c00c840c0e503030064200000c02c9641034000e4000c00c1140c00310a1403940958031600f2180d1680074080110b007018940c403001c00c10892284403030318012400030100500950740d0300c00180440b0301034288500314080d44441040044030502020754007490642c96a28941058041c10407090107415006201100050002002d40010050f5441c650f0303001c900b06030f450015a2483d0b05c1500008103070030004a03010314010003544640101003c884004005140a01e078201d402400d075041030740308094009402c940090 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 237154109 1250 237152859 237152863
    0x705120a020121050a0b100e011e0309060e0d110105010e0105010e01050d2406080f040206030405030f07030c12020d02150a1e0e07050d03051204021f0809010b0f0109090e0708 77
    0x80900320785d034400078018480005110312120007060a03424059012000d4038142d8010b507155103256a804050301859404240a0b00201044540948406c0c07803c022010a0000054125211006529554000703541121514240c800c24010b0070b48a200b003100402695025050700c1c6241c41c2d0506040b0304054070702440c4c808403044030b206034050103141e40d0b441c20051307178840502c1301901d850700d07046030341d80742410301c0000c0d800010308002d004820020000b402d1000600c150b94101400c0103240d5034446842c1402401d441080c4826034521003000900d5084600025480d50ad069030380e0041d150b414a00d0304244207943c4001d03c041c08280e280c908100070604954612080c541c046940010b5803030403000070601d4200a03411103400780400d1103000d8082500701c802e44000c0c029019640b48541d4461000c01c1e6900c10007076a1b003108844840f0081c618607048444280714203100402004030b40d03a0700e000c100d902441c150b10f00d4046196042c1c02d100305085070b00f00c0341d003811603a01110640c0e0b80d03920080b4 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 237155359 1250 237154109 237154111
    0xa0b0712051c0e07050a080a0c1e1802130e04021e030f0106180609061212030b0a180b01030209060d0207020d05120a021005060f060a03150f05030705120a02012105 72
    0xd40c2d0303074114144c2800305141039200c49014214103801001d28402030303a81c0c80440411809904544024400c44080c0340c0041c22000014104880002000d5240b450007800617400503031810340c1d000c421900120700c00f42c1044405105580003465001c20101c0807039040c814001c0d2062035a01030291820707a00380000e0901443d030061070010454444100c0b02c0070588100c80030f503007000148a080410400070004c003140580105900031410400205402500754000d00310035540c66004500c00310300003845840400c1107420020845400e010a60ba0b400044080f03104240300c0317603444003090104291007016035026090003480a0011007214a4540b01c15260003640c40000550b054001984007100b0703410311a0403d0441ca40c0410b010354284040010407520110b0911406501c0c04112001c0c02c44c4660411649001e19103443d0f080f4980b01e007058401d8071f105000c2c031030103482403650000f0642418024116802002d5015007684030281d4011100080204240c5020310319400841c1e881b40d029100701 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 237156609 1250 237155359 237155381
    0x9020304060605060f0c0c040b0a060f020f070e011d0708011a0f030103080a021005160c030e0d0c050102010c05031b0a050408010516030507020c0102070e0619140a0b0712051c 77
    0x1198540c81448140e41c0782c546951f442030b01490a1901b0a00c6503101c4400801c00d6030b44c207092a940c0100038040491900d110190040c1d807034402d007040020020030021209040e1400d038100e0aa80c8121210b04545002c0c05844000019a0080040000c00c0b5255045100300c2401b000072440c0810654400032150820380007900e41900c0000c1d80d11600d42c041064401c2c48000f03000c2030201e0f28104401100a0484103129000c2c400b003408039204041c810440407030000701c01854148102502e082c8001d050b40301c0d001e214059840d25004c410794501440a0741e20810190170100e241a580740d5413400c440d08210b107481c00b031020034800810740c0c42d1700307000d401d1062910034440e01d075600b400c91004041c0d03080906401d041d90072104225410b82d0b80440c45a040d141d4000f5084000c0c2c64420105010100b0f0b40c40d4518005012900881e60000300170440450303e80c01c0b68010440c03a00e805561a41c0d1141b048001c18100302e107030940d450b00d030052001d0302d02c0384142c18000103000382009a01090710709078211 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 237157859 1250 237156609 237156637
    0x31201081005060d05150a06030209040b010906060905060313140727050601320f180103020f0d0f0f0207110114030c040e06030a05031207020c030a03090902030406060506 75
    0x190a5001c05148591035112008031840b0000e945191240d40e01d034000340e01522050480c590010328050f80c5034104500641e40644883c10b00d03e020b040c20401020280115103030b4a003000b200140076031281403110b00341c2d00000d2100c0d140d0745030504510442502d280e0100e4400c80a00c01c41620707200d0500c2040300401110180c0b800c03910080c441000100704041501405503d06000c0c0851660302c4403074039a60480355184900150441400c7d6164800580301c240e6040c180040c4c4500038004e48070241522a0102607032100340c192105c010341c1603004078800900504000d01c01c018541d42c2e2900f1445e039148459400141c1a0300c1c504464050340c2c48040191084488000110300a5901c030344244000134122100c1c5003182001c5444861512035403140e80710000340800412a55581401241d0030a1ba02c441202c1e52508180c405401e000d0013110034002601605010150900700811784030002581640c40d00d00c00c034108980b040007508040c0058812990f100c0000c113068031824003d048811308d24071 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 237159109 1250 237157859 237157873
    0x6060b0313110102030f03070806040f020a030209130606020309060703030b03060c070b06040b06030604090501020c030a021c0207060507080a0e040e01050910090c03120512070305010f121a070203120108 89
    0x1007440b05402022903203411540108080c0090308070b5007040c0ca802c083c443c0790a40d003d40320100050080c0900039156690148006911004d5a8265008107071180080ea881c45000ea020050300040300c003144a00300240c1c208000b56003003441c140b030040910a00c2400c000641440ca00042803070000d0840c0da4001d507800006292051002c13a0f824a076012100701c5081c003140e1100c0002c0f03815400050182800355880384900000c0190030b40540300c100c9490030849844400d640e500075a00c1a41203156980d01e0f40541c04030f81e00360720101702c02d0252002a00c56501d0060280d03514601e5a0256051004001030b25800c00201d03916401900111500c007070010809040000110382400300100750000164030388280a00020345169907001100d8001d801c010310340300c02007001c0d9464032840c1c0c1c54400190200080006241d010361056068981d6458074540c850340720920f01d103189042d110003500304c1101e100d130241c00004180c9015032090107817042e44d0070300c10980c5000d010b0450030b0300401000e0300008 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 237160359 1250 237159109 237159113
    0x160b010608190515060913110702090714092103070303140106022103090c0901090c02100b090f180d050c06090312040b0c04050a0603090b07030e0c0d06060b0313 71
    0x214410940c0b0501001c00c000da82042882e00300c01007046440c4c0ca0213043c02240f8518543c0d640c00140c040c1c640c15178400d12000d510f80040e0850f03503110f110200d104162110110391680d10841040400703505841e03a0a280101d00d00400400354103e106d0b90307056040c2c3d00c041005440f020720103040c2d8a8400d460106088989418880400205800137400c552041b00b40301640c2c64601803080c08500544000342d41d135158134030041c0c2030414084126070000159400054580c440303070f0105130003000f25403e80d044018444040400d50b501440016804a40c01010400148402240541100c0300032001c0000300d0003402c5140c10701c0050014078010640114250389920420700c203290b880a8101c0c061761400161100700410f1000242010348401e0b130703500000e2082089182140c0242030000c04813103420382d80d041d0003005002c5061045848034105000b00d84107a000c3d0103030040030001400540b15002040060005d9115101001d580ca60303103a2000041e07081c0381c10015401400b2020920b5500e00307440c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 237161609 1250 237160359 237160381
    0x30212030d0b0f0a0501140405060c0a121706040209030106081c0917030a140f190215010e0a090204230105190315090203150c0a090b041a160b010608 66
    0x64840b00c0c1c01032100c041c00c032003541d89031140b010580c0c0703090034402014400c034401002c0c5409030f07030410381d0049000a440803004400241c2503841c07038400ca4201d4210458904200d446c0023000560701c1500c040003000c00c02c130340f9068000e0110760300040c00015070943d859800c0b91401040d1020f52031042c103404158001c150b40038007140003418109116030b030a4559103400d165280300e000d15001c100500c0d03201c104101605941241c2c0c1d21000802d0280d100c03518440e81e2103c1e41144044080984120080b52008100c283c5d480c0d81210809611030210355540e1201c40042c0c54444000c9038056a0b941c55100000c20300c091821148100003022180d0350f0408060145080c41b000c1c00c50007600c81d80c03508000084071040c0100489001080203d0f041040b4030129281a082440120305c80720380d0300c10041c0c0203550b54081c2075078501d255501002c80f6900c2d00b22660a11480c0107100c0e00b50994800d4100c02e815a000402001c56041240400d0552585801e03803d58001e800c5000042c8140050000003862 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 237162859 1250 237161609 237161621
    0x13030809100e0603181c020106170f0c1215010b09030618060411130f05060432060d050708100f0b0102150702010f0606021c0c02010503010b090604030212030d 70
    0x9007419030781081003500040700f40c0030007800d840200c2c00c6401d41d141c108070240f00c054100d80010058801403c0e9807031029010b015103000325104100311201c0d03400d0340400003c1d080040141d079000381c0075580a074000e0044058241540c0c09035441000c104003008085108803a00820310400103544030204102011304082d80a404d01015560001c410004034102281c2680c000c0e0340030071b03000e003012070b40404140b840700c50f99401c131001483d2101d01b940d0f2000b113400052003104102c4e401c1201c0c400ca901c1249103156002c81480c0d071401643d0007160320245000c3c809401081c02000da40486540d950381c01c1c81d201e641c1e0007442c040c0d00815124441c040c641d025010040800305006d010410804c00000d61300c40c80f40c140001100e8110300400e01160003940b21007104500004d0a10003203440740340203507035203400e02040419040100b190500a6204180160700f595059540e00d180da440d068810200d5042402c03440e902032000c010010040c1e40340d0300340b02a08010b903005152915061042c0c00f0071191 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 237164109 1250 237162859 237162889
    0xf090e01050606030a0207111314090f1f02072f0a180207060f050a0c02190b0601050307030216060501060e04052a090a14120d05090f030313030809 65
    0x2040c201406803c0d80d54800340c0342d1003d5140f200684030001405c0c030309401000310314503a802070001c10488481c851686c102d8011f188402111210ba521f03000c4020341d580d1018404807a00d074101c0840218609407405501e131040e07040700c0004d81040007945a55140e03c4450009003002d180c686010f04601040000561072038030111040000d070307890240380f01100c2c1900307090002080e900103640800c00109520800c140003044008005a140805500b0001d007042c440604c094441c900740b40e4032544540070030f903017000d5001c24208401c1e00c0b01c50044d0313850b400240c55003007450b4080c0701c1480307606900100c294200340107d40114617540b404030b01410b002c2c5c1d201c80b824041d82c14a0300308884401001001422640680c2d08440c00c1d0350b000002e255240926409603601585218000615402d41038030580350200440d00b51415038810901d5030381d180360150000c0d010900c240080c07025407078141c50850001d0005410f032464650300d401c40641c0f9002c150822a020780c8042080809400d01c82e0024103000 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 237165359 1250 237164109 237164111
    0x2a0304050307090207150e06061509060a08040821010504050601020d170a0b0a080106060e0a06020714060d0c031e0c051b1c0c06152d08070f090e01 65
    0x19080002290b1605054028100c40036000034002042140c020703c1031313002141022007000b480c0b0200701c22980700c4e042a101c1501c40c00c45e030f2801c3d642001003c0e00700e81044000401041c908400100195492800100141c4046c0c03000d00903181c1104030190004140c0c01c40c0100c20700d11f036050608000446401401d6141154044215415002d400c41907584036200e0100144580390340b0f9a0700e00026050040c0c0c0c61750401e01e103690008812105400020a42d940c54607650000c5508106000440ca450b02c980001070f40801401c018504a8030360103c90094058074540c074042e10908130704141c075000c0c85000d00096586460000001180c600c8401c4001569410f0128001c0f03a00700900364066801c66008041802c0004034841c4010044260005424002c41046802d40c2e1000fa18841c0c44040541d003150514018001201c000c8100c8019544103190f100742c030080444030140079070315054000c0f0f10f650982401042203001000058002c0021040c0203e00c41d00b0b02101806403210f80c62080490303 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 237166609 1250 237165359 237165367
    0xa050c0c0a06110c010c032c06040305030a0f021b10020f090112020c0a0506190501030c03030e01022d120c060c0a020102121e0f040206160501060b2a03 67
    0x10301404202200704940041c004220001514000711076845000b5141d4402e43c6860740031015250140c000000f490b840e440103000038000c3c00b889605a00b10040e1160050b00900c00050020b800780c07010355045503100000082c800600c0d0000d4089910044650107400603030003010740010320400c2400c2006008040560030640e8070303100251980140f0098506008c40c04d40c1610321082d080c0c0c10b80b000200040111004940d81c0d00b815511110280d802284281200250b001c640b94140a410b040303035401074080e0000b034034503202110145202c403803243c11030041040c50507403854840c40c00d040d00c5001101b03241c400460002c54601d8000500c3c900011440e0601c811202803c1c0456901d60011402c4c0340ca036514204c0280032030080c481c684501100030508020301150700c141c4036589122803030285144000da12141e002c0c5543c52030854000354440001c01c010141d0100113086a0300041c03003140003084031622480d16151907040070380c103030b00700a840e40110220741d6400c2d2003241848000c072001d07610b0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 237167859 1250 237166609 237166627
    0x41a030f0f060a0c020a0203030d0b0a08210d15062015010b09030a05060106030606090509091b0301020405060c0d0f0807090905190c020a020405062b0501090f0501050a050c 76
    0x120a4001c01c3d4442040e034441d01d21903014002d00c41011a03070381c01000d0300c5e901c40d42d0841d4000285a901030050140201c5000890380070400902d01c82c002d40b42424040c03c24200200b000238650119004900042c4c9405c45505410104d52800e0054100c1d9101d00e4282200314410f071036041d40c14907000329240c0c02104001d120182e00050b0f9415100000000e03036643d124080844e10b07104201c00010710b81c1c80b992000040181d8540e0140059503050350345e071400b0036030724001c0094415041d94502240e4001009002d4901d040840c070142c00e8201500242c00c241d035460010302241c010341e00b125101d81081c02d00c040340035130020032040740c05098140741b001801c2c1608001c054039083d0040b110410780c0da0011991040100301c5800030040980014032030345144190081d100c2e180c04004034000d60038107001c6201c40c034040e90600031000c20341d000401094081210301f0302503524144d041e200340d5650010440407900424400c50414022400814141440708d01c92080300d1004080c0019a0380601c03541c11 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 237169109 1250 237167859 237167863
    0x1302040212010828140118030c0c0b0703080a050a150306020327060c030403050702151201060206060607060213091103010e0c190509010e090a0e0613020f011d041a030f0f 75
    0xa07140c0d41000c401001042c0c085c1804c0c1c0101030300e4401e0000f200203400540101580405007090452107048078500040d1b0b10000e0403213030701a1042c014082043c10340050018801d83c0d1004d0382c0402e40d41800302e018031a454107507618000ea40c0050780c1e0541c0010411904900110400c9805602c048622082d144004182601c8800c0038080d641c034290b000011909046c071900503117141507001071604402005510245103503501241c4d4035681d0030f504500005520b4004105c852081c00041e181602d4901240e42c0e2400075808154191000000700c10017003031001440c45207900555591042c2607580d41000415003903080b00038000350360502c0c204000600008010400890204242440c40e2203a80403401650900d1000d0901030300306107100104140c03094a40c1200300801c0600003070741c03000d4880d4032003801c0000700c100e4069000800340420918039485115000e0610070a41100c2211800b8400098243c86020300c00540782d018502e03411005180c05d20802c00410f04880c001d001034442200c00315 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 237170359 1250 237169109 237169183
    0x3061b09061305060a0f0201050f041e081c020301081c05040e060315040302010b1c020d170f0a090e01060f0903080f04030803190b06040b04090513020402120108 71
    0xc1c0105004a000c019120401060300c0103850001c0036540c880580d0b0704000c0c40b00c111409590019820300300440d1031013049400807805981c01c51204240483c2559640e81c05d50314410342182c40200420a074000c0c8641304030160508560254017603500d5152040081c504100d076a0600c0d0891070012100d07004c00d07040003c40701144c810314850742d4580d640d9000282082c541852004401d0340c1f6004100425a041d449121a03010032607410381401560014030600800c0040003d410062142c8450085034400d000345907034035982c1024a28113100c43e0380619441e0040b0311603a012a01140c020f000c81190b00e031030107002d800b0f41c0c6030a07200000c41c03410042081c50f50703210190074024000340e82080c104241080310049c41d001407503595a810000940d01c400b861910301c20340a41e261070444001741c41e02008540850700c107400c907642040c2c14800d112008140250081c124a150005002d0060b112400940080e01c9500c21403400c544c03421050740e0900102c10301c1540c040782003240d00d0301600c0342540b00c0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 237171609 1250 237170359 237170377
    0x9070b0301051908010c0c0b090118060f0b0d05070e0115050304150b03031809010602010c021b03150a02031503010b03030708070615030c1505070f02010804051e010b03061b 76
    0x3503c0941081d0080c00052000b503044094994204082c3d4007095030031001c10415103100e0000f01072990380360a0083e007201c1120002d032010234094035015001c80c4041c0c0140302c0b555012a000a249040d900c00240c0004004c0e0007115540c0115400700070805c0c4040d1031500600c01c0588207140d028803a072004003584801040102001041348509130b0381007840e40540b01080e00a0102d80e0b0310350050b181010809025450984500554000030401c0c92043c0511510110650001c1c628030070000001450030350300d11490340c0c0500c01c05500d12000402c80f59034030b01548a0480c0160340381813000c000e2458442986440b0b0007a81422444007150314000304540d90b25400c0b40c0e140344c50354182d1600380090480440307081d400c181d0346903020080c001072160003000c40d103043c01c148410b00c4600c03000b901c0354001e0050242110341c03001038002c0554011052103070b104c0d125000b0750f01030550f0300303008221704082c03002d03480141c3c1c0d910441d04480c0c0c2070030411141c00012584d400e02a24448800e2640b0343d220f1148a = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 237172859 1250 237171609 237171619
    0xe060607050708070f0f0f0302101209020402030a02030618092a03060901060512010903050415030f05270c091605040b07060519020909042009010f030b09070b030105 73
    0xc44418041c0910480001c0d0110006544455071380f5807025450600e1401401c200764202e01c000076161003d2264041100d501510240000355a5802543c400e01c0020141014036218501800169100d00c000d52081400391300044e16800c00c84c052100b8151405070003da83c14115050052103c4001408504101c0c500c03004007903600103c1400100a070040a0070360140b080798140001040b043d040340381610403d80d0400040c4034030f0032409081c2c40350320700090007042040000784a0a007299010441c41141030070007107480440d894581c3d0888070110b65400394040d440c0d155080c2150840079140c460b0a54000070050340d8403404c0010800e00000c1c018000440301403580000030740c01201070301c00404007d08007503101ca045050440181c00c0c02c441e4401500304c1d0010900d2881614400c1d61000f142c0a0140e8803240d495039290450b903445920500d0308038101d203c10813015500d008440740a451420030010050b071461420045450000e4007081c030300c0e00305120078040a100d25054170304403002210 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 237174109 1250 237172859 237172867
    0x80306040e16050909070b07021c0807030804021914040e0705130522050d230d020d06050f0d1e12030506010f0e01020a03140c0a0b15010503010e0606 66
    0x10019005000290a00016014001d090a242d44091080030210340d03080d5640e0700d041c2e0710814101e44071a004d0240c48403140061080314003504140001d450390300c0307041510b14010b28580c1c40c3c00505800420303013140000d160004100071820304040c2c42440254080101d01c425040200149c1d408181014050003955074a0000a425000f048004000e040140041c20181c010700340880c05030008440e050904480140c1d54540008840e03219402d098026003d80350341499005c08403501c07001034182c10328203201c0c4540e01d00d10080a2000b07201a0a40140060341e840501d0042c0c42034491a80c0f2180c0310701000c5403040c1031741c1c442100061102c1c1c1d00880041035205000100903240240e0500a002034040150b00d031001601540180c1c0146800d032110a4034440c1c0c440c040703c0e002801e4891a0050300b0883c0c5484c0040d0003882c94100103658100e04c0e9050905c4007000a01c2c0001841d07054030f51401403400c1c002000304120f441c0412003401c0c43c21510310760602c16140805074014000c0303809000006 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 237175359 1250 237174109 237174121
    0x306020708041a180d020d0201030e0106050909010c0311090604030b0c1207030b01200304290a0c20090c07150501090c1206150503040206130b030106030b030f0a0803 73
    0x101c200d8019105400042c002d045105000d640d07079420062441c090080100141d04140c6000943c5c04030059005004c5894030240d0b81c01100134200298080440f59211b50300803072550783e80708034544035070280c1c0d00000d026035000310b0040a444c2c00f00d0000100d0113040101901d5a128074044409480d04042c8400325603c0c3e800c1d05c02042e01c540022483d281d5220414000c9290740360700520001c2c002641c890459070040360b0110140c403580d060080039a402000b08011540da5003410403840000342442081c482d82400c48101c0390340c040e0300740c1d5001072a240e1045c1c080156090341d81c0e011070b402d03640050490080e00045201d800c4050702000342e1810200d4240c04000b20b41d80c51b1183c080c241c0b0030038060b65a580401601808c450f40011020452107a291451904030780f140004a071020f8031001810102c400090b00e00707510141c070990304058104810341c1c0c4c4032241e0080400402d00006408d03901d42c90600d00904035041680868440c6e0406d82d03840c54070400009000e552030390400c2401d030750f9880385 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 237176609 1250 237175359 237175373
    0x150f070f0908070b030610030e06072015010905010f23040f022803140402190e040c051306030206120703020d0608070905060307031a0606070b0c070606081603060207 73
    0x1507405640c0b20f104025000c140382484001460003100b040d2416504164200810713401c2c5c44248203c1001d035404200081e0106209000388241510000348001d031624103c1d1b1000e04181d6a417601c0540c01c80c41600400c10483c1c603205850043c420203811800042c00c141c05803040d2140c414003500c4200320184100780b6951079038442608a981c13041c1c115600c0c1d0340040b0054007480744c400b000b0f41c0c5240f0180118400c034003e01460059901d00311340c050144da150b50070004281c4403d00c0359203000740200c030081506c0b451000c83d18001e50050705100300961410301080100035001085040c9541048001c0005889004c19141380a5881035420a1581c802d10103c0003402101415100325041c00400501013402245500507034070303d1a02880a03644000c01c0c9a51107803184001080c507201d511894819480c0c0304242a0000c0c0002e00c55490140c0c15102c0c060103180680d9980c1c0c441c00005101030802030316216103001441004c014054404000c400d03024518940e2201a1001c1e40020b2600c0030040c00e = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 237177859 1250 237176609 237176627
    0x1d0a060f151e020c010f020303060f06030c0705010c0809060c04030206040b030604090203100f0b060c030327101a0d03020d140409020408061f1404020c0102072102150f070f 76
    0xa040381d84800c2034902c40296150300da14103c5000c101c003940c00c030600503c007100701d0b44942005040c00c03005101e004240020b960005090502c0544103228000c0007503401c3c0078204001160b6a9410300034102010058107280b0068041d0542c0c0204100400068540e202980e04550750303031152980f01d59078000030a024040800c6d000350315029144510b03a400200340d008502000ca003031001c0007098100014450b0911940d05203a060350700500c0090b07103070150344950b00003d520320480d41c140800c10004d92807030400c3c0361040b6108141c17988210319400641c0b100b0322811074003c4407030541c1c40c615902c001e900c0c1c0104c08421020002007211502d00a810b41044600502c0d014204550306d0f542d0392450340c2c035030070191001c800316080302000059005841d22064103035224040b40b00e48540701d0004100007980304130707166070165400740105000b007440b86440245440010f080b0010305800100028201050030300b6040c21440960140450149107a86040e0f1041450511151000390756400b9180801 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 237179109 1250 237177859 237177887
    0x306030f060c2d16050a0606120b090309240405030f060105030d051206060703170a0b03011b02060f07030213060f0e0409030c02090c131d0a060f15 65
    0x101d401c050103009041200104080415000d81070038000000304103180c484200e0315903001c10b800034400c881c0099441d003c3c1141851169086030020b140f650b07244000e80d0000d40c000503c0003003c580e080b06011550031841e41c0014500040c42c60300b942000000c02480c80171001005015007000a40c500040480c221000b400d0700804032980032024981c0c0700d68800c800d0142c94085d010701c080010000e4010340035a4021003070084c00501c03554808003481510b82000000f0740c01c00408440c80340e030b0b620f2201001c0f4040d90400002181c2d440101c4245400c0d501c00408006102e608504841c05e45980420400d4102216039000100313500c07243c030114080e01400e5500c80780c4c02001000059000d403c458020b00c0705110b41c80b4509000345843c00c00007221300344140907010a03603812100700180b4121070300b942c2c4a01220601402c1400c0c80d0842a0b0030043da03040100c0c140c165031000d103002c0701005165940700c401801e0a00007181440764040352040749100303002f41e500e40c2c0103143c2c41c2540101e4441480403 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 237180359 1250 237179109 237179113
    0x6030606051920030301080c0913030f05040906030515010e0c25082b0c08060d060f11070b06030a050c0d0804050306040b070f081b0f040506120103120807140306030f 73
    0x1141c1d00111135201e40c401c3c42a50118071504180358454201005040d04c0b0b480307803d41407404d65225480603101640d41400148c20040204004100034009118520265018100401c1e801e0400703460240d604106030080060700c4040d2080200d8144800c084421441040440552a445c1d118010b01c0800842d44000c10030400481c51855140701882d03417602191200701e040700c2c09000200400221f8071000703038880010f44c9107400a13400c7d05007422030340390003449880001390010b400c440c0d43e001c4540c41c1101e0660884001840000d00c50710400300d070342200c030803005403045035413a03501c00f40e6901c0800c0d4518060201c20200405001e40002602c000304405803e40c1e10303618042c40c100340394100803900308021620300100c44d11128030680040780b04801c1e00c01800f00c070001861f941035854111030340c1105880d401300004249601e440020309622030341d03105050780650442c50048140450184020200305c04602001101544500381458543c2280e100603580c0d115440420304084082c0740700c02d458 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 237181609 1250 237180359 237180407
    0x2010c15050702060f161d1e0f0102070503060403030914031903180c0302091003081303030207050d03050d09020a03020409110f0109060c06050a02040e010609050102010501060306060519 82
    0x4050940107180309a40c15400c1e1041c41d030700c0c80941c0300b10300400c0d0713240e41da00301e040f0401c04031090189069600c2d031050003110724252107080002414100c0c18440c00c142d02c420707203004c0b0780080c01c2c468a403080300070302400a080c80c6805e04021035903c420003040030701010781300d0a89a0520104441203042c41041d4000c0c3d903959040044042c0426001e0314542001038980f200618094880d110615070780c96103c0440410207155408222008102906501d0400c0c00020000001180a030003404513040d100c000001451641c18080c1c01c14155602560003a03500001e0000000d03808000ca6600c040351240c0001c12400c14000b0034954030040d0002904140303001d00030b40a005681000300660f1104560002007440d070b0741c0044814111510440d408580b64921580014405800083c3d00030080034005051a07a564001e03801d1010030381c03044010685401040c4010f5174280201c3d4094041401c080c040d051800e0380c010040e00c150090b09100f566100140356040d81709811041c40701c031018410041c0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 237182859 1250 237181609 237181643
    0x203040503031905090a03050d0e180412050c0709060f05060c0709110d0203070c0b06040b100804060b180a060605030112080a020c040507030e0115150513050904031115040c1202010c 80
    0x7940051008a1010031b5110740f41550b1403400d045c0c2f01402031160048018103448a84d0b45811007000302000000b80441808080d03645141086031174002c000e45100865418944a6810034204103900200e005900820a4411000300041c101044405026000451580380ca0100005000e903404c100c10040c000405c3c002c1d903030b0f4000d070203001081c000c8103645510b449400800c411150540305040e08007142c15112555103001c1c2c942d9503405030168001080340d4800c4400104250360091010300c00c254800d00740251b00000e441a03c02401c05410328a242d0350405034628100d4500e03800050030258002840d4400e1031092000d000c2c8250301404c240000d0800c2c0340007901409400904054540ca0551002014402441020122031070280703141c03084042c0800403100c0d90701100e052141c1795044080002c0c0c80d22502c3c80144514041e40e40c0341e5125200d1481281003880c15210144504541014000891803140c640f408841020410f54003003501440142e59102c07440b07402511896942001000d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 237184109 1250 237182859 237182863
    0x22020304060e0d030e0714060c0303010305010c1707170c0c01060e0105040b04020405060306040207051603210e101101060b03011d09060c0d02031003060f09120203040503031905090a0305 82
    0xb114108070054407981c0246100031001c0700d10368040d221081d0310540c810418681090401c0351410000f4000038609034500400071b2842c2c0c000e910464803a0b644060001941c0ea2011103030089001601844516007440f44000740700101421080c00c0c200b0710500440e00280c0394004461198030040024400303190380d00369040c650300c02481100c1c001d600340128400340385400d100303e8058880003009103003151540410b03c07000303400041049501d072213902510b80c584007440307020310000c510074113003031030070080e08448140e8641e42598104103205c0743c405942021398400340709608002036854110580580040c00c0c0b4050007450340412603811000002042d0745241054800d064049214100c0c25600d80b017070070315996a002c84070301d0008041032080543d0240c41d078004580042c9504091070006880703407184402c0b80c81651403060b440da82c58104c0020002400101400360056001860500d4070703040100f5100d201d58110340e03112079140940000303124011003d541c0c2c03c40c4090810396166840e0700d4004c0d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 237185359 1250 237184109 237184121
    0xc090f151c05010c0e060a12090501140408091302040303120b13090302100507530a050f06010e0d060e0304030305070b0108010501030f0605041a13140105152202030406 74
    0x1000155410b91141c08508060041f5a08405a5561141d44250b2403281000510580c1c104403400d5494041030f020302c1c40d03001e0480340954061250699582034900800221161304005071038054014401080440c0d081001503001549003000032602940300d00014482050071103001000d185414440c0c4185680001c2c2d440c20280c94500802c00c0c2d40743c0d03801c01d50300c0241c5591a985041c7c82071501c813016141c00c0c0545600f80d000030550750355070116904002032044c0f203503003040c0840c6889003c21205c0c81c2ba90080c5c0f500f189040c40c1ca40301c0e1381450f0300000c1030310501441081c0225440e4190b0b804000d0039512407024004036030203070b03501d030b9840f4a40180b9030b6001c6002544c04498110000c1007026040c40340504070b0368800f402d240104415590800600001403064991020000595001e00c814040301d034400d02c0c05070400c07500070585190403802c228501a561815a08d850204040b5035012504042c011104440c41b610366040010007088074045230010b0a1502c2c004402c2c0401c00116402c91 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 237186609 1250 237185359 237185381
    0xb01030209100f09090212070e06100306030506011212091a070c0b030405060f07020f0604020d080c0f01020d0c020a08070b190207050a110609150f070c03050a03020c090f151c0501 79
    0xd0f0700c3c0501d0355800160388603c1030040300c20149c1d1420100c2d040340fa0181d9040e42e81d02480c20045a003941c0d94072280c2c14103800b6801080d40c1b00700c0440c0c800400c0b529143c0072040700454201401054206150781c42042003454031943c1d010800101d400500400921400c014030360000c2d590340d40d2506140c16030322a24103450200740c52003500c0c003040d07903a0300100701c03441a0080100200065581c1d9000c100c1d40481015095940385001c000e0183c4202c1c061125094002c020030000d030b550a00f00e04242c0031a040e5218007011504418400030008010703008403200c880c1c12100909843c4c81e540520104051041c180f892143d10005008042000105015405a010b0024456451700e0b0300140801c41c455114125802600c1c000120b0010080f413020b444003040c128400d41c2400c0556940c0144203102d500709840a07404040301100301075041001c2e100030384007580c210b0958180f040f000202c014014000a6105050303c2404c0c1036611404220490b031351881048400b0f1400031b041c0350340204aa0028 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 237187859 1250 237186609 237186619
    0x15280f0317030c0a1214130b070215011a0c0d03091a06090601032c01150605070206070f0204092003120a020316050a06021c0f06030b01030209100f090902 68
    0x15031501075007071105480c86000421031003450651001e02c115a4085240880440207569640115030413912061a07440359180200101d1480032506007072002c000300030040821175200d0352240503860880801036045a04010b8090030044001031624001d000b402240103051107000c44d5181016070581000b85144c0c088d00440807030b0643d2400011001d0400c0300c0080d0002100d0b00811950352190703028010020201188005030f05041011940b014403a4508103402c0c0e44962412000f10071440b8140300500c01402c2c01c1346008481c0e404102240180b2902a1021041490f14000e640311504082d09050b4481d150030460001003100303654070781c12400e1300b500034401c00020010f49003e0800702c0b48184840e400450400751204014078116078415402c40701c038010f0140c8100052058009014410300710794074060743c1504001d800f070482d103042c410000081c2c01c0601c1000800d95100215054035010f50394028699501170a10a000c074003944102080d40c03081c000000e01c5846a48106115442168 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 237189109 1250 237187859 237187883
    0x5152415030c0403150b1806040e0601080c011101090525091b020c030601050a120c050301050a0203040b0c04120602180a0602160f241b030f0e010815280f03 69
    0x3c50a0446c0d1303003007100b036030094070116150000c100e0400220b03900c5007000f400407504204807000541040310a03803206e46143d0159402e00d0066800c441c00840e200d05c503c00800c1210030a40701d031a512030480b031400d1074010507240031900e1600840300034800ba1620003420700500614140d8109a55507441d42c0c0801805407001008051801040b05030480760003c0044116030b0810041100742050403008491090200600151a80b03082c02010300c20213138040010384034909070502405242c1d0080000059043c204014484d0103400c10060f40c10a410400050300d800f402c0b484003085810b0612895808004190300080c5c050740042d9600c5d980b4000403825031000e948104920100da464001c421103000c024007080c1008030030550a02d01920309181c1454807080d010b10204000c29155400d40004418a03500400181c00001d15030186400f8641120340f403600c60b80e080b00303280300395405a220b280080e11080c560342242400782041800b4030240b400c040d60b00c107040c1d04203a58500c01202c030312031044 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 237190359 1250 237189109 237189143
    0x40201080702060f06040f090204140105041103161223160c0305220302060408061611030352020a0309060e0607080a03020705152415030c0403 63
    0x418024000c400d80f071541e070380f103454000811007c0c00c503c01c0718500269441c264100565558040c2d4401540c500088034159410107080c041a1558800010700d1740904209021308051500e62288003485c1c1072428001c014040001c2d0409048003421400010200009694442941c00c02c41030141241080282620240c1c150a403810319a01d2030143c040303034007840b200101070302c13680b02c007003101d0f41c1130208003013260300c9500085841c1c01c0386d00088140d0f4010b00403c40d041400c884200602d6959080c254000e21004440568034030005100701c40e0700400c1000c1c42d28035003a441070384e8000c1e0f500c40b62401d0700300803a103031307010b0080c80ca4050b8030105a5454031084905002044002c080c68240e42c50404840c1004c5007070320b2070000d11103659008102006041c0c0440c0c181d01c05460410500e03500940c0d01c25207030420350716102045900c0100b19102409104a09044010600da00c40081c0321040b5075601201c001000b01da01d1880d05000c1150003c1003210f598a80b03001030050328881e18002c0300b015030751 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 237191609 1250 237190359 237190363
    0x609060e010c0f091205150108030c010b030a0c051e1e01080c070b07140f0a11100b0f0f030a020301051f0e16030f0902100206011809020315131208040201080702 71
    0x180c00c0300f000c034201800c2803003540301100030250800e01903404c9821010a95441b058040f4090340401074a400c0411501c00e129428090602c0c560022802800d00740001e8961040d078180d02d1080b240300e402c881c1143e601050040d20009511783c402061000e4188040404a9002112581c07050014880e40005402020300005541310313140c1007003a46a180d601c2c0882511807040c10709488d203074007200780019076204402c9030040054502580c2c8607400095155901807078840c202944905260400690500d40e4a035800d200101d8502111038aa9007401c0b900824100f9004080c0a50554281400c0141c002244e00e20100d10a00c55615912801d641e004420315003001038480700610140d52032016440c51007500010402a1a0703c1e00003007110301d031340c00103001c0f2003880350500168101c1c500402a500c21805105020800031b8800c0c03224111542c002078455a40d0070001d83d0402c0420080741c42c2092140d030b000c12190380400c80000464100101a2032054202c1c1d049000503540d200003281c480c40 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 237192859 1250 237191609 237191627
    0x50102010608120928060306050429010302090a140102060c0c030403030305040213140106030b0409031e030204080d03050a05070509090712020d06060507050f0114070804020d0609060e010c 83
    0x4001d015040f504084a625622070344580e0b100d6600140f44465400007401c40c0e80700c4541c5400401010851502d40707940a002d807a1254000342c412845c140b140d0000175201e0041800029195224050b099046030061f0000d0244240ca981c000741b8040300420040781c1001070500c4007109808803407440d42c41c268a44001c3c49103014220309504140004c00c0024066000250424030040041c0a803900400168080300c007071840e003900074440c0d00c0c0100302e81c40e0144030f040407042c4242c07001d0004032000d03100500300403003c01c0d004076440c2c03a034020001418401d80c15030740a8081c01c001c0d1400a03004100080150005507030418500d40340c10040342d03079103010b82c00303d41c0007207400381440e040c940d50f50906840000c0004622031849400b0010801d140802c4c2c42041c0141c502030b21346a4480c40c040c100b561a2480c00b0300340000503032601031565074903400c1c032003026400b4660307142604280c0e442340b001c80c00880c00d03424001c010a00307003440c5c8000c00030140c2103c600600103000803c00551a40f0b01100c1400c0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 237194109 1250 237192859 237192869
    0x906090501030309030809030709020c0a0605070f0c15150f03030e040915020a0c02060a02160b25050304030b0406020702040b031c0c11120d08010b0c031602010c0615050a0501020106 80
    0x10700920704200181c108005447c203268000c05581d0869501e00603031050b42d2000444502d05d81129a10008000482c0710301c5400c00d0761403404180801c100351026120158041c00170b09941604154484440055000070101044415881030400d5440014500a12182c0401c90101c0c0c140f0856851a003800d204200320190014081c110550502809000960003c0c4003501085902207014015841300350091203580304542c01000482a0b0083c0100c6002c1c00390001039005a04020301c0c04952140c400444002034000c03581100d444003450044d1451040c2d90000788040001002c0105114295018100041c020395082c0b01d052546402c15403a60301c4040c84074103104120541300c90340c030300c0381c498a803072140310300300d10601c440030710300042c610b030740e402c002c00441d58400685440c01551041d401801031031820b1106052404643c0026200e020321502d110401c11420340103800e6a10600702c22568a40286007040700200300007203842c1040031400f5a9001e080c1842002400354814825002251 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 237195359 1250 237194109 237194117
    0x12051e03041104020901020307140714060f030406110c010915050603030a090e0606070c0e16050a080402060d140f040318030b13050c0306010e0f07090b03040b10120302010609060905010303 83
    0xb044508110080d004020803170304500c8107200b0b07413001500710a680d035071200b044c600400100d490220349002c00c600c10010720380503000c2401941e00c1d643e40c10094940103903000380040f8000804140c41c80d4a4004c440c520306466003040d030300c4428002c10400c4403158231000d020900003a6612400d2590302c0c4141103000c1d00050b200c440400802d001e0050117030f00070a00601417403902805e0740b54411295074907002990b0841008041c004960b49404259151140c641801802c01c0e118080140c070b007490040000e40100c01c002a6a40580b2070740d404000b04000c1c00c1300c500c540e030400b1a560104144216006c5002c50107402e195100c0f03451403d03540040700d901a032005444d90354143e03810100818514101d03101d12034030425400c0c9540601410b0b000c0d040c407044004203032801c02150703d400d1201415074810f1000700b190a00c1038003c0d107003c40740e0043c1c01c01303181c10542d101c101007200f25002550240c124910710062000c00c040d819003205040b600d81001c06d1200f10780720391780d5008440d020300c8010041 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 237196609 1250 237195359 237195383
    0x70e01080607110304080109062720030c270a021c0f0b03030705060a1103060603040609020a03050714150306010906110c031005040516060f03090203010912051e0304 73
    0x2e1446444000c2c1e0714600e540070b490502d603036240c4050a4401380e0304110b41d041d45450014240400d9400000e900e11742d800d00d18040c10001e9100c1d607510400306c403030640e01041c0c400c1452259403000c110020202201921890b4400070611501110b6454140a100c450f14030f0004100c0d44049402030722021900f10040b1800030000c8018034000304139540c1c14050445d12600d841480e42c1e400d2002e000201c1c040d0010b0291843c061a00d40e0842e00b1a100d21240e20700244144140343d2241401d0304d600551183c00001e006400d8000502d00031060340c001000d0788503081c0081040140002880b501d90015a445840f1281c0401c2560b40c0303010484540d030008540900400840348030f20f003005204001c440643d14142d803114042070070083c1260147c00b202da00c450511042000c100142a40e0b1401c81040e25406420030f14024014820b150000e410151a01c500c0c0080d55402e5018840302a4821902800c0b0501ca0002a1098100500c2c1c860039041c40b944030344400e03084a0880e8803c6078001000701c80703 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 237197859 1250 237196609 237196621
    0x607080421090302030703030f080a0903020303070c0f170a020d09050328051b0a1e090221040b07090e091c11031305090c1c0903050723070e010806 65
    0x9000844071510412000540001c05610700748807040245000f540d85000822030054050303d0303c007000e0015020a0b103401020340c0803e40c0882034940207031741454000c1c1b480c2603c1c101815984000e0b41f0141c161810303c4000302c81c08581c080140a44060358080c0e501c0c006402e8415a01520903219039601508620f070700300101040007110200100e0a8200d00000115503228117250032005c6444441c240c0d01c40000c1880c3e4a0800030040042400b95542108082c000c042d00d150358a162258010381900440c106c6500026030400603a40c0746c6580703101149250a041009404c1e10544e86d08000c1441080b0100380c0028180c1c6842c850b008035001003407804888001004c5484065200300304201d11001c40300703100c070400c0c0000c1850000c48140071030214105403c012002d000644240320b05c81c01005500c400a00c0440785812449040c0c4000a00b9075003810b081c1c1d01c0b4464200010007414100260f100d40b039a02540300c0e00c2d01840c85003100c8809450310401c5e98801428020031266620110000d40 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 237199109 1250 237197859 237197903
    0x8010609120212031909030512210a020d2301050402030c030117150c0a1403090c060c031312060606030b06090f030a0c080d08092d0102040f0b0403020306070804 71
    0xd143c40c403003007220701d003401240202400f080c000d103007900050b20390f00040003440f20400200141d400b00400d22403a11084150100c10b940c484070024849180d800001400304403e60b064a90011100c0b0f0103000d640e5164044194000c0c0c141c501c0d010742c4150781c0002c6104e0405200307070b80c0308001c100d40c0c407443d41c3d003840201204507074040211609441642100401c0c081400b880030f004104c088115600d4464480d0050407483c5881c4c0d107010080000d20030800c903090001000b1040709010395101e40d84526005005081d440b40c10420510110003400024a440104035071114040c05040f08200481d21000e00700c0650b0b8815103041da1080e0140460403080c40d009100002d81c54009040390b04490182d82e40e10194250b5070f00010251300044040d50096400040680d40f029030180a070040c034000850154015194804140c0752403070050710400070f40e4003513040340c0c05840c980c1c0c00c80c0002941c030f0001c600540c1c0a404200d009028040100d06a58050130520703019a51220070f03071022006100d0600 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 237200359 1250 237199109 237199129
    0x1e060803071704080d0c14010b030c0111101b022103070e040f05010602010213170303130813030f0210030209010e040506010318060209150a09090c09080d0f080106091202 75
    0x21081002040005650131003000040510542500c980d9060503850806c11403044603501d042c1c0702641071022500d8165008160404e02e42000d0a080008030381c26002140340c03d01e100c0394005482e28004041049032070589007294078103100d0b400c48846044003134130080d440b81e440a90810750030003800840e200500480e141c00080401820000c0d0040e058801d03001030750001e80c48180541d41c0001c83c914400004a1150003404102074039aa139800301a031415640d00c401070900e83c1000040022404008142c0216070130340803246000114543c50b030810600f080b802c1c800c103e03c0b400c0d0324911040e07a00c0c003d000741c4424001c140c442c405100402030500001d0301c070040c4040d04242e40e03000100041641c40080011890041d040113817100030441c1803102080b8184505554040c050244c170b8240c5a10554003020b4501404d00400e01302041402550303112065000442e0b24025a004210380c035a00c171500640c084030a0390b80220a90b0b0b560019180c0568a000e0350b104074072054441000360078048940 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 237201609 1250 237200359 237200393
    0x12020f030901050a0e04051f1703030109020a0507021224060105090d050c04091a0604050105061c1b080405011406031011040f0803030f0606250c030804091e06080307 73
    0x9615a82c8000006d801c40e0411a20003003d20111160035185c8a1800c551302c02800320088100f40003ca9103058a6480c0014851031204640001d045900f031481407007541d046035030103056048001c250101d841d0319154100c001c0300e004a80c0171001c00e1500c100700d44080c0181d40c180c403600c0c50181104284880450360030401d581030300c11001c0302041c075100c511502d400300e805503040104c01050941e03a100d0b4103001a040500c1541414014000381d07440390222901040ba820078000d00f0b04084000002a081903500104040f98100d040e0790410340028495120f00c1c4902c00070000d84c030302c000c806192500290780c070582550290030f0704400005c00380e021003600408000c507503080a5a50b104000e0a180c5504103190725003021003440010320310001b000b500704000710703041414111030801d109071460f00e0010071405000c07400503041c14464105214400786400520340303681d0b903450340003944c054a000030541c9420a9240d480009916862098038151204480034515000060b103036000c042400c4440 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 237202859 1250 237201609 237201617
    0x80403020115060203041a0a0e010c14070909050f06010e0610050f0d0c110a03120c0e0d030306060f0c1a0c040f080c0a05011826060f010312020f030901050a 69
    0x2c0c21401c0054016280000d012030783c0251364444c14560030000381e4001403610608410f091041290441d0040945000b81f4020303e0150500080f60405c0d1402d95045c6100207400c0c00784041c049000e0101c1d410040f80c2c03502800c00c41d4211101c41001583e02c18007441071a29012490b00840e1765450706005d2051035071540e01c2c0c294100740554040c0302117035000358519178506544a09910303500e50480940715400015074041c0c8003411403901c01800e41a180307842c1d071054a81d03d003020440c0e54016103a00e00390041c00f6050340741105072450050000c2c8a0360040720045a0b076000071b6104203100e0350800d00e40d0303540414241e88458000e0401140754402070324600904100b4440424880000b001d944002d005000003401c0820094042c08a60109508030740e04000500550204a407244041c050440d0150b030214849020720b8008002c1c0d1991042030501035000344010b0041304081c3c001820b0580e4081c1240041a5000341c0c3c060380d9a520304030308049a0380003401007507065070041016020211791070034 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 237204109 1250 237202859 237202871
    0x21f0206060118050a180c18091805010203100305010e0316150905030c030316032304030207050d050c0f01050901170402010903020907021e010216060506130204120501110412030804030201 83
    0x70014031081120b4004503400781e040852084038881b0b601613441d140382c0a00b4100d440301030b520310300c0812074418069009908d45503e00015905803103000d51500031f4010008540380e0615a40414690545100030344656003807030460300b414000401110a066179451170000358600c44d81c0c0b1900700440c0c15000040c0307580d45440b0600422001e00041c0f546c0641000515907a02d01004007284115003190284101032a0a042c80d2a8401032403e400f2103044a250f5001559100d1504030310b4100d0030b800450300301040300e403aa002c021001074800c0700d1940464030311382e61011103c01103d207402a441c050b0300040c40d444003140124030000d400768100d80185880410366031030ba0041036000d03e0607105180141d00007001800b40341c261905040b40c17046420025031130801000c8800c0303030094005c10040c14241e6180301080c010f80d40c1c0001d41a040320032403000e54581c0d0b03488011340300f9184508001d44807542001600e0340d1080303072001100c06a800d4100181242e6600da20101c5428170014422000d6641c0c0b01 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 237205359 1250 237204109 237204119
    0x9030615030602030405030c301e0d020d06051905060a11010207030f021c08180709060603200c190f050601032102070e0109090c12080304021f0206060118 68
    0x3c00103520450046009655030070040c4506403a010f503040050270700105050360709010548030021540b01c202c01d00308103522000900300c09a4085c03c0142c44003c2840005425045805c00f500504500c29810341c00300000390355071091001851000074102c2014030300070014000c501d080d0001e0f007402c00382860445511041148068220f07408401c00307401103480c0b0900709040d15410030800c00c2e800003050009009400d040c0c400f0386080c0014159482075034405035010b0b214002007010310010400d440050203182e0b62050b0140040c451440c44000d02e01560f08655000c5921208551301d40c0040001022209079a500c805200883ca01048030300f03200b03031104c0c440410010081140030b14090303021441078460610002c2404040d110115040d500051002c0004481c0101b00030b0444008800c04621280e452422092a00c4160050f138804138071060410203000794000031b9480b5601c00d40d4044502e9400840600b807190b0160003d01c01039110741f000400780e500c40e10041442d0720b410201c0405c580d46807 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 237206609 1250 237205359 237205361
    0xc0609140d140708030a05120a231b030a0903030b0d210c060504050106080601410d05010b0306010b04181e0f0905010c0f09120804091d0c060a090306150306 69
    0x1454900002440450a00c420034540e21000380c20104d4600200070100703cac11900b1624102e00941040c112000740300155504982c0400060080790044046540b0300c0c0c5001081c000b4078038200d0607400246030540c1700000e418151040c10085820166020816040c3d04100b80f0000140348031104100ea00e0202c90f001540350701480d40118031880003c00d2190412a480d4070300039050748180791240c0414150800000c9603152034000c8001400c2884040c1c00d0790910140d070700c49060989070408000640300301441070660141d074141c00f0032416260310766a903082400c007a0280d4000e04440d490201d000c0f00403820980c0c0000c6902c0d84415540c1068410445100103d48402116031504c0380c480858004003e000e20a0302c4003c1c03103900307240c2074010220a0080c498015030040180007420200207505006e806015a4000c0416403401c0c003801003070104810000e02d03d803000b500b080c854543c007170190345020016184604100d41e2404121491503e0b540b01401002c6d40c0b102c6c50042d00e0601101081e51 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 237207859 1250 237206609 237206617
    0x90403090e0a0605150901030507050301062a080c0a170403030f0e21011e02120414121303050c03280206070b01031101080a0605030a030c1e0c0609140d14070803 71
    0x705c1103010346031100c0340d0000d0260b900041512040003c2000180205c0360404d8000000c8020900c1c80443d02e02c0d05030303400100e2a900c40c2c015048403400b0500350108000003405c1043d8500c1032004904907000020081d02900850100601154206600d1204030340700d401d401068281c0200400070480320040068102480d030b110b5201d03940d450b0719603114854913203400c200780b81e136035030b40704500d000c40c000c4820356155409032008206107038100e09009104030030410b50b401200644d2900343d40382c21700340c503000c42c6403c188030844483c02010f4501ca103038980882c000c42c6040c10000704d07250000f0403d080380c030703000c1d141041240c0c0031505210700d5002c1000c1c070040c43d0203188515000c90304100341c1b83c0090301c4003800030413413000c85040c0340050015840110706190034070361508010800b103860380341114620301e40c001e4a00c200c88100c20801d05110300303e040d0034103c2d02c0c183c891000c0d498032240e4510392003002c4040690031143c0801300900180842c2e40c001000544801982c400710740314440241107500c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 237209109 1250 237207859 237207889
    0x1080d0e0d02043314062b0213050f030307020105030714041d09010b091501020f0708150c070c0b030a06030206031005010f020703020102150421050c011a030a150f06180b090403090e0a0605 83
    0xa804074080c407000c091309c3ca050000d0841200c007418451840340029580b4490042c00030b04000001c000300e07041600450360f40e500290386c0441141c0b44c9894648441d08000c0102c41102161401c3d00070520703c541c103114400c0b10f504040c04580c03c56858582400507140961700713580c11071040c1d00010301114003d020001c040e205a1015140b8250100d4400046100c00b602e07100c0d003500c0420913040016140141d040c21250340822580c0c596031200c0c0c02c8401031010740e01c040d401c6030b030000402891040c0750003100103031503003601d9603055426181400caa80c0c4c0d03000c0c04000d026034000e04080c07030ba81703480c007034410780c007034460142074844204130088825001e0025048401080780410300450342602070140b103002c4030352030200c0c0704481d40200000703549001289001d0155640200c0c0c480011025800048010004103001d2240660790803500281c0664074181000705c9250604032006458038014041c0581d405556515032070341045810078507014050085181d941e030f02d01000440740c440c0421680b10403 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 237210359 1250 237209109 237209111
    0x1c03020c060c0106030b0105090702060a0e0a0204091a0a020f09060705010b181005010c172101060207050f030601050d080a02070503010606050406031401080d0e0d02043314062b 78
    0x10780345181081c6c81c02c0060708801e110318001001c2200d07050b4001031655210b50100d0000c58800e120002050030084419000b94110b400c0010365001c0c4407880c203981c1841104840c0e008802e6a40b0384e03580049000c0c1c00c2503c444900c08000030700700f52800c2809002c84d24015400050003000b01c1c00000d600301407000c46140110082c0c42000800605584400000e010a00300b48040400c01e90b6071417001c9104100450300360001050b240b00000b0300e0341600044281d15249401c0c6540c442e4806540c6504912401e4440c035800305641c0128100400e170241241c9020707040e0083c2c6000d40e92680120b40040c40d080007180f058480014195409002d04402030915848107603646040400060544600c007049480800c0c01d00c0c01040041c00c005042a40c240003450701c81c22714400b4000140000b2100c0038007941c0b1074145504811843c80743d00c100361240406149449a40440c0406180246a584511144007a0820081415040c4a40108440d42100c00e51240140410205110b114090641001c8907 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 237211609 1250 237210359 237210371
    0x406170f0a02010e1e030601140307060e0d060518010501030b04120302070b041401090602040b041401020d02190821061207030f060e03040f14010206070306051c03020c060c01 77
    0x1a0a22922880e4004103028040ea07281940020701990900c80130940520b045010055410b210302900010340c0c000207003500eaa40d65146414650744400b4611103220b0700814100159041c0a4085240c1d503990191400c0503140150f01d91100a050040070790a00420070349480c224a0028420703203010798403500d420034080c10117040080b050940c4030220750500d8410464040422080304000d544240d12881c502c4441e50350064442c09002c1e040320091100c0d001040c007050700000d050240c07059401c4012005642e83c1000b004a960300c680c46540405078011811410400c030032840000b050340d02840050b850903c180c4095142d03104ac8400450202c0e138060280509403401480c40900246104000c0c4210342c29034862000d4140d0b2200b00518083e910041e21106840501c25070340100201d00e103a44070640c0d5681100300c1c0c100141c030114014042d142c0001d1245000b40f080c4401e41d08050b1146003a02d26007000006c1c0d04000d0700c0c042d4158071858820010545e00e000003041e001090600100309 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 237212859 1250 237211609 237211649
    0x50a050303010e0a02040b0304060509030d0914120703211119170603030a0e0a0302090711070b03010e070509040605040213090501170a0f0c05460b0a05090406 70
    0x31070500079007504e04480c01000100042e41462003505d8016400100c0046c05466104010345584112000d00c40000e043c4808182032244001c83d0b0164207040c8e00036036403c0d0400c01c02c203040510400100801007031205112644c1c142d00b0107941070003610340382e40029400c106900f1051641d00300740b048e898a038840340c02200c40d0592181808605102d407070842c98050500c1c0c2c000035240c0c00342c812207908020b00700c5003002a90f03840061000056070068034824090611240040c0703050116040c158242c0304040d40065000c1c5010304990403a2068510503401d40c540c02411103003680b001c0760040e44981c85100108165440388024140700c070454040c25030840c50715260700241e0380164450030b5404c94080381c050107600e0104490035880c0d845280c1c07011001c0d461601d5050b01c0c1c481c0c0c104580201b4000d4020080030000b00d01043c100d10080c120b4134901000010a03402d0842900c0ba042c2004401241008046813607405040c03441900d00b4060304080307050000ca811108213034000b07108800007880d1411 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 237214109 1250 237212859 237212879
    0x411150a0f1404060c020d020907020114070503060a0b0c0f01061712130b1c0203070c060b0904020f01051e0f1305060412080304020a090f20040f03110a03050a05030301 74
    0x11100d10798145512100300021180d581c80c040c910074802881014100e60046695541c0001d020603401000d101c82402c14560082c000c26141d40903000b118003c1005c560218024016240b09000013800701015a040a80c00c41d0107401443c000c5281c0d1181070040004101e003805040c003d0003500b28031001261170a01c07554030b80030203005180010b00c4200b144106d00d1480f8032014041e105045907180c1d84000c12007005040304407240407088214404170901030342d10742c00b0003078146484c010001407002032078002c2044120320068a000b90301000d94058518194050405403050f1030160300c08210394420b0321260307181540710760300400f030b5140b001501010720030045031000090301c3e06444c20350a150401c3c0006a881c04020009442910040002021961600400400342003c400d050102840c61000c0320060441102c1800781d40c6240754142c40c0303c03800768023954101c3d00600e120b00d4040b407640d1030351007880b2280d02c3c0b0141c100da40030341c002c07010620400c0100a141e05c12401190340303600d80036102c6 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 237215359 1250 237214109 237214127
    0x711090f04110604180203070509130504151112250915080108030a0c02030102090409080315010201020313061a0a1e06020a080406030e0709050a06050925080411150a 73
    0x15208070420f0005000c50301542000c4070105c42040070040c0c1e80e40712400c06503110700503c3c9401c0d034816255200c001d2100e0f000d4002c1c50080e845411035961841c4181140c030b041ea00c9090031224070f80b07800d01408030344a0310404001e40000d04800746019800c84035071203c0300368680709410404124980c1c010407110800e1618241000d18500e02100654140406142c8a2050340d0240040040c504082000e540d020741c112050610010010014603889140000b0a900104c0d0390b840300500c615007080d9554018000c0720302c00d02e2082d03100301e03194405a0728800188038880550245544e071443c500d40030b84a2003040009007401c05030443c070000344044c0e0145405484c4d0010340c2107401c03100c01d442c0043c001c0820307038041d25078505012901c5880d0b211224a0520203a2115010034200000d009603120503501c043c058440039602c800c0c07103980c0d582e1a141320008000d508515020340c8440c00d2161ba100b2070107280c00c02e1203a40101003d035444800102c11540c0c1d01c401c40900c410004002500c2600b00320b0032 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 237216609 1250 237215359 237215393
    0xc0e1002030c16140d052503020f0405040c09090804030204020703020a0209090c03030d0f0e0a03110d0201140622020d0605041b0c080a0513080706090605070b06060711090f04 77
    0x1103d4490a2060400b01e648502542c40c0c015401c2d0030502d13041040c01e22071041c3c0345601180f9101c0480425801f07400c581100e110590017200b000038114224282406401d106d2134010329489155803600c0070190042440840569840c0700c288004001a540c5000528225000354002d064903c003c0c010002180000342c0800840d502106a120041d10023000b40d422103003016100080015105100c0303030107803120041e002d503540541c0c1e02c40d400701a0085c00c184d0044080390304a03000100d00c02010303822030b0001900240b0402c00305001498510303155029015803c10307000c04408408144290364141d80103d04c54a4809440d803000b0310550505104407403001149460321180b175019408050302944a26501625280c03002401c2c0050724083c10446489010040440181940d103403185500c401040c080c40380020701401002540034031403800d5600f1650420305540c42911040c00f000b105c2d900c01e5900f100c240c0400300324803145658545004e8400c02c400e900c86411480d06240000243d0306000c24 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 237217859 1250 237216609 237216643
    0x3030c0c09010509093307020a061112041401020c060103030c05010b06030435121006020c0a120203010f1d0705190501140c030406121a060d0c0e1002030c 68
    0x304211a000000e0584010040c804910070070306d25412858000031100404140d9000b481c802d000e4540d500140a280460003030300100320b020442c9141c0d1a540c0308001c1851020300000c0e0124000c101d44032020a6860001e100051134134101c5242e2900b0b2040c26403040d070204603544400e10501c0428016802043c80c02c5030118a94501540c1d21450110001003480c01c4404692100f0540c004a1252000702e40a1024254032038000404070b9494090803aa150001c0780940400207000340001208070006000601c0b08030458104601442200d01101c4107984c9076482d842c5400c4080e4040c4148215190300707001401c10040030039038551404102d54003150048800c12882c1c0350444003241024160303402441c01612030340150700401c0150141c1000a0014040090700060345608907a0b6038004903940e070018400c10450280c0306ca10701d4465000315030000c004000783c4458180651000800010608002c84500c0300304002c9010170344503403040005070f440061030003180c1008010700000000c150310 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 237219109 1250 237217859 237217861
    0xd02030403080304030c02210102090109080105040f0f03050f070809010f0804020105160501110a02030301080f06040503030f09010f0f0b0a050a050d030e010c0b07091a0c06010e070c0203030c0c09010509 89
    0x902d0300103c1c07200030406010082040c5100c42107503070b1804480720300c07000c941b0903100e000180c80c42c4500030350241141c0c0d80410702a5800280c40103040c010684503d4003c40d001c0401d10a6850f16150341d01448022020050100042ca80103640d05000d00701c1240241c0b0110385400c201000075007802820650801031000391010000140e07032060444d680145014106080c3c1032084c50441c2c003504841c4d288100e0344101050b410280c0341d0001c0914101c1d0b1100c011a620011041450760300c0341030585001e0101e0b0000c000086894450007000360300b0219090002902c1ba00c0d03903031484100e03200039100d02216038a0f01844c244ea841c280384880050a011505507240c1403034640090326440ca41c22004060004580d4465030780ea00a03400001d1003500144003100c1468031142c02131462400380218074406071401e002c800d43c205204299441c40d2160801002c0307990808190110103003008000314100200f00c0c11210040c0c4007480074094421120f4002c005003214902008214201600064001e0200748 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 237220359 1250 237219109 237219113
    0x3120705030601110624030f070e09010b0d080306010e01110604030306060e1005220b0f070501110703120e16080601080d020c0a1829040b040227030106031703090d02030403 76
    0x4108002d010208040760800000000109048c43c80780154901c00780507100001603040212126144180084030080041003400301c20004086c40100c2d005e001003c003800011102d501401c3d030329408400504080707403082c280204091401c1401c82d41140001d0b12080e08100c110707000b084c20b10700c0c1e9104481e01d105906101d040140b1034050707801101c1c0d001080380600c0394840758903806400908489090640ea500c0c0c010007020b0264003640080300d05620b0682c03100c0f50304106900741c40910303905540e6000600484078611010740454118079000d401454031000d4907400500304440103200800140445600d0408800e04110310031032080199084091501d006940d01c4142d041a41d081640c0c4211106002ca0f849004140f03521120390655240c00c5064042600c01501c01c4910300101c500f400320300301d03040c1408180c1c01350301c0c02070201c400310403500001040304072041c0d41c0402010380002116235494030340403c089005107a41048140c00410f01020781c00c180804000c600290008514062843d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 237221609 1250 237220359 237220381
    0x1911060703061404050c0c030703021c020a0c05120f0316051b06070305181017060f030d031d01090c06090821090609150d0e1b0d0302031207050306011106 68
    0x80f8125610030741d0b6800001c0d401d0181d940c03e50f030500c00403408586d2120b040d440c001c4d5841140c80304048801c9000c8068011540c800101503610541c42010384078014546401d1103481052224035503040c2c0181010354900f144100050000941c1c201c4101d40c0700c088905085040c02c0503170024803d88000440e00035480d40703c5e0411514000d625103400c0d5a541001e18900c8200e00d40341c0040f90303103d07032034000003804641e00824401000c0c0074108a0101074540d20101b00312100301c45132098042d000a0f40c2c0410300390107a4011304a40c083e60030300115240f26400a02c1c210b43c00a54100ca00889100080c4510340c2d000c0080c0e809003800100074000c0803940a034130800b881c00482025400100020841d426440b4030050340c00c4d40718090540340f00c00701c607a165040180c01c0842c000016a24000614000120002e040c00d010000e280c00044c0080440003441203444014506405510003048261007660346da02c10644520306035075919880e07090010004141d24900d0801e5a0f82d58000d800b405421038403 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 237222859 1250 237221609 237221639
    0xe04110405031903020a0b07090603060e090c0603090a020d06140708101a0904020a030b03011803050d0c0c0209010b0405090f040506070c0203010e03180a05010305131106191106070306 81
    0xf1103c801d10780240c0b646812894640041c400034070503642c41c0117000b041ea4000100780103662264030180a0300d91548004038885d40c1c12104a40325074400c0a80c00507500346074004682218070071042d0b03600b1001075004216585110300d01224290740e211041e440004036030f000182c10951500e40b075100350803d5004074800b107682d406124004d61004103c1b06003410721104590740d410000e801992501c00c050005401404a605128040e50802d1140d41d00314000045a001d5143d05803581c50500724440749150082180341c40e0701007401004100d500169890008040c020041105c0e082c0e9941e0a00c8180000341c039004c2d1040a02c40c120206210008001284480d48080d0381c1c58110100c106a0002074003400446403000c003280000940d08002640981d03e4455002d401d03242c103220190b0302c000440c03c8a0081b01c030304040d504060075040003c0d088ca0906110038034018105800c050300c10001c0c1c404564280804008114050340440c1a03d600340807281d403001c80c3c0d01b0100074062400182c5503070b0070301d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 237224109 1250 237222859 237222883
    0x5010305060d03112d0114101701180303051021030819090b0703061a09010e180907083003090a06050114010e040618020f04030f050c130608030706110d05070e0411040503 75
    0xf4419454081c10314095010048bc800c9240307040b5101c001a00f000b0700107000980741d0082c132427400140458010228425488010741e446c00c0c44450340c10300d480482c3c0c03809025010320086031450041c0c500c940c60b00c0c003030900901e024801d505018101408040c1c03c484080d0301c40a4112050891901e810a0020a44441c0403080c01c0540c0e506054000003019000301c0b5040c4c1c032034400d518050100026001602d50250740f0408116004000140a1600004070001c3c00040103094980c030500d000e09004003030364000b005a002c646000a280d610881a9070090700301c0710364080030304030181080d80e0000c6d0032882c2d01d0050300d04120003800c014800c0c19a2080d50501c001141e000552024812407200840e401143c009291022040f81c9290168a510440c80403034400c80070506c3c20810211076104103030449150b0801103207480055a5201d001d4142411000040c020610605482030b07a5400395901c91005566600142104102003000311040e1244140303180340140f00c144144d86000030036096040d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 237225359 1250 237224109 237224129
    0x21f240b18031e0313080c03030301030615080f03030703050a020c0601031b0e0108030d0b0109080a1101030e0f06010f090e100203040206160f03020705010305060d03112d011410 78
    0x4009030210340f0340f034102100604048010021141001d001102500c166440403541002859540c5540380e950859124560f80c140c00402c010070010b00740d07a0181c014405950300604617190344840c2682462030a46a0300c080341c00020400005590500c54641d100c41148401c40c1006a1110081d65507841400000d080c006190410204c0303122088601000340b050604591966840c0d82d001520f91304910004810a8100b201d000015809050f400b8141c0300c0400003082d094006031102801e0f00f5940418a0506a80f04490b00da9000140002d0003860309030401845154549490020400300310792102c4280c610f442c1d440da20400d000304100c2e096101c0202c0c00758981d00c4500010b10213104d500c10003070800e101246000100305a100359140d98600a07000d40d040c5503038072001903060382c0c0100e85003030f400b90100c412240042c2c0904455100100540201c8000d03d5003602c45004c6058940c64200280d103101c0e9250407545424051465a070008c44402e0515080c403100ca15001340f4580a400058 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 237226609 1250 237225359 237225397
    0x204030308250f09050a0303050705010b0405010803030c0703030f0c03050601021501060f0e130c1205091b060d090b01060207031412040b0c0c06040f030209090a02030c04020901021f240b 82
    0x3e5104483c1e1074003a000060003041107a9403880c019240b030780302c640129801d500309900e03200145414400c0a048500d440040c518540c0c5e0042c0116290348144011000e041e41c9464040a4828a01c14001c052016031000a00c6060080000e0719000182e140d1400d90940440107002259000c20342d04410310841c141940900000d20010f044241c1101c0350080d65483c00440002459000d07087d1a0031280c908810070154855004090b00c8030940318250150802c10491104c2c24103201001b0b25900002010000710038045070703240c94400000707030701c60001a8008d210902c2403150000b5100001d07110b513002807029680c4d80020031101e0140b032043c60140750010a6885071200c007404520501c00004048075a555155003072201160103500007a0700520f801c50006034000d00006031444501d0b001801002a1550b00782044081d41c00030241c103045000d840302c1c100e8007800703100707184925400d02c11001c80c40020f08403000e0100c07031a01c0c0c60008850414401040060f10340d01c1190f07182100b0101110127 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 237227859 1250 237226609 237226637
    0x5010c03051e221d0a020706050c030a0e03130605090d060618060b1c020c07050409060c02060603120301030201030906060e1005030c030a0206250b0406020403030825 73
    0x10074081c41c0100031001107504401102c405840000b40710400c0526141403602d16440000404500c09014403030307405103c0c0c2c4c4001c40c2403541481460344909004809460400f150780c031032041e5401500c0349924500048244a41d0480c00d0007942e40302c40e1003030011400c001028030064200c0c419842544c0c140080001c1c40c07940d0b03403150041a500990061410302c4001c1c0c5da0460384001941104c41010010f207048030100c0c03000081070444035007000607501c0d03410200000b9400c100039402100c01031410f01c02d10300700241c0f40d2158006c880a65006d03010009610303494030390190600100600503071080e000f4004c82c41419004030b00342c84c150b80e020300e07000418031018030340747c801003450382c12540c03044040d0002c124400120b01192002e0310b40590990b184502054103151b921180190000d51200303051044a03540303000184100e05502c24252100702e0705040d82c446c4801108145c90a80d041c0e500004c003403080c15080f40d170050f080f0384050341d0b8010040080c2c50321881d078480d9185500800031070290b2481 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 237229109 1250 237227859 237227867
    0x2612090c0303160215030103050c12030c160f0e04020d060905192105041202010c060902060703050c01050609190e070510030606030506040209100f0302040b07060207060f1505010c03 80
    0x3115000541141d9a8080f0400c44200d160307400d000c100c0c803400074018182c0d40252041c0030769048980c1700004010084102c2c041100781d00c10305010300401d00c424031001030f09450030071800a02d40b0200b11034056041c00c1841ca60003003c40b41d00140c5030042400c0500006031150010001e10303980120300014010958030700141031110789100345c614112006524000d11210031220489510031580000c15440e142c0d030b082d5218001c510440c0d4245943ca9454801b650090701c0040d00c0b14418080050584110350000380d440d04202c80640c0003a0001c01c100030200350900ca40c58001c0c0b002c880340000c0f1310b0300580c1202041c00b82150880c0a644691105260003c00c0200c000070b040024a110491008210300034014072603485000b0000381401c0205480313040c14421282e42074030140040c0d0240549900c251101f00d40f03e00c0303050406034208000240c850000c00944010f038490080540d070340c003003030030b10105403560040120b0030380341740000011810f1102c98004048520a003403280400b030407410165 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 237230215 1106 237229109 237229123
    0x2125020105010503061603020708030703090507060801080c0105160c0e0603070603090c1e0b1c05070302160615051302040603061502060c0f0f0a0903261209 69
    0x8410b0001b000d4140d50220307650401528158040e90b80700c503980e00469501c40040d07621404281081400c0c0a040000d280a10b040c1e462541070481c09a11116901d02e02e60500000040c0c81502011507483d500d09150040748040b44190b03140603003035045030102c80f09480b900900c4030102d000d0340a485407404040d04072442e00d203054200746101012000c1c49c40c0342100c01000c04000180710100e030000300040003480307404010302010390491600751203014064809050052024190305100e003040d4088454112102041c1c51501d0103642c2d0151015800c0309410030604004034001c0d82d419001441281c12a681c20001c2c02d580300324058004d503c4010150040e04210b0201d250610303601d026001c0385010102c01c3e480c1c60300006c28081c2d6070b4003002280d00404e0170f10000700140000020311185e03030301038060f0092810214000c62007581c4210071200c2e426102c000040780b20b450003001b0203 = true := by decide +kernel

theorem cover : BRFrame.Cov 237050359 237230215 := by
  have h0 := BRFrame.cov_init 237050359
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237050359 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237050359 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237050359 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237050359 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237050359 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237050359 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237050359 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237050359 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237050359 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237050359 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237050359 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237050359 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237050359 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237050359 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237050359 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237050359 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237050359 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237050359 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237050359 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237050359 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237050359 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237050359 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237050359 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237050359 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237050359 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237050359 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237050359 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237050359 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237050359 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237050359 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237050359 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237050359 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237050359 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237050359 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237050359 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237050359 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237050359 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237050359 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237050359 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237050359 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237050359 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237050359 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237050359 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237050359 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237050359 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237050359 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237050359 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237050359 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237050359 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237050359 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237050359 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237050359 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237050359 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237050359 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237050359 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237050359 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237050359 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237050359 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237050359 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237050359 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237050359 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237050359 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237050359 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237050359 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237050359 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237050359 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237050359 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237050359 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237050359 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237050359 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237050359 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237050359 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237050359 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237050359 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237050359 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237050359 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237050359 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237050359 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237050359 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237050359 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237050359 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237050359 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237050359 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237050359 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237050359 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237050359 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237050359 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237050359 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237050359 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237050359 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237050359 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237050359 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237050359 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237050359 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237050359 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237050359 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237050359 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237050359 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237050359 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237050359 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237050359 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237050359 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237050359 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237050359 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237050359 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237050359 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237050359 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237050359 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237050359 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237050359 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237050359 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237050359 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237050359 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237050359 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237050359 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237050359 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237050359 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237050359 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237050359 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237050359 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237050359 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237050359 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237050359 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237050359 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237050359 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237050359 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237050359 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237050359 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237050359 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237050359 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237050359 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237050359 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237050359 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237050359 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237050359 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237050359 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237050359 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237050359 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237050359 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237050359 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237050359 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237050359 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237050359 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237050359 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 237050359 ≤ n) (h2 : n < 237230215) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
