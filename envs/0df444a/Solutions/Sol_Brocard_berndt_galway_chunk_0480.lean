-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0480
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:01:36.917225+00:00
-- url     : https://prove2.me/submissions/ac30f676-8eb6-4105-8962-5a29596a7a32

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 86151080 ≤ n < 86330936 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 86152330 1250 86151080 86151097
    0x414061f2606010e1c06022521020d1d0a09050106051b06060105040b0711060a0c020324070f110d02030405010206090604020607020906030a1a060315040b16090902 72
    0x1072030031924003000014915130703a0409540c13050002c519185d04600310b0352021680141c2c002030042e5076440c415422484520781c512007112542440c0961010131980d003074400c4104652107490380c1ca252000d081683c903a00c0342410a00064804020014400720f04030010740c5009004e4000390916856494074025503100742c21940100700700061828414241300c503414000c2c0d842801420f450f00b040000204144100c4c41441c03100751000c0f03002c40511091400c0c070b180c04840140150303564000c2d40009028000388074803c2e0301c0b0380101d202d04039a6440d212511311203a502c0c0d45202070310350340e21403050780c480600c107268a0404c86500040045031800b007000c20070212007070f00156211440c00f0002072030110300600c0491550804000e201c010303129030703040c3c43c009641201c1800c103943e075a1001c07a00e010082400649079500400140c00200081e00745d290140381d05506482c40b5894188036605040c5054a0081100c110354000071002c2c1c8440f21680a04641403500c0e81803070390303039169503416038014800 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 86153580 1250 86152330 86152397
    0x9060d0f0b011e0b0f0405040b03150702103c06210215040e1501112506020111071e0b04080a020c09070203070201080a1e05060414061f 60
    0x83c01070320054219070306001403040c0400280340400105a01d69180510f2041038003990303c547d50004603603001d0007200c400e42c0b0001200a000c0c90b002600039540c01802003110501498041c50305481810041c01081d510b826110308a4090801a00c440742c4604080d11050765565452010405c224805a24101d80604105504040244c0d00401c8000301a203506a600e4010410040100301c01d000c9845078005d2121819001c0d41d841d9100580e0014a00410000940155010340c0004c6100405885080c1003184160000301c0c1c440354180d080b02c400d84c08c840c110b10001d1100600040b400d200004202c1106c0100c018140c9180d034a114019000b81d0382203601040210302400d120340e0400890b0094201214210f10908141e83e01035220f120b0420068100f010320000100ea03092a40c11544d02e4101040c0440b80a5884c07042020007082d09680c114070603418003110448020404070024001d21008212600c0381c0204149211201c42c4200540c0a0100c1240428104541c000805203000718088 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 86154830 1250 86153580 86153609
    0x7060b03011103040302070308090a0b0307021e0c01050f07060b040203091005090a020d0807030306080f030d0e0d0503010e0702010b0d03080601030b090f180c0a09060315050609060d0f0b01 83
    0x101400e542100c8000c1603860b02c18000c000200c0d900141c25005c40b0380000c88151344101c2e02010524800054100f05078440c000001d00c8512540007503401004070480c2d1181d03441150383c1d10265202e0700c007440200d000480512252800803a403400500d200d41c0300350000919a43c0020111301070b60422601851503401c100320920b514000c40c043c03598044524030150000001d43ea0010f105100701c80300281c503810010401c1400c05029034016405084d043c0c0403210800507e0342d08a80d694051412940010b0800021920000d400145040c100e030540d00c640342140e0134258010110f81c0010b01a000310740d203842400c04251200075441c401240680d850142c24500600050309684c502c01085003da1880e0080051030b030611350f0802d4000300b54592840c884084411708a28040079410003d511000c0c5500000b05500e85502410882c2e204a488070701c07064520242c041210f408035141c5400030031910026003189040d80c42c1e40c2042e44184403261020302c040c0c440c884116400d07000542c9090401 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 86156080 1250 86154830 86154851
    0x80d020a0c0e100611030c01141b130b0a09031a04060b06030f0c0c0f1906200706090c03060207060b01020f03090f09220c0609090605030307030807140706 68
    0x20580740d405000072500381c40d8a82840a1012040400ba00c103071001c0000c5c0842d0340c45001024030032501c0c40c102404c02403001807081c80c940ea42c810002d60f2240f808004a8030442801880302c01500d2491160520089a192400b0f208e0b6100358440d0086000300460b40304007000040041036440f000c410081c42c0108180342524100d0200d030313210b00d01c59200388000d20411015034041e85985a02207030104035aa2503400c601181c0340382818400400010f0702402e40d0040c0c401162600142440e80100c0d001d1100308030964103111910341c0039905810302c1e0400c001203808940e00b030300000111f610810010325040d60340d40313840e022600682c90072940103880740110001e9690401244603082c0f104c002552402003808000341001040c014182c0c05102031000040892413040c0b41d461012130354090f0602008414507192155212602a40c400b00c1c50841020680d01c0d03c503c81c100a40700040c0c001c0d0300e0081d864405071402c101c0208041d0421040c1d4000029000000000d082c625200305000308425000 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 86157330 1250 86156080 86156093
    0x10b0706060902190c0602040506040603090b0106090b031303020c040f0e01050709050616020402040302040e07080105010e010b04030803061513091d030a080a0b040507090e0702060c09040213080d020a 88
    0x10b50222010380e0061100390700200805002500d00d481c0307401c140e86003503054a01080a4001c0d54000c070740c0079801040c0025490b0b0543c0000b00014401c0300d04840c0d036030301d07041c040c0c0d02030449005411035504144000380001540c4c031224031500d40240100c0740d1103010880000e0681300d1007000d10703042d152515211303410380000b4014107801c142503007081c484040c02c0001007481402010324689100088100c00d00039500c40d42c0c11140550740181007403042e0070703590f100a644d03000c482c440e01c44158038210000a501c43d0100001d81621030b1080c40b2481c2c20b295858800580e04060049580700c134a050b070585128075480d0080518101d040102c40f2030a1804013072004a81e04401d031031120f58405c1040b000120004030032190480400c0c2410100c680315a4888030080c6000d41410350054984014408a80e400403046000c41d05511003c03922070381c1c0c03000101d0716100250b45074a8845003c0c088081d00e851315801500c110008502500c0c0140e6880310445c1c6013100d0844610056000503c048050000 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 86158580 1250 86157330 86157341
    0x30203060708091c050c070906031a060904080a110709050115020f0312091908070605070507020d060c050702030102040e180d02030a081806091005130b130501090803010b0706 77
    0x60900c4192454041040f540b58044031001d0001c0302e11008080d140d0b00d00135400d99140c1102d01d0200d400017074548032418018540350005607445481c07a025050078a4445010910508000c1d210200390f445941c0c0702540b98110704040c605002640d85401030000c01045214000c0000d03501c00b00311035160000300d40c0e804076200e000c201190492410311481040000803548000d014103c0c400d0380da55606452401e101c80361409541c0d410060711907100f4005400301401340d0328010001042561585207059405c0d10aa8400035000b882c1000d01d00f002c900d16030310820003644103041142c900000f95002a089a125421002240c440c0806025003031044812481c0620040700051021959044c0c000e507a03070046c04150002c10072000000751248400e5013401040006980880304e2604140d0303134141d1100d6106485000c080c1c034040014070321700f04450113148070a42081c1c822018dc0c4800d02c1520040c074060340d06a07141c2d03481d540300c2000140380800a6009041600445444070075a1421380309640 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 86159830 1250 86158580 86158591
    0x70b07030c030c11031c0e0604050a11010e31020705060103060b0d0c090f0207020a0803030702010f18020d050f06010f03031202030c0f180406080a0209060414071101060807030c03020306 82
    0x82000c0c03420541300d400000325220700310500143e81c80b109a154000c005080342811000890150805000800c200001c4001c015031107220481112489180112041d00e003507400c156001240126100805440308001007000030110001c0003142c1c8042044426031703004c814121060f601c1a0010418000503100750745006501700c031a844007090903100e0200c400958021607a2250381da580000c20440b1981c102c0d0605c41d405049401800c1d540d07910380d07440350000c40d06c0d2800b550900c42c1d07480c01400f461003602145070000907108141c0d5155000c2c00309101c110743e81160a441112210700d80ea41003000403c2c001c4c00b03211011402d00d4207525000301003044041c00310040d1070051090010381c0458005488a56804605480d11000231400000203c110310006a0700035182402c0420684070220310350038150300a541c3d68800c0d1320343c0c0d030521003120310034003019048894034008940264400c98000194607548c0c0c0c00803403000c2d2130f5440542460b815920845003100e91507010000c505081c0280765206 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 86161080 1250 86159830 86159837
    0x504020403020904080c0f070b03041a0601050d0e0109081603120c0503010302010f021e010209030c030a0f2604060905090703050f040b06061b0109031119020103050c070b07030c030c 80
    0x103072860380414000280500010b0560320003044150408004012407605244c6a408a43c0c01d1a40d400700111a5442603806a074400143c1e60140d005110110790b8600405040c4c2d10140341022610600340113040944541c40655210424400451518406080d550101c41d16880f401182850302500801c000814411001c0c2003d0708510902d4102c0d050b079045070303028289040500c0700e07c1c50817400c00302c17201ca03140302d81d1541403c0c44150b080158050446502c0070340c202c5880c1814442010303600c6090000041000700714450583c0000c2c20100c444060210352803d03002d1071411070b102c03070101c3d4106070040000121201c030200007525241e654a80c1003000d034281004142014050b0100100d4018005007a0901e1480401c5a903243c4408613a90960004640407034600107032000c0f4041e04891106a000031072545c000760034000c0110f0700c3d41d100b020113851310844d030907603500642c080c2c2002440551041008c0c03103544007003081150028031514142e5400a60380c03040307c0d03006d01190074861224041 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 86162330 1250 86161080 86161087
    0x901081501031101120504050705030c030a08180316060e040605040504020904030c0302122206050f1b0c04050103030e0a14300f060403120c05030c07170f040f050402 73
    0x200e00c99114240c1541d8010000c00030f0b40002c00b0040c0d503850703007040031182c07001c0c500801c220502c00c1c0800d4803000d5031000c03410b079040501603c0070550ba5000d001805401d003581000911681280d0b400805d0750700c20041e0954400d480240100c1c9034903402c3d0380c0800d011408101e40c1e04242e140c0741c03252801801c1c040380c00f00507a04203a00818903680d002000203042c0600e5049045c1410f0080080c941d4942d10880115a1401103403001d4500300302030181c4041c031101306080810b5440c00b4100f980c004001070f4058500f000728041017003820701d90052000d5071314080c04005640a45840c040d031030107980281c6842c0e40300c81c0c52206003d070340445a408401131201c0303801001c0c0e040d680e42490104014180a103409501a41114071000d0756040002c03848510518024481c0407030042a1284914043e45605001160b00d1a180d000c0d142c009240c540020340c1000003d80aa4116000e40340305805408060794051020008c0c29695014840556441d200880d0821040e000c46007243e01030602610700758207 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 86163580 1250 86162330 86162353
    0x7080403080115051603020a0c0b09041404081204030504090f0204060e01020f0d140f0304060b1e0a0308280509120a05060105062203060b0906090402030d03051b0f09090108 76
    0x1405201409400c0700b00c2c05e21114145403082200d030300015040708100800c03603610010715182c0c0c2d20900929001d641071070342004c0c16801d1058580c0c03007140c1110b50b5614044c1c00c20045414024018412414000b040c880820401158401d611249120b030f00300503039480c00d246000d0407900d03503586051b04650112812608001001c60356005100d1242000405071150b82c0b03a40c0d10500400d80c00903d0610f01000300401e01560390061740203e001501d034840c5040420f21440507048dc1d4a050310340249401c0702c10400119075400a14440141403441d0080076451000203040e011400608000508085460110b42c5403c0384076452540c0580000d08100700643c6e0f41c07540300e010502c1003e1140c04003041c2c0c00341c1500d001c2c02c1503981d1200d102100900c5030700c0380741100c020081410041c0c011414000022103e0808a00090190b03400800030b0645841d0f1000c210090080280b1900710a040c059100324021544005885c4003803207023140507250710750391042c8a020708050b0b0000547d0b912007100303c01c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 86164830 1250 86163580 86163587
    0x105010306060e250201020912070302040506090108061b0f070b0114010f090b0c030403020603010e1b0408250504090b0f07051606090305070c06030902041d0d0503060a0b0307080403080115 83
    0x81c4084a584c000041c14141c8503010ba00a028081a090b00211040b070b10f001541340201d1118250b0784205d80401568072280284030412009009078200c550006010a82c0c008003c1d540a0142c51485507851034a28600b8080b0440d03000040100c80c0c20034900c006210500701045030443d0400c0c00c0c0b81915000259030402424040c0c00d12480c2d08603c3c0006003518010000e104032000f43d0b401030086d640c0c950707460588084241048601c02c4020000300030f41001050304038105d40072104090024404a851024064030480f07080b9a6030307100c0f68403200b0009403900c50380103031141c80e03018026043c00d500d0026044035a40900400351420040c0c05c011020402d0424104180c0301c40c2c1011002910031880c0c64161841e105000300581140c0c154a400203c0d56415000440c450f8425078062002c01112004946107042500040165400c08121802a5446003000e0f55120f2002040da0200035590004400d0390350050703d048000400b820200018941c120b0301c2c450040c04600c4850603400303858800103 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 86166080 1250 86164830 86164861
    0xa210e010c081207021506040903090603020a030e16030b090d09031b0f09020c010f0504050705120307020a0303020309010f0e09070f030b0a0b0a032d02090d050d020105010306060e 79
    0x6505210070a540c0d0014090140c05649050038000030564040c204140041d44d156104543d02881001c0741c400100703030b410306000e01400f095140c1c0741c800703041d41007003000d40181d0480c0d11038400709036a401001c2400282041010b00e0300b203220040004090842c100401d60310300080a507151944a4941c20fa6855031000c00c1104072a00284049054030040e021703c0c00c400580c3d4003001f45280742c00d40c00315000c22280d00500c1c0190102008111001c000c180c64819500700312405019070304540c0f01001541808046900c0e41118601038038a0701c0100d0340000c0e07040b44180c006900592000c1070424080d604100a024407a0550900003500483d210000d501340c10010311500402010544030028035009400c1401105d80082c6a49409910788a00c540c41d500508234041c00642040c0c140600501100d02c001c0c1440000d11f130070480c2c0351035860703050069032085110780e0300100d0413140c0c800415818850080f060b0074a0707002245551441c2095800e4502c00e4110a81203190802842070100100201 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 86167330 1250 86166080 86166107
    0x60506040b0a02030705030703020616021b01080601090504141005060310091104090c0c02210703120e09071d06250c051005071505040f0807020d0f050a21 68
    0x1070340e941d840090103d0035801080c100500c10300c00858004109a004603229110380b80c0001d00000201100d50100e03516000030104040d60789550310b00c00c5055210701d103020362244046c10300e07222041d920070209044511850035421003d100409012205201c241514000c0400701c40c0c050860401c3c401d03aa1413a040e81c031412403425582c2c02c003c002140c514040d0f80003090b20b04000c0055415580d005040e035106451b0403841454504605116462075540004c1007920b00401070181900310303900c681a00c0042800e503c24006031102c960303855034800c1c02d114459061030b40c0d12915150a01c070f04e82040b40c0100b0304d03144604404d1080244002c00e8405a0190052a140d078280da403100b8105075040b55150380065800c440b400f1445403901d900300e4010300c3d03070034401d014011f48544081d007010215081074130020404042c030800ea00201d802400503119427400104860f01c0d1601d10750312003030b04409540040300d01c1e40201c034143c1c2c1407001520000c0c4080d820100e02603d000011b8100501003200d10a2 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 86168580 1250 86167330 86167349
    0x9060b040e07090b03181e070605031305010227090402010e01050306040b03010615110f0303010b0c0304050a09060306150b090d030e060309070f06090302210a05070b1c06050604 78
    0x3a51091184038480001c0840c11316440d038906002d5141e100c0814004120080e80c82802c0805028101e921040604055014050071072075090540444440d80080c040414a000c00c481e8000481c0742840200300c10b904419540c24001034944c0c144c1110854aa0791a200740302c05010000540d8000a92040f4170300246401ca03a80da6500000a00500c0c00d0ba126503015860301ca4041000520102d1204210748640c507001116425070381e001c0c1e40c0e140c80d8890707054036420030b100410020f01d052000e096000541010f5900340b80c1c4807000300f5182e900c198003040120b42c84a03010410321080e4855000030700548900408800d041c1420b084c014441c1c030070b9550081d20500702c560185846010112104000145580d80e00d00b0404112030f95541e103401140c622050160340003424601441e14001144c0d40a4516500855806140d841c030301601c8600700340d0740c0500c0c2c45000c00a0400d04c001000703081d80b00c0c00248c0325860880c01460188098501c00b0000d807030031030144032940e03483c0141c034101c0d0003403107 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 86169830 1250 86168580 86168609
    0x106080a091b06022503110909100c0905090717010311012c190608060616050303041401050109110409020a020307020a180513031e230c010609060b04 66
    0x50720703440c00c00b8801c004442c8003544240214010382d0200d400d1003013185111322101012580000f0074144180d070311000301b00b08410008049507007441002d00750700c0107910040c2c85000d80b01041440a413928018000300046103101c0034405440c103903c215410812901d030121420351102d6181e6030541c0107010250050321000071114442c0e00c25181c450003044580034205690218000003003840b03018604183c4241c01e502ca5034050040c40f810100702b100d01607a152140d64a9800a005075980501c05191030258050485808103600300010750041d8898664403d07801004403025003107a60680042e050142030080309070900001c1c4080d1801e0b24049400103a5480b515078080e03240d4406c41c0002504106882e20005103038072492a030116501d01d0200500050b59440544144080c00020040c0440c107180c3d0413180da10b18030521911072607002d0400c1d240c280d0711214529900c80107031555040b444c50005022210346801c0c080c0d40d0041501700814000c680c10030f880410b0070b004034007a4002d00304091 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 86171080 1250 86169830 86169833
    0x606011101020d18050d031b030e03040f2309060a03020103150f17100b060d050403031d010c0207080f06011712040b030108241501050d2a05030106080a09 68
    0xa504540d080c190a5808004c2d0200107140100042407a1200742c4041c028801c0c15a0014000d01548a5600c09076400010b055a0388600381d0091000a0046519110520020480c2d103a420801005458841800c540c19543c07090158036840c240704100d8040c102c200c0504c00e40307440b0841030700141c0381e0909000c5104030781c200e40f40011008a40c001000c0d1400c0c3c030030000c0e0b0301d02e428001c2c181451501c401e0b14000d107900c02c003040a031349481e01e1180e0015000c11010b0000100756200329082403007441c000ca601e407105040507450742001c5483c8462a55901841741c81950104102d000812150000d4030b680b42d6110415a26207030144a08078001c0c880c0d04043d03d60032000e01c80781684260309082c850301c2e55115a04c0d004141c10034000e90350184190217400f9841041f01c14201c000129110100700155108071801003154040c10045040c03243c180030649074450700e80550814000410700b40c82d0002c4100c070f01c03102d03408811000042805800c2006000c000d511000701a8890340381200400d85448a = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 86172330 1250 86171080 86171083
    0x130b01020705061b0a030e3a06090b0408040f05150d0207050a05060702060a0c050c0a081c020f030f130309090b010504090509070e0c0c0a0f03090830070506060111 72
    0x500f0600210b402507140f40d00806d508030041030305400040c1d8101018008809035140d01d401140f030950f07062840e04040c8100b6000b80080c00c007101c0d01c20070740400c40042d269604014244140e8003103540d400081401d2003a24002c801650080004490f2204d14007007000c0035a5251042c0d80b000c00b4a2600010300c00d0901c48100040b6150661001c00c42e1960319104134000d4542c10243c07280750344507003041001c1c10381c288220305460081007480d029224402e180e40d6a40400e5201180d8184000311202c42c2c00070401c03451003d800d24074004200c203641d030b1900c018002ca00c0040206400d0805c0d8141c0c40d50b20200c1d60010038401564004076000400540090042e1102d010303582c841c002c4207080000f00f0003410004540c0108032440020440382c00d846041d4050f00901404050065035032003940d00710040780d0701c081144a41802400c240c07280540700d03400a820401c1d200303448007541300340d0746140005109007002005189000d085440c203200480c0c6d1910388504020f4103040c1000380c02c0c0140d900c1c6580 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 86173580 1250 86172330 86172367
    0x1c02060301090e0c0a03050a0204050601090308032403100204031a13080304170a050d0c020304051302030a0e0115061d0f04050601140a0207080c1203040b03090106090207060506130b0102070506 85
    0x10050800c0c003910b44d81d2502230758422001200324022420440420125400342400d070040d60745c0030401900f580d4840c81d00305501038001c126a1025850540501860f841c1400007030781041d000324000da911411810100303078150f51920540700c8064100d0402c40c0b4040d085050300801070f80721954a5503500e640c101204121706d992b0448e040001d00081c240ca0064000300100039140300114103021078000844240d889001d140b2555404c5580d111034010303003c0a0b03a00459008c0513041300040c0e42d090900d1890300b103420107a50b44100407401101070103800e03003000750b101d4184034019207943c006c00c151003c1455000000401400f664641d07000c0754450307001d224014004160890b205450b013444504c0259151558400c1d00c1040c0560003100d806410714810192906026100075881d1038907203050106282e00081c914032171956100d40c04160406140001c040040c003c00300403405061100c06c000b0000340860302a44003d20701001c41140e81d80114401044800490f042901e50781c2c44805c407000c012 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 86174830 1250 86173580 86173603
    0x5100528090f050105040f0615030b011b1211010509070905070314040605071211250f2d1119090905010504140303130f060f0c030501051c02060301090e 67
    0xa09080c500c40b604941540418100ea404440500242e0b107940c254104990441c058903a1642100b852007410a0094200c800402c00c18034048448050000b11080304600410b070031988024050015540796501c4400b0302e407055068402004141801e09440d559140b26200e505a6241c543c00020405030203076010b41108031034500500c0c45403803e0300e8180c009100844481020030300d0042d00c880c100c0c025201d0340b801c0d042c15080c00d0349004040022408042c3c200c0114800c4048920200030009180c480c107240041c0c03041c1c44504101446017441180c070b083c407548020008081e071011001140c1c8200d803114220005560802c1500a11000494510250b8009440307060400c428002040815032090380306a00910b09245000c83c1d030404903482c1e04c01582c500d090045030003880c0d001310b1130352034500011038411500054900402b0310540151107001109401007507882004001604010000702c2d00904020350005290b0101d03400503440b404103028100c81c140d582c00780c41d090b0080c208660260762 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 86176080 1250 86174830 86174849
    0x406080c04121b12020f060d06030210020307050c1804060c09050d0f050c150409051f0e0f01060206071b020d0501060b0a09080102040e0705070c09050112050105100528 74
    0x4803403d003406014120301d00340380c11a14242d040c0c00102a90a84200305400350700420903002041d0302003c00030703190042400c440d4180c1d500c1500100503940ea13140c0c10030754400f64001e1a2114040d09001c8d00b42180c19000f40d0041d01002a032100265800301044e0340a5400140040c2070400c040c0c04541c0d20b401900055000010101c004007800044800000380620813404c88042c001c020050211041d00c1c0c904565510300244028400c419842c0c00681c0e01c23a5038a00f100d0010145c8490071241440d1540c010b03c07000c110075060060701e0000010781c1e4003500c041e000038000d5082011000342202d0504c4124010086004003080071950b40c12000c01d500c44d0040000d001c0e041d1501ca681c0842c0d0f02a04a030000f144c0b904000140048040c004da4044641e0ba4039945255900d600b81a0740d00c4c0c1c03021404446541441d440860481c2d201c2c41341c24044e00500384001c0e800c0d00f080c5006400c4900c0501048176640c2c40403c00c104a95480041ca070681840c1e500c1003c00802000d80c280d0118503e070010b4010 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 86177330 1250 86176080 86176109
    0x4060f091514060402040308070305031f030b0402010f0206090d0e0109030b01090c0807030b030d0c0f0f030905010f0518120304030b09010231090b0a080a0b04050d11030406080c04 79
    0x801185400000c0078681c21071006446490303c0c42004202e00c1244001400c140c0e040c0044408203024a010310b84c00300048007015000061118082001c80307003034004440d9201400244800e6580c0569041d2206115000078009414407462880d510030103039508108204251064582c6a44203284130001194006507420680d6100c07048030317000c0c0c07410001e9880010a030400240c4070318401e001c1d22005e008082e02910060800e054103d0348001294000d860000c007501c030040000d440031100540b8103009030f54070039829090000050180d056800c0810811074181315200c0845100c2c040300318102c40c1280c1c6070f07115000406110303045026940c0b000d40103405e9072041088250040d0000c0960a1302d65051568112942405000f01400144500d403035140410040c04401d500f640030180c0240018040380460355900310a9103480d0920004031403411400003404204501046911079411060824406c451400543c0642d01d004500c203080800004901040a07105488221006454500352a441c0e = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 86178580 1250 86177330 86177363
    0x30a020703030509161505160c030b011403100209030a0b090c01020d14030a05070509030708010b090f040209040f020d020d0f050d0203040602070611070504230c04060804060f09 78
    0x2500464010703004641400002206590082031240c01050a6a1501860341c02c000034168a00c83c11503100c41800320401c000302540b0310009500001c90f03c0741c902000801d013146010100d42e00103030307c15080c04101e0202c42440e80d402080010072504052001a110317080440001e142c005600d4000c0c00c111035510601c0384418000c42c0d69140c2e942c084e02107070065448054100c4540342600941410300c14140007080042d10140c00040c0c200a4074a8500e007489402800a8280400c0380d0000c50380da03644140000d903509090400d00d41c00301c02e2140401c010701d020380114008482c010402090b0b203031340d6080c0c0b1013151b80708600d8048071034000d0808950f010440c0b0785411414000401656144038200440020346d10001c12036041d1358095020f805410700d0304030300396540240311030000d034180039444000c40c0c10b0f04c07a8460140021848070380d100084a0221075845110400780c828240c40804000c288450368010b40d415400507403001d0005500303040000d04000030082c0c0a03000782803030b541030100790 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 86179830 1250 86178580 86178601
    0x9090a08070f20090414120a050a03050a060e070513080d0c020306060904020a05061315091a0702010215040602121f060801150c0309090504051e010203071d010504050603 75
    0x44009100b5150a890101d02480000d4101e6420290307992004c4280e002a0014030b03403010b100c000341d0020045800d101c20700e888509858001c02844000980c0c04141043c2c1241d050140f01e03003040c103100701080300605003604080d01600c002c0081d01409400988055101c1c0300300c1420b0000c11400301500c14500040134000e015034200c0000b60f10034407444000c00c84a1034041282800b440e8001e01040d005480e00e0280207040d0096050010505400c0c600056540404521614024269610240c0090811000320f030f16040c405072012012005100000050742c00045084e420b6092600e0351166549901e0124080d110340c1642024041220302442041c41a080c1c1c82c2510070100702c0e08401d000e484080031542c541c8244100040486020303002106c0e41e0045112001c003d0191410a0000c7e0b10368541800755001a13801b2500c5a11413040010740c00b007c020710402c4030541d01d000350300d14140301d403000b005407112240c890308096101c103416109a000c1d008413002031002038011922440c10309401c0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 86181080 1250 86179830 86179853
    0x1b070b03100e06090f0a09020301020d0603031107030b15060f0a03050f1f0e060d050f060603160b0d0f06120317100605030c0a03140412270509090a0807 67
    0x30051041c01c81020501a15249102c1e10a0310042c01c01c280c40e5489011204000307601900032014944d59800c0100562400c0c0014021490100c4001c11240e165250040a406e50210314151542100d542071000034116101c1e175400000002180c1c031100c00c102c1c0010b419100b402c05a80d090100040c480400e1a01034121381e128091615043e0707060781d207141480d031440b288801c603510a03112524090202c809400c43c45504540003420b15074149409070303103941c0b41c5a000038152110f030744120100062032074108600c51411801c4210f422007a440d040b030f80c001502a10034004c00040d1a005083d05800ea07683c003101c02460150b0b054000c070440c604005d802d48281c02c21003104030801e0400070f80c0c01c40d2000180b03001c5500698910f4650f50314802e0124140c3c0080e84540101a00c0f25500310b0884245030301540114003900003140c01f0171102001401c00786190000d81e9074503600c00d21601030a54211021000c50b030065074108d90300d41c0c1e00034802c1d00701001450028280340380410004280301c1c414401 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 86182330 1250 86181080 86181091
    0x1a0103120306060504050d03030207140304120b06010e0f010c0521070204141b130b030403030e1618021308061e0109090b0109090201020307050a031805060c0307081b070b03 76
    0x4201c4640c44030f03c00c5442d07100314016160022422011000020311a41c020140039015044411247c05c2d1406610b0a641c46030f07202064106810039020305110345050300e25007201c1e007400c050308030601c14008140da002640c04910306004486402d132040c40320030310900100300400d880070380b4034001403c95000141c03c8280103900462038032190305207420f001c1103040d00600490594204100e2050300d60b0711181d00003002c041d00500310b040300250410442003d14051031085d01c01084018402e0045454038699800b001c007402c0040c0d000700100315180080341340d240e2120f040580c3e04d18103010403840400055100c404584202400c012251744540701d040c80c0000c20a841c108a070741da038415201910000781300500403018000041000684079400030f084284180107a0341007090700d4a41605205a81e00260040307800f00314011140c1e083c40002c0c0d000342c01c04031422401c0030750500706241d481c090303118000c00e05d6200013148025604188040c13403042c15400d049800864640c0302a142035041681c4 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 86183580 1250 86182330 86182337
    0x609050714040509070b0309120408030d0b040203060108040b070201090f050f010c111207020a0506070609060606050c030d0b01140c01091b05060a1404050a1d01080a03080708041a010312 82
    0x711509860b01d8003e0501411502005000b09800e20a0b405002c0d80098910100341c450461409580e100e900c0c05440200003000c05583c0344c508038108141512001e07074a4a100d107104101b040f100da81c00c40c200e16049500070344210003039a21000305a0050100c2400030305001000c40710001044400140c130403d04510200a00001c404141c0c00d41f40c451504841010302c0d080316030010014600200a405201d00013082030f0b0a107691400400c1543d4032001c0d0a45a054440ca040403d01c0164041c410043c0024904240382a03030004041340c40b8004d002a51002e0794a400c4a1050390f807140c0f0031401051940304a666407101d20810040c002d01c9084401c41d180b103030700030000c0e0541004084400440306c0180c022403401944d10001c54852000c01520051100d00780300108440e00c815510402501c184000c84801504480d0100b59502d01640130601c40d521440200000039400f82195821030b426080200741d40d282c514155043d0768914410845684410b800002480758806401c403d40c0c0c1c0310744 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 86184830 1250 86183580 86183609
    0x6080d02010b01140f120106020105041a10030206071103030406080f0a0507050901081008010606021b0312040e0727060f0e03070b0c07090906020406200703140a06090507 75
    0x15000da0a0756201c2c03503010b02103801c01481c5841042e421004011101c0320301403441c580048050000c040b01c0080e004480180c0d51a0104030400148a82000081825542e075814a01d010010700d85000581d010090045030003103507850400030003070881122580d000701620b44840c0c079031000801e0000222541e1703014514020110f540f070100391280710700580c95580c8240c5020b50384801502c1031400036205211903100b2600001e0984030078480c40703000c0c05090340a0f0040703004603030b000c4e118542c80703c0025100c1e401c0f543c0e1110900c0000801c47d01100c5000d4018141a03840300d005540c0018426030607903086800200441841601600250542c0c0036912907a61a503074000b4103c0c1d203800703282000c039010b0340b0109041c4126042040504881c00007202107401668440c006c0d10242c441409013280d000e5004202440310640000c0510446142d03a0140c44072254110300080e07460040740301c05010f40140400404401006105200d416500306805100050b05450b2840c1d40381114420303407100100d000d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 86186080 1250 86184830 86184853
    0x50108060f0109061805090c03070305030a030c030b090103020d0c030812040b010602190204050a1d070305010509030309030909060f190302010908030a0909052701050106020105060111030a0c03050c030d0608 91
    0x2c0c85004285c8001015680342c90710300359900c00c028940038010030441c0c4100350b0700e000242d40400030100a140300314061926484806005820380c0c0c031400181080c5410825072072203d4840300441d504594048640c070003445400d0500d44010041900090030015000a80b00840b894200e034840c01b4070701c2041c88107841c0e81d845030f040b611110402180103d4020f6802d488015241c140c000744c1c3c004066000016048190f120142c04058940117160750380d400c440700420038040288510360b400030801c0080c51031450580d910585070b20401040c540300d2090240480d50980781c020008500700800307402846a6099160f1544100c3e1481c8022800282c6006c00400e941d440407040c0c40a0010075101e1404450808034020045c000041c01068029031040c41e000d00e074056000c140a408200702c00014155051034002425140c0040429050083c09855491902000400c89940e5042460801d41c400064901115148a4910629503a20003c2504402030b0982c0d40243c0450304411b0844260090781d = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 86187330 1250 86186080 86186099
    0xd0b06041104171221190905150105010f0206190b0418050c060f1e07050607080106110a02060a0e0a05030102270d0c05060715020301030c03230309010c060f050108060f01 75
    0xe5802c9400c41d05c5400000640100076210a1908040d11800c2605102c0307005403604200c86c00f6030400d0703886502c450740100c8031003040407515002d0082840d01041d0102d2034140a944e0b404003801e0390b05190f41540304400b08202d20703406203104a0004109010704090310540940c2140404410740c4d00307002d801d010010b10714085e0229036403102c002c855503080000d03c000c240c0d00002c0c0100300c00810b580401460000a40074412140308503401d49401d04954140f01000380200b0304103801a0043d404100032402580e21181501c1c20006145491300e6102904808140c16440c1940501d4240d80003040303902440c2117030807003d103080e184401c01c0742d071040c0f42004000c1d201a20f14000f91203038540c41c80c14000c1c0d081000c005d105903401524a2012400501400e208980c0242d10580300362050f11024400c000814441c51091050201e400a03050300c0b501d117440d1680f103404401c0741444124a0400c0170411503420400d5220040305040016682d2048070b55140d41003100d0520013004a840007080c000d61 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 86188580 1250 86187330 86187337
    0x1080f090c1003141e010b040308070809190602011a030a020a0b03130b01080604111f0806010e0607060608010b010906020303040b04030e090a060503010c030b0d0b060411041712 78
    0xc840e0000c000c0816030509102550070903070304500805403212000080803442040c0c0a018591042c210304c001900c5500b50b0012107410b801c104034881040100b0004103140b0800c2d250015086206903a441d0145000107000a2489ca01b03071284000c18040061140e4044d40705e071541e060032100c3c0c00c40c0040c4d184201912840b84c500300a5001e282d0000500c1082c10f0031000d198800c00c95106031400b0880ba440351030911209900c884007030380c01034040004011f00341d40580c2c441d400c16511803201b117031130400e01c0501c1011081c011003000403400010740260b01c00c007503200a41401400365a40c5003818189a13014000e580600401d945c2400841095075210704802380856a042d8051811915260b440e10071034030b0058000c0c1c3c00c00004241c0101c0f196500090140201442140003e19a142805041c20f641c1a10481c209243ca001103181c8903440d086506109990b01600d031840c180da510780001c0003020702c043c1010a180020502182c3c01007085e0000d40780010600888400640b030b402071010511 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 86189830 1250 86188580 86188591
    0x105090d030605090f040303140c040503100c0804020f0406091e060803040302030d0e030a14030d050606030603030a08090102190c0c0b04140f0a05091003110906010818010204032001080f 82
    0x41c4c643c4009140038064a40898100e44a85400705d01c51006040c00440780c11b050b2804188400b0009080001e071504102444181c400c0c148240083c803a01040508040030050019025854012190800d9540e5600c003201030406400d04004041d00c1c0c0e0950540d0b03014100e91400f0691402002140c00d1000109407000c40b940100204403030b4130140e00032626800d02240c1203405109104001d000256207900001104081174000c0d62071740f05c1d091150003920f10150402d03003d90410420b015443e00c5c04000c540552030070b070810504070384030032810078020b2003002251403a1066500c101024558030504240c40c0a0003071840d41400e689070b10599440744514030a040c00041c000e00d1145950400310b80c2e408801310300401d0504c810b5512808920b40c410100c0c8c0d2882c104001e10070602c100030604192004180043da80c103070030391400800182c4026009026200b0301346a00400600c2500f0940403100516885180c040c640c03040180740f01d5082401d00403850200c0c01007400a10082551581244944c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 86191080 1250 86189830 86189839
    0x10031e060f020915160213150b0d0b040b0a0605090d08040e010f21060c020f0f0303190e06060411040305030f0418020901090605031812030709171b04060e0403020105090d030605 78
    0x61411b5820410729030300100c0031020b010344a1203d00d00700d07100040410020314414142030707074480c144d94a100c00c490035500114400c91504c0d0b800359694a9280b40c0c1c20680e14071307040266070f0320b0003240022165468000e00900041c0c001501140e44c101c15058681240d04a0700c0b2801e11035150145030464a000d8a969410b00b0342d140d0701035001c0380302c035000845400420b0040d16031a003000d056650400c4c030b030290303174141d1640000b040c070142e00d617140c01801c60b1009814003000308079960f0800c542c64500240400d8440d81d01d60b546034810004030340c1142c008507405812280e035400c0d1103043c20403a8200307104003040e107003190803080742c1c2c03480b58021a803200a05a43d407c14041c10b2117020784031034101518400982c01c41ca5a109042d6004001a44600000d001c1303a646a00d00407900400380c0c4441c0e00000e403120503c0307400c1c802c3d030a400964a5403052051020014400c28000441c0040185901503404105510306201c245a0103620250184049009a07038150403e0902941683d4247c441c49800 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 86192330 1250 86191080 86191117
    0x203120f12060105190c120c02060706021e070303050a1d0a0f0303020f04080a0212030c0601150201330e010f030201140d09030809010509010510031e060f020915 71
    0x121004140074a40c001e205041041c01e080c03680700050034104d58402120045a043c80d80710b82400b40312002003d010740d19290840305403841da07000c0390340350184102c020308040d004240c2110152020002070a407a041100c1c03d42c6807003290074018043c01c42a111000d4aa01d00400001401403002c5400e60b916154001006903a039566250072198003048010f50825909011561610001000070001040030000801d80c65441e8010414020521000c071a03065104005030341da2004003241542c1100c45030501c80e0702002c0c10510681c003500100007601803001c200c584a2401c006104c03069035098034620080e20b145034a60390700f540c0d800d03420b0107070f5202d41101c2c210400c011b40c4980d0700c5c0311280f80345245960809030342e070781005d081e03405a0404402145404c020003005030000d11569030f014488030000d200a04105000805150481c00003801e0420030b0b4500e5035007c0d141c00031442c40b413030344031008000240c5480c600030000d4012080c9a80b0071644251101a0000340e001500c903c41c80e41680c407000c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 86193580 1250 86192330 86192347
    0x41703070519050711090618090a0515070206070c080d092d030e040c0905031606080a02131404090b09010614010305090c010c0c1d070306051905060a09050310090203120f 75
    0x30b103e0002841d0541c000816404030011110388023900f0f000e00a50001800c0e1841c00c0e14180c0e04040444404816004c042c800300f00d826a8002941600402c240c10302c20741d401c1c2d850500004600c10440031450581c02c140a45c0104001e4000c0d9244207101c0102c8140f0522800150090682c0e10716000703000200b03070728102200c0d80b138261b214003126025030910f11681d40d600c201107420030701c3c1d03101c1c240003000d20341504000d25034002c510700350b00020107642140b5045818000a010070070303d0007452442d561072a0301c00c2103602c4a034004940705030004010042450060612030203040180607800f8588840307071116441c0d5019000340f0303014580b0303200134080b0034400d5801180e00d040190360aa40100792400c00151b020021250401141c0d1041e0020030b261820071406011f035151071340464010190300307083d11001d905a50000e419240200caa0960745e400c01181185d0040c03580d00010b41c54020440000100b03080762b4041000103100340c05a03550000602444061406603140403a68080104543c80 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 86194830 1250 86193580 86193589
    0xd0c030305340b0f01030f17120a15230906060f07030207061d010c02010e0103060f0803030a110c0601060c2906030f190b041703070519050711 63
    0x705000c080c2c0021480404071001c2500c0c4000300d407042d014030218402c26806000d421400c242d407140c06000c1008403940b46a440c1d002d00032040070082c2107002c400216502c101c1109045030042d03556008550001e080c05c00c4540000c00360202d12403100503505100083e00080d48007007140710750f5841e0344820703009515001d0118040c0000e0100b64405410000003841c241c1100103020a1402030780200041c0e400e010001d031803030f00168540103480c2d08082c64001180e81c0902051602a42842d000c25901c1d5018016000b60016800a020b1003c1c0500c000c541d02d070300040514418001e25000788542c03641d01345081d0a83c4a81c1a0f40c0006070414401445140d009a03444241c540c482d1813407503c1c4c0c07003081c0c201804562108074409441e10310041071084070300d810440302c400159041d001c1d0006518140c0c103c0c5007040401c20041c40101d0002c0060f040c810340c2c1e003404c0d02440065444660786e01c2e08282c01041540031030100310314000340c1d400382c07200244a41d00b9a22107070391011100c1c507007803403241c02c21 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 86196080 1250 86194830 86194837
    0x1207091a0d05030a0e010203090a090209121c030f05060f01050a1202030f010305011d030a030f0e010903050702030f07080a02210106090e0f06040b01090b0303070611030103020f0d0c030305 83
    0x440c6841980c2140c91680d11881010030314a40100c01642d02e841d40c0241c01022100c843c0c2d0361504552081c855840c10b41c0d9007220f50011a0a26400141d94a4041020500c2c0403003810000281e8011403855599075980101c1c00c4038802059681000189103c14101c2e040b9002919030640080c2d901d035040a03c0e5002d907005094000840c20254984202c50100c40d00b03076072044034005104d4030303032100401c10000d007405680f014400d00307203440c0305403956485503d40c2c03401000c4c1c2c3c540415413a100440d40c00d4945070b1107103654000d40b0000b030080603124103014203198031111041340a4070840d01103040d1407002041d0310041c0c0e10710307001030404507200f50204031048680d01081140c0c5040c0303000410000c50f00348102030090008820100b80e84808850080c10a0f203a4071041019411801c20440003601c2d4030303d0181981d07640c80c0006100e88108012038614000d03d5401003c40303143c0020f820728540c802014504803842101c1c004d60340a10141402108000c400c1c0040c01d505200b0014000a401840076 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 86197330 1250 86196080 86196101
    0x8040f022407030c030e030d14030c07050703060209120f030d020319050702070510020712120e09010e010e0c0a0507030e04240906080304230a09050f0f06120709 71
    0x251111040362019081490344903082c100c010444610483c0304268100d4103248440c603003180901078032908014090000310085d103a22000da6000000141042c40f4030040c1c80300e2642020840c0d5032183c680c80c2c400020f5000743e020034400e8950340e5880d846121300040583d1080c1079000070314200030041c4075074800f9401c05402e0400704c1108240200c00741e00e60740709141c881c8505600405410f80340000b4006400c0c0300e401420110b41001409000881d142c020607040c1a0344420340f0b405400525008035400ca400140c80d55000360002c00000b805628600745505860740d040a101003502d40a0440013507104910203607021070000e020110105e400394007507410710b0b40060408580e905a40e02c084843e07822580100d0002015010140321106540c42a10040d1600000440c6131a003044100408c905000c600c1300740401c0055041e148907150b03000080003d1403001402e00003800c0c90346140e01c8005044812400d10b07042c0320300058240ca00240e40108024030000500031480c1044813010160402e54031 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 86198580 1250 86197330 86197369
    0x9030303090201091d060f01030c020d14120c0301030302010f02160303090c0b040b0c070807031110110a0f1115030109021303020612100605040302031005060f03010f021908040f02 79
    0x11300150041c00040c14010300c50035050146441e2418000700042220505181410107141805080348140c0000350800f000156060560819003408003001c0740d4801c00b880502180300c41d4007806031916400e000345050721b10a40090000c0020340178103174104e0107080f1400442c10350301c001031000302e4002d0b03220910090181c03003108100e80d12502d240709190f020b0360010403d580002080c9407090018401140a80b076804090b0240710301d1601d50f4000c4850034140203101d2030358501c170070a200c0e02820311901c3c06904078090701e1041900d4103150f9121100300c41d00303481d0801c003131120580da0318140200046008680d003002d82140d00304412103000350480694a2100c1c019002c021015035182c1c400350040d0044070148021700d103070848180701001e4503644540148002484184016907011407100540c0c00d4203500002c140c0c3d2014005808800c00459058240d4038001c2036611155054004060310300c84120721403240d103000c041c1241c07503100849001d080e0307840f010002d0005150040741210564a9010b = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 86199830 1250 86198580 86198597
    0x90616030b090f060a0f0f05060a12050405031315081504152c04030c080a141201060801050d031704020609090a0204060201060e0613050415020a030e07080307020109030303090201 79
    0x2002c100c0c29a002c0e1030500002801030108451840c2520381038001c0d10107203c14124240c941041c0c099101400c0c09014452070011808891030f81c86001d140c1190000300c6024455810281000d9481e680010560815920101404a002e841c0b11078a240c0c20b82c2e00d6074400569a40d11250011040100368541b13900a40b180d1351342d8190000c5120140c0a00024bc58480d0740041c655400d96240f4811501c4145000d281e008104c04242c000d100000e0f19500402d0050380c540d5840403c803175004011413591700305640480c1459408848401150688540d0788404001d07980314003c001007100500b1008000a0420500030503e48404210541141c800383c911401c00342040009030b000d0004a0b1114402e65010070200a02d80e4240074200c0180324540f000020380c01c0c0075001c40c02c0800003869220016440f140402c0400001c0c047d030f1040032114103c11500d031088000003c028141d282d0120840e44604d1601282c2000c02004442940fa4140c680c000c11528503641178010f455500c6080e4141b141c4903 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 86201080 1250 86199830 86199851
    0xe0f0a0506330f03180703020607030e0a091122051507080f030403021006060801060e100e1e3609010f0609050103021c0b0105010c020301090204230106020609061603 73
    0x18805010f510b503550b030000d62640f070004030303845e92060143e080010580c040d42013080940ca0f40d200704c0d500303203030145005070382c0c10308510100700e40502c103a024400d810310782803441300f24115841c080c003040c070316103c00c0b840114000264a43e4142c81c901401e80d2009000010804240d03801004003007051141c5659402d000c4480c40c580ea06030030403a42030740903030458112050007000501c100c401406581c00d116201c1d5060820007008010820b180c603014a0724100c2c50103600340038946481d0049c10091103280c442031140102a009202040d42c2802560000380c840741e260042504075a401140c02900e034032481224800781203128002c0c154000302c4d5a2503d4508040030305014a2011f02034026010034207500d14410301405030101141840380d0388218030a040058400c004090440d1030918000b030121183e400000d004201c7c4d46002540a4a40310788190b09424440444003146424070b1107180607a179502c002e988481c0d0403903001d031581c1c0046000030706451403518a220b4410581c5400103d00000 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 86202330 1250 86201080 86201179
    0x1061d090106020601030b0912040302040c03330b0414010c02010903050601120308060105030610080901020f030109090b1b12130501020c010b03070801060501080a090f020a0e0f0a0506 81
    0x2038101c02e0060308100010f1003401890706c211794005500b40c5c01002c0102180c1c1000f1210b00450200912640d1124540303450148250040403000c0c118200000c1c600d01c50101d680c0300040e4001e241071251a0707240300042c0c1840c0f80003c1e03804640031600e210b120a0005401101c4110030321504a041c44004100070000c54000c00c0402c0c00313800708035040b6001c0c1c15582000340000d800201403504001040042040d2500d440340c5201c1062081d0419441c59121609010b0180c0140c900101c5000340101c0001240c00040c1c21a042d851300400d080545901e5000c02a80c504100550401d00b00b0010060007410381a01204168814440c8440700c80309002590b955099030b011120380f00850303448001809240c601400303850010841c0740000c00036289010006010b04600405800903290340703040820510803104e54032058598010030f032440c9161642c951041c460b2059801080c0c604407100090350074401c1b4070070f846c001d40f00103240380c007101800c0507a00301458581800002c004540300880e20100c65 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 86203580 1250 86202330 86202349
    0x108150a03080a08270a1202010f0e10060b1318060306020705010209040b0a12030806040b03031303112706010c0813141906050d0e0307060b01031802010801061d 71
    0x1e0b80c0d1400e0504150348200140b24403014800750ba030025400503454140006411011702da070140c415150704400341f0041e801440c0c81c045488502d4100311110480c510085110282101c0540003041201d8440100040b039001d00242c011640040c00e2040c08000010011109004940d080c01700f851900e9545804c180d0304230050464a9039000b1901859625050140c8524100c00b070b11240070b410310701411100d50700b0380c0300380140900c524071002c505591140e0708410803150024084994409850b402e1041d24001b6204c2a14a0f210340b1300310f01d80600d0300104400e9880450300081e0704440c1188200041498040d0400341403040b450400f2001072440c102516412100240c16000d01d440d0000b00001f150350360080700c1c4101181b15000c4621031000c0c54640990320035292075515a6403500100004000c2584e040c40d85110200f9000b0070046c203600100340e6080c0c00e98091015082881226845d0460820001d011034080d40052180d04e101da000821494400b400720620442c4800203e07a1070314 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 86204830 1250 86203580 86203597
    0x50706090615080c04050702030d091e050d021204030807030e0103150e06030c030a020d0b0705040b0408071a0702090a0213030f0503120603030a020d05030703020f18120c0108150a0308 81
    0x1041e00c01c10442d400f018032181c107441d00300751400c0c8140d2508031380c001e4487c4140010007082640d2000c4800522030b030000100700c803107401400c4000f03250b1a4100700355605441c0c03201000603c41c64100c440c40c030303810100f52000c40340c0c0206514200242603070140c2d4019082c1c0d5045041640e02d00381d6098580080400200500007503005030087d08017441070600b00060700c64014020350080d240d10700143ca0f10141d02e810907801c0b085280098032a00004c070b8403440f407540080c0d07110901141c04202c000d004200e040883d000403400d9665507450309000d07001c03402600f5010754026052400541c801002e50014080114880721242d801502c907503615002c0c150f408001c1e1340c20b500c08215000c4c1c4500007400749400c244210f000714100542110003c1daa04800b40704041001000b1011450f45406501680c4440350058042d58907603145060804030300c0000d010086c40307201c0417618000a81400f0070304001840060303455200503900d0040820100b01d0001d01140c10140c854400030101315490058400304 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 86206080 1250 86204830 86204861
    0x21804090606090608030a0e09330a050d03050316120204030302070e010f0f030809060702040e0c030c0909070603200301030b0a0605030705010c030305180607090f0806090c010507060906 82
    0x41c0e080ca901c43c4210381041d0044c0d40564001c00c11f64050b181c04c0608001020800c443c0381d02d166030748180030078101781407284e601000212410100142440000c564074046015603603050100d07540c90822000c104142d2000c1c02040c0100041010000b000c03840e1a10200c8509008480e5105100b030041241e00030343c401c1d00140c1010f4818013104885580b1540140000d044840c1d05070304112a00c88880424400245030080003e0340a115854030000d07152410740003401041201c2ca8091290f840341c5051881511038000d13801e0880c0b0b40e02c0d1031000180140071020003058814204a403d400074003422184a160f5401c1c000304144040c807050040d4081d40c40f4902c1d0800604094107441c0c151896900018880c3d0031480e014071490340e100702c1c58201c55030189404603c0d62180810f041c0b206c6540d42e40d105050150808000c0159004283e100c00c03103808589100d0a01d540e0764401e41c481600340d030440c1054002140440640d84690042c101803402090000341d100d6440d0364036000c4404070302f03e0301d07040d = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 86207330 1250 86206080 86206091
    0x3140c07140109030203091c0206040902280807140408101517030a1d04090602180402090901151e030b120105100501030f06050402030c12010f06090303030218040906 73
    0x8200c07000019940201110300240b1080151343d5010b0744038041c10902c03500428802c032808400402c1c81790000c50181e00038140700d42d1207441d100050080d40c41000040405c2001222607c00c00d6142c0a417011401242c0d83c0c0e0541d2910382c032004460303111918091444090080c880401c0f200f20501000c180c1d90100c88002519444c4006000424000f03a440380703416010070208100c05460120803180c082099141105a4408000c1d480464246403000da0360401c6c5884030035000c10405500a180903008414003580a01d500000c2200380d12070084080c0c1c00210000040000d5001001d0507070b05024603080800d01e1895001a04c14a03100320281c5c0000a91500440003203414800c1010341448500340080c031403443d0031980e00103188101d01c00c82e4101070791400001000a290362201e030250100920540d40d07400d0040f010b450750b0300802c3c21032540c0352030072000182e605400003804040f110591120307000d1610b151002e030b001750000340000f0148543d18140d03004aa42e50b1040c3c18040c0d110b0440000c1 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 86208580 1250 86207330 86207333
    0x150b0f04060e030604121202071b05030105010909020a1418040605060108070503070206060d02031608030324030a1203020d1e0c030b01050d0e0708010507050c010b040506010507060c03140c07 84
    0x90a40b42c90182e82c0a078011109100100384150740062801c0740500f0001554501007104e10028480d0503401740c0311050350fa4200030440e03142410b20b030807964110024441030762212540d070b0403502c03030b550000d500c5400d040c4108054849031404101d1620002d01e0007a05480e442d01c800d0303c2ea8000c45046440c5a0f88a017044015a0041440c40e04590702e840c200d41540790503030700a03503034240c003a0071180710f9000d2498000031540d0030460f0fa0019550300a88000156031481215620740040e02c00f500b80b41c090f007820240c4a0501d110b1680701c0b0100400800c240e180c00d0b1514220040c46405a10416408000400c0740007210f000c1c7d5040b269031043c1031003502e02c011020034215641c02c400c040130141031441a20701aa405000d4a203031000c4860002013000e4203030b14481c54a0001e50200e1030550800c02080303aa2a04000030780b00f5240c50700001e01080d01402d08100c1191412903405010410500682004c15800d0b03200052581040c05c0000710303d00401c55400d5410011602202c102c1c1c030010341c120 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 86209830 1250 86208580 86208587
    0x120703050603030a09170726060903090a030f05071e05031c020a081b070b040608251b05010606080105130903020307080c0a051507020c0f0a060c080415020304030605220204150b0f0406 81
    0x56000c441c1000be94100f040003c0000c201c0a028030015001d41c1c240c6c0340c00028007d00b0f02c1850b004000008503c40003241e9804c008084021612a082c0720f07002d00c01d816405070485030401048000711751b020b0103012809940b19016034201d407072561480b400d562190084101c003003102c103006d4007841880c262168506100201102c40082907000104030441e0118070080d6100b60041100e121800c08506500d0b0004242c032807000c03611405800e96080010000d04d00d80c11124140c141c8105071003010203454007140d61410341c0c0800c140200168020081d000210310400041c020420103001034440309a03036034644500d80300310040e51007007001e250030501580030303010060840c2038070003500d40050301003050002680400e1030348211400e0007010b089190400421b01c0407180540058215200710f024030103c029682d1b0480d0004031511351504000c9120034107460081d1021070341002c0c001c1070074410740c0d0900c4003805454403803c0224001100214054065102500c1c1c070520341d401c1680c40e24506003004 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 86211080 1250 86209830 86209843
    0x803120a0501050607120e03120d06030c060f080a110403020907120608070f030213020912030702010906082802040801020a0309060c0306050315060a0b120703050603030a09170726 79
    0x6100b00c00400c1a280050490b4418151072021410b003407011803807400c0449e05000c519801c00030860030000300102c00707a074581d10000542e405000c030181650340702e10301035400540208598006c2000035000810540b042c3d0049220001c100c04101c0c1041d42d640e01003503103188155031240c0490148010b0141c08600c1d84100701c010318128005003000f504e05111900364030790764000a400741c44a25210403500640350103c030410640075001e80e0a07280900d00341600c070740080f103080780003902c0d60b140060104e00c00c0a240303004000d0b105061001010300c41280a4409241c41210700b8142c00f480005480c000a102412510100d5100881c01641500c2c1400440c1c131628141028503247c940c0600443c0c40005120000414043c006042074441c0e00004101e882644e0010600082c00214600c1980b91b581d1424081d14003518180300d541c84510815840380610020003002540084007000703922a08000d1035034059400003607428682d02d49030a00f034840c40011810a2200d0003081c425081042040322 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 86212330 1250 86211080 86211089
    0x90709050109200f040303080c04030506010e0108101407050a030603050607050705010b060304080412140703121101110313032a020310050f06060912010e0d03060509010e1602070803120a0501 84
    0x1044c508580583d0100c55406203000180c2007220560020303022113080401ca4010b140c0110841310b003581c2d200c4010541f8a8240100759042c0640e01d01647d460105008102110441144c4802690b0300d000049a0a40156104504250700c0b42c20000102d07006001c110300030341441e0358840d44c4034680d042c15400c0d100142d81d40e500880040042101103115503082d1026501484e80054010080d030903c84c0c0518074582c00725402380100e040000030000c0289841c102401350344c481e404d0518400a20794225550650542c1031440e00f0000555a28001c81100210078428140308009900401c5011851810300e406140c0e50509050300c1400e62404200c24440300402d584c0c140041d02e0030f9040003048501c0548518040c05001c58001d1407035a4600e8900c0e21550a02c1c000c2100100b540d1500d996900c21568603004a032038804007050303a040628040b03050341c0d201048071039030381c42b810103890810034254034050440c0103025000c2611002803008210112840000f0409070504614140071904183c2c030 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 86213580 1250 86212330 86212391
    0x10080c0105120a02090d050303010b070201080f130b0a2007020114040f060302070609020303130e0a061406070303060810060807050d050c010e01020313090921080f090709050109 78
    0x1d5410940140c0e614550043c0b14a10141c0c88403010740105070001e005000040c203902000c400411440b00305d2019081070f41c002d030794800c440e845055901d95050340070783e1800c04809141440030003051046d850550415103102c2e00250381c0900c80700c0034182720410b02d6422040d00000803144255a40703c401c190402c030031011485e00d040d207042d0713205202c040c03030b4030640043c584c020a041c1c0600c482c070303404005a00e0f0050700740da5548070752071400074000301c0d28028001c4950b600c0b004035035079090750300c0f52205664000d0100b401004e402c608014542c1c2003040304808240d11480e000c9440c038428003100009500d032407008101581131242d09402c00710700f43c0185003e8800000402d012460020f484a4290070030708111118030300005c0100e00f544120035913504003000d4018000386c43d400725445a00350074094040ba907150081c0c1d040c803810400b40e0b942803200007010b01c03021070811040b003019250448840c204444078240e494035180d01741c0c3c1c000d83c001162135a441e0111100201000c0e04203810b40f01082 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 86214830 1250 86213580 86213587
    0xb0102010b10080c12070c0c09050115110f0f0d0e01020c0d120e0a08031c02130510020c090f0411010903050303150a050d06320a0b01021510080c0105 66
    0x1c20000704030074842e501000b400c5000316078000088821200f00d1900081004d00038a0b0420000e060010010f8045400d207034401000900c100c494440c1070305a914a41041e00380018011003281c1b0410220b600a41d80e01400d001700303130380c0c50303040081c80ea0b21071000300540031402140c0303005000d40c200b06080317134155004901c002d1203907504c2c90070405c01140e100d280007a021101c10000c442030b80700c3c008541d411a40c1c04001090980000016001e03282d5101d00045020f01008200c506074050418104401e2180c41810301c2a8035203c2c140c003044410601c102c40c4007083c6040054072412050f41c40c41d01c00d101c02800e02c000c1c401007044c0103c1c102020700345014450318540d6150b5072440001d001d00d18520308040c1741285580c42c0785c141401000014909090340c066420040c000b80100c04e880092501100510000380302d029107102e00d100720000c006503150b41c48884030b202800040a1450460041c8803010941d10006407926002d24940d0794114070b21070800d5055807501e4030450703915040c0401031 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 86216080 1250 86214830 86214851
    0x4062405010e0904061d061b0c07031112030703050711040e060402060c0a0803041506050a0b0d050726092a120c0607060f050709050d06091412030a0b010201 69
    0x32422a2502c4400d40380f0402c0340e60b450402c00020702481c011504914009015655001c000151481c040c8101607841c0c07a103410010000c1001e446445c41200c201d4011000030404601807203100e43c0c0a890103001406040144036245046034031056007240171480120301078007400605c40c2e07110f210110640c2c0c100011802c458080740d0355400100000d01c56040010141d08401017804042580e9906c00481c1e9141d082610f00384030440c2c1c0900f1980c3d003080c035103100000d0743d24003140d44a003200c1d039182c1818a0850041c203103502426004000d40c0030300800a0805008600b2113504504194940c2c04140c914103280703501600780741c0329440040107480800701c054894204000340b1200f10000700c41d1304058055400c0c0103420282c4503007040d50300940216a034030601030071781c029410b410342401c1c0400403581c030000181e403040e9a40c0202d940001c020b4080600240b06d503400829690b021300320034104003088940641c0346c01000c94812605500120600140034410b010703900412409000030b02406280 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 86217330 1250 86216080 86216087
    0x10f021204060f181104050f0408031311060304150f021305130e061303020c100c0b090109020a06020705010e0a030b0c0307140a090e0907080c060a12050406240501 72
    0x580007400c2281d85100010304076106a000c20000c40700c00c0025011013495062071071902c1d00140105010307506210000c0c404001000600b44038a80c07040d442c070704603100d40c244403109204a01e421100c9065400781000a59070310806184918031411034104882003120502099503201140b2400140c018090700c8650345c0389210120aa820541c3c000400b41c5110010310701420142210180ea4002c403828480040756560010083c3c81c000e808445170420440d0034480900b03c0b031f00000000900d04038070b410010780140c2c08103400441a038000b04110141b86c0028803516040d521560159100c144108025604102442d40221045542d01c002a00c0e44c0c451551000c00102908101c400000026085a0080342d00f507130380c1407121100720703100e604200002d403103410070f4090b1042801400002444980380000c2d10015075503d400a0b00c041400582441b0304c40d00455441c2003488a816110009175250707111f028402d9000c1c03240400c201c400070380c41c29a034100c92078000e817002581c0c0390140100e982 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 86218580 1250 86217330 86217367
    0x270c020309220204030804080f1b0622080609010606092108120a0f05150a140f03060c13060c030801050d0609020d030806100c050a080702060c10020408010f02 70
    0x140c41490140344484030500380382c44140141a2254400306010081c80086405003042d200d481007103032a5a14001c03c80b982d035244520480428052031010840242400005084005010f1038098441071071001420b80d11042900851801c0c1c1c084420020300d403009000c0c0400030302040c00d0081c0c0c0b15040c45600500004520042940d8406106001003005031900845d225038100491007800747c240ba0782c425020b010340d0361001c5001b5040c0320100f2080a1048102c0304070441c010302e41d03174049181100b41401412034012080e4020103d1555881c1e0b41c405000441c071402e004030343e96580d140c104c609894140119045141001072801c00c150009411000c16419500c0c21918500f55260529001028180809000790003000780e503010f1302015080715040340a010119290050104468012601340d001c0e031001602d564400d030703000d80c00319403944003c24189002800c8149802c2d008414280f5042c46171a8101d10180c1c002010402040b01380700d10390840d0007292095141409000d00d16440700c030b = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 86219830 1250 86218580 86218597
    0x117030405040e031306020f100501120f020307051c050607090509150301181109010e061311090301091a0106030501031a0a0e07090209011403090712050703050106270c0203 76
    0x43d601c44100c00058400c00541d14032840850045a0b0940c4580000b51280c1045000f482c8903c941103914000c4102c0e8002c1906071b034044648040c11104680710b8039100c55500324180d825000321000455a03488200c16030105500c03010f81c11140c5001880d000d840d2040c003c0c040c50400903401e0b4140f21035910311850540010003003101008108449e80003a0050001c446400204410004c40c0e0040000c481d038402c10410701141c608200c2c0e039036070303c1e90302c03014008481c055400540c8e148803000c0103c0030380c018010255000c9880341001040b81c0401c0c00c50740c0c0160144c46211410700080c0090061100040c050400c510b41804554035550712000b03512110702c551101e0384402000550a0802a03005110081802084550301c51b6a480580020350000c0040c900107607010058044c2056400b040ba40a200c07550018400b280c506030519410303460500084609004102000010450902510025040ea00e40483c80102640039114580e100303181b400c0c41450030028181d0034244c0210030f545041 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 86221080 1250 86219830 86219839
    0x181205030a0f0e03100f050a0b03250302190806070e10080c0d0c0f02010b01020a0f030c0311060403080114030607140d0e0f0a330f06030203030a170117030405 70
    0x180b14120041c0d4402008120341a050712031726a0020300c540d804d82020b6002c0300c0304e00d002c000319210b0401d0b81083d92421241150140c0c0121900c50020880e410785500d40e180c1501004030707240c4ca83c3e00142c2e58202c031584040e005110404284410711090049503001803050505100044c500310205141071080d0481e60140145a80042c0484228030220340d181e07555450100040110b000000c0c0450314001b942c40c0c0150704c1c9c03016048955000141000d4a160450490042c4600c01c3d5001c5650b152090421400c04c200e1700c601504010702040028055486a00c54451641c10040f10441406c85c00d00c6981c8030354440010b200c08550000d491030009900f002485580c0c0301201d449a003e820702a84400c1c01e4450841404e10300800419041d903c10b104035503818440c25500d184125014984142030030098246081c0452802c4a40c40030f00035801c1d6020116116990380c0000b8196004a49400f012070301e042181810801012445400340c014003106c012103a110810841e5603005602645014 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 86222330 1250 86221080 86221097
    0xd1101020f06251101020c0d030c090506040b0315030f03070201020c011d0405181905060603060c030a020c01060906120b010b0f0406030b0d0204060609060807050306100e040f0507181205030a 84
    0x20310b124550100c04c00300301c80700a41d42d401c0700c500f04942c1c6a44c08444440040d00d408a0190498401e12420080b43c20003080b0301e007401c2c24040d081c3c29030361000d084c03800507692144c0c010600d602c0a00858201404a901954031085e4600019080000740741c40c181c10014050000254000340903852050003000740e400160030b641c1c1850b07901a280b4200c00f1090180300707880742203413808940c1c0c030021410f40c0300d881078032010b455000a151740c41074240c524a600c8102800020101c1c541c5a014003220f9201c207001240c050380d188154002c80f00c49402014003090000702c40d00c2441902d80d0035600601310050084e16004407a0102841d43c080c5000b21420035031511020221a550500341e0301d01c55400600c104880c1e5510040600011043c2c46444045a28280007407003d81c040c2c82500d00c10340004d4032100c65450422002c840800400301210b61056660010382092211442290301c00d0680b600c50b0841712040b99003d416001299018141428111a0a000044000c4241c60301010716080c460305 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 86223580 1250 86222330 86222401
    0x5010c0f020103060302060f0403020a0b21040c0e1e06030d02060c090a1505030105191a030c0c06010e1009060302180405031204050a060b1207051002010204050d1101020f06 76
    0x2500301031740701a600500100e8000e8a00a0301030052007180e20846182c64010ba444447c0740e0300f8050b814484003143e90001c9401764010320707503034600d9000344101240500c1c03584807844010003910130383e01e82c4011800e6068840c5c540030340c2e840c501d800400840007040c8024255400070f6640c2001000050039182c081030034021612a00d20041c0030308030709000f2a241750302e00400144160002d00c82d15101d40c055040c641d06e44d904019001040ea006509800d80300481c3c59840b0b0042c1d031010b0601320000300200400b4002c04002d00c0070394082c14688010301a50705010020501c0385183d600102c4805182100400059440c2d000050460326610b0300c9d10351695aa04285040d40206542e1207810751a0f8802c0008211011540c0b14039984664030030030a4184603414071440c90b14560b06000c10781e0065000340724a18207801500142c0c0c545100240c50103444602141d101c441034282180e6003002c200700203040d9a014010001c0820050f8010445458182c0551a417404d02c40d520b5008494681070a01 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 86224830 1250 86223580 86223587
    0x30f1e180308180906010804080703050304021804110306010515121003020604030f0b0c030c0a03050a02040801150e091c210501030f05010b0108090a0b090a02090702160f05010c0f0201 81
    0x1030080d50840c0340035440755000d00d0682440094185041d04c01d0b940c80d03002428540c059240d107801a0b80200c10541844916a0180d41e90b60001d00142c1c1d0045960002d40c1c000d803211a00d2a105500c107010780700000080b60b0030703d8a40070f410303002144601c5a018501e0941d120300800d9030080c10854410135007075101c03031900020001c07203508007940007540001d000c01070101da04400103800d8030440380305120350358848190006000039200c00036900300400410090502c02c1d0445500b1011080e00146401d40d00d5202a08551110715120843d15135004100700400c1050262948054041e002d001c1e02613822001b86d490b441c10849103424800700840c2903403d5032061140c11120410308008100c6961a4204440c1c100c4007248125515800d200000100354400c411140c0200074aa0007403c1580240e80c079174584010003854400c5511446012001694071909414090011600907000010f6290459540690b05420582c03620f000100200300c943d0780f107034580c401c061f0040d818030b515185610048 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 86226080 1250 86224830 86224877
    0xb060a0302120d020d050a0f050a030f0c0e040510050f1011070b180102120912120708070309120f12020f0708070501090f0308030105300a030f1e 64
    0x280d00080410b90000b00804002010741460740d098003181c440034002d40c0c04542504c940151480040e0000080a81c45802035010b0050b0088034100030840c08500d42d01c22048400c4100b1000006081c114158018140340c800d0540109059441c480254100008144080c1048840b0390041b05e81044042c2d00911a80078440b60580c10802d0f910125610111544250007010f0300d03c0780707010324401c8210b181d0b0000500962210350b0303195940c10001d6810030000c4a544513000d1102c1e9005106814421041080080014510034101c4680720b01050400510744d00e55504583c0e00400001c072810f01042143c2c41d030340b542c680d00c10124100c0702051002281054040c4010003024825110040b9600c10301145000135241c00307070707102801542e132130343e09902542c0188005841058100018400c2d420301007800744038442c12001c010144600e2050913031544c0341ca4016601b070780c0c00c40600603040503404100c8404854503443c003003801e00c40502c00d8002d00e418402d40e0206020940c10070034141e503030b211480f = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 86227330 1250 86226080 86226083
    0x7030f0203030f0c061816140a050a0306020406170106020601090203040206040e0403090501030c140f0711061b010b12030904240602030304150e0a0f06060b160209071b0b060a03 78
    0x410303103c0700d2440302a541c4031816074a90403101e444464406c40120002178aa851010042c2520b17181450020841c0702d10152224680d04200002404911742e1208400000190321903580181e0703035841c0c810300600c440d10340410200300c2a66580100291640003900c076040d0f40407080d005030389031680d1001480324850340d440801040450030400c000e00d60890301e01400c40d202a00c0500c40c03840340c600101c03442d50f01040000c41400b001d000301120300d00d44802078000039210f440c03000909000000043c0d05900040d014601162582c03040300740c1880280600000000c0565401080410320003a060700ca000ea14030075401140d43d1151a501041e040302c6264403215a10304168a045e06e5001c000c0d100c0e40121f0302614020382240700801404442c0c80b40c044000301107805000d80d280c1641c2e071581144c602d00300c240c1d1600d4481c1c401046404902d8001e041520544201d4408803d40e403050040c2d1400c000d00c508140101c115882001061780e00303884050f10b074041a00d2502c2d0340c50b50002850f03100203030030 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 86228580 1250 86227330 86227357
    0x40501120b041e060f05040b0a0204081b0310021611040b0a050f031c0c110306010f06271212140f0c0f030d0504051c090308030601030e010f0f11070507030f020303 72
    0x71502445c180603806107001c6c0780607039110122680d5100d0f0002c103901c0740b031140c40166804021f9408843c003207920090310288004003a244500c0145079114245e030000e03200c1074804d2402102c280c0c01c201050011039140c003001d580a01180f6180070010300d078100540704481c0100300c1c030007058040c0c0c0c0d420302000d83c1152842104c3c4940944a00006000a904500031075001201c0160f4074107910f170000310a412219414882c508407410080100ea840341e200030b03c407503003412100007812810002d0300b106c1c02400b8103c00c54400c00c50981020701102c80c800c12542c041c0108626058102007124044504460b14005441ea43c0c2d101300c20b0040c581459100b0009282c000031070b858401c084d0300d400c00c9001e0780c0103030111908814150402c1c410103042e024000e000c1a00c0b8170041000500e00d001031076014805040008280c10794900403401c0d940700d5211240d500799035103d00005841e00b132081601d00d000d101d8002d402e200c00f9541e5070703a403201c450001600502036414030004640e0100203d80c2c02082450 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 86229830 1250 86228580 86228591
    0xc020609040c081e10060e0d0c060f120b0312180402030103060b0405010806090616200706140a050405040f02040b04080a0201080109050402030c010c03120e0c040501120b041e06 78
    0x822640050790401c4000d9100c0f442c44501e01d44004c4c00500a41903124011440c61800d08182d038a0001080c0c4203401a05d10740911001c00d0480388420000d004035100c05010300c540b010000c180e0000804251081c6180101c132064907280000c04000c9003100020141d0f0b1040581000c0c4030300743d0200c51684d4042e000000100406c00d541d040700c2c4a01e4810b89082c0031690b250b400440e2641d40485e914003040c2d00150024030841c0d084060b02c40c040e4802d0078400302c0b0f002078800181d9000c4001480304503e900907407042103510780c4010040c403080c4140301101e0030656041401841880380d48112482aa03c41e04bc04441d8402541294000d200445040d5070b500d54443e40710303481d110704060030381c0400c0c500400084c0d4070f4107900440744916401070142c00780c0c02c0740c0801900d20f0328080340117800700042c010301107941050764411092498020001059800c516900b0031007503c105030000882d1100c4019a075000038903409481d508a43d001003541324031444030709440441d240f01900509100d061a = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 86231080 1250 86229830 86229851
    0x80c030103030c0b060111011e15050d240903081005040b010c0b0411041509140103033e0a0b060d0302070e1506040906030b0a0e121e0304061b02011109010c02060904 73
    0x1800d101c027900d4501070060085594000b00e10008030780622500c3d8001140c0000b400000e41c1d0304411134903003038110300c55100c800c0c207803101c0c1001c0354440e40c0300304c0200b0300707a600344005440400c0b0a07100401d4110340501081c04034000081145514080040c200040140800d0811412002824494101400030000c441c910411401f0440061180103402c40c0340910003041c4c0d064a040190682c0d4042e140e907441500341075074001382d2000f8041c01c1c201514600d10b100c1d9522114240c00722181c2c0d03c0400801011082d8240407031705141c040c2c0160702c01e07145060b4031000a0b8003c240c0780c0484406403402c2c3c0342c96070b4400c202d030b01c0c51006900c0030b6400304d40000c0124001e10300394096001d0b01d00407800e01c401c1d540d480e80c4610031103d04c812101d4503540701805141c120760f1054000c00c14034040c100c0c009240c100f10301c8240400c6d041940c04640003a11444030714011a4132a44254901015200130710151481c1d03207403403005124022030740707041040c00400c0005648074802161074039413000d0400c026510300c0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 86232330 1250 86231080 86231111
    0xc0f0a17090105070212030d050a051f081e120a030515091e0c04050603010306020a020d1403010909140d020106080c1e0607020109030b0c0a080c030103030c0b06011101 74
    0x816812550140355060041030030805100341c030089041a180e039442d140310368007000810710180031001d185100400c04822030314102e0240e2030094403c4600072840d03040c80000c6902041e481881005c07060308246080040b550000742110100c1c40ca0500c0e0745015007107040d07560510700f40c1d078102040c80b400083c00405003549a4007152040900c02480802074841c074041011004050702d8558500001c09410034080303180440080c1c1040010140c249000c2e5140007080076904268000c1d2919540420207175111034040c08090070070300c0d00745092101c07908405044c82d030314081809603582e8156070b4071078081008180d068903403200c500b103001c43e848000c450200901811543c0101c2d000d90140c0c801812040c02c10703003c23080b41e41307064500c010040e03100d04042c030010390404001030f4100034070000000702040d0b10854513030094041da640c113562900c3e1b03841e010f05060800341c081c4131a00700400040010a90213840346180952104600d09503446003030040f91024070761401001d0b0781d460076600c04400201c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 86233580 1250 86232330 86232343
    0x82a0a0206040516050607060f06080f03180103090312050702010b0909010b0a2114070b040314010b06210a09060f0902011b0b06190902120f1305120706020c0f 70
    0x820402c6440b802c200c043d08140010861084941001051051f07100261107504440410f2042d0f41c00028074981d02d40c400741c500300742094070b4400d0350000034843c0c04448041050487d651020308051200340c44c550340003820740700d011071103a903056074401c08140c416100390001c400d10300004122401c1410001560390007001c545140310320074010f000001a20030100e40c000069120b04c2c4101004d0300829840d45600d00504030075650107806035402c0030520071400030240000c0d60160701009e40d19046001c8140c00c450340c80348150700c110f8041c4000c40e000080544400200342100950480315260f900d10040038100b541c00003424241040e8040a0320701e0141c0c00b2148190007603072294403250406900018080740400702904401c2000001641c038103120110726014100000844d000a507510210f80403a0001d94014882c14015000c0c009900c20702180c0a401c0303040c10a000010002c15a262a0b4500611284e958051800301d50369050100c181e042e50039401c0c110080c0c900c4503125440c6642c403600c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 86234830 1250 86233580 86233583
    0x51e04030803091902031c02070506120405060112050a02010e04020d09050d0311090f01081305100209010f0201021201050f0a090501150315030b15060403061a0f060a082a0a020604 79
    0x8104c607604403440440011a46a6503000b6018101c42103c0d0541100c000740d410400c00194800c0500002d043e44984009043c042601801c54001d42014503100342041e01c180d04c00041e1889406800c408a4400700f13240155960900307085103146604400724004e8003030340c01c0f03038061a8070344264081884400f00310000c0700c1d074042c2d8040103880d441088032100760259442c8141c000b600d00c2a0b011044d406a810f0350b421060010404141e64000d41d101454211002d031020840e42d0040b40f08841960003800c000301c80c5446000950518030307284144035034041c0511840d403060125280c2c081440c0c680084e9180900300c100702c14070856031500680c0300020002d40c61040001d01c1c100b06017460f081d00390b22000c25242d21200302c29454480094000210540c808050740c40706040100100080c2148540300e081c01140308a4160b281442040145d9944051683c1e030156404205440700d00780c2c0610519880404202284981d42002000603610301032480d0352183c0381c0c00003600304000c1d80c002520a200703a = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 86236080 1250 86234830 86234833
    0xe0318010e04020406080a0c0203040e040804060f08070807031e020d02031506040f0909061803030b0a0603201606020309070f05040605150c0f070f06031d0706051e0403080309 77
    0xc46800702030004034803582c0301e40b50014081d41c01041c1d507000305402510307014105104036401c0030346849141c541c000c400c0d50110f81480d4001070410003039401c14036002c01b07186641000d240340c0c60090409422020020940402c041e550120400080d80114104170020241c0c00115150743e240c1c20079000079803065a210001040c0200b03108682e01e440c0040364243c400784600322039590b2401ea400c4001c2c0840f076100303c40d165240c6c400081c8541440c0804003900d03020342c3d000300d8005101001c0c01540186034100c0f00c1014104182c00c130643d5400325080c0c03001034180c1200c59070707021a4104010a000713144030040c03181d40008140480c01d03000184100580e440c004100c2034040c0e60300104402c40e840b500c9642e40045c0344d400c5101c21005080c000e060b1208064040d940440c804a21550501e1056004000340d010f183c107080c0f11540e0705110305c070b42e260302048038001d507010a460300c540ea0300748034400d0f0000c1207400581e021004c01d50100310300248141c007000640301c545034035111605410846903041c99 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 86237330 1250 86236080 86236097
    0x1d030403031215030308070212070c030308060904020619140d0209090109020c060f0a0f05010803041707050d081e03070e040c0216180b1c060b01021c050d0e031801 72
    0xa00392849000403103001201c03d0152940741d90b805440d4070300d004003100309500a000031280d5400901c801441441d215007002e8039207505514001d018010047d180500880540f1304120040e100e0804031943c01001f025214800555020100e503104200391440520203008240031485503da40c01502c0420001c903094442c580e00c61010700c04074000c20b91512180c1d0300180110302e044d0821480103411041c802c01c0440c29890016010341540c40c203900009440e840024100300084101d203a020b5804200006442c0c4140303404002003d502c449200074054240c00610031624a0403030040511100e942c0c60856102d140c580e01c05440b20810300030517401581000809102a407000c200d0b000e80140d01c0802c005024200300061a802015000c400c50040d07444007007017455510f2220b8410070365480d4039400880e5005140c60300039624071003903141c1913501c5108080014450368411112848092038110340303e00700c203d000b5001c1c0c170f01b0100111044c000091448420002d241201c14500402c1c1c032812007 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 86238580 1250 86237330 86237357
    0x10507030608060405061504020c0d080702010606031a090601032712080708070f050f040305010213090b010f0f021603050a0204060f060e010309020607050706110f06150906041d03040303 82
    0x84071201100c0c000c03c55080742002407e500080b501c41c20a00d00082e00040c142522480c0c018600100640d034100850140b2080019003642405500c019004529080c400d80c074009040001e28107404403803038420b14000d80050380e20b0344680d2182140000200380c1c40b248201003032451242c01301445040c0e44100c0b826050100043c050f903400c0340690556602c2d890507540b05c2d00200c4a0001d02d00c20482005000c104031030492442d040544003943c040e400050340d520000c8500703440b08215030f00c040241810024540c0c018ae810190445403141c0c0c03410304014101c00301804a0801000c00c006182d00e640c11714000c0140000050403a4006100b62001c0042035116044184c50000340d00c5000300180c07c1c042e0107a12035120341c0001d0f06461018141e6030800079595101d0b401c000c20383d0880d030001000041280340003241001032081c0300c004040a02400d003080700c0141c107881c80d00d110003405203005001040b0203813140c0e4407014414220440b501c200c0359510b0002501c07a0700520050300094a01d489000307 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 86239830 1250 86238580 86238583
    0x1515090b01080c030f1801020a0f02010e0706020c10090b070c0501030b0a0503070b0a0302120f0717060a03061d0109030513050919230403030b150307120b1c05010507030608 76
    0x1400380c3c3e80b09a00b54115079501d14250071010008161144c40009104800304d0f165090001c4c011000e0140c90f5410303179511801d0020308450305580b103170b80355912148082201d0354000c40c02060011b02900c0d16000c8820700b080580700c8041d00d51045245010018900742881070742d0015a00381e4200f6170341804808141c50421180b514030b80a02036040c0c100135400c01014200400034030070b0701c07001d04016090480c459050107964508492525003288a6010803000070b50041c00701840f50211510304106042040104600e01c07424000206419581c60509028115859a50710360708038000c02802188201d207002461500180782000120400c0100410203140610307130903100d4052424048000c99018024034060302d0408640c01c003902904d00b000d118002001040da20450280d1401301c0d4524181040c400c00082c032983d1604006001d1007801030050340000800c0c0002c00006010803c045034034009070303a64244c000440300482810901d102040410341100344100c000352800c2000f26941c02c0036a = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 86241080 1250 86239830 86239847
    0x509060603060a05131d07031209030506010b0f0706051608060406061202070f0c06020c0310020408030a0e0a0801060306051f0b07080c12120420010212071515090b01 73
    0x36980999040d000b4081e45c1040344004840c210341090100e41440c11103801e480b4030341c04030b41282c1c880c0c004080c14024841180c3e09158401014a860400503240d92206511451b06009400c0d000c1070025903480e043d500c00f0305aa0000d84c000d0003c12203400c114401109409000c40070f000480e81200c001682d030300d414481c1d1001c9a2190300d03000345400204400c80d00a50003440210b9040814500c0600800d011005000140140303400400800c00c090b010549070002c0e00074115103207401040203014000300802503481c0c45642d401c0000c9d034464104009203140c0340755007050000e586407000c00410b10142c1d4210300e003e41244c510000b07000110705118680b800c0d4500840404200c100305900000e0030800c002c060008411043d11040e0401001007000780d40142c003262042c061303203001d000510044441071605455028a60a60400850f0020352248000c810b10005160702041200610555506801500c1045030b1b08022202d802d800ca450104250700842c0845490101d600c002035001d4400c4 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 86242330 1250 86241080 86241091
    0x1060e100311041208121303030f1506080406060305101a0301020403030905010503041407120308160f110c04020301030302010c0206090105040b010e040501020c010906020c0d0c0b07080c190305010509060603 91
    0x8943c542424a4032240b002c03490311008036091401085000181814440d00700c1c011824100030100c00340341c03410010b00341c1e8000d1418040a03071500c1c61010103d0381c5907695078210361240c1408202d0740e0715420500002c0c240d591010340140148402c00e46091895840040e40c8c0010100c4810520304003030500d4200e000d20701000380401c40b40d81e07048c0825030055001e56030080c41921303c161200305104103a820016160300141c181210070b840103041540014100f50f014400c0d250301840100035510082040c10f5080001e402e1141d480d00342000c1020134000b030303242c5840152055603a035a43c0d140c000c4c02080c458075118011b0003911b003c0344c544501801218081c60f000801105140d0800d02c0070b40320110060400c407031945d403c03c140107848500303002c3ca00301c1038003a180045e202d000d980000f40c14091200041d0081001a0781043c0c006102c0724103060f08400c0700d24000d9615601d112000842c2e118682000131241084000c1103a007d17030540090703050300c80954000f0fa00e0345508041c00b40ca4001a0b03003 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 86243580 1250 86242330 86242361
    0x30203010f0e130501092d0308060909010e011d0706110616030216060b0405010b0909040f050106050306010e07020d08040323040b070c030b06060c0303010621020301060e1003 77
    0x8001140300c1c00c40b216080b00c2d1240a5080868855450b1400c4030040c034000c0300d0b40141004074180800511441400041d103213035a5190140302c60790001e00910004200500c146910004600e025409500022008100000800c82c25401030480200040180e000c504244501c0d20040b039094811442c21120300c000b0340c010251515a10f00849645200c40380410416074280003031641035107200212511a4091580058003262841c00e01040d1030050b045091a48010030841e009a2140404c066005400c9694855680d04501c1d0032405851a071388031580c54410000085495040d0a900501400b0540c0883c0d0610071901800d5890301001caa01501017070084c116070344046885902c1ea80b03a65043d0307094516158030b40107905031540000a041d512300d410301800380100025400017136040380084840d5402c16407901b1145950344814000d840400074410445114030124680c0010141b000000a549079038485200800500044c44c0491080303a20100b0258818028840d03c0882c80c83d00e003 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 86244830 1250 86243580 86243609
    0x1006030213090b0117030d050f06040b10020d08040f06020408031801140403030827240402060f0c01020d051306051b0a0e01050705010905030c0d0e06070f061503030f020d03020301 79
    0x85d0b05113408409951141d494001045000c2c011111031042e588920079000c0c04d040c0300e04202050100b19030503010340c6800f90f042c130410b0a510640001b0300b44c070034804070b280a64655442c3c0c030309880e54003020746e80205414008140414410710100c082d0801c0100c009140603031000b07000044851840aa00103007195908200c1440030901c2203048039448003201140c46d41e1400040700d03449007071141c00e1a00c042c0f500074249856074511006061107040120980d0074003241842e8000514500c26010700840030075002425242609013901903c200d2855442c040016140242e116074010041c000300300c03082c0b450072000800205c2d8041d2014480084509045e050040a50068510b204100f0005040c4501805000000358090140c00604c0f4801c1c005181c4070020240b98514003080314404c41d00b03010401082003a41d84a10042d43d039030a07080040348550314428100f03c0000c00c030007044501c03215100745001c41410380000c0010a003e6803582150076031202010100c0c100e003c00c1c001c0c02d0f0500b943c0d0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 86246080 1250 86244830 86244839
    0x304050604030f02030a0b090705030106082a03191a06010f0f0305070e03030403060204080c0a120303020f1213030e220b0f060703020c04061512050a0204081006030213090b01 77
    0x1007040f800300391025048032000c01e003036240c03030300f003030008503800c0c28a070744042014001418280a070700c0040c00c0d400014291100b0b205544d4140c0582da4003034a1407a00e035a405c90f1441d80d410020140a040c072031904010781016030804280c00c130801c4803988080880d01001c0780c01940301321015100c0740c40d550b4818454014400d801c4018010103090030b010021071800400b01654240014002180b05940050b074407480e052420b400c081c5c0302d002c5c15104141e108020817020b50714004826800da41450b006981c1c000c004108200382c02200030301a170380c0662000300200c00d020381d907038441007034002c0c3c503041e000016580410401d07a001d03e4070340503603142c0c1e03030701308000050b05400c11040d40304020030000520702000045111504800029001a8080c2c48a041141407600c00c65000c1c00d603030003c010002d82e07099000350070500b112131074100186c0d5520028006800f07560659018040d51402e90b111030755031101141c050190341c08180d1081807130b111000da42d4801445101d0a003640021a03019a83c0781 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 86247330 1250 86246080 86246093
    0x8030306090a060803040e0a05060d02010206130c091a010e0405270c150706050603030a050f03060a05040204120201120605091603020d15081e060a0c090b0f04030b09030405060403 79
    0x5002c40302441e4a400d00820f000b182400500081c0c016921100580c1c54040b40081c10303035001034080c5000791200003c043c09030360302087c441d034000403d04c0d68200350403041c40c144610300c040e644008400f61070200302c2ca805c40981008041c1d1400d0998416401042200800c000c841040e1846035030340901003206060782080c1482000c41e289101c064480607a481d1000c40c00b9426a52580d41c01d2460000d204410400d09100f15034201d10150300443c14002e201d40080d0540c881c1d24003040424101200050403599021031810142101400954807030ba6140240b4114000300b0500300d010681c1740c100040c00ad10603100e40012100005c0102c88203072140c2a41009402c00c141d80388040503002c20a4548801c002d000e6600f9030800e894500940d2031811010341c1c104000000b0302108491a421828581e03280040c0054000f80c150000080d5034080318415036544400d03903c2100c00c0c003c08540c6040d211807910151044030300500084401d5551240c1c80d0340c80f40303d140107882e800714040c003051006c10030 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 86248580 1250 86247330 86247349
    0x160e040c020307020a090b090c04060c02010813120306150c020604030602090a0e010e0105040c0e03061605130b0315030a080301090203040201090330090e04080a030603120809070f08030306 83
    0x440e0064a19083c40741d0003103002110b40e81c005580721134803a82e2840d4142072080045034003100021340c40b1709240c104034000340f5401002401a04104010000c21740c07400c02c0800444110f5400740135100706101901c1c0190240960740700340b0006000c5104070984490040303840c8044240d00500c11071a1508654a260003504a10b169a40040410b5408a075203044014050b006e4101c00700d007400709614207410007003507032803c0203458100400120703c1d441c0b503140015540c0e086a1864004018004914005c83e454042d000f095207001000c04000521260343c0c100440c0200081d8056030b001d2804601819a00e81c1d4a220040010320100010840e00304a540919080f5105261405a0f81d0352616102c0e00351b02c1494078412541140f5494001204100c000c002c00001c5500380054a68a00200300c9180d200013800a4445900003e00d028024800c0e80040d001d90362201080d03c080221a100500306c0d4800c0728030403003c0c41003850201e140388160003c88212489000114a559a03100c1404020782 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 86249830 1250 86248580 86248601
    0x10c0e0901090e03091c050601140f04050a020927010602060106050307050c0313140f040b0a05041d0706080f0a02071e140f0115051f0c050307020301150509160e04 72
    0x41c818178079180d60340302c4100250002e0b1100d8451070a11070604508084040e44501a0250815100902511032181040d04400201c81c000303140e5940d9010403001c0d12a642c034099210702031044503031a03003000001078812244c031107014001c66a250401a65608400c0c00f56802254040c400502100e1150004024485035107065905040f8185910026031100c1e4004401d401b40a140000c0c0b54205000f0040e200303c400c031414003414420b40049015890075010b00f60081d40c4803030380c0350110303569900065440c25007602100c0c40d299681a009140c00000d1b28000b0643ca031080c0071805546140c020343d00c601e500091101c90042d15920030300c2a075522b0f1081120b5481d4545079944204005000c0d41c17449902c09800030641c0d11080c1c11107031400e541900f0161041d9882032421855040c0c00f02018600d20355030030649080c44540c14100c2ca1401000d10003503142d030030300c03c3d141400306001d541801120340c142d4101c51191035860701070703001c50150003422000501d00420215140b516030005420702 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 86251080 1250 86249830 86249833
    0x901060302130f0c0f0f110a02150702122803110601030305030108010f060b04060f050c120d0f020a0f1209050105010902031006090303021b04140a0c02010c0e0901090e 74
    0x9554a50101d12088507402510001c1660780c501c004160030a40542d0940c00c0c16851704a0009a81031809000c8120f2900000100310001100940c405810480c0b20943c41c1c008104540401000008025590042d40100d02480301d800e028500d030000062182840c10200b9034a01d03d4041d000e14200e42030000c0d110550402410f004000d900314400e2103240e001c0c1d0b0003503450355501d60410484c503007968818840e107117029280050800800d09031074196008e8814925058441202c02e50048843d4081d010056000c0e0007610700d8901c2c89009100144841d90200c001072103a42031805082c4200d00420f0b10780404140b8609542031102c0c81801c40e2102c00e180540000b903205880d86070903007114403d0700007200707081d80002841b4180368034008081c020061480d100a0850855800039110007158508644070100081c20b03d4482d80c90742c02096086021104600b9685024100c3c81c02402001c6201d85c05546000d480b8080c1511031079001c0f0111402074503486069192904241c01861003105202c3d46 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 86252330 1250 86251080 86251091
    0x40f030c12111c0618020f06040b0f130f060c03030b060315120f010c030603050c0909030a0302070c0e040609030e030f07050105090d050a080a0807030c090501050d090803010b0d05010509010503060f0901 89
    0x22114860310309200141da0400845c6144c910500c10000e4140006c54402c040a0004009081d01318003140d2501c5c1c01d120300543c540d2507203c01d05552503c190091145040e29207004105640d20404032441380b4080d540602c08810300c001888190f20003900c80140c0190742c00d07080c00d1076081c0b5110300145003050f40d0458803004140440d603801c40b0150740865000039124901041800f00070050055070710406c5510f001c03181482401036560f0311900340c0c4e081c14190040381e000c06100c6500070f001c004101c8142240303a03a00d032601e00500101844c0300110702050081d000f24445003000a0849d41042c28207000b00300d4542800019141608038080076603025491a2020000407803e10020b0301e8648200c0c0700c141c84100c4a10007a00103140180706804141c40c190442c0c0703c0341d60010740107044507c2820320969582c440021440648481c00d0007401c0c0c1c03617002000140302245540240110b4044843c2040b560340c03143c0401c03010344001c0c4592075243d44020b0100c0d800c40740c8254141d40100305c0d400009076 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 86253580 1250 86252330 86252333
    0x60a140d0c11010209181302030604061407030902061611060a0e0117090712050339030c030304110a0f0e0f07020c030a170d02040f030c12111c 63
    0x1154001510035055580341c4032056821508200c0300c00500d1480c20007581880c06040118a030110032140d0b5540d21400c0c000480c200c001c1c017100311100542c01500746d5085181504102e006028070b00240942051400001908207200e84101880c00e079004007001e1400b5000b48003a645211171120640e2050703030400602d5510366608006111052642d02e403800c010300c45600142031421f01e45056401c150044080103800f40001c1880000e590225558140070104e9041051550103500312490b041450501005502c41d00e54401c900511030742c2881500b00c050002400e80c980c0520040c40079070794010701c0400c0c0011407808a10354510340150030710302c1f8036546050a0145a00c954043c5a0210000013809041d2204401003548609140014403981104401080c2d665000400c040c001550540c84003c0036409582180c0c40d4507003451082d9102e5072203001814a030741c1944011100723030b581c008000400840c040303064402c154200c0d424101d900d6060341400740210140c02100c0c0c1582c6100100f00 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 86254830 1250 86253580 86253617
    0x103020903010f0509010c05041203050a050903030a030501050901080a0b010b0901030b0306071706090f0a0902060408010c0801051206010e011e030f1401050c1c02071b08032205010c02060a 83
    0x91182d64490001c1340c20b00707021810701d00711903062512104102c8104130030301c403084140070011030710f0f549490010b503101c0400c0d108031407500070b0651180d8903000004441200395450b070000350699100300d609505a0342d884c41c40340c0e9070750580d203001000d101c0110300400c18055904043c14030302e40706041c0403174040540300000b41003070750884034080411003003a0201c030011690700065038844015601c00e0310707504000e510420318501c01000034141c1e0362241002001c548880d41070f00c00919a04d4020b2005d03441107c40901004401d00505018541c24a40d4182c0300c80c00103200c60485440d107000c258507900382800380140b03d200002e441010405076200000180c00f04600000450107034510b410f041000c0c1d40c0e16829100e0240c14000303160300c10300a191003080303600d01620303020006c0710740140c0d95115031524040301070304840c2d0b079084092015000203c4441c044020040c12504120504401d50780384a01000c40e25503000f0207000400600c0d1050050610304002c0100356018186100f48040c01100320 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 86256080 1250 86254830 86254841
    0x9030601060206010e060a030b0105090430020606060403021005070501021c0903020f010e101e05040303021c05040302030f1c0614010e0f060f0a20030a1707020a0809010302090301 79
    0x1d10041e881000100b01d201030039140c2c43d1700716604403404100036165861300009002c042c0692032081d8182c1002c00e080000f041d111208440c0041c403119014802441d250508901c660b00740b50150044c0c0303000440600c0c100302102c0589a0007084404110203441017200c00e90028241150207643c20040500a0398924130703810151880c208000c0381800c101c0c64000d041200f0806005540e03810000c4980745414085242d4503c291010300009a180e023000c0b00c0900c1b0449201924051440d0070140800d06505800900c00352509030050b00c104080c11064104980d02103401400580051002c02e41005040000700121090140038806032a40c8891003001c80702c2a9004900b4800300c40c1c02030b1400d50300700c60b12040a8404940741320100302010b01013070f0148200151900000c02c0010003c00c50350140311200d880703082c818080284103441040c49a500d50159401c00c0104001081034400300c076807440f0f624800c0e030340c0b903000d00800ba40c2c41e0744903001900260319181c1130540920002134607407401d01c030f807 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 86257330 1250 86256080 86256089
    0x50f15030c36010c05060105040f091401091406070c0201030f0b0315061003021305040b0325051e010c1115130311040207200102070f030f14060601200309030601 71
    0xc82c1010100800e00e10028400400b07201c0c180b1054282003004240c1c0400c00c14111641a00d02160250000044000900000d00010000a69900703a40d0207082c3c154000b1841521910025014801c2c000703801d60785100c200c488200040702840d40e180154485c2c0c106040442c040d520201d031003100c21001904014540d103015071110400000c0042e18a00384540080080b10f41c2411403070110130442d400300c100d001c5e0003098000d03a102c0041c0c5030b050311304200b00b14141805040048007080c003001840c940d4041480744920035400741400742e4404000440c41150040144c680a84c401d2940c0d0302c01d1a071406049905610504c0300039180e040c07010a100400c03090034046445a005400c614100c510710b4810b8100e580102e10500000c4001415514210502c5040e00d600704010350101c00100e1910b01e90750130400306410084000000c0050002802c200703a84194114040800d0010090355206400c41c0c007940004c81c84403001e5024543d4403180085c149101c82568580004900403a01e0b0040c207070310 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 86258580 1250 86257330 86257387
    0x10303050903060f0126210415080606030a050415050c0918011a07050f031c050a1a0f010306080105040302061006090302101b02030d0513050f15030c 66
    0x280101c4501c0c007805600c2d40168100030181c00c0e9410318510740380c2065071039071007480101c0c29100e10703401240c1044100c40001c1e48001803020401036a907100800d0300079200740c650151480091110543c01096664402c41000e011942540d448001c1c100107004050015126a000703c004041d80700c0e11400341e0f40c8201403090030180d84043c3c04081c044042c1c00081e0005c161000f000061012010340007550f400705010050840c0c9600a50925500384013440c481102c071440300045078070f040300c0203040c0d1000c5c0008041c8104070603031b40c0321000030030744903042d068154001d0042400030041c50465000240c5e0241851b00095464070340950300c4c21a0030503141940503901080810071010078100c224406001c070b03483d008000d24603550104016006031042c005c140701c0c602d02002e0100f08080910b4036801d400800b11413101000301e00c0a403040d4446085035081040c480800b080504003e81d80817041003000c3d00852100304422a440303d13a41000d81100712a2808014035040b00c10f04c02e441940003030302c484 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 86259830 1250 86258580 86258587
    0xc010f020307090b032401050d05041b060f02070b0a14030a0b03010b1507030c062c0601050105280e180906130203150402030c040c03020c07092a120501030305 70
    0x42c015000c080280e00140701c2020170010002041207600b00030440c2c1c00d642212081e07001d540303801a65580201505964074500d0002080705024800a01080612008000c1c2d6243c6488007811100000401241c80141c1e209040030082d07080140000d09502c40f16181038030000a00d40e00341803190f4030540b0408409620b610b81c5420710300e42846031000f031001c21a03602595040a20310600d0501501d2070150a000e2009119404e01081e60010040b00c1381c07000101c0f884403680200c1e449503903440c0406c10140d01c600ca0001c00c0d19405041118000041c09250142041c0500010200c1d80b41c10030901003048100701d80c2c2c581d00c0d02c45000c0003100070f0614982d8416450800b025900d0190300400442c24403100310b2410b800340e1404140403440d020f0704c010340380c9103943e1400424076028100321030700e800c646000108800140e143e405001e1002803e030680341c2c2656030301d901609a4600d0761248141440c03000002c0700032307801d400d03800d90100103a040030015042005180c204581c03090740241c0200b070000 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 86261080 1250 86259830 86259841
    0x6060108090f010c1206300f080304050a0b010905011202060705010f050c0c0114040308150117090705030712230f10091505010b040902090105070b07110f01020a05120402060c010f0203 81
    0x10f0045001510a1301140c403000501c1d02c1e647c41490240c14000341048629043d10001d00c5a05050204c00341e400566950762420305140250352481400380641d04901524000314400d4294003c1c0c3e4100d880311001820084450340801005070b2112000711401d44d603405515490160f070303005483c4211070310350006455000d05545180bd5072240040c11107080c484a08000000340c102103203a0300035a14090741008501040010785001900038000142c25002c04100f200500e40001d440003510025816100700696a80d00c40000710064800141041c408824010080500b080c00e1007894405204451729000840d800c282828034402482541503210000f0100380718078800801507041084000f000250b02d000c60800c1140124010310b840b080d000a10241c0c1d903885a02030b24811900902032000b40e00305100040c0030030800c00420040b5001d2142100b041040620036609800440e881d8a450842800d40d400c418140081049a12502c14485045011024850b129010100281c0160307241010b = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 86262330 1250 86261080 86261117
    0x609030b09010c0c15091502031806160c021504330905090702070e090609070e0705031314100b010801120309230d1101030b01030b0306060108090f010c 67
    0x78030405450381804845001c065010014840072074001d00c07581100e07030148038842c0140c510741c400034086203d01c043c85c0c080c58030a9401940101804680040b5409020107401c0c0c94100841c1c1c0c80c0308903108062505407440c0101281000140b0040c000710300c404040108032503e4206030004014408142c0444d000008582d4071310313190480c107100886c450710550078002c1c40091079000c2c1c0b03800b6581d00700110308a00d0080000c0c8000e020812410706052600000303c3d595230304107d6803143c0c0c034031800c000041c040780b400c6843c501030300c90356071105d00e1603840e41500983c66000040480b400c0c1c103180c0035181000024858452280b40c820307000700b005a26800010025030040e044901e03020404041d0100003078008250f00102c030f0b01e2045080350384401850141c1045c444800c090342200c0d145035580d08014070742010070310301682600d0030400e81200c100110111809180d0f103d40560140004ca815980a07468065009004500700c810504005c003415095400d00b20030880403411140720b98200c4605d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 86263580 1250 86262330 86262353
    0x305150613050f040219050402070f0b0f1017030d0e0a031106070207092007080a080f01030c0501030216021e010206010b03090601170309030109030c0b0906090d0509040b0a060903 79
    0x341880074085410f00404070911035070060b00007803003280c005e081c03000e00c2c8580204410040c48000e00840d128400c5041c0315201e549100c0b41100e42c0300b411400620b000085161603400b0700c154200c0b03051510300380782c4014070f4844452a038003101c0c4000c2c000d01d050641c26000b9542c000103190080d00f403544181c0b5020b031154258004034440c1c1e820007000c200449074009019012101348007000300e000000410209400c200040028007141c10000e01c40042c0714000000f00101c4c00156034181d06a544ca070070300340500000b80030040801503800d030b04018941c0300350080c1c551034040030b28160303615980340d0008910400e2100c0c00c10300320341d44114208256030140040d5005100070b440b40740c5546070100c0035a40360030050240145c1c200c07080a250503c0403041003960304c442c80c00b5000300141c2c0c0031414003078041e1400c1c0c00c080b19242d10440c002264030b04013203815802044c6090003000b12100c07841d029109074004c0992160420f07903c20380000f03640d664910f950000d00d1281c81d0200b0050450a0041c907000 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 86264830 1250 86263580 86263609
    0x507050c030a120c0303060e010627060507030503150a031209120b13150c1e02030a091404020904180501050903031006080c0403060213140a06080f0a0603051506 71
    0xc010b600403101007007058021540c030030314915088402e20754604e4180e00070495a08061380030307003c5000106071140c000c2c0704500c1034003081c0284880520135000d0003480350954007032040002c03000c0c030070000028010406143c2020300b06c54600e00303c10b000c0c800b003011174a01d0740c015144051540000c00c8459000201c01c0d014080d035125000c4600d465484200c12068007070040d0a1403a001030410090100881642d403411403880024800082c01744c00007003084540d40c44800f0914841c8101e860354a00001c02c45030065a070303840d40b000082c03030410081440400304060307503003298003005071041a03a101d02c510810f070b20700402c1c0c0d40444585070a0140c2180d8004040c405607502c100103100c040c103081d1207004229106458030746071554038624220614012680024042400400e26040e00210300080d801654444c001c4c40c8005070400c010171891000310b10450000c184824042400103415000050b40088660400f142540e900d5807880c1c03600b4621b826141c0004110014000c81d460200307030340318040 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 86266080 1250 86264830 86264833
    0x308041e1a091603150212040c14010507050d0807021905010509150c040b0304020105070b0f06090a0213050d02030c0604060203040f080109020a05130e19170309060103121e0507050c03 81
    0x3c820081c0c61450340201d00014040f51031032444841d06201640448841a00001c1450345a013003524181c1c140d03a0303050145c0b902d01c500b04810b990b45c07544181c054940842d0401c0003400b85070709140094038101005001107045001d46868a00b60000740c103104000e091041000042074600343c00740c030741400c1c0c1298454174420010230a001c0d0050f0f201080d503040d50600a0007075502d4903a8401654644250300b402401d1101800412080c084205089882440e0541d001b122942c1c1c0c8101400c02c0b8407a64038808005811441c0500490400110200900d4070103030488000d0001d610000e10035801c2544504016800060280b0040b07507100d00700340013003840100a0009201c03580c002281c003c424001c05004042e0803802c24400c80080d045a80441c480f0f606860688414804444204607640020366444403455034500c224022041145c1c0300301e103148040c20f1a40d007155500700d09046a58102400c0001102c80c203c2ca4801d40c003807644501c02c0b281c40d05541c488140c644141071000341c100842c0300e03 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 86267330 1250 86266080 86266093
    0x203070305030f0c16050604061b0b010e040b06010f020303011502070906030c150f020c090604021c020a17011d25051c02270a09060b0d2004030308041e1a09 69
    0x640300c1c00c054032305482113801d20401c1079100300c22084030640405405403985011800015070007043e03010700f030301880c00f0b080103d000e995110010345942c0704840c03035000140d1081004101c1000c2c3d400480c2541c464910607a0130003a41c4008100685010350002e94600600540402010301e03007a000c181050080d050000d1420000b0720081d44440480c80014000d40e000340000d040c41c2c0e1990704403030341060b000704902c3c000345145013100c002b504030202c00004141c00251004001d02ccc0300c50800c0c102c0d500c0703103c0500c210070050003000018401800c10f1304843c0054903e1078801d00e240c25000c0da840d0581e6034407912080c108241c1010303510f981045031282881080454000c449000d2007105142000c0744800040b003089011445440980d44106041da20b00900030071111129130040196001000c0244039120b0180a0300d6520f0341c80c01044803124404000c20030000f0b02400e503013603105006500e5180d883d13556070004015161407103821550926a8403a03c800d83c0b1000b00419000841d01008280 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 86268580 1250 86267330 86267339
    0x30f010212130f0b0a06050d111c080316030209090112021005030c09040c211a040c1b02010504030c080303070201051005011209020a09021c060503030f0f070203070305030f0c16 78
    0x400030820f0b1018084c01c01d040300140d1102455080400103203c0606119800b000e94108181c1d90401c41030403a20521a0f11101942c0581808117032110540001c50306242d5111000c42e49851000c50800809041d0280140001c03665043c640c28020480d051202298031224410400180642d42d280d505010040c000c3c0030740c82070b0b00c0d001d5803a000d00030380340002d2007548150140c62900000220390600d03280307240c0b40183c00035181c0000b202c030210510820840d0058208010984107a500c100000541c56140c4050b0b041600b08011101b50040c100107103019280d8440b0318041700c42c0e820800b580c4d4000402d00003510b5092103020741c004407000c2c0d2089140e003031000007052082030b071000205058841c000c070002d40d40d688290720020504814210341c0c0710b800e075039011501000725844091240c0381c5000010035040100885420300d10729614103281042084010400341c100050990300f501c1440c1000c00040c00400041a00311030651001e5110004001040e01d400c0b4000c40c407089180c0c14140c00c01 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 86269830 1250 86268580 86268593
    0x1020a0312050403020c12030d0e010b06090904060902060f1909060e1203040e090c0a06030510170309030a06050604150302030a02010c05030c0304031505010b0304020d020609010c02030f01021213 86
    0x108000c100001c007003070680f40c908007246040d181d000401c1d40301c00c082d02c560320f2801e0000028007214000c00c10a11005008601c06422199041e010542200d01040344130244d14004000a52043c800d1200141c20740745a000b141c07060308480d9085008400009071000b081690304034020088405240026441e420030a00410440d11400c0e0617010b290318151080c5400800c0c410794010708215041948585007401c00b066072426042060fa009030748119001c56594841d000e184d00c05c40c04410b100744c0030b505d801c558030003605401c80c0c6090a400305100781a01650300303102c40d818041c0102c40100e1242131510400c01194041c079011044946080750400c0140c80100d50717889a20380900300b89241c1c015500b000b40c1584203a0740e0140c400e001c005004002c0000001030b85801d1841c800c41084660380b20b9090020510094601075071020024100100520344040200700d00041031414860800d06a0702084c43c008045000e100c1c1c5940105816020500700d024150340001100da42c103448032055103460 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 86271080 1250 86269830 86269847
    0x307110f040e120c010207080c0d141215011e090608090102120406020f070506010f0303021513060903090906090f0c0215040809011709060a050a06180510050a030f030e01020a03 78
    0x4114800d00130030761510b113403c20344c141c03808a034116509a03a07800c00c0d110340b191107101504800021030460140072200d0b410707020030b40d03201070400084a000d640300c0400b107004d0824004040d50400c490085181d2100444c0725450341d60030000d07110610640e0a108018001400040085805a1051201a502207001e401075500240c2201c0c0060b82c500365120034142c20300c40c3e42800b402521604000141c90310341d0b04200b0302100d01a50a0b42d40c150102e81c041d1f8141101503800c4075003c180d003c005400314030702e42e02c100c40040c4603041c4140d0041e038441106042e5005a0320907001c40340d942c49103d050080900a00060801c5480580940b1425026903400158050006030482c0c3c8085114507081c0d001e180102c02c1d121554130401c2d001e10740960050303652070045030030ba03d4541c1000c0219100b03a0960180400395a550404c034402070282e200d40c00000e1000511002441000d40300000f80b649440f5003201c05540070317488152015100303050142504501c0786c111030455100c0c1c44400080303175000c1001c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 86272330 1250 86271080 86271103
    0x1060911180d0506011d101d060111161403030306150711060f03090c01020c030607050d1d0a0c060504050618030a060e0106150503010803040306110c0307110f040e 72
    0xa20045228078010400009072800c0c002d1051088a001040850200580039044c4480114150b5903039225084685000904d01c50520940592060005141c1c040f4102590028040c5000c89001d116811000d01c0c01010b20300c110362003001040305200446440010204052095009614504007000403561032205010612440d030400301d451000c0001121100307854160003440161142141c1400340a0740d8802e45e40190141f00c0c01d08031002e154008a981c0036140c01c0100500707820394891809480310b9001400b0200071542c0d030048000d03034500d103030421040901840300412001401d458820a4043c280e0004028040284801c00042c1e0322902120081c40845808103040c2c003103070005c01d1900c0070035a0010202400c000356517900844c150320a10448440c046c50b11010003d150b41a00c140c8820b020300c002c0f0341c01c100010300100744070b03401402e08048200c500318901001d1442040c21074100348401c0f181514130113000144c51801258418039001c04032020400805e40d1a000750303507555001030 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 86273580 1250 86272330 86272357
    0x70503030414190f0605030106120c14090a0504051602060f09060403031e24060306030302030729010608042d020108090309060f040801060e0f0a0509030912030a0201060911 76
    0x50550003011480310b041c0c000c0c010301801142c1300c0d071034200140ca150801d0082100243c0c44085402404240b400b48995000041e00d03500d507808a42000301c25254000c030308030707500401c0c2d40000003903a8843d0f1080c20300c110241c684454180c05808002810300c00042c00d1280054007020501c400f151010404903003003035242c10001503010400501050f01d141245000d4600f86c0740c0880841007000300b000c05004818262005481c868949000740d085803024000500140d00a10002c8002400b0803880c0045503156501d00c0210300586041c16044071003600000009001c110600042195084482400b003000d100081d2403001e403e50085416081030502a040288042c045500c244042c000c559074000c010b440d0f40e030380c0c0d06804101d1025a0291184207000e602e041c20002e1500700c0c8034032003030080758083c107459030648a50300c0c000054000640205900c5c0010480911301c0e81d00c04262031200d0030001c01843c2c80301030b4035101030300b11005580048007042c1081401c040044540c022605805140305 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 86274830 1250 86273580 86273599
    0x8010b040c08071107031e05070602071a03130203030f280807030906060b031003030905030313120c08010f0605120a02150a050912010204081902090109020a110109060e070503030414 80
    0xb44c0d10301d00380d01640702500c80f02a03054034894407000400140d4506008000310f640d004e5668400b26a038100f03070712541500307500240e84090050080c00045402c034500d01c880d0030f141a00c0b600002e0441d031200c00c0010700300c50001110442e019104a0000041e5480700320b032507000b03003400c0e0007410a41e0002c01d040d08042e0f0311800d140401c15180d000101404004118503202d01d4448150006802140030690204d00c11100010300d03031030008112140f1100d601c0d05081d8091a19103078080714459484100c0b038102c080c0c1000700340d001013481a46180210702d000031072030520b0441403080e440d03612400780300260410010720026855082180721300000004849645050b41003040300c1c5801010080c9501c5480d0700032655a040301500a402a00d1140c01914035a600c01181c114100c1c41c0030400035008025040100031000803940030740184507071030402c802c101ca06220b0550840300703280c004131a125522440601050800c0000384007506050300118a4103061000301d0280c0d008503a0395030710030306888 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 86276080 1250 86274830 86274857
    0x306020a120c02061906080c191505070606080307051506040b06190e01020304060e0d0f080705060702060c070f0f020a030804080312130b040204110c070f08010b040c0807 75
    0x207554211210380301d900108402601d560b40251103c42c01c0c0c81079140d45003050300246600441c1d100780000c5681200060903101d2114090044140217104500d0a440c0c02c14000502c240040c03040b5144d82140c3e0341d806503906003500d011001c44080380c04c0441d89520912004e800a0070000d8004d00c403982e0740400001c5582c0349800a400340900410440d00080301007410507184980504607111403000c0d445244440a010004a90364040d0b44a0316002801103c02c40d01c0b54240328202540c460b014048000100392940c958036081d07030154008403481d500c994200081d0a6041c010107270001400303000203140c13000300d4136940c0215641c4d01001e003006000196140465440b0360344d19000710745c03000c6040d441e41c0d07840603c2500d1303030028552840c400404000142003c290803c02000880e4090b0001c04141c4580e02400006c0005a43c03184200b102044645610300302040a0001042c2c403510300d0f00303040d0034058a1425203101054040c01355040c01c0b0003c1e4215001051244d00c609149003444804812 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 86277330 1250 86276080 86276087
    0x50906120c04061202030106140105030112031e0512060102010c0e060f040302030609060403030c050906040b0c1f020c0106050a05060304021005070b010f0806160e12070b0408030301031704030c0306020a 89
    0x30700c030145501034a09100011061540c00a040d440e85c001c800812043e40d07a80c00e0f02407811040c41e20b2030b0020340104014850700a0160740c0c2d000340b900a28160300416581c1600755210003203401000c1c041000484e0107108828251340f2194450002c0c030082c810000ca00401402c600701c00c09181d442400081450313150709643c1c0c400d4500550f001401c891042c20501c0380035403104800d03034083d00000c1c14100004881c500480c2106e2041a000c0c04540c03601d480c0610540c1142c012000c9070078540546088800300003c8003160410b004c40032400180c1d80c1e4405040582154040d90160740540344502c001c01103070343c80609a0fa0312580541c0c00019030340014400312000d00c030b00403000b40708825100005c11950101a01c450039a112107007101d4058440d070700040b00d607403000362a1000107540c110f40703441c96080c01d0945100d03c1c0104400c5405281e103800c0700030f001e900700f41c0080c011940013200400c14442c41c6017051125443c0001440e10303140c01c5494054554000e404003600703840d00014000b481d14417 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 86278580 1250 86277330 86277343
    0x1905040c0e0901090c020f0706090e01080c03030304060b0f09040303020a0e0405091009152f0313030e2e03061215020306010e040504060504020103050603031615060f0602010b0a06050405090612 85
    0x1c7c24050b51042901d881028000d00d40318042d901810490b200045505100081c1c80ca4621400600071419942c035a03441c1c01c05403d24089498101803401c640502e203441e0142c1e81d45c00b652203510301580343d0030349040080c05080b030203113804e01c610300301028405003003c0841d00c0c100c2d9a000c2c000218840c01c4508000c40b001030340c081500d0045103450860b40d031004019900e82425900c005800e04d41d1048404481d080380003e49210781e1242d40d21100f1400a80112004a000403004d481c404080f4100101110b1001d01604c80301c040700a050044d02d403440c3e0520904000c1c0c01d040503140c100f590036866041d280800341e0f980c2090103500002082136a8040c09940c600e8030b900900074481407419140c104050303e02a10b0807404682014003087c0149408000d079201c14003c0401010400119258110050958420310380281d9441c0c0c03020442c1481042c68002801c4582c0000c03c074030311000706000300028554840d801308003041c0002d0016503180000a03421002c216074103401d00a01c10340750780c10240e = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 86279830 1250 86278580 86278603
    0x306050a061511060f150f150d050603070803030112120309020418050d080c0f03040f08030907140a0f090e0705030714010e0306010e06060a030b1905040c0e0901090c02 74
    0xb000403000c049035030b20018601140c50a10159001038035003a440f0600d001003921001d01c096040e00200080d82009441035031344240041441d494040c1480310640554002038034000d00740e80b107800f0801c07181130801459000f00606002145191b03d0300e514035200944480d0300030188443d004092012500c0f903044000110f0f0020b10402200a007101c5108409001080c102c8181c02050303981c00030b0303030300031a020b900c14000700241750310303000280d080950b55520080c42164070342c0c110380520020501620203917205d030a00741d0040c42400c0c2405081c01d5581c1031501014413480040310240325040800c0500411500795880106455680040150038031445800ca40d405220f84400041d43c0f4500c0c40303500302c40050a803142a0940502c00c14103803208024000c0204010b160320204a00d810050018406c02d0030b20b19000605000c0c1c0000039441c0c011051b211860070418140501403850f0610a0700b010500a04008503810100004659640310504c41e40c11081e40c0c5d1001d84803000d0080c0540250325 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 86281080 1250 86279830 86279849
    0xd0201080702011401060518010f020705101b050304080f03070c0509090a021005030711011112060d0f0b0a0c020a0f1410050c04080f030f040e060d150b030609070605040306050a06 79
    0x2c1da11510018016000725040c00d4088c9191100c0e1322203540908030500141c0c0c9607030f010f030044034100028041c4c842c4003280d444042103640c81032140c0c2c80b2508410007000c540b10780c5c042e580c0d640c50080c64900e4014440310200c015002000301200040740f4071412401c64070152030349011a5074524429003004501d2501941007400102c0c1050f10315400001148281055112442e401c4500c0e50318508036000030326034841009003003141740b080795021410700349c0c0f2500040072a285a1641c3c0d8030080002140c4c03030110b890f001c00d40c2c10b006120659020321341c1d840c502440100201c03180c0e9103070b00e5130328000b600d400b6090010910781c0110091086c4211220042c4481c3d080c402c0d402c1c180700005041d402445070518030302607826400c003911800b108640c0d1a1003410305150406080c0017042d42c0178034000e090903034410504200c0c02c1c0083c020480041c80c030400011300142c80710740d202c28035051060007807000500d5000b280091040c16082012354050f250810ba000039a41e50b070180302c1005204540014404 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 86282330 1250 86281080 86281121
    0x150a090e060a050702120d0f060b0415080a050405030d05041106070f0209010506040f1a070f06020d111908060a03050a0b19020901080109021c05010909050c0604050d020108070201 79
    0x304800090182e0103101d85000401c400d50b5000c208907101c00901c4070020380c6c500108581e0f9000381040e0000115103900c000700060060751000c180c1040d42c4540c0c0045906e06034142103400058003c00d000358001003c19082c05035141075581c00d920b03449900c10b1000d010307039500049400e000a000200451900103000c1c0c80d0381e074005003810700c44505141c00c101d10410f8003200114841c01d0050030b0381e085500e03452594423103608000c41c40c4e80d00001c0d201c03680f6510a040c407800300422803028403081d11900417800140d640b200c0c006001e0070340b40c1d041da650f01d04038010491103107a140c0410790301c0d020b02c3c0c0c280f5200c000b944800c00007401c10a496403014100c0e20a5440050030b1040c2d90303080340c1c00741d0012040c0241594600e038600040c0e010780c4081340d001c1810b000c0108000d0645400901c40059443e40d000e003400c40f5110360804840080c1c0064852f556a51145400c2010802554400300022101c00742400d2030040010084401c65030020304102c5150003280a040c000d4002802030070030880ea0914 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 86283580 1250 86282330 86282351
    0x10f02031018110304020108090f010c0e0f0f0102070510090b03070806030d0e01020a08031f08032709040609021f0e0103180203100e15010b0a02010605090c03150a09 73
    0x4005020700a402009040b03101a42c4604050310510000344440c80b03006085541d140c00548045000600048071030180c0c1801e605401401e1141c011084c0964840c04c0d00b410070f1070300b8403806041c6c11840342d0080700c05e20f4100d0a10317a000107541c0d0484404a98444242d60050000c5a18101c25072203a841480c02200744850142c004c5403261107010180c088510485000100700c40100703842c0310560141c3c2120008002040d006d0009517400542404a08011020114001c1c0b51407c5075220003510f4102052000843c1100721403e00c1c01080d0404010030411b62000085a0b1540540300510b0590f5a100d10811174a4960000720341440c600800700c010302c50418040e0200031a940c0c2c0b140003c0ca005003041c8011a2410150203054001c1c1c010244a450003901e03074018802c1d02007a424512440400c00f01080450281ca80a4100444d440362034035544400a801d440b200d400c15032180e01c0442c00c025035803030300c4425241c1c00549028517030030040100000c90000021600410001ea003803490307007032 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 86284830 1250 86283580 86283601
    0x11070c09020405090f040804030206032e0609060c1e2301020306130204150e040b031e0706050406020a03030b0f090406091502160803060a0e0708010305120405060702090702010f0203 80
    0x203e4038140d60340c2007a40c0d2012240c030b8503038004490040a014061000303101605010740515408400c6000c8499110400495a681d1040f90f104040403004100d0301400044e501c92150343c0100040e04007081042c41595440400c50181c00d0400c000710480020002403003030400320740121610f00c4418800070041400c0c030398040e40c0102c0d0f0b501d0117000032500305a074020a038402c650440e8800074903103405104d80c501c00c07100e0700805580c00b5442512002c0c4100c49130740920540c101d034249081080c4070700341d1460555007429855408403003408401d000411080d034010511000710381c1c1c146800200707140f00100003500e9010605049400040081c00c0108004569100d0136240b4010505801081c0d44680c00009901c0f0322440d030425241c20f4040040000d111700050340c0c1106e40141a56240d030f407152145001101b044500b24005120304004206100061064a40c5800340041e0f480c60141004081500b5200e034440c000d004000d41000100a07500c01e41c041310b480000c5410135544d9050a00020 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 86286080 1250 86284830 86284837
    0xd0203010b04091107080a030c0e0301020301090603030e0a051c03090306061215060f05010c02040b060304120f0206090606010809010b0904060605040c03060e041211030310060908030a1211070c0902 87
    0x40403c18030b0701c0d4942c00000f800000351340000b0760162080c0d02d003041102044003c1c01c00084680240f101c42c001251255900b0700140d4080c1041060024580f4503608008240481d00d46289001f4003c0641c144079039200d81000c480b483c801c54400030a00100341c0f4084588034015840600401c1c80c26402098409024001c652401d000d19003480411901c44060300868030b1900c5103140c0441c81d80000c01165008051640d0058001000020413000d0800030a102d80d00440e41164000002c010090006801181c2121000064802070103030380b0304a4034080d0343d0a000f80410741401003100004480a5094202c4410340c98094860b42e60390902c0d181204c00741903580076861045081c080c100c041107101c0d02c40e2201f03c0c2c807501d1628006850300d84030700b400407540314100350030010203000c00386494500308001d41c050100c02c0800e141e12850a00000c00300156900103030041e400c2040700710321803a4030043c82002c00d01401c900080801c04550748105506c180b2000030200c156100001504a100d83d025 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 86287330 1250 86286080 86286089
    0x1030f05101419020a020705090709030605040b2203050d0b0a1508012d0506090303090307141005030105010203120916060c110f0102101104050a0b0903251a0d0203010b04 75
    0x1690280c0b543c40c43c85000c1c0e00552500d500141e00810082007240383c00300e103c40e0403542ca400c103080c900b85c80303446920607104122403e4403403619810a0194a42d44928440410007000740214100c2c915a6402803051040c414010189906c80d00c04142d40e80c1c032561810024040f150909000d007034070407005000070b4030900c140c20464021001100111200426030601a50509068075145007030000b0004075422031079003940c1500c818000d085881d1420000795000e0660f000c050312001040c078080021a5020300c540c0001c0250901c0108410798000007520201c40c40e894242009994014600749400405180145260716404001401c0764200c0481420b25001c0d0841a4048845100340101d200e402c484641c0140d020004041c0c44000640c011001400500709140c40c0665038000108a500d41c1c4d08a9107003040005a00709140c9000c1120b40071111500b01e105030324880c0d9403c200079103007161182c17002c1083c0b125074003140c0500b901d040701c08200514604540f6540c4401410400b504213008 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 86288580 1250 86287330 86287351
    0xa0b041202041b020d0c0602070b0727060504121403040b09031501050d0311010b0603010f05040f14010902070f0203100501060f0c0803151f020f0c0103050f01030f051014 75
    0x48400d01a4922207042000c0324641c0040181c2288240112140c0074018407c0d10f8441d0300348455000521032417000d80c002d5800750b0340c00302480d0000000c6000030076404008000c24400f030400b0807030075400c542503030b0490b444600542d00180203401c2400884440d0942041c0c3c600000402040c10042c039000382000c40d10079001c90b881c14855030104001c20400780182540448124194400030f0701c00c42003407501c00702d480004680880e004000c80c0140c0c0003a08450303144440000c050145092a00c5034070301d48a1846400c2c4002e035119286003006003018001c010300d540c1c00007106824450450100700c01294040d00302d81070482ea8581c0c0360008c20080c0103800c002802611850070b418420303000052419005160380d451a01d076494a815a290303007003200c6800c100c080240406600700c48414070210400e60b00035099021000140a0401b00342001c40d6061501e000b0510240c104200c040c0d9055941c810610b42144d26242000c0c2d1401008511901680781841c20815240062201c410701503202003c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 86289830 1250 86288580 86288591
    0x91b08030903030f030903070606060e040f021e0d09020603010308071a07080a090f020907020f010e010606051206011b05030901030501050402071a070908070308090a1703040909020a0b04120204 85
    0x405032244a04200e05505520602600040b41c00480040d43c11421074000c9074030300030250751010142d030000d0703014901240e201801002c15003424080c00d03c0d5510050301c00c40c0341c03884e4069075003d281102503401c00e1203000491304050783c400a07440540713a180c006046980341c1d82d5038904012141e100240031548000c0300c0300d030010550406070480e80a0170355900c03038043c66540c4022003402081c1002060b04c8905a09061002684900700d505009a8081d8090401c10a5043c4010300b522000c02d034000700e40e850300004100d07080d03014007038032844d1928569003049611003000484000801c2050801d0a213140302e14101003100010080c41002d07000e880034800c50382c4e03460820040b4050404042c01050202400d9158001c2649460b50300401c0c1d07062201c0c5490301e07443c41510300081a00121400700300010941454580405101d00030038115240c0c3d0300c0102c8481d1b2050700c0b80540e10500312000c0d2104980c80454ad950710382140902001e124207074855954100c48882202ca008069020f140340c80b = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 86291080 1250 86289830 86289839
    0x5100203040308030a020706090212010c0306060e010c0821010b1306261009241203020d05181306090f050402030c010e010e0306070f11030717030703020d091b 70
    0x100c20341c1d0803250021001c90440e643d001e1050080c0d8011107041700c645980703890300401a510305910210705400200000380c03000c01c00c0005421600680c1104007480b10441107071060742c0c1e200f1900d41215a000001c60f4854100c0c1d801507190811000060109070140c10001c100c10326990044c24070f40c1d0100180c454400c0d501c0c0001e40f02c80b81070040030042c03101c0404000c0c42240141408039000b40010318031810850f0750322040400c8440e0300f0401050b15000507458144a402516071102622001c211114040d07015900070f941c07a80c3d0010701505011001c81c8440b4100c01c02c2002924401024001a80000c2400d0706038008101c1030040c03072404c519080c400d1407016224032030710b44605d9015004140000c032001c015926411500700c017070704009420b5005510390b181404110700a4000d6115201c0131b0358107510180c0002030800c0e00c1409a80180018401705034944a462141c050107506140e50b43c4401404a029108101c900b51410303091103900400c014481c1004ca0412141880111a00382ca5 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 86292330 1250 86291080 86291083
    0x80a0309060314070c030e0915030f01180204230103061d030306030a060e010b1305070207060503071b020d23070f0b030f0621010905060606070b0f0414011401051002 73
    0x501c400c0d81082d11034100062513090103141c001003158041e00b85403001c3c0d0b02003000952049003c507043c402c1400e8043ca00041c0741000c004945d60b900c01e40300280994090300c1c4000762624104540640318076110040084009030b032440c4458007142c50102201da40d0385a040601c040c04007400500c40221010b401c01c82a011301005482c05032600901802c80700005403034813006041ea040003a0b4040d5030f504045203880c0d5a2070b00480008860b187c000c6483c2c94818070207030405410b5440384080c0701c410030800222507031102c844c95090350290b2441120950354001b15118840d8400700408000c0c2e003103d5240c524080038174107240000000e08803140700e6110000700c40c1c01c09251080f60b40b01071007070012036105c0100c264100d80c00382c409044140d00c00c0300c0301c5090702d002d0440c42c0c5600c5540d41d00c115110a00109014244d4007030015103a56280609594481d10700010040c00200802e90143c0411304001100c0c0d20115084141710003803141e0341e10505402140340d021300c195481284c9a1a0a8140c07500 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 86293580 1250 86292330 86292341
    0xc03050c0901060305190f02090d050106031118010902070f02040c121b020d030e10060f030c060804020904060e0a050601090c08130b0f090c04020a050403020f03062a090a080a03090603 81
    0x345c1c6c0350a140060a141c500340508031050968090a40a00c0080c4c401d86681010912450107030300080307840b03844e500700303a0544042841414002c501000032010b0044141c615141100c0e803000c1d00507521021800e1801482c81c1009000f507205d418141c0b90703100207601c032040500c5002c2c00300e403c205e800c40745284040e60503c2c21040001680121030120f2560740642c1c084a203880c0d101c4161103041941c052118100c400c02d41154080040f4a1414410300c05040308140c00380000b803c20008608113500058080704008100a000035166404154000020f011680c41681c2c4001200d84e6541c5644144000d01032007005440050443d00000c1e0300d14001400b030250701900b00b260206a83c80d2060044051400100860003e00c00c80d078145c8016100c500c02031145100540c0d8003a185c90035841040071600d00c020340d851080e84000e05001e898103000b121030341081350055440c80501c00442800c0c3c02c5005103000b00c0c1c1d002c0342c00840014a00c1c5d01142e00200b09100c0d0f45e03400b101a480c6c140641c01c0781c5 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 86294830 1250 86293580 86293591
    0x906030d081302010c050d031428020705030904091103120f0a300605010806120705131503060504020913110d0f150c09060908060c090d0c03050c0901060305 69
    0x150709038045015040ca15114454060042c03400749564440c03a00c4030b03031925a0302e0700349100103070303881007480c0003040d101c101150400c0c801c1c60010189503011020312070301e00d01980800700c2c40707500042170340800c0400c1040710805280540309004003002e0b8140620854290030000707010340181d6030aa48601802c404940c010040412400d06103400c1c48801c6400444460900703078404024070f0504000082400c6035051030340d00200c0411881e080000041001c040a016140290b0a0490704900c081c2c0104104043c1c86d000d8031101000d03812407a000300070f80744100141500303404000d80842030000d1504018403803070003550100441d40703c600349444500b2904502808004161400422070701d0220512802c407402614038409900c12500c8a080312644800400c800d81e0742c0306181841590030409440c01402030742000c4600300e1900d409030b600d8810092150100e0b440000320b5218650f26240404e03541074101510008035601c83c40c01036a62519040554401c101d15000050400d100340180c51241 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 86296080 1250 86294830 86294837
    0x2406020106120803100b03160f092913030b16050306061207022b0e0603070207060810080a0b0f010b0406140901020a06180c0f06090b0f090d03030501050906030d 71
    0x2c070650b02d0b001c409402c054461541e80d52203c50000d103140b59140950701402d030b07010240560080a22000e003107030424101c41028449a0002008103011040d081d5400303000c0c04802449941003003540740c542e48a42031102218082801000c0b0a1046d01c0400d00c1c42400070712201c03c190003c0f60030980b003a0204841145d0b021208000d0315a0b03288c5002d40064100d0303050700445040c90b40c02e0341d01103442d004424040c030f80d074070301d0500c1c03113071010740c0705680068402e0705440071891410302c0c0310000d4a441c9140950801d00802030701081035102402e1071140103156030000d071048104d080c648901c1020341030b2090044aa0401c00108401004600700d4044034003945440e20044001000a40a5001150700b81d05501a00c01001c0c0420801d000d81030744c540e403600e100d603480701e450300e0405007201c1a42c02600010025420610441d5000300b4800c00792242c0351912902e9021155040600340b1800034900e800c502c1101e420307000c1581641100d8140d4904507454160755a9940526a8810021a565000 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 86297330 1250 86296080 86296109
    0x3040b0f0c120d0f05060907020303010909080c060c130902040503061b07021203030702010c02010603111908071512090b040303021602060c0f1c090e0a06092406020106 74
    0x200c20031600401c1440140016211a481800001074082c0c001c046440400303038669914940b00c504a114055120b2000c840306051414546402980c0b400140603401609994003000003d1000e0307c415100301e00030440854415180c031451488031600119200c3c41e00321901c074070100c2e801c0d1242c0281c80c29a41d000c1c0c0289007541c0c2d2600d00d000619141d044454508404002040140e1070b032a912200c00a00000155641d04001e18000c1c00c42e00f60b03409890869141140500c0010390011840310803620484201008190321074903810f590203540d100d414644188040080c401051507150103080c90a51144600c0c010602c030b1500c117550304243c00800d039660500004000a00030b5010344942c0044408440c0180b2660b4007041030340d440340b0200c60f0603034440fa03941c3c9040c2100700090303078010350100c400c03401c410040c40010349004071500a040980c400c100010b0080c04980e408400144541e1000344403442c0d07a005580948050f0003603100c5084020000400c05034014004c1c803081710040000c0405 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 86298580 1250 86297330 86297347
    0xb09070503040605280915020708160519051f0c051c320907030b07030b030307062408070b04090e0f0a08030f01050d0308070e0406030203120c070803040b 68
    0x2018010801115004050900030700408460082d0030440070184001451240d6410007c500341019074200300c206004201d1940040d00601c01c0e210350b0604601c000c081c070341c80d40c602203040200b1081103c0840d50302d98010024440001040200c0750900c400340850116507641c0303081074031041c09440020500801140c0000c080e00300c0c40c0030f0005d0300a400000c602c10f04003905003d000603a211045146841c078201c54403040500380c40c1e40c01100c400300038494a843c5a803404aa54401841d43d4145640e50b001c80140361828022600d00b240e001c1401c101e68805040e601084007a003500c20748035581580000b00d843e51002a94400b511184c0040900701442d01d0128405040c500b0030b02c15170390060595604052000f040709a80c02c0344100360740c0b0340780e1400400711264400140e001074410710440201e507000c01d0308001c030b2070b1b001130041ca06408014002000315020b03002d00d600081d050300c00c2074159103540341160003030624244c6160a5580050b0b41c5e01001d940c0b0700590140741c000348410032400300c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 86299830 1250 86298580 86298593
    0xf0f07050f19020c0301020f04080c0328030302041206090302010b0306010848030d0509090103030c02030f0601060809010b030105060a15120c05040e07020303040308040209072a0302010b0907050304 87
    0x70741d5807410f00c100c540201140010038203913005040480b2502101240500004100340302e0088a40710580c0100410003260362800c0030300d4411803050152096001c0c215007130620a03011a0f003c0c2030300d030ba4000105609460040010301c3c6544041d00154600000d103901346c07801190060403031b0100300003002c044140074102d41d120004155042200c00951610781035590400700814149102000c0d003100c035071008030a05007860740818000d0b04000f0108030740d0000b90358014565066035007526204a11030034500c0420f01d8400f10b50302c01d1082d80b154200002c0d107507034800582840b82e50420001c1c000c0808070707010701d800d0703600135a8100d83c481c500400a000c507680d000c18424120b0507a00c1c02441107401420301004848079200d40c180040c000040174850340c140020100d4000340c640c4004d500e1458140c81c010840e6001401c000d03c144103d42c00710708041d104150585038500403102c0703820201944040b131500c5c0f04500704228055400c0200c260642d01d000e8a5941c8690350380e8440900c0c56480d591442d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 86301080 1250 86299830 86299867
    0x2011103070204060f0501090b0705030f07140a1506091103040b06060405090702070815090c040903021618051006021506010221031504060f060e03070e0f0f07050f 72
    0x29252440140710300c00241c1d440e030007504020080c00e22212803160401000422109040d04000301e440010030012002440020481c7c60500b01d80942e280c583c82c3c10710b408203014400907c076400b548541302c425818081c2c1c1c04040100d4140c0040c041003041e5403158070605640080342d06602c1c5140900003380821444007856034480d10040c2007516258450b0001040e0280c02d540c10001640294802d002c596070400402e00030160354006200c541c545902c64540d1548071400e5070707015548a60030103080600801c9170956a40c02e1800d41540b25032525007413000d400210103115030380360a120110f0000f9031f4100403201590b030a03501a060301c21781c080d040b001070303100507107024114461500518840400d0034424082501d480b4180e41d940e0078680e070030300d201d8400311010500c500d1920504015104000c443c400845040382407907000c1a09034000241494a1039200620020245040240312155800351030b04c9280040b0b8111240d0703c5003102114240141051100141400c1009199154490070748 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 86302330 1250 86301080 86301107
    0x80c010c140102030403020304080c09040c060f0c060e0109020102010f02070302070608090304030606090903031a09011701020409050c07030f02030a050d021b011406011d06071403070f0c18180201 86
    0x4080074502442052822a030040710f00380c0040c4c201203028440e1440611060410800c00ca4110b8080d003803c3e00e4003e030032241c1e48140340602024005036014036006000358503690390010000c000340003041d9640ca0190690b1a4101c0c0194a00080c5c113030381d813050f4400d480e0869003540c000c002180c20954182d51503040504000c8552000307020000c0002d0082c051403000e002041004200060310386005400e8411418210300c0d00b8030030b034520080c9901c440c4603003411202d0201c4421102d440000025009101d5500607450030381c1440104401c241c01c001c02898681d02c01d070f82d40c180c0a000d10104036240d001b2208501d0016a00f08000303840405150060000c0d0a007440c00c01d11140209003049085801d5050f05c40708440144040101540c1c0088200040c51402d090a008008100002441c80c0c8203080005200e0404125031604c0e4110420072750308829440303402540f16500900304500b85045520544c40c948004120721009203001d8080c1040500e14481c1080740d0300055070055038a20840140d = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 86303580 1250 86302330 86302343
    0x6101a120a091106031302010f030b1207060807170103060902060c0102070309030209010503010b030a0f050106031a01080d031a1003020d090c03150902060a0c031b050f010510080c010c 81
    0x3035a0412140020528010409180000351400c81481e280040d0042a08428403444c01401007003d44020614050115039091a0180090340040010707401420030101e010340210818040b240c00e2400090340b10b0580b4219200c07d002030f030760440c045901e008041c00f08100b04842000400001c0d01c141c000c061403520081c00c131802c0a510710801c9003240c07c40101a0000350078071000f0010740c02d2185400e80540b200b42c0c024400ca1005102198bd9032115100003000014102d07403141c1440800c0d4410809194017a40c981d51101d000846440180001c0c00748281e05c7c043c04034605a82c1d4044c3c03007403840491803107555101540020f41044010041d2071180d006054080140d00c988100c18881c0d9002581b00b1100c0c04c0b2428114100700582c0a88503c02101c42443d201588025980d020242d40c40110341d49043e0070a080b051034211a54114040b00c0c41c0c49502851b0514204140401e20440704440c0354020000e0b55156400210900c0c01031280c0f00e4190060105070506522a01c00c0c1c407112405004d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 86304830 1250 86303580 86303587
    0x10f080403020106210c090b1c020a030804060809100b010c330905060c03071b1104050a02030103051912030f0209032b0504030b0f04020103140108011505010206101a 73
    0xa40c0e2122003241401000301520200381c0d0324200b003240700d00e40018000b9400108a0090f5030002702c2d00e5004a00500050a00700b0642c00c401c40d42d9607004803000d9540b052005440300d541c0e0001809001050b00c01c04464003d034a14500c1c02d544a100c1c104d60480145e590302c0913103800c0d03100c1d604600c02c00c0e00844500a003000800020800c5519030070784132050514000b42042141c1412410210050030f014030101042040c00b0401e90701c51001000c110807007500320703038410b80d901e0480c1074240410390f107d030010308000030840502c00a6026504a074090015118a00400008c84419201c00c0c0f0004060007420100554018481d50101c148413054080040c54010300f4000207107401c4115801030118020070143d264407810000301105044040d00b1b1007818141507950340322000c5001012189400c0740300c4001415a84642c10081c0b9000c2c21740041403c1e56100c0c12a14080c4c145a009074201c0e074251036002419502c00034200384501e0594000c8801541050004510b18103a2111091459010f0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 86306080 1250 86304830 86304839
    0x204050618040312060e010e0105040b01021009080304020405010b0a0f0e03070302030709050709050102030301030f06020a0c0b0f07080c09010503011703120106030c020c01140703031d010c0203040311030c010f080403020106 98
    0x7145a80114000e07155410302c001c40a03500000d6540903040411a54010b900400c02c0000b050082810740c2d5085030049103200315500100d24000c0c446554807045070614600209100d082c1b40114000d82c000d5409002c581c1c0c8030720000b0442c3c80380d190781c400000c041c100e40003a454443c074250064004000e065a500729070300c0d00060300c8e10007650410070700541e070307501404051a00200e02d0340c0101020300142d811903166807a00300c6070701e500c1580900f0103900010701143c40d81c07080c40664001a0312440d4507141d41050000715411000455040d80829200e0000c5034013403a5040544001781e0050350fa992a60b0700307148060500c3c03034854000c0e0020344010301145241200000790107000e4003060781c001660080409009107414010860316044c440c0342d18405d41e1000e440400c640545406080115031031503c005010500c100c0160007035101d510701866a030350f4941c0800140200c2e0300034141181204444410142c4410a100803d80446d440441e079801c1103010303551582d48a8002c0c000021a50f40c0d4 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 86307330 1250 86306080 86306119
    0x5150301110913090b0a0c052802060106021f150803190e011b030e0a031b030303390e030303040f05060f0c09060903030c0a030302090a0e06010203040302040506 71
    0x580000c2240301d038003007015125401e2075100c142e40002c0b81d80f001e00480e60262204860f5000240c40d1120399521000308060b034900031003c4944003c1100f090001400c0a0001c0e074045c50032400e101c078018048c0d03900026889100007039003100d042c400d880b10505880102c032610010301c01007000c10200c030722820000030700703030000d00c0a072401185a10351540414044800104000c8001c0100c0341400058901000d003a0040c59805c44a41d03450700b00861560444000107403000c038181d1000707040c0d00410000e070446000303c4000d00212446078805000000486108000f10b851001c01c18050300900590509040d41c110100782d20100d050800701100d1341c480c4046421940201e805469650387c0300315220411500700a0385070b02412000480d885418103116880c001d01ca4500900d115030404141303041541e40500448501001e000c2c11601c80d0f400518014001c0c2d0041d0340c03070b54403404e41985d001400c2001d500047d4480c1d0b405034051803916007541d0800009002c00360000743c10503003100052003028407 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 86308580 1250 86307330 86307341
    0xa200d0e011d0d0201050108030d0c031b18090504050a0f03051c05010f1401021509070909050d0e0102031e1317010e010b01020304030c150c050607050d0f0e0a020405150301 76
    0x4021071981100b0b0a61061500e0902404003680031a850711004100c1854040213035035908401c01e00101d01c0e1030058500320040c010141681d51740a46005c3d46848880e080382c40c6608141205100c160b000e695411030b081181d004032400f0740b40e80c00035080310300080c810580c0c030f110840c03180c281241030050002c20000c8101c9000090410641e9800060000500c488054001000001d00c5ca0031401c4124000030b4407040085050011000701c100429030b803403401d00c04078010304004038041144031401d04105549240c2203030f41c0808030300c00c08110b0400703520102c221000c20312444580b9943c1e41c944205990340d030348402c0d0608800c8240e41d1010541201c000c0e46007081c44155000443d1034407104c02a40d0841d898600100e041d90b008000810006680590220072101c02c200303400d080191400d0161441c82d41c041e4000e216019000400400d80d4000028004c007000105c0304010000805131000211803020140d0032040d408031105400500c1d254000603407044041c9640400944c5c11030100e0300303495 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 86309830 1250 86308580 86308601
    0x103080405010e060403031706220218192d0905090c0609100e04020d0c020703050d05041d0411090903180306060603040201080a061505030402090a200d0e01 69
    0x800054104074540c0d0050022075010000c407911880c1c180f03180e8000d00400d520b5145030003ca0704030000519070b680d407088459100302503031a000ba486102201303aa0025880300c910311b000211048c1c11400e050a0000e20550041c3c020440c495049007040410b54a007004202c1c2c07090309242c020402405d100b11040e109004264008000c141c03810146d8400c0e0030000a905240d010340c05c2444641c02aa850a00c0380f0070403015402d040d0010100080810060700c5003903c0742d01d42c01c3c1400040c2174071035030014401c2c00700c0740200251402c03600c424804480074070680c42100320101c3c40001154031405071003511070700144160342c48410143c0c0c68010032003900b011604603589820102e14001440480203885601803400c0b405800c20385005000580c080c000a07201904005d09040001c51040e1158440c10180006001c000307100c08100900a02a074422074040f070264401101254114800d80102d4421541a800059251404000705440790700720004201d031003a00c807900c1040b203070000c0c8039075260603 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 86311080 1250 86309830 86309843
    0x503131205070506090d0225170c150307021e0a0203012408030f0304170f0c01020901030f020909070f0311040b0c0d0212040909170a18090905031207020111030103 72
    0x42050f410407a0814000900d103626640048604001c02980420204600390b40c5e19280f03c050b032341c46442d01d8012082a01318604c0020441c01d03003e1421000500d0000c4040120740319003103c60002106052404243c4180d40503030b121b241d40400c040d84961507024200700d000c1c00c4404484e1a60002425150405a01c44d000f00318032800010390120900740601800303100b0000c500e04010019400754520000f0009013043c070303844d0008039813812410201c0c0c40c1d070401c441c1c0b825141c0f002c0c2c0c001c0c0e074000e6025012090101e880d0086809800b64107009940f8144001003100742130360340c0c040c8156a20000311a08804160780c848034803c450841d0780107030001c8c148082d8055290f1886e14a03040c80c0c81d03074141c041d8066503c40700b0010354195001c2c1c101c4090711001e078000f054568445c40c2054140c0708030068000080004a500c01c0e80070b03070081401c2041079040d803800d0a46c1d9074960382d41c400c40f840c00c03e0151031508108039540011b900c141c070783c03a0016014400025190201e0742040003070f400070313003046035403 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 86312330 1250 86311080 86311087
    0x4020d021c06231b0705070e10050d080d0e0102090402070b0103021c121407080d02030a15060906080402120d080412051c0b01030b03030a03020717030708070503131205 74
    0x502442e0b200d00314540e0b81503040e540032108199840c2c0810311009024919280140d102d5034524405082503c0c0b00c02d43c45402c940160303803a414007540c080e20842d2102d422510000002a01e85850921003061076040f0000b03500c8c1c00140d0a0703400c090049601c1c1c1c0c841a42d0200310062103a01e845c402000760a00480400c00c140d4114070410151411f40e500c030500e114042c40d08580412111960041100c800d07040070001d810054140c40381034041c28801400e84040032035a075512840030b800452041e002c52104100c3c1040701400038005000601811000540e896024050240240415500721f40020044003100c1d91840c5036602d090222091500011444c505006c100000000301048400382410914201908801404a5030b0424400042c02ca52690108001d1341d0103a440b408015402030192a07444c0d40201025010707512040c2c04a500f818905c110603d5061300c0002d480c05041580c1e2840d1217174803007401c120307a1a00054404200003208200c140001448130300304040000c255101c2a84 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 86313580 1250 86312330 86312333
    0x7060605120d12090b06010f0e0301050c09010206060118270203131a041e0204020c1204061d0a03060203093309160312090503010501080102070605060a0311040504020d021c 76
    0x1075956002c3c05040f5407400c3c1299000040c0703101601c141c0c010390a00e49407405900c0c406044400306800440c032600340d486d090034044158002e50040820403000c0e001c6070041d4803113000440d14803011408844e04070700402014007004d40074034903043c0c8081484442d00358084030001c001d0101e91043e144d9415480c80e1610110821640e611012402c9000241448a0346042d840b05001621400f00c000d03905022a01748000310740c2c980c2e05942d406407140c030495910b6040c5500c2c81030640d019004503000b01d42d003042c0d0304160307807a192142c0d000b60341c0103803000121606c0d5584000c040e410242903001d01b8058001000ac11040014000725207800d00b80b2080c0c403240c62540c00c00b04509001e80103c0c0c03035400c00c6080d4041000305080c60301c11240d0080042d0442d04021000b00c40189807500482d0381542080c000040d81c80c0150050700315507004600412060300e46c103040101042e004d00c00184055003913174013200c00b850150700540d4811300140070900700500715070000702d440400e11401480350790b4010b442c20 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 86314830 1250 86313580 86313587
    0x18050109060b0309070e070c0b07090e0a060b0d0b060c030c0a020a0b0406050702131d1e010213060f0302041511070b03130602031305030705070905070905060d0207060605120d 77
    0x1001851280c0040d03180d410700c0740c04e903038440300c1300d016a150007014040800c0029200b803a12600c0c16410040e6800c05080c50b003401802c5100d5807183e030340c0040361000802c05034411881a441202c0048410130318040d02d03405020003520050100e154014014001881081d03402d0005050000503c405404011b103144100072110320940c0000c11145000d010502000350041c0031503042e6901111504289000c11034400041c24800c0400900084403001c007410410002521800e80d0b0a100103109040601124039403c0b402907111813110030103000000c1100d60f000d01d40e58040030341540340c094075042d1662100c0300340500060303005000400040c400c1000d20300a110782c002138581c0103010303443d50034007440780e9100303031421103004e84210342c0000031400940d40c12603800086944501520741b510040e0402c252a21707081c1c4940310740c050a203c0014207103403013420f40b17605580340241128140200c5420046c002e41100c2c80890384c50380c2e501c0740424a42e45240c03400e214140d0380c0d002440384007849403004 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 86316080 1250 86314830 86314841
    0x140616051e01290d1b080c0d02030606010503070201060308030106052206080106030b0d0209130c09050f0a0507230a02011103040c050f0d0b04030e011407020d080d0618050109 77
    0x200703072640b41079692031010f107650442088000080740751071211440500003881c1c004d0260300c01442140c0311402c00300042d44499601d001c50780824240c0706c3c0014014140041d84102c04402549a0030400c009000c40d80998051078001290303100004150f903ea903101e0b809a0f0003078200d400415804124443c80c03d0020300e54081d103840c1036860170350481c5030081c0a0a00b000601a0b501419103c02d8250020386800c2c00c4a0840b41d0018049200c03803d000e21480c1c07081603441c0c1c00b80e5225400b540045085400c9001c0c65004500c0c88034681407541e1140e48039070042c03402818413010094107110b05c0c1e0440c004070315a50003021450103025503500118401a0841d104421000303800c61040c01004046411042e201088071015a48120340101110000e91490709034003000300703043c0c00c0d00240401e056024441c24000142038a4141c3c5042405c0304a0b250760148810081d44400d84100c80c50004014801a1054414401c000b00c0c0c550f403903103403901d01a54030040c15050255940010880c0382031a0051 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 86317330 1250 86316080 86316133
    0x3030315090c021b04090203030d060603140705030601030c0302093705010504090c0e1815010c0b0414120c0a0c090c051204020a05040905010e010b011814061605 71
    0x100050169040c000c4d4035260000d912100760003820300c0c000915155a0050b4076003aa0050590307a03100541450100240414050b15000078604500c1d100115040e102c0140074170055100d8609566603100110083c1c0002c10380748041640038014901680c4542c17552090114881d074104c1140600f8903a203203091101d00700d5561041031840300c01c10180e60090221030030354007014008100690409000c1d18207010511009070064010130380b40d01031085156886002d920182c3c2486010f400300300044070844000d290260051100b0404100040c4000010b00d0480f02070006075504a00668940303070243d0001091002c15410050320b400c1000f401080c0b840180420140400140c04080701c010b05074001e5000314a140215400030030290754410f60344c903004000003802441000300600e0450301030310856481015075801c0110049096009aa1780e0b101f140c1c01510150703485140508019101d417082c1c0070395070010010046510f2807200344440c01c082c140120000c02ca8141021784c004030610b01c1940 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 86318580 1250 86317330 86317349
    0x2040c0e0103050f0601090b090d05032209090206160c0905070509010207170303160e0a09060513050606031306090501021204051b031c03181202010f02160618060603030315 76
    0x17002210707030b001482e010540350001442e5440d0050500030480c80c4c580c46101401d10310001c42c190003070840480c1c11081a00c03685412000240c0d0b9a44414247d48110300002e41c043c1c4180f124101e40650040c00da041d09001d00d8240040c40d40c0d1f43c036500f04494042d182c140005500250790b0a070703942c0400c14034000700008014817100c01510300501781ca83c0006007820f03914103240b102c0c4bc02298400c101d40e520301c080c01032850328950713502d800341001402c0c0740c41018060415103513101c80d192100d120756445030b036000c2d140d02c0c5140e032000950700d590b400f01c034000c4039a00d42d914420b0300803d000340301511451003034801d1496036041c40c6c1002490000074421903815100c006050141d41d071008204d400400c140b108a0600340c0040321300c00d5000e41098116903500303600d100b241c0000d01104820504284806070020003021104007038143c1a4403ea078420b403003003894200c1170782c0011115440741c0304980c500c0b000c0000c0540f00c2d82c0c502c03041d21507036841580005e44560300075041813021401c11004244020 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 86319830 1250 86318580 86318611
    0x105071404030503040605030601121e0c020d080c0c01061e080c030f03090103022b060f050f0f060c011808030105030c09060906190b0a05030a0e0f0a0b040c0302040c0e010305 77
    0x41d2070f5070340c81c4030300c1c021081000800310118a00d03034007401c00f42d0a031407401007080c090a1449108420803c0320034074a80034590402d118080920700115182c0a026156a1020025030b84d603211001c0c00d1f4048142c100d400d46d40c0b1000051003121182c82c1c3d5291341020300007404428030b00008185410751000702148241c104041d80010401d0010403038006001c2800d000da01d929620048100d40c21101007240010541c2d0388000841c00c0351507100e00140d810300b4102d0710074140c4550500c18401c0c00350b403500f0b07000100304040f000390b4541480a082c4448204002041c05590640c4658841000712402c580030702c0d0110051245103018450310350140000d55007a00e0515210b40007440702140901420b003c0c1e0b01c401e0070540d8440d8518202c01c054540302110f01e42e954100d1500810f00e60084800c071041a14064402c1201c0502140207107060792a00002c008061498448045810000e0001c072400012008000016212030040e5481d2001c2da40783e0001d10150140094256200101840140c0305002d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 86321080 1250 86319830 86319833
    0xa05090105061c09200108150d081b03070c0603050c090a05100c0501020307120608070503030a14090d14010507090806130203120301080a0215211f0305010507140403 73
    0x1000380d50110301160f42e200c1c1070650401d00c050041401400280c40c007044131080701501d02158401650114082c0d849440c240c0d00c069850b003000764414610f031381c4000384c0d115a1011880c010b0141060341644041015040010046c0342d10310340c440c1e02e0464000d50040f904100c0740d50180b245c0c030790003401001424500304903500040c16807100d6000b507503c1040e1080c031982c2c1d0b00380314000c800000d6a009008640c3c078205140094001d10402c100c0d140000d05280d000b107540d43c4041034803021107401070011414161104003c1d0b9115002698a8042803000d003c6601355964440911030003500550f4640c41c0141030303169039800e40d030008180c0400d0086403e4104000e04000522603400859039103041082c005a1000908144081004140d43c01000c0000f2402c000d0100da404003980c03088456402d03a41d140341125106008054002011482c07a80c5820b60300c686000c1764541c403940c1d4010201100c40c14016014003d4640c0d08241d5142e0f64034400c01120030307001000c0c203a034070b02d00c1c00300903081c180b45 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 86322330 1250 86321080 86321089
    0x12903070c080a020f0d050d0f0209090a05040f0503030403050703090b0a0215070504050d050615011103120402061209010c1209110f0105070b07032406170402060c010c0e0a05090105 80
    0x60040003040420b0002d01044114803c0c44080c4a179083c1000741d6400602004009106030010401c80c1da46601e061403d150050300c07407084031010703a006040c40c41150344110200380100030041064071440d021800c00b4000940900003548a80d110391142a1990705605000b000a00d103500628900001040b0030380305030740c0006003614400c50a440e03142c80c80d42ca00f0304c12241030080354071940d00039005940c0b0004006000c10841d00c07400028601c804441e66000c01164102428412078400d600f00304201d5055080c4051f007980d01c58000303011145410619660b82c590708001700e0f0f40e0301159554036003c4801660107070002c030f1400d01c00b050070f0110709059143c4041c008800c06907a0b1042c54112181401c42e400394098a04c11074000141c0755240c6031021014014103800c0810585444038914a030044440303050100c019500c0681d40c800c41d13003401ca94484140a0b01034801da03030000d403c2c440810302074001d00a00342c03a010243d03600030580081e481844040011070b005039214071800380c01070140d900c4 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 86323580 1250 86322330 86322347
    0xd020a030f05070f180e010b030a050307051002030f1f15030c03150b0d0b190e100f0b0702090a09050d02010c020616080f040807050303310203060a0b030705040501290307 75
    0x83d5000300280d00d010f40d104040c01848e0038800b064042c000d55200c0c009115000c03020f820528042c8081e600380070309100b5038100700e100450703035050303415420404900340407182020b1000d090f892504c03d51001c0e840c0c0c148103100c100c52050040000b81c07505d00c014419075140c000c1401c581d071540ca51500300e908010700e48203140210151403001e1666003042c00c0b035a0f82e40c8528914050f80c00055502c001d52038294500c6250b000b1203601d2a100f605410010b4805400f25945044400c1603480e5418000c081d420005040700c007234502010251110041c070702080c0240031420720103540d600005265298030a001e8200311300104120803820465251104070354010780c207a81d101da2800d001501036945c500c3c2c250b0003070142600c041c2842c8000b00812000c114040b1114008594980704512545e01c4220b00d549042c20f610307402509504600007191440708142c1203010081e9004003078a141984a10114080364000d901c1288400d49000e8800c051a1b0404c401c3c0c04010b2880c03051070b1862802070742c003401c1c565 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 86324830 1250 86323580 86323619
    0x105190b0301110d182102060f0c070f0318080d1d030303040605060a031401140105040c0e150d05040807061415130f0218030d020a030801050603060d020a030f05070f 73
    0x20b40b10566058691818a240d807142d90b4002810311061620800220324440640c1b8900b001d07209401c0400c0b42c11528140c031070300c11803004186601c0c04400303a030f46918a1401201c100d0900c00d484450756600d0040101040182400f2401840c800c0e41c20b0304010f00c48500200ca60080d1403820546130899140402200d0f4490740240d0003182c2a21440c020030804062580068000c245402990f1003402040d002013013010903641169402c2e90302c03401004102c8180740c484101003401e0b070038409004d040c0900000050301075402081d080811a40301d010580740116421203248900150010400415200c0ca40021901868104043c9440000c1c09484040c09040c070b4070505082c0c80960000c800780c0c00209806103950381c1551108811090120b181c0302c00840c8905c2401000c00d400d0000388001a400085d036011fa40d8040b550746440103000c940d500141500b40c1001101c2c0c04200580c07161103c032402180b0420f0042022902410302c03604000040e0002c1950f0001d814007041205076100b01281c050 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 86326080 1250 86324830 86324857
    0x301050d03091502030a02060c0c151008070314010c0e090c030402040f0903031b0201020a0905090c04090207081c060b0702040e0f01060b1308010605060a0f020a02030105190b030111 80
    0x601090506840c080b071107901407415040518140c80031250b010014001d002d04c55001c0302c01c02d45503418203c62900400c00161041e511106035000f1501c03426003038075084600c1000389401070381c82d2492142440d04d650416503d0346801701c200b820800f800d11a582041030946460060000340200142e0314400243c10701c3d108200110201d410365442e60f01050aa81143d40c0410541d002c034a000340c0134009150074041003c0d441c1150174503041c01030085810010950b6240c0c2386860820040084050f40645281071109081c440411005824802044000d004180c0700c0d4a41c0c07d90481c1b40c650f200381160382e044090070401d040007070b49511819604240d504840100380c12018421140c07401d122052604421340c00c2000002e2004000e80c014880c10029481400403035446400b40350070780700b030741c8152600501e041000e81082c17803050080442c1c2e4241c0348161040d0886540002e401e503003040d61141424070702c010060251058a04c94074400c01c80c282c009100003001e0360f5641190707000303001d42034822 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 86327330 1250 86326080 86326099
    0x16030305030925030515070905011b080c03030f010b16081b01060b030a0b03070e010e0405030f0d0203060406170604030e032b0207080a05070513060e0a0906051506030105 75
    0x4011003031062040c076108115002180340d29210303e40541a0451100fa210350003040d2204080e0090000c1503480f600c180c0d260303500001c0c03910004554034040e2070002c001c0000ca00c0c40700d1001640c008018100d480e101c80c019034a904001809655400042c0e1020849850070072288008840340c40c881414180c105003400d4541954850409180d0031028040202d94a03001001c180c0781c0c4290701550041c0707030040c4100701401b507660900d5a0f40700540160590264014010002c80f619243c00c80d91003403040c0244d904040b9411302d002c10319080804224010340d004000c204e590304041c881c030702c000e211508039014203103020060540c8512001d00003a080080a100e06150b0b902d00b002a414030386889420300d4944508c0344078001c0071903800d1454000600580781c0000701800002514052a600440a000024580020481d88030389140b8040461520b4500005407040203145480c0b142d01c04400c041800e02c0c0d140703051801c4a0f40100302c001c01c041d0250900d038140e00e0703040c1a079041d900140c0311001d4 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 86328580 1250 86327330 86327341
    0xf080403060c021c030b040e01020a0c11040605030c040e0a0807061a010309111002010b061804110901020d0305151215090d0c171909030b010e0606090d02150301120309081603030503 80
    0x80c01842c1c1230a001c9600016440e50501d41c401c80c43c820203070040c103407042d512641c401080255902071048680c55800880c0881c410b11b17081d400841c004e80e89608461100041b80d0b02c500507500310013401d603003841c1e642d07290f440301d5032540e422040d01040034a0200124051a910f0f035144114403210613000b21140f0441c001818001d50005d120b8040040505403070300c83c007034000348144a1401c0c8040c01a0304015100242d0408030058880c0300c001600640000c004099048000b000b00070030784034010103400c0d402c100301d48402c141d00020001802c0642900c036070a41c0341e80e0180380040c099600030340c0402e40c46e200643e402075a41d151540c0c0503840c1000351006440c80160350007440905042800c192841d82c881c580c010300340c50b00b200d1113120852801e81c0c0c1c40c000c415040c0f0301180d110340c0020040010a8036440c100310a141e031244000d00c81500c258624030180d00a030426088050789140036104407041c0b42d0050554001042e07004000c207140030300c44546804000c0c05110040501402001054 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 86329830 1250 86328580 86328589
    0x140901030b060a270b040c0e0105070c0504061d100321090e070507020a0801020304020102060c0708070c03110406050d1e140319080105030303130b07020106030f080403060c021c030b 80
    0xa004002e500c1c0764800350841c0c2480010541103c0341c101084c00d24220016406060038002c040d8100b18946641407044214801960b01d03030b03c404c00c102e8200344080700204a558580c07080320081e0a405588002515600807829070820340031b44828101003404500b080003601f02d0201e00c0203404d0755a8607807010005114289c0d8100f206811001d07202d0054020400896409400780185500888200b09210b5407100514200d2006907401303801078101c04001603214080000a00502c1e1103a002d0074a07109041c0c5808900400d82c0e041103d003094058111280e6103000e00480007c0d00e421510342c1d00c0d56104c1e42d12422004103503411031041e005a4580070081c0080070001030f00031070b6540c0589940d0000d594085031041a84041d40010403a41c0c000801d0070b080000a9a00c9040b07890007075100403101e81c50350701d00d081005064504564842001100040301983c034010700e544211809a1514110324109044d108494568011540400c5607050194042100105816440c9c20001340180405005c40c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 86330936 1106 86329830 86329849
    0x10e0601020c011d090403050f0703020705090a1e05092109040501090227030309131d010e031606110a17010902090a03060209060d0509070f140901030b06 68
    0x5003a03410505c0d032680d0018040d041641c1080090002031400303034480300040300141c00c040b40400040c04c081900c260000c8111070240245400c5421f456002c0c0300d010101c0d81c4072a165804111501818003000ca080c0380c0c050110200d501c1060b04248455101c1c034000c40c003a520300000022036415610a480b070f0300703411007020715280c000072b030b07244c4075105001c1c0303860382c0c180420451000c41e0394422100004449510f00042501e01c00c0d01c440d106c5032409a4203c0f01d0990409411000c0c443c404002c6908a200440200103100780d0b50401030018501d0319400d80c20710340f00040f00041e4a412455521401d240029890400ea0321494001c069004540d2a1608000494414000140780e60003520a95002410f100d081074401c100079000c2d01e40945904440b40c020f00400e10444041c402d010010380111b02508404a03401e0001c54403000d4144009000340b00300c0e202250b456603d01115 = true := by decide +kernel

theorem cover : BRFrame.Cov 86151080 86330936 := by
  have h0 := BRFrame.cov_init 86151080
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86151080 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86151080 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86151080 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86151080 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86151080 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86151080 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86151080 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86151080 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86151080 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86151080 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86151080 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86151080 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86151080 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86151080 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86151080 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86151080 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86151080 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86151080 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86151080 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86151080 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86151080 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86151080 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86151080 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86151080 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86151080 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86151080 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86151080 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86151080 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86151080 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86151080 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86151080 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86151080 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86151080 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86151080 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86151080 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86151080 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86151080 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86151080 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86151080 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86151080 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86151080 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86151080 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86151080 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86151080 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86151080 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86151080 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86151080 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86151080 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86151080 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86151080 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86151080 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86151080 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86151080 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86151080 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86151080 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86151080 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86151080 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86151080 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86151080 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86151080 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86151080 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86151080 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86151080 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86151080 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86151080 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86151080 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86151080 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86151080 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86151080 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86151080 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86151080 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86151080 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86151080 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86151080 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86151080 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86151080 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86151080 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86151080 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86151080 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86151080 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86151080 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86151080 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86151080 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86151080 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86151080 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86151080 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86151080 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86151080 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86151080 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86151080 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86151080 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86151080 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86151080 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86151080 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86151080 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86151080 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86151080 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86151080 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86151080 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86151080 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86151080 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86151080 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86151080 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86151080 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86151080 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86151080 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86151080 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86151080 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86151080 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86151080 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86151080 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86151080 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86151080 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86151080 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86151080 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86151080 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86151080 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86151080 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86151080 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86151080 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86151080 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86151080 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86151080 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86151080 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86151080 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86151080 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86151080 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86151080 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86151080 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86151080 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86151080 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86151080 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86151080 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86151080 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86151080 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86151080 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86151080 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86151080 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86151080 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86151080 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86151080 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86151080 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86151080 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 86151080 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 86151080 ≤ n) (h2 : n < 86330936) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
