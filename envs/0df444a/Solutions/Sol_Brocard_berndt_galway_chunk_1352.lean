-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1352
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:31:40.878749+00:00
-- url     : https://prove2.me/submissions/2326bebf-c1e3-4fe8-8c99-c5a62caa58a5

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 242985611 ≤ n < 243165467 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 242986861 1250 242985611 242985689
    0x31509080a031e1b0507060b062811061305010f060b0301090f0905030906130807030309440f010213090b1f0309030915030c0207050d0309 61
    0x181401c605a050f8110800000c409a104800e0f001d800602a0841e001c001e04440740c40298100d49400a205001602c0c0d054040d000016180742c410300014841c0d0b1015184004640070f8103002041800910124540c0511300e050070b012807510b000d040c94441200410403000e4024225610050040942c01400034891400003005150f4880c898a49150001d106004000e070a1070341081a0b90524060382003200c1d8400011030520307801104204540e04480c440c51164a10700100080079841005540700450007074845560340c504001c0b14008004250363310041001d0910004180d284042810711001134480c01140217940342d41c4442428442d00c050303420120f6001240c1c03d060345024950318801c840b89203004000015000742444503038004106816050480e9101581c2018000e4002c020203074401c0c84c00307116190320b514001d91260040041c150029942d00340040c0209d07010407510019004c100c0d620304031007180303a400030104121030040d0300c02c10301c9076002c1d59812074640d240e9141003c6488 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 242988111 1250 242986861 242986867
    0xe18030c07033008060f06070c03020f0d021e010314010501020c0d0302011506080603010608060702030a120f020d1a0102060c2b021b2e05070c06020307180b03010f03150908 76
    0x1400130000541a50a64031903181e2040109035894490308490030381c5c0d448001599903070b00d560204403550991000d842d42003050313003091500682d600d500342403c556103900d038414030380d207182e0006040355104d054442c0c610000c0700060009a03000030710804144400c58020b207170300c0554a4102c0c0544002c1e0030107200001c901e580810740030b401140c0c3da48101e20a40c000c010890343c44c0742c0c003907645000382c0c0c0c1000503800030040121014420160015020b42441021a290a001550394103e0707009440c011007403591034003607068400302c00f60b07031180409091006203614100728880e1101480b640c0c1e00c0814071004068031948001c00ca0703680e003100b075080000c00c5481d461215180104840030381c4030306c0600d00078144001900c08584010450032058103400500c40040244204024030000e0940800e000020314a0300005441e030005503c107041554900300d8842c02d40ea984985070115810a0b458100d05000502014200485040499412050301004620041c00400003002c1c080c1740501464000 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 242989361 1250 242988111 242988203
    0x12060602010b010809012a05160c06110f0c040e0a020405010b0c06011a04090b010203072f0109080c06130f090911010813020108060f0a0e18030c0703 66
    0x19072100c042c1c00c03802c2e215061a0760300e4441e420b00301d030000111400007860300d001404450805021340302e01002c040c10300d01e141c80c1c0807495541384a289108c040715089034041051007913660106050310205010001005580fa0381d1040645406c040c88045000340e54810000300300c01c40401030000a16005403080107696150805540d055105142e65030442c031075000005110089411408168200e440e5094285820b0a00301c80103061055989411480240b22031004140341030584803e50035582c01e41680c0105510100e240048410b814605200c1c202500b0040c4000104031403262000844660b50354100b14402ca84031040c094211141c0c0b895102d0020900030313003640c099201d0602642003415519500c1c030045446040440f04c016000098181e2080154061032006400c042c0050084902d26003060200301c0c25802940304e079103400032502c00e00226030301390788040011089100c00342d8503140014600559800007488010500f59560b524554020100c4050f1410205080d00c3d552240f095 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 242990611 1250 242989361 242989363
    0xa031b0303020c060c06040f140f070303020d020f0303040f0c2c13030c0b0a0b15040504050108071a07020f09070509040b0303090120010f020418050105061c020304020112060602 78
    0x240c041200580718029030341243d80703061000c0c2d0317118200340001081e441d41c95507110880d94400030700c111103d4084010b1140d0ba83c40c00c1c08840304544101c0d00401c0e086145080091030888158120829900944192070068001100301c907401078000654019001d2903140c2190092181e030320181c00c03055102908111018154440310498070214103811042e203d0041d46c2030380313952460b00200030031107014090300020340c800c00e41a0310443c20400000c0c119440000b00c0c071101c2201c02c0c1c204012200080900952a041c4203041c09000d02400406840342051000a00e002101441c04910f03070780407422000715a2403101c0402c9410000d000501d00c1c0c18801d001800b990444105507102d2800c0c001042e4807424008282c43d40c14805940b044401c0004148000541201c6284a400740d5240e86040310301400f680000d0004160908481d010104507e92043c101c80301030300500e1207042d0802c21501c05426041c0303c03080c40d07212100016643c1d1528401642c0035102c44480d42401410400b00080460f0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 242991861 1250 242990611 242990663
    0x9030709020310090e060106052226010e0d020303130615030308041203110a030e0a0206070309062a06020c010b040f0203071b0503071b03051203011427060a03 70
    0x2404c0030500100907011034140e1a40024085c09002641c01c1c001a460700c10715103c11150500900010300b138003a281c007100c448030f2003540c11219030a2465245800c60b54024072904005c030361224080e100f04607660f03100a4585c84050060000c0d01c500b10004c01c203000072a0300140130800c0400390080c0440e40c0e4a005480e17040c1c216420fa41030540d140303410f0f0a90b4003038000c0700414100c0c6000280342681d001c1068004210401d4042e01390721031a41040d005864a00050030720f10b0181d1201c64100f1b1400741e00a288114904040d100031005821035101c9002440001c0a2641e00c03010158881d05154106030052140d8080e081d4424140344040c80750007102e90046004c1c0312680c0c0c8881801d00c0380134400c00d0070400f00350000c003281e10421042011900501c1c00c0c01d14201c0c0080307100b0b41c0a0f034a85030285408d030860710b10a0003000000040212200001b0181a5511305803850309611495240205401c0540c1d4800040c0d0b80c40c01c1c000070600da5822030350728090345c2d00085c1d16000502902030040065 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 242993111 1250 242991861 242991869
    0x702031f0515030307030e09090106170109020906010f2f06180c0402071a040c05090408040608070e01021b040f02070c050a050405090618010212010305010e06071404050609030709020310 82
    0x4055000c2c0b0740200e003008070844e1010b135010703140c0c1c07558044900705000403100b00070030340036940d5603858002c84c400c0e40800c801c84820f036206001190004041c0100086450701401c0307141031088600c20301d0740d5181c2107225075905083d80300d4544540c0301104043d030303031400034411070807024001e8404020301c41e0340d8140c03e100c8c960200740490300841c00210a110881c44ac1400141c10f0300d000c941445401c500001c01a5401485032154055281c1d0303510218207034407026102190600350104080c018598030580d510f62100091504900021013280080e40324076030400800502c03080560110103039151a0003407030f82c1c4078100303d04556490f058181083c40c5a60350045512612240500007103615290095501a0080704083c00c415200c8071402c01103104264042d46d2155020f00404400104030401c00c0d000b18010000030544085800030b0909019000301814184456500706c000d6000403038003618203544060310456511201100040d181180d00e5018044403400003003000100d202c0803507044221 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 242994361 1250 242993111 242993131
    0x11070506090d02190204090501020a09140108041502031503060c0408011d0d0c2405011d0f060f0a05060f25030e040c11010504051e0a0c0501050702031f05 68
    0x40c0c0710070720740585440c40740c00c42c90010303070045401c4148410000706080805100800028500446540b007909903044201600003243d1f08440410415403110060368030740d402440d224013507290a565240324200c1c421440007140b035012000800e071f0b40b9402040c885804004084968078a801c018041983c0d0246c06498459402d2204014190308183c40d03894059a443d4003800c0039010441046450003403a003025100002945910b00702c550f004c1c144140c44020044000c2004d605004650320001d901078503420f61803028104100c8a90040070216403c410200d4070041d8001c50180040c81596054004681c4411300050342c02e0a4041c05004015000301906250b154044030562040081e400400150104d903105000e02c00c0380c58603a000301d41241641c200203a00084210341603007124000c036030444881d40501d50390840d0000e107000d500d13a0709116000520b0240c0340d82d82e901481a25a05c521410b1000109a003811035405000c110346400c80701c071401c4003400505c031010002d800280c0700580702c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 242995611 1250 242994361 242994373
    0x6131701140c04050d150606050409050c09010905060a0207030510090204050603060f0a0c030609020a0f091403100903020c18011409160e0319081c1407140d110705 72
    0x1009603841244982c1181e8011800c00345003105016005806010855241ca034074000d042c90440c0034456103026142c26522140c03503c0c104017182089410240060071a90403d001d05681d83e07901043e81c0c0c0540388141d0340c4607202c0c03140c0101649840e5071500011700c0e9024429070841c041d80e90b44d0003040c58500849042c40180c44007010b05031160403c1d5003400e942d400c0840001c5880c08143c12081c1c181103145400156030750b4587d8414102d802900d10200083e09100b10281003070f034000c0594016107003070b10748500c0b030342c1004000a685503055545c2050050700d8855400038540203000c2e00c1203041c40a020b00b0a1403820780180c3c01d546a0034014004500128003001915050a04080c0d200c1c1010b1180c0f8071a4411401007070707520303a41021907543c0c18450303c450144a821a074020004ca103201c2c0101d04e454900340c003800c0e0010308615148080a51404d501e82030940d004400d01c0c0d13003106903824503460001d04e03142c000e00c180c411a1080700300b082c1007580340c04c1e030f000c1290700912500d8001c3d8140e0302 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 242996861 1250 242995611 242995631
    0x3080610170703230f070206060a1805100f1e06050a050304020f0f30010924020f0403110907020a0506011a04030b090106180b03030f070206131701 65
    0x381d0000091a21450703100726070700082e0814029403251100040c1c4010b50100d10b0554040c0035101801240d460308406030142c14414070310380401c000380d00880200c601c0b6260707505126000307441410b0074140c41c42c200d481e0b001140f00c0c080d10a40705030141c08401884a00b840d2109000440340c0203070841c0c1800030030314090000340036115506072800d1041c1903640074910f480329000c04c00500b20342c0c030000d0760040c6007003286a421303a242c2807941c801d807582d00144070f004a803131043c0b44520180d00d803000080da4140f0740c0b03e038000303800c0c1036548030300c450351012804103083d8013540e0400a00031f2a00000e1142e40008010007808800d508081080b00203c4100403240c0d101801284c80780f281940040040d40103a005110f692002c14100c00d00d0510501c1182c03c107542c07034a4000b0b81900607652181c05941d074040c01e02c03400d02040880017503281640d06c140b007204490004030f0b80e03d2284c4020603210070030101e100d804556541c402c03111154400d8880002180e15407401c0d460800741d12686041661810074100 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 242998111 1250 242996861 242996867
    0x9050406141e011b08091009091a130c0507120c0c2909030309040f060e0903120a180f241503110f0a031b0b0405031b03010b0d03080610 60
    0x41c00007410b030349a400c0011815141080c92104c402c00b15417031102441502d11603191103044038815481540e402e00d58928103211502120741d40e00260071154151600076460341c031a41c0c04500413200095001500498811302103076140202c01c0c00604030b408101091707114076030001000207114068002e0b540e5455a8110018010a0b50720098111022a880c40d40803851550046c115008024080e00c0c500020710300042c5c102d4803103015041e10103980d018144010740031042c603194000750355402540340c10345c4c5074600700082200a1610750350340d40315003c07800111903104501521036481030184003103490342e10b04480030401d2090390411168466004103008007040c02464a41c14171501840242070540d164402d8000c2c0181c6059000448100c45044e01c3d240c04141100860085401103e03610340c41c0d80c0d5083e0604242c0c000c00c05008144000e000595000c039980b50345003455509a94112210701c0403d002d0903801500a43c08803500700d90f0800c0c142c0016500748038043c121007640c100f5549010075 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 242999361 1250 242998111 242998159
    0x6170109050705101709190b0a05060409050312090705060a0f0809030a0504062613060e010c080c0702010c1704060318030807080a0204090612021e0108160905040614 73
    0x100c00003418441e807003607102010030040d070703041004141962408400c1c418207d42480e0f800c00700722200171220040100080f018417440b0381210040b2030510501c0701c0d9494956a0b40203100300b0034036022002c404107420140800c00740c2c0c01000003610f501c0d03c480108a02a00c0280c0e00c5030040b000c00c0c004c400162100c0c40c040110348404109444980c00c148c01c01c40e00f25000e07012005045149042100032456180c030903550340d441441c410542d400710300301d607180490546801940c91080c0d60b040c254503210154201a040d644961000c681d0f03a01c84c0c01c00c1c001200e02c1c0b80500c00c058102d000750190a09605903140040051b200030740c03418082500c2400005c40700400303400c0094001401040030605282c803500049820200d40c00700503062035200d05c252001c540055004140301c00101007100301714148494080740120381040c1c01084461400000303020404010003030901d15040300417441c039590080060b00c0c050320b4091f0042004603240d209160002014412540c1300b40d4501e014030244043c00700714 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 243000611 1250 242999361 242999389
    0x918020f0a03170f040504060305030702010207060512041203020d0501140a0f031205032a130b16020103020a1106010b0426030a0c080708070f060b03010207050604110406170109050705 81
    0x40312900f0300324000301540580003410240502c142c10480083c00fa0784502400380030714001d00c0610394880d51440007a01c2c00705075501030802e01006000452029910411140c1c0c4542c02c40c901c44030030340c20007104800030711442d50709204242c07400002090f800c44260441505010a44500244a403a0f80cc5140c40b004140b00c01080300ca4690441d00c0103a00c210302543e040024041d1b9869400c111444038000b41c1d8080c8840b11000d030010a085c031895004151000080010806283c68a0482c00d80c40094101c5000f02a0500d900055034228051144460030040d84a039003c0e2101c658441000c1078480d8894410301c80f0300180716032040c11840f01845900d8041c8040c4008500d8040c0d112010342c1c4448100b0b4083d901e800050201d071012960900c010090107200b00c5032400c0f1070019181c0641105c0c0d481d18a14080e81c814000e510004900003849a00701d50044c0300040c6900b404000513003c0c001c185c00039403281c6940f4040014080054002d0400346104100f665100394984061040d42c0d0310031b0709 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 243001861 1250 243000611 243000623
    0x50d020d060e030903060103050105070e0f131a0301110319180f02010c08030a0912050c070306020705100912271214060115080a05060f1005040918020f0a03 69
    0x50903200181a070303405060a02407400c10f80382004841c400107401e14600364401e4581d42d46807402c02c81495031003070482c17103111000c560ba11544078011011450440110030440403203a03896020b001c0504024041407040c0744018020f020b1040e4040e0400d00642081e1080e0000445098008a6400300f502030003201e01d510071080ca00c00c4e002501d94501e010a5980c059050203048581d22020461510003148901818240803c40c40c41615010a11900c0e207601c01040103c1441481103114020a00f40100d0790807401c05601d8500500b840342c1010200c40c0d80030000d13441c11a01c00c081011418181e0100c4106071501d40d403068500d0038580604012011800310f0060010052003003400d203038020301c110340c01211a520390240000b0307500d1415030281c1101d189114025104855103a1020885901584c0510144058144075002c100d00031081c00f074852117000302c101d15141807441041035500420300c040051104501c060300000d42e40390901d900303038001c6070506846840d070b0400c21020f500712540a4 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 243003111 1250 243001861 243001879
    0x1406060403080a05030c070c0f060f02121905160303060302130e0601031419030908010c05190c030c06050c1e0721030605060f0307110f121303210801050d02 69
    0x7260482c1d2652001b0003600d00814188009000302e410303d07100e0310280815170794018038035041031000381c002c0850b41149411503000d140b0200a074807140060b584800d030242c0e4400007401401d030059031540100ca41e03013440c030740e40f80c0c5114040c103a06420000840380282c82246140e00c907600c4407416110384818040080e4000b2004000140601c084405800b10700700035504042c611450300440103031340c1c00b810b600060400310b00b80b00a090a1007600c0a04c0d5450034060b1401005900c07181000040904103001d01440400c01d201381401011186207003a48500100942c2c0340403070802a0300c0d042001000d910308190070004000304440c00071644000e421040320104052101d084201002080b254101007588800000030709488040107444d5201341446500d440b45172058009000355600e4045001e5a400b1030029a500000802d519142c0c0c0d80c8003507101c0d034a541e06503060000c0042c580c0002d0420000222400d03015010070140c1c001400150303074800c0c0c01e990352010042006620100a03610203001 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 243004361 1250 243003111 243003127
    0x80117071401050706051e0a02070201020c210f0322030203190501020904020c0a020f0d03050a14040b0a020d0305060402180603040f021008041202060c0a050c0a02060a03140606040308 81
    0x31150300346240300140f410601e801142e03900c5400361002a40c008814078415603050307005e071480c00a0540e000b800120114103040b12900000c1d9101400803000740510080288400244814503501c040000000201d400d26040801015070302d500280d1200c2000d141c08020300b014041e07801140084940003001800303903807544140c003402175616100c02c988966003000190219141c5002a200c1c0604040c050000980b41c4d0060003058540011414032a40642480c100041d41103010f407000400e840c5800301240520410890841c822030b0049032410b20080ba28840d49a4001050880c1d03842070ba8083c02940c56040030305c01039020740c0f00c460002e22070240f1480410300301540034681c4180112800101d4001c0e80e000b1a8130344900ea400c520002d40f01004002c217004c500103620b81302c0c18003840241242c0c0340000c048904c60003421040010414005001c84200d10200b0142d03400d560010201d5513204908a1301900034015401400c40b004141c0f40000ca4510300b00303090760b0450b50021140b515195039 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 243005611 1250 243004361 243004379
    0x51f1a01050c0c040606020c0a08120304031d031207060c140d0207020102010b130615090b120403300b0d08070803060d0f050703020a05030c03070e1b130608011707 72
    0x401030302c1c00740358802c518480045503141c0c09060b004104540142a408110ba010b002c52404290815081a801400b601070485041c8080b0382d4401c1c5c0601d000e142420101a01003407062666021613894411400c280c0702c40500302c0010800d4920a00c01000082045802602d10710440c001c40003c01d0811300014070398152a400403c415441440001884200500003802110800c49158809a61010140b20000c03520700303180e01420990501c200c0c218034102c1c1043c403500c14003e281c1015007001010400b094020680c014943c0e5803010b0003c400070072401604140c50300c103c400d1820318140607a468090522690030a00e182d005a40503180c40d02d6500c400364517610240a00d90040d540c0c4e81401c010030740140f40116007600c514085c00085143d8010045a1009a04a541320760804651004c060b5000914001110512031045066913103031010180d0044070642e04200c4164000398804081409005400a681007a101d00030583d0301d03042c49100b20141d4501445807644220014054021 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 243006861 1250 243005611 243005617
    0x30a0b1c240608011d0316020105090d0b04030201050603161206200a05090901060305010b19050906121f06080f1f0b09010201050129030c070807051f1a0105 69
    0x42401c070644020751101100070112012070388518000c0c0d43d208100008441e800c003000542000d010001d508003400103d5410304201200f034020b0610900040d844000c0c0c071a088403d1520343c01c12440003941c0303007070304010b8082c013400c8031242c1c801e01850103c00c0c2c00c000051020800e48420402d0f034034030020310f41c1d0341e03030014140c1e441d0412428000b80d08021500d00090018020000d80b0b40e181500e802e403103001e20200d44010b0300b0050a041c10312005001c0500d642c2c0503520340400303101c00d00c40220b043e07400980e4180300b4002c03402d400c660000340e5103000101150455003d500c0e0282890303402000c071401c81c1c0c5440c01c40d0003201c0010300b9840206920580b401080f9810074003404c6525500940c40823042d0030f001e0207900c820010400454500c06035a0207100f01401008013601007035612910b506e440301c11000442c2c004222690102c0400e003107000e040d040c7c580003607102c0507a0395200b406040460b544c4076260406601440c00c9100c05040b0101d50040d214224540184048203034007000040d1910b070 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 243008111 1250 243006861 243006893
    0x806090a080310050909160801021804020d060b18090112032705060a081503060421050f030a020c06090c0f010f05210a151401180801050a02030a0b1c 66
    0xf10710743ca0049107136030314220280e00600321603000b02007600c54610300c0000440c80f03034071036491a441071200010743c910101418001000803074005070745100d00707449038000740410340003045254008180a408107009500d0010407040032a41a0010b0707a82d900d00714110400c0300e0303000700010b0061a0501e001c0b074003010805885404070134041c41068441001c40c0702070f00940030341d40024849006100c4510f01c00b07030100705c080f0029006000c4a103041c1d02c501080d141903000b102046105a2200c40d1454481d40a841c1d0082204003002e907641450f81400002c0c0d040140800554058080450303448800000c020100500181c01030500c610490015070703120300e00d0401c40051180803c807400020804084c6001c41d003211300070302c981d81d00b881c0f00014200d41003400c07001082d0100242c00d2240c0c4420030100b03901c02700240307000c0400341c1d40100441d41151503a031148a042d8208000c0c40640b146540107140304401606040100240c0c10b0104000c0070101c1c0d03942040780d401a10460040750002c600a0349807 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 243009361 1250 243008111 243008131
    0x307020d020402131701020d0f15060f0207170c01090605120610050c010f1512080d0f11040b0c0c011b06090203030f0a110c010801080712030c0204090609020103060806090a0803 78
    0x2482d17030303080e104400b0450004501000d03503002070300f1a8440e80d00d2040e61844080d604d420480900d0900c00103041c1c113403502400d02845024402900782c0c510800c0304201500000d0b004854000340c21484a5680080c4184a80462015240412003d226600795814103c1c034240480701515400244010300340213a480b04100601009404d40c0e0000900078040000701401c0005999007112503e24807241190300481c2030400c00882d003030046541300c415610280f100300000181c90250440c00001040281c0008a20343d1010400088070320082c0b006c0c142444805066500d559990707401103403c0300310f0600c0180c1411000c01100c0109103990f100b5041d4034409004c0340d00c3c10801c0b02c0c2e0080039800c903240700000a05180034204070741100b4806d03142076810a0800d1034803541000c0b0300c56104c0b03009000c0c107005c81c0f40c0c07801070009261041810880958020b4010030070f600c19820100d0103010700d03001c280d001c2814810009800d117400612144a200b108015042031681a56407151550011b840c480703038 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 243010611 1250 243009361 243009397
    0x90d020d0f02091008150a1b0f090902070201050f090a03201201090b06010807090f0e15121207020112060e01050114030105100f230307110307020d020402 68
    0x589440c0604110140030307071420640000d0620400240701001044041d0696448500b0010341078002114560101200092945a90390510780001011865010003100401d44c880c0e0340d620b038100305880388152040c2c0e14220325a855480020691049141c02070000b0002c01c08000c40c2031126000c2d06a8000040c00c01040700c0e92512a040c03105603424030340040c0c4000151104443c40c18100d0302007d80c4008000f80f101c1d1000751102001000001c0400e41070215850000d1103441c0709010743d00141110482c406041074465900c10400c040403542140c49052540996441d4036001c01400c4086803142c0091515125000c4072450503000300710228103000320304c0703521403080782d0f14010f80c0090003c03001d240f031440d0b1502000400c03202e018000c01030800410801441542c88901c40060309180038103000e001011304a20894220820860400003040b44240081e01c07801070300300641c014106070740c0d0040c0405d02e40d14401d8a81c403407414025840062070b0a4071f801828a50007409004a42d1501196 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 243011861 1250 243010611 243010613
    0x509060105042d020901020708190803060109180506040c1b03050a02010f06120605100308191713030e1008010909050319020706080c07021003050a1b0801081005100902090d 76
    0xa042e4200359a0f0b00402500804c0c1c4404c0e950741040a18003c02142008100310102d442c0b20000d12451020050000340740000013400300e9000d00c1c00c540052080008035601c1c4881240f43c2c0005000c25540548150f0903d041218080e100b00b903036407501016000c0002899965030b8040e210f50340f01e444c0241c2076540300e8001c4000000144a41001402036090301400180b062034040c2c200d030303802040ea036000d0341021402d0001c1a890b01c15a07229448901c007a515a070394145c400e80d1000c1c20818521100c00580e010802d00b030f103c0707850303a205031071082d01c4034003554500c0c60800c1142e000803110440003074507101c010420036210750411000e5501803015649010041d441c0400003508810320803015a20070441003081039030010f8020313800070040e4002400c080065001400b2800300c141003038109074441020a14865040d80a601e02212401203d2252030400e032010300701400901c903228880c000c42d803101c0114260f41c09a548540e00e070b0401842c031113040890410003504201c4c3d40d141c201041d820010 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 243013111 1250 243011861 243011921
    0x70c020a2606070306030c23090103050c03010b0103051909140303040302060106021b06120a060b160b060910061101140109020301180905190618030807020709050906010504 76
    0x5501140144014801d4068080d4240d141000160440e410140303006810000700b480d4010300c0c4142c0c0c014884000c6480001540084420303807401a03541c0c131404020001080280008022907604020340003440003000c05401542141c1c0110b8441102c03c034020003602c466142503100d083c075180300c0c2030304e070032014911000e95280d07400c02ca808502517070213000107000c030302d8040052041480c003a07042042d924858401003106401142c4114007411042c1d4081501d04c24160842e00240000d81c01807522840f00710f0700b220800301401015100c00d54002d010403128105860201d10400c0c18089450b45280380c210119002c0042c0c500031100d82d540c8039901c4d04646460302502e4004c003100741c00540c0302d504000440500900340d5140001c080e2401c01403000184002c20500098180c103520181805618244003010f400401e485184415046004e4010550400d0305076029045690840c1c44140d00c540c039900448006860300c80c07499119a004002d9032070141c029511440c0c0c0c0d021600d02c1e5000303503a416 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 243014361 1250 243013111 243013139
    0x50109170715020c0a0f030302070e0601020f0d02011a06091e13060906030212010e10020901020a0b01080106030309150e0f04140403080a0c031a0609041b180e06010503070c020a 78
    0x1100107802c20203a1304071603d029a05080134004004031040e241d403542c1e030080d54640d982e2080302290314400b000a822a0b00038405075803e11071500a0751583e40721014001e009110054200b6201000c1c6030704d414030742c200003003a5048854098a40315111400640d022400d000d045900303980580d001d02c69092a551724010070006103c088801329080b411441001114610034140c0c0020780e14000580e2002400004c0803003202c0c461400042c0e40d1028600100e00348160f12030003519900303010000042a003015030100088078060350702d03414026203820002070808200b50345440040c1552100b44a07501e0105208080000b00500c0081d0b40303413581d517480216003c00ca90a0340411030503800c020521910380100c00e41d41e1124a070410940c91b1802e04840f40c0203281c580d081c01000d0120b118201e64844da8846082641c3c00c40000311011407200340106920282490100c2402c000c1a0000e00113032031608490040e8016141c040c1035542e42d000172103440003170782c0003641c0c01561040001241d002c840700c4 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 243015611 1250 243014361 243014399
    0x507051503090105070c05030a08040c330201020408070e06011e020f060c09031e0f011415060403030c060504051e010c021e0a02241801020c04060501091707 69
    0x200c59180d29040c09402e0865038000c260380e050014031011031b40011401b00442d16100058107110410340c845041c41549803940744c00145d14000e840c0040d446410a40140400c901038451100081d200c02000032400d0b0701986c42160096440380710240804c807400c030b4000c0c1e0300290601d0407102c0042131080c50030407000406415001f42e08540580b1032220b006008407a8418008a5902d02e84003425000c203980d1942d00300060b14102040c07500031030f104002c0c0a42202d000c2103d0007403112020810000d543c50b0340654000c441c0300b1485103901c600b4101841602e007120f4141d112510250456120341014000040c0112114091414034544480528080ca1507a84c806400041e1842c1a140d0191038418034102c00300314070001c8111101c00c894006207440f8010350690f140400b9903101d89902d280d5103144141d109605c07001141103440c52030305c21098030075400c00b6400c40e40b200b10340c0c90a1100b110068001c1c0b90000c4c01c1e010b414401442c420507240052600e000440d070308580e0750b40d0715084660500350 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 243016861 1250 243015611 243015649
    0x20c040609020a0824060d0f02040603051801062102041812030e010e0303071407060515100806010804020105130506070c090c05040e130f081b06090a020d0f050705 72
    0x1000c901c000ea00060090707004550040c19840a81880d0361040145c0e00103821a1280348005298020602e8a401ca009068040c44055486a03280c1c41301401610303048801c101201d21907550007003d0041402410121a41000022100100d0701c0358100c1030340c84600243d8226480b40c0303010140b00c0d5070740040d4013041c0c010002c0c45210b03100140c008060300c050200c0301c10981c0c14400c0c11000396001004690300500036040c240442d21942d00c1d210304500500720040e106a00c0d02042152488032180c0222110104650380200403c0e074a505454a210070346015001841410006005500a500400c04524942c2d041c640103903a4030005010340d440b0782c408a03106003441c0c00c1004441240d0113424121316050802c0380c10141401000d82c603d0700e00524003041c00c86401d050105000074450001040ba401c01c0145548441c80c0303001c0d910000300d2480300520340c4544000510030110100e4083e103a140d000b003600c6103000c015160a03d40780111501910b60340151000015142d54403188507445841500f = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 243018111 1250 243016861 243016867
    0x121623060c010e070b070b0a0b01110709140f010617060a0816090e030a0503070e060904050705070c09180305031801150e01080d05090423090304050301051e0c0a020c04060902 77
    0xb452030130500c3c1d5503c170703913880c01041c09420b0008079111041e56101c5c455080005451180c800121004d66a401c00300140f0301a075180802d001285400500c164000540c040c107046c0c40c1d040c41007056400902c0f4100c0015104007140c003004614108468004000401d081c050545030541c042c200585406078907400c65004000300101c50490050700a030001002c0038600f0036041d078074007400c01d100003810a402c01841403540d0019a403102c041c1c40d400000584100b10a161425000e840c4be0701c100304c1525110f81045002800c00110300407051203a1702d0085141d2500307110366083d07070550405811880b11b0a81d400144a1045c0244900b04038540a801040449841c02146a141185c10f070000503050308403007455180c25801c1411a2000482943e001940380e040300b4100e0000706d10310070444280c00346030050010301300c0d00202030f105031001140200150349807101801c0c0030480c42c1e00c01003c0149000c00251140d6a1000548001c0030ad90058032421540c000008046600c4c940150400035404 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 243019361 1250 243018111 243018131
    0x2040b12150c2a07030f1208090c06090111100e250b1812150604110c0a02010809070315050118090215030c12040809121623060c01 58
    0x2044946400225401c2868648070020300e050140080142c1401800d040740e800b1a6201c80f0200014401550080e85510b91103070b82d8540b01e051800845001ca00282d0010302080100c500070135503c0311902c00502040c50503000340e00658403000e18030a4418940606c51242c03c00301d015000c6c400086070b18030054100a948021460441d507000840d90030751401211702448014104812111104540503a5401c1c96092000080407003551000000460140703600c2c00304008030811201d0b010790b80440701408041a00308040301b580c041e80190b00a907a110cc2030000155001e02c010076006600d0100740c40909850340c40d0480c2850f005501500450f580c0c0c80104608242d42a6601416050b00000d10115000d0b0b0006985c040c0b002c81e89641000000000c900c4038650002240c4c0c91002d00c7c0b11100d01d030b240c1030601e0040794000e410307520300a640345103003170515500200700c001c8800041c16101202900f408070f100303510340c02d100c218884404610307445081652240040e1030400b8070b03200040307817510750 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 243020611 1250 243019361 243019393
    0x12020c0a060b1f1407020d1211010f0c09030b090a05060c0703030c090605091306051909060f0b040e09030d0e031b0c060f0d1805030717070c03020d02040b12 69
    0x83c05049000948400d10952049984042d184080740510483e0f16102d2400340000f44208000b800b0050034148142c82c0b902c3c84542226200307821055038802041812030002203442500c0d0050309031000151844803e0000844640c0d0880e000752410003200c42101d0030380c1e030701d6190890035505d0141c042c001190101c00c0551500035249000a1440c2401800e880d01401400314000c1007060391144840540c489542221980100001d1400424041d032200131a0401d00d1040b0103805141061410a02c0c085480c5440e101e404e400c48407588012340c40e19141c03111845400c0d0300a00142002e0000300b1088040c04818010103044a050002a6585800003c0041700340040500d001e02182c115404600d400d6a030842550303c064291510140d8800710b42603444010861000d411003484a01c200210a0040c0000a02082131091420604d500521030041e09075004900c002080134580d09010f00042c2007401c0501c100da88040d10215417403120400164102c000501d01c50003680c1300c0740000010b076071 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 243021861 1250 243020611 243020629
    0x120c050604060c0606050a1a071a180714091f08030d0b040518032a0706020a140601050f0609180103060c0201060605280c060c05090f010215040312020c0a060b 70
    0x444460484034070302041102c2312911032985100c01c0b4408a00c207010312150a01d08040c03015030300090540e9281001d8541e821000c0c004080d059841004004210501084421100138800801208071550b6180c1e818200740e510422440011141440003e03a244081014141a201001d004218020440300307010864a0040c046c2c0301d000c19400d9941076100b40441110031030607060750000c000e00042c208070b8004006134a51701000c2c6c800c0c004001261540071516442040c41444181307003000306c8403501941c41ea070a00400ea40441d41d041c0f0408c50746000001071507901c43c05040c6500301c80010408611000b4242d000f55082ea07180c1904040d00355080c816034024254074109541005501c580c40625161030340ea0081c0e6002420b5580040a80104104802607901050610000d6a140401401900004199402441d00500ea22000c1d1300110303110319014041040300320030b80d03140c0d03c0440d4450352100c504c5000b540e08108168284400f4400700001500840b00032402c0b010750003d004502c1 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 243023111 1250 243021861 243021869
    0x130605090c01170f0411061e0d1506090e0403031803020c0f0402040b0304060c020a080310080106050f031b120a030c2a0e0402010302090a030311060705040f120c050604060c0606 78
    0x541d0320303010032140300c400c0045140c20075000a0760310300f4050851b01180c41d078030840580440703d62250b001001015000e400505c0b9000c01101c003441400007041030f007004903a0b10700840001c510101c0e400d002001e02e200d0680c1e80117001e4500440c00e03408041151511080c1d8000640046e0030130a100708940c288081c000c15442070036502103142030300c1d002c0c50b07032030a01018100a10740c135202e15203010454400c0180340001608000c1c016a42d003440c2004098100d1709118414280d4242500006d203031500c80600d03169420b001e8041c0010f10403d00b0918002002e05460903840380c0d1035695480b01071420801e210805120303442e900e0114844e410b00c41c42040350b25100340d6000401e4010300c0c503c5c500c040c01e48800c84002c02141926a03c42e84010303800381c01680d1000f9040780d07040d00c0c000f09155004d02c808404840d00401d413222500c1d14003048450340300d07a0160f40c80c080e4a083d42003224228401004e10441e02840c11100026203d40014070a948103911002c0090010380351281488a2846683c00034 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 243024361 1250 243023111 243023147
    0x180f0b15060703230f07060c030603020108070f02120c4606140f0f06010c0203061605040302060301080105010f08030a0816180608221703130605090c01 67
    0xc03240032001940300c0c810000014200a608503590500801c410303100c5400340c410003101926803418a0003807005030096902910300e6806c0c2401201c0300c41c01703440341400740ca406039500511641c8a030421f4880c203900180c403008612130302e94052010001c2c40060310341c0c07800c240003604a8003852011035400c11580000521065091440e89842e000071521741c1080b8a6420f8a5001c240081d0810384010010780c0c0229508140102c00c000624900003505031140950349443c00e40c1c1d8540d10300450701c6140e12000250168402e00118580b8450013850407880350072071a1885c645501d030303030100e0116082a030010301d0741d03910340700144000f6802c2d0048101a1103018001e40c1021800100104211000b90840400c40300d601007583c0b43e03511520382400c441c40000823840e42c07503a42d040028080b04040b201111400420100b02d02051100040070341200c1d000305800c801400c41c40d400014642c4050712081203600e00482040000e401409050310a10003907010300340c1f43e6403c000161122400c40c00549031 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 243025611 1250 243024361 243024391
    0xe09010503071203090b031f15140d0b040e0a0605011d011505090d050718020c031e07050d0309050c040c050315030c0a0b031f15080a180f0b 62
    0x662800070302d8604841c082d030349081c2030b00c0242c1401e0300c60b0a49a089100294800802c11108001001c000c060340d841280003504841e40d611002450084a8000080022160200440c600070a20084c00c1080c0d003c10000030020002c2001904860f00156410201d40000b400c02c402d000c102d1041707600406004525020701d00005681560f040414003403101c010b80e030b120101000f40e1091094850700718000e40729030807100c0b05062a80d80d54100b44103150071a080c959504212915034001c0c0c48448007000015400e151001c43c4100601a150a999400400520000c1e000c554100b04a4041e56203a440010b00ba142c90b04100d030034002c507030000d10700850405090891099201003101d034840d0440c01110840301003603000a091040ca2800c203580000c0000001c03030041c1e8410000c5020390034002080107028520b2030700440302d06180c45009400720054102c0002e960140304103d038003030a0303507200007895150940300e500745290079032064403071003150301d80070040002c146040340c0c01174280300c400c2c54 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 243026861 1250 243025611 243025619
    0x90c030c0306070503040c05090108010f0c0212160501140f070f0f05030f090a120f0801080a0b0c071502072018010b090307030b070f02070603150902090d060515010e0901 75
    0x1076602d90103480e03007081000000002c0e0602a80004001c003822004040c004956035034420180640568008000054034203420044c0240c000120030450304445212039040c99420258031555234150042680ca80d52101c2c040c004001100020512602840c1c41540340d41c2003404004118010900780c10050040082d0b0140e0b81ca60006d05581e8008903812540120b40c2d5052101030030051004402807590a14107101e070710894104810400300304099842c070040c1da07079036002169940b00610740542441080d0003c160600d207401e005000d010301445106102484004220007282e2121900352000300040c07403c58100c064100c004800301e8400c49000d4065940f105001000c51018420281d90010010b900c0e01c1949081c0a540025900314010603140e01d4014405448515840c0521006010755000858030601900c104030a038200389440c1c00d11a800e0042046c020f43c042000c1561000f098a201e41c0041c1542c0540c510800c0c18040300a91981d040002621503209404018031034050000180 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 243028111 1250 243026861 243026863
    0x150c090918010216060e2806050c0c0d0e27070809010b09040b070f020703030806011b020616060515010215060a050306040c081203060916050d020a08090c030c03 71
    0x390800030041c116207600346a00a4180280305000315103503101112100c5805008407981300c006074048180030740d100c1d84609a410580034070944000c2d41d12000d80c0c40082c001c41c10a5025940c0b1990940140c0d10708120f82084614003809454840001490380c14062214200200d1504818410008000c3d00c040810741040000c50018076034010400302100068020209400030340c02c1800c045c2000c40142001e08054008502c04c0b9040d102152001c4010710001d0310000d22001100d030180c0e1140c00d140c69144c01140e001c40d0100c0c0503a0141082c2e0300101c05aa1240c0c02040202c44118010007610340d01c0c03410200351034000b001819150200c01c0c218400f030344c001c900d07408080c2030701103c05825076030040007a110760004d4000907014401c0c80c0400c000c00100980b01d4060784c15603000c0b11600c1301c40d198110010320081714010381000c801404640c545042240b690311100c901c1c1446410502203203c80c0c030032604000b1050b0002403e080a1002400c1705203c4005098403d401030700e9070300501004a = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 243029361 1250 243028111 243028129
    0x30a3e1b040b010210090809060403060e01060b071203090503090a080c032a012006010e070206060409020a170a0501020c07050a09060e2805040602072001300e150c09 73
    0x1201c8043d20b0b00c89103020804034600300e540c1c0e441c0027403450380c40b01c0d26820079500802e40007240110381e6290000c0801c0000201007900c2c80f40c0da00081d504843d00e882c11046002d00601c2904540910050180601d55030740ca13503011000e040024000d000501016003050710b0540420708030104130f02c030064076102c52040c2d0100940c0100003801e000708541d031680010303000200191001109406024000315922403580360803401100e02d035003145c7d01503c4036000c0000700d404000d0025406101c1c400104440307a01c520110f698841c20400f5145000b240d92a2036007a603000d0150129070f600801ca0600180c500544984054401c056040005500b800804151540c0c0501a50041c507041c06070f803103804004120000078800035440031320190402d8904813019412892046600030f102001c0b070b00c03002070b01514000d4041016501e00213162491849031941a0b81c002552500780107454504102011901410040c15024002080c25204060b00c1e203c060401a018494004040288158666650440e = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 243030611 1250 243029361 243029383
    0x50d030507262703011104030309140f040902041d0606211209030f01020d0c030f020306030a3504030215030c0a03020a110109061508030a3e1b040b0102 67
    0x605003c514860455814240915030003640c19800c0918200d83c884140b07000c1d004680c400d446064525890715440c0c600414024000d0307411880039084801a842d213a00011101c81c000303480007608248065503100441400c060340f03030342e0350b10543c2807105a04000c489000c50440d01d801690244242c40541e03511070102454644000c100820f4a001595090204000a036205d030003c55407800c480f06030340060310305071040c000400d14003490030701802000c1c02100e2088100a0217000098410394036109a04685464040b54540442c80442c0782d0842c0c001c0e9012080718402d00545440c6980b040211003000c1c8148182240030070b2040c801208800416548400200d04002d62581000b2408031000c0c04a6001c850003982056042001d2100c1d0350310403555100214544076034607132555260b582d640701341c01c0da07400062071940990502170301c00c03400301072106030b102001c11901407a8808420303812541c1d5010700d065005440903900ca4100e68a441c0c00d0248196810301c040c1030480d001035102c1e040009 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 243031861 1250 243030611 243030637
    0x304052707030501051c0332040803090f040e07060807020a1713050603130602160204060303260114010f1119170306060304020d0606050d03050726 65
    0x6003000344054410314005640004602040c5a0725100768010054079081c071466006801c0c441802c0410030740c4200b004241c50b015205c0e0858600c81c8500121a6020581c0000740c10034107104220350906001d000f0001400348d94011a21041c848040090180450400354440c1d4a400c02113030705000081110300459000b41801c099a58510340300b80e0818100000041c16208403841401008039500c020b000001c064001d0b189a40340c945c82407000c94403040d40c03540313412414164400c00088580c0c0082021242c4031220003100c0304181c0c0071034203032201750f041180401d41680c0152a000c1e0001a0030014152541c1e900070107500d000301d49170500c03860880e04e5041000100701c440026014100840c10b110400702207606951100718400001d460111003289d00628031030243e07940d110341e24183c0303000b03a00090815103140c49075030800400c00929101103840b1901c0308000141c40d0f8a2030714110205009882d615900c00c40c0707150954110030300c1e000c05412080c0b030941200303d048040e02900e2031070400038 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 243033111 1250 243031861 243031879
    0xf061d04050a1a01082e020901020712080702090a0207080a08041b0b0306010215090606060c0f0304120b0a0c200f0a0602071106030c12040305222105030405 69
    0xc144941003076010007001e45032191460f94801d207003140c1210301c0e040351007a600f90b55180c1c00714020820a00d074000203410010301010400700009070942c1c014580e401d01401115006540d40d5140e44483e01d404030240e440c081c2c04902e4a087d4248030920603800042d01c42e0840c5010b00344e59980c907440c05000282020002c803403000900300900c031445406618203000480034210380e00d40103c0d1190b0710468996005003e00751342040c0740350a11402034040c1c6100805860382e982d41c0300c01c1c859142c00c81c030304060b56449100f4009808030010310050015068801c40316001e500c050510324200030f0f018040008203881e100c000ca017850392016410443c060a44041c0c01e503644618107041c601600d0410b011481d00541a14400b008610b41c01840407511800300301c0380302940d01042000038041101c0810040f03c00b00078a12540c040306200356030040c401d05104d030601c0e07007540c2280200007084200351240d11007954240b00c007041c1142c4142a40d011410018124100c42d40c03a152240074520940e80034900751 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 243034361 1250 243033111 243033113
    0xa080d0f09050a02010e0307051c0503130b0c013218030d0b09010806190903090b0f07030201050604061202040908090306160305010509040c061d130605040f061d04 72
    0x40d401050340c0c1210880c05000340d4181d82001c68940c60b101004a010555513110039400d414040344000458100510303694884006014450340c468032840100c420340410481c506103054020803a02c043e1400641594a8030a914810f0307003110303038020602c04000c0f1600246406200074040c0c08513201c00c10740c03016065440e2540c10400300794401c28680e400c0c2c0400324031103402d28100d500c000a04041140c8804141c3d0b69513050341d4403200b0556507400c80c0b5207800c01c03001d046003290304030b400500e100380f602c0860284e64504002558104008001c400e880024403d028107909020301c130b030803075012a400c004680c68240303191491001158002e001d50b842d455440c05001e1058240c807441400682a1041032918013009451002803000803004289003000106050500601c05440350b0707400030100840e240ce10405070703203800070041c9140d20b0746814001c0c200d16864800901010f200705400103c1c0040c10442048251800302c800e0100e283e18001003041518a41040344540700c021200070304a903169 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 243035611 1250 243034361 243034387
    0x509041211100608100f0606141815070605092a0118032406120312090507061d12030d020a05120c0310080c0a0e15090408030601020715020a08 63
    0x4a940c1c80c0c40328a15140000600284c041518600a411403104100303110505442e14221106406401c00060390300d100704000c514103c00030711641c02610909002c1d10309034000503250383c7c402c5044112100703002c034003601000114050342d50071a40c13220140107420701d60704004810380d52404400d00741c1e44d4042d19480380d6034021035003510b02610726201c240c402a12810040f403000d120341c41a254020134040200c61001040c81054152140c0944030201c40701c960700c048400c1c945140c1c6c3d411182e0741c0c550a04000610800c0040014170385501d070b25a030181070f8207903480c0c060030183c0402e002e049070b006c8001d8004004822501c0c0b20020444c0140c4031400c2c0c1d0340c1100c5034000d2a5038020414104800d100c1500c2d0f607400554801c00d007003501c0f07420041d01e0b010520f44414061400f1078018480038418852850101c20550740702e1800420004030f01d08400028140030002d42e002e41d0290000018003005507410320244014040995400468900420000b5a5282950005450941c000c160764030f030950 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 243036861 1250 243035611 243035623
    0x905071505280314091605090c04060e06040e040f020307060e010905060310121b06090b090d050f0109060504020a061809051b0d0506030105100b0403060b03030c03041e0509041211 79
    0x1d41003104c03401c07625103130404680d51642c031004010000c031251400a200e103460781c401c904c6103a01005245c106071401500743c5440514400e0240c0c402c0c020b010101743c450101c44101d100c1da000d8807044186a15030700616062802c99080700080220140c04590b546c1d130840c4000c000c80b0020340e0201e90760b540340640810900416000441d01e90880b840500a204c461503107400d0f05c40240d0102e0407040c1d81d5000075034003a2030921600200000a2080d0442c030b140111000da821030050045e00c030325021035958503085500300341080b144a6551014402941046455030000c0e004c1400d044040c00220488048600c0c40c5206e111245030315440040c000c20382002c40140c0b0040503031446034880e844058040c01600c000c4902c0ea000758a0840040d50f2030101070a0f4004550108010900e0319041d1346a06029012220702e05409d48401c124100c1c0c2400100021700c018901400c04141903000c803150b0780301c0d2408540c0607078410f000c00701c00e00c0041850351071810300b030b0203450924a18940e040941035080c12 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 243038111 1250 243036861 243036881
    0x4020a080a05030310141f1206091d010e06180a0206030c0408010f090809010c02061b061602013b060f0a060b04081507050d09050715052803 62
    0x40141d0340d5507410802c00001450040e0280644007440030749413280103503540b48243d6010780c01182000400b65031035440c100e424250005103807116440711440b0290096407215404117440607a035018003c0c4903400059042040c2203050001e121b004100324a80740c0d01d100141861908880700654442c148030f041014030010b60340902200d13143d14045e6852002c42c0c01a1080710401d5003808211039255050b481007440c41a40700c0061414010340c0d0340110741d9020f9003803080340c02410800095422000380001ca8100300c514030002c061518042e402c4418141c00d1920040c256814403418481000c254a80514410407680c0404180c030300c00b83d5100c0c0410740d85a9030101074000c040c00e202500900b00c5200e0b01c680e10100c2c2c14048035548400550070b0348224031900714950044180389115150408099401174058903141d810841c510888600700da0042e141210030b50f000c07180408c941c417090741c44983c040304281401c81c1803040c901008998160351100071160180705a000a000314003a51282540c0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 243039361 1250 243038111 243038113
    0x30315190f030f0b01120c090e03120405011b08011406030406090f060501060e031f1107050f01020a020c0a0510030c03110a0c0b0f01060504090509120a0f080c0c0304050904020a08 79
    0x1555403401c3c00d8120030081281902d010b04008008911403411005004c0030342e5220194603041450004480c004241c101540c2e90079002c10801e40140b40c459541d85c0d0b01641c016400082c21362081c81e1901a03441d184580710003070048100040009a0f440540070054160a0f1405981ca990764036000f030050070803a0000b040c01e20a00c00000511509a1040e8160f85103030700c83d14113a20000c42059035440b00070014050943d407400d81410000c02c0b54001840f00400e4484081c204840b44c1d45950611481c107400440d41c0c0e42c0030429030213160b4100409480280140c4000300100d0612b004103100030000300c00075044c16110140900e40178032a074416601503402c1c0c86160303210510098010244c424103c0309407100e421450100e00300f45d03160f8002504880003916050b00d006e18051410000d0000103115100600601080c51410070504004126904207941d9038140c1c0c001c0c580e405024154060445030030903030280600c1100748000021182503e20481b0202d18507039a81c030025000c4c5c1080d410407401 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 243040611 1250 243039361 243039389
    0x31403090d1b080c060702060d06170a0302010f0203251701090902010e030606090105012016050112060302060d1d15091e0a030804052505010e0303031519 68
    0x600c1511031035921102004828446003a42e65007107941c0d00c484c100440d03a0300c118200884c40051034090004c2c00070041c403407404568142d45031484072883c1c400107170100d03464002640841c10542c1c20310030b400d00c0c0f0b156080218214100600c103261012001d000110807440c2440001c1d60300d23402400704406030300c0c4620841c4069038440c0c0484000d440401d1049001c1503000400007900d18011403254840d510203001d00701540c0c600001119843c0e0302d54400c5124416001c00c1c0342e4000030a12100702d0380d40301800040a0035141c40d0004001105050001004615001c0c0078001607031340d4811600d40c0305e40c80b00c0c040360742c2001144940c40040f00300c0c2e01001611441c48a820704aa46910b0123116015010a13a001607100c2c50121058482c0300c02214903c0d040242500c4c002409409041c0d00035016100320741240d90304420701026a4400c440c04959020b400c0300070029980e0003c03129550718002d40180d13045042c28040045003800101101e07100703601005d90040d1408400025000402d01e030b00c00144 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 243041861 1250 243040611 243040613
    0x6040f03031506030f06062307030c0b0a021e07170d0b131b11070501031a04151701022b02070c030f02090c07081812010608060a050a0506010504031403090d 69
    0x30062070645c90385920103040080009107580290101400c43c0d80440c0402e00c2a9503000542003e640a40c0b012420703c0450902c0c000401c041c50412846004005401070f90303070070b41502c03a0741449507082c023a40d058402040003000080074804c4c1e41d1420800083c945485402040480d0040c07d019080c0c16041500001c908034058016040760b009480e00e40035410345442e00d0f4a0445101c0d500c1180e0399220b070700c01e02c002c1055512951100008007110b048103240100103c0001341940c1001801d13181f01c1601900c24080c12000000412100e01c03075a0003103242c8070341500850701340c4065440c480080c4000c3c42d214041e00d26160115220994000c1d60340c035646490f4030b041d440829201106071300880d002030000320051803004c222465260070014030340c1045c1c004d151040100000c421859000000c0d81c0c42c13503c0c00301003400b601d009404c213640503011a00e4603000610407940002c2c01301e56a2800d10090046690b0010102e9040d683c00c145061041c0e0540500310b851485802d00c119006120020404 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 243043111 1250 243041861 243041867
    0x6050601021903020709050c070c12020a09020f072a06032432091306110f090f040603020a0513061a04060e010c080904150302030102043506040f03031506 68
    0xf8186ca014401c100419120200000071900505400600380d40000400740080d02000040041d00c600c01000a8281911246040c043c0c0c0c10109240702c02c080c1c00310300d55040100003000740c1c8000088801c41000300f661881d40080100070b0f481120245544e90364500d04031412079056450603060031004810590b03440c800e00240d01081011905100100141440001611499841d41e4800280340c0c030300d15210ba401705440032a01c04800c40701503503030711b42c8100d090002e0006468500180d4104c2622401c4100a000b5010440000144a01e103440405c0c0f0050b80c0d200b8559040e940c043d500c0042c0300c0356090990300140302c240c003da500458a0400500d03150304c041c00030400c0d5900340d034032000c9000a002c015108102c44010007043d0140500000619042c02e61200990501104400750102e503a500840c1c2243e109400c0700c145001ca44c1078001500350742d040d0b80b214004010f001c150260074900581612114080c00c0105100466031642090500c81c0c0c0198405c18040c1a104510595410f03000e = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 243044361 1250 243043111 243043123
    0x3090b0904061a13060503091506060c010f051603020909070c03051b01090213021c050601031401151e020312070915090303030c050406020307020f0102012007020307050901050d0605060102190302 86
    0x2113044c02800d10020030b03c0c520940607240941111002081c0381d0424a82c484000780c00201029003154050002c40c803045803d0203501c100750007588002440342000c0c0d41c03281c0c0301000c08605070181070040000c43c2e1181c4400742420b5000384036141c140c210100f2494100d500d8800c030341801c2030f81040c4240800d00c01030103510040e9018800c5035040341c00c2c0240040e62061b0702600781c0b454000d040200c50042d01a81d0340d0000d0754001014580001d0002140e401421412400c0c5c001c40302c900c0740712200c1070402d50005400042e1000b189108a814071407908025568402c0c0c10054070201d0f80080412205405111a2000f0b0404e4181090840c0c4481c00d0060501c5014441170b40000e003484400f185150003001168203a4000c0e07401740d850701680e6001d100c00050709546060456680303a440a000b0480c08480300380d524040940c142c1d40b1116030040500d4150960042442401c0d210010861030b030700d07400005d203404e6110902049959800006038145000444000d00c7c10041000c40346c205a40400c40e = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 243045611 1250 243044361 243044377
    0x20604030506101a030601030e0c0301060605030105030709180f06060e04050c0103050a0501060212030c040f17010c0f050d050415060b0c19030f0507050106050a0f180903090b0904061a 81
    0x3d01d141c1c02d6030b038611070030908400e0703441d042002020000305100c0d52098000b0840c2064100494040300191804030782161565444a4000b500200040c0800d240c1070101c0c1004041b000f50601440340c0120210f00042c141040051001e108515100201305081e04000c0050018510018280c9040d0800a4807080c1a10f06540003c0c50400010314141c03161050760b041e2202c40d070080070b4560050400b5a0280d1003e0126400550240710024001e0800719880d4054148400103200a600050350142500e2140c0707180402e0200398100f000707075681c0c002c1c15690300c102004c0c2c01183c181c61b14180103403581440c000c5101400d06101c400301d050700030907009004c8104007070112103100e10071204507a0844000307071000b0300090020310b0442e8020300c28409801c40754051800001c610780d0700c900054080c0b03031562140104501d0f20000300030042500c08124a40e10051509000e401e6441d50001c04511480c082c1e45241c1c0030104801c80107455a40c08030001e88400016040030070100740081d8190303040104 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 243046861 1250 243045611 243045631
    0x23040624090e070516080c070503070b0a05030703090212010f0b010909050114010e1c11120105090c04180615050f0a0e150d0b0708090f0a020d0f03020307020604030506 74
    0x35021080c0e12070810002100c4010070050a241c440b00c1048510381c1c00380030500c041c0003444601c580440c0342c0d00024103e00341d410005084640c0751106040c01e011482c0c3c031915003401c0a104a184064011040b00d03030222503850b00091074401c0744005400c000f0740001c41d0b01c10790300c2c012001c9403154140e8030004d5441c2013600d620418503a5680000240c03007003401882018241c500d030992702075010702d4500c081d0002c0141203104290030502d0b8580915000442910304d46410100c011140c2800414074012000344802401341d4908020050350314518075410030700803959080351158829540d503248212950011041c042e01f1030b42d65928221404900400c0c0c0300782c1c8041824600385c9040f00c1d000040310140044814a590f60003a8141c039107c40d03031151a001a0100e8090340020001826980b040c4500d0700c488101d401c18058043c0360080000d204003041d4401c18103032000d0395401d100207841030392060700383c800b03040c251604900b18040c0c03100003904588041004006c109001c1070581c1702d03864583d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 243048111 1250 243046861 243046919
    0x1201090501051e10050403080f07060b0103022703030415050304060b1804030302070611030a0911030f0a170405030a1a0601020105041502132105010b0306010b04230406 74
    0x3410403602d000000000308100b0b82943c045400c0b41050650280e034920701c1e082c0030381080e0b682c3d2513003409503001003541d01d0041400607002040200a210f66400340c60286000c5060032003085542101c4484a0310242002400075405a00c9a404004a03800360a000c0501c1040c41e80414018166070415101198100e04002483c1094101601108101e1843d50041c10241e11203440035002503000e95425169540c80c2c40c13011010f00300b041d0003180a000c00100009080200b801c02d601e1820001c40413074407a403c41802541c5081c00025078074802500079103030b42544500d4101040151203180c2c0541c1d05070103a0400e920074026030114840d08600302207212007850f55141c1c0124200c4e80c00300d4000381500200380070f22001c81d440b41d0103089280c0041407140e0301d103a150358490581240c21000100c596445880c0b40007080400e0050001e09181900241090f50514802130440c1c0a14011805600c804001a11031046c2c2c1145910544901a0003084510303101c40e80901450007051148080c04000 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 243049361 1250 243048111 243048119
    0xf030409090308090a050c010503150405070918050105130e0106080703050607022b0e0f04090819050403020d080a090e0a20070c05060c070b0c070501080c1207030b0d05031201090501 80
    0x1081c4000c840350303c06c005c2d29000744680c2c015102e0b504064a0649081c01b611100101d0742c989200b034034094080c0391685c43ca420320f00341c1482c05046440c1d0900000d03900701001040503032a08480c4842d441f405410106054880200c120300403c4954000d840074452482c1c000144400850b646005c3d203074550a40300110b0700d60395040700d260a80440d82908480c200c1c9054080c0d81f09808411a25030010402d41d04115400f00180544070300160652703142200041c0c454008041000c0c1074a105801e041c1035040c5807450300001c00300b0449a10281c06c4110002d0200b100610034102003000e80780e46003003603280c0e0400f22189401410011240c000d40e11500c03410012680c491800c0c4c4640540c00b1103106080c81c1880c0c1886400c0d000801c40c51003501c01c1d00b030701003918003022010780a20309008008104c02454403000405004028200c2034800404000240792003246001c00390303200301c450401044950b04400401c2d644504000060281d00002c10010303001c11552015504031010741c1e006102c9030341c903 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 243050611 1250 243049361 243049363
    0x3060106020a0201081008100e070f0501020601050603061207080a0c0e0f27100f0b0603070c060b01021504030e04050f01050102100513120512010902180f030f03040909030809 77
    0x3801a00090392146015000661190141c103611014004600000d0356680581c180307040c1048500b00103054542c2616405001c040003440d0003008040380010303d075031914002135120b900c18000c1e50f001e0000000041d40c203841d04001d0102f450211401c89034103903a40d003031103600e58080309000c840031040004005005a107091840d4001c02e00c0c880c01d5031258940107440d80c002c0c1c0c081000d02d4294111650001c610b464240301403100403002c82c001041c08448031220034101c4814000d4240301c0d04042c000c3c060403640c0691291050356000703a0001340059014010303840d2807042e085100d14030091408010070141d01ca0850701c103140080d0307400d001d1900c81ca8284d0303a05400c01d020b110700580c40a0001c011607c0e0136008142c0201140781e0b142d0840301075403100a10303008041e04860105000151161000503c5030a981c0100309140045091a00380080c0c040403d20155090384a00c0184c00c0f07010042c0d6050115280c030311040170841e40c1e0f546e52082a070024004901003903020a00000000d054950 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 243051861 1250 243050611 243050623
    0x9090a0b090a080306210f070e0109060812180901060306080d0305010803180a0806040b0423031206010e130606030b030c0a170f0d021c18030308280b0f03 68
    0x3d48144001d04556544003440100702191045080c420300c0904800d0b0b40810601800511075800005400c0c807c1c105001d8803a85501a88411102403824004011082c0d010401d0303a1070140c103103510b41e507680e074001e03c82c40d2075160762141c2c50340000c030040001a0a50542e00c401c04550300d01d001d0305e02e4200d104000b0703002c8410034820710310150010085406c401c0d00b0740b080070312880b2009042c030400300c6e2504076451030300001b180d0488400c4020f03420700c014441e40000e4129a00e00c1004107803466003040c900507449000781c0031003c022042110104269038000c0c403141003603c0024000f11108103101d046000a06414811200424500301031200903003404608070309132000140441100341d161142c000e1003401e4410222500d4041c0c0c842607078150000703104051075481c05034010b001819034155007104842c0010000018403032845000c010302994880c9440440c2d4041c103003504c2d1655052200c114088650744a8007040d1101400295001c40a07131003c034492005071006a98144840145a0340324 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 243053111 1250 243051861 243051863
    0x3020406081c030e1002040305012a0f0f03021b01150909020d0f03050c06070207060215061e130903020a060b0a0302031c0c020604080a12090b0d051509090a0b090a 72
    0x3610681c11002c1c014002d800044142c4540c0c0101d40c02c03030800c10301e1582282c00580080300c850351221880d0600840320502c1e01017121800d044080704178990a00500700f0000c00c04243c00303120f0000000e44601e802981640c003045140b80081785d02c031412122041c024582200b205400000e51140401c02200f188105180c81d0350140480c1040c150780d482d411048000540120104502000003880c842814400d0601582c0310350001c201903400c2003406401c01b9000c40554001403910410001d4a80d203685540c01503e441c03480d03a000c0d500105002c05c0c040748000260030111b03800c0c05d0061080550008128201601403581007184482003c108940d07013846100c0a58144e0000400e070b0010b41d06842c020114100a05000403c50002c0d03002c282c00350410303070007901290450413140702480342a100c4050100601e00d080c2d00b6440c00c01c0c45603401401400030b030310512a41c0c1c40004482c1c00078441440c0c40e1078070040103107205160194510740c0c1e40348195070480e54111500046a145640001c10101c41 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 243054361 1250 243053111 243053143
    0xa110a02030a050904110403030804050607050306280b04170c030f0a0b190f0203010504050f04030504090903020a020604080c1203040b0304170d0507020607020c0315070e060d0e03040302040608 85
    0x485658582100c0300c3e0408040131703620584c2c0700703424142003010400034030081d40710341c648030f0072031070300341405d03420b1010003840c50050140c1001000440c0c1d07103080c1c000c00c0b0200002d00c05217181e007036407110100502035904002d0000100041c0480c040307070800c40c542c8620781c8101c01c031000000000241500c4000032102c3c2d6003554000011980058952405541e200d82d280410020040c0303108d22100c19506410350801400d07a0010042c01141044d00410b0750081d061204d0041900742541c00524921881c0f1074013111560302e044550815209006840d18240c0042c0800e40b11511450540d88034181030344034600c5002e28940c0300040071070200c00d841c100c925000c40c90741503540c0c0e51110b525414108003400381054080001e00506201e80c1704a5000380f49541c0100558079000e04040d2400110261b41c501c658840c1e030140085a60380040d25038401c6451901d0400e00c4c9106000c00c81c18061000c0380100d00c1e080c500c01c0b500661000000c2c10407280200d8003032102664840c1a2500d88201450b91801 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 243055611 1250 243054361 243054367
    0xf0f011a01030c02030d0c0f12090b1602070b070501150819061122031104020909160e0d061407170612030d0f0f060f0f030b090a0210080a110a0203 65
    0xc00c1d07000364003040b10318849005480c81c100700000b0780300849070790030103100100b4255140e0044003a8410101e603d00300100760700300061201c5841d07000070500003c1c0b9400d02076081c0440308601d203200384111402000142412515000355260440c040c0c5801c442a403940c41c034100000a6100001404000445204650121001c041c0c1c50b104082e11003840c00b418074a00801040008124200310074070b40e02914440c0401082c21468441140408020320911403401446005801d903100d616030740d040164652a249040480b4105503820f120500d0115445514030480805120040d00700346000c1c0c3c0041c0407a04a681d856005968103141c40301c1202008003003400045039400c00e00d121010760703071402088a09203240000c6620945010042e914592078941e07a0803090b013401401100702a05240700500740321402c0800407588103180c1e2102038445607960000c074014510501c02104010f401425a42c15580bc2000207071549506480940026180c01c40c8441c20340c00c040183ca0310481c640d07010718a = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 243056861 1250 243055611 243055661
    0x150605150d061703070303050603010605010905120111040803070b010501080c090915030105150405160c02011d03060c03180c21010e2e02030408040902180a080f0f01 73
    0x84507080341d01200005a5a0800407030701c5103c41e60201c24100880c03008640d182c400c0d18004090310800362109000e681401010300503680c10000803c1502d6090301c02408520003a020301c1d02400c080c840c01082c1d804000b40c089101a008001014403c1c051a00e0f10402d9a889004495115045980c404408414000b0b0121442c04107502c0e07812a03c00100c0011480480002030708588041c0c84040300c84c030f4062100103090030640142036000c040e10740f54407032a0b40c0c00e9902411344032800500a0400002000c42c006d9100407102650404001a0031500a481c208ac00f800240d44183c8020010218039400450740f0b010028a07800b41440145c40500080c10400d42800240c14400007044036540340e108440c142c00003009001080e601c41c2d40020007500005041c2a1060010b5000134081c900420400000c1964034085408546205500590ba4484409001d4000c0310111341c03541c0c001030f003400015802500046c070600c010b100750b041d502e2802045840600300d8002d1a00cc4e079010410101c00c0e1 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 243058111 1250 243056861 243056899
    0x90c090c03011206020c011b02010f1d0601030314160308041104051308030601020f1603020108010509071b02011101020a0309020a080c1c021c0305191d0d080c1603150605 75
    0x186c21090200080f0f231130f402020031100f24520309550300005039510145054000c5c040d004407030320301d00018102c04d18407a40e003c01030340320041400080c081c04441101491445000400c440d1080c51483c030040ca40e608915000384049010303141501c003a1484081441c461030688180d40c01011240009000a035259449162603003005140905601813200102000542403051000421080110030040e50961001400908040e0403050181502c0c1e0b0411500c143c1000d141010012149071001100300507100490340b901c1d17040400342140d4000b20750146d004d501a0018420503100311503951350303203444000e41c540c0d9185410b5a80c1c2d00c40071031281451001c00380c1040400460024209241207941c600f001264001510011000100d0024030324a0b07115212842c4c00c502002c41c9004046e0b022582101f0f80094034460307980b44100d2040611b841008504800c031048801608191801c1034a01640c540800407988030540d0040041303644400003a540c1d00c2020203a0300014100000010b000b4042 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 243059361 1250 243058111 243058117
    0x501061d090a020d090c0954050f010c1412270604031103070b070e01030f051305100c0c1b2103021b060f0a020102040905090c090c0301120602 63
    0x4615490703802c100780841c0d11300da401391101481c080c000b506026440c00e044441140c900c102c0c0115409036012503103107041c01c010b0030f4203140c80040003030f03c2290034181d506008071b051410100701400409032111081010204016008011880007000f031a281c070300e0152070039094902100c00440040215503c140343c2e100c81c09400c0101d2344203403152113040c0080030018070070708500c013403190344107600308820958007003214a044e010000c05182001c456035282140050050b0008003440780ba081c000c00d03264072aa02c403a00c2ca5043d10400d201a0500260b1403103030081c03003d81610359020b00c5100601c21015030107603240c02d44143e27803010b606e80c40649865420921001142c105aa000f040c0010015005100407c3d1100340b4074031104030004500d03020f4540801c5035240f107001c0e070500041c0320b8981d40f01c030706651900048100f0303030340c1d6221a2502240203119982082d98076034501014480d81190001e1a00c036031707800a607035025a94851070f1001816000900c284081c0030381c0000014002540d680107 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 243060611 1250 243059361 243059371
    0xc03190b060d2d1208061903020a0b033310020a050c090601050d0e011e0c02060f0c040314030304020406060512160c06051503060106090e131110080702010501061d09 73
    0x908407109680c0384200e803a1166081c2d400202d8105c02d06c9094035202445c0d4004407c141950b10704145164045050341940d84180c1545900c00320001700051a0610300914103e01074004090b5400041080a0b14007581c1ea1b019000e00403400410380901e00000f4414109508800140b1000b6200e80401c01c41a00003080541004414031404d4102c034a41d016180031018800004200f800e80c0c411b0382c26440c100c1e0410000c3e81c9050482c5607425540105241c0d800031401d84642d015030b40e5003c051501e80c895a8801050400d042e08200500080031010b113001d41e1080f6401d1109a031b450070121110701a4500c05501d03080c1e080089050b07070001d1990b6020711003650401d15002d40d10340e154001102c0b0122001c490407034107121002918601884101e016005e54144002c8460500c4407001a000000341001000703c003c2515400740601c07007903030b0701c0c0003c4002c10105032445484401000721006032070602c0036608000c004074059014031054141d20420310108080d00720301d44104101003d001d02 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 243061861 1250 243060611 243060683
    0x4020102030f0d02040602210304121103210604020a0219020301060e010605090a06030510031106040e090a140d08070c060f1a190302010e0907020c03190b060d 70
    0x2c585041030008040d02e052200715000603210741c43d00c0006800c081c40710f01d812041a800a80d82184a5001e809607a00660059070003510514a1002695554854603110b92540b20101f0074801c8112080302c010452424503e94040729181c41040c4802d074041c0c03140c090007603040180140b00101c864501c55814134001000424410b50300c51043c1740f0f0040a804c0000040c000244010079030520f03015030030082074685810400d0746014607140883d03400c0b41c0001803c07a0011140d40c82d80b0303503c1e003094401501c0251040b035072034144407100f2a0b459200640c00c07107980d08454038103045603070003040200c03881c0c0d460346036504199201c000071a411080200120360260369000c0701d00080806110300c80b440c403006401c8031040b0381d0010070050100e200740002d91219040100038801071340c2c8010044005101039940603c90307217074400c05a04090104100603090301c1068603004003900c980f500c699665000350384c0300d019600c0b00014084044580000a07215901509610403001c0c41c4400c603100b03030343d5016 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 243063111 1250 243061861 243061867
    0x209070e100804020315040305040504020d1b0305041e052112010305030903120309191703040602031510020c010e010314190b060c071e170601150309020d0b0402010203 74
    0xc8009011000300008040001e4909010403085040801c40032420300d5841080e490300303152a44d0014a14031490040a001e1500810020000b000315000710003014401c1e0000c2c01c50700e0051000400400003102d082d202d440c03424058070b01000280103048811900031000d4aa03085e510700d0b00101000304c40301541c008003000c200300010301c0d03525203034603020b94030400c080c5a03204100410140780cc44607045e2000489010803d2002009000900e113481d401d0801041218610343d080502041d4a0603001407000e120002c100800c0202c0c5034025441040300e0500e0307551078000c420070f100005192098603030150340320201c4052590f01500d40230744c1b460030516002c207100b00c4200208500c2c010940d24200d154500c291071401803542c031700841d01000403e44509060201906030169100128811b001118001d020300c54082c000d6070503100090611780018683c5d00ca142d15000c1c0d5100824807800c14100016035a200d51325119028410800d9002840d1031085a82600d800c486e20201500c1281548410 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 243064361 1250 243063111 243063137
    0xc0c0503010e0c09100f171c030506040c03020403050604020d06020f0a02100b010212040e1905070509131118060d0c090e01150f0f0e0301020c0718020c0a020907 71
    0x90081501011801c400f4124a4106609010010300c003d071059480408040c400e12075030161144541c1102d6006130001c0408210700b500905008134942800d4142281302d22803190f0350b4041d001103010f050191810040d003005034904030124066800001c250380c0217803000c10f02500d0106076602080340136000044c500b00048210b0202980300c2d4080f9000340e0001e001d40c001d552818030400b091300e9000c3c0003405011105500074100c0d0304c914040c0c1c045220041010582554507070076509101c0c16695810004c50401590242c00c503040606900c1c810054800c403003043c50418024007114039a10483c150904444000d601040d0b59084107068011074207000080d01e84403e801443c0301040251104080300d420201112407003141600100904c000c05a030384207015178000118003214002d4581502c011681a0003155002d840140c9158150300200d18a010300b10702191200c1200c00305010b510130964459100c4003640140c00200e29690020030080016052907420564000124a4492808801 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 243065611 1250 243064361 243064363
    0xa0f1e0c02010e090f06220903051b0f07060c02010e18090d020a02090403030b010c210f21090201050d090b040606060216050f13020301090203090613120c0c0503 71
    0x211851440000c003410224000d55030030040e0281510020340c0c50a075a8502801840301194000e042d01c0e001b1303e108034480b429000e026040b01c1d070780059a08284000c031800c0c20020107a0308007610712542482000c0c6c40c415280c100150312150300f5030142c05030440d145488025118050200c100768188600005500c4455484d403c00201c42c2c1d000c0415806d0354103142c11428584080d2003000415544110340101c0940e0382c00200c154026458940401da040c6c0500048506240703510004100381c2c3c3c600c0c61114146140c01e1000030100983e51340036403450700e0b1401161f07055030801e9650500c01c0449045030801006811031196240103040c454605518050754400b16049400c05031000e010b603c00344420007441c0e010704002460749100910180c03490404047d070f104403610909220b2003c200c0080d00f16101c0e800085e00c00c4003a040d00f15101c0da9a0025800603600032503030940c80d40135107000075090000e031030102d151490308121403000701c031103500040d540b0300030360002170702c80404003180061a030750 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 243066861 1250 243065611 243065657
    0x207030308092103180706020304051c0203031204020102010b0103110d0507090e07230702061603120c170105100518010210021c0606080105030a060f0f0213030c06030603080a0f 78
    0x40f082d00f01e40c0c074a400c04840c0d0350301d01c07216480620b541045504121645e400400d43d425110110384903403d482d144110303613080782011400290580404261103200494200520303200c0e6000f82c00910000702c02c84011030440d0300c602c101d514215000d001c1d40c4250001035100d140c1c003600c10b080c8040c1d010781310303140342540c1c01303017112482c00041d0701d260301e05800343c5c1d9201c41001d9031f448201b240d07003004200d0740050b00b140685041400d14070084072249050501c522401c1c140110048010001d0b5031043c400100940200c8100d400000d00c1d10f00001514180807102c103034200e50341d0750344d10704140d120882900111400300c5400d0440c1f0601900010345940303440207000800280f660400307003031301521099055460550001050000b81001000b00c1d0710b02141811526600500000303211180da8400d034004d01684c0010f0744040e2020803c010000301d9016044283c03400b6403040070071180e503904110152845400000c0c50440b0030700c00408030f40c5c0628150801d450709402c08102d80c00d803611540ca032542c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 243068111 1250 243066861 243066913
    0x70912141606140301050a06050d0b060d020403050c030703051c09030c0f060201051003020f0f030a06020c06010305060109020a050405010e03030c01050420030705061e0403081201091b020703030809 87
    0x301c9034801004030580084500305a070441c070b841541550726080014810b400e00d8410707002402000144100501c07010740c0320100c001c0c0010007441c3c42d03e421640e035a000307401a010403a036520400000300e5481ca000603181040b02d902c0310003414a00001c1100c0da0703245142e11480c100f44200400040300180c60902c010000e802d0408500d105185099030080c01c0d510040c007410b00018803c1130520141e1075604100c4045d24080d1f4050101035004400b1a24082d04144081c5c141391004c43c00d0241e02c070001c908203040302d000d10111500b60740c0741c140380001c070301c282c1034203a0200b03504200410180d40a28605880300600030283c80c240101200c0960a503081168200c4403002c0380b1031091314400403884001c0503d4404d6000b480c1c55400d00c0302007001031158140c01c91030140d08120110038141c00394115401380d50301c03132141c0d602c13255464030905480d0030a005545006081140c0b12000c0690420140c00d00c0100354003c0c10081d140da10280c4520340046d0100e0924040c4102d10070100b980041014070030 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 243069361 1250 243068111 243068143
    0x4020f13060c03120c0207091a0301020705070305010507082e030807050706080106020d02150919050c010905010302030402090a1a0402040e04020906030307080f0d0b1e01090b0307091214 82
    0x2c810300e480c0040000300c008240a550600c2c20903904903c0340d0000d040301c2610701c04075001031038105603004c01d070042ca41c1f1111254150300010700da00401c000485c281c0d088900c00c000038409a110078a0079901d8210455243e08000e0038021030700d00380550365144d2403107000580c104008244d00d0340c6411080d41e01100381a00d00e80d100134410442560301c1880305005001501c0640309815100c04001d450303184ae0281c0d040b105c000d090108111601c11b0100c0800b1a0131140d1780d0442c41410300d00252550b4101408030b000c03580c4000c0000d1154004c0c001ca03446030741c1c01000c0012503540c030000344c4014080044c2944c03444000070480c44054442d88010805005072070248035103440c02e0700c10080c2c5000001d182502a800601c10000002c241006690300522050b550a898242c0c000d40b02004008050039103a0280300210100880040130001c0c98059200382d03200d000040c2c45082c2400c0d64402581ca180c00900c0e400d804000313030000c40e00403800c010311950003486680d8032042d120703107001d0114505e1001 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 243070611 1250 243069361 243069377
    0x50d060b16050c0f061b0f06041406010e1e0712020f090a080c060313031817011802010206060103090c090212070206070809210d0501090605040e010204080c04020f1306 74
    0x140b00007000380703601d2041c0c112955441c42c14040d01043c0c0c507008509000011485600c41444040414411519119041c40032142c8a24042c10500c2c1400344041410186024075400804e5110042a405c1c4c854040e02450030b900000d0000c501011003001040203007005004000ea006910303207400101000d0f0020422240c80300ca1500030841c00c505a54001081a84000d101043e00c0d20b48500303076070740b0542d0085180001c0d03506e818280e50304044001c1c1c0d050759007450100400e440001c60201010894803e008001010100c80000954082a000070340507034803074000030f070f0a507201e50400d03036017240305a8407a01042c1e554000030007a0b801124040b209900403604015505c1e80c104030aa6200003146000c403190700b01080c841e0b403500c91000003840181d9860034031001020f0740e1011140b080e42d04004c104031940e910039082d4000c00d01802030301c1c0700f10705141126151980c14000e44003a2100d46020b050f440d0b20344001c12000790b000208401921000380456441018550b8603503000700425202d040e5 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 243071861 1250 243070611 243070613
    0x2070308030c0c0f0304061d0d0f150e0601140d020d0b060f0d080301030201080c040f1a160303051602010603050c0f0301060b0a121b02060a050c1911070f08030703050d060b16 77
    0x100c0f9000c14020502044104104c0f0a0560303110302c03034486502c1e00074001c815103070068189418461803032141b80742c2f007504020b03401c980d15000146041c100c0d100005681c040d640384904200808001c540007952000c108410348000c15032542e0304941241000b0300b58020407803400003140c034507101c0305000d07103085030080010019541c200e414070b644600f0101f001c41c80d0038101255101084200c1c002c44013440c04016001e09098900c08c02ca0fa483c0900b400c2940001d0581d00d4014050107007280c43c90303416210151485902d50050180f0f0003926404005000a10010428800c61076060300e0041c0d4150740360310380040e0301b4840ca801000842441c1e40d96004211440e041c0d04151050a2944101115080103551600394081080c03600020003920200741903c0c0e1002c074802900840d07269004000822804c805010f40044e0901c445c0030410042e120465680c07407414022180501c0b07007400300c0d0002c02807030000902c90001811220318250700010141d4032080d21034001e40100003807001402c0c081f0200c40c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 243073111 1250 243071861 243071867
    0xa15050f0103020d030f05120a0507030b03030a050a0305041127070c0b01090203060a090c02030403140d09030f0f05030a0309140a080d110712031401080d02070308030c0c0f030406 79
    0x55002910003031040003549140d0200d102084091409010800403800b0f5031001407003501291064241c0a070754101d5030a1502d8501d000704026034003072010030f1418085030301d035040200030b80740c1240554603114281000d0000540203480010809c070707101d0701c009002c000030b40d882c91800040210b40704040d890a80c16982002c000c0b42e13006e0040c1e821302c00054010000200015a00c0b0b06403412480056165100c100200e84901c525030000d404250621140d80b80d415400000340044900482500104055449180d9100c0702d482948800003041290103102040e441009440ba0741d104805051200c2c6080e1074076425500503a10a0300083d444131a240d0034804e1200740716546c1e030709000141000c04003503a1907000501c518101da003c12a00c504d0303485811450f141c1510b0348103401100c015802040408014000d11596024600350b1807520000b0840340d50002d801000051103800030309405055407261610354000411080f0305041c1045201004c180500c10345c03001d228070380002d61703c550500b6005 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 243074361 1250 243073111 243073121
    0x2030702060f01030507061419121107020603010302090c1626030f0105120106090609090606080a050604060b0622051e01230c2a150910110a15 63
    0x10800e200b0418018800300724081b07900001c0342c0300703810a6024840d001c81c600c00a4010b1041c0004540c400104a412040d0000d01c0607070395441340702c4100400d0740040b5541c00c640c0944103019402130400e1006000500342218600c2c0c120b0341003a0380c01d084c2540c0c500c8181d0761300d02c4110b003101c82c01035045150a00c800f100c0c00200001d035004010908528054111100f6041d0501c50688125518000b03203403108003e6001c02d002e403244c54018401681c0310310400020741540790084030325928106001409a2010500b010510340c004068a03094499844682c09080c0f9030b00c142d46c1c00641081030f40c110f800d61200001c0c400e1060a030301a2220b103810100322504e05402c50040d00443c28070707652003039070b1390214070b550a04501d0300342901d142540c0c8201413041c1c0034589036819584602091420210b031004640c402040402c40e414a002c0814010b2000007200b520201488040c00c1c000d12450385840000c00d04072030402e182500381c0910b06142180341074944101514030440d00c4102441458840c060 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 243075611 1250 243074361 243074371
    0xb0310060306090e0a0605101805011728020f04060e150301150501080c0705150a0c0309030c030302030402030a02130c02060f0f07081504110d0e0c0a090f09080a030203070206 77
    0x30000395494858003603e5105c0074030010030720360b51380300014190494002d0300c002130043c182928014442000304100105401c2c00b85c6d81d403039440d8813180343c0c10340c000052003156007064041032140311003084625407002d204400f0880c1c0c0a5070340350103101583c9440c0329000007416800f409418905148442c0c035001013001501d80e01a03414043c000c001e0204140f649800c989080c41c1002a5641d403c20062040c018a200140b04d802010725440c524803d0034002401707003d5080041017280030308001a401c40b004814000c01181d511400f07400032034000d5010307561184c00a01604c640686560029842c0c03850b4010a0801a030380d80fa03090b04641e03040080e19840000c944180302d0509100850b04808000200f8101c2007140d6007001407254489103a101d01c41100151003884158160400c030400c82d0001c1152008080ca0004500f020a4000071414002070001e06540415402c2030f10041c0942020301d017000c68142c56500c59000180c2c04002803070900c582d660b005840b4140160024101007000c0c1c4 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 243076861 1250 243075611 243075629
    0xb0901090e150621061e0d024510170102070506010605180a0503060411060c0d1205071b031413030c0906050a062a080304030f03180f0b0a060b0310060306 68
    0x11183c505404640c1c01da0a00203800c44416204034221710014094403e0724184056890084060007660362014040902e40e01480d21050400f2209c8810072450a004071403803130581c80030031000c100790b01140801c908202002c40015240c451a5240c0351300c0e100083c2c0c404400102d00040b01810181020f4440c24001750031034400110a140100107907550705d0140000e0000c15030040d01a220755a402c048500c1c812510042d030389500d89030200503040e6011000d0180c5900c3c24030b80051000c40c41a40014021244450203090500554504480ea01030b0b00900042c11401003200c584448012000140114400c2c0c4200e06041d0500205000b518804e504c101c2c09400d400f00c041c0702c80c0d5004440b50f03c0103112140140c00e211141c407903072020b41c482c0b18009086c8a0b00001070009143d482646e5407400d01c01620141b20341026100d03e90b9500320b056001409031480d130f02040340021414045290030940b50000410180d845d10408140c0d5401a506030040225180d02001215054040e000003040130074 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 243078111 1250 243076861 243076879
    0x91a0307090b0901050907031b05090906010905031f200c0c040b03030301060503040809060a020607090806010f0b0c01110c030a03050601080c04150c060c030603020a0b0901090e15062106 82
    0xb001189000c03006001c0c2522031008000000e1600b4400d030b03c03071a082640d641d03401d106041c0d00784c030291090b48a05001401448101c1c00900c0c02d5000f003100008551002e4010312001c60300030f41608502080075460900caa40300c44240d078405513180d038080300c2c1e455078a00d0780e50388402104c002d514180701c01c0162809903003000c108100566011085c0e1781100d0190800070303501d903205d242400d001e00c51121600c0c4d00500110350781c04010b50014072039124007082d403112142551140e040ca5561f0009110324502166660014080326446002800300c128a0740004101003800443d10340c0320340c00400d401c0105500c0410441c924a505005141d0486000e01301000181410410b0008603c128052410420f1512160325101403040d2130b2500140c1e0011000c20055000f150020040c116130302c0180d1160f4060003010074030003542c038112502c03401c05031200e00744507190850003842d12800030180c0010b0343d5082202c0700035440da58014034001c10300c082031020b00000b00c00500b185440160003540511500 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 243079361 1250 243078111 243078131
    0xc0b090f071e0e04080c03030a0506042a030e0f060114010206160206010303030c020c030d0504080f060c07060c180b03181603021e04140105030c0d030c030c0c091a030709 75
    0x14021003426924030700f41100710741d540e40c20040628810400c194081e03100000801222a02643c00240036440c1210284a14400080c20802c002030001e800e10300310401d100c0108045003c2d42c0f082c00701c3d0749420155103502a501013080e007003034000d91160100503840160f0310f5084d030f814005643d20a800383d005041d8441510402552161705020013400d0580e511120000300c2d000b000860f00c0100b008088515030700f044080103103240c020748503004d142e114054040303207031076004912135101d800d04000c4075081101940b20400509074102480c0305108146001035040e031124442d9101900740d0348042e86c0d036810021145520742503164003805164202c0300c0c1c400f0503455140b541d1003c5030b80440e80070050401e080c0568420030354511002d03034494030b0301658640d072a01082225040f22002c500380c1d08a0911202400310038a81043c0041c000740317000c101a000203004887d00f81c00e031406a10b0701000d05403a696002c0440304842d0340b602080e090900b4200d564a8100300b0b03030003c0c000c04d8000340802501 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 243080611 1250 243079361 243079409
    0x20d0c0b0105210d020d020f01140c03060a05090928050a06091103101a06030c0301090e0a020d063603050306060712051201090b130504030c0b090f07 66
    0x6010340d501c26080c020043c1d4000d601e0300c295140040282054400c2e210800001964a07550a00410003600442e044012546810310031181c908008280d0324000c1da030fa038001c05407560310091285500201a500100b50341e140c00301c565205006002c001c03e4800308101c250400c180c40d00d1643c803210028032400304000b800105140300c82c070358003d00c04203082e4060700d00b42088585c0c900c046905403186420b82060740c0501c1c0c224180707480340080501c200b105040f05000041c4401c484010414200700010411201e03d544903078043c01000041d00e81f400350540c005188010414400c2e0340b6503440742c1061954024652820003440c1e030021001c0b003160001401d10900d5080a0380241c14480302100046031a00e80000715400341d42c1c031a64800521032000b0000e4500e4010300c4144001814600012031102d00303074481c50070414402011001c60380c41c0348181c00041c3c80004c0c0110704100703000320024005000304800e20f01034030f05a00a0061844240e640e0341ca803214a600140c04a40400c040e5011401 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 243081861 1250 243080611 243080633
    0x309030206070c032a0915031704080304030602040e0a0c1d0a0b0a0206010e0106080402010c120315030606090c0c0803040f0c0308030c090109170601090b01030b0d080a020d0c 77
    0x140c1034862640b104240d0409550004040e4000783c600039510707900780392841d250b00ca4401500301801d0000d4180b038490b507050085400b03098a40d040310384010000d10210710390410480c00595815039503850036032901c0f102420f64100f5030041b50001e40100701130095811408007150310682c9044100b0003032400300c10040414202c0740204900e81e03511801001c86440d58048600070b0401903440f15a01d141114000b952100c09104a540e0000c41e1070004c503102d8400c0e981540500e40503940d500d81154644c0b034108641850130700060a1669030000038031690046d80342c4600a6000e6100050300703d20f4074055030151410950540104503854484000251280c0183da4105800c41076120440b601d82ca0044000f001c55000545901c00210800c580e101d803880007009214020307030340c13203400c6030382c482081c4c6808003481d903064202d41145c00140100e1245034032550002c50145400300c0d0740948a804102c0000c003102c41961405030015103000010f0301040110005191450a149200419190001080 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 243083111 1250 243081861 243081863
    0x80f210306010c0605060312040e0412080c09061c1b09060903020a09090309050d050102070201020d091d06041808030f150618010201020d02040e1902030907051c051f05090703030903 80
    0x2035a1740c1e0105442e174404000d6114000441003100741c0e510740700c000c030b0785900b1821502220381c06109507030380880314802d84d08180145038a00c0c03441d0508114030200501c0b90004c1c44d10741f00a02c901100c2005843c1240100003164020301d07a2201c60031181c40005200b030500d0381146040c01403d00d01000180c54222050701201c8490b04001160030a82ca001c48030454180c0c0712540c00310028145a00340501940203280e5030f4403d030200c40d1410541c0740107550b82100b900c21012030706810100e031a0002d0000d80c440750302000040001404091941500028a07100c41043d80e00b01c1000c02002040d01c00e134031950703400c20302850380410082d4070f160000b4040e1060107040803400200c0100d20b01264004d406450420f81c1c440030030b64880d5101d585049501d4001c6852001001c0300011740180d402c000d2003180e004000ca4009000542d0a000604c034440e5809944103125921044038200415014802180d0811341c80342c3c2c2020301c1c0c41403d480400d0f10009400c5045a030000201000000e4101141c0d408903 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 243084361 1250 243083111 243083123
    0x80910090206070203060705130e010e180f0303070504030c09060803090d0f020901150f030504080426490c060b040c020c010224060f0a080f210306010c 67
    0x11030014800300d40c45010307400b4029090f114076010702200603040b001800f06481260310140300340d81e132041d810005900078407034600c540110358041410811022981401d284041003260508000c100b007543c0f441d80202c40c4440001d50104080c0204008481410024a01170300d00f40400c5092642d0151a1312a0300603180c07082c035408a90300108500d40ca07014400c00d400404240c03496075100450b000342581e075100c00c00020605403400004900a11416004a0308100418145414003013081c400040c28101100042040c81406050103002c000121807092000c48010712a400301d0322060425082c9640c480024000310760401c2e04c001c100d103085042d0412881c0404510741d040c01e280f0000c00e25440e03c250010305001c2d180c40c181e81c0000303080420403820f0f03007107c010031070031000c210071102130f10149400841098089203291601d021060f001040c01810590704650344c80300705151a0300e207040004e5030380101c0c000345180302c1c0c3d4200c14580f00d908015418030794900342c00000d0951260361401450 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 243085611 1250 243084361 243084371
    0x17190e0a240305180109060204051201090c0504020c070909050c010906110a06022a060603160e040f060e0304031121060a0504061b051e0708030106050304060b040515030d080910 78
    0x20034000000e96484030031852000b041040c080d410051f0196125001c0c903405040040c13040b8604800521407a41d1036900b24002c50100d60404003004060f500210151949104500e408100300c210340c4280b8520700d10070002002d0501d0008000342c0002807643c01901400340300e0298500c45030303010030001c4034154001001aa1501740060708480c050948000521400071070030308910700c0c900001c006000b51011008c842d101202ea8000700c071603078203c0c051000b0012a40e408580003507100b05000b06000c0c4100d0002c1802401044014a907400990050394201c4444901d1003441c144014207824010342c00c0360350302c40098441000756030764002511001440756507000050620607107912226103019200e0b5002d02142c030f0300a0003007944c4c0010210000005480f08501240540542101d0031030354807100d00790075a8a880001d40700f0340c0000704160303900e0b901d84c52000351581d103900c02c00e44902c501f050034040103400c1c00300703061420300300020301c0b410300c207043c0c0901c00b40e1500010360f213228901c54000458 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 243086861 1250 243085611 243085621
    0x15060317030919080a080124030f061e090b09130f0201020c1e01080c090f060703030204080102031603140f0c09060c0709020301061b03080417190e0a240305 69
    0x85040400c2c40001620240d0f0b0350090100500c42004001c1622195540394240c1d0701c0700054035031510030b5444070304e60040241c0e040311004d01927000581c20400002d400620702e503488810220180800c0c920401021490900780030200d054820035080d80815200c40e0101d1801c0303040c480c404840c020014045000c00e0b482d0781e046a100300b121542400018160000000000002e0b0382000b0300b80034030380d001c2100c02c800540344907c150280c89000a006180070720610049060000c0d991101390103608154003080f001c900c413682400110700440ca480c5d104a8141d04610f4004d0480e020400380c0c03407040d210042401110116100b01c0c03900511010034a61755402100001011841a08600c03243ca00890200150003111580070314100c17400341d152815403a6901030690100c0d0400c0c180100415000804100421b4942825071061484c00c4111864031440c3d40255044ca6600c080c510000780b40c40560110b5070602e0054000248188006c2d58203902c1020015280382c40d4000e4660109540e81c07000030 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 243088111 1250 243086861 243086863
    0x120402030c040c030f0e03030609010902130f0608060f0906090115020309030123090604080a0f030204030209040506040201093003020102090a0602060f0123040b06041809150603170309 81
    0x107180940103008000a1100010140203000d94410400340d8600d1301ca015010000080201c2c1d02c11400140300c1c01890703081c03a80d00f400030741103034500001c0ca2040386800320b00c080030014101c024000a4450a00b549840010030102e4003814000c9401218141d0071b001154403a035079100c0c10742d41c2c8800c03810b001071034101040345540a4002016810b40c2068040c1035100c0080c010f603a40394400d2030a0940b07950314070724001d50f00c08065070f008100d401c0800c00c120141c1e02c560398010401d0303180e2502516090f40ca40015001c40000e542c180c4c0c81e500848140005c66803c214020010610081c05003100c1461500c1040c681d603002c4070f00d07400310101ca03000e034080600c00e40c101c484554004206401090321801d00039510304003100c100d0b0500100c0b00c004a402d5400b03d00456003014030050080030051060240005030081528050304104d06010200c3c039180240408507c01801032800a8105524104408040208541304040902d084420b201181b0004200007000c507068030f03169981d4890080b11 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 243089361 1250 243088111 243088123
    0x92b030b01050d1104051302070c09090c0905070e190f030201050f090a0806040512120c0c010603050d032a080c030903090904030804110f060409110d0510080d0203070812040203 78
    0x1524106140924814400201130050400d8403802d8540c0e014061210351300d01308910070700002070400c80000c035003007144140786d411a1640703920440095418507541c0b00f04109607041642c0e0035000c04c05950360b09019051812034070354100e00c45c1150100c040d142c0058408140c610f8000a4100100060307045c0100d82514100c42079150301030013601031560748107251074942000752402c98040c0120210282840001c3c0e05540c04a101100810010f45560450310100d0f440300c500320005540750300c40040824403e0101c100212076542f004205888000c01d802d902c0440d14005811a103c290445034010b0f5020080c1070b4051316641041e171303032600d80b003861070700e103000308100d4592250701d1200700030415921030b080e0350045110f41c0300d61a0141c1c03c3c00811014480e1900d0040d040701c1d05000c10070001072141c0003042c0820300d82044a14200100c031055007500c00403a4803180401500c0810005000100803e03041c0c3e2100d4806142410170036910402d8510030015800102c1c028100070905659043c021 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 243090611 1250 243089361 243089377
    0xc020901150e031902030d0908030d0218041518200a051303050703020405010503060402010c1e02190510110d03020a050408010203040b0f0105060405011e0c0c0e092b030b0105 77
    0xc541c21301c45080913181d50814030b100200d0207402511540303042c00340902c0d08d50082c2c40305c40010f541071108600c00c100080d08000380480d42410071245490480e01c1d1445a80340004980b2490500b0900304091203020001c070480484906180082d03803841e100c1607005d10901c202030207540550311603024400301c401b0300524201b07036501f4a0394000003040110000d40b20044a20980e030502c10750b80e0307540405071a100f0442e0080d000c26050507050740080d10703000341d403507040000a008200500b40341e004595000c00c007402d107170484c3e03c07a84401c1c8120700e491508036500300110710704076070410008808030b502d0b4450004040c00303140e004515444428001c405407005030105c440215164580360800c0741c519841038608051600090001042c2d50a0003800c890030760301c040e1584000c8148107941c074510800d140ea1034800f04030390740c0302940000c1e0842c18010000c121480002885003002c1100ca1b0400c281c030545c6d4071240c50703d0115020544c01d040c109420108040c140041c05072940b00040e6610302c58868 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 243091861 1250 243090611 243090613
    0x501110c0907020304080d0f3504021f0203090f0a210213021801120e070b0d1107030c050f0601060c02060d0f0f06031a010e01170c060d0f05070c020901150e03 70
    0x603242421a2300c003160880300d007256070310144400c3d1200c00030100c00c0e051045064420034007160801c01d003411790100c1c8d034210348050800825154002d00200c900052590507600503000020401c603285449a50408130f08000c440f0b0002031460220110341c040c004000205a60001109241c150b55800c2c00d84558002e91030003d5545481503600d42ca0100700c903c14440c0401d142d41c010b0544039042d80b085940da08803040c0200082c82c2040001c40e4103802106001400a8942e0342164a41940d000a0300003a8400d4654501611a17440c11908042d00104a0145680308200402c80340d0b91002500300940d4040e100c05030fa440d04d0100b41c1000d41220880326021604101c2c1c50031200d04194440c1c400c8078045d10071065075001210540109503000e00c90300c001400d80348010320200071035081c0f5150070241603003100c14041401000c100c154003e410b4030082d00c0d6469804a0980304140142e5030322810034900181c16841c2540015074120042c007501d4a00311100b0442c1940900402c560000201c0042c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 243093111 1250 243091861 243091873
    0x50607080103050f0604080306011407021503040311030f0901030902030307320102030f180304090501060c15020a020607050c0a0c090606020705010819180605040c030b010501110c090702030408 85
    0x14080c1148500b07201c121800d210f81c145842c8243d4021440c54003681d440580300c3e1854842200442e509860300c0800b010041d010001000180c0d240d4829120a2100d034000760b4132860641000f85c00066000c40020503504200034641403502500101c0e0010301c5c0034200001c0740c4101b40003003440e47c05070000080c0048988000084500d042c4405c00e00c41410991080b541c00030043c1904d401d0b400140c80188408203007202003560384004181c01c45400c0c24079011a418591380e070682c0010390308203910103000704081050860502c001d400212020030004c030b0003546410903c0310025507582c1c4c018919003c11401203070700303c000101842807840a6420450300030040380c652030f540e0014078880c07187c0005072040c01030001c0c1e69400b0310481442030302181c4480c803994813100300c110007804aa0f0343c0802c800704442c6103074000800611032140602e000d2a881c030701c403d04501c1c00c1400804103801a605120500d4203402215900061030b0804803030545003180700d41c0300d4005c164039502664011000c1c0d4001d034 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 243094361 1250 243093111 243093121
    0x3010509010609051501080609040f0512030709090203010803120a1e0b0a080d080103061104210203012d020c07150c1a06130b0102070b041e0b03060d030c06090506 72
    0x5400c4082030f1036031800c00300f000c0c0d21481ca500004140c00303130103940420f40010014100703141040c80207a0090180d0403034005100e00303644850070304c070f410003a2540608010052200fa0350340301a0341c0c00640210350045242d0f50500d15000e03030743d0203255140e400e00000100082c0c0c1c43c0056400284018003040500c6031110100342e034070005002c0c000049070150262820002e0a2040040c0d45603000b0788030348640314540d0941d11480003034100c047d902c44108004000000d5120390602026150101c407802e24815140c03030340304050070b50701507007070340a051081e220250403512483c0a002d0340c0074929000c01a030306c000f001101da0400d006a40802401040d5110b8003540035009036031002807600c1225006a0300c54000c0b1441c000010039210142c01c840c100900046120710742d40090310300001401211a4680e544040030320310f40c000d4100c48484105400885c440f0b45a050a242c06004455405802c5160050100d211480031180103000c0100c00041041848015030100311101c1c4c05c2400c0c2d030741510301 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 243095611 1250 243094361 243094363
    0x27041103010e0601030609020a020c042901110307120e040c030501080303060f030c0d0311060c070f0209070e0901090c0e04060311010305040c0909050d080903070b04060b060c0304090b01030b060c06040f06060503010509 96
    0x2f4007009180100e040004130007004186960b032103510702e9041d100100b400070034801194044150341c0325400500c02000f0403004607401c032809030030110581d65000c01610341178003400b064841c0c240b42d007000e02d400c1100600403640c020041e0b0740d1103003090390f803035100070000800a0310308030b561a5015000326003ea44a4285035105581c4191401c01d4002c840c0e290b00c0b00d400044c19031044c80400781c0381c040d01e02003440061828901d0180c000f06246807095420a203000020082e4000380d00c1b802c00c81d55104030700c0049075003128048003894800c4078200101c034910703200c01e500c0305002501c0f00d04159481c00003400300909001c50002504208204008501951816680c6c800c81c03150100c01182c80140061401071002048581e503e500c16601d000903240c65440d030025081c0d0181681d0f00032000d208410345c140f8100003420042400b8500407502003d01c0c00050102c58000c1c1119001e2802001040410907002400c2034200d039002d00c1003a02042541401c1d80144102e070080c50307041d400c09062042101c0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 243096861 1250 243095611 243095623
    0x90213050301230105060313021309111507021003020c07060504030302071a070f15090606051008062202190c12030e070303200327041103010e0601030609020a02 71
    0x84207030020003040402500804074103201c12a04000b240a400c0180660f0808202454210b004900032001e03044c02680054004042c4040c1c140d502da0b84c0c0c00c83d4030140180c51488a0a055040d21803500d15035540c0c841070680d20031a00040c0c017500468050352030300351081d8101d40c0128044001e03600000d4131020700811990140c4400d8006101d0140081400481c615450b013203c0800c40c07005183c08171650310045035405407e0140c0300c0c50f07c6c44100e6800610790340500e601c5141b00c3c5500103080c504160800a9056501403a882000a00030400c10543c94903031444020f140024104840fa908225022010f40b08070440f50020464100c0908038040d0001c2d04c4809040c451420170b00140c4150504808503403040c11b00c4a42c540c41401e0400c00700c0d0080c01000d19940c000c0d103840c0641c2080401243c555841417000322107030410665040001c004a4141d0181d021080300d0a001040600f0345c1030301c0b2030106001e0980c10316048c10110380c1ca03a000703512680080c007070703980d0564a4221111001c0c1d1150 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 243098111 1250 243096861 243096869
    0x50105040f1b120609030309060c09080f06160c060912051801020c2b06060f030506090111030417090d050d030b0102030c0d0807140d02043318090213 66
    0x100340180d064804400b0b00200c00b05481d0500a58600c003601a26080054420031000b90203242c1c0d15800340340850710900170240128416140c8454040c541070f541b9280205030284000682c01190a106c07200d00d000c0541c80060090707242c00503d4004030308003200104504007004110340c0451400102d010b410401405c140d00403128618400c880190040e40c54000e034100e01070740035032544020003480041c5200709200d8407880b101e251001000f60b440d0f104446003600a54030302c807440c0d50100104101004865480321480d0000c0c00100080d840d41b41c80740c0800351000744801150100700034240c03094025141c00c940c1c002d000403032480e110f00340184c849400c0c0001d0400207080c520004c07203550000007110540d40c80200200140c1140210842d107490b0080d04140030071903141c0704a8000000c40c00684001072495000581e078615000a240082801e01d10303100310055196401c540341340c0303003034124201c1c03030028107000400b03140d010150311116515400074201b00c0c0c80410710b4041813010b000960b040d6 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 243099361 1250 243098111 243098123
    0x5010e030a051203060a0e01030b16020f120f090909030c010513082506021b06090a0302030f090d020a06180f030b040b0403110a030e0f0103060e130501110f03150907020a110a03050105040f 83
    0x100d0007290bc1240c451101c801003800c5544610240c0501c520040003d14264a10500c40c40c1000da002e00041d803103500c1035400c21069070010420b026240000e100307071904003c0f00710b20009050303041d5461072300f1800360701d85caa460807194103039602002031102400202c856100c2c0c03045603a844e616804941c00420100300446910600e40041c24001c0001443c03404590150015414000d5aa0b8110107a5000250454020310f05104e03100044e00c402640401824098a401e149040d841e10340d110b0051581d1701c814010342d84070b40c0800c0881c03140c3d9070f1203401980010000c00c203035546050540e5000155851050701d4400c0400801c1855401285c980c40c04c001100c5000c0c401e500400110705881d103a00616406040700404210000841c0301502112031140780003190000c207001c50880150017500320320f980e0203000000c00005681040d180024484119030300c10050404d10070095036038850f644000d12084a03540440e410360303140e183c034400450f0f000d002400301d07140c00c0c68607481044098074100c8107 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 243100611 1250 243099361 243099391
    0x4090614070e0d02040209042a0e030a03090b160c0f03151413050a0f030f0e150301060311040503060a0606080702010e0d270b0405010e030a051203060a0e01030b 71
    0x82070701c94554a14502c200400078079510400e5002c02000350300429200781e00a60701c40e09604a00340040c1d0324114078082c44e03a0030703c3d6030160280140c80c660404055a109410900048000030780000102c0b0a0b81c400614898603110700c3c0c42011404090103001038000803e001c0005221151580341d5002eaa1040b070042a22209031040e00c400c2da20241d400c0b10030030070078000151f150a030300307003010340054041d004840c0f1508854949145c0c130134141c10180e0010304081c070f42800c2d0a40003200080b0b022410b503103404018040e82840c000354041800781d00109512480701c001028010381c1034401501c802815030380942030641c0060000c0c41180f088001007000c0d100015490b500600c15413100110b031102030034504041900407102c5202a00301801000d41000c500d06074191000b07110809449100d641c15a201d0404001401324103491000500c0fa601402c0d0f00c0c0f00046011504904500c00ca221080d16034503580b0000305855002c0d0060f84000665078000000d0143c2d45080d079020b81102140515 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 243101861 1250 243100611 243100621
    0x30c1a0c0f030409060806190c050d051009140f1f1d0403031514040f140a0b030609030c0c0f0a12050706120605031c050c070e0906010602030a0f1d04090614 69
    0x92031f03282c1110280c800d86000c55145d80b9801e041c2d0003421142c2e06c90b26201d0300e042c801c40306d000220f8100b03644000c851100c1e20401d0008006500c10152204d4081a00d40075034502100a0224424001c20f10401c0120114580c2403045164400402400c0340300c0d2504110b0302543d0a1100000007200c003038002031b091000781001101d00032060b80c2951070b0b50398000c40d0601c0a1040c00081c140c804090150349588200c0d03201e0381c60f041c2c4445405122000c001248501c811010185006005070958566810400c034000c0d80400000d42804c0c0d003003003a038580c00e80a5086001075084c90b419480320002c0141c00b07140c031080107400b052101c1074070000c0c0c403148442e03411f249195003191072074001d181c2c15070300001d90940072a20390904130704402e00c1490103505d040d960403178030b0303003001c5150384980c4000c0c20000c00e2124100003440058090605807000b58204082110010300d80c0d0072068071a41440b11024524100d011061155921120054400e0124151928141006100302640d400c40c09282e980850 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 243103111 1250 243101861 243101863
    0x4122f03132903270d08060118030b2a0409050106090303050f031308040b04080f01020c06040b040f061805010c1715120a052401030c1a0c0f0304090608 67
    0x700c0c0e4085040e00d66004940c8481e40610690f001528102040100b5420301c4e0100c200310142a040a80110150080b280c10b444050000ca41c0a001c59050090400301080c1d4a1200c0741e524003220b4005542481540b2079220904903840c00c8511003075481c2204100d032100c6880000140100c80c5000000c001980e41c034002100c4801880c00002e000440402200100e00c1d100000f6580100703259138441003408682e0f85003a1240d01035808002030313001c003050405c2040c80501112980700110002036262001c0c00c0b4040f038071030f040200001c0c4403012100c01b040038040006142e0082039408038080081501d000481040c0055011041340c01d903003420068007000e4400c600301c4400e142503505564694039840d000318103c50007101c07055001514006201050181088480c140d83e010b4405025180b040c2a400040c1840c10684640302c0e1443c10010000241100c824404031006a07180500b036044000d82c1c1b01c8107100344541da1205200b01ea485040d8214040010400c540c0329800811071a41c0d207035600f03 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 243104361 1250 243103111 243103139
    0xf0f040201021522030e0f151b16030c031112060601030c02030c0604081206150414040617060906071b060b2407110904122f0313 57
    0xa005811103052000f14000e454200ca070400020b48002103182403002d000b1901d4241c0f400c0030b50001d52454460346060a001e000c2440109060360103000d41403140c180300d08144952a080f14600e031408000f0f003042ea109120381c4480a0000580c45122540d0b401d10820740c81e840d000695108410910411041c5820410b14080c0345026020306010303500e150064008042c103819420035400b0802c01e001100c0340910400d031149215091041d140c0041d800520000ba0000340b41600901c0a2064501d0300b461050507038040301e003588403d00084a0302d4000c640502102c1d0b0140300c0140c09001400c3d084040030411500c903d49401c1116036644d01c1e8441142c001c582da12410160501c403200f14004503416400c28040e196015050020840c4000000341000e161141d05500c1101c001c5141400c000010341d01c03112685045480480900345a10745c5010702410700c0c01142802031a0050b04100300d00501c03280745911101c7d02200402101c1a8403c0e12688100d0060042040405001c1388128420100c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 243105611 1250 243104361 243104363
    0x8121e040905070306050409021c0c1502030d05060f22021303110f0103020310060c022b1a150d1104020309031c09051f0608120909060a0e0a090309030b040b0f0f04 72
    0x500405a070306404252b1f4081242c041c10780f2744500d41070b03000c00c800044c0c21084050607410303801941d039082400422001c4942c00340c00603108038000d5139559000e036680c4900c0842c001065074440400c0c04c2101280700240304030355030840e0b80400c03a50000b003849040c00107220b100000344d4100700c1d00652000110100d01c41120840d5030f00ca2116401e02c83c4a114000041245202401c4511105401107640c122144594510011036450712601c20802c400014241111055644409490b04010381080390a4103001103a074002c661020003641805418025140c8030840504215524103141e00020740304e0f40711003010150400385190001705071189128907550385410401502040e0030320020542001d10001c10703400c03607a0f101c100106510710f050240a81802c185003800c1c0d5540c4440040c010410801400d051050303a010340b080100203155130140d640440c9014000404113080c1c03070190342040c4070742c0025000349140c00401082004c0780217160300a00d40c000c0242040d0795840032010072003800b120 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 243106861 1250 243105611 243105619
    0x50414060913060b09040b090715120e03070b0408031503070503030a0c0201090911040e0a0b0a030602210c0408120301060c080306220f050c0408121e04090507030605040902 76
    0x8001846a0402c050882500303100c0e2101255031480c0c800040d0748014261802d40c2c500b00900c052112480082100b20003c1c840c50480311845440ca10380a01141030f6a80c40649941e168000c10240440a1040f500c640c1e42c080e942c41403e04003170a00204e15042195034031800c0d0411000e4406502d4009074040844000070019858008104400c440e10070340c107001281130085d41c143c0400c5800f031a009492564012100c4c844d04c032031810722103041c4000040c0001003814a0600341c001141c03a021074403015203421000c017680c2e0313500000000480a0b00703024001c038444866014804914000c6001380205c0709240201c0d01d0001e00010b480e000d520080c801c080104056103400c1e0001031560000c0d42d80031900500322a00c260308680c80300d100c1c185071a02d049100795110036015041700a4070455410118140096050500b0000155510203142d00308225404000c180d4002000080d054414200e4442507542d07151941c80c650740d00901000d40d85200824142700004c51036040c04d20038600b045800038 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 243108111 1250 243106861 243106879
    0x5012009060313081611090a0209010c0b100b121f050a18020405210f0601080d140f0705160914061207030204020c0307110307030c0e092505041406 65
    0x1001e04003107040d4544040b07a49110922038054528515481c0d0711651b80201e0340340b0b605949442c1040703034002005144a600700e1060003103290b644d9120b400744460b56030140c80010f06403600e004c80f02d60410194030280201d000003c0c5690840050034005001c1d00325031198900300c0040ea41b40024950981c06856040303031072041c0811003040f60400b43e58920389580d40c01440c154480c0007060005d9a0290f94602d8903d60301000c000d401c1081007008601400341021340419418a00d000e91200c0c018040d14081182000c051100c000110046584420084440e01d40d0707001c0d2484d107941c81d04000e041c40d907013443d070100001a4280d0640220700c94115401e18000d042d50701d0000300301256454203526842c0b842401004001a26140300034481101168002c41c4c170b804903843c00b5a5082d0422003220300075040403008000184500c12448156468807800713803081c1c1d0318442154544580c40e1003203c0e035450b80c4020a001c4003484003d88060b51001d82e420b201003482c24000204454041e00c105800186035 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 243109361 1250 243108111 243108121
    0x80303090613060e0a060501031104050705090103090c0f03030c050d021506040207060b09190606050414040e0a0506010e0411010206040f03080901110c34060e060412050120090603 79
    0x5990350b100b0b158030461000032800c40301a0400e00d00b51000f00c080304d4480c2d81d07000500a1048410507643c108104a80c00e1020780f1b01000020442d000d1451518145502e0301c58000c10800445c000101404480c140204034598a080003014100c0e2540c040c0c60301d001c0c015007040054030225140800f0200450144505d8640a00380002503201d003005552440e6184030220591799849040350141c1043c0c0d0100010b959900040400c0390300303e500c01018000c0402c800c003d4040c80c11143e103005107089800044240700001041d082031421031009109001e4503001080a40c00305080c94001c41c00b81c1703000e03010211010010399440b903040e64060708100440c8926000213200300e400340d501c600c440002007000c201c00c9440c2c5403035030085204280d00d500300b407584a0b0f0b440b8016139000d81c00703091440030700444560050001a8a16240604010050704000c141166260b8404075001841c03200070200351444a420454000c0003614004510215090403445400349030000341c9000800c01001185540c80e0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 243110611 1250 243109361 243109381
    0x305060c03060a1d07030b0103020a090308130509090d081305100f020f04060c1104230a110a020c280e06030c060f0a14030103080a0c0212010e0f070803030906 70
    0x2003081e0340c000801480490000c0342450b825008a58401c03030801c40341810170f405030550b4194119241014410b100055156501c008001e0880350091181a924001001649401119504040d421113500824040c003050000354041e5095026035504030b09445041d1108415110b9050150070713a80441402000c0c2106540031000c199200c001c01440c08244c804049072503041644414003150005084905000034203507141000d1508a9040040344516810020818650000c40c41c00941000002c0d0385407001d5841243e100040710346c01e685407004038100a43d0742c1039070445280900035032aa0702c040842c40c26000c244001034004103a1500341010a00f0084080043c0016498400c100801c0130540321040144002101c803c895540c070245848040d044849044004080c124100010008565440b0555908480e18a02001004d803a4000220b01a0701c41c043c1070036030b51030184800c080c1c3c1c1c00040c101001090761015121081d40c1c0c0c1c0321051300c0380000c4401c0e40d000e401c588000380d04918 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 243111861 1250 243110611 243110617
    0x4050c040e091615090312050a080f0c031602070503030d091202010e060a0b040b150712111b030313170c0906031b06071a0a0b1903021003090f0b1b040305060c 70
    0x41c45d26040100603a42d890302500b01501d0031201d400703d000064a088100d1b80031401981c4180030300e01c905e0322414546042c510740c1c0700040040c401c900704544103c2449100380110713001450000d00301c81d161100500b5000040070900b41c101c800d4905181c82440b42401801042000381128016206559594041001030700d000c528041c1c2c080d82d54a030064582d95000c030300032222400e900400d07441d0326040c940301a49450300551002031114442c104008094001aa0560405490702d1030728820f81c503801007031845c0100c110608804200240c0442c950b03240c100e0800e40c0344454421106241c0b8040141b2110000941c2d03402e4041e0400c80c620144035400c0031030740401c5840036180501d09200703030729403009194062410826020300e600500c01c1c1e80e0b84034050408403000807691442020142d14000c1e400a800748402070295200d603030607a003102c0c06540310030421030300040c5500b119121450f01d55440e000c22181000c2040d200040a0110034004043d1001c0d40d030320000401c440d80f28031b1070340301840d0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 243113111 1250 243111861 243111899
    0xe0606010908192603091005010f0f090906020903010203040f0c060302092107151206050a0e18070f0f0302100804020603010b070204091202010c09061809090204090204050c040e0916 80
    0x4c2e070503a840c1041910040203612461a079009412105a08040d20082c0da006078804040c00301d110000340b004e4080f03400e4110271207000c8200052141c003507141c180040d0141018032603140d4400b104000c2404035013560652542e200f044038111884d15440b06400300e008a104140e0071003070000018003140f4101c9030145180c07035144c0c00c5440301641d41c4421b500000b91584444006004404030300d41200d042d02038200034150854180a5543c14a9001b2211800003881c0c0c42c40b21001c04140c0081500038001c0d40040c100562443c0001502d5100da00300119031440100d0255800c0103400c02c9452040040c5030140368010106442c1d0f03443c1a2680350310340c0201005980c4141d40c0d0300741400007448025015248011f42e000418109100180079103269010391002c2c0a10008404c0c0450840141d20150140d079240400000c14540a0000c180149010b0ba4001c4d0030502d0041401200c01d2001c01805c01c45045850706046603031015030050711800d10300d00d01945a0036684060005600b903d038990303481 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 243114361 1250 243113111 243113153
    0x60e0c041e03020d031106060402031905130c0f030b0c030c040b03150a0306050702061311040c020f01110306030d030e060a09020d050a0b0a0b040207021f120e060601090819 76
    0x100b81ca07034001807013400816038110040342410102015044050280640c8220100c50843c210326029400582c296030000d5034201c031560360000560080780e0445ca200c40070703805c25102d41c0801d445045086d2524054001501c0c02103003000095000c90350942224440e4580825441c2003520700208103005030000380c0080c5604652443c9010241c1311204100000e43c05198041454101101c0c00fa00b08072002d4601c1042c42e00101c01d0742d01003a0100c0c10a504000c0503500007490104031001282040e181e1850540d0715400d04501004c07a0b28400d01450248408a00380e81c4400301c148000e804441000e08071040c0ca8000c100004c1820001e544025100b42c005040b03840c03143c01320340d206401c00301141130131120340c00803500303110310051103201d820607000c0140c0d411490140715400013800f10a031501030400c541101440022428498018001c144a104130103004941d4000205501c81c0e1301154105e000542905000690361400038248180c90b488070320035100380a40e51a50294500503c190382d0729 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 243115611 1250 243114361 243114419
    0xd0303091401050a090c08010506150906040b071a07050c0601030320030d05041115181f090513020f0d0c030b1507060e03070b0a0c180810060e0c04 65
    0x41d2081c010b882c4158003c4500190700b06142ca0450700101c0943c101c0c05a0b41c2c0b600c0708122568881f81c480b0010404d01c40d1101d620740c144100058824416a00440540c90b000705101c1d00300058122481002d003246140c40782c4030307911940c0403103460084910313024842d07000c07000420120b80070f1b801080007004100c1d22070140c1007201807118039507413204040e010042e9032a4204000c1c0510041001d80100c412207039203110340c80580c02ca0840f03001d8201709590541880d00c01c214a56140c0405200400c0e00c40b00640318200b0340b81016001c0c500c240705444c02554611046074000c2042d1080b1015280e403565854140700003044030300024000c00701141c00340b694844400507280d55812400c00300146040b074040c7e17282c0452400703406803030041651401e00d510600850002580203142d95500c5001c5007000640040c008104641410300902421242d81e12488041040800441c0707003010543e514805120240d502c1050441e80f800c01c6808404840d01030000717100701140750340f4603008507c2083c0c004130 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 243116861 1250 243115611 243115643
    0x1404031803080f0a031b05090609180c0307092c1803030c040501091203020316060204051509100905031b011202040902090a0e0705030402060d1508030c010e06060d030309 75
    0x102070740004401c1c0e183c140081806094030fa4940184805007001004005041c100d1400280c80e42c0104800c05114500224555070303e0307154210a80c0740c0b200c0341041111241032011440410394000d03210340c0d0018800c818042054192889404514281c24448109601504045000c0300708040c00103e110b8909131804190080100061401003050410300e0ba82c942ca0140003400010295101906002c0782450841c0425004001d40701c011003940e040e401031300d9041c07405200a1150750400c1303030f0145501c6e00484c00c82d0280c40c00f400b40180160307401d201c020b40600c0140c52620551042c81e070726900004184000516844c42d005d080c0c08181040c1c603da07407400784804140d03000340c0c00a0941e0f590101d030491152a103902250020440348040c000ca505080000a10620000b44040e01544002030007007100400303030703014030750204271000001d840320b46030b02c9003d4072584021039142c125820103030766074001d20000c5051402090001d0980848038034944c0c094000d80b01c0d1001c1500c035201c401103540 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 243118111 1250 243116861 243116873
    0x80705190302060915130605060109080102040305010c0f1706010e0102190f1101080712111908010501080a020a02060a0b1f0809150f04020123120108010f1404031803 73
    0x4403a892094002e80014a07041080602e000703035031190300300c8042c0b046050109001080200e00c502c40d8010318040340711b541e0071005075408052a444030a0b10b620005d40042448819130215280380e02999903129047c80062b82151041030703c5c41e080c0d014100c000e000c105070398081c48950030600410b00659007881c480070400351242d814200265081303400b940d5035000b000300c05101406544c0e424284a01c040c2010b0a00404014541400440d0169224000c4450642c283c0a4030400748a001041d91500c07042e207401050241e0a1141901061110020a105a00c0c500034bc680e408410b600800c183c0d684d401c01c0b10701030300d1b001403481c1d00803920700c0c40c229401f5a080c1e011200f901168a401d1032509080110600d80704000c2c1415400603402070070301c101a0b00080342c00b60042d80920348288100078220100c04088a1180c11107040e4400080001320752002107980341c1280c18140080004203211111042074416074a015a00d83c5040300c00140001d004600e004030340080440007000c09501d0340d03030302 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 243119361 1250 243118111 243118153
    0x720160b04080609060906070c03090308072006190815090106020d0206061009120c0803030a0f0b030d0207030206030408040e0112110a062f0102030a0209031b01080103080705 77
    0x810500d10006050042c08010045035402c901100024800c82c9404040e043e12000e01800031070400c100004400c05042c4101c201801035030b044481d0b02c1d900c0110f41350440c24001d0091464018000c0080c801032a481d203082030b1003311240c0742c240751900001078400c40e21420010b1a01e4000002d90680000a031241e9502501815060b0000c06100c0c1e103082010b860000c0081c5a036121328680c1d1201649950321070b03210806c85036941e00303510000c0d03094174000050801e1070300621003c0c44040300700811142d06800c41070080710108010820283d80308180354681d400c4d084000d000d80c1c800501000117007441c07001558041d008245140c201500e5241c4206007a0082e403103064068410302041c4140030300320030030700c1c038030b05003221030076030b040d1404002038000c4040c0c1c8070081d003a200403e02c00c90749007081c48030101d034074007110001c40d540d2070814510b2000b504000081c90080c414035000c510a81060b104000d003105058458030010781c659924807619a12190084989000780800001d6003501e8143c0c07 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 243120611 1250 243119361 243119369
    0x1120b040f0614130204150809191b09060b0301050d0f05100f0b03010b0a03120318050610230d03090b0a0804060b01020c060f0306040b031c0e09072016 67
    0x10b003c41c241400c1001024040ba10b0303480f0000b48100001c002c042c42d80c500d00c1d4181087c03420b1070345595940126090410070f0004241141e5459038100c0d204101e040001a403c04140441d95075039a80c80e0445402200d01078010119441c0c42000113010914000725604040d61064100d6100e0b011030341e0350242000f002e0840081d85a8a80c60f2002c026941405002c2a82d40141d00030400c18410000190303098007a884080c011000240f0490502880ba401c070b406011300300e14a108510788a4a00350b0b80d1120212148882c0c1900d40b100400c102d89981b200031031080000d50000041071281d41000304203600d00c0c1049051045251000601d510b21602400c01c06041e43c0b03498402d440d0506100d0240c2c1c001c11246411500100b440e00c0f55940e03050156104801e00404c455100d40d80c2c0400304000702040581d46a02d807184160001c400483e003040d12a461816039284903902c894881803043c3c0c404150b1300c040208400c03100c40c02c0c0f0441079036000490180700303c00b1100a11004400c0c00801481900 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 243121861 1250 243120611 243120629
    0xb060c15010f0b07030f0e01050c030a0903050f06061f05190203090f04060b070602090a050a080604052505190b0a12050c04060c0b092d06090c01120b040f06 69
    0x3004000804099480800404031143c0d007a20341075056a005000441c1114640280001402440b515920032020751b40245860000c0360342e902c15290028010045a220440b1103104440a11841131000304055001c7c040260030144d802e000a01e20080c15844101000c04000f0700f80861b91402a0a207102100e0f0120754019503651a1214140540c600b50581c00d030f80258105a01044420012003c03111050b402c0000180c54820342c0b000680e00750090b50149a01c10700418001c00c1200005c658680118480d20455452600c400385060410101e0552454454141c80d030410003410004001544402c8400340500f00076110505603000f0f80001401c0c0c000940c0f405900b4080341840d11450340c0000c2c0070381030f00303060626140c00241102c8442c54014802c18824010841c240000c0014010751074100e00d01810403083c84698031101070040380c03121164402c0d4400709a01020100d418840c601069460042c02c66500955001409001d1403441d0841e0352602036514000c1d81d403040740c001e450064 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 243123111 1250 243121861 243121903
    0xc0115030c030b06091611030903030a08011e03020f01080415111308120304020f0a120f061d1002030717190b010f0f1209061a0306010b07020d02040b060c 68
    0x3c03c0284070248010b1810740686503402c1071105541e0b42103407206298080745440c2655000310002103003940107020f250f035090310020800c1c1c03500700d8002c14002d06a405901d24024860441c0f1440340c41c5c41050721001e03411840d40c2a03240c3c525407146032410b0344a40110981c0c401d010f01e1440c204200d8498a009800c1c0c58004118a1400d10b0381c0700c1c0c4403006000c404020310600a00803209101c520015000a110b6050610390181079100c2803004801000091140c104407801030a02050034811040203c03401031904542800110300d580416030094195001040c41000845504009504c00351546013400a039041100302040a9105540700343c0e000c60074200b244401c4500001550340301580701c2c2c140402e50f0301c0259020f40c0240799060242103880c029410b184c90503208802420801c4000d030006062007280c55032150285850012084c00780c088a000c0d0380e88802150b058045c449000707501112000070040540b03802c0e04040081b400007402a85012210b02400e07150507000442e5081010400d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 243124361 1250 243123111 243123113
    0x60a0b030708010501181a0304061d03040305100c1224030303021209060705070b0703110a03140a0b1c020f090709030507050a0312050a03061707030c0504021603050c0115030c03 78
    0x58a8540030341d000c1b4070000038241004542001407408020081050200c00581402800e400103142840c005004918907501450040e4807584180015038851140d81c00442c20000c1510805412415595501040481c00950318001d040d5083e422081c1caa100f1202442111200940d0780096101e902e005903039050070101501c0402006000b1001a007000f0200304800360060f088079880382c0d2190f080c030201e81e101c3c1c0c001c0d40104034540c0580c005060100701904401e4051b8489800345c00c0c00d2007146910350300c0b01ca55009407070205480d43e07000401d00c4505c2e4445c10300b410000c03860314801001106015490408a80f0b03013481129101c0c0060800380d0200207108041c40343e903010f85025200f91b1780d41402c6454209003d600d03011442c040100000d00d02a2851103540400702602521191581c2030145080c4035a40364803e00080d1200e5540d080d0001e1386181502c21254001d40c500c003002da0341d80d0252002c3c1e820b0b030420002d52100b55210705059031241020001c0e4005940f0030810440d4650035 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 243125611 1250 243124361 243124367
    0xa0c060906030b030f2e0603083112060216060504020a0e04020105070209040f021002010f06081911190803030106110c0f0405100302040906020c1c0e040203060a0b030708010501 78
    0x803d10350940241c204820b0480c1c5403802240c0c4100b8045052030801032134207000d504200107134090b4140703c0711501c3e02e00701000304010100109000103000c242c0082c040ea8512100b24045c40706440c0100040ca0240708000c40c101900030040a580940c60040c2000324440c0c03e0780c81009054011181250358404010031072500703843c018058003201159078100c0ca01070340081c0140c8100365029100300390310000141003022000c0034890b000d60142120f01038120f070460280c00703009018040b16000d400c19038081001b0400044407840342610302411a200b0b03180e0340f100031109444400a94002c4880082c41680c0c02c035400041b07005258150040d686c80d03152080040a8035585a8103a00b40d4201340841c0b034841d65518910000c428040f50009440d441e001c5500d02e143c0d2140d80000d40050902c0000c2040c0207255000d014859414025034004541d5010400c0100c1c03203906000c004902071005440b91403d00390301456010002401c40014262940e60a601e1504205c0c0d4003000070313020000602895034 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 243126861 1250 243125611 243125621
    0x52419180e04031407020d050a03110d05041a19090602010b1e0f0f040c17060a03020901090b060409020f0c0c191809140607091e05060307020a0c06090603 68
    0x491001010507050621001546a002d40068100714084600581845a441c02c586a55a0007040351382e03644020310344151690020398041c0d01060707000d40f152310703490004103410002122590710035103054145403003400a418040004102c4070020b0203800b0008200c09004c2d40018216107c0c00002d52400400034296900958014043c030905400c0011350020f00c004030b03a8a1404440d03003610420760102085c0c810908441c1d40da4058201000a290780790804000075000c294140304520661700c0c20280514031001e4032000b504042c0100040219140c585d10141c07050300001c1c14589021340e190100700580c5c00006552070581800500b6502d424000c01c8207100004080d500020015202084064045854803403401441c10f47e03801350310070070315960121181592240c0e0281107105031210307075640c41c0740c2215840e000c50101580800c4864060084070480c0d44004112403a603414039041c0001c07a04050420307420f51003071000b0340d03001691080f00c1001420f603594900c1410742c606180213050311 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 243128111 1250 243126861 243126887
    0x8120a020405010f0f02010e03130314010c020307080318100609051321020102070204060803191d1c020901030605060f1203040b03061207030309031203020c07052419 73
    0x2a104000400035030b60002854510003c882c20041c0781170301c114105a01416441c240b001484c00005042d5580c071040003103900a5078003807034007540c100c1e135511561403c903800a4114405a030092100c85c000500d0346004546c4540358803038250321b121044880c00d1502610005000302d071521200e040c481d181d0f540c451a54003409401e4080d6154541e43c0b661011542c159400c4801c00d124000380d81d50490003501207a5549501403c01c00c00c1581d240c2d102c039101c0d00310b01e088007400d06110000c070007858401d01540a0103801c01401c019034060360810030141064002c0105a2550400030b0f400141c0d44070103c00340254010300c1c0100d000e207003400800001e071440b0b0881c24802d640800c0ca200c0104800002e40341600c040500305640c03034a9820005030a0101840048a40e02c6040c81c088109540000c4000c201e07031060030318003080359650600b070381a8000c8013014212680920310801070345c076141c5000e202c0c0b00b4409050f46055111450000c04c5944800c48040e014074100a42030a0503a0100c4900310311 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 243129361 1250 243128111 243128131
    0x1804030309062a0f02030c0318040e0307031418271320060705070803040602010b3f010c020c09010605041a1c0e0a0b150a0306050a090c030812 63
    0x810a10705403c6010300c002d00e80c80070002c00000410b003950007001150301d078001c48011240c680c0c0b082c401c040e040307120440c281d60140c0d0804207803010101002060714030030b039413680b01c89801c88108441200f054004140b14100070b401c02003210f0840e00e83d0240080d0700342c80781015040c41c0710540e40c1344848a001030310b002d5003060203075070b420041071005072400079070840784101c5070440f0014000a402c50143c500c010304a8062900700141c5400b001005104682084e0000d10440d4405020001e400310801a04822401c04500403030b001540b1104c0d560348049140110b000844d64500d5290841e02055542009640801d000303c090345000500310740141040c1c60400d10f002c1c01c28040c00c101c199515031004152002003034031110034040c5520307110140c08070542088030071220500e560752800c41e2441902c0740781002c004503000e080d080358a805424070150650803211314540d164402010010001c081d400e50303a8038038030002011a1411030081d80602007013502c0312100c1d41d802d15008009419031501d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 243130611 1250 243129361 243129401
    0x91407050f0904060603050706090305100203010b071b09020f07031407020102071e0305150a0e07030308160c020d0302010b010807030b030606060c0f0d090602070602070f090b180403030906 83
    0x19941c0d01c0301149520005480340750356600c0703902d480d0700508115000281035010352070000c070b0b40320f44c80340d1100b084034054002c40d82ca0740c20b00203201d41248000c1c000e0f00c880d01e4040003828085100400c40f20b854070714402030601034a603038520980807030300041c40723030007902100050100034141e1040041c69422284201c00f0700e000380c03030350001c1d559030064401c00346510441400358400c2d000501e4a070b4019904001074845038011164905d15032981180c1200441d0b203000e40000c650480001d6080640303a05450b0510f03940c0ba0300900c2d00010b050140d0a000b040850020400107071580e04003940302074483c0e000404c141d140a000541110780090031001014640803130341550b03035000203110340c00250a90750a80d80d82440b081860030811501d00241b405d00c50380f401c60348501d034052043c00c00c1703a030301c1e030b00f0b460010780c886500f02d880d0440c500c1258000f8650b2041440781d00e029911200c2001c8009005200c032101c8c424a95011709006c840540c0403075070320790700b807418452140600c0c064080d180c0c0d0f81c518 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 243131861 1250 243130611 243130619
    0x604050604120f0f060b1e03071e030606090203010e0f0c0f0706090206160b0c040605041a310f05010f1227060e070503190201050d02040306091407 65
    0xd03805244600039001c010700c03204100b07029440b8a02d1007010f4008001040700310090401d0405881c0040c141340c05018901e19841c0070b03142c15580c03251360420050161400900d0001141300c075030b4014068200004510341c0010014030140b151307100624028101584a6140c0115110b621400408a4044034111020019000c1204040b1912030150000d9903849844900300b441c002d050205000390030040018071130782c81900e44a184404103210f00000c0c900ba58402d0120312003070245105550208109020038054400302d0a00b810049404c1070703480782000c038440d111801c41d4114060050907036200c0010301e040305103201d030640f003d44000d9980004a505d402c0000306000c1c444850401004041606002c80c2c040c540c100c10242291111200c140180c059080510301c04556811200d0741e240480312558804003240100803604010081c21050112a01a0f461142c4480c012410454100600c1850799420700c09003005d540101c0000429407103900d0580c06004000b6a500031641c00220100 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 243133111 1250 243131861 243131869
    0x5300c1e0319050f04170a0b090d090e0405030d110406080c0403020a050409020a0906090212060306010609060f030e010c0815041e09050c10032408030a11100920060405 74
    0xc00254943c075001307594503020300e50345100340115044241e1142d41400c0d01441400c001440c00e00c0c040c060481c00e076940c1c4030b10008969805d040780c500800305090400070403407400369180480c0d0050180b020741c0e107840c421802c0350048a0104512a910040202d821312200b40d00202c05940029030441c198030340750540d00081c41c13500302442840c0c400c0d9200d5540c1011516401e0800000b40003195003800f01c507171200d4042019412591544017040c0c00e40c030000b0841d00c2c0c0014124121825511a0b100c840e0802c54111011410070400708140340d117480300d141e0003010034410062070403103550300d0307508500b030001900059100c031487c6603104500349001c04a014100300c48501c100450020b000903980700528255091440130849a68042984040b841605401d60000f00c1001e8603404882c1c2203803090350603d910040540148c08043d4030a1080120f814040c825058002807130000322240c440c107401c9c190080e190701610031075a88582d0403a120401c035450754a4113402c8000ca0b0b820b03041906204c045 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 243134361 1250 243133111 243133147
    0x150712081015030e01140915040206040b0703051b060f0c03090c040203060102071805010501092702090409060c0903051e2505060706020c060609010305300c1e03 71
    0x1500000d9007141d048642e980a42e000210307074030302c200082c44884d001c0c090a4a9592003201c550b16503029040c00c0344900101004031910441e4010003142c240f40c2032441701d0348290072403a011800c0c048104101400000b803055050007010034500149035500d40212600188403028040b50060081070041c01941d140200d0309050442c0c0c1941c00580380e54406e40100d24101460b8840017060032000d80d070700590030680d00558180d0b0803c1c0c84065041d60303180d082045122112200e120fa24921441810000040750018004410001d10118214481e51034090441c3c45c5141c9030404200ca0070803c00030004180500c03441c01e018252007000c0343c1914448282c40c0c02407498030407021400701d0380b104002c15906101302c02a02028040d181c80d0442894074200075840800d054266120f031100007a414541420441c1c162640701c0040d010001647c0207401d03c0348401030407400c0c04c2c4250310100714100d01c48000b03030003540b02220040c50310140750b400d4900300c0c0c1880c00700307560345400402030072862403011803070 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 243135611 1250 243134361 243134369
    0xf0609020a170c09043206090a0201050708090d020405010b03040b0601050c0c090c070803012310050901120f0c12050a0b0a050108070909020a12050f011a0705010b1507120810 77
    0x40007045988030711b4003110758211059060146080c00050600d0700d44074018021032011030700304888883e2213200c041070790351111400007800144100980c00c00980c80e0000741840d4003002d010b00d001c0400d0b60713000400b500d90980000140510100801c0240300e030807004a0703048002800c00915113000303140c1c1c264031504407460041c0503003810004602d40720910422114055041030950340c69503100c40246010354621465a03601c5040034803200c070b66141c01c01000b00e070401941ca40e01c0c0b42c114031200550301d9845c0d000d0203104d01d565641041c4800e02d100d009040c4480242c0d514140e4084401c15400b0803920003a0824021703900d40b15004441d41c451a0071001070741c0e02401c01e4221907031004c408036035882a175084544014000300c3c0c203000c600d40280000f4266800c0f141e0a100940e00d136070720306c40f1404003441880640001c2c1c091000000c0102c0f002494081d0242d00081411101480422821001400090080c031400100d89050003207a820046451140e80f4003520070b400c0010349940410f0590003 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 243136861 1250 243135611 243135619
    0x415060302060a0c050a021e09010803040e010e061206090c0a0902091309020d17030103170a090501030b120106141009060c032609160b0f04030b090a0f0609020a170c 73
    0x2402005d2000403c42c0213500c66000300791541d0340510070414080201d42061880c0544080310020030041d01c00300903030342030f200c441040404583c80e110344203540090203421523030440442c40740d40b00a07a2050003003e10a031000c0008200381911941804002e250340c1c3c0c4204070991051021203043d940da00344448280c44100d0010410030303000c7c0000385030b580f014000200611101c034000000b02407124040c43c1280d0043e6010040d0804454040c00c0c03030b100d40c42c5110001038110f0802e1005600030f03400ba030384441d0302800007280d00c000100c60a0844001b03420562503c91460506030403841c05001040070306545191001143d0300d0b10001920303d401d2907900030700380450200e5483c041032030400680001c910000b182005da003001c0c8040703a11a490b60340704a410382021400454802c0c004002c54881ca44134105051074a4070f9510354110b13281c000340070680107000705d0105030045041c080815440c20b00442c8006400405881007203c0c1c807500c3c0c2d00c0b01031901c00003150050943c00208000b07100100641d = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 243138111 1250 243136861 243136877
    0xe060304111014040b070c080d0804060c0305070c150e0313090f3608030c030a0c030b10030225051006080d0507060b01030b060a03150512032209020d050415060302060a 74
    0x7c13401c1d207904000c54011400b80e00c914101402c0141d80311900601890081c0c2c020015400300400880a6a030101d841e078001ca14280e8003580011002070b00400e8049900d231001446040c10059103056502880054a13002d0103040d050007110305602ca6824100d0750860100050750000314001e480c403c209001d00920840551700e81c580050782c0068040c02a4013000309580c914002c180031920313800603034441c078215107400801e8074504d009100c0c8011000c1c0041031440000c0e91900c1c06c801079400781548541001603140d81d1a83d8103800c41b5000505407095000d08504444021101c0449034113602000d8541d115941007084213800030b0403104120342002e408581c40e001c0700c0050340900248070f0b40c1600302c800050083d0390750b0340c582d00036040c000741038260a140590b500c00300800c1d17080000603540740390400c004041e446402001035a074060b103580c48a1400e182d030745d600c041c1283c001c0a041a05a80c0b0b40d410002009040050800c0d001c045c407000300109410f41e004a0030138000c404078134061110355 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 243139361 1250 243138111 243138113
    0x80405010603061823071403070806010807050306090303071202090d020904150b0609102025061b08030709050406080a0c051215070e060304111014040b07 68
    0xa40100d00610f401050600c22110700b2076400c3c0e4400080c482c192030f010800034409400c02265890301e61404042401015100d0405180509810500c21a2503044c07040140c005078140003130000c81d00a01c080b4001d0724500c0e244c4000e06007401c4000300b0411305500200300b04200340d50812041000100c1110300180c41d200c61401055000f420b40401950105003035003000200411440c00d60342c1c03910b10150a000c0040300f2400e1000a0042c0c244595000c213040380c09002d5144070b0502005181d03101071407146104492000e10b4180034480924a40300c080485807004208000c0b0745200003412a4035048414a10b2180201d95040c81f4504c01040503a000011a1100e40300d10314100240c0030040003005480e5807590015500d6103101d01c00c45070850034040024440c5411407102201240d03680180c00050481c4e1850010070703400914020500000d02c601ca107c2e5101c040c0034600c04d0303218040340c1000015260402500040041c030701c0c01040714074440c1100d0b20080c501035904a9016000c16501c898207 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 243140611 1250 243139361 243139363
    0x2070e1b04030b090a020a050a050604090b040212040f1b0e0403081b0d06030b16080f0615210609070c14010621030801050105090906060307020c120703051516080405 73
    0x41c1d0b500103044a58100c00b80043c2d00302c00304450042c64400c550221290765501d003808200c03009880f64a91042d000c1c0400c0012003400d403c80060045e0041c40180b60400030802240700f0300054030181d41511051001d00c0402c00326100d604a811b848807214002c191401c809110203001c0248004c0400400c8004601c20040304c090210441170320070101911081d03c80b0003800149520702c020b445440001002c41c030350b21203103400d034079007021140c0e5811115503402c1010005403c020f40348a0300800013035460503104150b03a0151407098407001401c00d07081d0140001e0686000003a20280c850350940c014408025003002100005c194041030303403c1e00c0381d014240180100a1980490690307112000300200d183c00c054a8201300b64403984030154182d0300c4400445a50180120050308141c1400209505251080146900c50000c0c81250321440000000c14002074921f9031010055100384805d00400a040c082c207005511039814030720306840d04000300194060160104428040c07860041824800 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 243141861 1250 243140611 243140617
    0x110708071b06050a0818191704030317090c01021b0d050303070c031205070f110c150406141c0507170108030a03050a09030f030c03020403140706080702070e1b 70
    0xa03040c0900700c940d03550009030031039104240740c0000a20301c1c0009490095039411007040c86221034010030101da101c0d0340e03420301c0f40e10008040d246000c0d05031080091031500c900400c040c61096403140101d4200303071100040103401400b442c0c40d40d04054030000c000d0744c3c00a034441d01000d2030003080c961540103101090803c0c5800001820034007000080101c020b8000702c0e400390340791103659002804581812402c0403101c00792602c070300140d111210503111a00c03502e001c0c040c1310045410740b90903030600c0000550710841d6100c0b50342610404101041940c0d0020342058050403607090f55490402c0707407150550724212902c0710901c01981d60b00421502c502c55410411002054580c040765543c44034102c950781e42103920050006411701c000100000c0490091640096040e25202c1c1c40c7c10781d1240c154064883c801f080800c2641c02d110000c0855000350844050382c03400c1c0c0250100b5410000010700400c802001c11003594040542004643d4101081031f030f0050341040318000c01c5542240b940c040388 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 243143111 1250 243141861 243141893
    0x1021308030c2e09060905210a0f0905030a06060611030a0e0d140d050d230714090607080711060906070b0604090b09150604062108041703040905010911070807 70
    0x80c130340302c2a401040f41c0ea03480719504034000c204440020347e400707120407000d00c1d591070b03441d01c000d02c244002160503014006d10074243e070403402c00c0c0b4030b40d0361614080703443d00c22079417419928907403514030800c031250b00030b1001510f515029018629000b070546002d02007210500c13580d40151340d41c00c0042d061002200c05a041c1021000544402416a100c01004c6c1e412000c08058182d2425081c580000700200d0210010301c1c000250502c25581d003081501e0440c00042c10150910041011450b199075140041c82c1843c4640302c503d4075007201c1e0401806000f140c2c0141401000100402082daa59000c03c3d51582d80d0721102040e102c0c1d6808012a020300003481000340050000d0701804504c900200703202181101c107680a1019642d00d03000c110956402c0d1280304641802c6181d070080c401a4139071460049400b50441500d426a00c18000f02110405e00701030005400c007180070722020f183d034000c3c18010000088140089002800b4034540c600c100301c001049064001080b40070446515184c100107 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 243144361 1250 243143111 243143203
    0x105061e040b210709050f040b04020a0b0f0a1101090503040e04110a030f060c0206060108160203120403030608060c0c070504020d0f050a0e010f06030f021513060201021308030c 78
    0x405800c003c40c01d80a00806050f400e00c0c015402c000c5207840701c51051034880c08050507800003d44aa0712030480b040c0b005013051341c1180e11004041020903960000302842c000a030a00c45ea00d0b110454010f00c01e0850001e03800e0a039040811900124800000b80c405548041540280c43e40303035440c000000e4541007042640024040b80000140140e19000304009806640c0500c052490000102d071100000c0390b805000c201a10702207490082000780c1e016011089004913442d02e600b81d90f110480c0304003180d04800080c5c03140c2d0306200240d001d00442d40c014440000507401c11282900c00354552556005d1640960303408180300168400e5504543c5d01d903481c0754030070015810305003021400f400c034040342044903601380301c0841c800d07080c41c2c420102240e8201340d50000d594100d50030000b0354000d401203801080802d10071030010f4144003036204014003498000507510100d003030348144641c51a03840f4105580003440b40300c00d101e9000c5070100c06440d440800b42c148042512500001c5404070304c4035122 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 243145611 1250 243144361 243144379
    0x92003280912080709140a0306050406230907030305090a05130c09060512060405040303020903060a1b03020304030509041d01090b04020f0609100c02010e1c0c080105061e040b 77
    0x1415a940c8040006409800b159051200c50301003500c1021040e40c0c8180003419500081210f603200340d80c11994801c0040c100c20086540b9110b034415170b0000d40e130903603605542e81030315005d000700380784d283c002d10307011103580d1046250040055032541c0c81840054144400010320880941d543c101d00009450010590518224014182c10041c43e11880380d0000c200d81a40100e1024024805e40716454990401041a03a4518080c030019000152040701450380900c05500da03540c0c03e1000e1441202880400545803050011100e03241d1401d003081c0f400d00d40704000303000202e075000c030499201c90002d075400b2800c0150a560040d22000302000095103501c3c00510300e0402034605c080078000c0b8000c40c6c095402c25040301c100074940c49803110041d480307851001a4807280c2e008903058400e060050600007008010303800801d514100140b403440b410507500c40d41000f0401d01c4801c0101a02022000b0041860a440401d0b03000d44610250659841c1068a00030143e845030044d0a0b9594042c000c002 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 243146861 1250 243145611 243145681
    0x605060c010c02060601020601080c010e040f0216110f010c0f05100606021605030d05040302010c0f02090406020304030f03050702120f130f050109060f08010302060c1e060907092003 80
    0x402050007501802c014054080451815032002441701e060f210410050300c0d0000c0e00c0001076441540b407000058015031205055440b4031114806000d010310800b202803016101b5141c880e1804100d11001c0b407188c1e420003440e800d0340c0da1115080541c10303845003c3e00c005030441c1c10130780c0c80c0c031903841c500d400e02d5410007501050107640460b00d0302e040b1007030491004e43c0355100d84c20941c450320a911207500252082c0070401c0990710a10320481d285005081c00d804080880c1c01081f002e1308100c03030580b07800750000107000c100755000200e89035610340307498104418108004001d48599070301e48000c00d0140301081d0320a87c07101800840d1401d1907003001042c5107a0b0342d003048600c603059500c1840c2c04aa100180001c0c680d008800b140000203c1d541d410840da03007940d0030803040c4d800c02d542400341d038071607011050074000080d00307001c00340a440c0d4001c16281c40c280741154030306465600000f21b001c0c101b44204004030302d0707260034602c40c812041e10103480356074240ca100c2003030807810b5030b1070208841000e0083d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 243148111 1250 243146861 243146863
    0x23040602180102070e07031817070309090219080a0b091014091b070809091f0522050a090b0f011d090303060d0501020405030d08010e01050d02130507030605060c 71
    0x1001c00050080d100c0022146080103a8441c1382c1449421030038824940080c40080c840c0e4010598100070060446007040c03507445401040b0120950360103131400001b0810280f64101c0c50100080450b810154502080e5120703024201090a0181052103540b0303002c030700000101d80110500190142080001346090b03011194213100ba8413800c001a1841007444110341413444410f4802c030880641081c8503030482c10b1007241940b203090180d0344840c4c01c2c856128a6900e5042081c010341000c0b09504403101b00060301c180e06920703644024420300aa500024454041c640d48081c1d080700030700000380da03680f10841003010f0036072014014000302c0d8960030801000c0250305054182c2d51880c04540d5089420031071421958400d485440d89035000f8070002d2040d15100c1d40c1c0c1102c0d03a11603000542829500c101107440c025501c030b03a00001ca01142c005022400310003001e5401400c04a410258403065600030602050580b04d61075070482d1544000b616541c081d4000c0c1006040240503940d944100300401 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 243149361 1250 243148111 243148117
    0x42301090b0c1e010c0518130c020102090405062205060f0904080a020114010e0105060714030412030201150605030c0304080910050903190804050d050f0d0908100504031223040602 79
    0x10700300c1c2044400203082036240500c50007285c0c105545a107850321700c0e82a1400301d488041c1c0701142d8416400301c10240e01b1340b00c50080c101c00304c4480e0000758481848404100c20b40383d0003040704d0b0107500e0700ea00c060384900401d030380000054030324040000e1a071124004242c985030003100f1070750041c400b17205220412610400030180c41d4400c0e4002c1261440340040d9113161907081c802c65586166280040c006440e203040105480c0d407146500c420700300d4541e40c2c2a42150440c1d480302c0305130700d00d04020000b4140c0a014201003c00c02c8202a40400d040141c050241d0001800d080820784000c80001d08101c00c160850b00e181e880100100031607040250002d046600c1020306c01c1c064051040c0a0702040701a01c1ea116000c0e50101460f0300342800e280920240c0702d00c0e18002d680603c501e8000300c1801e0f80500051045a0b20f030fa4400306003505004a00c0c2c40c1030501505200350310f10f404100070200340e00c0350a03c200880000c6021507400c482e4484000d0200d11075260822031b10411060000708425a1b000b = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 243150611 1250 243149361 243149383
    0x3080301061d0307090b041d07060908030c12210c1c1506050c160e010503070b0a0905100509210606010302040533070620042301090b0c 60
    0xb801c1d20100c030301800071102c580d2040b1000c1e0181c1c480201444280d0103900200110742c405040003645801c101b54031141d0b01c04c00c000d0008940c01040f41401429406810100900112001146020b404580740342da52081003511484100010cd41035145000e050340003404091401c1e800c2e120360514000d0740ca400c0d4415654141c007180070982075000304096001702d2000c0e501c006540c00e00703545007070420340d0f16500c15903095445009060803d0300c522074003800c06000e0480700c4010040f031360505082c90301e400c0d000e401440351070000307002e4480c01c9039100d07142c0c0095820513a2030503e8a200100c080c0d46c240a100b00f0740354000c030451101d165250402c04807103080c112050855076070b80c81d4500194224440c7d4001e4a0300701009a0071080304004560318107816082e405008116112686482d500b00d400851040302c1c0c403501e454051030001e2a00c0066506440802d94442c0b0b094a000c200c0e0322655070b09040796442c22190650701d0110f80c0102140401030140c0f49103196030340c40b0224500c1d00c1c2c65092131 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 243151861 1250 243150611 243150617
    0x30a080a05060d020607150608030f030a0b0f24040312120c08012d0b120f070305010f1205100c050702090934050d060b100216140a030206040308030106 67
    0x90454500b806103102640c0d00603017060314010b031584850b410315500004034a503664440d0000501c50400300014030a115001440300d8407400d0403010300060b5682c0b140224890f1300d110000349400e9035801098448840108011441120070406c500b0450080b075002900c4841c080740c2031154a60005a41c41a01940000070000ca1408180030741d61400c01f801b5880024040d107801c42800b00740942c1d034000070000c09600000450b9203003142d01003640080c4c003040b00009440c0512a01d900c211340e040d0b8110080d8242845150304004d4440c500011512036440c4009800a04209016051042651091a001c030601041c180345a029009a100140890007030000d4000078483e85004603190461021000f10340440c4e1804d109903400c455086e07101190601e5118030001741560318645e103605028481d45020a203c100c3d0340810503203d800350841c40139504909a6481e01d0800d1001c450165410315444c00050407103400454841001d03600000d402020025012003480002400ba50485605603 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 243153111 1250 243151861 243151871
    0x110c06160b06100e060a14040b090901090b010507080f07140304050a061e03090c1503050f09030336060408070b070c03050d1e020d090201020f0307020108130f05030a080a 75
    0x242c14007100d0b0012003500c00000e4100200e03040945404002422002c060785800b14585401d2200b1031030a0f44594403d42941c540002d20140ea41021241140100380c82d002c20410100302074006460f500c90702600412052000685100305048a0207a4081e90340242c0d2402010558100480c0e603070f80f0501507940f050031210000182c15101c1c1e44403001e404c1c0030072142c10201c2a081c105501a00f10000101d404454108001ca45021a03080f1048a420320350f9000c01d1b1414580c444d4801c80d80c02a00901180d0010010012f04c0300350407144142c0c944030518140214400b00050621049507204645000c0c0140d41c180410321200c1c1c005454081c4c0180c0088040d501c83d54800d0791102010280103000c240c0c28012505c02d05040d074856010660741c1d031104095000d180301400300320792043c0c02200c489680e546200c4155641002156401402d20000f140b0382283c80d000a04440c10003842000d501803007584079800c1200320484150341d03075404000c83c0d8650109120207018110110f40c002c1c1c2c1d01d4034103 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 243154361 1250 243153111 243153121
    0xf0302060103060f0e0c0f0102070b1603090501030c02030a110f070303200705180c0910030f0e010b011d0301022101090c09060903061812020c030c0a030b07110c06160b 74
    0xd110390f030801c0d01010006c2840314018014800e03c116801c40070342c15401100b000280c130196a6005085004085903030f1105001c4900d805400d440c41604a52704062900342c408502c560000700f00c860000880c20089400082104030b9454404125030f0710301240a6100c00100b056001b48100c1700e40d540840140c1000c1c0725640e06a0340d94601481629803180f0f164010702205540c3c0c0400a4003c544504000d1600788c0c21400f2402c4226140b012000180da1884401160409441202d102c2104400240f00d25500100000d00b550034503200c040d0110320f42c2c034851100e540e0075412148000d095040c04100482c04507071041e0141424030440c4451410f00300701d052504e10800440d01554040d071500c00002e030039038513804000c1070388610000200845080040200381c90282a0711205410350013007182c445080306250818003005601401181071880a00004101250305a4059002d10f4a102c004907500c00080c03804280d80942c3c1c0d04440e00003006591901640b40410b84680100c03409205a01e82c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 243155611 1250 243154361 243154391
    0xd050a09090504120815030616030507090b031803130e0f0903070b16172503150512070b0c0a0308060609130b0109030501020d1a0102031303060b0d0f030206010306 72
    0xc882c020708803a004503040030820f0040704000d811000c240c071b0001506030341402080c0b80c140190342c0d0703142d060543c210048c1800c0d8940103246e030000c0e03c0e25040509914005d0341c0b0000707000180c003a11095468010f01e40f08168100140c9a801c00c00c0014081146d5642e41c5d401d40e01c1009407602d6100c5400340001611802000040301c1072640d00c801c900380300350384260300d180e041d01016602d0810450315003010b10500314141c034041d0040c1201210464142000e2800c1c0c0b83e28541d8110440525041c2940c103031380d100003889510125081501c240d207102c21106c0c0c6d49810a0398a4014014070356010440d00003030500041c01c040042c2c400e484040e8152105410003041d4014484d449600c01160358003a031840e6080e40080745007a1042c10a25001c94590b80c42030b0a90b00480c040e50070a83ea5824089414442d00141c8812aa0280003451814125840070210384425000150040d0303280d00b061071a1303444016a4035030907a0848038900441c031441c82c000352200002c4c031080d40c081781802038400d44441 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 243156861 1250 243155611 243155621
    0x1a0403031b020604030509040f090b100801200f120114010207090b130905010b060c01020910111e07050d03030b030105070302030114010e0f0d05060412030204031109180d050a0909 79
    0x41c0640041500d0340c1ca0343d904a8040d40801949034215449040d100c50701c1c071040c02407090b2503101d21002e10792031070405048040780400c0d41c851049613051107200303180c003510200128514404c1d08001039071500d035400c000e200380c0f043d20340c100050b0002070000601c054140040b00062394003682a00c1c86c250340c98041005582c004050681d200c003400700c03210840c981650001d00c01d644204008100c3c00110310008425410041020080d81d4002840200701d190075541ea580d0705545040c00188000c0b1004900c3e607440c00010401e4000c00b1114130311000403070401961009010040142d5000b010390f180040c06401d12041c840c0c0650300344000709000038020300030740c2c1c1a40c60400c0c10f01c1034034204e0790045070080b002800306500110f031180d40880e00d403030707500c081030b41c6030301410042c502030030f151900010620003007481e2410144184002d100146a05400d942095000c0b03d5040164642c1245650b507805982c56400c1244070b01d008001c102508800074044e107404030344031105255901c92040d01514 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 243158111 1250 243156861 243156911
    0x2809050718170f0d120e03070317070c1203021207080613020a050f030a020702150c06010e0403022407031503080304062c07030b06010c0b061c1a040303 67
    0xc4441e034007030110a5100d0031464410b07080504403007440b03054952903030408980061240015014482d41c1e04031300307490f000e045200280040210b180c046d0646009056180410300041c070003c011002c02d001d281700d900c918190300d810030b200100b0314a0064000c1c00a41c00840f081c4006030300440020185030140120744e105e5200507140c101559011086000294401448802400000e10100514501d0007010b580300c0d054044006a841565004104400c6007c003002e01c0503140c1000440008000807070014111110300c82d10418540311490144d0400a940c507243c940080d194000c0030880e028001510b001e00581d407410070000022200401003001c4a0201602c665020004140018071590190031298480d02c03c00e104958811002c0c22444e80c9a04d40c800941e024110600512a4905505802c800309003403070602d054440e91000d100301e000a0655100701d1004580c3c0824501a50020601640c026502d4070740359074108900d140d0101c1a501500001d2602882d0780d620790000260807045 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 243159361 1250 243158111 243158147
    0x30d140402090c031f03050709181106280801050f0f03120c16080106090b12060601120e010f060e010b03010b04090e03090913060e01050c0d0b28090507 67
    0x6980e030119501411360000e018500b0000340c007001c46051020880c2c40303002462254020301201850b00c0701d0101510710402c50b1030100b40c10b0030b07040d80000d0070325215088059000e03140755842d0401c6009403000c031280f008100305142140d410074030456034481c0134141a01d900b00c1d02a0641e45a84091080024800c608260594001a11b6a81451558000c0d00d0002d8600003110341e116940300300926646115800350240c1d81d180e036000e008d0080d0501980c000c0b22001c0d10111507841c4a101220343d107034000381586060100c2d0b0b6403402e0503403889800402080048100a200c0c40420500c0500100028401d400103202c50000102e07011b0303007140c1100d04031a0f401100c14101403e0210b01c0005110020704041c01c6e12041100d61f007203465a01c02e082c401c0800781c000e07240d18121401c0c41c0c4103a0b15070340d441d22410392625041106443e40d680070781d08941010030b40014150070300c9000c175446150007a10741c1c0400d00340c032140c89601544540c01000f552408c540600403521f8000c030503070f170001c4410010740e04 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 243160611 1250 243159361 243159379
    0x9020d05091b010c050a050a050a05010b030d0f03020c070b19081b03010e10080607090e090a02031902130513021c02100f0201020712050901030e0309090f1009020c030d140402 77
    0x5150704c102c062810460186094460791707aa50f60382d00d4501801408100c482d900841d42c01c8040c42800c0c072818240c181d09401408111031002ca006181400c0903401c8070030325a002c5050403c01404200ca1009040c2e03005446076683e0215200225171661185a840058612400102c5949503106250700a0040d07000d46401c5908018020070418002800c03003c3c00d48038041c0004035908200700650007a09151110004241090110300e070102000300010707110b9211f04038000060301c0000304d2041c00c4005203881c51003c01c042c8000b42140e81c030340e48000c8141e81400c081c0410f56a1094130900000d1089441010ae00c0008074001c26691342644040d40c40380e0b126200b0040700c2e00603888030010f0030b2188001803400d2801d42c0c80704d0882c0c10320483e000c0011004510351015580502c9842e50301d405000040d0308203000c0c8400581c1318200100b20400603865400030889141a80e42040c02038041c001055440301d00361a05c040c0d89401042c00c5d2081c1c1401d00790109100d005402040c0c2c000c6401401001e0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 243161861 1250 243160611 243160663
    0x3050405030c0d111c0f0303020d05070206090d030b0102070506070636060b0607080a0309051207080904020915070f0c050d020102340303020705030610211b09020d0509 74
    0x442115071001800c21740c490540d48000f949140102106a209490042c0c50380c080303207500b50031142d00821440665004a050100b031040001308903030340b80308500d03002c0342c60750105004034140441a402030350000004214401002515049000c40c5829446042182c00301c04003151060081440034040007000d81c401d020106031030350026040610003070074403481d1084513541d41c081580421804000280c4d07a04103041000014000340c1c49140f03660020031700703112868460581c00d100b049440c5100b00d500040d030f81701984868a081640d200000405900e51150741802540c94510540c200c8005501038008240d61800c1c2800111068060707005101e05c000b8056811040d02854107848800a0b00036241007044c120400d404001d13520030b50140541c54584820b061810310060000c90002103030b92024884000c0082e00c048210525103002460880c5030b04104400d2a00510006e86403a420a4089040b0b0b00035001402c40480014080017a13903640355003a5218103042408542101098000308 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 243163111 1250 243161861 243161869
    0x30c090e041a0f06031002030601090522060f080f07060f0305150301020406110606120c0d0611031320010509060717032d1303141603050405030c0d11 66
    0x5a4024400c404030704a48182e403a018514902c2107409070480004802000b00c0b608007809207050b01d01680ea815801c500b032440001e09000f026010b1903001e640200c00c000a080e000b001a0a1060301c0d88504001c12901c54641450700400c501403050680f041c0c60407035000c0100094500b003103c62659440c9102200310408401a01c0080c01c044405108200300b2110b90784c5c28401000100003039101e0160a03031071f075100300d030500030020403452045072081c90026244d00d001c14000d41119044951419603c0c451030f0404c0184010841d03011601000310401c001c900c500c44003c032003a4010f05180542c42c4e04522421210155620001d000400034050240c250a20402809909101d01802c03900207001c184600019001100d01040c45400c1018001c03000d00e1541342070614110341500208a1710305500114800183301e0b400804102c82c455810b104540c03820107960f0f001d18011112185290340f4100107200750040c0c02000d01c28090042500c9181c64680b50080080354040e207003000000140d0100 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 243164361 1250 243163111 243163139
    0xf0406020d0f1409070e01030c05040209191401110307050d110a061103010608010b040609032d0b060306070908060a020a020a02150301080c0414060904020f0a08070e07030c09 77
    0x4250365511644078030b1400960340a4900d5104105443d10243d18000d0308080c988403603540040000d51183d030060011409441c0c1410551f203041ea40076030b440c088c080200e07024a8040c25082980d888100d8007107500d0604a020105c400801d90f582d44004510a0341e1984910a080006146901100f04030100701d01907030701f00e01510303003000070b0f203404650544a480c2520070000700040b90031400401401382c01d80000721140035004e8143e000b4101810044090b003d0401d501029210807200600300c050ac2c0e6034444d2682801e0113280c0c5d8210b4440305403400d01d400400585946100c2e011302c000180d402c91051070300c04122034881006004541350ae4085000070350048090307804601880c0c0140d0003689446004e81e0078160b1620310380d40c0e290300d0080700d28245804111000d11690514140368502420011806c1e004101101c0d8041940c5443c40002d95907411024103e0b0490031005001031118000b0420a04907000305800a43d1559000e038101d080b500c02c00d80080c0460131400c0248035045800c524 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 243165467 1106 243164361 243164377
    0x303120615091c0c0b0408011a030d0c0314040e090607090608062b02091e090a020a17010b0303040909110307060801090c030b040908030603060c030f040602 69
    0x1c40710200e0143d010340010089420a090044000300c403001040c0304040c184d91143ea41803014068541c031102d41e94182e175500c018010b141404118040013106076a60140c0000b1559070584140c0d030501d0700d45002c0078003800041840d80088454900554130790004015a00e40b442000f41003800541016041001c15002d01409445403c00c4882005000d408104242022541103442040040019500c1011501805000c1840e4910100e07225550040d181c034598800c0c10041c5c2d51240c00c80000c0d042203892100300601c421150003054260684c3c400443d0040000d030000b491500a6080a006d55070b40e40303003400c10040d000100f8075103140180d0107400001d141400140000b0014400e190002d07460b5001e44850501c268000c0d1400c5c40020420090b604c01030420b0343d8a0380085510600a105040204240f001c0344000d4a00c42e034503800102c80555680c1e43ca0320080d4000d084 = true := by decide +kernel

theorem cover : BRFrame.Cov 242985611 243165467 := by
  have h0 := BRFrame.cov_init 242985611
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242985611 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242985611 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242985611 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242985611 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242985611 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242985611 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242985611 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242985611 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242985611 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242985611 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242985611 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242985611 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242985611 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242985611 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242985611 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242985611 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242985611 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242985611 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242985611 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242985611 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242985611 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242985611 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242985611 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242985611 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242985611 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242985611 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242985611 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242985611 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242985611 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242985611 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242985611 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242985611 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242985611 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242985611 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242985611 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242985611 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242985611 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242985611 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242985611 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242985611 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242985611 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242985611 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242985611 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242985611 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242985611 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242985611 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242985611 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242985611 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242985611 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242985611 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242985611 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242985611 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242985611 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242985611 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242985611 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242985611 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242985611 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242985611 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242985611 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242985611 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242985611 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242985611 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242985611 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242985611 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242985611 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242985611 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242985611 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242985611 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242985611 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242985611 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242985611 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242985611 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242985611 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242985611 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242985611 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242985611 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242985611 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242985611 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242985611 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242985611 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242985611 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242985611 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242985611 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242985611 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242985611 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242985611 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242985611 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242985611 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242985611 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242985611 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242985611 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242985611 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242985611 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242985611 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242985611 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242985611 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242985611 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242985611 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242985611 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242985611 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242985611 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242985611 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242985611 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242985611 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242985611 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242985611 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242985611 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242985611 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242985611 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242985611 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242985611 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242985611 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242985611 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242985611 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242985611 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242985611 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242985611 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242985611 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242985611 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242985611 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242985611 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242985611 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242985611 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242985611 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242985611 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242985611 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242985611 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242985611 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242985611 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242985611 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242985611 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242985611 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242985611 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242985611 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242985611 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242985611 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242985611 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242985611 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242985611 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242985611 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242985611 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242985611 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242985611 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242985611 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 242985611 ≤ n) (h2 : n < 243165467) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
