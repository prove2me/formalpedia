-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1571
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:43:38.18854+00:00
-- url     : https://prove2.me/submissions/ecac579b-870b-4a11-9d21-af65d9505dd3

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 282374100 ≤ n < 282553956 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 282375350 1250 282374100 282374107
    0x60f0712061211150c0703031112041d010b120105010f020c10020706081503060c0f04030b18011a03120904060e041a070f020d050304060e0d050a0e03060c04030206 72
    0xd0001000e40d94410341c0c484624091000c20070580140d451a03071101210a084140b9012000c440c0900c5292074050f80d98001d40b07000d10010340501c05170f1131100c18010403501c0310915803010030441c4d40560410401c000300504180b03081440905528050710002828074205000300e4020710100006006150511140b00042c509180c404c000300d9884140050554120840f02a0040d4131340d841c41c081c2d2301c0000c14481c00290709044441071880341ca40c0150080a503550f80e84a81d58054201e480249410300c001c010000218800035069401445001d030340740564840d280019003120a10700c440510120340300b07071342003c1c0c7e85d0204035040c0c090101d105495032030040e01c000030020160394101e00700000244082c08140203000301c004058802c1201103030080d8940d5a030a4510106018500340168003006107058414402c8006d160041e10525010844003c5821080d04140d020f6800b040002c90105034402030541c8480c46404100054000d840b550805075125903682c810342c08003174050132001 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 282376600 1250 282375350 282375377
    0x20405060105070b010f080d090f0302061605060901020315090912031801061502010608060c07201002010c030c0c0803040209042307060207090203060f091504091103060702060f07 79
    0xa0302140c684030f03032208140203130b03603150243c00c955440320703019540662041100b401c01c00350007100c125060f0348035101d503d40403619640c200030065200c41c11624a054950141000080c001c00c0b0b200e0042e06010005602d034500a02c0030303200304a0010300349114800300001d100b5110008104401000a0b40004507640d40e07402098020b43d02c0d0130b1024613050b40ca0003200141a024004510b8100301680d40203200040c1d0b105002580d42c50192240c00300071108205503400920051407550401000c036283c07000c41014000003481c005082703085540503075103400e010100c2030360511680203618a80c5c2001042c4004644941805000c0104002d02603403145011405000d85841e00c221408100e080c0f044244400292171500c2c1c07061440384030094401c01c04045040312050081e00e20495001e005040125445010407002c51f201a10315402c840941902c003589485038018a060180140c0c80b89081241c0d032000d06107019801403a10302107400410074024041e408040041d000685480c03c0c6d090b00040 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 282377850 1250 282376600 282376607
    0x12040b07080c121f0306060513150e07020c13050a0b03070f031e230106080309060708071b060918060803091e090a2f090d05011103040f1203090f0204050601 69
    0x103034a00c0c4039004c01c8a0700081040300300e4211209540c2c040e43d0340104540c0b85501801a00c3e4000c0d0415203010b6040000e0085e4120400300552003407a510403910140540b07408120080007440c2b12601e40d80e10b0380204841e280d40c80c068800c140c2e00542c02440d02d0713454414a00c1c514070f41c0c0d01004003da081c2c00512040c60b40f41c240e040e41c3c41e40d0014681c800030300c6030103185142c103c40d10b1076510b079a5003000400244008003000740e498040e0003910300c901c0d10100d07a40e40f0b5a9a88480c03c2140d454a10340c2035030802c114080c83c0003000d440580c65a04205042c40d640c541c0119400790409071480c2011401d020350079000c07065402c80b020a03036500e5007034140c00300703200503031750054020541202c1104200012481250030002641100c0650180042a19100c3c0310024904010901d0341d05800c00484410781846c2294421881c02540005000c100f4102a12010341c02940c003941d5902c40c02c0e5001c018230400c03c210300b6017003030b0340d040800148980d81d441803450006681c029100b15514000603415900 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 282379100 1250 282377850 282377881
    0x80d0f05040b0a080106020613050a03110f06010902040f05040506063a15080109051507120510080c180f10090c0f0f050f030408030601050f12040b07080c12 69
    0x11280f501c1d411030440041144030300f40b10f02c500510404c1c0c041440305004004c11801540c00c44007414000403961002ea0f020840c00718540c1c0b1501c601d0160824652080c89203501800c05000c016a40c0c0380b414a000c1d60244440d0030051003107280000b0b008040c3d50702d808451100085903032000c02c09038040c40310b24440c650480d41125a45015950b940e5982c00e503800742100920034502078000c42d0321044941e0883c0da40301c0380209260b008150103100c10b045840d160794481402d203884030b040000c056080742662001c1d101c484203580c40401c02d01c500c0740184a4a80245015981c0103d202007100c591620f0040103001c12025800ca80003051384524401c904401900d2501824003404000490092414956480f4440010001803810f103285209608940103446644092410740e110703501c40c400243c1c80540b899040c040c0c01c0001c1c204800c014409440c40880004900303182c0c0c9401e0401c0c08200000030f009408000d1280704004521214a080c0c0702d281502c2451041a65586c0a01002c03225 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 282380350 1250 282379100 282379109
    0x1f1802040308030106020a030815060d15120c151b0f0c0b0304031214070c0809181801060602010207240b0402041707090506030a170f030a0f15080d0f0504 68
    0x42c8000001306a45400142d071202d00740c80383e0f84d440031035034a15500d8520200c08802c00c1da40301504206000c1c51101980001c00c42d001c80032011031600b0348e5003015600800b0b40e40811039032802c1000e010040c1007070703201b0013196801c2d003411f04420501c854402040101c4200e02c2c0188800742c6c59450030103200a191000000d084450116a071b45e0500303048c00b80c1011054060b2030011400c3c004c0310041548180940c40c0200c880761034590340b100030b42d601c4a900d0303080b1075130480e0014070100c00118034480c130240c0d1a0044c0c5110700310045d00c02c0405000341c00d41d5125000b05055a0040006200140c0341c2c00b000a03e140e252020b02e090040c100c1081800703800c4016070306600c20300110703003c60140d0b45006103494000700c001c02c44090503603c0a645c41951804c4503625410740100d021940402d2015201801114a4803d01883c0000300500328420360003d90f01c8171460f03983e0f56086a5408041c1c41401038004650000036409407403d442c0300e540c2c00000c9240d0f801c0142e44000307504c0403401030303003030745c0c00740 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 282381600 1250 282380350 282380363
    0xb090a0b0106080a0b15030a0905030f19080106110304090905010e0607050c010c020a0b0a050c0f03130308010803030f0403050c030d060b07020f01090b0405040203060d0f060c081f18020403 83
    0x1942e6400c0002c200441c00d64503503901910741300c24000d891501c00c03030715981950340c000c0c541d040d55034070014200100884101950580400c105036503000740448000c100c02851490480c0400c066024001c01640d0140c005034248103c2400100c480800081a1412514207000204200da01c62400c6400f42220780c0020119105e01c205004815400001405038528484002c1003c1581494100d030750702030044014080420780c3c4003080007031989401459001c04414282403800d81c200d400c3c0c00682e882100c0c00c8070920b040348540000c02d9480a9044d0040c00da8400950035400c00b45e00001d09c0290141000382404070021715100125014810344030030011240b401c100c804c0d0342d5584400164030007141248500304203400000b640d03005d940d480050380d03044c070b21031406e05050506010081d4400f42c446030740304200d20080d600160f45c0ea90509070040c403c03d004612000300c03005c0503208400280c50070b212031000240342e900c82c9422960803001c0301c0001c00180051030480181000a20407904041c184 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 282382850 1250 282381600 282381623
    0x20a020411090910240e060a0512041b090903021c1b08032203050a030207051e0312010b0a0e01080c0c06040506150d020a03080d0b030f0708011a0108040b090a 70
    0x20002c1c0e10054130200c90131822030b0001d48007840f56404d280c0c039006007444041000050305c0746032418003401400d400e10721410080e00d029800c0b0304070f00f608202218100c402140d844c0c030b0403000d075030345c01452350080c01c0001043c05a85407641d00651510240308a80304102d071840a016001c6201d00031a03840f0a04000020707100841f42c0c100540b456004580300d001c0e00c0d400009800d1012400003001101a8160351110f08000984800f24040c0d40004400d4401d03208600724103100f14101c419400c0d02c841140020755807146403000340e0100384016400b09015103014041c60f031080782c0256070054121401d01e07040b00380790b40d450300f0002c96000d902401841c3c1d1045030100402c00500040d2203000d0505103043c40e800190031410401030f0910710000035003100100000b000040c03042009010407a80b070342804034070607607407001103898603c0c200d0b4948229801070400b000000c50a105d00000e100c0111003d00700c2c81ca100002904a180113070005181c4003030b0303000140c2909402d100400c0c2e42580302210060707 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 282384100 1250 282382850 282382861
    0xf0b070308070305100315230903030c0d14100503010f090b010b0f0f070b040201020601140d0b0603010e0a26091809030c06040309051201150e1801180c0e010303020a0204110909 78
    0x1023506890540d5040340c1545043c1c0c2801c680c000c01849181042c00651440d603c2c9600285180c05c861040d0810a440b02281c0e541202076203000e6100700b80c41d480c110b03019440c0008150a642a203401410082e290111034030201c2d4004081e50f040d01c1ca00100300780c1c0d400c04225040418441c450003400660b8012481000b080001c6082130300540c001d9003140c04590700e07a80043c108511002089621429209459000601282c04170b40c0c41080140000796402c11a07140314203110702d43d03204a030540020010704030090280c0034030090139880c1442d443c0c00c210b42c0d0030100c0e4400d01200804d9012099407170015010b45402c000f29105120b290042d0b60b00c41c2060315001d4213105641c000c56100d20a80400c41d20104014421008160141140b40b8030350307458181d454083c01806003404070042e13904941ca030000d0400b40501c130047e108e900e07801c0e02c00007424140002e19640c1600914014a1920010400300b680062010407454040710300203001c040180d00000b10380328442c6083c0d0007641402c1008bc = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 282385350 1250 282384100 282384143
    0x402120c0a031511040806190608030c060403031d0c090402030102041a04030606050904113709051324090c090515191e09150f0b0703080703051003 65
    0xa003950306081c3c14031982c12040c166a405000e03e01031407445902030350001c0d5864124441030001030b20b40030341c0011019280d0703181c2c80c29580992240c401c02d84c0100144010181d05124451012800c0d0300c04142c56821880032684456000360164464400c01001c05c0641d03800f94115001000b84008020b03280204c210150a2504148426a0780c60300d41a03000449082c1002054880ea13840056041100c01c0b100410212440082c900c07409003005041586070100c21056030350102c060035003040c46d4146404491001e46400030814919011000800d0000803600008501c0c1050480012405138014501a50040210b80c20191608007201800034106485602c01030003281c0399001d4042e5060110203026100008540000801132810801c0213403c07140400111643c400d4400c1140315950741d180f00c8250380201101004000c3c151404124034029107180e0740041070240065401c0c882d842d10060140c840c001e210400b8980c40d0f8001410442c213071656580a1580306411402c11613500c030004 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 282386600 1250 282385350 282385373
    0xa080d0f020c1f06050916140c0c1207030305040e07030917090f0d1203020703110318010807030608070504090204140705041a2706070f1115120402120c0a03 69
    0x102d000104900d80d12040403403405104e0582d00040c1030b4004a845000c41e091800c070600359131a08100007070580d0046d03c803030b5200801c1d50820100003031000d5000308003040f1840040c1e1110304030550189104200080d08803040c1d03803c8462030f04480d503040d900e40c4001e5002e0050740100030134801020915083e03545020f000b030314403290203481d41ca4002522744207001003402d1603d80030b41109005c1d04200d20322407080d0000d00910340b09142100d5001c4500481c20725607080a04054280c0c646600c01c0c030320550b4400b071141c0d8404190b2170107202592804400c0e039194011401200d01440d1103500c500e0541d01c0e180c00c80c1003149141c8496501a1a100000400f00d402c10302030001d920301f034881203007000400f0505895084441c1c5112180f0b501d8013000801c1c0c110324242000e42c00203024050400410100420905024080c07030399961860124010082110422541c0c1e408149d828007601003400d220001043e0b00542c1614110ba54410203d0307517514264440500551080355848048200413041006 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 282387850 1250 282386600 282386623
    0x703140a03092a050f0d060e0f010b060f04290711120a0c092301030b060306061c1211070602010218040c0516020f0907080709080c01020a080d0f020c 66
    0x200c0b16803107424100e80c1141a00500d40520b40100c4038028081841c140842685d040c0000302001060b640999034a010307603840d04504030054204024589051000303010715824400d04645040c5026404e002100c0f050180d801005126043c81c140c0030314500c0c2c901a0a1158038a090081d611040b02d484e10100c0402c10702c00b21401000d0303111000b40c44100004440c1c00140c1e010b074421419074181204000141700440c0c00540c080c20b540b0440c801d40042c0040207010f1409000751510a1410b20181481c01c40081c3c409030041c94480000250749504412019000d0760001e203444203251881c01c102c0d40c002c1850301c00e00981c09010b8001540940560040821040c42c205284080d004e0703804002c11a2240601f0301d01117903041003007515440940d524080710500c0107106403010781d0f80c031022980c03002d421181e00c070125240b4001d1081c5540c010b21024010000c001c001c12807842e44800007900c8600d1031800524007603002c20800041080e64200905404564408540355050005002c1c0d841c20b10a04 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 282389100 1250 282387850 282387863
    0x1005041802010e011b0308060f041506020607090b12070c02090a150506030702120d02070503070b0612160605250305040617070804080a03020903011e0b0618060703140a0309 76
    0x8000d03c030b54001c00c030008050034010080c3d0b42e905115282a906208010112035000c0403080c1c2c10102c42e682d5210f885600090980d9500b80c0c103081c0382c0c01900d013030000380821043c00700110b03041064040040c104c0740503000040e5901040c1c0c43d01c45045d1444004024001e5102442c4000c00903140071550007608541340b6401604121669130b0300344211031100755000302c0160007024000c51180d1344a00180b10080813860018900320240c3c03541811074101503401c40da620580e0050214a1600484984402d1414800303020008480c0340b900c03050340c100c1e104000501502240011311044c0d41c4d400c030300d003050b010300c00c440c044c90081c94000d00940c40f9029980110b1004131400400d80e2441c00503d11501c000d4403920490345458481d1001900610100350815800b00815242034070b0030300807070840d98004642e000e0b66072070700c82c0600d0a0b20030110105008034014420040340243c82807c00794041801e031210b5541b030b109820304607444e050402e040601c010000903003016003907155114045080c0500e8 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 282390350 1250 282389100 282389117
    0x16080c1003090c060c0c032907031a040b0114040305011b08010305120d020f0c0c12010b0d060f0e250e090c040f0e070609030b09160905100504180201 66
    0x800e8080711800d59002d000044003640a2150710b0040790005c0c0344034080c00d2244225a9241d484051907036552a4002e0b01c2c2002030103824160b10226911a0050722600f402d00040a4a91308211000407001500d03205648926000f802c1c0c7c4d003d0b0309400b08840d100c4c4c2007540d9075a101d08009000e00100205000a10441c0c20221126445040214162070784000a001c200d200d00b085141c080d00800040300d0186d03801c210814180c000740d00205070b58140140038200c0399015404024030320464103d025400d9040c0132440900341d44030710950a1513944102c0008014003040794200040c0b51564011007244240701807a4000e0040020389510340b80c5240600703955903121303408408448010b451245450744119454061445d0503001403400008090000503121030405050f4a007072442e0340310f0320216107109024010710011482180e0f00c550160000c0040c0c1203425000c20080c5600e01c0381a07141551400420301958800c02030000034070008000740300d420700200240e48200400001203000c61042d1 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 282391600 1250 282390350 282390379
    0xc191104020f0f0a020321060a09061404020c0a051218060f0a051c180506090d08010312030e0a0317070c030206130201090e01080f12030105061b16080c 67
    0x9008a414071690304842d5418121000041905508440a408154001441002140520301d5115540c0d0364050b00c400f090703414a24240030b0903843c0303600020102403c00809107d02c034000004141400c030183c1c0d00595841007182c00718104038107204003c2031802100500314940004501804000a460301d184020000680400003079100712440c1000c524818400c1c00c46c82402940503210301840c08843c0c4001d1400c900c54076040780c48144c174403180303d0209898401030101c00c020440d880508507008000c08200c20b14090421081484010319900292402d0749146202e50440c03c4403241c0e0780211002c0c1442c0b407a001d000b507990440d510f00d0400c2c031400021100d501c00d8403422801500340d0081e00c440c0c0c485500c011402d094802099061010403500065440034440e40d6500030000f501c054403408182c0705040d401d0004030300c142941d2907810300042c0641c0c1d641008842d14444030300728070b61500d10040401401c03d0414074095201d40340051000034102000325041c02c5141c82101c5480d4101000d = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 282392850 1250 282391600 282391609
    0x60f020d020a0f03031b030501090b040209030c12031306020c0f0906130e070302120a1103060403080109020a03110703031d0102040b070f1a0901020a0201060f05010f140c1911 77
    0x2a6980840140d10110aa00c04a440e8a02050605029280c00f045601c3e2596000c403651007043d00d582c6c0000d6490004000e1203e051040c3c1410220441d82985404038100000766100c02c0b08503014031072070329101c4c040700745c510402c11200e40c074280d0490408491342e1901d004c0e440302c88000c1050300074207007122070000500d880400c192091070010720a2016429114441c4000d000241141a45104007940400542c0e1100d021808000548004140c0d4080504d4040043c280d840b003001d00a40c4030f94180400a82c2015090341503032b020f82e100603100c01d440034040f030261051828aa000410010300c0b202410b9058114034950303c1c507007040240b0039410a1803c1e00301c0c407c510840c16521014005040003035030140200035928058002d0a4102100c100390300c031000c00c1554041840d83d4001405a1f4040e0203018010041070048030f41d0414515100000c0c21f6000341c8041d0004100c1148010201088248155800220303aa07003150f200301002d10300c2880b0f00310307401c1090700c201e580841000c030316160 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 282394100 1250 282392850 282392863
    0xa022110020f1c231f2102030703061a01110304050f15090603011212030b1c03020111040617090c03030a080c0f130e090a02061b030405040213060f02 66
    0x2c2c0840902d4000040202c1c410781c0f032800d0160340700944a00b45141c42000c2c55210406407200b42110030254145642d629590034a0011620955400264100700710a089041c01c0031005001102452040603480042d0030403a090300010021440c022040000411203c520b9206503000c1e01c0754614101a0440c8030750700d014030320880e40d111944082c0f80c0464200703c0a081e2800803c0c07205a414443c4183c006038054200740c111130003d12161010313a06000682c501c41102c0c580324103040114080001c04111200e11303e4000ca458081010801810140700b50701680051901e101403588694580791300820f42d94480720b580340c0d0000c800c804100114004940fa88841400400175442d0064002e4203035441ca070010542c03141d1150921010108509241c000c12180f140c2c1240561118106a10f0070707a00301015222401c00d0b4420010500103889070386c100c408004581003105240e40c0035400040c590311440c0c210380c1e0000c0c0003107158046900a000c03e04182c490a0b25640c1e500c40c000301c0d0032681e501 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 282395350 1250 282394100 282394117
    0x10801080613030507050d0f090e16051b010626010510030311030c0607020102070204050c120a11040513060602060c16170c15070206060d0804090203090a02211002 72
    0x10851408514902c150142c6500410300c03a050503800d00c0c255807509801d1401660311280800c600f008001c02099200850310701502c800c054070502c07410311640c20108040d507158148248800014001615289020001d03079240307045000f44440c540b6800501b0381200e40320400e402c0c00340d0000e0094880305060240714890058400034010041c5951011100020005403c50381400204800401c1440c1442194410a019000503076998450300c18001102c4004102aa40000c1030040034441d074141c464141e040710392000040f800640102d0a0740540c4104d5200c0e40c2c0c450280c0703024000b08142c54000d5030854403e902a42c2c529a0b844100c100306226913000007044481414017000044e01003441040c1a402c210850390600781661541c525101090316469100d6405104016200c3d6041040d60b0b40800144c51409000901d40d85560380790050b4003c00750b41a8001c40055480c28003007000d2824960020001a20a02c50400b010043e5086554102050081342d60540c4c00010600854102c40c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 282396600 1250 282395350 282395353
    0x20406141e0409020a060f0206151c0602160c030501060b03010b0f0c011107060905010c0306050618030a0f12120c0c0f0c0e0115020105090d020307020d0c050a0603140601080108 78
    0x16401c15030548405030360650859000b540c5058040c090386505001001a020326280ca49401a980030b010346440380c01018141100007000000c074035034a9000b15800081d40303400d4403c01113442442c1c440007034040e00c50b05441c400c4840e13956005001d10072611a080364004e6000300080340c0c8407003007104244000d000d00f0714451001c01c50b04c9016200000106620b40707040c000000c00201d0001c1140044c3e10103801030f107080c0d4076582c815040c00300a110f00c1d214600c05041c20448189040003103099030141d0950001d403085480d0240641d506c09100e544e96281e4441c452042910031440c3c01054910b070720382240001a42c055806040c0701440c440c441c0314076900c0c0c40f209070b5030303203d0381e9541d80034000450304840500030110001a2820101d03134107806000101510602c00841d00d070000e08440d0010000c0080307500803031b078011040350040210384c00c264041da94a40c02410b00d0030031000035607041e400690000855080015000c0d8580d0141a034450b19462040d140c4e1075080c011210a03100380901a0103 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 282397850 1250 282396600 282396619
    0x4050106080601121e02070204050a09020a17030f03010308310b03070201090b04152004210507150906261905011d0f150f06220302040614 61
    0xb07540c0a2001350a1900411102180d580b060209804103040c0d80d002c103c0c0c0e0315802040060442c503007406031a074440801142004a403000e5000148140428461340e000d241075919040c542e5442030044070405609100f10a54950392454201c4882e444031942007803890003014120f482c2c1814130b40808400005c0c4250703240180c00c2c02d00d1541158405400300007950f40e1100c002001800241456104034060004221220f42d060703650000c2e2200020032070f400909203140031026801003400e40301074030040308101401d1107143c2040716002d009103101501e0b034440c1420014000c5400313040c802d030700318165850b441c0d51075840806403500c00c0300071500800c482d49031000c02c0400c0c908041c9954440c0b4400c0307800152118120300765013100c1c02a040500d8aa400000702107480529030708058001d1401851203540780b44c0704030106003403084035035010303c900311003410000e05a0b148816107450b03201c44101001034082c6c484170b6840b0040c1c244022400b481c1041c0000454032170710f80001880020181c1304c41e07074 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 282399100 1250 282397850 282397861
    0x3060603080403020a0b03070518060c06040609020405010503031c020a020f0f030a030f05160806040b1206011d10030303051024030f0b0a0501030b1c030206071119080912060c180405010608 83
    0xb20280ad60580303400501c10b0055030020700f410800301c0e0007180115000183c207103450060005641050b00550301a81c8100001520024005c0c1d030300f00c5110030f401e80140c8900ca601400c03800c1000042401d030440c0324801806a11070f00c080700514280780c0e0341d242044401e0315841c03480c00389c54040300c81c603031722a01205075143c039035000d00d10382c03503110500400000d52042000001a00c40a4007070f49158554040001880860f050044405450311801e804090600c2c4c1080c5540d070141a03404002c2c06c15480c1e20205541410582c940c202416000c2002c08100c070500d0701c201e00f600ca4091080002905083c03040501103900e100b15004a4400f1748000581d07401c0800650150800300b81940d0800305559000205c44584401941b05034480c0d80613180758140000c0003420b5116a510142c400c0d00068a0903a6a07415003aa1003550340c0d1140c02d0031b8a1302404400180d2124411040740024003428080181c110f140f80002c0c01d1402c2820128540140c04c1818081180c609000c2da40c00305130400b0200f00c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 282400350 1250 282399100 282399127
    0xa080306130609050c07030e0901030f12050c0d1d0114041401020a021f090b0c070e1801060f06090602150a0209060412030e0405090a0b0105060a0903060603080403020a0b030705 78
    0x207035070303404000210344607580e03260141c11218115148802d5060200e110400c055002d03070011410b00048a0440780b03541181c0701c00f244d00c220380200400040001c5003c980d440e0041e029501c181011405807050000781c060b000d00320b042800c6801c000c1d00750741c07822686558002c0c00241c0c0c1081080414a04050803c01c00b1016150800c6a46041d40b2803031701c801d4016075030061858240c0c40c0c070b0640c00340e034500490005420034109420000848200b4005281d80e1500055494100c9880c034400041c5a141d103650900c00040075103090384a94203100300410051052305003541240e4965131221011640c40c0e4049072241060300980d02400480710100350b1003026038002c0e010000c80200807900c1c5c030380e448069131141d03844298200c01180b901c501e100300e50714280c0b060660201c074800160015800b25641c140d55540b0500a80d442107502040300d104141c821550400595400607041100c19143e0034900e00c81c0d00701c0e11089101d42c0003582c004c92985d042e181524000c2d001358660600307051030400c030034 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 282401600 1250 282400350 282400369
    0xf0121060617130f060e12030108150106020d0f03050a06170705090a090c050405090f07090b03070f030206090108041b0b0d0e0d170714040608090f06160305090a02031c030e0a080306 80
    0x1b4071240c4a04041d1640c644072102c003c5008040748001012a40c00981101c1c1d0320200507407055040d5004000752900d80d07500400105002071180c900010103603520085040204101c1d00164901c0302840700d620403100001610f10f0985004941c6d0354090740c0e4000201c1c05603050414018100c40280700b00304011f040c150030058020000c1c1c01507a0129000c1042680341c0020340e80419203da4840d8100b10403400c040c0101806040c0710000550724a046030045802072140a0a00f41088101c90001e81804031042c031100c05500031440509416a85480d0060180c10025110b0002841c0c8200d8042650001a601c0d0840c00703130b6210280001d8070300b0055414000c0040c01c0c8414004030148a91303034265003400400180c441516040b02500f440e80d03100c5d2802ca15440d0813075950340148180580445480240318480e0307c6407a0105007a902e0820407400e110101da4001c1d054401c805013070100e080360301050320030866607660400007080291202c03036481c0c3d035101001c0c1c02070307030108046a8a0b050000c2c01 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 282402850 1250 282401600 282401621
    0x1802040207080d02070b0109060e1612200901090f030f0212010f2c120f0c01020d2c0604080702041802030a03020d0215060f0121060617130f06 63
    0x10506100c0144103003030981c1c5c06418200d515907041e80c018885402e403132140b1009442c2401420500b0715103040501e410255401c044014441d00b141414443d9880390000f41400c58584d0343c5220303161100c000481c2a4225003900e0340410407400012800080381c1890384126500020887e12070b0b0066001e101ca10800d1402c2daa9065407640ca00f401c180b242400b80364501000c10303160000d2030448019038070f003004074800810000d421034058000e0502031441542d452813100c4112556516001108a00900c203a84d1916510b43c20030b642030004140c000e000c0d1002d002e1076140441e00b81c60a9106680354a000c4500506411051100c0405800c0913441001502c0e040c4210040c05204c0d40c0000b0324101c0103090850069004080542031280c1c140312a0036910080240340c0d01a007000d4000500c1128103d0400d0b042007410b03900d040074002c0c6824044884198600200700c0d0715140c0c40000d1403031135106424502e0000180200b800100114081c0700c200b80c001045054414036541c8010240161004 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 282404100 1250 282402850 282402863
    0x306061e080c121003020f011115060f03100609061d01030f03031410090b0105070201021f0204150806040605060405030a021e0a170d030e060f09070f0303020a0204050603011802040207 81
    0x20f40fa07021400d2512409060b6403600060818514030410075121b07101d90705181001502c0038080d00710301d0001400d44c2c041c0452811600181c3d00c410110360960360002c0781540c540701d140c426010040a44d0b12090582d4403031181400000c1d100e1158100b4101e9401c410300f6091007240042021444c00b00d0549080c500c246804074210741e5400b4a80c1d40d07024103841c9411200070740ba604110040c4113104001108c00300f8203225007032050580000c0d44440d0040d141c1d0000c80c03602c11540e9000350352541160064401e00321282c11009900000800d01344048a00c0d80c000d901e0410003040c2e42c5002001e44040303890060003440c100e0051f07400d110401000790503040c458180700303409040c665504200203000d0401d440b40c9504030011030701e0451421400003d0801407600d0607102180030700c1c0c0410503903448000d0060703090564656484052070440340b684812103a03215024017108040d804110110214004c0700c0500094840d41c00705400c03135400f01900c002031215818204018149038000d412900e010340c2 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 282405350 1250 282404100 282404107
    0x40501140f0f0a0201050708100b070b0619170601060c1509170c0a1a10030807080c010c05091806030c010f02120a0e03060a050c0708070618060c0306061e080c 70
    0xe0b107000c080e800101c0d416026075183c008014405602c01007a95100c4c0203284202d00c06031400759481e54511078100d0251184072140300182e89921030740030010315036a40d20040b0541c20364840c090720b6481c0d145c4680c10424010b08000150003031248017040c03080c0350405640c0c3c0c0340c0312401c2e5039080100103121080341c00c015101c581c4906056081c0240400d1075075180030782440c40340c03440c02000110220700c58096840b840014400141000c0184600390382e44040030b10f076a10707a5420b08100c1c5000d0400014000c1d802e1010740700c20690702c000648500741c0c05a540c03c0000e010f541c58000d080000b01c6203150150701044800f02d0300c0d0321419a180003145c441c01520f02001d0324131070070790700d1340e1040d5100408a140c40030380340001d0500b000380e10f5100d00009010012400c00060302ca40c1881110006403c9900210308001406110303401007194500c0d24100007128142c924007140500a00311808010901d011400169075018040c4855041c0481c3e0000c00004600302301a80e410b800641803203d80c91051 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 282406600 1250 282405350 282405367
    0x1b010506011704021c05010e210f070201170c071e1a06041e0b030705030313030b041e03080f0a0b0603011e05030703051006050604120204050603100c030f11040501140f 74
    0x244442c0f0aa07000704000705605104240e400e00d086c1050300c0c40a141000c405050340718114030010755a8158101e84030507910405400100c3b031860110382030900c0c06800c20184180c09140780010080c0324403c1c024440750064100d149690b0060901002e0b000c404030318802c2e240d801500070310700d9100704000e00000d502141405803001c8540c40e030204010660b0340da501d2600c02d16040009100404080b002145080254581c3d40000b1601340320007003e680841000c101040f03884c2201c4c9018841004001c484a070172420018035102066030740d0748402444901281e0105118000c2208564000e00442e19503440e12061051503100c4000c0104142c00742c01000c26107640501000c0c00841c0560014000e128442d0380203000c49245602c020b100700c008000c100213000d550a958845a9011030b4005425500c040200c0d041008175407520b28039030300e0200c4114810b034155202c50b6252500c0441080b140000c94071103206881140541030100d0498110541d0307410341c0390020700000c0240c5800c81c0c100500d4 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 282407850 1250 282406600 282406639
    0x60402040506120f0a0203150405070b0f0d05040b27120d06090618050906011818020a06050408070b03010803070b04110312180d08042d0306021b01050601170402 71
    0x40320308110300754000e581721000f58035040158000d0031003010452422400e180d580d881d51780040d44192424224007261503a40b41407030302c0945640c214a003100344698603152030304a02c00070b0120f80045602545180404218003111841030403c0c050f1401081c407a800c2241000158100c402220245a16560045078250841c09030f0350040044c4107954036901c0c154108002929001000c03130046a00c2040100406440094005031603046e0302000607040d086841c15401c4080c148034080e400080703202c3c001504560100003402203684c1c00c0140e442c0c00f83c4803960200706210030310940500754014403205002c41c03c12030684d6040382c850103521040780c00a00100e4144008034040b40c440e0040840d42c008441c0320003030701c9103401c501103940301c032119516511080280140e02606100541d0510ba51406e6900c0d409280c24603000b0420b1100d00310344c1d900c0c207400694801440014200904d545a40b13448605001c1d081c02a00c058550f6240e039030340c0f00d44004003400010f1050340e20030005940620100c00 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 282409100 1250 282407850 282407863
    0x21070210020f10050402090c092d0a170606010e0d050a051b100915050405030a05010f0c0f0813031202030702060f0709050d1b030203070b07030906030e06040204050612 74
    0x80d5000b4286038004841e000f03092650308114000700c14202000c000040e0390340c40780d05600c281031554840d1078107080d6010400d2190600c1c40203d5240a4140000861007503103509040d2420403182d514455860b09400321260583c00000c249581c4000042170709503010702500040749502518002c400c8403079441c0d240c50034072100c1003902c582c0c02c84d1a035000e240500a0880e0759618041d102811004215100180151034034450328800c0f049145680016620407001c4030020000107003220480764039810120b0003428007202d01d40c500b0345032a0300b04010314021111034842190a440d0082995031b0f4014944219803540741c114100007002e00703904074144181c0b0166025075002d134018501490320111702e403c0c4d0b400150a000501410040401140d0717110100748207215484080d401403c85882c44180384c4070b040381c0000350b050241e0306002c0b03111420503025100f5103000b640d612500c207a1320340c0154100c0b490107082c681f890b042040001c000d803c0c107802590300071102410329000002e0050300300c0d06242 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 282410350 1250 282409100 282409129
    0x307050a060903030f140a0e0c120606031c050d0b060708040e090c120a031817030d0606050304110909100e07091a010c031409060403030915030e210702 67
    0x3035407402c0c0141810340c14403a0701d040b61060f00c0c0030402d86003280001c600c1c1040c002d007000121901d502c41c0642d201000c1c0b00d450741d4003c01070192021018209480e0b82c54170f0741210600e000307110f01c0301d200f8203486a80094042480f42612070500e0590036161940213444d402c0303000d941004082043c02c0000711410001c1000b0906052080703000c0c20300c0c0c001d039410b096107104070300e1107111003c2807402c0b10100402c0002d40b42d541403e1034060704804044101c0c060f0180c0d400301c486480c600540c1484058040000e002c40302d0f40c00304c2040510748070481942c0d28002a02e025143c1e00c1992140b20407401d060083e2038000d483c1408541d82c500300802a841541c0399a0150016604045000c121098043c000c2402c0b201c000500c81080209840008020780408000507080040031541100c54420385400c64807088070241c040b55a0300e4482c18050040c4002d8411150044030b07a415404a56100e0b10590b010449240c026010148180b06140400c1c100140000440c1208020b6100181e5807103440b4858035 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 282411600 1250 282410350 282410363
    0x1003090b070f0e01020d09140f030d0e03070e07020607030e030d110d0c03021c05041a0a0b010e030d0c0311010b0402120a18050712060b030102070c080706020a080405040e0307050a 79
    0x400d05182c0240b56142c903000c06419580a607407140e2910380c00004000a40f02a000d490360340821100005094003a800103942d05070103040c0003071140c6030b404903402032403880a070700320b03400c3c9552458100b5180800321032120043e00401e0114000c240b1a4000c5603203000c81ca811a4140601c00e0041011545c040240100142d40081c040c69a12114003e043c04424141021814041c2101140360300030f100308122016143d5071800603081180744000d0340030400d42011407154501c0e01c0c110078401400c0c1484480e0200d807224010301e4542c034000400e4040d181071655288030404240c0d42c10303611310410300401b103010b548905a000041c1c80360f10103440503000310100c1100c6401c04103032604c211140459420034010440481101058000965034115180408401e0040c10b0704d0411000900300103074401e0785940001000014040500c40d0750081d14003101c103580380156214001d03a540c22843c200180b00407400d1000b08154036041e4402d082400305501600d06d803c20550700d603814139802c0307881140c00c07 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 282412850 1250 282411600 282411617
    0x7140f09310212011e0e07051213030c03030e1212180a050304030308070c0c24020c2404050405040c09060902130302130e0111040801050f070e1003090b07 68
    0x44010301e5403121000c040da00c0c0300310302d8840b45146114440b0414082d032120000000320202c100705580e080319006003541c0030b02c0c503d0303410868401406540280c0005000c5421540469110b100094101520552544940c26455803540e8103130007a003a5064050128006d9003c0102c0340035443e00100700c0540c0d6505150824540080340410b038110361040c8011545c001d5898a0014100000700c4d025a80c040c28070620a641c1c503002114a0144150001d20040e260704002540c0d880c024140020242c4070048000e01c586020000c81c0c0d1502a00b80a9520400f10030b01075100340d00d60510789880c420400c5185181c10346401c0890181c680c1980e040314184c61020040181c44ca0501c5040098501c2d01803d600c2c101f800c815502800d102030001a21504031000d81e1180241140c0c8070000302000b03d002800301d5141131440302b0298021f44500c000b01c1d401e00300010042c03012095450b103e814941c82e2103458410050911003041c402004240505a0703414800003c02c4816051030300c60308590362039205 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 282414100 1250 282412850 282412909
    0x2010e010f09020603070c05070b04060302090102251202040603083907060e04090210030b0f010905030304090c110a1b0522020c03121311030607140f09 67
    0x21078001940003051035150070700c1240165620021640c02ca031862902140188003420007500740030481d031000345151000200082d04075055000b402303400300c00360280c400068000c0030200e20040d030000c1c0da403580013001c0b03001d002000c05101c2c0c50039002c0c000ba00004445849a9504a080d8032040b12403e03803e903a40c140c07180440b0340030b400a450084e007102408480b081c2d40b01090750380006006100621222030604281c076180e644c840d041c240d800814400a200440a0150050071401c480324040c0000300c1011402c0c1d4018800b26003264400760046103490300e4448103000415096203000f0410072a142456040d020801c940c51007179010310361070780e0b07946195a020b0030f00020b16404a4005c048000d00e140b585008000f000d03041a0320000c01594800428040340c0c00d61080ca22100c5010440809100c081150007203024441c500c40c0f698070f8103003100c18080590300d2074101c666030009100c1030b5030701d050034403450003a051109c40c0e440320703d0070b24440a000665009400c2d2a401c880c2041c01d81084 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 282415350 1250 282414100 282414103
    0x91e03040b12010f1203020c010e0111060a1401090c320408060106021504080307141b03030610020c0d081e0301080c01080a15050d170408030301090e0d1218021002010e 74
    0xc0003441710700178480281e41140d42c00382d280c0c80c2c0d5002c014184840380302800b9841e400b40340001c40780301c7c036102590342e145042c51510f801890640c50540c0c03080050740010511120b544a195081022601c40d2009162501e40302101c05201061014041c1030711801d1744c40d003030b00000180c00600300c01d101410103903040c0003000713181100607030507644a20011000d0002040c1c50b0340c200ca405c00800c2c40c2c0105d910002609034241407046804500c410307143c82c984910020b4012002c0c5016606c00c4601110505280404070b030f442d14081c2d1305690140d41c4100c2040010220001040e142c0210007200390808400341d03000b00150000da0050743e480d00004518201903078002101a80b00003400d100b0800446c055009000c40c0c00700d400f50034010040c0e01c8000b400d0001c814503c10035000244800b03070756245c031000956260740081c810044454144440d505030000007054000c02101036540e8100540c08080d0700c8409000940b4940c150036a801300c1034009621402100b1021480d113400118860350100302c601e = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 282416600 1250 282415350 282415379
    0x70323030723070b0708092101060504051003080a051b07030f03030507080c09040b03010912030b0a060f02030d1e09030201020301050a090b030604060506030f01060806040606060305091e03040b1201 87
    0x1400c4075002083c1c184000c185040075101d02a0300426410b0310f42440c0004610040351281c0382c04030341100a0510390030414150040030548806540900a6171905010103220000307a00000f02078443c18040100d4803445034020740141c55104011030390038086100483d00b400c2031030b001a1803501c45403040302c5c00c0c103405001e0750780c01112910b0141502c0c507100070f05000714047c28000c1d44c071980d1034980e032000c01d6409400085440c2e40021100d413051600b108050020014900f81d030b4000c5440f904000b6000c0c1c05004480d10503207980e009185000008103504000b45101c2108034800c2e4840e000b4400340d10060710405428910980005940b0350520041204003403ca5000c00510f41c02c0c5490101203480110b180c6801035403218001c100e680391200040e00317200030300c0e1001c04551700c1c4c0100040c0c603040000e207550040b4000d00c4200806516a4811400d5a50840b403d075000d070b01104100e01e40440702001440c00101e0f80e4252800e243d00c50b2009200c960040e4148120180f02d180103220006a20018 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 282417850 1250 282416600 282416663
    0x14070e09030307021b0307030b0a0c02010e030f0406030504080c030307123204110d0308062b0b0a0e01060b0403021009081002030a110307031a030f0703230307 70
    0x11400c600c0c200c8802950351201024148000d402171306402113580341080307600c01442c2c3c880d0510551346800b010b032030000e0140260700801903081c0f4010080000000c030881317807610120b0441602d01410084150040c000107801100c001030100601c0f404504244040e40c000c981c0b0f40e440f18015070300b01041a0542c1c240007140c050700702034200300c2c10064511094004140e01032490424032582c441c100148410552000035402034a40302c810000c03d50321666442c45168104d810b00d20345400a8405d909032404101382958440c07090b50321802080007980c0c51a1300031503030399001ca07070f2611a940d514295001da074403501d23034688040b03011f101f145400c019580c0036004914290044501d01005141c0e1149a58000200c45034000081285904650405c403502c1244160181d80c80c200a50000c008040851300c0400a00144500b18a980340c04991201115000002482c44c6821904c0300001203c10b00c4503982007031180c8140c00001c1505101506d190341c0560013038500000c1481c450046d04ca2030000 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 282419100 1250 282417850 282417853
    0x10303080c03070e09131739030f0d060f0f060e0301110a030b010e03060705031605040504150512160504110405030a1b1401020d0c02010c0f06021b0102030f040201180314070e09 78
    0x541c07400040214024038104007024914041c206d200c0c4028000283c0111030b0300c1141c0000180780e0742b1098400002c5c0440302590004001560350351b42800750006d40390141c03001024440d81d08103c00f80c400d0030305201c65072000b000040d500e020f503c0307200030701d60001c4a04000300741c40e42d60340032682d82c01c0b078107081105805030b0181065103400c2c50001d00601c0000c00c5100001c2c0805109100f052080c0f0581c0c000e030601030400c00c2441030231341890803a40441d1240300d1185151041c03c0310b04080c0811200c0c0019002d9030015034440c180070400014000f1071003018052001400300144650b020859100b07203a000300640e00025600382c242c00754203441c6070401c1280c0f510350281004966400200685000500d01d0441c542d820b16200407901c80c0401c40010300150121790116040c00555401400307000c0504140d00008e4182d504101d00b40c0c00116902c540c505400b200140255006901584001e100301240703c0f61035450743d50b5181c0780045000d046c1c40c03550010105000c1020f540c440c05402c10b00010 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 282420350 1250 282419100 282419107
    0x606090d2003060f01060f0c080409020d0b0d1205030a0906290102160302010e120609010e010c091415040312020a0b0a0603050c13020c0d020f0c0405010303080c03070e091317 77
    0x807540b00c00f103213061140b981003205081005a9561064600c0207103207601012081d5619615903c41020750805030802e441b2524280726504e0a00d003071060140403070303800007a4110316198440c054a1a400c001c10040a464543c600f0100042d058814510041c11020107103580f40c084050000020307410204450540d400001701c00c0152403440e41d28012254246401d60300300103808013007040e59240c80201d0549110760b41c00e2149012040d0411155220b9590003000715610448044032550410712904000b00e59100d045505800c0c90303841e84d0190018142410700d27007542d0b662003000c14124210281d0068200760b81c00c20420000103c03c541248411006200710760454407500c1d03d4110f074503803e522858100c100fa8104408540550b01c64150344026641c040c0f24110000c1e4861401500851250140e4902c551952501d4440c66044c1c94040d525000e040e0b881c2407542d543d5902c0540581c090010400c6a0a51076580b001d51520812220300340c13100040c20740c41d10f0481454040501d01c480c4c403003030 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 282421600 1250 282420350 282420361
    0x40f030c0b0306220906060602150709270902030a120908060103150903020114100509090106060522030804060314090604030e060d18080310080307020109030204050606090d200306 79
    0x1604001a00010744034a04c10025000801030412490017402c09080250000d00681c01081003440304000081201e42561016070498800b056030140202203104c076818039000384118946c882408c480c640c0d00007501d0b8038030f80009161a000c42021942c0e198000d84051006a008071040b0040c41c000005260f45d50459403a00c6030744c64404141c511540c0e80305214000e0520075082101001c048010528040c1018094040505243e016582c046c00101001c540d01c0e8405104244c1100e0207903803070600b800d003500c0c0c0e0540460034000d0104040307a02100d005c4085244080244020085a1400500d28442c0d211354680d84e88018400505504000e08120202e500303d103031003a24500c100c45080d039501a80c00711600030b0801805100821062544c40e40400c0600720007507000e040b00d038050711140c955418509a0703900c00d2480c000d001030a500401c00c0141000d070005500400c00030003150a20442c82c002c9035295a00b00416240b2800d1034000c42800307800c29913110803842050b4043c04042ca401d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 282422850 1250 282421600 282421609
    0x1e1e0512210f130f080d0e03070302010c0c031403040f0b090a0509130c030b060103060512120a1b12030c02210c01060509040302060601082d0a020f040f030c0b0306 72
    0x80c2400d21407030000094401c0d601881d60704543c07105501c2005402d00035181d0703626902005060240140138411040040080ba020718144c420b400c40040c01425241d0941e401120400d20801d0100e0ba80c2180000200025056158a03481d07220030600460b100c904d4024240c60354042d40d841520306500402100c400c91b01c0382000c283c182c803c2565030b042c03243c49408a0a10024401d84050034044034502c010042000c00300d00d0b9030048200f40e07000d0000603101e00401c00e030744141c41543c08455101a4003040f404180d40041c202d014a43e04010507030b011004038110084192140071503115103110703280b0054941510800e5840105880141520125070481c60102248008409844603012138682907800c425001807001d404041c207010154206460060f40e103001c203682c800e011400550008590280e040315801c0b00d02100752070700340b0050b440001c01841001c050425a2269003c0011b106004110343c024401441d50346035030381100d0b2550408001d03046041e00108286403080041c031035181d55 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 282424100 1250 282422850 282422893
    0x1050108010b1603091805010302041409060a09050a020405070206040b22020f0307030f080301170d1d010905030d05040614031506030901060914070206150303041e1e0512 75
    0xa0a40721010b1100c0f640c181943c03005010392050310600c2201c2c0402c104480381d600210f040743e01c2910140001d101c0e500c0c50303031038444003225040c0c0d0790341c400e100041880c0d10b182c100400c501d0080080d00c5a206542d008101a11401c60f05000580d00c04800c0c0720130005003001d0160320510b0058862075030304c0c4640f4108810191074001074031854500862108079501032108000460f4064030480c078019407440d107149990024825184105205140345a00c60804602940650495540d4a43c100c41819125a03600c040c40d03d46410449205000f24071502d04111004001806071202520b4034540500140020b540c0380e400500c007030b020720902030a003001c0b120103007803140d040700c405480740d490703192039130050a05601c411604c5080c0385540c101c8041c5200c1460140c086642a10120b55036540315008003200b11038613a070558000c2204001101060001c0d8403054007519400890540c0c84c0c070074000440d4810907941100184000070400e0b4549034101400da564964090810010300e2a110b490202 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 282425350 1250 282424100 282424117
    0x11205090c1003022118010207050d0528020f0f011e110d05040809090604050f0f0703180c150206090304140409050a11011d0f0d02031c1701050108010b 67
    0x902035107066041500940607592408030345c010000c0b002c4414a85162003000070344558041c240005030150a2250600868055507004030017003190b418001c00845080e8054030009018041220420007141703e116007143e01114598001c1000e001049845403c1500703e0074003030403a80c98008400382003442da4603079001110b03400100066610001121420034403c08612400c207916141c100030400c03220170003616012030180c0b505942c0341d9410045c442221303070a0360b50a46140102c0c00245400252030074169200c00d6a01d004600074801480022034100c03111001c540c8040c05020030701644032810142c05c040e81c0305200909150911006090b1a482a400b8039a84000c014a00051640711a0801d1180300e0707000049406184c0c5504102c40802d808403d1180041c001300421003070f285091148440e04070300105000e5284000104110318001780403000ca070140210305840d07444001788803980c0c1d81c45030780c0e81b20722611115030002c1e80742910050304900d051020b4070006110042c0d1031400d542180 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 282426600 1250 282425350 282425359
    0xa0f060915090f14070f0807110a0f110a091a1012050619090c030c020c06090d0f29130c03110d050f0115050303040303050328060308040302011205090c 67
    0x400c00f4800b01c0b4040c0803203c0000c281c84441005221400385d02c0548442205103d40d584001d03a20344003004c5a03141c004c0d01c2410600c1d0b200c0c09100b40440c03003c8400400151050380304403d07107203404011590003082e0b9407202c0315460755450100f006c145041b0644002043c2110282208514000050329040301404403040a540c2d500000c0e980b51640c00b888605090300c00c6c425602036039550361820180c11a0540d13280000d05002d0b60100542c00040c0d41d5411707010042085041c601da2a00f0b000f0b42428400064850400441100300400c5141c804800341c60715126480e0030318850b03080320308041940030f80800c0d07107010b6103035330301011030604541c04003565800110342c80f40c00240c40c0041c86080e0201c034082d0090207a1404494121015889001c120000a103c100541c0e41c3e0b9007016101d00407440b001c0c01054040002132101140104002e61900e00450b804981c000786820160894800c0c0d00200c4e40c09800060034419581c200011594010061509000c903141241078075841d44000c14485004 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 282427850 1250 282426600 282426611
    0x30a02070611150c0c150402060406030207030212030117070b0901090e090a021201020c01060b0720010203070f030f0306090e071a09130b18010b0a14040506030a0f06091509 76
    0x10100c2070100c0c2c24019514071454003d03013040201d0034065805041c500c00b451140f00080c04d481c2d029500c40038440c03900100018109444e00ba000e07000307940700c800c040f000c6000d181d04085400d001d4101841c0a031415010841c02c0c100143d1219160649641042540b00300c14080070045030f0340001c07441c050f00c42c0c0402ca451151600800b02d45001d001c007000950040b0580941445100154050542039044400038880103541d0382901d00f00348034000c405410b4012506900d002c000340d007a0035441004d0182b0489282c072580e40c5035910840180c0c0412000146c2c80a11041529031502070a00a010952030030080500b041d14100ea440b6020300c01c3d10052003207803282141d01407001041d52103001c005130611508000b41807110004090806401d4401c030f8008003485108000140703184d041c0c5d030300e00100c2c030301d404042a4103903101c03000040703584950503040001180700c1d114880914011854680045440128040350300e05a80894200440032460f00303819a00c0170300414141000c490010100044 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 282429100 1250 282427850 282427877
    0x103030329100e040218090a110d0902030a08030108030301030b060108010b0a0e031204090204031208040c090e0c04230c13050405060d081603020609030a080103110a1e080f030a020706 81
    0x3c507100d4412945521610209142d0066850708600710200c0360125407043c0c266644c100a5400c80d00c10701d0340c410881c041400035000340c00c11540024039181c002021522042c069544904069009800003680d50300040010010050302140e940c2c0c002c0380901f8000d100c0c2d810401c02140d41d00800c41c01404011649000c1c00003030b2000d200c0c0c9450fa175001c04007181d490791100c180d200030750700034401142c1c115100900b02c05254072604006000e0f81d84854046c7c0300740c2c0340c0300c81140a0400e048803401d20f40200191513941e40e64912500184116103845200c000580c14001e6003200d400601c2c14158a01c01c005802040750642e0f5100141c45085500040c01d403a40e5003c600300c07101e098030080c14414001134680c1c4080444492000360f0f8404c0e401c41e00076540b0300000680f2800344240c0200890304050040c000034401e400c406070ba03440c02900f0619103a035240003500c4a00e66a803000c164005070104180080382c0d090000000100f40703113009500e8003003030303100096940c3c05d20f124070010000100034003070 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 282430350 1250 282429100 282429107
    0x30606071704090c021011030609180109061a030d050d0e0106030501020d0207021c0203030409020706020705010c090f0618060e12010204260d0c0213090b040b010303032910 76
    0x6020046401680700c5844200100040c071013414002c000d0321501c500000b103582d0a00514419003e80c02d0424216103d10080c8048200c000d00785941004280151045081c404d02c501254217002d0007001c180410060f80c0060328140051115020b500035103100a121034110040f101c4120b00051300040415000503464014811600010300c40c0d400042c24442845080c0c000c0c001c003500894a0100c48134011446503035120036214000d4054005220802069109502a21000b4042d06015260101c0c5680b91405c40c1c00c101c05c0f40002c02d41010061040314101c440d032101030002401d01c00d42ca048188a100b0100c980d511a1800700440c0024644483c0c0780c0002e01140c43d12040000d40d10b4031b403584415030000781c13103040710710100f8001c081c80d00c2644000a107030340b54034056881d9040000300f69028032003082406804180d00c00d403500b0b45000050000710081303207e2409044218019415490010107481142c41c80c001400314a00004a941d0303005a22829242ca08440010300b44107180c1c42903 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 282431600 1250 282430350 282430373
    0x117070c0b041a240405040f1505150301020c0a0b040314030703021e0406080a0b010e03420c0904060b190e0108090304031b0905090d2303060607 64
    0x4241405000030700c001c00206104081908079550f0103029150341ea2503c2043d02480601c00c50b0000071418290b203000d040940c840c5800c2401600c41400c0c00c02c0700e4680c400c0621001c0e0765071054940e03c50420a0302c0c03025162035203102c071080b4000e5141094411409948919020b0080c21510851011904060103400c10000c076800810849407039160440d0060000e40101c0c24000340328290001d1005c0220885007142c0945102d51a8080540c903018591401400e100c000181480007a4a200100b50307001c1195a00300c207003018001c44041050302008610505800c0c01203190750358042c0d40001102c5511a103a400111903280a44a144031030000b0050304059101485003100001e075502d0b11040010500c40c4150140c5625581200e40300045484031000c4580b0805500103000910010314a0031251f00c96180100a9422054840ca41c100c103c0c6e00540d451485a4401e13100c401c112074011003c0c0e142400c0d042140c4000440e200041005440001c209920424000840c003080050301601e6 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 282432850 1250 282431600 282431603
    0x6020d06050d0b1b030106270b1605101b0f05090418030e03070b03072d030203011707030803060d0302030d0903020705040e07210f0b07120b010e0117070c 68
    0x25264046001e05040241c1c0f5000c1da59592040b010106100e00719a10a08481c100c1300541d030703029200d00c40b008204e001c0414010015694440820000411809030406081750300102d0707403000e98080c414030380b0a00d4403030410000200da50808000040c42d4030700603010981c2030031500303001c000b00c2c02021007120b081c8640d003192a4071038982588018880c1d005012442c1503032181c4c0710700703a200380010100740ea41c03821403145415600c0b0400000e0002841500f0380f0390081058130600e00340c6085281c001d03295410220380080040e6002c001000840d0f0821410f4010690b040c02030002c00d400d54030340d40c5007031200401d0b450242a664070100d040620030011164010001c030b004014440c10b502d8000d440e6905403061a201c0e5061080490181002091030412518400001290724858001440d001207165200340d44034070440c0442004940c0fa00a0144540829034504101d00742000700a0200c440d1a125a0304201e034058800348270381d0304598260500d142d030a500d00b01a588200302181d408061000 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 282434100 1250 282432850 282432859
    0x90905030d0c180305060612150403270b1201050d0302060c0313050613030f020d0905150712080103060f0903051b010e0a14010513050712110a12051c0c06020d0605 72
    0x20004c1800030120724140510821202c0002080468014585d1501003c402070001840d9801040011340180140d802c20140701c180701d4a80300c80d250a01c88418200d50080c40d0400c0001400318078686110342050140200303c0c0c08003890740560300d000b9a03a410090007411076240c0040411140c00002c60480c0985904c98202c4030103190a124a60102113421130444c0450312000110851900200b503582c42010303240e89298a181c5000204082c0b001c41e41803904030303d90104103403c0810184680e29003007003683d844038202540342d440c01208590184800011342c914044041d000264003404481c00c01d41e80c211071281c080c010018940c0141042c00c1c900007a841130500c09410800405802d00c120700442000300542d54903100700d200c48000b003e6004280f504004018000541c000040040881c02200c001c50800d84031000702e16075003d00d40120a1070003020b1a02d000308202001424000d0200c0c10024518500140c0054010b19240000402c6290003148801c0d242d9400d920203001020001c0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 282435350 1250 282434100 282434147
    0x120721051605010c0f0509032a09010f060807080c19020c10031a0306091c05090307120210110c0f04020702030d090e090109020f0103020c010902030f0d09090905030d0c 74
    0x9070860003421300040d40f0010400300c43d40418140e01410680b01003603005000341824030054089001c484861038140b514600c415000f40444d51962070310070f0301801e01e401320608400d04050016003100d00c0189400c040140d40410006c1031080c45040d03c00c8018940b240762424030404005038145000b1071103040e0401400d1086000d03035541504a00301c4040c1103400e603c10001640300741501c4020403190304034503038841e503454100303502594484410500e61b80b504d507042c0302c9101e0020313003481c1030303a880031520044601510382949012280d05421018504160502c90701980e03600d52114104800c0a101d11454800c2c8161511950126000d41d5402000d0b1080403040c020094003a24090250036000c0142e100015134840d014406e085100340c00400201d1710605000044010358016040c0301125503c4590032801610108086091001c880011b45260030000c03c0041249081c1d9003c0116207040c5901c500114501000320348110944102c0070030395800c0040d00b592680d44013001d03205400500c0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 282436600 1250 282435350 282435353
    0x130204050910060f0f0b0f040312030603060c0203071106030907031a07020c060403080f07060f0906051807050609040c110d1205010506030402060306041e090c081207210516 76
    0x702d510200c50361a090308104160f00c1c3c03010010054800d004601d06a010301106100c40c42004001c0c0c81c01041e5003c050b494644c690342d9400d81070a542113040040b035100d01040c410411240102c110707801482c8000c500b440301c55180d11940f041c805030704c0b500822001010030b205140030701101000e55081540c00240340d4a800088205283c2200c0780e0005014218503c82030340340002c219801c81c1e80040c03002d4107060300101c4288041d4042c40045905a941d4206107000b2842c60282400303080c094000001e40b403422503640541000d441105281940011000788800e5454405445a89109550005403030120181c192080d59038103520b9030031841800200309032150f02401d080c402c0c2042c0c40040c80680da88205001150000343c0e0020340c0000b003440014041d040c00d9000b0310b0180c009608001261180c2e10350141100e2202c4416a03580c80e0020382806444d0b420030090070341d500c002400c90304d4203c06480b80c2006408031081d5914840781050790710216442107082e59040060604e44d1002c2048a = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 282437850 1250 282436600 282436603
    0x30d060f051306030305040e19060306090308060301020406050406030f1d0a0309060509060901030f060e0a0b180402030a03081e10080d110d03090807080c0c0a090e0705091302040509 80
    0x40d4801c1c580305a00070341e01c14122a11a000b4001103940c5511b54505103410300c440ba800342d00004005408004a5038044e007001d8904c5e006040c0114060107001407100c00c00e00340200210002042c280c0a40e00420042101030fa010040301c044480500e0000b48c00c80c58412088050b185035003d030101561015020703010007101040c03103117805101e61552441c0541d9094265001d0150441d4568000c0e400d00c1501c140c2e500a800100100e0215100054001c1d04c81030700908074401030322044585942c421840c0d0f0030381810030643c8000d47c0c2c00304034003105181c035900182c0c1e194030341c0b0130003010001c900c00841c00da81c0c508148400381020441d0460594680309141e20760440c2e1074850208203202c3d0030700424030140185040e482040340760000e00658100c521060f00030f4070116008480d06202003002c40c000c65060300c050b10020b82d0882c06400504600003c02400f00e4094200d04105443c000808048410028071082141c0c42540c0e2051166110180369214821442000e90480d0400f0308000d49882d0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 282439100 1250 282437850 282437879
    0x6050108060d0309231c02091501110708030408010e030c070b09031501030308070305070c03171b190306060f0905090709090e0c0307120218060f030703050f010b1e0405040302030d06 80
    0x3050311012048020030501030320702840d4002c0a90005c80c6103012610144940a80c8005000d060400001d00401944bd6524000b150740c4010459007000c2011302580000b802808100080c4030001c40c103000600c2c541e1038450032544241c42d056603002481d00440d4030144009007401c1e42c1050716115541c1c0d2030070701400f034450031142e0400080ca040c0002c6c28403805082c03680081e94165590000307422610380c0348204401c01500007844880e4040f0b501c00c400030400014004001c92480030300b03070301600b504c000e8182e5130306410140620218000d001c0c80070340d2000b011022694211041c034159107800c0d00550741c64186802c19005070741003070b0044510003070009089a00304c0302a03084410b055070fa01c100304500c914541000350b114182e6407030100f40c20401510390b508000024081303021400e5500000e480c110030380d03001b12090f42008080703a01e400002e101d65007542c1c40c280e440040d030b070b5030040c074005d070180002c0c0c0400c1c4110340e9400840c0a151082090340c174000c001d0882009082c4c1c599021040014 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 282440350 1250 282439100 282439169
    0x90507060e180f04020d0201031529040806161211031905070e040f0e0307030206010603050a02070f030f090b03011d0c1612020c150c06090106050108060d0309 70
    0x8042e40c40e1031911080340c0e40410711440c03c1050b000403d4450b9801c000038844071610070b030b040645030302100e40c0d041d400b40c400300000d04600038600800c1c80905015041c2140007500d5490202061004008030b01c004140c0d5940403032860003070f8040b40003201e000d03580d00c880f001900820f01d20b0700300c2924403103150400660080800756500540c5d12034180c060001d4840031a000d42c0010144480c0032241d00b4290480d0300c803506282c00104804402d00c90083ca117800521040d40164003c0004000c540c0e01403041c9a044014110294a0000d45464110101944d488014100302070740c48025000c520400080028011501c24945d40c1c2d6900c2c4940004d0030a079030605001c007120040801c03211a170110441e0b0220b05020742401110131103480302d4101040b92078000d419401100c400c440c1503555280b85d500e903665810591031b1038240c400b11282c90510010042c0116030700d000001e0000f070381c011080c0c540c4070304120713840d44110046107021603501106610034260000f0701428502002d8801c40501c000c1c0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 282441600 1250 282440350 282440359
    0xc090303110610180207080c0105100e13030f110d09060f08010315020c28030f020c0114030705041d060f18040f06180b010f0f0b09040c03090507060e 66
    0x24050024507202e010680d00820300d0070985008000e49420302c2500000551255030043c01d00c00707144c844035001d51000102115a941d181c08001818516100e00ca000e4030b071441102c10140f0b401f081a2901030f092500c00307424428050300e1590400c0c480c008080500711218251044405041c0e80545101814010701d00454801d0b0342901c101c0348120845070480b5008000000e941141c18001d000945c071014a812050094130520304484e9004c00c806810311020407208440400181802031204840329640b60454118440d40c07200c581e070264605089003510104243d407030712042c000b595548100d0b400551a056000010744030700c194418540d1141601b6240800c58284d01010408600d0600c14601241210b140c04a0080f807401140305200030300c111000201c6411126035000c6800b2012801c0b50b01c000c10b540180700785101c0040d601e0041c14404050000380d41041c0300c030900c502401e00007078013a03982c58500c03003281c80c400d8000030751003600302068035003507074403072030300500841c20081a103004 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 282442850 1250 282441600 282441617
    0x7051c0c11120a020318030309031603050d4803050409060603060b0f07110d050f011b0905040908120103080c060c07030509010e2206230f0105030c0d0c090303 70
    0x110210003c441c0212080da002d180b0304584204107168402c801030b441030f0944010f0000850f541c40c00c0103000c0c032801103c414280c10920b50b140091610301d02080100801464808101808000002c81002e0720b0b0002041d24244461300c0342e5110024015185000d40d01600000c5001d2680020080041e01c000c560103104850b11380d4420b40545007140324003184600100141c43d403c0305c6083c092b24a4910803400c00d807050301e5500000d4406410b001d4107560b160000c03641d50080c01800d1082620031702000304000e0002955000162645a031441494043c617100ca0000042200b150200d030b0881c003580242072515612824544104d40182070084450b2140c480070400c504035040940340c20590564440e03140001c440011103440000d070880c00d80104c070030b0030448041200702c1c100e0088181d032107000048140c40c0200d1420095281c440e2803003d0810140401e00644030503e40c901e2102c002c1c00c0540c1c3d00e40380c0f4031f01c1d5207582c803c81c80d99000803841c002d0301d4148030b9880740d12181140c1c003980d03a1554 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 282444100 1250 282442850 282442873
    0x3170603010f0203130c150c0b0702010e010f0e100605010918110304060b0102060708090601150516080a090e100e1803193b010309050105010e010905090d0807051c0c11 74
    0x1247c861022040082040b4601450008810031910b80d480307601f80c8004a0320b1800c0390115401e4a0347ca002030310b0801d0300da00403849035001c100200f11010000c0e4405100d410b1030000040d020b250140074103060715010094400440111350000c0308201c02041e081c40d40ea180900b0300c88010590408454018081d00000c121072a00c2864184d0040071400050401c9900e032200c00301031040c0807043d50080c40414000706c401303e4050a9108969805002120796035140000c00612007100f0b500450075000282d018001c2401d0010804011b45010248845107070312010f209001c410455a01015144000034050341c1c0c00c52074030605a4180f100d52900d4010190a1105c190003a281700d0000706040c0e00c0541c3c8100d610ba00e040580c68000c41814001071034240c6803101425110243c0100d2107102010703004000e61078444c4030340313a8483e44440c05864643e11042004080f03600242c2000e00700200403808068001444a01e41041c000c844c1d010030500c43e903500040d1200014495104660040b00b4503602c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 282445350 1250 282444100 282444119
    0x40605030d170414030706050415020421020a180212070804030c06090312060b04171c120605040603030e03010f0614120106090c082203170603010f0203130c 69
    0x1070301d22a0a844200c00309070012031001d0320703040042040d00c41902c0c802580b906940144002d091680c05841c1c0401d0707a2805081c850491601c5924002e902c1b44108020400b6801c01c0401c0c2440300080040610310071030b6800021501c501c240c10804542c51807141c0d400c11104164002c01c40d550502060b070034599a8144180d0b038100c0c0456000d0041002c2e80e51039000074074140d100c00c0348644a41014031100d140e00241c0011140c99410250046c5c000003024044400300d0f07013020851454180090a10501882403544483e58001c5540280f250b0010420803070041c9400c41c501500e4058003c000303903581ca040c020101c80c0078452513806940b8104002240e281c0e41e00030541503da00604e21002d241c4024103100f4908050081c1450a5503900f101141010082c05080f011201603510f824090038075500c480b01c442c902503a09101039800300d80300c10000360841207980c00a8000800b81e011540c5080c0401d014041c28043c21800510000070816200031110a001155008030800c482c0305481c1d45109 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 282446600 1250 282445350 282445363
    0xf0602030a091203090306050709090e0c0109061101060302030a210c02030615041b0f090605030f010b0c0313030c060e040b0f0f031006180c030506010c23060c03040204060503 77
    0x1000461000d003d220040d000034102c904540b081c64190030380381d0389444a40c21038205803036110000c2c012401c00c1001e6100d9000f603a6003a071030701c2d0161190000400000c0c00c01360083c4195801c7c010203603d052101107080d44148000c54000d020f55503600441d00c0c0401c8420441d0030303c2c05803082c1080402c0b01491003102c0c9a103100341d02500074292038594841007101f8000f8492030325805a02c4100c0a840d00304101500304070176031113031a201c000700340340b88000c0c0503442d09802c90804c1103814070801181050710680b4904480d8601d000503500e52010340309a0451158214101c0c041c1c1d84204000100090440c840c001c131074990340c0d051196403401c0e08110070b840e180c0840660150303047d5003400192920b40350007555002c00804950445445a10b5101502c0a40d8424065080350601c000c0c5408210b016404103081e86260410442c0752010000e400c0104c1c101d07018202c40500008036600d00681083c084c400b0300300408941da50301d02210820140d80c030460b822800345082c1440010300d400c00080781c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 282447850 1250 282446600 282446617
    0x1091a130602160f0b040c17370506010510030c1710030c03050c1305070215040c0803040f0302100801030c060809030f0f03070306050907120e07090203100f060203 72
    0x11100c1914640d201c01010b9085250746020194500080000240c400101c0500103032051454010900d89801e2203507000d00c0641c0486040a0740440b4641c03010400300721800848807500050715202460608a10343c0340031080491000b003240a0110b051083c00036a80303040b20390865070800c1c6000040e40840c10f44124802c00c00c003103070f078000c81c00d16004c40460050707074000e0781c624500b504c190340c03030b180d890010340e031a40152680c7c1c200e241d11070107509101c0610503000110020900050030043e10007907540d40d420018082e400704000100f4104800500f80340300920041048a450380e032240362107800c25045120417031107105040d81d641105d501650421b41200d41010b484ca0740203207080d00559600800a0510b00140010170031079640841a02c054240030103e503100c00d0f12480e10b030360003800300d400c9500050b108a00000410880d5540403000c0141c3c0701d1050b0000c0f1312900740c880c849103850540c0e0400d529140c0007100f00107a072440040703080c00716000300d2548034070540d80d103100f079840e0f12a00c0710 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 282449100 1250 282447850 282447871
    0x812060a051e031014010801060509390c0c0a05030a030e0d03051c0501090e1204061b060e1f0509070501050906120703051807050f09090a0b040501091a 67
    0x80141d00a6000030382c6071940c4034003500f42d921209081880b4000c8490b08404848407681140052100c070f03509124243c041c000070b9910f80302a080044000095840d542c54484816005c615107660900100b04031001103000c9500c51900c80c02d601e103581d6203a02842c4206805507503017200000340d03840c1c00121915060f415440300d0000346003000070300040100001003034080c46800c0010300710141300704001107c040140e01c80011554103000d007000a0b2605c1d900068042d031300200c0c02a1340010341c40c0c1101c04560356800c0c03c55501d01d0000000e00342c800a1500a01078a1400700c00b0380090304042119212540b5100070060198200403240080300d50980c1c030f041d1700e03038020041404103500076001442c401100401080c20700540b1180f0810f10801100c0000002c1d881c2d4040c002e0804030941e50220108515020b054654101804103800784c0c000c0844501c0781c460304000c1780c03852030103005110740c180d005038580c95945413a052040c040d0107005400c40d0548034841c00c1c098503019001c58a4004e0000d102e = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 282450350 1250 282449100 282449119
    0xa0c14030406110a121823331b10020309010506010504031a0c070506130c0b040b0f03040807020d050109050d080f040308420d0c030b220812060a05 65
    0x10400c44404004582046101b040c1c000301041c1424041450064103a1109a0070706c0c500710407007404643c40c0034211380c104001184580c4c15404061944043c24450322040e401c0d29083c00784ca0180c04500340340340300c201074001c44041e400400b559400441c441c0d00c0e200000d0080391241801110a031040e4440545013100d500d102031013400720b03c80c0f0345400400c400c034030b42c0c1804242d44510b414945c003070301d1103451120039151600800032094414001002c20b800030074206850900309610340c1c402d40f12040e20f015400000501002800030940eaa415009450031041d01014500b09008146506003074682e4441d90b0460350001d841103802c18031680d0f80007031284031a02e0710f55040d01c4442015103500c101c00c16203c02039000002c8190800308403aa00304d03100001060350014000e01400543c00d8501540031b01004c40013041c401441c0743d0440e98000c0212200e503072080c801030f00034a1280f1a10881859040c3d183d400e110484005d000c4018202000c291170361151410400150b03135038840e031500414000f = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 282451600 1250 282450350 282450383
    0xc150307050f0706020307170711031e070c030b220f06020306281703030c04060f09091805061509060609041d010606020708010e070b0a0c14030406110a 67
    0x75006410303103609140307419062a005039240710681c0c0048038502c2c00581503d036108034490b03100c00700c2c642044c2d45042091803005003400007030b1a4031407040303000d013900c0e400703e113800940e10840b0448560701e800650000c103c9449240410050794251400014002c3c071410083c1d2544111007400246a4001462120f005440d980d403400303500f00505081e40035a6520492400000e80902800d4180c0c03281c2d9641d58031801d041031200c4040c10b2004010060348103000304000d480c4082e0440c3c05031042420500949203000c00112518034160700008422410031880056010094418140092068003a1607895842c1c0c22400040178001601e907030300113192408074400d410100020300c003200000c0c00105411500300425021103508a11142c100d80d51a1010020309134140b0580c0083d1425800074803c0d04e00324861250740d01118004c410760b0480014030128424013824802c0342d2254480c001c2c045400a11028507200c1d0420b126200100b00c000d00300c581008804682024407d9102801c0442800314 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 282452850 1250 282451600 282451607
    0x702011e050a0b0405010e07020f0622080d060b030406180201020a0206090d0b040f02010206060a030f0818030d1e14040b0304140f060a0b1203070b060307150801080c150307 76
    0xd403415040c256521000f040301c0d10745002c0c0d103010304020740d5010481d041000d0000d1900e180458070341120381204050015410043c2d80c10581e41d0a0345000450710b00e281c0c106070440b4880d1610121200b85040400079501c050030b0080e5101d10301803641080152124149012222024031009005821401e820300041ca801c1c8040c0c0b000e124081d15104c07180d200d40d6140041000141c8069840b418400d0003501150f074100700280c0d00202c1610403d00350303403541e907502c20703c0c0840001c01800c0e0300010800308101c052501071043d05080060880c1c5240081d00ca0103820000e440c1c0a0b00c820200084403070410070b004070f5081409145445402d40390515241071111a904080c3c401c07200b151070780b121188064010030920492040704e1000d41050b04200050380c04445079019403a010344a044403103001906c010040d140c09036000060301c00c8941d0340c0400a802c0014039000310303010b80c0e041c1c0001403400354400c1200303044c1e5003141300f01c03111071001d90f04202c7c8890b6544100000c2090400005040318031 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 282454100 1250 282452850 282452861
    0xa060f08130303061d0a05061507120221030f01090501050a1a0c071707050a0509060405090a0203100f0e0106120f051203010b090f01110d0309030e03030c0d080702011e 74
    0x2403034000b4449840b54405c4a100b6400000303582c04160140c140510142c907442003130341207001128900c805a150300e80c074000901501501620311182001c040701040d009004142d885801d6203070081400d0400c8107004e4550b04203031441ca070402d280100129540a07a44640c1e41a50300003888003880e14074060302c01c445408826810340c01e4101c01d0100c1c2c50744860400c51070001d08107400c801c2340e4483c0101641451b103d000e5005e580703d020200000c101a480b42e09105801980c10b5501044650360a00301a00d40200d06a00a41502c144c40d039444203503100340e2240521b40d18002c4240f004000041c40a42a80c031075001e45c01007010b803640324030300240c24000000f0a0520442c169444040e20f05003000170307030308268000d0401d26800100341190f440e005044c0e4101c0442401e1100d40c070110450780581d1035501071004418956101d000d0014113000325070b40f20b0348940c024100c03982c4010f0012003070303112054410420046503d88000c244100e006000e450b12040e8902101c008068142100c50007604 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 282455350 1250 282454100 282454103
    0x601120204060906080601080d03090309090f0e100c0e04050105060f1b03030a09021810050f0301020d1113211e060f0504150b0306040807030e03030d0b0a060f0813 72
    0x10b07515400060a049507000b803a00500752100a01465850001441e0921200c022980308042ca410050400290040c140b0070030b440d0700d0080007802c0c10380f121500005281d2051014618403e00380b4a240d403184c130b07030170900c20008141e6030313080c20800d030405000595600f80211a4014014460a00d95071080e802407c48081d00c80c044000c1d041e004413400e41164002c1e6003a09072103403261480c0056040c01c400c4c43c503042d4003028103101035281507109000c00c0034141c06406c0c030840100388c000e04540d4003501a00d44004080038108151001c8010400d5503500124050a030860085000030755840d4103090003082c0c10700000d00c0c500c500c2941d0354001c2160091310650351035a038111290300c040303892407140e6040d110b55101c0c00102803c1c41e040c06150000540c001040701420500083e40f60386020446030740107a4800009a185c200c03514060b01c05600c161030441c5c051002140c04d2400d00101d0f0410200c1c80404d0342d03010f001c19245c140860f01c42c14000c0d0b90002050340030011400301c04080304c0142505 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 282456600 1250 282455350 282455359
    0x3280201150f1d0c0a300605031905120a1701090e0105010b131a090d0f030905090c04350c010e0607030e0603070909090b150a03030206011202 63
    0x10104611442000305140c205064600c00842d043c443d441010444103640b00c0740d80348448072450180c8101e84144141000c507020001403803c802d524840d000d0f820303d6204180b800c2d001840c071042d01714000400c41032042c14402c0c406c9111243e040c94001c0d0404002d00d410001a29032580300d013511100030f034040120303401008000894000c20200e15400d5074041c141d00407010418024114009080d58170680240360b250b4810030800103904841d6000104864500002514404541d201c2c5c01c21801107c1c500d40c0c02c000380e03507011000c0100000115800c24469292281c0c0a6203d00601901d07110444030018040030400041c402c0440214030186c1c2c0303501c840000380010131180c24000d008040900300c00d919520042d220b24032513800440c000c40202058600e541014610f8230000d16030400950700d90f003c1c0c0000404582200d11074007144024203d82c000c140b000f0300c4a80350040c0080012035a102c40c280c1400303000b01051a040784048100ca815a0041141d40d09115030000301c1da0f021034080f41e12 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 282457850 1250 282456600 282456611
    0x50c1b012a0818030c010306060f03270c2405070f080714010203151903030f090b0c0d1403091b011715030613080f0d0207020607060902010e0303280201 67
    0x1924040040428080b1543c826000e03c100c503060603c0c006180c0681c034181810100140441740d07200c018080502c00500d07002c902c0102140701041c0b05100190309000c403c0d202c6000c03006000741c5c12002c504640001402c4040501044403105d443d4225400c98000074808101882c081000300e442618058014800c66160000c0303542d408a15403403002c00c10105940200802803c03442e00c40941d14690000d690110038400c843c0c9441c0700b81e98103408014203203c1c08500c02040244154002c4011b861030000d07140d07030391081da414a6500d0750015080b90000d00070100c581ca03c5c1d0035000c19240103240780782c01020041d5518417280380d003c01c2c4511180c1040351801310428014107450080e40a008100390032101c3d010114280360070000009d100210402c807600d0722500107441c0a04540003401c2d411900c40d10f5100d607a01d4800a0300c11580e000c1c1d808600801c407503042c001c0076809107c00701d04c04d0302e41c00144c518010515849021313031804104030b01107014072904101c0107110005a0f0b2101c42c400003a0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 282459100 1250 282457850 282457853
    0x20f1221070305010e070c030503130f140a060501230f191d09010e03030a0b0a03020a14030d09151b0215030a0c030615050912010606050c1b012a 64
    0x200036008685000c0000d44490041003800302e909265500100c1e58034091079001a0741d2000b4003184000b0308021841400320584d4014403514048400510398440c14242c1409105544213654290340c803010ba91840c80c000001842c40c00950002125803040103d0105404c0542c0800180c402c402c500c0a8004401b01d0a800f00030b0420440540500080599410500b503100400c0e8034480004104106681c5005080c040c00f61000040c0c0358000c981d800041600c02c0c540011031228034440e0300c000c1d005020070300b01007007010101208142c3c00c4825400c0b60364030303d50a10120b561002607c100c15804002200c2c0e1080244101a0416080115002c1403000c0b0080c0d804181070217400d0461207084600481408842c1207103003d000c0e82c0a61918051001508084caa03554240303103e04a0000e00000041208540d00c1e40c008070485011b814000b000081e035035440c0a40280e001150114030381c01885224041c1450741c1c500610141d10607511200c5040341c2030211000d000f42c00030465800d944c100903e40 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 282460350 1250 282459100 282459157
    0x50f16060204090c110c03210d060509090d020f12040b0a0306180903030b010c08030109110c0d050903100e1207020102012405010e06130e0c070b01030309030215030402011e0e0a0806090706020f12 86
    0x3402884084003c00c1e2034053b602c002410f05031208a034401c560480c64856540007038900171796065840300c41100756541040710f02500103040301e0748050340014030700c1d880308280e803000c0d40301c07507510750203500d00340200c0300808011110461020001410010b090005000200c107581c0460a2208280200c5182c103608021aa16200107000040c00041c0c000904088030309040c48032040250080c0400c1c49440014160103031921040100c0701400d00b40451303a01c09682c405d40100600728400983d00c6c002c040030031010354420550380101e0f0301180e00e0890703071045030500c002243c0c050904100d15003141c2c0d05010303000710700d128083d00c20385940c4000d101a002207000000d04c1402103100b074648400395460f51050094900215511001c80213013032040201503604141d070626055101d14204185d0f010011054a4041200c03a966400880807840410700b4074000a80305d0007240c00b4000c0b100d03030b660f0380e00c030890b9140c45c01d1415401a0308100081550007048001070603162030b07903180900500722820100d0b03 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 282461600 1250 282460350 282460369
    0x403081f030503070f17040303021b151909080d090e0c1b0c01030f021606091b080714040504030c08070807061e0c050f16060204090c110c03210d0605 66
    0x540d0b2030400b81203a1810440d02c100e90310310016074403a86d0340c206807035900c01039292124910740e8a402c40004212038100e0317490f00307206a680030b03071104200c0c1c40c0d00c08a004803182d08501c00e44031010800c404ca010807540030020300340040420507581d4600440c14104000c0d22000043d240c1d84807000180080c20005030340071421541d101408004019852908000406460144e40a0340300d051040080720718000704030000040c26600490301190b00c5c50280b40c1200300301d50141d9441c0021503402004100f1100114100045032001d001c800310aa4941082108492041d0f4000340810342082c1c42e00c0000d0440006021154000c0c3c41603070402410391501d1040d214003800c0d04481c6070a60f110f03e150500309104034000d5941ca4a895030803e840c0b006804000e01c52054890518070100c002c00f020014250101c50107840845414002d18200e40030191030716403c04040300040c040c1d0001070707e8900f07000400e2218a503060540d540c4000c0d000e011004d0950140d480c080126488207404526070b140d240c00c0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 282462850 1250 282461600 282461603
    0x702060702121b10081609080106060e01030b060f04121104020412120f141e0c01020720010206060907030207060e030d240b0a09091401050a08060403081f03050307 72
    0x703003d5268100902102084000c20418410741030107446a4038660b000d407690340d018860b07035055030b0001d044000c240c0d0348400b26800a641d640c01d0050209100b0fa00465038401040c003078905001080b840400c0201c90f02407070a142e1300c0c0e46014441040080044103ca081c90340c0201e001c0a151100b002c0840d0603a440390300230070428120441080208240040356000d2440180740580011943c600000e0802110108104490a011038400c180c1000c0d040c14060300580018041d68171032034502d10718040c4d0043c440583e1080c40300c0d40d040300001030f109c1000c041448164080c1100e640c99904202001070060003070300401d0f90074017081e000103034188620180c600361900159180c2e01c00d140000142c51364100840c8550342036492110796007142c83d0142054a0b40e48644545844140d10120340c289080d41c000c0c1b50150a000c801100b0100c2403003d50b05a030342c2500c2164185440380203041c0c1d03c04bc00c0e030300280041c3d011000249d0102d01038900660300c0d0003101c1e0744440c09da6240c881301d28507000b6140 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 282464100 1250 282462850 282462853
    0x1009020304080a0908060f0109050907050303030a060501020c061c020703140309060405061f0314010908121e060105090409020301061d0603010509070f030b0a1517060603060c040b070206070212 85
    0xc3e800d06494021401034000e0103468000d0880c1e2520300b150080141042c401d0707040c2161a48089001c052051050402070803015040b40d840789419451074015005c5403045034054007500380021401c2c10101d0444440c4042444c074554140060740c1e041e0000c0d848820141c00b00158807032041000900e03031004601440079600140281d00303190810303034104080501042200324800d102000001c0340300e01c95000f00c3e5002a441108498101c21817130140045070b2005012030800240121403845101950780200041002c055515809074520001d00001f03444040c003047c020701c05420240750580000c65450300c0580041000c03503541d04662008240044441d003031048520401445050074840c041d404090360004001051400c0d010004007030890001070300038010f05c1d0000b20581d916400890300c1000c03a050b4101c005a491940002151180c0313210040e600403100400c1180ca0001003250140c041100c003149031614180c0c100c1d010b6800481c0490b000b440034488000560703a8050316240b003034603100 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 282465350 1250 282464100 282464107
    0x50105060a0e011406030901090804060215010e01180906060504020f04050f0901050907052104030c030201050a11030c07030c020d08070b0109061818020307240c0203030a0305100902030408 83
    0xd0812150700d001da04941086000030004002c1c00c966012011001042683c04580c0c0b600e5001c4140d02400c0c02480103082c840c00020b0000300140e002a01240315442610303502d0b42030f6210301d41144085801e1140c0b201c400805606242c1b921425404a01140e00c80e09001a002c2d90fa140403409980000a80509254001c40c040010b0f05007580824039100080b5900070b032640c102350003d8103002002e01488104100400c500400e0450705001044480d8a0020070031a8686894007c02804c0c50081c1203006500740340101d2010740c075074042c11204a1105130711505680d00c50240b00303e507400480d401c0e401c00c505200e82d407002d40c485035104210035000e008135a40e18851401e10525802c0f06a00181c03556180260810015a0941603a05104030150021400d078980b252814540c4a4111000e0b5250158bc5c1000403429400d0a818101e00d0f841c048031045041d61140640c0c1030f40c02c3e21006901030b0000c00101c02c2d42c9201e52f100c00e9004130140c440040c819164460182260000c039002c40300e920001 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 282466600 1250 282465350 282465361
    0x20a05040e150a0c0219020901060c0c0b070f1202011b05090604030c0b03011a041809020f0907200c090115110601031208010f140405181605040b1903150216050105 72
    0x601c12080e0140803006d892540c1606a4040f41c0084014442e0104002c88107070001c04205d100254100100341c141d00147d1991560700301294407800c25501255030302d00c8d002c00002080d0060180c030410500380884680b01c0401648256095404410025407200003080f001c8009040902102d0203010200d90880c0c40e0340c1003482e0484803107101040e010702e01006102c10000958034030304a030005140800e0115804800c3d2004c500d00c030241c800f0040d40140500104075890364000b40300c00744120030124000111181080d442e41b146580940c05400400040040c8941260b540201c91640c0742072821203403603a0050000c40c1048070a800842c0c1101d81860441e82c01030340120301f540549541c0c82465041d910b0240b105441c0078000355414001c07130321100092454152487c404088020840c240c3e01d00052014186141c84454001c45100c1c40c5802c00b50300039402d10000700c14814400f420142005402c41d250b030144000c0c0640481c82260b02007000d41410072000c1114078900d48614000714050405 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 282467850 1250 282466600 282466603
    0x1203023a0203190c03060e04052103100e0c0409060605040f08010b131a1e031b0312070c0b0a0c050f06160c0302070b0301030b0601090e04020a05040e150a0c02 70
    0x1040c40c0014480d0042c4240041000d0090071100b1215842c500080daa407021a800d03009080951f000d890000c4150003007005012000c50203050780c4518000360034207001c010310140301500003640d220b1080a2199018003c079981d086141780c01c80480d900302e5041c81d554008000135102507030010400140c0106040180204400c04580941400002407080c8808140402c0c03d4500c04051042e80d203440d00398401d072060a90114030310802011f0040002401c00c01c80154007011409a01c1e4024421a03005050000804004c42d45421004000e03004401c885000589260014001594803c22103030b400220703030721303520010442c1c03c0150b10740414510440c01d1403070419200754080301140d000b410400000510366058560030301041c2c10f284101d85541e0401301c0c0b805104d90421800c42100000202c02d11259410251003403809a0703540a159842e611a00e107401000d540c002d400ca040000c05100a251980140381c01d221048126100c03e00104e8030850001c03400c0c1c580002c801c0c1d6030810161042e50 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 282469100 1250 282467850 282467947
    0x6140a0608070618120c0810022d07050f010c090806060d030e03150112140a0b19110d021305060a121805061006020105060d0b04110607020a0305070f0f050d120302 72
    0x3141c160460504038400b031076265070f8244400c003030ad4017030030349002c42e0010700100242c400a9410404a940c00000c05002600a1503480c4031100800c45405001503544400259a0705c2004040c1103c6000e4403140c0c0c003a2000ea002d01c20503a0b041c02141e207a002451030217603d6900030f04e40d8040320880c2c41243d041800c1c0505107003005280c00e1b045440840042500d403446aa00b0020800507810501c52010580e0f0050a200e1560f80345007500103402266951a030b009040c0c8406e1010380c0e29034440da0761003000450f00c82e0760300d10004942c0e401c007510400401a40521f1144034035a032030b07040741c81e0143c0d501402d00760102d400d601c602e01003a90501400e83d0910681d0782c49401620721070282a65622296000d44008000418040b41032a190305070b525460151251254003070008000345031030740303849920740080b4059403601c040c91440005100640c07800507021110301408580046680c0c0c0c0b0303400c440103c90754442041c0b54013045840c4210b026175042d80040414800301d41c006040080880749501c6 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 282470350 1250 282469100 282469123
    0x40515090c0918040f030e040b0a080a170a120f060f03030507050106051035090f0d0e060d09050c060309030703080603010c090e09160306140a0608070618120c08 71
    0x40904104000070b10050604140d0036018101120f07081f070f8620029000d445000c140581040c40450000340200e000284050f4151140c0d054800030184403032a00064041e0381c0f50000010159002d01e0544004d03540917083d5491201c1d0082444d9444182005039000075500c04c0300000d4002607414240f10b420700c60040503240c1229286202d00c00b00070300402105910030b03146110125240141207204007a4140f140011031080741600e079103401e02c0d1883e140d1000c00c0e4503000901450710742000241c0b0034600c4d0b04c24a200140494101030b640b0203014020010282e0442d00b40c882e0050443c040e94401c000b5520482129009643c0d850035840c1c01441c080001e00124042e130b0403c03c003210300781e8000103d41d00750340c5010711b82003803941d660310080d10b04100010810210100d0010100521a00da00f043c0c90021810f040b1503000d807961020441111a039204142c11604072440a20615116111050081c00c803021191001a100c02e85018004581d020417601c0e42210107080002100a001089519 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 282471600 1250 282470350 282470389
    0x70b030f160905012312010e0405060a0501051305070201200a030b0102010204050901031b03080a1706090708010e070905120d030b0d0503070213020d09032d0e040515090c09 76
    0x10b0b0f24010002e4001244801800100320002c1c0308031802e020090281ca096205000c0005100c1d41c3d07a20031554041c4003924141d80e00d00450340080d1352407801f4081c1604a0f0702c007414802c2811140344100c4000c20010340080110754039a42a8078250b090303008000e001c080c014030010303034801c03040f440a030807540501c3e00da906590041c00100000d0350354011032411290800c21031819040d5044071200d00600750381008001003c00303d4800c114030342c00921701d600c1284404a41c0c0b100d4440c0d60400035001011202500040d66990051007254540d091041d000f40c5142064154135072201e000408913081006120b2a95102c80d0350040c0c0250305000e40c03070040d04162564507000360079841c1e054803072095070340190080750125209100107000d50b04950a035a5040301c1007101c0e100350310f401090702e0b0814070b4401490b0f045200d080190707500900240000f200c9601d41c1c40074200301c0c200b808041d180090801c449140c15000644060b1907141507148150407258185584d00c008000704000300c0d2800d803180406 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 282472850 1250 282471600 282471617
    0xb07020c011121070305090607080304020405071d010e040e0f0f19020604140d02041817030603030d110c070b0408011808041206060305010c02071706090d080405070b030f16 76
    0x3d48011a08074200364240c0229500d00e90340c241528540b0600c00c8154128030001004401e1102440c040c41c05a48202e40034441e070740300c6e510100c0764500320a65805061115158103160b6602071400c05a000d031001d40085420001e400c5001d080c242c082c1c2040c503031608840ca0500c40320005104181510044c220041c203141d209402042d841d0003a8081d01d0317803401500c041a04c481d503503881300c03c40096000b4000d11045109110300500c0c060520300c12902c0c04090a11076526116001c00d413489040094011400c040c000707041c50010300240406821035a104000304620890188507810140048000c000d81c1c0314503004409003100c1c07aa0500218800d26a69541300003041201102d0880f1601504c41301c40ca03c203401c100004240c1e41c0d00003000c0b03619040c81e200a50b82c010444508982c045020500741d00079101d1910345440d0100e86c201107580154410b040b00358003c26149801038081c0048500c03090b158221550140d0081d81c0c0380101c40c40b0f100c200b00010080030308a611100389490503001 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 282474100 1250 282472850 282472873
    0x12071b03110603040c1a071b051507060e0a0c1a04150518100905040f0203190c02100c020105060f03010c020d050c030f120709170c0f0406030b07020c0111 68
    0x32009400c01e00791048070000089410720101d089004080e02c1e030103d52003248400440c9008041d03000803001c0f9081c082c0c03842800d0b01c0100004010381103940140c90202403248401e800080d6a01c281400c852550382e51070701d043c0300001003007003007140c0344900e030390744c50030f9042c4010b003500c03c007045081440e102000c01c02805160152007480c4010101428540c0d1980d00003030700c0700e00000034514015040102000d00c0c50140341c0c4078603404e003212020b4500300410f05680d00b400040c0d2004a0b007a140c03142d44400700020160180d03201ca00301c202c1c10b2042d80c802000340d552400507141000030450050b134450701408a1480d210f0150510120201c0003004100600140030351a510b030490004e051100c08900603034045c0341031003160007910200c21034554805285022805240f0213031503a500190a03070744007040b421020b151021154039400300400c00c07010300c030707013005003043d000f10101da0400c0d22690000001401840d02c0d030b0003a459900600803403060340d80010300107083d03042e6103260b9600610182c0c4 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 282475350 1250 282474100 282474113
    0x16050f130308071a13020405040c08030d061502010902011b0203011509060312112d01090506010801150302030303240616051002031303200f2112010612090512071b03 73
    0x216200e1b4180e1300070400d5a2107040c40101c903a00e0343e20000050000040074156010a54442c0c0190741525035002c0710f0309428a0102d00300c8509944c028041020141e05405500d02c4801000d10a44014004600c500003500d0f408140000e5520030401e880d103d440c24802c00a9001801501c00164a021002e8410410065503200d41d8811085180b00c8060030050031a4006c001d407a40d81c00c406402448036017243c3c544140d0b00c4609100d0207985500e4101416480c10300070104500f1645c00800071400c5458a600c0e4042c01070815035900c0f00c01c0380b1800078071842e4a0340c502a040c403112803890704520034980d09010342403890802320000e038648108100034508240035015402c00d0b4062801101304c01c000101e8094480070645c11a100d440313585440317110f440300020441e010450114840360f001010310000704080c050140d004880c1d8420100602031644181c81200740d4440200340800c031418113031a0582041d016075003c618003000004c0c41c1c000e0017640b003031540700c244040d6403819154bc13a40d201c40 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 282476600 1250 282475350 282475381
    0x2070f020f03010f0c18050906060f0a0c0203100501090b010e0604090c0e040f06150507030215130c0806100b03012409030b09160e16050f130308071a 66
    0xd01c03426002050000c0e0307441c01d503c80e00320040350640801850918600c0504055040180403a01c0c40d07003020046080c1c100780c0a001e00400000d000281030941c800c01004031a0800300c248810400c00c1c1c1400750150b94100403081020300556400101541002e12404c1030b195401301a906200c00c100700c0d4040c40d15900308aa040700e031600f200041d20000c801080b100d00d800f18003083d501038181040800310f5412540042d0031503010707155008240c10881c0d41902c80340640c20703018025800c105058001c82c1c0c60300118076480b02140d010040720101c2d42e038070301c501c00d00260040c940e2940800e0400c0741006064102002400310308440500755850003001c6c540c0310003005001e1001c0c065903c504a11135002e60155005140d1112107240e89140018a03540c0d144644052050420405840001c0c00c0c0007072840c49018407604680b0f01601200100241c40c030380c1c80000d0454070794000700640b18591a80600c20b0016610644000f60b4903a01401c0034a00303200e42c4982c05550446036424814050803003881c4 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 282477850 1250 282476600 282476603
    0x80a06050123030703020d091211060c22051002010e06070207080a060b1207030f02040f050f040212031c02040306060b0c07060806030c09010620011a010309111f1202070f 75
    0x110f42d90b69242c62049021b03001c2c0e58101a015420083e00001300003569054001039261395958107946005000440d40c1e44109407000b0032251000c000d030b1011424003407000840540a541001c000c03603981c034040340c402840c40c2d10f030000507550385030114003040090103007607040400b03403000744262030400340166142e45100c1001001c00c2d59550100001c0e40f14a6880240401d51000392042c456403820322036070513518254124465850001e10006886081c0701d4076020f00d030760741c42c42000366646a0a00c40300146441100f2a24881445610b2015418130706513000d0b1501d070b59025880c0d40c40d6107401c005481403500295404041030141c420301303950002d540c0e4111159482d044095449500100e07003880b00301c001030780e04011001d0003c1f0f8001e0304404400f840d0784241000050302d00c10018101e080f03440414205440c5a10844008007a621030b4001e40c81040c045c80000300d041000c10000b030914804500240c00701e0215141280105810454042c0d04400704c601c1545405400d544050340c400030147c0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 282479100 1250 282477850 282477917
    0x6180f010e180a0f0213031a0103172a0d0801050306040819170f04031b051903090801090b070801090e0a0201031109030615030d03020408030d0209120607080a060501 73
    0x2c3c41000b41d0303042021503c000c41d07000c566441c0c003644010080980d50006440d05a0750001c0c5118540c2c103c18002e040701c4d0024003400c2c207074010b000c0c1010240d00542d0b000004640e4140c4401c00e02d021000152000c28003080101840405140058070507001640305a200f904018100800b140c100011910a903584410442403c3c0b4004030541c2c2107910082d58204441c806020401515041075640d0300544c0a80c8807240d51451200c006509030307451403c001c00d0741c0c10130700a03042c0d00001140c1081d400c600c24204120981d032500040380c00c654180c07400b620303611150800e0210b1141c010070080d01401c00c0348028407010285c0b540c000c0d500d40d120786c8000d040603038030300314000b02ea0b03810300c141d5824140080550710a4200b0350200501f031054484410b20034000c3d501040748803800ba2003220100c46504000e14184140481544000c0d04802c40441c6c01002c1e81d9843ca5555030180009442075816450788600741c05c0c54a03d440840b011900218144a208032005000301080384c0710700034210b000030 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 282480350 1250 282479100 282479149
    0xf06090b0d15110f13170f070608060621042901060c020109171b1801030807060603141501091a09072c0f01050306010c080a030b06180f010e 62
    0x20788207400c0e10a02c40744003000c2c1e501003804042c40c0d41000082c2c040319484007400507000d41b2075543c1d0307403503490b5010421681e17408440c0405c0381d5806060703207603404100180000d0500d00a5684030080d240b042c402d04004034149402c05c02005480301900710b100081d035000e241d0b1200301000406d0511010300517038060106071150b0b80c04580c401d0118801501d824452410507203010144266500340c07882110f0075414801581c4a11801c10910060a8801d50526544907910750b466610041d40101c00c1940c0e61601c6c0d00780840424000c4038030108a02c50707140240310a460148008241034411b0300242110350809920000b03111100c244d00704003540845504e4000e4461940c141e0310b040112403100700c407044003402001d116294038440485100d05031402056400418011a0710348400c6540c680800c5440c1c43d0000841c02960140104c00c03d40e040000b01c100102c400207031170350030159180245143d20307e44107881c0e00340180300c10700b0080c0030b00b8001d50080040c0c0000d12400014510030380c00000e5034 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 282481600 1250 282480350 282480371
    0xc03070302160c24021b01140906030718090908040303031a150405030f0705031f23090118030806010f0c0f060212010b1303080702130f06090b0d15 65
    0x19910350b8456607121500c40c070000c1d500c001c280c420201c20038254040e411454a1a014280042001c0058060040280000940fa440151910880d00d85c0b000d010907420f02031281151111001140100150f448008905281c1c85141c1d040d805213802600240707042c49800030014540300251000c0c0c9606007400300b4078400c01810b4240e0b00300307130598035580b1141341c105000c031400001d0020000da03070094040e141e140303a500d940e540d61b400c07140c410542c142c0e00c20303000d035420940841c2003149903404600020ad20901a4600c8518a400b010803404801d00e800f014030290030b0092050707005401d01c82e80540d10411054401601500c402009603061024a00807071481a00c20356420400c540d0200720401d41002c94188075000f03400071000c030590031030030000102c0d07100d0f00f810503a40780a1004141c0f54489080d9034400305140c000c5e41040b07030018a041c44000044825004d0b40c0c143c140e400c0c100007069071078141709205884891400c240906190b6000201052242c01070a2076141044c40c0819501e802 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 282482850 1250 282481600 282481627
    0x5061b0c1b0310051012080c0f030901031d0a03120e0111070c0e040507030221100e160b1b031c0c03060b0f0703082205030403021003050c03070302 65
    0x28500210040e00890190449000c0d003900d8118001d481035045510341000703d0106004c84d07406803501c0401c0f07000a88100100440b006020111600c104412400c4c0351881a07110300c1d100050505ca03881d90008100c0d04215681849105c2c3c00b00c0c400c1c0b842c00300000d021039105485a0b11858040c6c1007003d1410b40601100c600d4100c0040104110020052108103596a0305107030072a18080b1134608401c1000200c0000655105000c0c0c1d4101024211151031030f801c104005404d204128100d100c0d80c0c42e0746071440401c0c490031040100240380410800c106051250400400040c0d44220b440c180c1c1061005908c3d080540c0c4481814440a8211501014640b1700d140201000791106035040481c0f0610400690030040d660701554800f4440030382c40b640100c0301405040501810032105101403c04640708111041d000340c51202e001c09202c4102948101c1865490800d40d0103510000341002142414404503c0119051900700114240184e42d5041844058031542c00c00d600401c07000c0003a8032 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 282484100 1250 282482850 282482857
    0xc0d0506210109060e0c060a080603010b040e0a0303110406020c01030b040f02130e06040c05030601030902120d05120c030702030405150d0603061e050403080117070905040615060c05061b 82
    0x4880240c00e0740c0c80e2090a005019200d180012900c4904101018684410000b50003031200790081c145402c001c081103003140e412800601c510790540d220608041399403502d100f021101d9035104041c0403042c07164103000d000d9401070600000c2c030742ca0030401000308a1380459403c8002c1000d01e408120b14081e1000a8094031001c03c440c2d800d03a10005a81014040091851044034803001181505a40d004100000c841da244e60344404501c0030000640c075580f1039400480c0e05440104901d00c00017400924602d498010301c400c0e404201c0c0010086100ca009034101e0341d0100219840d00c1c0781d45401c40000752240920b215090103200080c15074802a20b4130030540b081c1426901040100643d00d05144003d00030071010480400e07103d00c0e04050308011802950300c02c51301512040c20b181d01c2c002c0c01800b070101501000d035040c012481c000c14102118000e01340940c2c010403021401d6000d5083c0c100107003841c2da0010f014042d607501c15100060001c01d44c0c0c2d604c460790406054140d6011804040c1c13921 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 282485350 1250 282484100 282484129
    0x5010501090606090801141815070305060a05120a06021b120702130903142a0d1107030c0308030c1b06011a16140307050a030905010f03050c0d0506 65
    0x508100010421003002c0c0d0010044035543d40d1884003280c0c1d1445424201e5280b60021000c80303c5140c005210b031903100044c414800c03a001c0c2251410350f115038807421510410b507141c20000b078a86090200354504020040c020b8441103da1381c2c0301c00440c0c000e070780e40da0300303815001001d140d004600b5000c03100101290981201000068904a4842000214255200e1a4101d101d0420501d030101d80c0c40c3c443c0303e40c0c5060340d819103400040403900c100d00c0c00c03103801c0311040c1254221089011801c0028104040e03004416810081000e10007400303024248040560212580d0b91080400300302044542c01c088040740d0300003031410369039100c901c040c00c118400c030001036000e100c80c0c00c000000d013400080c0142c100c910030540007030b005241c400c462203148588494080301ca14014182c0020175072514072198055881000c492900c482c070381d620b600b0482c0341a000c0e004204d503408104100d58100c071004501c00100d217820802e0303190141500342c00c1c2c0200c0148403062a86c8000090030741e00c80001d81380340309 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 282486600 1250 282485350 282485353
    0x1501020c031203040614060607020d02040b0411040f0603050405100203150a080604050c0609030d05030c04050a180b0402030f0114031005010906060e0f0f01081003060c0c0203010b0108090c0d0f05 86
    0x42e141c41100d0000354015941103503558503084403900300d130318a00c00b1700f4010403004102a150807916020003280703241020082c0d03405076031000d00d03405a680724482c2400810b0031016850700c842c0380c280e03881054111940320b4824582000c00f003000003100800c02c1c1d410300c000100c005841703440c0c0c8030721010b400074060304160b081510504080361240340012402d00c6240314008035130702c10a141c010b004c1207002c1c54890b141c0590199441050090142c1c0c040c0d030303211080000b200e04240e55080091040003076a84894844000c442c400d00220800d4090503851079425601076145041c0074008a4a9030b205100c4d03006009124030310340d0001d41d03043c8001d405607400200e090280396101c250300f0004048900c10400490351903c2448400c0c105040b0500462400400e102d00b901e140740300540f403400c0c0080550030340000d680004800a40c492060700c0a904490350381003074680c1d02e40f06041c00c441039078280c141801031b09000c1200b02400001c0c13848900c002a60700554050f05441d020994564107078000301603 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 282487850 1250 282486600 282486613
    0x1200a030c110301110306011d04050408120c090105090919140601090503070e0f2205030306180609060609030a050102030f040b13120c0c05042c01060e1501020c03 72
    0x60540c0070041d10112801014010040c01c2910101400c95409655040401c00c003800025415170003441c684818590b040c842629101c1c12400040884404030740466541e80003003444848070743e0441009500444070402c140c40c155284c0c001801d00e02454400b10301c59040700001520504101c1002c200364541100b041c042d0204a00b149103600b0b000b02c0d151400182007080016543c40c000030580111541a40d07109444e440c0c0b03002c01d00640307000406030a00310720b401442200b11980c1e03841c041d018502410182d9140c0c1444020045080c13000c00d003100c0740034140000d000150b03440400300c581140e01100c01561310400107020a0400001060203000c951003c800c11100204006206100d07a00c1900c000a00340e68100300c4001c0c0d10000c04010f48084c03921550040d030140a012020040d07409150b403400403941d00d02c00241602c8820712524803660405822441f500140c200345109902e1050003405941d0a0082c588003d850043c6880d0303146100a40360314142e402800031002406014069892 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 282489100 1250 282487850 282487853
    0x3050c0f1603141206042d0209190603060609051f0e0f06070c0e01150207030b090c2101050601053c0705070312020c1806041103010909050106050306010b03010501200a 74
    0x2c210310100c0c0d1090095040c20005414158003103208247c450696400b036140d0002894460001d40014000c01e400c6134141602010034014402180002d0602e0396002c5170150400348001c24502c0c0c0c59000380c0c010700d4071040d40c0300c2d10041c0c402c1c80303046203a003031812a0311a641500081c7d448103641072115001040082c88a050003940c00055050340d1201c00d40d040f66907070314244000b15003d003447c1c010043e00710100c28400610f00c9080039411803d80022542107019140000346105120100701d68400d41c6440d42e49503c500a0107010b0740440b090807c0c504202c00000c1585035540400c4100e0014522009180e6051400e900c4030b003014280c1c2c0c1c0400b078641c0d00c41c0c41c1481d91000240030550350041c4508615222071320006e01c00700403003005414074850b40140d000d81003c9200103801d582d4044e8507080d056030b016090700003460082108030b4021850141c07a003802c41c2180d1290b0000c901075005000140701d042850002c80c0d0441ea002e1800c841e102742a84d01c040d070782c2c1114030000340d0140940e904120 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 282490350 1250 282489100 282489127
    0xf09090507230708030402090907090f0903080601141c020c10020a1701180e0a02040e0618010603111908060103060603150b1011010b09090303010603050c0f160314 72
    0x40c18110124461200e145200000342c94501500c00001d201d003400f040002c005017400c0607601c1c0c1040d02002107884050311b80120a040c2c540d012003540c0b000c1d617200950800c0c55441074000f60450801c1c2004489501c1c010b031038200522503440392181c01818802c5c2d0340c06600c010b6040b035084030b0040054a66020f140060507002e540b2036040e0300d00127060309a921054500c52914541250792040c8000f08140885000300050f0101c241c00c20402d01a41c035680b000f40e00c4034041c3c003a160104502900c91071600481d0400d41500c070011780c00140c1c0c504001400000d461201e0390082c4203007150149070502121182c00701d8079400707070008581406a0000001001290703002482500c1c86600701d060446a001c1c010f4049440c8031075040c8c0c0c00464801407840803030280007107104d81e44445001103169009000480c0e490f4805840c04c1000313a00c004010881e45034184503040c0c0180086071078610f40341e030825408000c0c0c004c4d0740c1c6210550b41c02c50400c108160080d46a0210003103440c40326a1504580541e44 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 282491600 1250 282490350 282490367
    0x60406050915101a1305040c030603061506020601060c0308040f210305150103021801120b150301080d030204030b07111f0207021207050a09021b01110d0605010c120f09090507 77
    0xb000c200007a001301d900c0b0900d1440540701402c0b121288900258074100410018080046000003455074030301c00800468481e0040000001c0c2d0940e00080052801c0700092420605920801c01c114400c161500000e52002d001074005070071000206506c03206003458004070900c1060f00c43d42c954106854000c0c65015084144142008208130161b031018900640c00d0b4401c07002404404103140b400c1c00c8041d0700400110000c864043d10015051100201144c9028403410b400080b880e404001046002802c2011550742c044614003541058507550351710010000c080c110700c1c00e002041443c508444000c00000001594244440c009070070410243c2d4002d600c07018060b0b0140e55090041c09002c500001d41a04a6501510b64810680b40c005500c00075009a400c402805207148004002c1540900407804850562110203a90f0741e4100c5280084a00745c0d4091414003550301c4540d40443c680c5440001d03561168105000c41074143e4108548402d419000680114500410700a20b5130344241403 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 282492850 1250 282491600 282491609
    0x4050f0619090e0708040b0406050a0902190305280201080405030f0301030f1506061e0507020a0f0e0a1104140111060709060215060303160c08010507081005011106040605091510 78
    0x300c00c21340b40d0700c0088607090004c44001c0c00303603400200410002001035020320f038800c51030400020b141d85541d00081d0501d10001c0f00d4008180340e010140244a018050b041c2d54101200d1031141c02250750a00d040301c4010308070068103008800001a0900009000311200e4100d140b90650b036a41e1a4909580840c09142e015280e0030a034801a0150300e20f103229a400b600e9081d00d411101d2684089040e1103069822061400c01105100c54070040c1c6440c24080054080001412090750400703100da9410f103002803550760524101400103050b00d00040840341034495054556180108060068840c18800417030300c5414481c0b102001203140d03000d003580040d10720a50aa40c20703514809448011680103990456040c3c008002c451400c1407001c08603103803d0710a080000050f82e07180300003421141d0482c1c030384002c100c2c18001c004d54800702c082448040c24090a248080c2c080409465503190002000200400e40e1240880c08502c01000f0f0114000c0316000f585400d403804809590b58417005214 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 282494100 1250 282492850 282492869
    0x1803050d021005060d0209072a1e050705040b010203090904061409070b091318110108090109020102060f0402150a03060501030c080405030318100c020c0f0904020303071b0b070620090604050f061909 87
    0xb4601e40756041cac0d0300203440d402c10300401e003440c101070420008005201403036040d0700c01041080c450762104806035204901504001a84082d201820f034602c0030014121209034001c140b00b48108030f441002d032250b00310309596800c91000b0000b02c802c0100380e009500008404c071800c2d40420030458921602200c1c5023a618034820f034072890310301400c1c0c585c1018000c1c0580c100d24005115100290384c210360160006000c0c403000b129200d5403c030785a01c13280000b000a61036100501c0b071940c0500600c43c61a8107031070500f21510389034803800c1e145d01014003100351041030034415410b9204204401c0e42585901142003041840b1070783c011f950703000d984d50428001d003000b20140500349050340c100c62046030007501451400502d076440c03610072045a56181c5034501040d0003c03d5022081d0041c01c21140f00d16000208542c00c00d40c1e601883c1e21100886444030410411100c040d1105403c5e20308444003900e0306615214208009034987c062410008400950480000070351540040d20030b044605841 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 282495350 1250 282494100 282494123
    0x60423030c01180e04150207031106090d0801060f030902041e050112210210050403090303080a061a0d020d090c0e0702010b06090108071803050d021005060d0209072a 73
    0x6403041c11403c1e081081192440004220708848070160503846445110444000d28001c1000c90480e00103900550000d00c01c1011440d89610410001c4c1d0070031319030b1005000524850780c00074012941405100100400c900c1d003079500901903001036640c0c40c1d0081c010b01540400300400c00d2214517000b51408040d0a0400000b0301c1800d0800c001051908250003042e10381400b18841d02d901c0f6007485910031881411103000c46131640d0b01c69a4041d81c402d40da5001d060786107040003403400310043c0880101e42c0c5804002c10010701c5080141b266200d10030140d230384030715031440c40c04000c2c000c101c80c10094030b08080226040000c0820742c80140e800d0200e074420141c0b9000c00c12800c075603404420741d800000c200602081e135801416503a500182900e014001d0781c00e04183d440d105031039540121129846000301c40c1c00fa82d01070041030040792007900100300e50314181e400201095184038003e802184140082130415108100c800441c025801800400010400081c20200384000e0107944103250708 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 282496600 1250 282495350 282495373
    0x14030412230a0f050c0a0215070506010b040e22020f03030f1306021501080601092a020a140c0a0b07030302090603070f02010b040b06030f100815060906010912030e06042303 76
    0x44007038645c481c0554004181421043c3c0c00c0c02003443d441d100760b000e000c0c02400f602001400421001d4042c0c400b0440d05d90302c072881c11181440d0007078045c04c41c0d0007019000b80c44221a1036140d080c0c0d020036404440340d01035003a0032070100c7e0030340c85111143c62010100159803c0c41700070b40c09a542c22125a82d080341e601081842d0382c1e07142690280980301c440d40000c40100240086500b0038052481502000000d652103040500c4500c680401100c0240e009110700c5421f100700008103001d0b400c503180151502210f1500042c14084035801000013101010501d03006062090303054039000344001d0809943d034109220042e05543e510020980150300748402c050103810140220b2480080180c41079081d0b440b80311401001c82d00042c103800500d91400d6001a0035501040b410b521849404169400c1c0d090000070320080c54401445141030002d5540d00b0450040000c56100c52103801d881c02a20032080d510004590744a554000060000c001c6009040000914080e00d08110101c044410490380c1 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 282497850 1250 282496600 282496607
    0xb09090105100b0c1203090a1502041401050f0702041e050c040b0414010e0604090209121b06130b04060305090c0102010b0321071707050d14030412230a0f 68
    0x1151800c00c0e5403a001410080f19184030003409003c4626402e83c1c0c0504a81c180c8019942c000300c2c0c411401c0d82c8690040003e2060501e03102e1030700d621458080d880c0c2420900d924103226920244203041000c00207900c8442400c01c0107854a00d540203006000c000c000080800c920304c40d940c00c1000759840c003c003003407040c1141c404841c1124030002e03002c0d041c1741ca4200b00c0807141d44400c4c035650601000c1c01c0704501036555400104040d0074009030040e1500c00c3c420074400c0071500340500f54115481301d0200c0301050132103000c83c13000701406c81e01c1e1652444000722115080c0751a5008880394640400c02007012505500714a22034510071040f1640e906024004a098502d407200b48c54050300100c001001200004651201000c00108500d25007203a681c0c0300709000340502d0a4098651002c1240e0b010001c06110203451301829142846080e007412500600d030744406800282106035000000c060140501242d100700559540411419066000c804815600c0700385118000344032010f095a01500 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 282499100 1250 282497850 282497861
    0x70e070f05070c0608060423091204030b15180a0b04050604090b010302011101110f13080d0e1c0209041505091f020f09151215031b040e010f0b090901 66
    0x8000380f81121851420100b0b07519170b80e010f41020f070456200c060008221030b000813007104840503116400242e1401e50f07001c40c02d02203401001c07004590200000c10100e01003034142c3c2c0e08100c10b1881c0c0d80d46448540300003101d030b032030014154451103050410043e01d10803035400b19000d000150380900480e5078503020842155000c5100400000801c0010310240d4811402012101c503940c000203955030305000711022a070810204c0c1100389000054183c40007422604441c010040c1d50010407601c2c10111000d030141009403080d1b40500002029500040707000500c1184940c0c014100c11202e0070281003211040da000d9921070030307660510012a080d8100010001c2035161401010f003041229180c82e107000e03600080c414200c3c00c030148840901d40e62290400d845441c00c8498403542d401c3c02032090301c46101c0091010850300042d1401004a84000c107500303950802880c4d4042008164100207401441505813901d065131900d060b102d03034000c8a0384540c01081341100c4c40d0203a90b0351181224243e60 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 282500350 1250 282499100 282499103
    0xf0f010302011d010225180506011e0c060216170a050a031505061207020d0206011a090310020c0703020f040c021e0a050d120c0c0206040506070c08070e070f0507 71
    0x1404070800901c9000303105458909602d0510680300002d400545080d0703080801d106c0c070344214840400c00c10042aa141580020716840795081c401d515260380080e1201101c540030f681802000800d01084902c0355917550755040d4018011510303011035103501c8207101c400100481fa10080d0540112015510f10140c070200b80c015582c09140030300443c0110090504246520300740c261070080807134a9a0307000c2c0903185001185620041924044030002c0c42c140342e46002006540103200140070840035982513030464900b2212250341e51036010003080ca4003a45440300d2034454408105141c6e201c0c408515082180d000b02d07420300740018550200b0084461403071103900964030100d405070584004144100c0c62129180645000071200d498003424159001c5080c000210b42d03000d00361000800c0d210b46a1040c2562070003480f000d0369903001c10311601c0f41c1e00030148a4200418640704010103042207101800010048d1481030b940c6a07061001c801003070f9035001c00310b003403840000c01c4d1900c034030241c45990303 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 282501600 1250 282500350 282500357
    0xe0115090503060a18050f0102071217012309090102090a0501030b09040f17030f011a0306180a0b150a030c110307020409030e09040c03031e050418090c0305060f0f01030201 76
    0x54603090050f400034a00f0748008809420508103000108101f4014180b200301d00c8000136030786804500d8440000782001203541c09018581e480b419042d001c8010240c1910706805600c0d100c09440d5840c8201d00b207405103100d030b104248408000039180190045c0c04602016900c11455a4030707800107500340c40041c180b040c1c100d401b900000780400c20203540c00914a004154050030a201d007071301d041441d4001c40c4c410705010841c1d0010071034100300c840610141a1000242415410302100160304940f22000712600303128080081240300d0b07441da022300c902c903c0041c1031031500040c003541e54259801008021000c42c0c40e182e9500101030040ca281d030290a00000034520b808000e508001c01090302a4080d800c2040069900201d40c8408030041d02807030007011a0f107603042c51880c00030100d00581ca54440720b8051901308030b01041d088015a010340e406041c0d1071198401051911b001048100405400d010766040000240000454118010401d281440310b03980e85180e07200c10240020b22009000 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 282502850 1250 282501600 282501613
    0xe010c1202130e0c031b07051902120a030c0b06090402010219061805010207060509010b0105070b15031e101109061605010617100903080402190f0e0115090503 70
    0x2103080c550040445004000b040e03800c00e03841d61030244820300102c070728100c811000814840607085040000003200d080915403450700c0403daa4650319403507001071a500c800d00034043c041c215910511503210301200c480403250b20030340d54100140140c0300c0daa01500c0c00390421740403956504049292601c05c54041c3c00400502a1900f01401400c1d1002d2003565110744da09184800c0550750304005800c03030300a40001d81c550f011424904d0846001400c103401c640c0c500345c04604583d8100d4140c500031508502082c140741d030303140324203a02404251505039040c00b5045203864800c0c880b00748007100f108100704841d0710111061580007183d42e801c064030640758003070000c181145020350050410540b402c0300e2080d0310740d50360b89103400e5032000c0d00601c0081d40fa455a03074034449000c12080c2c0165500310b000780002406910302030700300480038201030301a030078135803802d07183c0d0300403005000041001c3e040300c1890070303521100ba4400c0c12081c090000302c1014044143c1410384140c11031019914020060000c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 282504100 1250 282502850 282502877
    0x1c03090e070909020310060f020a021c08040504020d02031b03071202090d12030501060f0801050d290f10060302030f16030f0e0c04060e0106020a030f17070f02010e010c 74
    0x1180c000c0200349004202920300e0205102c10300e8005103000c0e40800c040d60040798103192000c1d0800e02c070b8812a804641c00303904000c0c0580e40700c0070074500c81c000b4081214107051300c2d0b0800d61035900c500d4124a800a000044010312161250b0056100761170504514021042940e580e104a1006444000005502d030120900030b0302d081d8000c02c20000003c0100100d0500d954070540c5000040d0507040c042595080104882500b000254200000034030b4080c0041d81440c0c0099182d04c00942d000e0600c0704c11004120b107500c0303880303d401140880b12210384224541501101c00e151421100181442c1c21a00000b624a000780290b034020440102c0c8400c03190349501404c0d141e039001403000c2041580b148a500310152052184044a036615805800301c0c1cad601e8014401038072103a40c4003855441004004010070303580031412904282e854a00000ca0f111031078421510321002203000c00505400e0800e00072007a030000c460213951400703a00240700e070092500c1c14034202c50400c031114020a83d60f404501 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 282505350 1250 282504100 282504119
    0x7170c0108040f110f0d0501090c060905010207090c0302120903130608040803070e0303040924050d0b150d080301090e011103070c020f120f0f19020d06051005120c1c0309 75
    0x4c4546005410320030000500d80004202100d110015076003a5520140702c0c0a0003040c0403081e000e0320980c1403482101d403034000001e50710b001501c036201c1015a5a400d82e58403500c00e4040f64400031440203103000c103052020390f580d129800411100300c6c13005d64a10014071607018030f0710700b072142d41c0043d038460665030b5913034041d0b40d0038034200c0340203a040c0420000030842130000c0c480c420203252040c2024103a19204046000e184229810040c46429070f4006c0c0400180c680081c030354848101da1707100e109810243c010a84810015100600c240000700000c034443c0201e42c0003c007050960402449080001d8088882034401a01c20b1070000d1000942640036040451100440c0540500325401c1c0c950710f900c20a091165400c440c00c82908502d281c0504413000b00300c401c1729401c184991080700c0034164001056504071001c0100300c1c640701c00010380c85442038142c60b0028030014280049140c211100240c8074102014aa40b29020002c68400d460400c4207200da800e0394580c075681d071214106882e94 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 282506600 1250 282505350 282505373
    0x4060b0301060803220806250c06090f02011205041203240f0806091c08070c02040905030307110309090105060c0708011104060801060201020c0703030e0f0307170c0108040f 76
    0x641642d25200000361a04042000b0100140751401c0301002c0c41d0440042000490b4603440039a030307039010109100ca48110000d1826070441d241d055507200340315000342a29420103102c4013404591a2a40d09000d00414502d1100858400d070780300d1510562004211040321410303100a01006510300f40b07021824026400140513082d110082c20aa403c6200d03503080d0002160407802140d0504442004142d404001843d000303800000504070b04030001424081170310f405090300007004008004646428000e850039003032590041c100740302201071801c04682d40d6005071140800921a18004d10b8040004003d9510121000704204080d03441c10040200542001e5031003815401150800128082d0912402c0d140340e43e030902c00da4681c0d05d840d10207441d44c070f0140e000c0015a40108080c5c40c0c203800211303103034054039414100451011801000308404000380310040c0c1d050f118201000c141c0c0010360150106c0440fa590440d100c910142d0300440c6d610400b5100100504c14a40c80e200020300e958080 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 282507850 1250 282506600 282506621
    0x6020a20010c020a0b0d0e030f0a2a0507050901050409030215061804050d0f08091e0106090c09091a010207060c0215210106030b0a060513050409030f020106080705090406 75
    0x1a84140b0a540c00144001343c3d680d11403034080100107072070b40c0702c02e0340d600a0800d41810304000d9400c1200d4000d200403640304941c4440200059000000c0711b01c40312035034031050700c1c80709070500084000c07a03e02555903c03c40d004980c402c0c0300c200c000094610707042c0214400c150385680175040c001d8804e01d1803414013202400c1b0550010210f251518111880d031941445503010344d004260035955141c0152003d52440502000c118212041180120000038090007030056001081d8150844070000c1d40140324031307044900498100500c2d00d0085a0101038241900d65900c1c0c104103400742c8020304103544000024550258206500400506003c0c24a40c0c5c08140040c10541204071541c1d622201030f40072228000400d5104045080040c40450f60701c0d001d842d00d400c042100480000c0010aa0703041e92103500c0c100708000910241c55100e00700c80d04001d000180060050344441c2c03401420b030070902010310700150703c1c060740003a030700746c000544030110f4601a110001540751604c45a024240e0741c0c0c0c4 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 282509100 1250 282507850 282507857
    0x9010b04090e1905030304170702090403110a080307110c04090317100b120f13030905150c01110316090f050114070f0b010812040302030c010e0102120a051306020a2001 74
    0xa168900d1040c1c031803992543d6101c1c102540e524a40352500000c1514490717100420190140301010040c0c940980d0700e0742103070300760900092180100c2c2c825032030040402c0d801402910302000f0b22940c10340044400007c0c0340044180c030040460300080c0700850b441240701a002804481c0701668000304070b00480e0b00f103141e0003442481140c86001100d0b95510000840d9075410000c401c02070060708642d22582c0003a141d08600050088545004013143d2060080603c0b480c165030005807580841c078201c0300d0903400640240f0a11081d0340c2d41181c2900200d403286841580d042e2802c018034072901c08102601c13000b0702003806150400c0011243d1040d078800c0300848807001c2181074042040b40c0101c22041d40f00e59902042507040c425520308020210071a02100300c818030046c40141c0c1d02103041e4221400030301c0d0504035002c0c0040100e2504080180400188400048055042ea07001009002e40c500040c58080038a564420882c0d9a607141280541009120a09000210440c0c7e2840b48448814907 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 282510350 1250 282509100 282509113
    0x103110a0909051e01020a0f030203060a05090a06090c110714220903111b1e0904050f0c090f04020d060b10020f06010e10031401020706090303090c0509010b04090e 72
    0x20301c0681200c0001d80d0a50309548581100f15203006604115001062904000d5040c09043c0c1806403050071281d6002043c55004000242c0b16103c080158008180040c44000d650425103580002040d06020780401070f401d00b200124464051401801c41109140c0140055850b0503801d400441503000311581c03040c48003032640c0500101d4040c03200c00d526038140c0010000300700e01e4043c0902c61603003110040d507045201c569484003c24505c904a01c41c082c3d8040c1007924032000c4510b48081503209160b4070000407400c0c001481130024a8080e00c60450342283c0200040008101c9a500d0031543d422051607a5000103005080400400d2206032140c2c2c00455031045140001e0a9920725203102d0006034071200f03072400c89020030041907006140d15415011203051201200702c00e240c945c000a040104d180c40c0c1c2204030107003581181c8080f500440c00304111303481860003e02038581c29a05a40410701268085650701d03184401038100c0d480c0c3d150b11403600f845e001110010308258035201c2303010702560 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 282511600 1250 282510350 282510359
    0x8060705280206070f030e120d0e060106020706030e061b0a02012903070b03010e0403050708090307090f0f05070206072003160b15010509220f0b030c06120103110a 72
    0x7854882103154642c025100d00d1a003c900202040c1c00d490520082506109445000310030114000c5040748030003004955440b0fa06419101415050148a04078841c00f13000003229075001c2040020740b41c242c0d509004201110341c041d80c0e100000c2e20100010400c040c00e0f4145840d07134000a01002400d8000411101541c01c8040303008642800380c500441c801420410b02d501e81800181d000d462a00e102d242594180307801030241e0400140000d041c494001021401d10a9000c155090350070002c0441e44815240c90114024002d0303c13a402c5406420318a02c11011f030900d000b91380c8201400e500900f640e5955400844000003603041020482450806ea8411180140001c03c4039003003aa40078151740714146046a40500018089014a95905d5400265a82c0710b01160b507a0102118209940b80c0482d581d4416014450907180c03915190401c01c081e44400b64000d0a10060200c054503025030207101480742c04d101d582c9540b44104950300040c40002c0c0784100105143d9400b800101e54141c88 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 282512850 1250 282511600 282511657
    0x4030b0105060d090212070611061501050a020a121e031803050f130b0c061f180609020705010b01020f0a0f17040e040f050d091d090f01020d150b0408060705 69
    0x31ba4014540070b03007203c1001d02c100e68100340200441c502e10700040c11980750000f0340070041c40320014140c1c10044000b070180da425100f000101103483d000200b18441ca03c00310005010344015859080c9400d1485510303040b006d010b44180008081c01d0318500f50300081581d8210384592045202444000b000d100d03130780c0309420300000040500030708030b19580d80f0303c144c4032030619103c0010203141d90f550188003410404042406408104d0300400310400321040c1c484102e6000d41001c0d000591441d2001c90740300309010054001c070949190a0b0280d4540d040002e821070b868000b409400750640704429407140025056100141608003018082810035403544901c007a41042901c040d500700304c101c1c00c400c0034048144100c000850050405004840c0340c001c1001da03520021250807101100403001980341e01e400d04c070140e04100c480c0001c5546054006110006010468450300c02e0310165a000c90b910986104860603909124004c03c015603c07104100d41d150300000b41c00402c001840d0f040c11a9101 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 282514100 1250 282512850 282512869
    0x309020402160f0b011712030604060e090a0b010b040b0403030c0f08040e1005031f050a0b09100f150e22090609020127150e031203071404030b0105060d0902 69
    0xc6030148040f036840d241050b059500e410307000703200d40c10100c0c000f03060500d81c0041c1510501e540180119121b903642000a0014111540f0031500d130510541040024a008100c540d20944104542206640c0310400c00032507000d41c0c042c0106002d0100410301c08a80203042d1004114850055862020155550382c01203402541c042c25002e0f140d1024440a0745201c4411409464254001e000b01d90201030400341c5042c4c0305550310a6a569031020078194800b40e0026041500082e02c005c00a080c03400c1100e10641d4103103e584054100a040881d035460034050f0f408901090390788100d1071001100403c1207100450200d09200030f214181d82601070030f50b02505d512203004039000940c02183e030001401c401094030408041c1804404c0540d0645419107910003a036202c10000b0a21001c5200c00765920b4034428405079042c851484139401d15a5090001c61065002c1e5941203408421800381d02c901e4061800300410440360317800103001320b081c480c000c1c001c0c9150107507001c201c8141c0d54020170441e40 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 282515350 1250 282514100 282514103
    0x20d0c0206090f030909010b0702040b04060303020f070611060f0c13060309112e020a0506040803150604030302030304151e0b0405060114090d02060c3004060f030902040216 76
    0x80000c1c04010310418107200200c001c5544001031071810180c0d80000c0c560180500900013264000b040320b4040d515260702400b00c1d684040c100708102a101c0c1000b83d90380c1c1200d80c503801d25200305c8102003101e61007a41d00c500a10300100c010141603c4200343c2601d2034a0003007500b10141006e001d4041072644000e00200200002d4500040d42c15060400c1c582111403103025034012207a1240032407060042c05050000c1c03503c40074400c1c1425043d950100e0a00a080c400a1b14600c101c20900080c0b0150300000d50250428620700160940000c0620900380200c2c030016015800500024001c12505500348111080a24000a10fa0344c0c0e0200000301454202030700b02101d40d95101d26100d41020720810781c22810900344401d60300c80b41100c0c00036034031134144540e00030041c2d141d4600441d03c401e41a99074404519065900c0101e0762804607c17132603507011180031160200d2444030703010152a802c840035540070f5550b0380e061045550303041e000380042b21012608160308010388011a0780c0c0112418006 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 282516600 1250 282515350 282515353
    0x203091804020a0f0e151207030602030a0e0a032007050918010b030c060703050c030d0e0a031d0904030305070c0803091609060506030403080712020703050306040f0528020d0c02 78
    0x505250040c040500d02a4114084038000310b0420700171070501c0d00300d03a80c2c01710a032105029540c41040c01303c0d105a400540005061043e00c5001c020070030290059840303100c0e0b070503040041d1042042495580c688174140035000c203101102a000c0220343c0030304c13416080d441c08202c0390b03081d5440e4041803038084222041c40504500882c1a40400005c2c0070781c1010701d4007180105600a07030140010640d100d1340000400f806030000d001007a00c4400e00039074040c440e0b9020100000d0400703408281d10f85000c0c0703c040340002c4502000035074002d002e1407081640700c006070880401c4ea4940d541030b001003802602c14000d0040408503c00001c03604d070f00031807103030a88030050a5040020f4130001c9420307096401a800d0760303003444005d2210342c079044c040d030341c1c8950180fa1903c1c0941f2118415100e412562954000d110b000040820070704d5000002180566030594003048030204400300c900403118207403034840711a624021003c1400004d440c600c14001e079006401803501c0c40c6609070100300e0319070490762000b5 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 282517850 1250 282516600 282516649
    0x319030207200604051908100c02070803041802031509070315050603010810050c071208040209070519030203071812030216180203041403030a06050a08071a0901020309 74
    0x10000690b00b84003000c00c2d82c407100d020703100e002c0c80091603501403401424000c100040101941854a9012400510704001550010f2410031400c00142181c84101d01c05442840700020b1200000400c0305c0c225080b031400e1900c0c1e80c550301e000401960015000c2c0c00344501c021020211599400c002d0380c00f540b1641ca00007000303410750b40b1031002150250b120501c2200b0a000420800d900400e18641c10000000000b410b50f903455000c8009005640000c0e02851034442541c404e9034100d8a0240118000c0321211101d56640008943d00c2c0b05101044002000041c0000d400e103000c3d8024607006585401c15a0700300c0700d021401ca1180c4803e910000c400320800c1520814181c052103e0702200300351030000c03d070301410a86100501e2400070481141a07500000060510406121210000103407078143c036070b40e00b02560300e0b00150800f0700840788610360b0039000182c1c903000060583c003100c20201103058a00380d05000d9848940107038014505500040002c00001c1d5214400c80d1001064400174001 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 282519100 1250 282517850 282517853
    0xd0608030a0e090c07050615030111030a050a060b03011518050d05030304020a0b0903190c050a060203090a091b03150308070c0e09030901080402090402010c08030c0403150605210319030207 83
    0x1d00320004e0310600d0100c0c03041000401054012441c140d110103186a61030110520701d022900400000340c1c008000700000c4107008045072280c004074010449014140119502c0301c185256074802031007461541501c0c012030110381802200b181c1c141e01d40010000710519a1100411014640944201c4094000008000c01c525056280d040a48181c43d07041d4109144d2001295542041801c030b0203070030840101510030010010000c2019080140c8805052541c0302c00107542c81e005005003521884d404100800c1c22032491140740c040c01ca1038051b441210817014400e50040c21400b4035414041c125480100c081410b400003048403d115405c251007280c542040e041000d50041e00c800700507002000101c3c45c580e404200c20307400030780466401520351214401640c8820080310001e00502001c020080c440e000075010303100b00c0b030023151440c8010603074a9020080f20b50302d0240b07031b50207104100b1112140c0c0c1c0b4124081c0240040004a91801009015000e0714000c060511000207030002403410 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 282520350 1250 282519100 282519109
    0x303070224010311150715050109140402210102070f03050403032606040b1206160f090f0e04170d09030905120a0602090102010f1a030706021b04020d0608030a0e 71
    0x4191100c07400c1e1001c0c65504683e101c18180b80c904003040d10030600c9a500711070102400701242e151550181c5401401500c800000000d02024421581814606401109891014020903206660041c603510815166100440e0421a408215411590b0070300c0303403500140660002c010082d0180d1625602c451441c5030040c18075403000703600e2152204941e4840b00d10070880c000c65030043d500b1507003c100c045a90002c03805020032030151000c0c505c03442c414003803138000c000d00c00c1070b22002550701c8036610794404009450190091013100c6a00c82d042808020b05094160001e8126200b01c5458454401700115041207030011990b000740c1594071440d00007050f4108800c40e004000a440c0c140e460f5004040c11611121034840c06011241c0001d000c0f51b0301d81c400e60001040500b0044108014100520f07183c1c035007581280040d000e4820158042074050000600b41013494416141140071003514003808085d40110740c1000d4442d4440ca0040340940302840607040064041d0348041d1a080d5100801 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 282521600 1250 282520350 282520393
    0xc0f06020703050309060f0702041b020105010501050c031e090d060203060f04180b1506070609050d020f190f1203050703061703070605040510090305070c0e010b0a0f1103030702 78
    0x8205540c080c50041001440200588448080c00c80b00507856515171400c030500d034455060001c0d4411b01d4a58118507002042c8021a40b801442c3d000b00001e03070b00c400040d520b62182e880e00f05400d9105104a1010810034006000d00c2d8050b0100d071401c1111030400b080c11170080c0c81c0c040303a441740c0110402060703040c80840c00300c60007001c403028001500320840c600072103201084050040144e03c00040c1d044001c28841c0780e102000030300259540c8816040010040c200103208882c64001d07031181c0f408440c40021101d0400d02420b020b0150803205400c20343da40d1100b03100860748481512a91404100852088000c80085841c0420f103032070025801422280b2981000e95110328249125601030000020b81380c2042d4004000038071a00ea40c10b110345080356210200c007038542014002c2d010142d006020300099032054182114072900c501c42141480c02c24000c00780c0d451418406003084a100e00350104031404581000740b4104c0202c0250f50031984225941170141c0e0012000e80040750340007050 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 282522850 1250 282521600 282521609
    0x190c110d030f031503120903150b100507030e060a081e090d0c030e1e011706010203030a05040f060e0715050426191a070203070201082e030c0f 63
    0x1001800251075402514042c02110003104044c1e81d911003150445144109a010f150480c0c017004003010041c0008081e0320741800110b44007408480900624502402402d040c000005d002104003000d1810032200c0c2d801000058040201282032030000d6250880246a800c005031b85544031071500c3c0c040851034141003016917004004d000200506103034049603030040b0008601e49100d000010b81011120104103a12181e4402c00c4481c8403110355949c4a0b0030465a002078850300b0b101200da40745107418207401c80e40b560141e00104002201c4a48950069902078802c2d2600f44140190340c50b5001100d003007034000380b816400720906219114070082c100035000c54a2915624040c00c21120ba06c104c0c214020300c02b009600c0b4010311440ba034082c007550040424204010359007030345900340300c4e22a13401c03140082c0c440300c10b00d0086580d461000c8219440e081d01a1100e002545410a0160169120044610030062410400c0c81da41a280030440001c0d4003c0c030708944094244412240b000f01150311 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 282524100 1250 282522850 282522859
    0x40e160507050a0b070504050a08060901051602122b0c020c042307020715020304210f0f05030c0703081b06010303091205030d0c0216052205060303190c11 68
    0x5200700207000010090f24040e441410154a43c03039030401940e1a01481d08016407149001c5c0e03012901d03140029245100320001002031100352640710005250005820300c01e001a00161381030780c0c0c107010752001081c2c1400441401c840560481e030342141c4460f0030030758a4000907120728040803140d030304000100003d441124104000103544030790313001e184030031a500000800720302c0011340014000c2c0945001440964030f820003103c02e240b0300a40301d51090040c01608511200c3c40200351445129003a8480e5011814054000e0941c913617004414020700221014070040103006035182091118070700039132098420076260700c41483c000c5e5540d555148521030f04d038410001000401e40c080c070418111a00c505804281941c5820524154406c54008040a5007001c00d03000300d03150300095807241988001810700e030720b91b1645c0801150039448001c81280c02c001d0440900e00c0e140300e9008541040000381180d182000c89901d5006c0304c0d01001d85000465491030002040c0311051020201c00001104c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 282525350 1250 282524100 282524107
    0xa1a27010902031909050a0c0f1806030803010605071419110612012714010e0a0e060c0904090f0303021b0127050c0d0c08070503010b0a09050615040e1605 68
    0x40c0c20880d06108028075114251188485006d10905000880341e00e900509400ca15680f520a030f1050200c840c440d070b0281400405594141640510407074003600d43c02682c180ca56442c1150440300ca0300a00810f035151007941e0341c4001c0600d41003110b01c3c80e07070b4000c4c3c5580740c2110082c2031000c00000c690300082c0c0980c508010030b4030361a5500c042581501c0c00d507500117804400d0740c115210108000c2100701c01c114a00003211109034091a5598100e92440340c0e50f111075641c004285e0180c1d030070f43c40000403a91058011032642a1080c000d0100b80b20041c2000403070311003e840b0342045141da1a800e82c04264005000c098030600303110340326201448200244130102c21000901c0e02010303a15a8490380c41030001d050802c2280922206035500300c0140320904031443c6007400300c0c11075032a1040d05024450610000f0303803820180980f02e0310719401420121310310316211000700540030041440ba4010040d2020302580c1c101ca0000e40007418035102161001e00d0480c80041c2000e00500700310301400000d0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 282526600 1250 282525350 282525361
    0x150504050c03010b0f0a1520010207140a020a032406090b0a060c030e091b030a0f0608120f031e150306010f05130903121406150a080a1a2701090203 65
    0x50101b01100c011104110303001c040321000721000409030688010300345450440400c009815000b40c004507000b4136041e408020494170142c1da0742000d1000940081450744100003255189210500402800a40148100003094170101b1150303150042004103070303039001c440e886003031044c0280080c02c010308120614000903103003d00030284034050340c0c0c0301d04658000500700e00e5484400d020160301c1c0e80d0141d501c0e41404c0d9030181c003400d2024000240a803030000002a128400100e002d10b12461024003441c20b11460034401541d4402080940c01120100b40c00720507103140401e06200740d041180048103207064070109400d0503c10f80c00310052142c1d03602c09000c55a01d080e5215a00e516000300000c0d424494070301525400d9074210101c149614108400170520500c00c0c401e84150421241c0c4000484400d41c00f00701c0e0b000300d081040004035180c001812036041540030320060b910f0500655209409080001c20400110396112001d01001b00c0110b59850110391990140c1000101507045141c20b = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 282527850 1250 282526600 282526609
    0x50108040506010e0702190f02040b270a062103020d08100b0c120f0702090109140412030e030403060614010815040c0504051e130c0912150504050c03010b0f 69
    0x600500380041000f6011170b10340c40c0204001410114044004801e00407681000701ca11000400113902950030288001e050b4a40411140074400d20a04030b044481008150350064420040010b00c002e90341c2c0d203020681d40400c81c01d110b03580044550f04090101c903490000c2c1030807038400e126030611258109200d6000c0c1e0480743e00064880340e80382035844080d08510305141480085005524000004001c115402d0003c01003004d207001399585203003a40d841e440c0f041140da202001003142015000420005100d00e00320600803000e82c500070841c2c894400c041403c56001d9030081b14a5070b61014100100c485000803000c61201c2403c0600442c50300200307452400e00010700852043e60f03658182030a4500030400d17500900340c041c1000c00b404040000200540d00e8142a0030703c50468035a0400c1d015495014140d54448640e442ca0326240c82c00c50403d0451a00346000c80c2e03a0300c1e8100341c0c0d654010b42e0f44100d0744030b50b010b07500401140b4040d1051500f1100c1400e140b5004101c004048541c4e07890703 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 282529100 1250 282527850 282527863
    0x50405010905101e050a1b230a17070b070309020d02042c150603030403030516081b01150b040f0b0901030209120a053d0e0a0506010f0501080405 64
    0x302030b140240e0700501c00d60216580311182d2207119496401304c0310a601c241c0e01001800012000e03071103010300041c0b020300e15031101c054400000d01201d9032a107200070100d14002d403100403a5041f800c680003d611541e071080360102d80d40c3c0601075144040b90760014031483e202c05540150382400d04201500054000c640340d000080d2011340aa519171000303810007450b10068400e620031051a0441e07954603146e800b1b440b104500b843d10251226000443d80c0307481c002c001c0705c04881e17040d00c40300c3c605801e0b00801c06801000b40c00c01d4408034810b00c0416803200c02007003001d0680954200000c1c40200000a240c5000f81030b401c000500042400f00b405884803080c1400251844280099111412030b00120003922a40181d2500003824119124642e400003440c000164414026128802c0403488a11007001c050400b0025031000c1c1c2000c1c44c0c00d032200c035180d034102c588a41000702e0300100c403103907192401070b9a040444950f0b019400400044006000d21070180c0030910f03020815007010b0311840d98441 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 282530350 1250 282529100 282529109
    0x60304030509040527161d0106230f030402030607020f1005090703050706180509130b3607080607090e13020301050415150e160309050615010f0504050109 68
    0x20780d00c20224610351600310046840d1005540720445c818041c0c225070340c6607000c00c000705054903000c0c0d101140c0080c00d407060856940c442150101140c0c078048045815001668642281441800b407684e40c4400c990b000301160308140116540e6410644141440d0010042c808411900300b11010741c0c0400e004640f10b08901c81a001c00f20b05900e0b01e10700e4604050072503200400038820551b001031142d801400d00b005642c0e0800c81201d0701a0348200348405102d0459070350400d07070b46114400c80010158282d0b150840d940d00d0016001c484000c803e14000720400550b5540d603541c030100144208410001c02c40a843c1d20000340c811401c0c44280904100300e24020300455503803100008039000e6141d41d102c0c2820741c0040090100d402d081c1009028501868007090585003005110b100c448442c0941004480b043c000c0c9880303540d0307650144815442003000c59010181c4030300034480410410480c141c02001d105d1001486081424009030942188440c0783e0180b250078001042103a806c54200802c03074 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 282531600 1250 282530350 282530359
    0x80c0d020c070506120f1806060d031205180c0105090d080f2b050106080403020d030e03070503040902040608060a030b0708040f0206070606061407050613231b060304030509 76
    0x26150704a0280c00c00b60303a5001150414000300300509411841c284880c01000f01d6074407094207803290728002103a0099000c0e8409180e100317070041521400c041041c02d40882c0a458141110540310f0401e0007910342c00d4070225628500c1d0071200c200c3c007404bc040300140700d8090038aa843c0420035000b0070380e8094a9040078007192008507410710412407490848115002c9200409141c0c0c01641e07440304180c1c3d084e0345089580d448c000010034402d000b881c509004580503001460350800707444c0100c020f40300c0c2e031000c02201e00081c00202d0001c1c2081024101a2550240c09601c0340d080200c02002020000c014521400c0410010004185881000ea420030707258036000015a803503040514240460300c400030b4101d036000514800380403045d0310100966041d030383c0390682d1107248e070300300d240502942d080500b007504200f01144080e4801411030785414428a00d01c5c4602405400000444221030081174580e08030090015a4004082c14001000d00c119101030446c1801c3d00c00a117103024484c4503074000d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 282532850 1250 282531600 282531607
    0xf061e090a021303050706030e0d030506011e0207150203120a060b0a0503040203030f0c0a11010807270816150207030b0a2f04080618210c03040f05030c01080c0d02 72
    0x5203e040340d40007444d0010121000150f45002c020000d0400c2201c40c0501d01030f007680c1c0522a80300380101405028140d4845414400c981e011300f10b141c08920108040d4420b9603400903c0041c4000c4821407004641c01568450740140848810b40300c0090079a891a4076101c0c0c14030482c105141501c28100c500e00d407007505e907581c1d440424074502c19101d5514040c0e40c00700d0a05942d90f400103007855143d03c2601c6080382d244050006480c4050147c5100000c40c041b103100d19244113140e105025800c4a000c004115103030759586040c1041580d03400803030310043c3e00205010110f081180c018003042075100030230700b040c91600e504130a036801505103442c0d151600c2c0141038801ea2283c107403400e01c031150580c003626258542d00c446681d00504c81d04440d8010a80021464650201d0941d03180007010f02401c0014007038a0070f000541401d80d83d0b0b1620030340600c46051131036010000b0b40050440003804000f09030601e4101440d0840c2029100e040210250030003000111680680344c0c42886c003800941c8 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 282534100 1250 282532850 282532867
    0x123040f050c04090c03060b0d020105040b0c070509150102070b040b03070305180d030204140108041e020d062d0e10050601030e030d0203100b0c03040308160b0f061e090a02 76
    0xa002c072031500300c1d0f807090400c1441800d201c2161041000c0b41e200f480d0400c210140c1905100d0355015404000c4c0c08228244020042c0c40c10380c40052031401d1040d81515181c58841c000509500300954191a0b019500e48540c5d60a50301040244081c00da0814602e040c035150540141d0b0501c80142100304154468020514515041e4240d0781c4140d17079102607a1100c00940b0005009402c103208900010f41c10110040481d400780c030f5a035018a8100c1c94403004042d900440c150418050b40040360070124030458400890620311642c0c818030303039021142e0207002c41d040340d600c817400d441328041e04040d14000c0303a012078001c0003560b2030341052040b80c0070030700341d40d0f040041c1e006040d002d220010f140000950303e801510710b540290701ca1128003c002000da0f0300c0d194500e02c0ca024400f0100c0c0d4950040105101003400c00001c0d2102f0030600d20403001c00d0080782d56226148d40705550400003510070100380062450704000261001c900111070b11088044c0400003054058090840b241150740007401c1103 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 282535350 1250 282534100 282534103
    0x315060708031f0e070f090f1208070f080c0d02010501060809060a09020102100f021218030d09080913050a0b03030a0903170d110301080c0904020a0513090203010f0b01020123040f05 80
    0xc02010700c135840040915100d440942203580356080c0e0030000d010054040740b0300c3c6002140a0075200030f40142074811030340b551880200c3d840602e00750341d2a462240e03004002415a0020440d61510310040c0989207070350070740a030030350b4010b070081402d0020f443c0800034074400000b82c250f403140d9010004101d01a840c00140e0522a000e90079854041c00e150103c030348164560020500000c0c081c40d10324841e9a04059106c4ea42d540f071301c1040d82078004010701c0d00150300030f42104c6402070250001524211218002400d14282ea0400031960358032102040454003652040c24130141d000c0d8003642c07620241c3d010003084004039010052210200b0344591005e02c0702c0100355840308040c0502009050018030b40c011040c0c000344189484ca105101000c180b504180c80464021503000d060880c910781004200203919400320b011560403682d450380440075a500740125901481500800103203d04400002425a24407281c210381c410058505040c0035440510b83e1a401034110a0707030400b0308030614125 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 282536600 1250 282535350 282535411
    0x20c0330070e31020c0c060f0316050c07030b0a1415150d0c0206041b03110f010219060c09121e021f020616080f010302010e010c05030f031506070803 66
    0x5200800010038905002c1c10a0f130f00a105500c0b0141c111044110148100041440760078105110081d00344045403900b1842d8010900080190402e01c0c00d1210801c0710501e031514070340c02070365001016810b009542886100383c1c0591a180c80c00c051240c50040719400302140f81000c01e50088050038003000d58101e8480c1a80c0e800d01118505200701d04000500130b65503007041e10b0aa5040691544803145518500c4030001100c0c1d0018803000084181420018041031160700d03141940982c01400b6103c0300800303145002144100000205121400001405000c05422007489400c1c0c18030180701060f0940c241020350701c45804000480030640c0b01048040b0344101c031a1030782c1e002020523040c00ca80c0100301c0d207125444280240036821142801211142c0007540c509011070116001803015500c601c081d0300d1084030606080c103c40a45035206840c42e8401d00c1380741094403000c0241300070740e50241c0154007282d00403500b8606081a585504141c3d100c040e0403c2c64800442c0703501001c200c0c1701c2610 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 282537850 1250 282536600 282536659
    0x902010f1202071a040201020f0307030804110109080d0306080c03010207020307050d081303030c05101a01080a1b0804290106081003020a030803041b1505030901020c0330070e 77
    0x28240c040c40541c130481103000251000c90241c0942400c16188100010a8442943c0c1564030704200782c0751501c036013071800c09410390075040004c0b9100100e075174103042181d48020001a82c00003011841c000c1242c5c2800c6c1c041c02180d00c030740d00405c00200135a6002542105841007201c6030f080320030285c51710340440d12a003940d90720541c02c0c40b4000010715401c0030f406c500803400740050751480303080c0500000444095005282c0124946601900503510420041c3d80c8001c0d001070002d0103014050342074240b00c9403400d4410010f13680c1001c1204126444401051240b404034040003000b0b0038012052001c10140126010404d40c1d070006003003000f44c10b080d240251f030040c064501d07248d240c0c101750307845600840301911414002c1c5001007050050410348400c0340c040980c0d00f01d150783e0075001240c01d64406012a40e480d90288280d02c0e101c0c0c4244014945109040c1c0310076480940c2103000f00c9010090805101000200d41c1041720044d0031801064210b10102c0707001c0380800341c80d040860000b201c03484 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 282539100 1250 282537850 282537863
    0x3030a060f050d140c0d120305060603060a03060903032405011205160503041707060504020f09190c02030408060c092404030f0614010e01050a080c1e180903030103060608010902010f120207 83
    0x2040007d205840b003001703441d00304968080c0b01ca40d84180510480d0305c002c0d00c400c0d4021032146020000704071325134400130303049100341f402140d917400000f00c41e041c1c80e503034035841442c07100c1e056020409076801000508a21609807002e1140e07150180740f220080d00010114401d0080c00400601040303150015078640380c080c2030029469140740e003001c1000f0001120201c1c041d03d217034003190603c3c1c60040a810720502406103162401414040040043c181d03e00020f800d510060102003030082c407d1104a00c41d6841440d4a611481c0c03501c108000c101080020544103000704c8240e00304a400c0c2400c0720240c0b50440060034040c0c0c0c891a01000920030164261036000c052400841c954061404550480e00110f82403c0303615201e07100540c6030b02070018026413107030844c9042e00740051241c249a044801c01090850301c80a40f284803c3c8504089501c06502d80001006004100383c61107510301501e0050020042c244580d400070701400d6003682101c00b44034000e01d080e114260160120b0742401d90000c03 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 282540350 1250 282539100 282539119
    0x91e15060822081b0a02030a120c14010506150a14130308030f0405011a0604090504060603020a0b0703030c0908101e020d020913140103150f0e03030a060f050d140c 72
    0x40003e1150402c2550f84d944012021404034081400a115002503400402a0452020315070310b480c5581114902141444660b54840011440b040001002c04024800108503468000704000030540031103001d58051006101c42c4074000c1e40010604480f01510080d41e03074070200111400c421501550004200c00c0f4000204540d501440c0482805a0301c0b0364001e01c18802d40d01848000f00d84608030598206100748010859507115401042d0014040c04000810fa42c0f25008228104072680122071035540000c4d03c0030405600d40b1484000440034035041000c0341c28805190b840d07541120b007520300580c654014421400c00c0b852007002e8811a20401c640e24241c8258440203504008034051090600100c0358404101c1030142501e41070b81c040008400d0f031b080daa200456111003085400c070166407a03130030200300542c40c450f6400060a241c0215120f00c0c2050083d410b40c2c560f17070031000780e0303c500c25010001520fa034400c0d640c0f0180d00c0f0100403884056411a180740060004a00e0350140480 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 282541600 1250 282540350 282540353
    0x10030f0f120e031606050f09040e030a180801090f0201030903020c090108070608090f0304030f050a0c0308070204150506031927200102030a08040201030b0a091e15060822 75
    0x182a45291030b01a03058495202c04070340d41d44581c1116118060104104200c031903031003c0c1180c001c2005d0500208009944206020600d01e1a0030851240300401d0803201d101d05505148400c000c000c00300f46000740b248400079603407006801264040203052507122210001014002c0c00440380c502806090380c1090740e511400030303580300740610428012654030340101e00d040c0000300c2d803d00120b050304000c514103031640d46c5601240d011788000340e60358080da91300200041c0300082d00d40025400340c00c50302e0301c5141c0c030300401040f140041150f1140380d40720354041010352101d0040d20307440b24803035442c130502036202c2c45444041c0062118030001c500700743c80c07041001450b0701c1d40482128011900c0030001c6040c2000071241d00080e800c0903002d648144004900d10b4890308040740d0252041c503001c00e07044120380124482400940125451503240e01c2458140c15000340381d4840030f035004e1401d10076020080a4080c409040d806205d003004035400028907800703901406600c08034904100d0200d0b20026 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 282542850 1250 282541600 282541607
    0xa060c0c06140a0c1e0807020f030f0304030e0f150d0612081306020f060c0a0e03030304030207080f0115120203030702030a060203150d032c1503160810030f0f12 71
    0x1142d050b0601c81c80c0000000c0d503248501c17502000c15100301542d0681e41d90b6041d0a03115041c0003000300d801c511507941c001d41c5d0343c0d506001034603d29251034009510307824185806000e210b403000c440e6004501d01e41080d4256030382c0348031042c1441a0303107034455a1601f89114074009466a60009507a081c0c6042c80f035000c005d1400c00074811302c1040c082c18a840c5858143c12616000c411a2114456000038045100c00440400802400200341401c40c0f01c610703007001290a40d00102c8080e005a04003070310400180506000c5000d410707080900801051001d850864000c0340c3d0303070244d45540060840c03050210340301041110480b0f03400400319031004c440d62030704030041e6000301d80c2400c030040075103410191401c201e03086071142c07a450f840c0c8000c2081c3e80109180b4450110009000c15146036503407640d15180c81c109001d41070b80c4840c155580b813509003016007100000c0c0c4462002c210114081113184d002d0200c8020540f0751100c400ca00ca007880341403648061501450180170005001c0c3c4d0b20003c0d0341c1 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 282544100 1250 282542850 282542891
    0x902070b01140f180702010906061d07020309101d03060c0310060e010c1209050916021b0102210d05180105060d0221030c03041d010f0303020a060c0c06 67
    0xc00300980b41e40d03500c0c45028040080c001403a1544c1240261030f0801c0c0380e001d001416a4800954800050a01829291041503078040d070f001d1a00300006ca40720080d810245d01281d9445109400214030b026802c0000c10740c02490000028104640123500d61140340481c489400e80e0800103041390b11b641800004013030558402d40b4070f80b003240a00d00001a8090244030402c607a07500503150004104179684803007102620110903d410841c20001c00b18407075a481007464003555440c0c0d111003aa0f000640040d00c2c11754004005400354010102d502c0940c2e03400664a079200e940b400384c842d100395141004a07000d00a0701d60044810f81400c1c10030141242c41810308251000f158002c1c0031a840b810284550400c10482c040d400c10442c003001412015001401c2166860405c110303032605407000d0001d410340e002038104401c14808040e51b803034000d0340a0004e40c0900828044840c10904d540c0c3d02a54802070080300422050300c50071210046030103401d01b000641e4001400384010100744030081e14982 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 282545350 1250 282544100 282544109
    0x4110a0e0a06110c09040213110a030b0a050a090c02030c0a120f05031302190302040e0102040302030d0207151b120804030201061205150622090c061e0e0402040902070b01 75
    0x30310720400294283c800c000141da028070b01d00250550070075000a125558a0080003a60446541101c0c0502c9203428490301c56013a084c5110903231202c0f01120001c00ba00c5880004c58407910441d8010310031540c2d022041402c8501d43c20300040c03e40d0710f9000a0341540908107002e0341e5070203103440300c40600c4280b5401340a201c54030b5403600e074070100c5d08030140d8040c00261a042c9400010b0910140182003450754101c8401940d0010b0000650303075800a42607604003071540308141d40200e42002107050411120b0010b11540c000f510031a030500544541810421801004222001901c00c4071801969041046141c015242e07002c82080c1043c0940079502c01c0d0380841c01507191100c00103020400c104031b03451760341d400b8020704508a03000c419a0301a034000b44c0b0312540320301c041d6488080b4000d0900511110000440c010800c0191410810418452540100184036000d01030210349490110706124103101410804a82c2850320003040081c0140c0c0c12008201e84009103490611807994003040c12038 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 282546600 1250 282545350 282545359
    0x5130209010c0f0803011a040602100b06041e031403030601050703030b0f060a02150c090d11030102090406080d03060605120a05180d0e03070803070c030b0a0f091101110c010e0d0204110a0e 83
    0x1203c7c00d5004c030603940b06034403401d001038101540c0b0300101c51858100d82c00101004040e11b0034141ca9111004201080c2d0101709881d00140404004100300c044044114000c580043c40c21440c0210000c0c10303500c551540141019501c0301213202c15690718688091805002d440c40351604995100696a03c45540c204003420444d0703000900d4005016044440c2d01030090301d40002c0300c5c850303680d24018810b0120b00c0360340755409102140851300c461042030f0041086a008080a41c00e610340501114142d402140070031208100008800c8141e403600c0d60000c2440714002030790760391000d90003194100c03d0f80313083e010f004805881e101d481e44030b1101c17005d20300e0850030b8500c40e90b0f0b40c0c1e2107203549202d08500140010302c1500200701040c5090b41644d400a03440380b0102d4840c03c1690035000302e0303001c8902101d410140e10121042940d11a52240981c00d80070010a00c0c002440e0018200e9014243d02510495041030a001103440f960046e418410117501d0b42a01c0d50945000649500142e50046004 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 282547850 1250 282546600 282546629
    0x7110a0b0a020318060702030a0c0501020408012d0c080103151b050901031107050601030b091615120e12030c0919150807080109050408040302060304121805130209010c0f080301 78
    0x4940200e211030061b03015400841c50004010019034a034041000d050714295424070002a00b00802e0061041c145101c1400882c184070b4180740702010211250310300b09141c83e00096001d8103403c02101c0341503907005811446841a00459000582080116104001200544510030a0300100500603c1509032400c1c001da8010700f502c00300d10b00440d00c01a140c0e44c000d000420100d03803080c00107600702040006450103810301c2c621209965005900803101c5101c1e65041e04e0219034415403800010b0301c1800c040c002d480589105d5907503200c0e58400030b41c0b002c1e070000c04a00c50354547c404841c400030015003044d40346c00b02c41000020704c0ba5540300c0c0c01e2646c040c100c8181003142c030400c446440740710300343c03900291070b42000405001054002c004071004a020440800543d03a840080c40c41948103006065001c0030b41e0350020300780d00f0a10460f8142041201040c01195540c04a030b5600e40440040181ca41324000c0040780d2503114008040c10b135240700c1d0509824001c26800460507941d905141e00344 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 282549100 1250 282547850 282547891
    0xf220510062102031507021501080601090c050304050a02010e010e04110c0615060d0b0f040e010e28020105071b0e010311060405010c080d110406030902040e01020406020607110a0b0a0203 82
    0x785016541d8000b941034000107220340040d00b04e82020340e00000181f0495034490b590300901000c0c1c01c001c2c0c0107034055610482c01000011800d00420340c2c00161803500a0541c20195241680c440102d40000d041c00b86994040419074480c04040c0070b00740e0020018040640b0544e15410700307902c6501c4200c1c540c041c000008070906021500380c421200301078000d61400c01380503035520050000b2160958001194002501c0076555802100301414140c1c0c0001000c90016130701e10718010400046010568224181501c0461007041e0500c04540a08000b80e403425140342401400f541081161400c04100d00c011400d480ca40b14800d05aa02c00c40392501101d51010800082c1e010780c2c1329640c0014000798020001034443d102400e10740b007520b0300102c0e154403c4440d4485a8120b6001900042e075610740c140705528090041c40080d1241c04021450030b410002d00135200e940c01130a4900384144824240008001001040e01280d000f20310340c0702509082019201960044c0e54181d03038004451034846 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 282550350 1250 282549100 282549149
    0x604120308010b181306181b08040203030d0b01020a140f0601090207080d1a130b01020c09011503020a0525030e0415090506030f0f1e060f22051006 65
    0x30604030300d40450320130f1120b00310308120810b0b4400600751401a1a24400204480e4000c1b00094461506102142c0040c0d00060640d00180c0f80c001c0004005440e0144005600c004c412101c2d03107000c100000c80d01011304070046c1e10300340c501407008041980009024501400c0455849001d081c00d5090f51080e903a40c4400e501030340a41000900404400c05c0610465125030f0721014011801d01419034091248800003100c0400d40580c10080726103542c0030404941e03041c000400d80e110300315860300c4c96505004420600c0d101081d2034070141507001031100741e000c1c043c0003660300540c045100840d4800a981108005600d00c0004402165070034049001c10319003809510400c585000d2811b2500e490419400050100a4241c0c1c1c4c01d03010700c10220011007002d101e2100d05803c404003c00d081d0032400a040d40300c410b40d034a0000b0580040303003409142c400f10000e290304800180091164907449241d01c0c1010340c2c0080c001015841807401040400c1806d030050002c80d042803444522601d032064201 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 282551600 1250 282550350 282550357
    0x70e040902131a0105040f0501081909050105101d061c08030c040e0a09020603040f03050f07050606031002090a06051c1b020c03030a02070b030c070503030903070516060906050703020c0604120308010b 88
    0x5c07c4c4020b2100c2017400154420521261710699008002c80c0d81c503400031200701210102e080a454694443c4204a00b4000c01c02101004020740b0a07455603a5000c0f0304c1c01c60410710b01400c43ca00c00d002d0030400540f10b9808800001c003468204051a55a00b0289540c51059000d48214480501040d0001d005010148103541c9c1d070b10f40280c6481e20315516681d4a441c208486c0c2c3e412020321005009030080c601d6054082e05031176100d48020229402d2070810035150070004504025610700402905095803528050b89045502a05000784c680c070603840341400c1c281e9601505852186810b0a43d24004403207085021010703055007d8600d0f01400b0705c06e26499200c0e41c890000564020340701007042422900082d03501400c0d041c4000c3c1868034076a18541960710954141c46640d1000c240304080c02400d02c40c081d00040450120070b8100c0c5041009854131100348198030500001040000a060080c4005408080010302a0f581c0380e4a030081e04000401000c0260002000c1c02d00214541c2c0c030345803c4 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 282552850 1250 282551600 282551609
    0xc0303070210030b01090801060f050102160b070212150f010311030f1b0d0605010603050f1302011e020c04060830030a020f070507030b2d070e040902131a010504 71
    0x28050300c2c0d20015000340103407200c50340c100030395003000140c4442c0c203100b15005004142d000911891600c40028a413240801c010071300b14a05000400084c0c500c3c50442e81c100b40e056445c1401d00c881d4044940c03c04020103c03c010086240c420400c4204056404505892041c607003041142100d0050541c1e82c1d0040315100c1040e448002d20803254548800c940303030b074400000d103085d10b11003096443d4002c0d22002c0c0c1c8200003007a00e038070512840c55450050035078003070115074040100c00e0240d00002d0840b0075500c01020011079280c24200310b01d2003030001e0000c103d030250003440f51075980d15070b0340e9884144180e9030b80c420107090603540701804140c0410b280311030301400560840e107503c1d804600039485400c000d14400c4040040c00b000803003d001e14001540950b42c040c20303078600302100c6010082d5a101201418046e8850b5010000c00e030421903402a005144c2010b0007403a28002c41e0042481040103940f20740c03a0700e040408a0b1558101d030110720301a011036801c41c0083c5006480034000d9018 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 282553956 1106 282552850 282552859
    0x120c09060506071e23061914010b0a0201060812070c0914070c0204021b0109050c010206060303040e0c120106050733090c08030c0d020c03030702 64
    0x605030040c1002d032003031407900d2030340c1c2e41c1c102140300c410011a04584054000d0710601103003800e0008900b50300000a00000ea601403407683d903e50031110a80740810106412044e140240070f101c0c0c1c2c6e1005010540c0c0c50b0b07400c0c01c2d81000c07503812002e084002c5650303402d400141004100180e01d210b002c11031380183d1b1001182008170f1000c84075004821704600b4424440760800d1030316074560784618607142013a001001440060081d1041ca0b07216504070001d01d000d4102440c0640c040d5510720b00c98021684000300d01c2005980b01c03401250075a500d0340050008205100d845004941d2100400220500d410b10703000b007080d0102d90a03080140050b801003506c00c204410121110404c101c0d4890902c9020b4059204160f4001c080c00480c40a0380c4071410780342086220342a038005000340c034050360384480808140c01c0d0b648280c550060018030515008003080c0c00c0100c1211001da801a0 = true := by decide +kernel

theorem cover : BRFrame.Cov 282374100 282553956 := by
  have h0 := BRFrame.cov_init 282374100
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282374100 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282374100 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282374100 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282374100 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282374100 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282374100 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282374100 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282374100 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282374100 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282374100 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282374100 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282374100 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282374100 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282374100 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282374100 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282374100 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282374100 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282374100 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282374100 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282374100 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282374100 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282374100 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282374100 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282374100 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282374100 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282374100 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282374100 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282374100 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282374100 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282374100 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282374100 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282374100 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282374100 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282374100 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282374100 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282374100 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282374100 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282374100 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282374100 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282374100 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282374100 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282374100 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282374100 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282374100 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282374100 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282374100 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282374100 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282374100 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282374100 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282374100 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282374100 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282374100 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282374100 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282374100 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282374100 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282374100 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282374100 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282374100 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282374100 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282374100 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282374100 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282374100 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282374100 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282374100 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282374100 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282374100 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282374100 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282374100 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282374100 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282374100 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282374100 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282374100 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282374100 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282374100 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282374100 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282374100 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282374100 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282374100 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282374100 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282374100 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282374100 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282374100 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282374100 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282374100 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282374100 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282374100 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282374100 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282374100 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282374100 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282374100 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282374100 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282374100 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282374100 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282374100 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282374100 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282374100 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282374100 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282374100 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282374100 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282374100 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282374100 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282374100 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282374100 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282374100 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282374100 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282374100 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282374100 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282374100 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282374100 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282374100 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282374100 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282374100 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282374100 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282374100 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282374100 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282374100 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282374100 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282374100 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282374100 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282374100 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282374100 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282374100 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282374100 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282374100 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282374100 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282374100 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282374100 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282374100 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282374100 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282374100 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282374100 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282374100 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282374100 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282374100 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282374100 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282374100 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282374100 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282374100 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282374100 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282374100 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282374100 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282374100 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282374100 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282374100 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 282374100 ≤ n) (h2 : n < 282553956) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
