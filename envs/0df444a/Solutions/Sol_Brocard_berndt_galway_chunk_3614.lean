-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3614
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:10:44.687238+00:00
-- url     : https://prove2.me/submissions/84328fc1-4676-4289-bc96-e6ec7e77cc98

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 649820143 ≤ n < 650000000 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 649821393 1250 649820143 649820147
    0x30307050304030c1a090d0e0f01030b0d0c0e01050a1202010c020114040308030a021b0304080a0209040f0501020c010b09090705030703020907020f06010b0406120209031e16080a2907 80
    0x180d03410510901300a90206955640e90b042104030b100a0920b0814440c20031414a004212008031380320790f07080007641c198010740403e00300245e072884141030549843ea40001d90f1a5090300000150304002280010f42d1130715805552108203200341c5100e04d28124010505c6640b0512003100c541d8141c4a12071400801d43c01034440f0040d034605805c043c0710502000001c9288400254441c0700400340050342c2d00c01c05100403e180642c2a02214194014001440340000010780d149440b60100c6a00307055654615040940c8492684020301c2540081603400707042505400044503441c046a0742c1c0c1859a80709103071036a80c61144241c40e03050340311810030405414050107840e040842c0d441644e407a642d680001500d80107080c3d00c0294604800a410003919500900510300221318141c00d5140035080c0c40043d581d0752851f01d54180301d402e000c41c0e08590100801020380e03106001e800000d100c0355281103082c1c8451082106845100b1400304203495841032420030a410b601c1d0f030701c0740049170701ca01c502 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 649822643 1250 649821393 649821397
    0x6050108040f02040216031709031201030b250e01170903040303230c0a051002070c0b1305040509010f0609090c060f123e090415030f0c0f080f03030705 67
    0x209981160b420040e41d004207aa00c5110304e6070038008d8481c04280000d401c494225000000c1074103400c1d40040c03045c0c0004003850b8155034112900090b90400b940c8441040c0400d40741a0140c071262200c410f02102c0c0e0381e94000c026202c8909007600c540307544110450014012000c126421900c0d60410003050001070b0150310680f000b000441684900c203c43d002c9011000e0b8881820f40b4403d0740f01c0701191b0200710017040100040341c1482000e50600f20141d540c44501341d180d01510490f03050100b005c4801c444040141401060014000e00c25418a01e0003580280804c0e107907654103600708035000c04e10710b8090080010301e81e446000b03d21028a444400c9640e458507280603410081114000340f20403e0034014241c441d50b40004202c910001d2100c5064100580581c8490442e1341c20044d0811280400948800210a56010518504c0400754021003522a0001030001a80c1070200b02400781a10540c02a16403607540b42c00f4a6840341803c0d42c2d5002c43c1107052040364003c100140f141d500c1080 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 649823893 1250 649822643 649822673
    0x91015091a070f08070f05061332010501032604080c0402090117010f0e0601110c06030c1b01020a030b030303010f230409110901090608060105060a20070303020607030605010804 78
    0xc105424491303942c40c1000da20024003038541e5002c1d403408074203005080c080b0641013080b0700740045036080150b4580b446101102843e8a003440080d20b58100c400c04500002050f5031a0402007000390785902c2c111000d507803418064001c140c2110303080318810303503024115001d580d400c100618551401c4001c00000c1c0d07100d045901e040000c0582900042030501507418040d0011081018006003040007d414060008000318100814812381414484000c241c0030042803040c3da0f01d5590343c0c5d892100b41c10501c5002d480000d01f05410111020b000301c19030190180307081540d01031180020400400d9544c0c007080c01a10140c8616420800c00c944101c4144150204c0616607120907540701400101252601d94007540d84080c2003820b50040c0c5420720b001805402a8a41000031905000ba000d43e901c0050103450300484002500e080740e01c0c01030724894009412243c403131a1001d903110102d5203c18407440210058440e1602054a440c02030140b8415180182d590700704ac0d69542e103550304407840401c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 649825143 1250 649823893 649823903
    0x60806090f160f091a03070602060702190b0601030e030f1605150c0a1d041a0a0503060705300112050f06060607060f0e060a09290420091015091a07 65
    0x5c54052140c03020b105c40d00040059401030001032810260190801d444800040031020101e0762400000701c0504070660000b90a00e0009080100040805e19610079020b500503c03042c0030501300d0b12500c03858410300101e8410b2098949000364050340c110201d10684060b00c0c5454140b00044400b4421000f002d0107150040c2c8001c80c078051760021070101c41e8800070301500b90020080c04201800c0000b882c0000b03013001d0b401403415160410b8010301c1405403140c46080441140d0314041d1102c100c2031307034183d8403100344010001565a100c17095140740307407203204440b00d010300104206494008902c15100300c8001c1e00c0c60786001e9059803864000d05008482c11000303961488030b0500c21800b001501e129242100001892100505001ca4040c0980c08803900a000c08030120568400310340609401c5580881120425410115141068081851415006120a41007101c1c1d00320b140006411a5036420986000c03040c045000c1b58000f04a02500120300510380045412146001c000d200d031601407 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 649826393 1250 649825143 649825181
    0x1303080c07020a1706130510091a07050405011101140c0c01020c120301050a050405060a060309080c030a020c18040f1403040807080102041703210406060806090f160f09 74
    0x65000441c2d0020b0754105a548200a0104e48590305080000c2c03500310b010305044120001c42c969407030b5a100481c4200b0201d0300d850f0705216040000d01ca40000e4400b20484042d91240740c5070740014085c0e04540f11707082c005828410042c41211040c0f09a117400510704c49404103640e075450740c0a116500940c1803040540d0300300200074182c001440043d0300380e40f01032a00340d52549071500b04103403206280c12152041d0300d0310b8103000c01c6954a041341c804a8915050219441300c0a08194425005400c981030f40d80c00000781ea0a803665020400a0014004a80791820790b040b085410500f6202298024003111070800303840d000c42c501e5288a400904440d003103a00d05178450740e1050401c10a940203407642e0303402040c20b000319403024034094445020310004509004810091980b264506c2c40c3e0030f440560140041002d022058124002074880b00d01200e60301c0c203110b40d40316550301c107114140baa58020b50040c002505420400c40003100e60b0840d0400015042950341c10040180100042161800d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 649827643 1250 649826393 649826407
    0x421110604080c092205070612020408030313021203030702060f1803090f03211c11040603021e03070c0c0e1e090f06040510150f03060504052a0312031303080c 70
    0x10105e030396a40c8500c21000350244510b080c50150031100340260603041140180000c0c001e0083c00000d40740c0c40f04089450422407241ca00114058514049221005000c0041005242d58002440e00c1c01100c9002d82840340d5030724840c0400300207102c0c031b004a101d81c108100010700d500c8c0c17070924284a40401429170707409803044404840041040079150341d200700b0200d0b5044550140600200c20040001c50910044c41154800a00d40c80785000340010700d54041003004c0d140307240e80301060850100601065032401c00401c007411000642d0000c680c0010070400204910510181c1c1902030400d0b03081c0c00800108035102e02103c1ca10041204e0b18600c07842c0c004002c00350381009807070b005900070b01c00f0f0064201d4401100040d070302804c0310005030f007810315020400c10308003084040c122038001d4800185030f01c6a1406c42c1c05d0281000403441520301060380440f05c3c1030025070420303140c032088045429820141100e10f00c503000031075400420380c800d800c010700428018541d0680c006090003000b407074080 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 649828893 1250 649827643 649827691
    0x90d0b06040e1903020606090709030b040f050d030603060b0a05030316170403030e1003051b0a052701031406090c0a0203070623060102060f1603020421110604080c09 73
    0x2c644008500c4803c2010801c024180c040c01281d80206054440a040346890400039240b0350301c0e440001c1542a055000500340450a4445000c65500c4000d1b550081d6111030018060f0000c0c0c00203442103403402d11118030526040e00300324100c82015010358140040310b132540f0000b40d03150a06a42d601d26104101c45400e819000a2001d54840c0c2c55040250102c50188005030a000c0c81d1101803515240901007001d108641c0800c8a0410000d200e56815200504850a00030050f40056185d02e84a682010f80316120b540c40c05d80000303903010000c01c1c8241806c4100082c050380c0060300140544003044041c08048001d281411035030049134600410b580e1a201103604085004407902090302c02c0c00c080c100003200d26500038a0910040000b4140f9051503684560050aa6007400300c8240c001c6400340e021f90103a40017803804000317050420f012500076031001410b03038030102c0f4003c2601585520900c0c00d10140c038142c80d070003801060482400c1050111440c07019104030130941112204400e001 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 649830143 1250 649828893 649828903
    0xf0c0f040503150411030a1713120c080f01020a05040506131802040503011803050d2c072607060315380f090d110402030723090d0b06040e 61
    0x40d840303850480c4203180c00c1c101505c0c0315041e603001610907001107841602013200d810b080c00d1001001c2c001143d0f2101c03202c11034150091035500403500f0007002103204041c04103414049085548240540e80d00e0000d03480d00500300d12130043d6100125800b80828480340c00c021002d09411050001c000c070042e0b8482c03203040c2403003030f162408181407a00020207000d941000c1c010441c0e0843c0300c02d03020600080350760b0003808030b005a116008070320355912414020b0301007904040c80354ad00302c00005500e60035070030b40b0161240400c1c014403004601044000d03600d40648000118030064070720141c00c00c0da040280490240450300c40003042802144004100d407070b080103080e001c0920844c0381c4107092116402031006100411203808002e8814400100906240e41c103c4803101c00440d5010380801c1c140c43c000311410452003600c2c1d001403001c010800d030180c2101e0801d4200500c0460080b07400c860b1088404544200d59160750400c100d4a40c4000158518410741d421580042010072b80c5000214120310307203 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 649831393 1250 649830143 649830163
    0x150917030106030c0e0d0602090a09180309050319150608102703051803030c0d05030601021504030207030b0601031b031b08040c05010e0111100507080109050f0c0f040503 75
    0x480080100040794151065481100c0303581031415081203e9000960070f081c1850000c0c0c41c0a800045120040e5100300c0d00342c002c0c1a1158042150910000599600c107c85080c11030102e040108041003510740050398400302c140c2c42d0614600603d1590b10045e0062052030340a0205032a0302010030f0b0300384203104242c034510680070001441d00d035090340c10142d680e129101ea0b0030011421034035030102e035209040340e61442480c4480145400410082480d5210345100e20000380140c225060260b5840001540100b40990031a02d50202d07201032440040070613240280940e0080c0010400180d140c0c0c41194028414103001520301c10040c4048585c4140100d1000000e542e82034540b1840c5041840008884107842c058081e4600b50b0b90710180c03074069010f410706200390700b0312b032a42e540e200d0b80c52014030310600e40c1680c074806000c07038020002e4101500c44070b01040c0c220b800410703210801d20400c2d1140b40210040455611050b403800e03200c0c0d0185400c03200c1180104004585c0b030302d0410042c0ee0b1 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 649832643 1250 649831393 649831433
    0x70609120305180a02120f0a060902031e061906030209130606121e0c03140304090605040e0c120f07080714030a080d0b01030624020c03030301050a031509 68
    0xc10001040040c11260300808600ca1481e20b078540094040340042e4480300320743d060300e03034440005060640034900640300607003911a01c2195401000c001260304048030780b6100740c2c21640d511040d0714071512030112284030307503510394821b50005080600052420200d02c80c041000114141c91360003052411400310740710380c044048031b1b4140c02004820b2103031078001d00312440c170606007614554039540b010b9400754241d810803c03602e6218080c03005135044040255800701c4c5404a8003020041d154480d00319100f50288030340b9002000509007840d01841116003c10300182501d040341200300b164515403c06c020f2224801d140380b03130141500c108060030251141600070103045240c0b0f07402080c10800d07903141d103005ea04030f104158001a0b86200351156421804400b007a03003888900101d0040c45660721807020710000321615618422019800840f01c032a41d425505114074500c02d05569200038440d00b50804070611003000401c0320500740d1a00c4000703481011a0b00c1401740c5944000c074500400c0403403 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 649833893 1250 649832643 649832663
    0x723130614031b0d020607150c1710120b1911121501020303010b0c0c0a122f10020f0102040312020601060c0c0e061c051b04050112030311070609 64
    0x19003807070208107090900e1540e40d59900e00b503101c3c00110305a45000c81c0024080c45c004a10306040040544040c030301c4d205041401c0110b120307001c2004080c00c0f4411440c6010105031404110b50070360440c4000c0030388561000622101140b59900b80303400c3c400424030701c8001c1da050103800d0000c0f0b450054a050401d48640030340c4561850b496115008405400700404250a040201707907a41c000c415039044458110103103443c0c5094400700c1c4c0c04c20580138051035001c03005000c00301e43d1100e00007800d5280c40c01986040e070104071803007610700e109100000c03400522481702601d40381c51500b1490340c003000f8202c1c03040d20310010504c41118260303082900112130840d400041b00d03403480d504201b0140100018604400b4000c1c080d218100f01d050740780a8000007002c0c9000048064913195501c0c00d00000c860344130701c0141402d042050b04c42000c40451101c651942c02000b20915003030085034181c59081e0910500305141c1d6034180d00500076100e0001c5110011710443c004038003d8840c001c0c0c1030740100c0c0c0802c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 649835143 1250 649833893 649833929
    0x10c050408070f2615100e01090b0310020a050f03040507050102120310090b01050c031207020105090a02010909020a110a0308061c0519080c010c11010e07231306 71
    0x5802c04006800940b42d03251040c504105001d40b50240424054054640c003000c82c1c11218540d007800341c1201d04000c0b100c40401031008090a4a2003801180c3d5030081540d403d03621001102c054607800140035505a00ca003442c0300003201550b000300040d24003400d1803854101c241e021180c403500105c1c1d00341c0d941e81142ea0b08024958042c824498404d908001480c514a80f8400440c02c04c040d900801420a42c0c82ca00038003540d01460846a184440c1422203442e441107100c1c507559a54121558030055082c40c001c030b07002420019040c0b0b22198142c483c62007883c2400203000c029004080b44008001140c4210740e091041803200d02d2400b8000e5664511600c4c042045c002059500c0340654945420380840e040840d1002c54808a080a40c0440002c2820981000c4010b4044c0250720401946408501c610311500306241c2106c982c08200240503a010101e000364840c5902d120740261403050b45545000c00a0b10020340c0c035050030090a59900d2602d002060040b12015000859446151401c80b = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 649836393 1250 649835143 649835159
    0x7090207060c050f0301120201030f020d0c02010e0607140904060b0406110d0c200d06020324030601081c0207031a041a04080d020a030f11120702030a0f11030705010c0504 75
    0x100781e03000354140b0f02d20300200030303500d00c40901c81403040301503501245000004584c425080548140d030303036034025034a5050b0980d447c401040790501d5813016601c3e06540c00203841c000300301148070341507507254001403802414039032109501041c003943e403181c4da485011801e076640d00e024002038002c540c2c82680ca035085ca64094904004480c205c2c4c10300609890440c000b404e02d1840e44100c3d552141d03010008211100441d041c0c2c2c04d81d071401030030302c3c0c008410410300b800750083c240701d4542403041c0603104030500c0041c0345d22503c0a010303480d15a000b2500254015114141c0078444560502c100c4070659a44c0e191520000c01d103801444010726602d044c0030030b20000003041c0b0001252541110480c3c10695100701d8544981d1441100490300840d4540c2000d009502018a80000c00810b1003c110542d604001c40e81c441c41985080c8420310000c00d03041032000003611403058660b20340d41c4003010401000d5070040b2101c00350340700300d00c41040342c940000c90038080d4004500d29610380a8549041480c0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 649837643 1250 649836393 649836401
    0xc0613180504050f0a0f080a0c020904080d3204021f02160518071404030f050102030103021906080609040f082b09110f0301020f0a0203070213060324020c0709020706 73
    0x1c0c1d00c89171780501080c0c4045001c016520001561061015a80c2c42040e03200b074502c0c080c0000d000e135204004404000c14002840c0040a100c0301e00042040610f210001c0c071440361803034183c0d214019441c10f010703244010400170f403540c000d03000601803a03030000c148443c040042e903c0c3c0a200010303005014004401c40c0385502c1407000e018100c2d0103419920b084044c0c5441c25034003d00700001c00041c1203114105501010440d0040c43e0060758170114180c650509502030350080c03100328003c0c801141403200c80d952040c0e42278141c0b03106642e008441c0d19504104000020003a200f52140800011181c000070144c00040400e410705802c0000d5046080c40c80030b5803200b160b00301000f000e08150b08000026801a13a085000804450340480c101414000c46d00a00800e601425007a000048442001d50000094000144200c9a804206407110728860a4400c00c0c4001032460b00441c5030004040d2141040300d07010740740e80b8801400c14440b04c5c521454141c0d036030b014030100e0303a00048a40c203000041c01 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 649838893 1250 649837643 649837663
    0x12130605040602060a0f022512030603051c02030912010b030607031b1112070f1502091302070f0c060f030f05090c2e0905040e0f0c061318050405 64
    0x4005080c1407421901139103880004055402c002d54a044040e4450380c582d0540b01e0701807400d40002e078040034902e5200c44469207511305590f880e880d800740d200b8061103030240398142c80c0d000c400342c140c40321850055004c00042d08003050030b47c082801030140c035840d007019041489491360004541c90021005041c01c01c80c000c4d0405003014184035030f203007106503010820052282c062800d5644205601d1551342049141001e1500210000825400380712800304620402ca01482003026040d030611400d50480c42136140403508401c0741380151094079210ba014041c15402000802031000003a0b07075440d03000340c15802c41e40100d4142512a501c0344d0303140c82106004180341008122600300940465924000c003054544607540d2102e00041c080c040d2004041c103c1d04c40c41c0f10300e0f40b841135400041c24408031402000e0060786405050ba504450000d0103441e9403018101401096007028140844c0e984500012405480b0326400002c003000c187c41c000c1c1c80720342d04140020303003800c0c1894850b04045d0520 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 649840143 1250 649838893 649838897
    0x1003030e0306150114070b01032a14060a1709061e090705100c060c020c01031b0e060d0608101d0a0b0619150f032009040507030608121306 61
    0x2c4208680d25203000d0f003002810409081c800d2080088112a40461160020040c9009082c00001003044915092418802c0034400003584a0b89040070150200201d0b1007804000b984810a403100743c00d1010051200c1c40d09403a06440010300581c0c03c045168003980d1071403060b40408100f200510303483c4a15160000035041016450503e0810b60b9a01c50160043d18400c038180185068007a001c1e001340303005c039a0b004505102c40d0303400c0d090194440071440400350100342030a02c0744101c54506a001c0c1481e018a885070710703038241e800e02400781d90b800c01040074114580d543d1010804001c01c01c0000034110352103a010549032038000c10013008608103120201d1543c010003444d400104140c1c0410f13409036081d1842403100c41d00f40200041300702c45500108429000e03499000140350f111035200381c1c107000d0703440c240324501c628018001000861703840440b1801d000e01201c41d1526064104680160b120301d404a140c4c1d031a040307014180149a0b040c60011400014508c0150402da43c1c0100104032074 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 649841393 1250 649840143 649840153
    0x80601030e0114060a123c060c0206010506071a1911041409010609030f0204060f0b3a320f0f06060901030509010603141b061806030714031003030e03 66
    0x1a47d21410441c0e4038407030070720507400c0002c0c440f00055028142c419850040040315000340d041c42c00d01c50024040c000384400103000b190004101810201c040365407107030b80203038000c100c0301c4050103500303404402900402d99103110f000c101200750300f280940e8080105184201c0e1b511850807484c16450509900c0345400340310040c0c0100034a6402a1114040343d40081c0b0b000150445403002400400158220200c0300c0c01070392002c10002c403850043c00d00c28280035904815500d50200e905514041d1250f541140c00c1c0141128080c009a900000340080702410216045001180360382c81c1d0104094181c041c0700300103000c2000b00d221002d0301e91b80240f00003201002500340980400d886200300d900c51070601d41c40d4000310b403000d6030941c400001544c101000111214050220b1522848540c8814080300032481400d805d03454031030101c80f003000c6500d04090041c960711080c030015400c010048070600100c07080720000e903401d04c4011032041d00c030480380c4170350340e0308500d0081d02c2c2608008020b4029449 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 649842643 1250 649841393 649841429
    0x10051e1b0909071b2306040b0106050915040605030702070b0a09031709120d18050303040306091b0306060f060f2f1006090c1103030106080601030e0114060a 69
    0x844220362074010300759000b072610f03034500c001030707034480e10414156507001010711004040c0b140b03103000c0030303843c0403080a20802d048060307443c16610301d000c1d24013600c00c0d0405001041002d008200034a00e0746009020350580c0003441e030761185550443e0344200d01254000042180700d5505014110241c101101d2040c1031400241c0b00800d83712041c04020290440c3c001000d16400004081d00ea950400412005500001c070016984917441140b000011407040801d4541105000410304c080c1d0740c02400540c201403464035510050b00fa042d00a03550000080b07112400030b01e588070090090740c010980891011b1030400c0d07082c0780381525440801001a11181a000d00382e100c2003c02400090b04a14404480c0461101c001102031401045480c400e6040b4801d8290064020070f080743d000c0041000010000b0b4801d95110458400c0130713899400c104014000507000d003910540001c410300d40059060000b042540c210340404128072044091002040000d00c1c200207000c01400e0040c0380c0c0045044 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 649843893 1250 649842643 649842691
    0x1407140f0d06030605090a0b01081f02090d12170a020313030c02060f070303150602070302150307020a1208161b06020d0b0409120906030b0117070210051e 68
    0x1840444061800d0005008018140160441405950044010041410120b80c07566841c48000001c43c2d5040360f103030000071121b001081d0040200c044a00c4140f14201c10802880294080c00200d80d02c0040c0001c01c10210700b0a84402c1c21402141c2c0301c15600c0121b500310320406950041a401c501401041000040108a090041030660601700103840840c948005070207401190302d6402c034080b0200b0403c05244e4590041c180d8090301c0402c0c2c00c0c489485560403600c49019000182d0010349064032518840a44401194417140358816a05103118640d01c3c1c1c005c04031a42c40e820000f4684000b40301c1070080b090300b540d0b1424428101aa4001d0700341071207051b0f68400d00e40c098001580441c0c1e45a210120f508101c03000300340180100b02c82001d40c80d104407003480d0181c62000040302507074041180c9000748125040d182050310398a48000013081072044080e070091007007085024180d44d0002c500320900802d800391107580b4551200d6080c44980504840000b80054032a800e011480e0b80c80741 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 649845143 1250 649843893 649843897
    0x12012303030313110d06241703120903040b04060302090918071703120403051b010603020616050a02031f111905030c1e12131a130605010306140714 65
    0x43d44044c1c42d01800c0d4200001039003900308058060070b85410204e070482124040d41c00d03118440c49000d0620142512a00000c1980c3c034050380701719030727a4400c004540c880d42031040c0c0f03180d02240540031645404e440e181c040800341c000345c2c000c2c000700c2d4010840c0382075440c003001665444a0459040d00c0820103503100aa40c0d21407501c106110445d03a040013500e0b5841c24400c0380c04001c181c40c0c3c096140d00b090724004065522110180d820303081000540c10072800f040c022442143d4008200a0905c0c0c070040203102d02c3d40c0c1000c1c2c01c81d03052013820100b100503203043c4107200800c0b01580e140804000c5c01c10340c8c0016140250501411640200f181c080c0001040714801c00f582294503146450350340e50480c0c45c0c1a8403490480e900e220a40b292581f907101d6210f0000d064141680c4100c04032a103410f1f015125a44a160004104144107215600c1d8400d0300e800c41a4003000585d070080e1440b500c0d0b06e0312000c56130700781c105840c1c4685801e00000c1c911501c202d400d4200002d07150a62201030300303494400707030b034 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 649846393 1250 649845143 649845181
    0x90207112d060d0f0516030e0d0c1205090d1104180803040f0311100c1b05031204020f04021809070c0803011203020307020405010b0d0606050c10050c120123030303 72
    0x540d0001c51001d02c042074a80c41941034002d0b0038020030840c204144019841e800b00c012000c00281410506c8c19501000700d41c07400b4140c01a194603440102e541d482602481e900c0c5006020010240035400f144d98542e198040c00b140654100c00300c09034000c040c801652004004030f51192038401c0160005091002166801a080142c0c002203403010b281c1210807403140c104d0300b9118030a00d0030304040403440d07034854036185a00d610303031001490508071404810030445c10050516001400040e030f1182400b40056400f5100516403018006440b00142c1243c0022140c040c06c04919040c6154900b440b6174010b03008540303824580d07158051561140c1040c40140606140300b1410150002014020001c0c6c60545600a0051001c1d6854104602036078000c3c40407084e4503804c200000905a00a41c2103581c0a803800c000343c149002c8440e00c0038003400001e0003a0021070410054003007207115034281140030305041c81c5102c00c03801d8250800c075010f80f03503401524469081003041c40104403410190b5829 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 649847643 1250 649846393 649846399
    0xd0b030f12030603030405120607030b150306040e011e2301290702030a11100801060504060f0c0f0602090114030c0415020a0c030506070f0309200a090207112d 70
    0x6070343c0c0c402e0042810341c05260b100e90b03000403180b03e0070300e5040d102003601441800555070801186100408219103040404156400001d04201184407810b00e0b8010a035a4188a40081101045800310404c41d040911105070215620050102d01c401800104102c540d83d040c02c1c600341e5414200b4942c0c141c90b000d04040f031001904000729942e04640e00c19106a2500107050b07920007071490400224804011509900c0381140002420b00302d0f0246c04614141d0b103071039944038106814440e003a1380780441c8520080c144004920f15400240c00243d414440302d21591015840700000d8001400c02d664515180d03000d00003e0082205101e0450103441c116041e8680700444801106400c1c0d003411501f4002919004030309a01105210300010214040d6442e41c1d207205104010718000c504070740c0752a60090801c5210409c0318540c549821031003410582c024032001c640ba03070340c06259089a02000307040360b44a12041c3d4076030702850a502e0105100d8009005072200c1c148a10183d20121020b0004600c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 649848893 1250 649847643 649847647
    0x7020c102115080d0315060512061c17040f081b010c08040e1807050d051506061b2b21061203050c0d0c0b0f040f0c0b0d0b030f12 57
    0x20a06280c5102e26000b0400e4a05450204040c80303070090140c5480020140d4a131361083c03000036403e118404032619001090031055254864504000201190305a50781c00709501c081c442003c1f03000c2000240d10360000840140c1e0b202d02d0003c0e2040c0080d002c0c0c1c040180c40d0004868860010b02c00100c452000303409182c24020039100c2e18000420303000e141c0000c111031001c0401c229622017406141d0001d040ca15040ba050950b5440410203586842c00c00141113401800b00e2240c85020010101d4001900400c01403c01c0003a08001c082c4014250300961070f42e024811550002e2140e41d000c04c8410b070f100b06001100b000100d0060411072005203415207101c48407a0350b80f1004100e50128020704040400c01511a5490038001c1564020641e1044540504501215041e000310303080403c2e01c2d848004141d550751001c0c26182c6080009200384ca00320030100c0c02e20002900e034020a4040d1201c52036140e1039044a211207400c442d004011103000f0351102200d41c1c0500f0001a590071900d40380c0300c50030703 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 649850143 1250 649848893 649848911
    0x271303080a110d0507020f070e0606040b1b01090b010f1409071d030102040f06090902121b0d0f051501142203020312030f0c070209040201030c03021207020c1021 71
    0x803240f04103d05008024135000901001c41d901255036900c082200045504064072684510540941500e6540e0700590030441044555540c0010305080c142d840c5914603090900c080d02401e481c000d8508036001c590034001800001d1611100c407011341207041c0083d51081d0603101140d410900505010113103c48803440010203c20041c0c0750160410180081d074849654941e4018800380500803107020980c40324001c114010584242e8000c9040c1040c841040d8640e0644030014134100e0b0300c5505016410002460411000d01407003500303080b0307410009030700d00c0c0250742214414010f0320307034504201c0d061180010140c580c1043c0c0714032082c94910494268211034980c1e07885891a40004e402d230203003160b450403140c44580074600c501c1c4096a505e07640d40d034042454002d40314004000754058403d5000c1400342d4032070380c4110310810300d904005191030918a94064140001c41d00c8500590003c00162080e04000e038003d031130042d20342003402001004041d160301824041c410070403241d5880d103840e = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 649851393 1250 649850143 649850171
    0x160b030f060d02030d0503180a08090d020d0b0c03010906050609030601360b0910061707030e0604050705281802041710060608040201020c010e0a05271303080a 70
    0x142c0c250319030090854403032906003400689603400488010b5507a401d6111103544490011480f000d606d83c0c0480c01d289042a5241006100014094280c0c1c000f0085890880001d0000c1c45050080c460440c109403207624125130142603d04c2d40d08080c1c02180c0901180f0b54545002a50505641d100c0022851060742c616808860304140651200c600305405d03100c500c002078581c4003940f018815100c3c040c1a9840c0c07402070000a12074030407000000c6181a14000380c0020600040e080300d400c0c44d01003000c8140d41c45151401000f070350b096a042c1c00c810760801c40c0d881c2c400d0724451840b048007054910120842c0202010118038858000c050754100421b2030704420660480303000d030070148502410000d50426003036882c034000015034085803030240c01140d118001d242070340c4250ba05900078089151000011207107040b52950b0243c11091203030011078656101885110500002110b09500d03042d403444d5800044d07806802c2d109151380242140c80461b034400c4075268001540d5401260584d81d401e05 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 649852643 1250 649851393 649851409
    0x5100806241e101407030306050f01020303130303021305060a020c010e041503080309160e0114090103080a030f1104150306120507050603040809090103230106141c02180603160b030f06 81
    0x10813464a000080c199040580550004041d900140c0d1505200c0d40c02d04010b90340ea110550301d408519404112030070002e071207070300100350441e40230a0007c14a551400030400caa0480091800560054000940c1d1560b110301280c40c0800c044070248000f10031501300d850b9520b010301028050b02c4000001901c6290208040300c100c01c040703140240703201c0e92200c4401d0f005400b801215420b81040c0662042d51400381fa00c030303050341d81020b00f00c1d2400c450711606a00031309000c40e03c600b2591701c481000c05c0342d00d0b260002e08010a081010f400403641c6080005044410341e40256520003d0342c0318030001704000103001c03c150341d000d560350703690781d1101d050044150290f001d506501154100020040201611050350640e042150003d01745442041c21400e0b2111402a01d8440c040d09a070180d052514410111b91590766021400009240c0d4000c18602d000d400340041c0307200f1040d0140402030400700a0f214104103100301d036030702250400010711043e00c8041d16a44402c0c070990042412540d403004 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 649853893 1250 649852643 649852667
    0x904061d060105010e0d23010504260d0b0f0a0602060601020d0302040e010e07170c04030204050a0209030c1011010e0a02010e010c0c050123030a05040c0915030605100806241e10 78
    0xb000300e807d2020300c0d4019000e4401128200c413110700300f1041c0041600ba0140f800241d100e580940303410120403180f42c20040042e00b0303000d079008800d1042c0700d07841d84030301e00000040d10080e03016164603d42807002a241014840840007018410041041055090380c1d4160541d98a0306402c001c0f9110928100c4103905c600d9001402c00301da12080c00400000100288202e9100395424082650341110f1142240203084145070581c00596072003c244c80c204000100320a801c0c1421020340001c0c10345c15007103505044103c8025409108a8429581c1041c8c03003480c40e400034605800044210359541c0d1104485219040c10320421000303030601c00c4100307024503806101150005489140110101c0081c180a550540310222001c0c0c0119417000390b401200070840d90300d01c146a19524607600c1074001c0500528501034440c0c280000300d42c05c001408003500440c8185076159400400303251100418215142261040c418450440319070304484104610b0020101c8041d440d092480005850301d4000f07807 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 649855143 1250 649853893 649853933
    0x90e0c0120010b12030705010b27041e030c050c091b0904110f0d0510080c2101110406020706020d080c090d02150403060b040504210e0904061d060105010e0d 69
    0x1c4c0035490a24001025040b480c4c0282c0091011600c480103100310701c00d1000262208490310500e1000c01ca07c050307070302904244105200d07d0302c0082038988214a404100046000031044550501840820084947e41c24021102e07115241040c0300480310301d0f02c0300520401c0ca050049800306840e540c950003020340f80356031115142e0703d40c0d044c1c110991541c0070442d6884000d180002040045071031510b41400d17038480c623004203055034a0004200e0041c01085070404540c1c1e04202c00e2059400a0283c04040d0075120a429211414140062304218098019000710b511610001580691211445030400c009518280d030700d90400000c00c1180d404d20724082d402545408030002410003a00040041380e005100c10004000c0711020003055540546001e0f1010740c40d40403d25488128000d00040d0034060304080c50215110000f28170072541c121816204143e40c3e1003c014044004520000d01c400f000e80a004591b043c500060300200e500f41505005186272050031080084e054481003103280c00b0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 649856393 1250 649855143 649855159
    0x10f08040512120906090a110d0609120302040320031b1f020c03070602160329010303050913050907060822051b0108040c030b1504020c010501090e0c0120010b 70
    0xf4408102801a108556a4807401c00016107403103002c280ea624140d404025601c10405000401610b001e0101040c0c0f42580c5d0740c00800009240e840c060183c600c50781e100940c5551440c10008001e8000300d5800a4240c1203505c3c200c02a6800702c1c40b02800f0b040c1d001076134040600c0f000030400da0950501e0307030b0000d4040346141071041c270780000d50090803880403000c4450302c685800c030407602c4804132640c904e2044554103041c000601e15503c034280c0580c483c2e4040600b813445003d1680c10960a03071083e03010942c00241e46046062240d003440b65050a01014411420300110711642da250030b11a54007007000d4100072840b0074502d51001003800d00a00015215482141851511850700100d40380151607107903685029540a270005610031500074991848051a603101c0d80310000c0000c00f1170215611001c42403110fa901d600c0a02502515100005490742c10012240c1c11aa0207860b00805a8002c050810366603910540086404400507819884000c4c0300110a01420701103003116449040 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 649857643 1250 649856393 649856407
    0xa031b030501080607090305060f060f0904061a0d0515060a08011d010e01110313080d0c1d0406140d1103190c050118060c020d0b0a1d0c010f08040512 66
    0x4180c001c0790684840710b0640b0110f46540d04140e0380d802c01031000030400e030884000106908041c14ad400c2e4440d40181c11038607000303000d4001901d8400120340071582c09940c1c40600003000d1861450307a0104000340c0304000103280c147c5540b030703683c43e011606070310300003000c13000410640703070719220f607004081810088c02040c8800d024415041c20500072080c40f0341c41d0114042c0c400005001d007003d00112102d9003450f5880301044140c0740c50304080c1c140e0300b61408006590302c51829109600c000400e550350506148192001e5000056402c80094803450403c003003400721580410148840c1c0d03c0c1210030b4800e840c4503140021100e15000480e030342c0b40c000c44d0601d11091a0b01c1d1a8010118454240c1c6000313a503c420043d00e60001c00700b00000000803900b001e102c514011405580b0f16030008101034000390107543e030780c4a004000c941d81400f458031810f2101d904008419004600d5198201600403042d5120000b40400541655401007011b0b15002c101404000c0c0200390b1119240da070019030742c0030 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 649858893 1250 649857643 649857647
    0x1020a2102030403090509100b1306020d23070f05100b01121a120c09041b050105040e0a020a0507050307030203030f011d1611070806040b011205120a031b 68
    0x3500e44948145030804200c68440303003882103038412640342d201c0400d65400c5c00240264640300a0100707555a480350300202e2101c038140050802080182c440d40f0185007030900013810030343c009007a00148040f200e51030104c05442c08680c0441148103d00329100e015034144070315440301d0b15102030901d02560701c1c02500290300c2d0304290000307502a22500490b41c0210015421100c0d074034504c130030260b010311151003586092000d81c00720340c10040c01c80b807110007001e0000d00204000c1d81c0844900c501c00701c3d80100240b084480c1c600601c0242070180c00c003882d21a0055400c2d2008062602440d40041d082d10518002c1095510494002c0c1c2100e407980f881d450069034903031007500d000e1207064098000140c40b0400c2220400400c01c3e484a4001c580c88e4141013410401d0451410000e02c6190702c124202d4480800c8400010320180d001020242040d040600843c0010b810001d071569580b5121b0011440000791181520400700040f60340d800d20032130440007452104240e00000120b0000f145a1507 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 649860143 1250 649858893 649858907
    0x20310060806030d08040b0a020403061d0f01020c0703021201090b1801060e0115111207030c061103090307080708251103160905100b070506070e0a12060c0c020301020a 74
    0xe203a41d10780820607101c220815541e200c0c01c41d900400107518100003400207058944098104003844c90250400ea280c0d03640c4825103641450148800d183c0c4514030034050350070030800c00c420900100071882c02c0c81100d20b440d00c81419000203030003510262540341080900350300c1f41100f6a0481c41e80482410650140d20a00d10403040358601076023001c101082601001600c24100e8050000c1c0000344030842c0001e44d0204102d121a6180b4090b01b40c1541184030082c004145c1c1034440c0ea2004070f04c05041ca88003048440103204404958018810051310510010413294000d030800c0106031915824a0040382e10711614070b101d200307015214141010380b80517840115100740b14054500b1054226010b0581d140760550103019400d0300703448100070f040c0072580002d811806a5000d80c80c02074580c3c03441440c07039000500071550356003c4030410804c280d00060440d044c01084402940c0d0034038001050100c2c160f81030f00641019030b91280c0d10f8070342c0d0040545880b581c0d400341c004d5407a8001120094240 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 649861393 1250 649860143 649860149
    0x1050f0f0f03090129010c0501060e2d01050a05120115030f0203250909080405060c0304050a0e040305120712240b07020904080a020a0f2004020c0606010f030f020310 73
    0x41d40c00e00152940f082e81c00711300311015100b855030458805da5001c4c01101c011014a4040c0c0e90f5540c0c0b0080450481c1c184c61820340310710795007200040c0c0790b2180701d0102d908074152049400d17880c00c000010b01c15581d914102c00200c0d18129000300781c0c0f5445203242c5004140b00c0b503414582003140c4900000b046071000c0031000c0240200c1c1a00c4919202116020318002c90b40e0300e006034440c0303104d4140b00c0c082842d4421500b15000d200c8950810f5182c9000ca00c580c0c0c00904012101c0e840858108600c0c034141030030202420146225140f82e05059030003410501840f88031090711506600044c43c017030702c9203244e000041c12404050040c03800c0c000d034498a00c0c0803a20500700340301800380003080100c0313440708541c00c455000e4050141a503031511400810780140010004500400b040c10012a60706044451018028071000350016100000c1400306550000200c1c0281e0040c007800015402c08580c1c0c6074050300a0070990001c0300c918030700301c00070000c1c41c1085459070b01c0802030000c4c002d1001d103d4415 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 649862643 1250 649861393 649861411
    0x20a090806011217090102120c0c040204090e2e0903110a0c1a27060405090c0a0e090411010c020a0b04080624030a03051e0a051c0e0c01050f0f0f03 65
    0x40c031901081e13030380e1a201e001000740c0980e004045100ba90958800140039031000da8090301d01c900030340340c009002d03a44598800c041083d190f4400c0c0f001c0003001d1020071a03a503000c041d070050081c88455100c3e50004028203001c0741c0b91b51404110b052501600760510b4a0283d4025940c0030030092034403d1000c5681d005900201c040001c1810403585660202c415070009c1c0c0300020440441c4070000042d04007071002c80d03500b0174024032000409407102c0000354000c40b40c01c01059100c071001d6030001c1c405815001014400d00016051201003414070101e44102002841d01c0b040d4040c190020808090082d031040038540c8000900041418001c140d56001c1ca8101c80f003110034104000d1f0314481c0c45002074009505800044842000070b001e60002e203010750601c138040070020b000e8055010544c0008622001187c0c000860040c0090032030152000c44c564400c003040315a081030a200e5607104002191810b2003000030303d11694140240907100400e5405082a0341c4541503101e140c402c0e001601d050351 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 649863893 1250 649862643 649862663
    0x40209150f091905061009050d080904060f03050c01090b040311150a0e04050903120c0a2123010f1203020a150c0f030c1205180a06050712051009020a0908060112 71
    0x40d03506c1c1000e8000444d1500e59151a80e19080808014000c00480e0086404040400145002d03450b14000c0c0c6000700f01c1d640710840341c6440d50800354140b44c907140c442810018460381c10304c1084c0c1040292404d680c1c100c003070240b040302d609000c90016070840c621801140000704007000090341c0000d801c89011820f8134240080d456541034180c0c0c90141d0a03012490b240300a00054001d00c02102801340d01c2001c0c41c1204508040c0c4511010020350341c0070b0450501c2c0c542c41c2c09681c000b5881c0041185030000804c200c0031390724107815011250340600407640d0703403581004001c00b814800c001000c8036070382003114120941c0b03590710030200400071b1283c0c03d03012850700c40d43c100125009100e405118885030325000004015240250004d00c0c004048003a0300505800008188008210741007140340b00340d0700058641048000034000a0810358076000807404c200800442c01c840040450803a90752100151f2100303101031041d02d80d480d5a4115515070f104040001480510717002d40a01c03260f0040700449 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 649865143 1250 649863893 649863901
    0x50c1f020d050f10080109080a030c200313060c12080c041a04050114120f042103140108070503030f0a0c02060c010912050c0d0819060f080106080105040209150f091905 74
    0x542130350f04011f0084c0901605020340280ca43c0260840440094946403a400400640c0420b11020f1042c10b50000b241c1d1011400c8002964883c408101070405400c0604218401c1e640c1d9425111440307030720361304101c15140420000503145e400e54000c2e140710301500071507406100b1031518a0300103101e49400a041c0c251084003000074070040b100403080c281d00142076a59038030034000c17400d400500104c40d0140f6852815910301d60500c5003900da4165968041030b1035846c0c43c00c010642c101a0080d85207604444c1c41042607582c0001241c4043c000a8156511103103207003410b844024080d503000c0c2d0032071000102c121000d4810351142c03200038441c900a02c07941c011503104403003d008150a040ca568021740302082c0140c051005650f1201c69098401c00392a862088101614503a41c40071410000755501032100d90b4081c02070318040d01b1904000c1101d454550002807091201610b841d985d0402c040021541d0380700c0c440120b4400101a1941e141804e003100700707040d100641000e856856203050085 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 649866393 1250 649865143 649865159
    0x906021e04031e030e0405040303020903070519030308060607020307180f02040b161119170607090521011b18030c05060c07030f0f030f050c1f020d050f10 68
    0x1c0d03025250450341d2040010f07440107684a5801000030b040c1c06001c07056000805a03950344c082d0a114034440e582c050f03210380c1c0440602d85000066080140700751200f00c0c0d02c81e4084600301c0311800300e0783c15141404041e25100c000ca401ea20410764042e401d40191800850030305c00d9501040513070704d98050f040202096141c4c0800c22400799000704864414108000d00700c50708880042001240203c40e8010040e045400050740c1d201010b82004070810075480412602c3d00c0c40e000c6050728606403014040a1070450700040c0b4040a50103110321030340540b400c86100010b9035003402c8030002105c0c020042c01900700086490000550f000d0300c0011811110510000142d10030701042321383c00400c1c8010a8202070401405410080c080900fa00c07401c00000086a044424641d109000c0c002c4845203800c3c078240280700124030412076041c084100045403502d200003400302c43c00804600d080c540c031100000034501034400d511044a07018209001d2003c1c90350b0034141280520f003130b02d522407c2180c0e103000b8 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 649867643 1250 649866393 649866397
    0x605030415180809040f0e0c0f06030f06040908040e0108011506180e06040906050f160206010e04150609020c010b19051507020402120f06040b09040203060a0c030b040906021e 77
    0x70302418540710242d0580010119000740100e110010408103030807003044080c030212001c000364a16150f00c000703200401b505103c8107000f042c034020f031030042c03540c41d00c40303050041d04a001e800180607030f41c0d4850880910a01c04181e07800b034022211401036a503036580740c6901810300540c11100050481c40b000842501071007000c0745030480101c0c02d43c0e1603807504100840d081401403005402903141e11030040060b00c07510940c0c0c0f28042d040e00201c440d04041d154140c002010a5441040d5030040740107220540380c402c121a40264000411882c450000740c011024020503440000c0c143d0011802110580040d044852511001c1d25100300c1009200e4030101d980983d88280c0f50006c00080d801e9000c00414001066607500241002d1f1074440405114082c41d00c040740c0c490303100307000c010502c0f60324a094050f0380c401c8141280e0046aa04254001a40f617981c05020043d101e961000c0e0f03075500700e0090b000b85000c075038000c00c2000805981c2c1001e9010f9406070301440703914500c00b190140031640c2d881c1 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 649868893 1250 649867643 649867661
    0x120f010f05010c030e04150b12010e040f0b0c1306080417041a1e03010b04181118030c27092b030b04020a1e0c081606150605030415 58
    0x148019002e00c03d0b4800303468030ba215081054105445024181e220034900000c04010480e41e0b51203036680d0705504030342c080d6070010307002111180200d4007400003064203034260103400c81e00030707180195540340d0640154041c071410a4402034080d501e04000b40803500400c10b0740c07045005110090300d00c811000d4282c05845107000e0030641c100011082c41020b8501e03006070610308042d403200140c0d100c442c0800b40d42600241e0010141c1c1000013024005180303101204011407072070820910200d5004c460f241203900603641d9613485444c080301900386540d801c00110401010141061081c00c002481d2503e20441482c2c4140462002c5004243d00003800030b0220000c4d20001e090b030784040703007512401c59540d00da601d0740030405485080d40c610b02da840303200801d40340e2000d4440c0e07441000e41d000d0441c2d1500100d030100c418403080034418004107038248105c0f800c8008660306910074005601d000c000170f2200c00d4009100714604a008622a41c00c8401036000728004c0b082d00d00145420203000082c3c90000c2 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 649870143 1250 649868893 649868897
    0x1031a0901060f051c0e1603080403110f040606050301090b0105160b250f1115151309080702120d0e0d1e03200c1e030102040b120f010f0501 62
    0x600402c02280705803419031995599141c940e26004056021203c2500d0502c14000542ea0318007041203c44401c1081000c950b109a9041e60000c0c55038542820074040d82c070001d002c030200d460b000680c6a40b80c0007a034900040041c000c001140d25020002c0040d0824015403e000d0302c0c22990741020742c002e03005c0e22598455581508160359050f034034940c01a42c060815071864034110b100380b240e500084004030800e0705958802800001c0e05c0e40040468071043c440031040d800c03c000100610101c002d1060b40000340c841501100720002c00442d10490616400303685851400800da8100b1480b01d0080c24424000c60743c0c0c0452400410800e40c0303c0201d51900c04c0170a111803016250390031301d02030100c2d4080c001c1c28404010319044682c21101c0b8031717040007180081c28940410051541401c80600d40c001c02800604103015420301280410702e8042a40c0c0744045034036080c029580d4250122805403c0c005984d548400c100c3c0e0081c03c2100050303800c0c02c074103c0043c0020400c07a80101d10003003162130507 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 649871393 1250 649870143 649870159
    0x1005040305070b0a0309020306010e071403072f01092f0a0311030709050f040302010c050c07061b060213030b070c170c0703020a0b0c01050c03100315060e040605010501031a 76
    0xd43d4420320b0754000c0846809068441c0b403880050398050002ca4000c0c002d01d1912019441c1500c0c0051440d038604810103d0744106000303100c1d02651010490060101c40305820311080c20003002c0d004144210780301040e141d0b091500e5a001c11410410704c00900d0031208030032149601d10008100c0c014801440e540c2c101d6100c0f081000400e03241d00d40a45907900160a5885841d280c504000a8030b00440e07010641104082c10b1204041e4244100c42400e40607150031800d00386087c40d02c82d1141420700c03e1004020203048002c224241103901001400d034080b00456446407904041d100301000346c030040e91011003480000708224050161100016400440c518465108404400d003641120521409500c2a440040016240c150400015040c0c0a0345607450702088091142034550040515020710800c2c4140700c900c10701e400d034650507642d00c180701c1c820310540f5400000040420358010500d0500c6a42403001b440200c1c1d1101d07050300c3c6c00b0b076414411a5007556031920b4000035001d103207412580c0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 649872643 1250 649871393 649871399
    0x21209012f0d020406050304140c0a18060f09050402120705030d031802030f0f1e0604080a051c0b122a010e1302120906100b0d06180902100504030507 66
    0x5480528041441c0000701c40e080040450004040380c00507040366010503000403d000c00d12182110404100b90643d004000300303031140c008a40004007501c00c00040001c04072001c104e0000d03680201e006001c030800c000010310b90b540007500141c01e0644040e03001d0741d0a0444040303100700108609081e02c002400500f085101d81d901180101160310500020f5081c018403030005075001e110410284800400a1401034030506415040440d00485803045060302429104540700200d8855882500035410644a4408507800d690310302c207401c98050040001c080324000d1242d50780c04003a8a00f41036030410b1101640c058544c0c1d0783c18101e1541200c5503101d4142d605040c07405640b141c02c0d09410324000c25141c10500102c0e0300190782401d5036207040e40226000200420b4110340542c03080c140300c0108070b0350400c0008505220100d000d031140e0128006070105100758030740c20010003054110412200030211540c004001c280702d41e001c0388144080c444c5201051320520a403001c0d40c1c1c100000d4004289 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 649873893 1250 649872643 649872701
    0x90f1b1a0a050c06040c0e01050d03020c09130506010e040605070503010b19030f09062a122a050a1701051c05071a0a110a120e0f0306090102120901 65
    0x700d50311040400c00200841c10582000303000d124029446140303050390345401c0c880030f1488080140c10241c01086007141d40030101c2e50014492145080c26500212240c646440d45220503405800c05040c0384185000051044612600c2c0d501c5140541810403050704d80078800c0352144000c0c410051a603038203205003071151031810120040b540e49c0d0308002035900c0d500d810f19016118904010344503640d4501c40307120384421b29a0503140d010100c0c035001030744c1105144007034000340d100860081241d90707680154102212041000444540f54645d80780a480000c0005106912204150001400c405100380701c2c003003000b0086044c0c9200030702c0120483e1000003900c010850f945000c2d01c45214600300001c0407010b60401841c00780c0070607419507440c136560401801045440349044201e42c03212141c20045414081c00302d60510700742c40e2801c0201010000160300e901a010358582c50b000d00c20602c0314209055000304207404d0340124051169a03441916800c86440c441c22201d001e14001d100d8008607 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 649875143 1250 649873893 649873897
    0x1060c111c02280f030212060f07050304110d0f1104061511210702090c0a08060f131509060501110a1b03050a0f021816050c030706090f1b1a 62
    0x2203a12007020108522004903030325140c0b181c1d200d603180c4041d03404c0070300c15410301c0f2038040c40d1001703044c004118600300340041029001004081008002004c8040341c02c001c14400c00002c03e0100501031080d80e030150820a00220b1204800c64852040c044002541d04050140100b1507851070080501c2082c950700030764905140442200207400f40544410a191034003000301c100250001c002502c1c1c170f01a1051040d00e01c40540001d8207448107104400d003071540000d8099211405403402108100a440070a04130b41c0d061040c4541c041c24100c900440c1184485400101c070503040c402c1c4081070756034005484102d48412040d945e074000401e01d00220b05100c0c5034080844041d60300706101c0c0d17600c0c0c40d0103040c6039803080200ca00c000f00451380001c0d407400d101ca24440c10700a001309015424100025a403000c0855091428840081a030607000c583c10703c203454000742c011400703022034180d078a408100344141c0d40c0f084a504d0001d03201141c51221010b0240180c44606104408600844020003859 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 649876393 1250 649875143 649875169
    0x1506090e0a03080705071a0417030f07030f060504051503070504060311040b1903030f17160c0804050418060c0804080d24080114090d02030406080a0608010501060c111c02 75
    0x4004100500000602c051a040d4074120f16010000c915041502d4031070100000440c04a2410300180300740004c020014030702f0340c0c10641501b40050702401c1840090b0242c0020307404268064541010040b40e0b50a000c140c0c102d50900710140c2d1891601c400401c030480d5032078000a003001800c141c8080c2c150400394040b030002c5100030310f00281003400e4010200c0d0340c44a034004900048880075400c8125810450122003411181c0c0b100702c05161441850412840e0501442e04000e841b0b4850428044104120b4010304400742c070078000240c219041840e60701506500b25245850030204580052050300e0587c0603513807141c0780901d00034801d03445c00044e00111300f40caa0704806030300c00c40c1d412090154201b001481c01da03002084501040007601d50000e002002002c1720303001100c15640d140d501108a074150385035420040101e45a100b5140c0091002d40c210342035039880d1800108100b40c00c000c100c02c0300c5200d0b4010168580000050200450310701170b500548181c00080c960062600c00b44890b00 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 649877643 1250 649876393 649876397
    0x50402210a0b030a0311010501061e230309010b09090109020a1806092a140d1512080c2e09020f1e012601150203070606031506090e0a030807 62
    0x200109030b000013401d081041000b2004241c000c030070109420b20a0268500600700e504129421513100b42003000030720200c40d2000c0c1082903020300040250f03550551042408211070300b0503128901005003074000c0000c0041c1c0c510600303070040000d011180502a0b03e0325030f81c3c050003821115203010341802e503c204242065201070780311034000c29992514800c11410180403501003c0c9000018040c00020b41d4800d448410041481c002c084c00c1c090a1017151402d00103160001800c2142000301040d0824680203101d0901d4031550b131000b8000e410001d84425100c1000b030319002c55148648004480d1b04034546040c01d11751404a80c000d8040b58842a021400540b070092880c0101c0c0000b000c0000b810080351885003010a55001943d2050150392907100300100054410790721982009456414442c54034181d42c00740c8070b80c064030300c24020341d80f500c0d500103000d004098492a015001340481c0c03105c0d00442c0e01d040c034000384611139405409820380c0c03a0006420000420344044035030324801464401 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 649878893 1250 649877643 649877651
    0xe12070206090a12060f110705060f0a090827010f0207050418020d050f010c020f0c1507080f0306090a02070803040f17130816060f0e03150a020a0306050402210a 71
    0x81c8011410141c44c155034401e010020301c031448441e414045070801c496556505101f80031100c00501c0018409401401c07807590024581c0d20704101030080c00495500809083c004581c84584c4075050b10000c008070300e035100740040e1414030001100c54042045041c40181d11480040100741056884002d00007040240f05011003a141c01140048100c00c9003182c480c0e001000c202d00c001d0081c03203001a410401e1010340805104001e1050351500803106040c8216000540f6207030210b4110122a0b80c50742c000507081d1500d80003110320b03140e900120340c154014910080001d90300c5015100321b0320300742c1d8444440c50079030701d590301e071240310290500302103404003c960740403a5081c400d48080c088050782034180d0507289003402909800d040b00d505095880881031182840144d070002200700701301c1040c0c40c20760407519000c0000b034540418580c650140d50b1800c4144605200300380c008029205480d1000e00845030341d0010700c400c0788146400c20310703003100480c00c400000c02424405500404a140c02203 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 649880143 1250 649878893 649878899
    0x1150603020a050f041202011713140a1a0906060d031403060a1e0801180f030f0c120c051921020f06010902030f150a26150603010e12070206090a 64
    0x9130260b40301d03800045002c03030030b10540403c640c1e11440c0a07202c00b103420b26261a60400a00a14940020000003041c00810325824400c0500030804804001d801c07000141e40c0042d102051210321609581001150207a240014a40c2c180000400003007603255807190400c2c00403d280968542028200582c052021000040d038a0549034110030940031040040c101c2c145001c400d03c0c2107840113690381d003034000e1400381c6a000c102041155000550581041c5216a24210041324024002c0800038001c0901da0324122806d41d0041820f42114410000c461700c0d107038a00701c80c02c83c2c107007460b500a0203d0107881100f240c0110000404000b03807068012920040d01c1280440c1c1007503000d811842c1d4003540171042000c5030100c442c038180c0208005102c803c0c0d101308500401c0e4289450f000d422600158074480201c08007286e0000203400c49610242d44030900300c801c80410003501a200d042c800e608164a5074060000411480c0850807a00011868000c244c0c0c24440c03181c0014640d50303441002d9503000 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 649881393 1250 649880143 649880167
    0x1707050f310608010f0b061602010c06110703080601031e0b030c031510051206010306090c080303100306050606090a0e09031312020406060507030c02012012070b010801150603020a05 80
    0x10700d9614500c0040401c4140c145402d0700c1c01c40d00e0500d010001e03581803403059850341c0c48000c204c407029440c0320b28849000c8407900060317400d000640001801646172002e029851440e079400307000541d20a030b88164203515001e0045040d43c03901e084091012803c200620b109540700c0c1d120512582018058542103207150380024280409500e031040340700303024000c003c440990200e210002c2c01c001c031048840e5040140c26550791341014000104080d603603045010a102507966404000e0841100302c9a8030714043e02d1001c1036000b1032004540321400c00c0b01044403803400d0000d50300010005030207074404619180291000c220050300450a901007003092402c0120501d200202404d115181c035000c09203184103010466855611210402505004a0700000d501c10300d8450141d030240303402c1252800320740c011303107074841581c0c14480f65110305011109000d40502c0a4108a80180c14200c00c6aa0b10b004040c00e882480405440416a030502070204c18000d50103000d54406c2d030f1034980e007003101480e40 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 649882643 1250 649881393 649881469
    0x80f10120503030603150103081b10060b090405071b020f040e06070c1202070303050f03071101020a0e0a0e0702190809041a04051e011503110409061707050f 69
    0x40e40c1e103030000020440345040400201c031620b2184140e0b28495032440e1a020740d03030700880d2030010b072456001c6c052030000c01c400c1008500b0401151801c002203079a600f0560300b241d10447c1c0860003141000300080380b1074000c0c1859002d5a0015051004141180d800c114203c2c4041f03d4181e4000c1c0c0c0c1d0940d80d0601d05e01003100d01d01c12030982e100e0100c8501a800c0a110740d01c2c00400d500119807100c0002d2001960040036917000c1152402e129440340c0303842000740d8410a02000c50300d041c0d840407805030100caa100310282002d80080e103011006503111485440314101c200c9800016a100c1c1a1001401e40890440b09615010b02e604505000360b250016041e40d2011001c115040d40e003042030480d5107001d200304c3e0f401c0040c01404441e04010f000054600c0c0405200700a022400d05100b04040c0d4081d410007040541d1400c12290742d540c40703103170940003406103006070303240c00c070b1248c0c01106500400185035040d00c5009100803c0858070030308120360752030780d9040f002960f1442000c507020300360301e40c003 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 649883893 1250 649882643 649882679
    0x2d0b060102071a0a030f09050c0315151507050a051c03290d06230f090a030509040f062d060503010306150b0d0e0d030b0607020909070b03100302090105060a080f10 72
    0x1911f4010260f4042518103c12f02003038200c1c90440d01d003800321015254034804c1000d0800e41d5464031b18031020001300554014010050500d00415503039004000002c501c1d001a03c01d000783c10580508011001c0381250411446a079030007030500c803007906100203031070300320051600106900440c10043c0d9445c01a5006042003010041d05c00703400081001003c4031840d4010080700c0000d00d07601e0400502740d6183c45851004c1c00b40800081c558000da2916003005404503600036040c00b40c03d90314480e040d0110390182d90f0350b10b04010310803002503601c4806100400c4442d0782e5505400d690035a00e0b4400100450100324900030300c0030500168100c00c038809003402032018080010444d602c1c0c5215410140207001090400d4500320035940d40c0d5440205031151507070143c0e1108a81c1e603911900d82e10340303032103600203a15100c0f020082104507025207110005032842500c21b0702c41c90340d9030360500c038240c0500106003010034a00400607000d804000c24540d03002d9810320364000070545d28648010011030000d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 649885143 1250 649883893 649883903
    0xf040b0c012703021002120402010804060f02070b0613020712030509030403020d1a0108060c04230904150606050a05030a0c02070506030a09140304120f2d0b060102071a0a030f09 78
    0x102d80d4280f503010301981c2140404903806620380384800f1940200a0310040009040c08024000326050018a034009442c4403034122003103540c0c0c0c40606081ca1080302c12211544101414403042c10340d00038900030382d0101c0d54000c001c02ba0311040c0050640c0a040d00403c000355911040c8000070240c0d89500d0455591405801324400070030030340704c0e04161150b0503040313100300781d10240c180003142c00c00200710740849009041852455019914101c03044c0348804440368891311000070f2206000c0860000f201c4460311040030402070b641c0e800151790500550a0f01c80218201303000140c00303240ea6411400d556005841034501242d111030008995410584122000d80c0d500c5000b6003c004d402004040f00c881c1040c015400d01c0e15022071003820744045c4500410315030444048800300b114440d1004054120000000940c6c0700108088540018040d82a1480304442e40440d130300e5400440d14000b5691003072804401e100041120301120340c080940102010f981303d2490b200c250181c0b161050641c030074 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 649886393 1250 649885143 649885211
    0x109030302220612020904020c120a021c02151305120309070f0503300406030506010909140c0a050906040b040504060807180f1410050909030f040b0c01 67
    0x140e041c030072500c440340062861485965010f0080c0350b00011840d85096007010007581c1e484602000ca0080d011b2a202d0482c40d20507200d007101d52505103400b41901c540503908484113800003018621100d041c07051004050307003100c2d681181623101c031442d0a5101444592424521b00d131035456905d8800c4a01d142210f080002c4103020b1200c030b0500647c0d00a180803016814164240030000b6100c5143d0700a9118124480f40404243c260502d1003001d200c03c410022030319190b40c5d420140180c0785c110780c040e0000b1940306020581096511800748000c2030031241d60f034959207a03081c07a81c8076440700d82801c0c10310a050100e8036581da0b40706c1c0104058501101c00680f144d2900050000341c3d2416001591645c0111100b40440f040802410000c2c4010b00e4000c10003085141103d0003e140e4100c115400b070300d42c041004020345900c047c1c40110751050701d44689550780d482c0301c15100c0c000d07048a0494008100300401c1120030000c094168500300000010f040c0c41140e8071404e445c002e4000300c407482094 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 649887643 1250 649886393 649886407
    0xc0d020105060a050a08120912160e06060418050402060409181b15141c0b12030a0c08030a06050613140d020a0b0a02010929010914040f0f050109030302 67
    0x5058080020401074172054a00c0c0c0c108090240c6403c45e101c02080c09501c041040402c5aa40e100c8802008602d9003d41d0054040d0f984040c4a44000d80903036543c4001600124020b820b10b00308a9080315401844404d400913403010b417201801d8041d02c207907403201382404007040c010b2644c03103240d5183d4075280d02d44800c00e0b0742e49081d80901009a840c2c000d1000c11070003c2006c3d014080c01100c0c41c010324500703c0d04000d10003411440500802043c03004000e8150a2051510015030001c4040f0004440c40c04a0340e015000c0182d40348a218151800101c8507503921001031082e44c0903641003400c0c000c0120f00f80e0b0301c403800700d05950000d55840d4415a05010f0800c4961070340304400414000541d00d00c40d1540303280d0049a8002c9180c4980a030b010f800040000b80e5a10030360044502c2c50380845004d21040b540e0105007008004241203107500760b100030000404420910034140c800d003640c04180081c3c0e8854030b814840b4008020103403a00b0160391140c000242007841001c0401c3d00c680c50060b01c07150 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 649888893 1250 649887643 649887649
    0x80d090308060301180201050d020d050a062102130908091f120515010804032d02012f070302120a1d010833040603060504120503041e0303020c0d02010506 68
    0x15018120742d019900d401ca0081080c00c85c1c0092218183c0c082c200f56680e540840020b400a1107441101c2d01e03854a0b1a05001d2003419507001941140d01e5410309417810b101d4455110300300021440c0080d4419611803100f10500296002100740c0c07402000c1e01c602300128600420b1200d0803c000d0b9560070210300d005001a690090041d010103800e00d40100403d207041039500e041f1060b02c0c880b850502c0341e43d40005040500c1458500440ea44849001c0320300303040007403035004001f002d5544201650070200a00807551000d0190382100b420a16803d07901032085444485030781c4903001c103900f10b00801e00180d10400d00f10008013500d030380c0303980e60115a004580741866040c2c11200442d04101052040c06541c8050601c2c030f0f19a80c1010010241c0c4448464184000c112540042a08182000c9000003886060b500591149010756841c080681d1616022140c40c0b10448000f42400101d40c0700307040005100e81c40b6900c0031702c40d0400510300310702000482d160800840328900107030344a0041000c141 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 649890143 1250 649888893 649888907
    0x14060909240106170103170f070609030903020a1a0f07050f0703150c030b012c03070603150e0903040308211602011109032109040507081503030f0909060d080d0903 72
    0x80c0710100b084e8255065944d080b81c100c10000c000056014041450383d07200e4900d808441e40c03164041000c104d60500c46c03030082c0842c03516201c2688079005440001031200200c0710b400002c5001080b50031305e401100c07612140c2070b40090005461a10803400c086030b0001c020880b070005103016030000c00580403182c0e02c60050740c4011558604150a00090001c9070360403a0300300e085101920110a07002c000701043d99884c2c076000d5145075240c403c66200099031034143e0301c003010300029040c2c0d8084007078441146160340507058482120315401008104041071302079001c2d180070b003450a48800d203002001380072419010b094441c80c0c107030b015100c1c0c42140e03140c0912402600303480c500001400c01200f000003c0c0c0f00c56161030b10011507034800b0603014061000c3d03000c0f201100d4000b0304c10890340c148000d00400944048030320081440d400702d030002c0d080c42c0000540c1c803080c000a00c11403400d140d040c02c1c03006002d0050036507a0880c031119041b000254518000d080c400041e00c80c001390134105400c0052440c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 649891393 1250 649890143 649890167
    0x1509050d0c050c1f032415020105150102070501050c010b061c201c0b03031603080f09070b16230d05090a03140a06020a020601051314060909240106 65
    0x8404c5125000c00c4400b4440c546559042e10781070000e61804000f0920908401c91a0301e0740840c0c1c8207240101c0c00c101001103110000b141d56008110642d180c41c02d000000241002c0b072405030b84940300802656100300010106881c3d80400818131700200008581640c002d00b4401040102041818080381020700c0741c020b0b0003021101c40d41814550032007402843c4101d4000112040c000701d0583e40a90721900442d15005000d012030350f403184804461003000807481400c50015000c000400c0707186480c1c00325140181c0c4000c0203050240c1c509486d0300945d07881640101c146408008801000c1240c00060b40351a40c0c03165041580d803000400154142490441c86070140501480101840d80341c4122241c1981d91184092030540034a0585030700e8095039060040c182400010850215079010405034101c413400c2d40d40c2104281c025000c40c2c16105902c840e901c0a0056600103500c41c9015004583c00c42d03050700565203101c0908003003801a8402001c044011040000104044c0354404003002e01 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 649892643 1250 649891393 649891399
    0x30909090c0d060b0d020306100e09030304120302070f140a0501150b071b031401060602011821120f022a0a080702040b060c0609010f05060307031509050d0c050c 71
    0x103181400c50000750481a441005440195602c030900e0140e11003003555401710381c008040303618528040840c1c0c0005442801200c4641d980807010400155001050303d00480e07110351109013020030440d08030000e40155109541c0081e03103030701d91804500c080c2d59001c108458080034001b0030100d4244542558142820854040340f1644104000c80b00c4806846101e07038005080ca01d0294000c4900d0060b40e0603802c040c100c0e144c84500e138180408158007080c115003194000b0b00904002d020480e44d20000e41d44080e04060300c8400030300d0185680041202140d0180c02c01c2140180768222410031504009036490b51603030f000036075410888841122050803095043d04030322143c4900d0045458000c0b59000a00380d1802041000441d92290007000b1034480103040c0c80e4a512071620706a40e160001e81e545400ba500e015541101982d032030149078030621010340105003413440c5a0340c1c140c82c040340c0501400e4440c0d0781d40c0c40c00b00251040c415a0040341e800d0355408201d25040c00e10908105171300c0040c40c4 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 649893893 1250 649892643 649892653
    0x10306050a1404150e010b0c07060f090b13030803070207030605100515160623150616020f0a0816060903030801050607060f090605150f03060604090804090c0203090909 74
    0x100071040900c0e0304081a8007aa4040361348030204055088a802d13940105c0d00704018000041602a000c102500001c0c240c1c0040300c030211745d0340703505540700105180028002640d41c035007031008254010042c8840c500d102446518550b50383c54a022641003078500b40c005810492003001840000d01030a6002241d142c10120f840d840c0c80c0c001000c02c2250403e200c01c4110225000f0b202d1000402000d0445801032000d010385c40308000c86801282402205845500807003010035446414142240740c0c04101a0503d403506c900c46014001002c000030080345c2c4400340618000c0780f42c54019502004014800040c1200002040c440c3c1c0511403030380001e02004849002040401e503c0400d02c0d0440d24203941c140d80c0d504c400c0c108100900780c0c9604000c143c500b8101e5a4082102e958441da1042c8403a000c528040b1185904100c0b06900241c074a540c140d201101281080c034156016041661162071601c0c0f405075110808429a80d0458000c00960004907100700c00d0300349020703101d600141200243c4 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 649895143 1250 649893893 649893899
    0x501081b06030601030921080124020a0b09210c060105270c12070905120c0d060b040e07060201020a02060a02040e1501050c1207111002061f0506030106050702010306050a 75
    0xa815000007010743c0e040646803c0104180310f00e50b41e07220710281c6c645030003940f5000d40c010044c1c8240e1080c1725a00340310f40c11444040d10860b914000014498850f4042c0a16501d15100d1048109004d482c042c510700850000c0915905403410403807080707000000103a160300040d11158140030050748110b00444400406080c100b030051011003422580c1108405581c403510300900c024050107440e003280100030070034801429085264541103880031541d09018400d0f5115403521202c50400030303904000b43c52423410001d03100ba04a0a80c4487c040d000103100c480c0503070b200e45030801c140d1000c40542d40c00201514600c1e4180000d96014004d01d205610341881c0c0404048401d500419030042e610900d51507a445038400c0b0100c50340230304800110b0382e581da4441c000c00c3c6680e1012004440e02c161603807090446040421100c2480c0c44a50003030141c80c0c2d02d109400d0201c80c0400310b100e42841001502107400d81d10000070790301804030313992226195440ea00c000b404481154000c24801d0031f24280c10 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 649896393 1250 649895143 649895149
    0x30902040e072702041505030f01080f030703030b13020412110418020d030e1017090706020601060c0305070b150f0406030c06050c03040f03111906020604030c05031c0501081b 77
    0x3051102e0843c1e84075102d90702400c07003c2c2c000e0259800203500010140e41046110b42c4c443d026500508c011244141507076a00c0e000c0c1d42d40d81c8000b000c5e41749282c000b40088000b203402a8040e02140f84040d102c4202c1500c210042002c903070180d08904020404c4c03038280c10500440400c1d42581c4c0c00b0a8900704042110750107007400c20008007070001e00c03501041c050201014840c0b2110012144080c180c00c11002ca04140a000307001c410303240421161410340001c41b41507001030440308070383c00ca401a01059082c1042116541d05502040e002c3c04070402941001405a5888501c500e20740e40d400046603001c1001c00032640780c240c8a09201d5818074a042c0045500b100c0b0910486019040a6a407191705540a03415401194000300302e200b6401800828001c110031021310040d011100c2101030340174a002101c0b17101c014003d10005038024400a00000e0043c00c99411150099003100e08009500e810300c01e803008801d4000340400c0d10b40004100340c0004200c603400182e54010070300e0a00203c1c07008 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 649897643 1250 649896393 649896419
    0xa030e04091b08032d040302010323040b072d0e0a050a0306091205040e01120f051c0f02030403021c0618050114010e090a2006040303030902040e07 65
    0x45104954a07081c0c0c5041140022141d07403507051860062003002c1c1da410540b41c51303070090800030200200b00c507858015940703a40c110346030300c5600700151420681150011401000d180030040014051508403900407840d004242d44164032818503a00d05291079100280590004110f10102210f6168900c404403100507629010385243e01d170012103019030100103107d040d8035902c4a80c000040d06c03408420b1103c990031101c42030303001f00c008a2400841400c00c840e24400c9100343d100707d56403c0c0040c8110503d15041d1101a401036100064800154a4040c109407500c004903940c44482048840003a4201c1035070f0170a0f116500146041514540104902c20305900140c5000a0743c80d03959010401c0b6640100822842c205c08180003000b2860420700800b801c034515507502546000000381404499150b500c90102d0001030400b030b940c250b6842030101c6421154910400750342407a004292030300707806000114082d640c041130030002c90041c0407c0351035005072414290024441484030502c03045d4 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 649898893 1250 649897643 649897667
    0x2030a030b011e0215010e0c0703030b03010f0204060806101d040b03100606081e070c0201032a09030311060606030c0a0203040b0403240504050c041d06090706110a03 73
    0x2000309007001018012100314070280380740b0210304010501d40320450b03800607003120703c400c00c0b580d0440183d880b14400c4151403000c40d01c01202e60020003500001074440e13003118100404c003800115102c00e007041d0320811307a00b00d80c11600006802004001030ba01d000d000c480c074810740074100018440d0f14010020300a10078068001d0203641c0742c4201200c40d8408000500840f001950200495038035554018515841554090b499030b556689540c1c400810b0660342d805440c0544800409842650064010f003e14032070688150310074032211b0b051241590312008a501c9039a031071001c514154030780648615941c013203030b006640c0004104019601c405041700e800c0a94a180f154690300200c0b8202d146201c0d0340c001c81022000414000100b2442c5c2c240d03007a000e011200341a001d02c9103610003000b114030856002c3c1440e4003070580c0304050304140e401070304034802680620f0090100c2c40056031401038290340070b60896001c400104900e17507101128003600903000000c2c105125441d103008000e460594 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 649900143 1250 649898893 649898897
    0x50703140115090306051f06140306041e090c1a0c0c01140409021c0b090601020a140a060203090f010e0f061f1502070e061804140a0213020703030b0f0102030a 70
    0x100c0b80c98441e000302e2050009542c8140180170502d48480014100044400c04c1c0d100303642c40030408a0040d0055241c020080b03030343c0c12007a0541e42c0d1401044050f00404440348541d094190702c0c0c03242d2007824001e07041818000c040300c4030340c1464041411031003503502c0d0b03940b8801078061003000031f075000101d0115034140c0e007443c2c0041142d404200a0715140b0440d48607910b13651001581c040d84400209501c88440000c0d1402c00c8092081400c1c85003080c400c48180f40143c0221047d0030019192001960b450b80f034400480c3c42032201d60b610b89080b42c0c02500c420b40c140d4007000110100c00c00902803141c4c88400580981001000741c03c415a4a00c0064840003104905a00540081a00b004110000c209404188200100e00c10700a925440d0600132003515021510000f02c05040a060801d0b11404c041242c1c41d8555071900d40345407411106103a0031540c001c0540000241c1d0314900e405c7d4400c180c00e14010307a280c04a01c0e000d001c9410b071801c01800340101050800880c2e03004020754400d00918 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 649901393 1250 649900143 649900169
    0xb01260610110610030201140a080f09031309361e0c0605030f0109050903090409061404150524040e0c0a060f030e12041701090206040b03040201030507031401 70
    0x6160aa4400384010b01c0c1d407189100d450200318a884140c600c04040300d00030380b82d4101c2c00d45e800344501c286101d07000003000415004000309162000d00c020040d0b0228141058034248684014182030540d1154401c610141e2601e0000c11080021342903006a01c1500050780e0210b2980842105071015244000d80f240f2080304002240545900c040c00354a07502014a079925601d0b81d0300508150019a413400d140755070000041806070061103001e00503902403000b03500f41982841000007424425600301c4800741c83e800004842d0510104090090388118000e045400043c000002192001401c51000320200006401079420300c2e400d6108411080e20701164000310300940302d1818036128031480c0c020745c06d80030000c1c0c680d138082120100300980e664184003035800c0c101c409580c0c102d80b2050a1144104000421061805401410b8001948800440c2d0b802080c2c0004a290304243d000e0240b0110010401003190b9142c0700e00380e4410201c0c141040301603e461012000fa2505000311100e41040c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 649902643 1250 649901393 649901419
    0x607050a12090b07150c09060813050109051b0111240901090b0109020c0f0703081204031209150608160b0a030b06031801201c02070f060b012606 64
    0x108042c0180640403010b44182d641103545001350701c6002c540d00414410313103809074240110384201004421549140c1d1540d0481c0c8450381208410304107144106c2d555940c490018002030803e0000140080003c04195640c503500000900040320704403003e02a90041034500038070108545ca1031240c00382900d182102c0307542d50b04100d401008005000ba00060502c400010413111329001013038841000d1003591030002c1303e149620395030541030000034038070042031100310302c842180b410143c1d02c90701030310300405035504080400c011210030b60415640c40e094428082082c0e0150301030840140304060061440c0c807903107080c01c01c50003100d0140707040046000881800c1c1d079119422000c0c42c070400070043d84c2e5070704107882211074068514200003299400c2c160303561900130070750130381803004032007014154500940c86000304080750704145d4400c8803d40c00e100c0200441d40f14005021901d105200018200ca22031001500c07005000030050b4041e882036a00782c1041704901a600d41101003600d6440c0c1740c0315 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 649903893 1250 649902643 649902647
    0x120e01030921030b040c0206160c0f050322050f0118051c05100b060a0302030703200d050f060a030201030f02280306060e1e0109050306190501050607050a12 69
    0xa1181d0010b0081c0404814501c50011084001d029800d400d8500304085409841800207681c80000e03100b003d0380040c0700245200034a0710034020808494948402d100800e55500014884401c2c0261410750020480b441c40707203040020012002502c89010004038039000001c0d80c1c0c41d001204190400c440071078900022000609014044c02008102d95500d10b82c00d86045654080c43c9030036119403050000301c0c4840d4580f4429a2542c020207801c0c0e84c900444a00181c0107580b0207841c03141059a24186010790100d02610140c0d0034803009241c55403140f00d04002c1044d18409800d075200c81c400030b4180020340d51400448400c82e5420f08000c54003400c10351321030009000c0c003210005950342500346880c41000f00701901044011584003001000d40340c0500301c40003400008102e4000c0b80c840f000381c094940b0442c071402140c80c140340102c80c90303444102180c10110705480b110171044850442101c00c072014003d00f800345c0400d992043c280310280d16495030b10724001c0750180c05d0040803039581000302c0c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 649905143 1250 649903893 649903901
    0x10506092b020102071e052b030e01080a0b090a1509020301030c0e0703020a17060409050d05090f09060d03050f22140d050a14010b040608060105031603120e0103 71
    0x81c440001540800012241100c61007145036080b40103010f440030106208a28010210a07100c103031200400e021b040806000b20301c211041d48040b80ca803580c0c50303044840d00c0c280240350054440e5842d6400c50041034000350211401409203058542065000921511980c402c2944030094110126824203444030103500c030034042e00100310f0140000004414403c80e5564134007101c407140380c880019917039090120120b00469401e100080c071007030218400300505220403900500000d00000c0d510460341d4400d071034268182c91580100340003159208242c5082c0410300b1500c2070035540303805c041c50403c0c00070b081000689001818040c0104074081101c3e00c0d541900c0000e15250704c0860045040442d02e00789007114840c0e000501602120800ea45c20010041150554400c0040c803540c0207507941c0150100380e02c0351201c090741d40d80b0014451503546001c1c00000309001c90141806d9410301051505040840000c00c0c180702c56003008100081d45903c08040004540c50b001e400f003415035004902074 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 649906393 1250 649905143 649905169
    0x15090a2f0d08120711070504091e030309060b100c080a0c1a040b0105040209061c0f021630030915090302030a020714010e0f060f040b0d180b01050609 66
    0x403080041d901420003980200800e44101c03a80141c40d040d60b60084101d4032507100c1c90842060f070700510350401003800c0540240341300521030211202a02d0b00d80d14000b41b4071003403840503400030307444a250000b071089a11802014103010b469421400c1e000801c05400d1400445004192800015041032918130450510500d1580520350801c0c4101456402214401c240c1e000d440c00420800002140c0c1303402d10846003614005090141858440120442104031092004800d41c1c3c84083c4e284c40741600e80b0040c090058005a00b62484032503040030440c49011001c069040d44c1c10b45401c0e13040c215101000d040380c43d411b10b400320342a0018a0f00704130b112995140ea0300c81b181004807010415030040064244000c881e801c5030781190380e62620703400d00000403040c60f010904418081155051a8030f2851808202420041c54601040e000d007500c0e600560000034031b8400455900c0c01d10081e4002c0410142c0e505100c4200d130183d90b207803110020410f100e810f01c503501c001034540c10340d260440e0060f20703 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 649907643 1250 649906393 649906399
    0xc1905090a150203040605130b0f030f0702061509150909100e070302010503060d060f02030708011721250803060120030a080406090212010614010504140d020111030c15090a2f 77
    0xb02c550600c2b1481198105070360362203054000c0000600c12510014400d071141c00d04112000c0340807000400c0c02070801014005180c130b4169030304024260b8a0344002240140114030041852000075980c040446d0f14454504819400810040000d81c2c1d20005998106000b00c420a00700c13401c0e8546100101030703610f0b0788611640007004101c0d1140e000200300b412100b1302c541c64503158800015960325004030f0160644038450000341e03007290b440320b4000b510100403c083e2541c0748404035078030007110b50b032000021504e035000002040b1403540d018810100c0001a602d00300d001c0540b454149443c1c3c020103600204020a8000180034000c41c2e070007660b03c0701d0300504001807804400325840d003c1c107d280079490314412200104902035209101700e40840c1c0100d940c0d0391f10703082581c04204c0016540306040c0d041040000524001c1c42040c001490820390034001481081c201d8240544001c100400c40612900050034050204105480b039008010840d803d4403040c41001280700aa080c100301c0c1c2c43d070 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 649908893 1250 649907643 649907647
    0x90a0b130501050c280c14090403030b03010e2506020307030507021507020909010603230a06090812071806030e0a0204051f0602010b03060a051e0c1905090a150203040605130b 77
    0x2441240003132210b03410b01d00030350704000b0158903030310b06000a10b42807c441c0d41001c05540080c011910039808402c1540c03000b0008142c020510f20708910f400d601e800c100803032541008500c281c0c0000401d01b980100b180e80003560130103109443c050003a004240b40a8000c19501121028090020003100c840c59070041c03400c90241003140f400782c020100c50104942c68012200080e41341080c005daa02074518680c001040070608990303480300035000c812b104031510503060008665001901c0d40092081d10641c2d1020071410a0049901c0c0e0707000a0303444002407524124003d4811103000c541c5441c1e1540548ac0890103031100369002540040d0654005900001070201040c0254190040985020100c0444c4d010b03032201e40e03a0004840050780d28a04403907260040c00c495552041580e5401041910720906115002840f45101203566140c00009440024041940c1c03070640c0000700a02041005100020b00d41e8034041e60342e1090b802140284280031400065545200704254003401035006116 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 649910143 1250 649908893 649908943
    0x3020c0c2106010515180628080c0310060f2003070506010911070308070c021c02010f0f080c090402041806061407050318010203160305090a0b130501050c 68
    0x10703a2100307007400d502081e00503900000703120300e08050074114140a0b0011940392024507800c0c0817803413a0040c201c940004082c8406607a0744200342c1c0c2c428540742c480300052204600c0850003041400b0080191901d04000d00c18072000a00302004c00301a0b4080c2d00b400b500c00104031200361203983c0da0000051010046034031007110020040f01074a8201c0c810000c03250307180d0303c59a07030000380c98469014440850050148002003072040c00003a41051007400c28101009503a0040350078000314104111200e42d051090008559101841c0c02c3c20450920708802450b4086100505000700a8400c08100a010903a0340055907641e0448005011041a040d24003031280c5501016110a2107502e010400b070801c040714040e03030041100c1489500c034014600d400c0c038408a0440042c60061801d04500c01407103c0c0c510782190303030401c0901c14025290603440e1b1400300c04000e1141410780002005090074850903952101c0d09080f1026200242030268491401a86880c43c0c00c0c2415030006018844175440 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 649911393 1250 649910143 649910179
    0x30f0903011428021e13030f05012a0806210307060e010c1106060d030c0b072a0308011203030921180b0706091106072307080d03020c0c 60
    0x20754091540d40c910f8100302d08501c2c04000b2405803681d07030044911440c4600749a0243c0c9801407903454112a881c5c1c403a5074807511904914009171707408480356952440491150022420342580c20034100110740c0400600c00c000804007000901a2406020034010410024212199210072640c0304000c46c0e80702c00c00750401c480901041c4030720703191551a002440b540d591044485032100381d1086c005041c65250113040c440d515450040c160104500d0b0000080019603995410340a4075207551020f0070140a9440c0e404850300d2100e045050080c80f104040000b80c1004455045130702c0e20b50132000c844c04a040550161045d600000c0c503d0000a41c42d00007241e502d4440c04050840d984c52100c2c401c442c0c6d403041d01041043c00f841402800602011002541c4c3e5000303200218428040510880381c0c2002044031034000403021204801e540051004401c1200042401c80014074001c04406240424164960039004074650816400240c403804503101040b0b881013014000d800d03501580e04038020 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 649912643 1250 649911393 649911421
    0x50912030913021b03090a060f0516030806040501050a12060504080f0a08010614040f090509070f0b0703081b160503070c0303120507021b0f0114030f0907060c05030f09030114 77
    0x246556013040104980180c83c0c000103440440fa4040d14054031142401d200740c44d4500203000309001c2040401c50304040107080310f4400b6900784030313485400c3c07a418131030204400d5880507040140112400c01c0100400e01c1065180300060707402c81000941610756090003010751080d101c8400103448002030084415500001d918100c0b20203076184440141e411885549610840c4038102000d0f040040a000d031b00c4240e4403880d04400d0300c02c100c48201c5d6480d40e80401a200d60361140c840381c800860f820040c144c004038295844034641c010104204d10b2150001003d010b4240100c1c1c010000004100c1044420022210001d420030303002c04126640f460010114804048440078031803c050114020034000a4030807105d103843e4406202c1134030500107000149510308800d40c108066500902d0140d03002600075400350107002c203000010300d40204481c1ca4206140d1000c0c0402c0a0b5082007004164080292130b41c080940424540d03e41d8500c00007805004c032924440000b02481c401c1c0158030001e001 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 649913893 1250 649912643 649912657
    0x4050d032702210c0a08010209100e03030913020315061201060c02060c01050f071b110603090312160f2604020a0302130e0607020c0a030803040302030408330705091203091302 77
    0x200145c403d6100d035405400e0f405070220487d008403502c041a0200d5004e01e06246a58001400300c0342400a090b0014180e0041c0c90703104806c0550000c00d000d80810b50031814140c2107401c2e90200e19142000d8230f4259810414880c0300200000c14145034115940c090482d20400c04201c000c5c0410705021140c4c03940e1100990396000070480c1643e414014940c0040c51a4055400480a42000a20000380851580b00414101c41800200146040c200c840b42d40079004426141d80c1146807a41c511014194200e0040d03148140700240e80000c003404945842a051130494050302c804a880d6880400d00910b880d03003000758000001c10290b2000c980a03400b100e4400700b50811180389485015007642ca990f00764241c01d4108190001c2403010076144001580c1140c0b084c0304903842c003551101010f043c0038080101140b2041c40c84904009c0001603a00003d480e50080891507150402d01800380c500c2c0b040c403945500a40e60b1714044080c020b028000e44001900c0a8011901ca0160120b940001e50241c0c0d = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 649915143 1250 649913893 649913899
    0xf03250c0b0a08100b0d1d01020a090510110601120203100207030201240b120627040614070804020f010c023001060617041b0e04050d032702210c 64
    0x243c00601d0702c4140340096411a903000b0309092800740108032840c0030b00218501622406040710810030f40303103801d01c001c000041e03041c0c0d584a40e0b207041200f044044000b0b80351017410080303148008819000003007016411101c0007004110b6032400c61003c02e00b0502c600d043c00c14214070108691082c503806400250342c8001501a20340c100000c1da0703100702d402805000340119400e0910141e2840030710040829008207004210240b8000700b507101c482446140d002d40d1440003d02d04c02d100400165000b40c003605040c1c0380003092146820903008010000080c00a07100b80e1720003480c3da40301d9000e888041d040f1034015110480d50806601e40308000e003900c0d240c45110f1041504c07200b2138800d040c0f080758150740c61541c42035540c030b0301113440070001c0d0406001582d240b1083d8a080c03400e90700e401d840000a0650024003505860a41082801c01e81000d4401c4141800c1040c2c11000d4504070f1a101c880903884841e56001002078004141901d80c84000701c20004a8031101c1d40b02000c00081d5000344000031 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 649916393 1250 649915143 649915157
    0x13021306090b0d050d050f040506030c0c1b090402060a05130e06180402090628120213050f0c0a050405030a060902040e0d0927021c0b01020f03250c0b0a 67
    0x6003060020810088401520540014485450701446980186803c84030b403401f0070300705622100011620b130700542d5040103000c00001d420007141c1080c096054505003100c2e5a08090051030041407000c0c1c00280001d1041d40300041c003600c40c030f00400544070310403206814000d9035600c8031200b07880c6190555400d88235a07100400800014011802c56210301c1d80039011800d261070701410310042c0401d02c4c40ca4400050912010040c04082002c0c42005100000c03402c6044185c50052001d0040c1e82c010300c603200381c01c003030411107113280c5041040d130000003e002c01956003904550894107030107240c12059043c02248907404c1800220f40003100014000c0350200100c1280640743e0395155040300d841c1c80459408502084510703c0c80f00c20301900b01c01c01080c00a5400381030b9584081340c0c40064808620301c0300001504608186100342a5400001c3c0000c040c80324440045655a00601084140c984058886410b00b0f0060080b80b001c0581d2140d00c10341807a8690380b555409421050f41e030000a148 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 649917643 1250 649916393 649916411
    0x130308061e040b0a0b0d05240d02011404091d070f061b050c04092004051b091c030203040e1609090515060309070303030b0d030203030f1302130609 65
    0x407071001d1008582100c1c0000441c1c40324000d100103009108043da0340403110900002d10000000014010740c00079810000d4285000c4449a401030019002c1c10f9480c0e88036022012261940c1004002080d02400c1c00340c86c0812411807504030744290740244e00071a09002100402c404035201100e417400d001816203a03a00d45410711001c203a00c0030300c078050000f8500e4040e800c0d00c0f502a44c905500e035004509071045540e540010405503907280d1411100300c507002e2000d6005076007a0b80b10490410080314144000c0c2400f410803901c0410141039190780c00d00c0045e20000c5640c0300c071031501480c00400100d6110314001c1c18040d4980d0442e12070202c98203004400a103994842800b001da030342c141911901c241605044000c002440c2c001d0141c600e552401c108101c5030f6550501031442a1201c2000b030030005c1c251318000b0117541a990516020301c25107840900002c0d004410389500c201c600d444a085540c88054a55660342c0c40d410186d00400420000d40e40c08140707803c04425240440f00034811440 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 649918893 1250 649917643 649917649
    0x8030a060b2b0b0d03050d0908030f150f0303030105010e2704051903050d05040516090c030609021201030210140d050703111e220e0114120d050a050c030313030806 72
    0x1c103d01643e44980f0381e2442100083c041ca010b4145054400f0380003e00340c8107030781da00150f80d20030f50b540c1302c584072082d00308054415600caa100d90294103540707c03a1442126004aa81ea00060240078184102a500c44503607448115241d24641111103159a02a070002c1140c0013118040da4103495030701990b0960a007500301513a40c5a111031f49641c405161441c180b025500419010300100d445020700315080381001c0e200003002c400b505031360200250340c2c074052501a04603915039000d010340a00501c80f41030540c21307182e0102e0440e901079840c0038900d010b20300211440f40d0307039403110914030802003800c83c0c800c0c802ea48021310030903da88081000d9203420040320400d004501c41015040a14101e0810051050303000c0c0a40510300e0060074042e6030500c1014121030301c1c0e038104a11030340d1200d0041140b80450500030300b20001c1521140000d044444845494982d40d550f488240040050300f40a840d101e9400c940700c1c0c50404045d03985a041051981d4441030111000340c0003d51103c020400c146 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 649920143 1250 649918893 649918901
    0x1d100c2601030f080d051807150210090503040b030a0501150503040f030c170705011a04050402010c030e0114190206070311090f0609270709050d08030a060b2b 70
    0x15200c0c0340350401680c0382d039468202c0318a0041088074190028852070389800440e0017960700407041c0c012800c00e2504ea640c81c2c41c0c5444015800302011840c40d04a100406030086092505146001008075204d5104c3c14000d20303521a80d84512201d200000030410040444d5020505a81245031402130f5102070b076204a84501003035502401400074a15030740700103800303040560b07442031207107046400180e044d410383c04007030b0004002502c169444416031040301e0300884000e62281e504940c01c005030708050300001c1450b03c01a40003028030030805400050350b8041ca00e0300480207400d600341d582e0382d0071240e070311b240000181d030440c80980b02d0100400e0515002c1d02801c01341d007402102803400c000d4010104190003540c40401c0e50060360810000d034054503154101d10303c100500d050004400f00d07d04206006032401040300040099010062020303990b050b445014090b04a04003d07241d40350046113500a01d9560303c040315010001801c001406864801c5180c2440041c0c10310071156003c1d58103105071 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 649921393 1250 649920143 649920197
    0x110d020d0f110708010204080c0f0406030302030306090a18060207061407051804060801050901200705060a0506061c060f05090405030904051305070602160503030a080a1d100c 77
    0x840c00361001c41d50207038414503000d0000b04507071080300d11280c0d0b64440d40382203a00c1904410792a800c40f6580c00030f1400c009025031404c110950f0200725641c03031a140251603000192626100303006100219290b51003a0304040d070310404444400c08120100c0c68904002d50002c8401c564050074030180d5421251841c455a00c140c4407515000c0c5085030380d40c4c030010180228007000c0c0d48141d440b4008075401c0824441c0034800c800380c01c00011b04c1314134040740c030b1281802141902d19014042001c0d50000d2004078181e030f042a00c400c008513154558000290a80c028031825a0750021040503400f6583c1003a0403404c02c88100802030300c9001d48442c06d000510030101c4018103540d20400402c2500d042a44c0015480584d90760102c0b001d1041d0340e01c4900301602d9610000069001d00221441007074090020b00c0104030440003107241602488024040b140020080c400840d07a40040c1005c040c140390241c0d01101183e07056810340302c00a00d11400070552440448002001c5208084520298048440c40c07 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 649922643 1250 649921393 649921397
    0xb0702031c1802040209190308040e01080f0a110a15020d08070201200304020d02150306090f0403080a0504030509040609061806050105041806270c0e010c111f110d020d 74
    0x40641d0b650203120180d8440e030701a6820201035003514002c0d65018906e80082c521489480b660b0798038000e503100701c1c030506070042c00c410f8108000580f4000c0c00005c0c1020800d41c403564040d04958035a000070000105035201007141d000c4d465445010320360120307079400680080d0301c803c003494640080c00c81c22034515040c0700f0260440808014802451035014590141c4000c2011041c80c070980c3c04035200c040140c1841c540c8010110512880d0320348100403a80c850300d40262100d00d898240c0b4004c101082c0030707284000c80e9503560046000d06204508a07100c4480282003488016a81d400100080680b403041140c42d04404c421490600d27002d0042d01c0842c0d00503134850b400d050400d10180401c4e254003904126455541c80b0000d45519284904c0101030300c580e0b106581c10141c8105c160580d0710402c2110300300a8a0034140ba80c40ea0068245d082c03141c0c10103080c0901240c01c2020411009803032894070b5095841e90075018400c1c0d8010041141265900155603000b040c540059a807181d45046d0b41300 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 649923893 1250 649922643 649922681
    0x120a0501060c08031f03030f23040b07060e0318120f03122e06080622020d150806040507121e0318030302030a0e1206070503040c030b0702031c 63
    0x1c046401000610b4121541002141015010100514020017241d1080380403842e03d1030042d91a98000c00b0214204250b003518950803214084805524480ca0096201200002c00c141080c085c45600c4800c8072440d0f081204e9441d445280c081c0c4000e0300303102400e813298018011840070050085805a00851200020350400d903c0c2c1001c02e034204401880c01700c2c540d640415024545140c0c0c018458400e20110041205900300880102441001440c0a0060305055559113044201d016002200c040300c2e100140c50315400c14040003d0300302e0000020100700b0013200490300c041c01044460180703109404803000700360b03140e80381340410001140c00352080101d42c1003020f160b5080c50541d25468803d190003100c40c081504082d200c035515800c00c4c0c1c01644041184640d02d40c02000c9440b24010440741484516919080d0964910300240001d04201c0080089820896400c030102c014552000c0d46059070720f88140e0080d561f4001d00b1031400c01c44c038190903a003e441524418201c4441ea500c400007 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 649925143 1250 649923893 649923917
    0x1517010b0618042d05040309060206040c05091504060b03060306090a0f0219050603090c13060311040903140a050a1b020f0904140d0305060f090906011403010902040c0203120a050106 80
    0x41210300c0210105180e6007075403001d00c400341c0000302c0a1320098000001c0b03c0c241400d008104440a030400c10030365000601b4840450300034008078044640494407054940c5e00d006008a40e4018858170780d42150501c800401e0054004010314440c140540403264660740b64000146e84074407090700544292900030b00c940150130262410320a1840c0f044060010070313512700c04680160710450b41c2119a40080540c0724951074024104040448006000d0004a0540c0c0f00c2400007044140b54511a40e0740303508800c10140107101d11400400b8101d910340c0c031448400009403c65002d58190000601e620040c8042c0081c4031280c0f41903140c0141441c00100354520a0000c400e40181080e25845100a4242c02008040010b52a40c80c510b0780d01140e81e041041c24419801416602c1c6c41c41503282104002581c032002038514110341090384050000728102020900601c1d003004042d4015003045240203140390000300404002550038100d02c2103a07902c0c000c00040350000c3c050840003600095400c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 649926393 1250 649925143 649925149
    0x405010b0304170714010209101112030613180302010609140103110d0b070905120d1e14030703020414090f010605090406080604050c10170610031517010b0618 70
    0x1103d00c0320604800391074030a46480d485120b030b0900c3e8403407010369000030303210680d810442040031000c8200e00b00034200750005003100da101d905c07000c580004404044001190f5503a003110342584413002043c01c009038101011203502c0e00d00782c580e06030f000d0360810f00c00052240c024420740142d504c1203003081740641d00307580d01d950310403500400d404c0d40070010510000205001c00e40d990f0042036985c841c00c00c001d10708014000c0307100300a80a0380c1d09401101007200e4050704403c8a08521002601c5d40c5440c1c100d842d801d4031154030b075050984400c48048204031040390103034000c109440c0b00c00342c58160b00c0c03142c1c010800c2ea9482140c0800451861100402c0501d0080c0090701e00b110004101090341a1a0011240f806400b11010b44241d80424a2600d0900382400d8003204c003107803882d0100374003040760302c19400c100000d0007080c0a02c0da40c0d142d515420744280d10010600f9540101d8024242c0e640c2d110185e10400495581c0c1306520b0090018503e280606c101e0f00b803040c8a81d16001c543c0d043e4010 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 649927643 1250 649926393 649926413
    0x30412020d02220e0708010203090d2307051005130309031509080d091a1006180b0a0207030c05060c100209180c030702010609180f05010f0e07090b0405010b0304 71
    0x80f82c00800c52010107100006540c80030020b1444008000354036000103100519200311607026410591040003401910780000c079680d0309400740d0f07043c05240103e0410603641c080c1c80b07581241401c02c41c00320381d0008221000c226000c0000c1c40010038451178850030031810f00400d2104009000c141101000c000040490200d0022411002030000b0b07090b400e07482c1d01e40c40b03900c500008681340780c0c0d50303604030b04006018055280b4070750b5541000130586011040070041e10b049000748010700900f5615042540c0e99440c1210251410f0402a81c07664007040010799540c8090208071002c071203014000c41d640c140700c2c01b520300c4c21010000030080582c040305400002e5021000158200c60500b01e03002d80b6260ba007668900880070a580c0f9a540e180c0804000d00f1655a5003201c4903040c1800070b00c1000140d81c48562850320b4101071051400100c5141c0640140784000900540504221016882c103d000c10740c0310403543c080c0818800d4003054030400c412502c090182d030020080a0011034081540161 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 649928893 1250 649927643 649927669
    0x1b060f1d040b03151b090a09020d09060608011b03110405040e010b19031e0201050a0318020a15090e060d142103090d0207031e02040b06070c0f060203041202 69
    0x120018482c884032021074207044880d0b60b00340418140009000308081c00364924100c403c001c10120781080403000000d00464040d115148500384c020030020800782d04c40d03102e00d54a41d80318404010f070603911031140d406400e20703081c0403800c0105105103082d40da02030b024030b103484035010001d10700e414240410000100342800c0702c04025944ea07000002036440e107076000300700c1c00d00208038200e415240d8508886112002049028021502c54009005036046000d490f4000c04030b090205000c40340350303454421705021060181d03014507400c40000f40c2e240050500d0000d40d03c281c1d00e050806841b44103a0101c0f4206954840d01300150368941d4001c40c0d9080104030800c945d8406889a01d03c1004076240d02d556020107400c4034007000030900150304c01c10055403542d9106e900180c15005c1c6581c0303070041018500e1a0744804221311a05000855813150700c09016044018910f5480300301508005030030f03d2450095410b25602d041010640c14000002e842c111042c00c000c09a00f00569401d10000300301820b = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 649930143 1250 649928893 649928899
    0x108240d0507030c0b1905040308070b072105060102190f020d05070b0408010510060f09050f04020403060203010e04051e0303010501050a030204080105181207080301051c0b041b060f1d 81
    0x82d00030000070110480c2500034000c4962031629180040122454030008030f07100d03c02d10000f0001000020f480500351890250020000c100390755901505482483e00304800c07902c41c261180e50030b03440101560245014403403c0e8200c601d011240e40010700b0b4a11008009011074040d5407190006142c6003003c084514400c030192103000350303101e4202c0c01c15001600808281d9444904020307054103042c101900915840c507103050700c010704000c0600014200d00445009621641a070011034440d81c04031001981d005c102150b5942c2c2d1050380e4640c850007914221814000c1506006c59410700500102140c1c103181d020714074692910006407000d41c05500704106060f028400056000000c0c0724a910405038108101c95030a024100c550030440481da41c03810401085c00344c0710208031200e05580c1511001d55008051000381104000440b00c0410b004110200c00e00420040001d9420405007241c00d145003090203540302c1c2d8041c0e41500f682d020290000704203090054801c0d00d02008624194006 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 649931393 1250 649930143 649930153
    0xb13140f060c0109020102210a11010b0d0302070f29130e0114040e0d050405010c0c030605190c08010506072303210c130339050108240d05 61
    0x420003151090b0442509000306954646480301035580500ca013280c44004002154043c0008620407400d600603010380c0340070841080408802d0603c03d40c4401300041d40181050660b1803249002075450046006032807010031155000a40c14034491404020080169480c050b4041c80074140c10302504000317101850411080380010b00c00920303064150107001d200507400a20341038001407005440c2d11280d85049036100100020030283d11100b42e0301a9402464481003521241c00c02241d8846117400241c4114908410700101400121040450309104041407103280100ca02c2502c00d10024801e0503042041041440e001404100d5402c0e42208000c4040791030005180304c80349144c100d01000700030707040c100c100c408541c4901c221072503201160b21400c51410b280389082c1300c0d042c001d6100080038148419560304021407040010b10b1250310700c2141562050144090071089100c91141501061218000c91409202c0c10860310b807695902b044003042821003418007140c80c60300716041e2003500827 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 649932643 1250 649931393 649931419
    0x11150f1c0204050f01141207030b03060f060f0d0201020109050613120503040512070614040302030a0908070f0e100803030c0414010c0f0b0c0403020909030307091508041b1511070b1314 81
    0x5107d4001d008203169580090306500400034545000c801609000c0b80d40761020800c440ca54501d8100c51036208199542da0300e17041c95100507805400e01500082c2a4041c48082000d19160446918421405070002c0c000100d81000140d82d148020f5601900b40e422002c4c20b050802080c01c010301005124010015403034004645807007002009032411401600002501240a0ba11100781c130080d000d00b00291083c90b00d0030f02d84899090032841000c805540d030100007184200c010014200411529043c0d941c0d070b180134114245150300034090114503080c0200c1c50b40c42c1d94030410100d00003a61094111405c0242511044004c9a000381b40c411003e20030030000c00162200701030f05020303008840c011900c90600c450b0151122229400090440d900000082a001da0005549400913003141c94000c120300340d03000d111900c000581064211451501c2d1b840d030296071000300b0750780f0741d502070041e10180d5454403045e0030b0f0781c41120344617507440140c003105009905101c1c1c0b80c841d103010024030184100c06 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 649933893 1250 649932643 649932667
    0xb03070e12010b0103112b0b10020606030706050a021933050a14151507140d0504080705010e1c081b0a0b010311150f1c0204050f0114 59
    0x7448080c565400d9441e0b0340480c03042d5030103001b0414844100c01d04030b42001058000c1c82451038078441218202450210281120070f246d602070400e074503028051a450712003a85019540da001510201c0c024410002c000540500c41c20980751165019400390005140d45c9a9843c250664000180c607880c0d030b85508284800341d0702c0c58206410700c0c030074104499141d0718907404c411507130028502c05d1442c1c2000081c8503a0b1400c800e1061b40541403900040f1485403a070701003030303008400d42201c4284c1d010004000c0144120740e440b00c8602014181285c0c00c1801083d000c84250040b0302c03402c43da9034061402800a0341c001e9180b940110310103400000c042c0301d0050b480140c0c6003c1c46083c0d070005400980b580b60034103140340840c0d94044030401022045c800380c1c0c034840c50b02d10520010b807000440148802e140c0d0b54231959142c01e84c00f100310782130301c800506c81403100d0355011031b00042001040004154032080240255000c03200c0040c03000d28103450020055030700340d03010350311040250000c10103000006 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 649935143 1250 649933893 649933909
    0x1202010f06061d0a080a0b0903070204110d0b120303071d03061008240f0c070506040b070906140d0b010203040b04060302031014030a020f1210090203070e100b03070e 73
    0xc1e4503038680e0030300c024100030003811000303912181c0c2c000c4103a11028014005c0000c2d1000c05158403071031800c0641c1e00c01c0d00860070340c054220002d500c0307400c11042c40c0d0803914000c00b626440c901c2c00d0003003043c030060340d04000111400500c117000c2500140300003200a401051072214003607a100c9840001050040044d00700380e403c8500c10181c40040303405010b2164100203030401c80e80506c9c940080206010030000422400a0013a0243e0005000140c07070b02106205482505034400100c0e540c1e0b0420b803500c00c003c483c0460f80100040c0c120100064920700c90217101c003501c051009981d240000301540a07000c1e040b05100385055101c10480040c40644800c0144002c1040740e42c01a2a03041c1040502041e01c0141c0c0200c5080c0a62108044a42d82c045407640c1c445078100c9013a0100140380740800d4440c4c1c100040c5107124003441c0310903203420b41941c000c40c0015100320281c0c4c401c151507900303050781c02c141602d840c405d22030601c905000004c800002145c0003105401c5c00240c911071a00021b082c0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 649936393 1250 649935143 649935149
    0x4230a150e01090506092d0c130204050315180a1a06010207080303010e0a0605090613090201270f09020304080a1121091504080d0302030c07020a031a090a0b041202010f06 75
    0x5512034400520440b203010445141c0c04e10149140c947c10b44500e00c290782d60540302613003510a0102901c030202c0b694041e41202c008003405410759485005c1ea229805602e40708071400802141010100ea18640020903041031056100315a1071242490069540c1006401020783d81980718514000c100100c080000c0c50081c4414400581c1610344407203c1026150241d01145c0280413410a000503903071080c4804080d1150440c0010b00c085c1c19000494583d111141d02d9038480d0750750040744500441010104003079400ca9412158401e03074614034a0200d11040350f0283c400402442800741c3c0c00c0c8a101d075045060041e004803126050082d1034020014030f10144c45803031340c500040410b280d0925238010302c010782c0d82e082c01504092074126002e846540e01d05c10310342015400000203c4c403001d0780007513420140d000303000140c0541d143d180095488418000b000c0c0c0800910000410409000480c1a0043d034083c054000e192070b00d5803001d5014a0f40215403040d5501c51820340010302c402e101d00401 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 649937643 1250 649936393 649936411
    0x30904020705161508040f15060b040501091d0615040b0d05010503011d030d0b0319030507031b0f30080115050c0d080903070b04230a150e01090506 65
    0x28540f0500074070b1410f030b0b41a44910410503075113410100080d009a0201d60054001c2000d00031038109141030502a141d00d01810000c030300c1e081003c40e0001842e006042071b20000c1c0c86414000e5115809402c0840d680e001030000c0c0868440003a40500780014002c40340c402184000d07003441d445a0710021644c00422580422965520040215117402d01480360100c0700c0c83e1151004144d81c100c111740320301c903290340c0b2054103032a82e50025150324100643e10000e2100c10200000a0451070000c10710f900080b425070000c0c2e0305224100c240d0031100175038a000f5503c942030703a10b80304203640d80b204800300d4480340944c40122000c41111480c0c58644038080d0154650300c07000c0c258180944665448000c07071138401001428086a00820400240090101d949040a010b580ea80301140c1d40366201c3e008008040d5003010040c40100300002c68102e4404111803c2c818800710142e001aa486508400240403040c00d0206240c0c0c2d0b00341c6501c04059028010008904122503071141c601e041c0003070300c1c01c0c54 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 649938893 1250 649937643 649937653
    0x10c051009120f0c02040e21042409060807050d1401090e0a1e170414130e15040227010e090d0f05030c070b0a02071401020901020706030e030904020705 67
    0x81000b018451a9194a0301d5003010114a00b02e1034000705440740100000b0300a913130f54035001b84101410401c000c1444403084080c0d0102c1400d80f9401d0040e0400d1013a04c0c0c16510120310f0078002104241901c00100d040d80d18a075041e03140c60000c840300340c40a00240e0074080100811040d1300c040c0d0040745400000088030780b2155240045040484a404c000b8018680008210000080c0200300240321244a5070108143d8207503414880e00c01c51024101441c6a41d00043c00111141c0b0000380007801007048030a40c00c4007146203240340680b107010802c00603a40000340f8211416250341c0c00306420900141c4151840066550f03545240c050081d40340c108404904010042405581c011507403059802c006040c03008210000070300568600c00002003401008400a00b84030200001d4803826a00b18500c101c8074101350081000035440818142c0785050342e0707102482d0081e01402141c2d0440300c184d0081c0340b6145000b100324010710f440a90450030740820041c40709181d40e04d0010341840c7c0e01441c0a44 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 649940143 1250 649938893 649938911
    0x2001020a02070f0f03060f060b0c0a060515010c03110705100908070f08030403080705190605060f04060f051e0402130518040302030a0f0318051c02030f030601030b010c0510 76
    0x42d25140140d4007220800c0c101e01000d000582041000c0b4044980c4194003084100c2d51b130200d031300900441d41009140503c0816103900d01d40000a01c2c000090040100700400e0315001c3c7d16104042e101e11006010174190610b01000034411070381403905940850035210f4031502c802c0011003103145c04600030000303903a031001032244000a01c142002440c1c1200303001d403481e00c0c00360859241e0040e84000ba11145011407a07006214080c0010901c001050600412005840c60400c0060006407240c0b405110312114200c01406c10740b1900081d1120404903a045903d01802c1100035000c2c0101d1400d034a00c48500300030581c880740081c0a04032807180403c46510301781401d1102d00711794200c0d090810b145040c24000840e40110440f22240494900b020500d40d500105401400585100d41081d01980d00c65a0602001041c0b503d004001c0c51040c0c210b103041c030f00f800c0ba85d90140c030080c403458540c20804114258020f40c40456000360605110403014000e441e8107050801c8010380c01c0400c2d0325110b80b5 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 649941393 1250 649940143 649940147
    0x807020f030304020a03170d1e380f031f15030f021c050d030603030f0c030e09130b0711010b04110d0e031e0d050a09031e2001020a 58
    0xd020a0180c001c608500d0716400182411145120140c01403078030109182644410b402143d4002c0c2c041603042c0404070382e10b006450080480030f120100c0600c0c00407980803407044251004002041c004081980151000b00345400c0105000c03026400403060079804d00d01d85046c4040d0030203100600d501910500340c15480d800b9203242ea20031407a2030b80240703014400905030380e0903000c2164040d00d20000110201003400c3da11901d6000c00b40c518030a0446095a15505402c14000d507840707035440c60903580001506980403181a10000d02259100705005443c0c10502c3d48540d111290100446c144c00d407944600850150546070440002c1d03d000440750f4020b024014681d2500054400300401e4004010301c0c0c2c807600583c0760b42071340c0740d455160280060100300155241442d011154508000c07414804120a42c4010402500305043c480024600380d1240b080303203000358254aa280c421040300496680201d00b0001d08024010301d1004114070341c40d2811200e940c695010700050b9035044403040 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 649942643 1250 649941393 649941403
    0x1c0c060c050a17070903060603111908030f0f070812151f0309060906050a0207061805030f070311070b0909251d0324150603062e080702 60
    0xca001031000401c40c02d084103600c003215105a015100c461085900d40d180d00301c03404112a80042c0400e03040c104044107210850518080114040b00d070840604103507103080d1014505403043c4034443d00244568498000042d00400040304503040e010b15180342c0340d0750981c2030740141c0c00074008200880108910102110900c0d0f010341d40840346608105100d11510922504800404082586901103d000c1051302d42007541c0080c0c2c08102840740d0303e01102c201d8001e41062405581030f60400d2440300110360809186007102e50080003a40c50282c80050341c0e000395110100c00c6041003c1048980423001040c000c40340a08410449240d0700d400da00304021594101804c419800e81e40f4400350000d1190303035040c85009805a00304661100b100844c2c0205900d0b08078042501401241070800301c0c0418980c403004001500c12541d043d5407a140510324060804401d06170304840300f080400c1da2403801c0a82c00c2c10904103200b145101e41342d07640401c3c0b21030300c40700d10b2107010601c180140300302660140704c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 649943893 1250 649942643 649942661
    0x50f06070c0b13062003030417120a05061311041419080c0f011e0f05130e0601030e03251403190801150c0b040c0b040303020d020c04050105011205091c0c06 69
    0x241a28a903a00390b5119107d1102800c0102a100050302c0c0c84860b140c1c640c1941c0020081c8140031503507143c00c80506010745000c80c1c40c5441036071000100d07954400148500a02031030350383d0556080c1070a04480b0b05200d0046d0303c8103607000d101d4603401c1c00d003c800601380501402c0201c01510443d290802445074144807902ca0b03d041c411104400c103a042000c02103240d01401610f00010710440088041da46071050210700408540850700100f00c822051750210301504007030741e08100000118002c03940f28000d001040b80305d4011408420141c6003030303001007040b1030301840002c0300c1082c4801a845ca036174040b081000c80d1140c0452402c64494000000d10300410381ca08110185000c4007900400e81c400c030480040000c0d000d100410244007182500704050002c01d040c0c5d80d80d031502c2c2d05010796520100d101d00300040c0b00704080d955042c2800d000d4681207900c10703120340040125502a18001d0000180010310034810000610356941402181075802c40d480d4485444014050503e0010350341108 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 649945143 1250 649943893 649943927
    0x604080a0209240904021306090e07050916030218040603050a0c050a050d1713030f063602150f04140303030f040b09071d0a0c030501050f06070c0b1306 67
    0x2c3e0321450b0309580c200804004010480301001c03a43c0d01c51000071000d44490820f20051450f041003c586d44180b50311464a5441000845032510703603507000c1080400048400d800361403010a1000245402034012f070903c4540d0b0a00003560a01007400f19085888a0380107480c59403200000000388900150b03254003030902614140750042c14000414414100c410004000c40c502d480c0381c650101000c011340310b01c018101d1511010641d40d045c10070304c900300705200f903c520703140041044100b5030b0440f4080f208440c01413040c1d4850003002800f420704140d210140d07008550060740700b403a240c083c03005200c0c000e421806241c0751401d000d200740c0712a0450380154040d134000c2050200d090414221680d00c00e0344008007040075650040528184a00750340500c400741d41480e8030500c42c400c440e050074400d0488100030041710b04005012000d0320030a215098005d0b6003600c0084990801c10000c00c5560701a0580b440a43d94030f07110300645501000070a01c0400f6810002c0c0101640204094681c440c52 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 649946393 1250 649945143 649945171
    0x306010f0e0109180207060207240b15090102010f110a1227140303070822210306051e01030506060f030c1803100c020105010824060a050604080a0209 66
    0x20002e4050003060152080c3c116400384c441e460f840b40c940446407500d40c0300f00c080d51101c0180c03a11a02e5000301c403900c0c0111039440541007100d055140b003a8442da06004200e900d40440c022210030040c0e00c0b1440c1c0c18115503c40d0030801c6455041c0c058244608201f101c050b80d62050580004e000b0105d00d00f2100101b07040850082107108120603c440d4190042000d03074000845140081004904503d034040030b0202104120b5101d0304030404901c2078114080c4c2d85a40441213030360070223040320700ca001000d0903d040c0300d0211000646c00d0341d0481032242c0c1800039003243c84000141c1051903000300d64400409180300d2102c41e50f07050251307503040042a240d40781811004141070855000041000c0c80e0610003060400c94401c0c2005664018207015040e12109418240c2c05006414440e910f0070140d0b00f40b6000050f44540003078452041d81c64400c20b100344003540002c1c400c0001c0c01070001daa0110040d80301140595035400180300802840700200350786040751050002039003000b85622046800 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 649947643 1250 649946393 649946417
    0x90b0f07180b1602120309040b100c060c02010213030b090d0f0c0609020102160b07110a06020c04050a060302060c06092a060d09060513050705090402330f0306010f 72
    0x1030070500c038050754068440c0da5240c0c0711034801c1c508258502030020307500c041c4040d005114841c011008192000041d1400d10280e0545400d00a40c0c4080103005000035421010050202d41030340d0018900070b20300d00c001741c601415041b080310050501d40040c0e80d14036580e802d1107031000b010021401d412455050420030740e205000b000c0c101c00710800c0042c01c426150010b00c021680709102c00b20050400903125402240c40c3c42c2d09540700d40000600b140c080071010561100362400c110303054121080d5500606420180406100140401401c20201540c5450010005a480401a141100c07010000f0a00d0f880c0c41c07101a80b801e0f05400007205003089111410401c0d211464405080120039581181d403100c0c1c5409200041814200213024a458071080c45106250355041c141e561f8012400c6402c00f03600c800030070120105c262002540207101c4c9054601c80700c48100602c494040001103056642100201c1034860340c03210410f540e1791030000080181e2580c000c500c10000c0c0740c444c0f514080d00a0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 649948893 1250 649947643 649947677
    0x9020a0e09071421010909050c01020f071e0f0b0a090608011401030c020f0111090f0915040e0307080304030507060e0a0c42080601260c0904090b0f07 66
    0x4441d00082c82c00b0001d42502030003059070111001d03000ca281c40052035a52806c03103d0092100340400c44960048141c2903150f58400900c803040d8081c094040c0007820300c2c2540180b2818040288941d00c2b40305200e00141e41c80031505260020f00c401840142c1c2c458410a00030f054a10680101f42400001001406a1400c160380e4075400e8a00303080000e091510201c0580c60b08201c400824081e6082090071410060340c00c000c1d11080d141035070000303600641d000421440380ca003100c1c40010061002000340192602d6000701e0f500c2e041410079a45030151079201c1c1d407080e610840d0160089000000d8032002c00003c0d1203800ea015141c82c000e4042c0340c8466030351710188800d9100d0304840280810032120850850103511020700d41d248100d08a101c0002c0c03c050408001444860110342c04030001a0103500800c4a40305018090f9141ca007525a07442a01001d074001074440450884d051040360701c0354945129004006004922114243c030f801d00c0f109015040040032003040241c40030004500d20 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 649950143 1250 649948893 649948907
    0x60218090115080a0b0f03010915111c090f0804141e0919150909141219170901050f071d090402030a0204020f030709060905060306010e01031509020a0e0907 69
    0x1e00b42e2000c240c102e00d105c0000d29004402007200d502d946400c07081e00421810f17540b461212001c0c544188050300246154034440e0003a5a01c21103586e03410305440041e0321040d40100c104901c602d04000e008465a152400560495082018407810312200c1051030320307024000c0c44468035070190381c5040850880c0810b0440501429800b00100b0803200000c600000b500800e0001c118000000091542c031610140035080004056402036180381c1d8182150602181c1e000b0580e40050800d071901800003074044105110f07404071410004209002182940050800e60242204100104090500c829000301045010340902c0034440c043c0c4a2880d042c0c00c40360f60300d9401100301d826011700d940380e001003420b054011754020341c081e200180c00c1e20700e0101c040140d03002e504a540c8518201c2e4490000386c40040c0c041c003819030301400c140002000e540c8200c100c0442c3c100c042c074003c12203440703110407101c50780d0150b080b1149290b00480da4400c0f83c0d80c0310980c0452401c1c201c40494007401d0070307000070b0046 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 649951393 1250 649950143 649950151
    0x12020609150123120f0a150903050405010c0624060e0a050a0513090f03020304031a06060708092d031603020f0f1203031005120f061f0306021809011508 67
    0x50440143c1c09081343e492048500040d1242c03800d03245481d110740400e580741c481400c01240d100b298400032214403401445000d0503640d06484030380c41d180c2000010340b51801b81380c0c0b04858007074542420607540100c900b04c2d180720340b401400c0120400d041010140c0498041c0680501642c204d04041089a580c0e00700d1100306c400c161056407a00c0c034040d800c0c601400420030040c06641310341d0081c6040590000c000c0003101e0240820011050300c801520107141002c1c0d6045900c41000e002100102c1c9500c0010f140b4600010b0203c01010b035003030000000800c2c1010301c007004141c1c000d80507140b03040500080842e00c4030700139001b800c3c0e03065034006009a001c200300d250041d25600d02c0782d00d0380c0e1903000d00041203c2c2d134001229101d00d005802a0600c940b6405894006d0105c082e4080700e01100080c1050040380f510b01400d6550b9641c4000241500b200303c0001e0318803806200000801c213144028641c5142d4501d40d003001003444410300c081020180e115904907010501048030840c1e00221450700 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 649952643 1250 649951393 649951439
    0x20111011808091305131a0c0d0b180f010e0105010e0607080307020a02190f060302030c1803030409020406020f06070c0f0b040201180b0a0809061501080a09120206091501 75
    0x3a00fa69602060800484500104a103450f1200380000c009a4241d0110b0051140003c03031b4000344c80e14075100d01c2e540142e9102d180304c0c0c4c080c0049140440140c102c1d03101c44c0c038007a0900c6082400304102d194098810345040300e44640d16401440020701c0f045216026040a0820520340740740d00010500c5885940c0003c1c00340300d4048041500b0f58402d020500303072650001c02d41c9030100e40160817400705040903c250082640261000a1740034003e0081d6403040003400e204e503013086640041c50740d8200d4441059540340c042040b000c5407040c0c603072000e00050261580100148400000c984d0f10f020400340c0b04206008202c24480005070740024032a1040d5030111424000e500c5903c0143c80242a011051481008030180810660882c8e005007031411300c0d82d50340e80c001ea110000304503110740c401d41d01d491458601c1e035058442540240a844e03001103669400142c1d9940b41e031601070580c07001100540040c0c0045003072000c51401040090000c40707071403055480a51420280300c500d6800380902d449 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 649953893 1250 649952643 649952647
    0x30c0905010c2006040b0a030b030607081303030b1e03211e040506040e06031b030606060f07060e061f0f150c0506010e1806100614041d04020111011808 67
    0x80740c543c0442c20192480d0181003a0340319512501560115003040900303100291800c00e64030220720b4000740241c0150040d0b21010034540356003001010348420001d0680905459814850031603c4100040305140a0f645145009580c502c04041c200644201c285140e11441a0103020142c1c583c8100c8441c0440c82010f8500c543e079003c00c04450340103a500ca9a4004400300d0b00081c1882c02241440c851b482c12400d40d0840500810303003c02c0a03400d1881340b43c16501103070018409017042030060004202c5240001e0804c1c0e29a030302d04040d2205460074000f079821102c244403408551030502006820050004a01617091407075000003038801d84241081d80300701c114110b1901d40100780d460b2000d608036064607200c2d85c440c26584070700c440941d0010b817a01409980c4086110300856801d000d01207041031b00948600d80041110703484115030703a0740d4034000c0400c000103000742e98400c4d0030700c061925442c803000c52a00d40005020f40800094240499051181d20b80e500d14084031448019584840c0d056 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 649955143 1250 649953893 649953923
    0x2180103090f05150a0606050c0723131a030609030304020d020a15020c010f030213090c0306231806010219150e0304210b04060504081201090507030c0905010c 70
    0x403685000420b4003030501d0268043c01320300070a40b0440244a0002e2180c24071800381d441c0b500f201c4c10f1007007068a5185400c00c0201b40180e65510b580070321000e04080340602e50140c0000011900040c5116805020303603110b46195403500c3d505000c205980701200a0f1200f45061007600d5120700c8009d200a00c50b0421003400c6046540700b18512025001d48401841c1011070b4440c040d546034119030840c1c0c0464a072400380c81242d486402203d018069030b0400071a403500d82100000a4050280c07186d09040d210b8001103021031940d2042003403242500d0803d60032080308400e001601244c043c41d030000103a10800c009160340c00164003001e00b03940d0942000c0420442c1490fa090381040900c03501110708110684d609038500001400c1540c140c10960b040b00d00c082c0303443d16128000010b00509441020000501003046030780450790042c055840709181810300016010142026045504455510700070b2100744c80d8940300e000305c1c070322241c18521700e001c0c20000040d120703510a10000b0091038903035080c0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 649956393 1250 649955143 649955153
    0x9050604180b2715060303030606040306050a020702120a2010050a14030907170105071704080f0a030c0e04060f151e05040e0903040f051c12120f0218010309 69
    0x2c60030f1903001c00040030110300000b0311034413000d03400350b00f4081502c41d90216030240340110841c0d005640c01040309242c649540e81d0080600b200801c0d0f801620380c2400007201503124008109000c03014900039081035529803411a800e20081c0e620a020500500001c6800b501c4e4a551f140c0403049d1410845d84541003418112001800324200d9002554040240001350000040711020388411600c80f01f01d4a00200e491822107000301c482d100095183c3c01018601000c000d10b2540042c0503502141c03501c1d01880d00a032981e8082109840041e035110f000b000c106600071000c40404074119414805a4500120000c0c5c00300d0600503242c1000704490054100d03270150040220107040f4540e42a11000302400107000c98000b07204160400260344c0001d8124030b00807040300c0903610b480c940302103000c1c1054184468804030011902084850407000e50100e6001042c8400d60000c030350720010710a016404010a540d00303510941c0c110f900522205019402111682004010a1030000f0f110340d028200 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 649957643 1250 649956393 649956421
    0xf060e100609020301050301060b0f090f1309080316030c12020f04030b09031902070f15200a02120c06030c070602161a060d021c0c0503010c02030409050604180b 71
    0x3118035240503000900e02d14690040c3d41290002c4001b0817410f0b54601001100b0700c90300994441e107410800441400d0720f80500354110440025100f910441d10190b0b04000b00c0b03144240c2500d2010000c410441150b19402d408401c61085140a00001c5400103000c2e151080448801e40c01c00c1d000300b0110342003c50402520000d42d00100d0480c51420030a03003d03074503540403420001845c24500462005580002402c0040342c1848144000161500c0d001990039070600320504100521054110340811000c0c4942c000030500030050311150300140304118074402074000c1005150000d0b00c070740c0003075030750718080e05e40c803d82c540f86d096540d0426203840741c000e1281d0341100c02c01080040441c1c007800300941341d001c808142c1d400c000041d62103040030800020306a000013944000c2030040002d441e501550381c1d194062151102084d910340300c0002a003501c075144611401030340042000c10422865000c0d690300039005031010445500080c07241d0078002c04029000d0558240040400c0410780ea40352 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 649958893 1250 649957643 649957663
    0xc0904020a030b0411031303110c040f0c080703050709060c080d11040303081e040f0c0306061d22080f0c01050c040815062b020303160c09090f060e 65
    0x2045549800000018009100b02c0344224040c52400c034207022064401c0302241d014510750403040c2c500c405596000c5454803040c003020322050180000c04080c0b0b480c0e074010060120400900031960380040700c00101010802001042090700300020b01220b00d4000900703800f51100c40c1740450340106181000740c0148118078410000d1484c3c0b0768540e00d5964400b0107041508c1c03003a600d00342c154841c0782e0341c9021117030100e5140010903100c2000c01e0021300c180b8600031140d4401d002f4003881940c0c1c2d031203030000c50b840c5511224054111070b00103507c2e90441d8000d0f40d400002030403c00e024203008101c056a2584a80e0020300d0742d04001a80760400c1c1d40c001c15200c01e4402070009000b01d19001c00c164005820038402c4420600c5450080c84450804614582c4501c3c6c014010108005040c075901c060321204009103a03403108402115800350724240010000d1710301032003c1c02d0202d0468645002d000b0040d602650301c8030310741a02e40d40000e849032042044650415400300d03006011122250821312122 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 649960143 1250 649958893 649958899
    0x27070c030c0b0a0527151e0901060602011d1b030a0803090106053c040b0a0305060402092518080615100e010507020d03020c090a020d05010f06170c09 66
    0x10041001c048104d4001e0b0b0b1080582c114541005000500c0c010481c04015140207155003001d180f180d69140001101680700341046084140c80311103da1000c101e03d4103481b01d580d26511000184a059024041e4010380c031280c06041c20b00c1500c450b102c41c0c607124a100001250000214038914994081005480c4140c101301f0413075403410040a114000c0039944602402085e403000300c01c01303807140c0680607200c50354100030251040066040749608540340344111a40103503580300b2980107489a08101e03000d18407410042079a404d060041054030000203040c55501c10004559413003084081e00851690007450030400020208100c3e10b95000c052342d0400d21443c40b400003000814a0b0754558620706410a88604080c00030014040302c09000d90300c4c002d03010074410401c3c0001803c0034101c65907414028415125280710060005210750020342d196890b0030707004503804400c00400d104080c010150685021f90807440d100c0c0140c0201c000708420100c6d00c2c5050300003401d482c042d20454400304802 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 649961393 1250 649960143 649960163
    0x203070513090e1006080c130204092c01091208060a051804020405390f03240402040501080703090c0b0a020708010b0f061e0706061427070c030c 64
    0x202c200c08014140d1221101892065040c44111424644921425240f8180242200c44112414000148a40710300003441a07800c204c0040c0c1e16a42d449a9034074be800703004038820501407410981e078041541c404090135a901d0450f4540000b2030201c11103c01c603465041124540d80d0346030001d4800c0a0940c03102e500002c426041010f1a2810408184214421501000280c90726042003c03802406025070007a009400ca8501c18070b00c06920004e6141e60550f141454009141352412098105640443c40c003010388129051402111300c0c111000d40301510118101880d1130002000c0c5000640b4400c241940e80103880c0070311072202102d81c0608513a89c5910303070321010301c0350003545d6180328404c40c1c4a5510388081c0740205c1c0703014170030f08510090082800f41060402c0504080040d81d05102080c9100c080042c1c00c00180d05000b404004c0c151603a4240f50fa04510050048100f0703001c80780442038040450718a46180b812005ca50056420b1400002841c0545415910075803d1240a8948a10 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 649962643 1250 649961393 649961399
    0xc0609030d0f0323040605100e150d1b0815041109180a110a0f0f2601050412030e0a171317030309190f06200a090509060d050307060203070513 63
    0x2c03130000d00d8007031481100104165525000c0380d03c2480100d005a29400c185c004c0411440340740164070b1159003000411400180030725655840855915540b030140d10b040d214820085410144401d80d43c503a8020030341c0115103041d5888801d0311400d056114440d82c82075000c642604000d002c04c102d522108000c803011a0210f08010242c03000c2180380d944901d400392800300d20500c050704d10b102150a4004180001800c00344480b035058182041490450242c0110f030f05c440b0402d0040e140110302410007407a80c0c0c01e10740d2000742603408280d980d10891340042c011031b001500e000c40400001d110100c80c80d81300d01c20702802e400b2203089540141c083d401d09202c00118400003200850140d40008210f0b050070003c403150342842a1050390242c840e07078910740760b1070102e03c41e0b4111250010b10300000000300303003104041c2c045a4100c02a8000018440841802141407420760703030340c000138100e61000d4a050280d5800340e4070300c18014020103854000c4080b500460141080d0f803601e07808141030801d403d031 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 649963893 1250 649962643 649962701
    0xb0904050c070501020d0f0b030a0b0a0e15100609060527040e010c0302030613110a0e01090302100f030e12070339060507170105010f09030204050a020405030c0609030d0f03 76
    0x407c80881241d010b181c1030a0001c14940001c43c0300f10503a0000116201d41d5500b201000103001c0300520200e54041c0c0b01c0c0d298200504110140d00c1288402845400b0605103c0000e04002c1395030040d4080c07160030040e08040d42c0440e00400c02d03000f06030310745c001020103d0011401030408113a0000d025802c1900c92861b040e01a0080e520840c1f05071907007090b40045560385c105581600101b20401076080051721801c034440c0d0a6400301c6803040c10640c000b00e40c3c039404101c10034079800c0804000340b00240c1400140380d241c06413003030103060b034401060461414803c0c894503100e02c490050512104022854000340300680007032030000c00110516048019140c51202842d09801c12102e461519000411890107081806001d122081030079120b42c1c2014010346603241692881401d000b0f8121000005a4460088922440090101503120340c900000d1502d0300d210140107034071407441845050042c0d200028044d25201146c9840c2c4a0000000c0007a0001d1511040034010740c448500e00280b646 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 649965143 1250 649963893 649963901
    0x60a020a14010204060e0301060608010b0f0403050a08070b070305040201050306040c02010b09070306050306090a0b0622090813120f060506280f0b030402030c0108071b0b0702160b0904050c070501020d 88
    0x5081901d034211b20301080001c2508a030f599008601c0410031450062283d07020040180800401c0d682199240a8694596610300114800700711208040055000e0400a0030002c00d5000310f124102407160381007650001c0c000b400000c0c2141d009560743c10007a0316282c402d406c4441c0084010700401190704010070020041d100500406029104800c00300301410f04c00507030002481d4109180040b80d0700c0e014100021842c091044442040c1c61003603d03400c9845902c0f07540c00261081003000e6980d540060341c00c1c40390103180d0000840368841c00d0003c01080d5044d0240b00714030351006000510360b0b5004002814000140c1c1e000c140f800380040ea80100c0303000368041c0300c103841d1a003451841c50b9036640b46070003880c40210380007505900b10440014941d40218040d0350400c2c41c90402c41e6107030b54408015407064030809810f44054004401384140036806012080d85a01c03525003403041d85060a030701858071b10400503818022680c0744001000045840107480341258414000d41d980e410301004030001d4 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 649966393 1250 649965143 649965149
    0xd1707170709030b040f05070e090a08070819030515011d040b1210050405070e01060f0f050d1418011103070e0604090609020307080702031303060902061207020303090607050a0905060a020a14010204 87
    0x1f61103091004076108001400c014032a200030402419030342e845940784901c0c4d400080c0221201d80c070a21441c078059400381d41581041429a8000070719141940074040301c0c1109000485c1444030300c0c071b028605140d2440b40c00078065002c0d5404510050283c0114040c80410003000c01c0b140586510780415901c1c5402a50280d4060000c45182c5030302c801c809074071030000388222000304003a10040508a40503150003c0041c04504215041040d40603404048d00c26100c01e00640071503120402c00b0b410b10035070113a05001c05d00c0b00200300510500c1c03070708000d07840042e01035030611940c000ea4601940d601310031100a083d001070244031040d0b484541101a4000ba6038074004a00314400180e20244000142c45074412120180720410f455a25604010001148280d070020b008004034180c11451990a50298040303900541d0b4900d025005c00c0d0500002030010000c04c4810080001c950794810360450903614101e40040c2d540d00c200c2010303868014112401001c98405026545203030506501a00403 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 649967643 1250 649966393 649966403
    0x40305061009050f040b04030e040f090c080102070305040b0c010905010219110607050301150c05011805060709080a0215070605010f050f15121b0c0d1707170709030b040f 75
    0x180a442d4040c07002503070801c50b0070207441210703c40050301141c1014450354100340282400d2908280b0840480c0a4442d09001c1c540e80a40b9079502100700040482280010044038008500b03050495400512a10580c800d1070035188001c24142c140a400f944480051684040210741d0f44840030241c00c0c16416024510011900c20011040940400709489118404982d90301b032a42c0e00700885010440010707070150040009004034000050024440c040d00903c80d000a521049150701d803062a000e4010b01c40c00c2040f00500080044000019004110550464243c4044040c2528440181c021400e0280105091030000141442c2d214040307801d490080e104003400d00e06c0c4409000850f8100101c0320b040c07000c100014005410880030254001d81201c41101103004501404144c40e00040c800c1685508024118601690483d1000a0001000145203191f1504050242c110384401c50b102e00c8100200001401d5240f003660288042e50744000016035505050400c1c9090b80d12640080314 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 649968893 1250 649967643 649967671
    0x30e0405070203070f060f0e03040902250807031b02041d0d050705100504140a030f120624090b0703030b09150901120c031703101a0f180604030506 65
    0x41c00d2010003240d8903550040c41482c032290040c0e46c6e00b0b00408121224400950b505c1c502d120002c0c0041c4000c02c010001030a000d601ca1480e03103131414918110101c494035071010b8440402c0010184000d072080c080d01800c02c03070741d0740c0705050100038410b00c00c4900a40c0545400d0850320340c035a80c10119071160b000c2c0c03003c136000070444100545861040b5440074002d6441050618035210b11500700300e83c02803003900e0032007040c601d480e5000d15241040a085010a151314440041540d100f4039541c51200c03502c4c4280007251420100703ca201c5030389582e9903c56111140c10a8400f4000c00800c00141002e1036100c0c3d5540003410700a00910784001d0b41340c49410902c2c0800d01d040b156450b1640c09003c001e00c0c84c042c59180a040c07800184042004031080c400d102e00000204a0b0a58110b841c5040c405c0360300d0381c3e850402503031880541c0715000069686c0003c2d00d030310f0707800e0304003800c3d515145000c0d9551561015003d258900c140c114218681d446a070006000c07040000c081303561405040d119605903 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 649970143 1250 649968893 649968901
    0x20c060703021c0f1403090703020301180303050603030403030903030f0e0a0f090b0604031112010b04090b0f06100e0613050301020409020406080109050412030c12060b0a14041a0f1204030e0405 85
    0x942c0700c2011610100001e401711140b0120944100045420422240490700714550382c2d030100c6e09491b5145081c04480502c44001301c141501806010741c0041c04a025501d00340c21650007038500060b07804080d0800a0000501566500400082103080401041c00f0140c944d00c0d0030003808240b04d8003a0442241c100f001700815400c0c910180c2c0c09a80c0c1c0300a40c6031441c04010244a1800c5c0c010180900542d282c1081c908070783c07501d21400340940d0107400405039030300c3d0085120b1440c0b0000b816541c0600c002071945846564004041c09461104503011665100c03145400c4120000e51307004964176510028001950b228568000c0044444076191248a80c4c0d80d226242c00310703503080b24060b24028038203600300c0049210341d00680107040e590a040700c1c844802d01500c1c044523400e8000030a413042c001042c401c02d03504121501d0341c69080410441c40c3c0303404d04081119a200080005516540c013107495500018180c0030745204850310b1007820414503050500034080b506014105010314076280101e = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 649971393 1250 649970143 649970147
    0xd1704030c0507170114061014070f050703210206070f02102306010f0f18080d020607030f0e070e04061e02090f0409122102180a09050124020c060703021c 68
    0x2440340030001c108c8003d91010a10a8400c50800e40c56810044410080b82000032101c1802c095058098002402054154079103980d0841321300d1402c1003011560200800380a07400a400b071b6100d00d01d440e06500c480b06c801000c0e80307000c40100002482c10704001064061300d03203c0c2840d03149880300840400031512610015500c00b010b801c01400043ca1340c50000008500881c00700c44102d4643e4041e80010f036807501c2984c20860405519001a0010010f1000d201d506008070807045081c2c200030855228940081c1c0e41d00e00d860b11400e10300705882c10014091025603441000701b5501040340d0044608101c1d803103402907201000152040e1f0140503035400505040c81400d81d485d034030410041840110180503550059a98003400400c513407520f662040140340c0c005008101100e1402c00c0e101e45141d0b0402031500081e07007066801e1403818004001c1200700d10440380850340520f82258000c000800c049081c1629120800c0d00302e540015408105503000407121a91400072280003c3d0032070385a01 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 649972643 1250 649971393 649971431
    0x5060705071722090b101103090123070b042f010507210e13020c0309060706020405180a1b0806011b0b010e0907080d1704030c05071701 60
    0x14200c01c200c049140a0700d6240001000c204501105007588400c00e07450707030f0710702a00541151309125241c00651410707040c48540d0018142a604002070030401002d649030b541d000b84500141040f486980c07403819822014101e4070140ac141c850184e440709917080086401c1e0741038408032020015030701c245003409860031064182403500d002407103c1e07000d05001182ca82d00943c2007078617040101500b045441101780461040d490881c0c443c01c00840040080251070301403a4030b038003002d078010004408211404400c8030b560010813280203442e07540c103007820b4000b409143c01c100e4200000b0340100e01c45c20700425503644100c42e07000c02441914070100c04038280c09083d0004c6170208600801043c1a580907142d80440303000314031134418501c44c5503122a00d65070403e174440c80d40a40124240185d65006201d40070141c0507000080012007a0104018220503a803c04400706100071030100701014440d0042410540e008000c8401d0261200c2c40c0844c03055020785640b15a606c0c16050700d00ca4010190 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 649973893 1250 649972643 649972657
    0x80f09070e09030903070f1701090f03050f13060503040b07030b0109030809060c0105310f0b06060d0518060a0c05041223010902040b04051531050405060705 69
    0x904100ca00c1c280551041010281a03011640801e000008154500b00503800c01040b400d02420a01440d000184408000d5203000901e164100303030000d404030301f04146409449505142c1a6500c9800000d00900c1740500c01ea651000001c20400041d80c540c4800a140102d000352026103090719130050a4049403924030810303001caa0a60801c10110b681c2c4400381c4070f005005020140380c03c654444903402c548080394107010a0b0035130720082c2d4690303414210141020388a600c49481c09510ba440fa00182041540e0003020281028002612501c4804c03c0d80c480c8203103100c0c00c0c0301e50301b4011003980944c2546041002d061080600150010015001d00d0007d0b20980d21502c1c82d1a08080100d003035151080010349000d05401035541040e11400039031030a840b01c1100001705900b0520410003546d02c2c0020700c40c031984c184414016500501150f5426542e000c0781e005440d903400460101c00d03883c1aa48619131190000d0341e150f1100c10b160045c80c4610301c47c9050300d505640f0304d2002d0303c00d070013001307 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 649975143 1250 649973893 649973911
    0x3011d0c100e09131506080f071205030f0f04050d0308370e070509040813060509010f05090111011d010e0703051905010e1e010c0206010515070201030603080f0703080f 74
    0x1d808101c11458500c8078503075042c09200045d1350000030100304400ea81c1582d0080390305610040c00040f6040342032102e0000341c0300c400f5812110700401c1d11442d07500d00034140c145005803070008800d00b040d48980d003102c2c01004040d100c0e424518503414050800001101c1241c00306020490002e040c2407024403141c1c03802503000165001403441e0f00400010203000381912114425020b02240c282d030303450b004601c82ca21800003196a07078103254410785a100103510203421310809010b10015070380c0050000110f001c580c5416074441e4400c0c0c00498034085800171444140d46001400a281c1c0070700c01042c04840103100c020310038001080403150b5655034038840030b40345410005540414816511901101c02c1c060f00001ca2942c0c10f030084941003a0854140d0765440114050903d44403800b170050300000702440c0042c021641c50302c808141203180008100c141d600b4005041400c5a00940c0000080d40c0c101040e2502c034181014818410340c480d100136400f05d192400050040456250f1842c4582065 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 649976393 1250 649975143 649975159
    0x909090d05030a0c1b2f10080a15080705030f0313050f0310050106082502060a050720070509010506040605180607120201150605072003011d0c100e 65
    0x283c281e40300030885100c0d40000c10501d540c8040b8180500350803009440c0c020075005c3d0b030941008075165148a00340c01c06025001c20400b40d80c440e96914010510322002c5410110741070385c1c4406468004080349203407040450032140380031610703880014064061f203400360200c0c0d803800c9000c820303243d890103218034503480d80b03a0702c10b030520160030800c100c116001d20180c2110040c1044007082401e80e03000b45c01450004805408200c42e80c1741b83c0050900b1a00781544104e00004c61000003922441f0003080c900302035807500082008580700b40030707c54030f03001094050200b00e403040070084c1c0c0343d8015105492160410400105080c50042c0403603080f18000c0c2c0302c15140103030b505096a6025030700101103074132240510410000c50180407003086907040c0313513000240614080380d0314010046c06400c60800c001e01405034100181e4401c0c084440a00b401320030350140007a40c0006030140c00d00c01717134200d085a06000c911034084d0700007030100400002180c4000480c01e2010f011a0051910401c0a500c855a = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 649977643 1250 649976393 649976401
    0x50d08130b060d080f0c0a02180708041209080a030c060f0c020d0e040603021512070f0203161b120b0606180f0d061a13050423030418020909090d0503 66
    0x2003c01e49400c410f21410101e030034498103c0c2d0000e00d90300b01215903c11030b0490800001117183c034a2000fa144543c0d94110401801c190304020308511000b04020b1030300c011242ea44039401c2c000d142150040000c01c040780c10302911032800400040301c079101107440e1420038801d03420080841c040c03502081c445a000303200c00741ca400c40c12180c104000c03805540041d600d00011001d6160110040000443d07a210b86580321112004080e010100400b1182049159841d10760141c2c1d002c4203d80401244058a0805e0401800c00c5030080014031070240a02c07000312000500381070f040c07041c180c84500034201c40d401503030b50030b00f4446944640c0c1c0411648a03c0b601220345c02c3e20303290f0145501d500b00904030312189035403903a070007044950020b01c580c80036610003210045403030000c0e60031101c400c0d8190140610f040035500d440b81c3d41c5801e0302031000102c3c0d03c040940319000400031b0343d000f0704a200b458000c080380b4245850081d440b03482e401e8060030800c03001549244001a0841c0c00c0d1046695003451695 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 649978893 1250 649977643 649977649
    0x6080f06101209150b0f010207080709150902071103101a060f0c070305031909030209040b060310140a0b0303070c1503060807180c08040c30050d08130b06 68
    0x2000c49815115103660b014404082450043c0c441d03000b8100701e200241104c40c035170401107085560340c5990304542c080303141446006000b144840c01c031a82c105021030070040f05443d042d111001900501d1000c1d1000c25844103100194802454055013502614074080004c0c480708203607640002c60214003032951003040068241800101449a02c5000c66070078103582c403803030a04000b103a501c02e495680c00801d03146c999291b600b01c01c208440007400c1100d01d42d0314682c041624034200500181c441036245001039801c4e2014090071140c0c002100c8100501c0150008100001809884942801e0b1a20541c0e400301c0c00c00104a0310342c190024041c003090f6140c041d4403009070040305900303800c15443e404002007002007040f03d000074083d1001034820715000061001d0849400700d030f440041000c10801d00010030038400c2c0c5001a112036029140285020441448a02014031540c03083e10101081c803e00341b04001c9182c0c0c0d81d01c030095580c088280c83d0700d140d8581d100d020700000fa201005880100391a46 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 649980143 1250 649978893 649978907
    0x6050a0b070f030c121e21020f04030506010611190b0f06031c110c061e030a060308120402030f0c100e030715110c010302040f0312030905060a020406080f0610 70
    0x1407291a240c00001302a940fa05039030078514031a540421110941e00910384055019440602035910f01203a014844c0d560181c00d141c0350744442da4001e40e000070007620310798074442150051a00082100c41950356014020060400c1104411140c0a243d440082031809048074068180d0049410240e03500c0c0d10442c0002d0010140c03410380e0500c245080303c0d84018040c500e042009074181c0300d64582d4080c1c404118285a80c1115441c4107510170082d0340620790344017108d174544000c1141c00c16283c0d51407520981c024001504050003151000c00c20b42c0d107461b85942610703c114801d800f035814840c18052100d503036800750415640e1040007004079811491141182214411005040790441035031103400302e10031032505030040c0c0002c3c404441c400c03625800f00a400c4540e40280780c02c51030180b0b00482c000c035064031404000c060640920815103000d12070b400801000b80c2041c01d807000c3d07003001e91045000703501c04c1c4103001c00f003010350001900340d00d148036980c0e1044501400b01a040420740030219418 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 649981393 1250 649980143 649980173
    0x10b060306090a14070c0c12051207081e0d0c0e0105180604180b03060906040210030b0d150e1009120804140607021e1c030507030f0504050c0406050a0b07 68
    0x2040c4d03500400703040401038450240c0a1003c94550341d24094840c200111014602e401c0640483c8000c80001e0010300005152103480118074041d50726400340e40340648851080010a44000450324206405142240300404060000c090100100142d4050a03110340201050160104509000182800e001c0300981200c90400500d082d15190300e59455000c0d03882d8082d00d1950943ea56251a040350804000c4c079078108142c8401420640307003681c000b0f00341031105a140010541c0369807a111880e02c0d403003190241c195000f52a00b07a8440011101c600070550742503122102d01c9801403070111000380d4030a0f88080c6030400842e0000c00706021301540e6009018104a5849112801410803594103210381400360300e41d036000e49181c8455445600100c43d0303860000f85c2981140011f04524044015046182d0300c4e24100840d050313031070500940061146c0d01d0818040d90905040000708040410110f24070b034070440381040f00720381b0742091040381c02c824010004540810864907000c151511410b10351 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 649982643 1250 649981393 649981411
    0xc02010b03031308160b0906091224060d020d020904080f1c2d090311030f03010519030b0c0310030c091e020a0207122109030302010e010b06030609 65
    0x50318030980401d20310791040c07801d115410b2141009010300d05060140603111007203010b5100b4980d00700a59100941306001820344140d400060700501510740300c49141d401401c44056480c12214048c030341940d0503100403140c2011400700c000035003c3c03500d0f240d41c40c90550040c211902c0c0403069402e00c60a1080038100f50781042c0240240c4042180900081c20030031001a101c5030307403400000d20001035074510014145030b4000160f4450f84000c40da5406c08100c40c0440000c40e01c50381c00c0c1000c3d00c1800701c5410114250000003585800307683c10000541c105c810a0301e80305001403000b0b6400042d42418040208003400c0800401e101150741d00166030800c00281c480005079980e0b80c4d8500c640042940040381481d140c40d00724819100c50384540040240b0600f0544c030b0601c2c1901d0080d181c1003540280d0307503040403681c1c1100c24040321b400304120102903151340b4000c2c0a805800030b403403040c580c4411401503003440d200700c0d070301034043c0950301050704040d00070f508540310442000750621008000d914 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 649983893 1250 649982643 649982651
    0x260907030609060b09070c0506010509010617040224250515071101090308040b0a1a060c0c0604081f0c02100c0215012606010305030405010c08120429060a05040c0201 73
    0x165640c9013104107005811b03d41360401c014405203080d17130608205a00a0b48200b07401401044540c4e04880d02e01921007a01d14000b02503a03030b91000458081e1400546000c0496440040300c840240784000c1080c08810083c4000e00d00041c80c4012442400920043c2160098080341c1c3d494018601c0054006100c1c2c01d14090720285200942d0031240c48050030341c0050000c4042c00188000c05081d190070081c1031030140180d007035400b0000c0b400030500100d9406194000b454115485091100b5500c5200003031015544030b6484004581e14040034043c01a801191080303481e83c50560300c2804955229900506200d1840110100041c805410780c0400c1d8080d00300d03d180601d20420b23007030f4041d2480081d10701111303010200d1074150b2400030b88600d03925400300c401400440c1c0004160303800c850003441e01c0c0103640c01074607106c001406810403800d40041e05a041c4030820089061250140091322400e4085c0651851b032014400300548240d6000b039a1400e0030701c0a41000d03040400c000c030403800041 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 649985143 1250 649983893 649983911
    0x2003010b3009060f09011a01080901090209042d0c05090c07060f060f0f0506040e1b030114040c0e010c030c0516060c1a0907090905070e010626090703060906 69
    0x401140100c0e0b6001842c0c100300c04100021036260b90458000294800070400c51840c088030880003500500345034107110f400f0000a844043c00d402c40b50401da80070308562042c0c1821701c1e1180003540000e0580d090920030036000803c0200d248110210b00f5040217031007000e00c0ca82020b003c000300703001c5d042c1001d00c4020010346001c06d406e80545403165408140009805160040007962002c55400c00c41c1340c01c210800030410f5540c0d1005503000d032641c8c0c01e840c003c5610707241c9105e10000808504100c0b041404000021048072001e0141c0d42c41c6403d82c0c05205000c00c15404941900e00320f08001c1c0403c2c0c0c12802c5101080c4100c6c08004440d2140c01141c60b1000d2014001070360894960020001035480300400041018411801814815090358200103080048901d900e40d10310b030203625402d82c3d072001c0810902404106c1000140000d840142d2a540c50301001001c01c102d070040024030000e00c0c0400d0483c01a880306070751241401c2c0b0041c02c00c5c541140c0e907039001382c40030a9080e6101a1100020 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 649986393 1250 649985143 649985227
    0x51908040b031902121b0a050f030a02040302040e070f0b0316050a14160c051002070e2203032f0d0f0e0d05040e0903030601020d051605010f2003010b 66
    0xf051190740d0743c05441c01c141b9041113071145009140b280398070ba151040c44a4244140c0100035103d40b480c10340507240d10703903564140c2d644c0203000b42c0d070000c0e51143c20009080789400d404105401650102003860324440e0301e680c0c100c0202c0c402a1035aa09010000010480341b61103a40603000401d02494550420000340d02e240400d600900c41c4c401705000c0300f031001c80401844100000043c0000c1d13803140c0c0c0610170210080c0d120315591040500d140d003e9400120550414084061030702400300c40400c10f8002c904009004052580d0381e840070004850807031064070000c0c02004a144150307001d05250522004810000c0e1982000200080d921000420800c0d41c09200521b04c020107660307100e8a9500d85002c0b0380c00320741c014000c045503030010418000c0c45e9074081b90102c8401c009081903980d80d0507031034040000410341d2070701078030a5113050401d103072041054008450403148440841c402a00f01c0040f40e259110031320405e45051404c000100709141e120130030f01b48180007980340c0344140c2e45030420 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 649987643 1250 649986393 649986397
    0xa030f05130f05120a12080414010c1d0607020d0318090906230123061b0601080c0604081f090b04060c02070f0b030402010810081207051908040b031902 67
    0x2c02642c5000d000c000384080d013441807074840301000100040c2070741c04540e02c8003824400b010b078100d002c0140c074000050500513040480801c2003440e034002c000107a0003002c01403192005110b094150031200000c0316540c0742810540e10390b01c1c0c00400200e00d025941d6400e603078034104103411071802049084000b0f2111500e2085020250080b00c01258002003011405407030017811010340c640b01d44420050002010340c640d801040e55000801a41c1130300390a000581c24064101e000c1410880c0c40c800c030b40c0307402010500f00e0403206e18008903019404028100412805135025807025940201303091000c02034101d40c035695003a584000040c1488080d110300980d2102200c05540781c94403842c54000302641084041e008010160780768a81c1c030b00f0000060803510028001038100702c29080401c0a21074142540001042218111541c80740c003860f810780c09420044054405000d4418011903c02c1e01d05079601c480c50344000e80f50b02c7c182c00c1100c0d41c3c6640c1c0010f46040304043e030203070040f40da11482d480 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 649988893 1250 649987643 649987649
    0x709081002180108010b0403030c08120117120408150a140727030c05011110060807090614060703180b040608010302040518060601050c0f0706090f06030e0a030f0513 73
    0x50096542d1a40c4400701d0991102d00c072410f8100310351030004004c803001340300681c1c0a0781d516180046504803581840c4c900d070300600d40c6101061085000000c0c036540800d00044503200e02200f03941101d41101c15451980c041e034818044944c002a0b402c0c100300600301981988158907807030001daa600050742c0009102000c541d00c6000c03034902ca105141d25508503840706a8900841c40084410b400d6696460340c15100b40b003464184800b84483d40d907001d4091110341081741803088200b040d07540d00c081a035a40c0e00e0750f12684076254600140440c0c403d0050507000f540031b01c043c280d546049442d550840d1a00c00c1400d040003d070030442d001248018041c1d000304000c0c0159035801e03560b941140104411610003415680c062120310074a044140d201080041e4001070900b095601c0700e40d6582c60b2030801c024103c0604050161030f90119141c0e42252009040d50092903810003110b403184420342c110f41180c0d1039030f02280c4c000550300b00041d208030b488014684803854464107000c2000b021070521132040e0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 649990143 1250 649988893 649988923
    0x30203010608090c100e06070203101b08040203120903071a300118060803070b07030b010c050c09071713030f03090201080f04141504030311041508070908 68
    0x40108030080e4080d01d002d801018003c06052075050f01000141e8984014201c0c40a00c40094507030240355580e031003625002e54015007500c4001030900c0007107000344074892054541c1c800e2501214079140c882c02c1e51030310499008e070003050340006800e1900525000780c460964984965075010420340d841c9a031000003600c03119442500c5540e501c0040100703511181d41c80200502e104a040c125080c407150701c40c111810000084090856034001d880600841c0e044080244400655581007140030035665200d0181c0365000c0044900071001181c001111020103803599001d200c00c400c0720718002d00c1c2c0035048106800c104d81c5580152600c02e003102ea080301c1c00750041000000c00410b068010101001c14081482c0400882d11243d0010b0000c0201074811f002d000004030004041080d01d11107080c0321141241201c4110b0b5030a000d20740180000c46003100003d040c044c03d40d520b02500d01c02e0350281d0b42005044440401141000c5541c0280105100c080020300c280001d4400001c1c800d00e40700ea0809 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 649991393 1250 649990143 649990147
    0x17060103170f160b01120809091801090c03020405090706080412050d090f0501110306280815010f08060c07060e1e250302010e060f0708181f05220f060302 68
    0x15040511309480140e01c0003007101c100c00c68403c0000c07a40d9040b62814401114041c03a80c0c0c60300c41c84a8031100440c00844450b600e4400807400f481505082d000459100721402e00481e960140d810791110300c0d91143d0808161031601180020300000c1410300c064849140c01400c045c81c5205402c00d892a42906032500b03154190100c0a208080c00341c15860f407000e034042459401d104012807a981080c003200c0d000800000c600c507500c008940180c3c8010488002100c81100d42d0210840d440442840f4649056101040001c3c05500100e0780d213104890341360200d810804c2544414025000e4030301f0b41d404d640183c116541c0003c00c0f401030801041e010400504c1303015849040050304c42c1c0050f10420000c040c3c13070401c10051303034030150b0608404010b0342c66607115103400303141c40b16074000c0742801040d1540200d9408000700d00c6107d00d0301c1ca0310701110360240c181c40500094087c0249030710f0300340024030304006005103101e103401c607420b8858040c42c0329070409541d0340f03030700452940d680c011000007900 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 649992643 1250 649991393 649991437
    0x1050a0e04051501260c070507030c090606120504020a05010c020d0c090c0e010305090307030c0302120c0a02011409090c09030a02040e0a05010507020d120c0e10080106020717060103170f 82
    0x80960105880c0105d41035002c0c00511402c002c006900d001400445103103070018400003080014041e03074000315486400c0762051526189820081d202c2030284900140005002e040308048030f0107420f0065801418500c0824200030045400c402690000d0360090700c1c00c0c0c5040c0c0069005c02e01800103001c000c0000501f0524160000c200881c910780403410141080c01b848041c0b04003004031422903515003444090794281e0b00e0244c3c10044007499001d001400407030301e20780b408804038644006074400d81c2e40a440070260304842559001d480c0d030030764101001c0310000b0a0170700c030b40005250208004007201c100761401d60001b81925101e5420140503008144450f041210901400340c114119001501d00800d100000034004a144040d881159856620751582e540c080c01502c1c0c1c3d100009041c0500c0d80b0090b94003e06121404e10610005100e001d400003002840c20400c4010300900300c2c050003c1da40785440d075414204004030292405081001081040d0603090f0081201c0c460740c00076400791080f = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 649993893 1250 649992643 649992647
    0xd0606031b0e0a050907080f240c03240a0609090507140703030507170a020c070b030c0f07020f090906040303180206030a090f2a08030a0e01050a0e04051501 69
    0x700d0315080710070064401e001071100011030380300b03142d20000c05a8001038540c2c81d020040c0c034004080e40185180d01850103000344d401000b00b000302c02d030740c07507040e001178080c0c0e0280c0302100318030080382c41035020882400400c50942c20b40d55000b01060032078051040d0764400750006104012070790f2244010400002c0e04010820007070198640c418220309244001440900d48681f0900c551940241056510340024442c03a0280c4c0c0c2182c0540d282e4841d035406440d050701440300a40c407a0822001911481400044240554040b00e124860102d00c50b800c10003241001d50154000722030890780006000d911340f60300d480e145071142c490140c0310003d243d2810035040c081c044404a07803892400d80089036448000d0b807038a40441e078016180081c0000c00a440d410261400100e0706c90080022501400c804200d14401d5000c07403091a1410995101650710000e0a03900d2086d104c80001042d4203d07a507003400d60054020384414101410034880100d443c200040844030300301c1c3d460102c04907140418289503 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 649995143 1250 649993893 649993913
    0x8100b03033108162102010c0b0901060312110c0a0302010f120212040c15180e04111008090106120b0705032706040b1e0105041a0d0c0503150708010504020d0b0d060603 74
    0x74841c01d45c10040b800701e640000f810207066010150000c0005000700d6001e003005d5015500850f0040454101000c0c0444001c4c0031b40703032806406e1a503205280168045142031801c9c0012241c3c1611031002c00e60a0401c181c6400c0900c070760040e1000c0d030034010005d446a4140e0114485d520078080350840d0ba0406042240101c0d6030482c4000f042150a0011404d405410280050b24130100c6401a40c0d5030301e250039640408039031801c0f6008044c04244507146608502d1150040c07070044024445c46460f455545c0d03145c240b00c0c0011b09480c4050000ca010180600c001795040448011040710078040b01c1204404000c40d201201a1603001808110500c6808160603070000000013400b142d91010b441d10b80300001c818050030b40f1441da01d14842070000f0700e0100031903808601505650f40400141070120701c8580b180300b0f05000740900d41e0394603605003084170b0080c801c43e4182c0742c40e00c2c140d0130031003440000d40284030840a240e54031201d101807a6240401d080c22140b00344070108200e4250315180e8404 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 649996393 1250 649995143 649995179
    0x80408010e0d080105011b1e06050108030c0a02060c0a0209040b041719030c02010b121014090a0f030e04020f2a030f0306061308100b0303310816 64
    0x1d038020ba045501074540c003c0245045950900e03010f0818100003e40c400b10903507400d401400f10103c170301d40c0c0011180b10f000309440b40303010300b42c1045140c1c0d0381c0c010241c0b01d10400c148401d907500081000001450881c01514882c250b14003181e4090029501061107030700141d609071703000350381c2100300403c0105403075007100b2070702441440c1414000c00c42c0c42d420003101112994000e0544903500c0c3c0d40894401d5100305141400103002c2c6e20034803c02a04a5210f41441410700807050400405240c0d0070560419075006144a200420300501c05484584c0e9901164508500304441c1514080b21965540080c0290150402d02155141c032918240c4551880c02200c00701500100031050140c80c0c80401030325080440350084030381e640c2e2090006099403240c1c45074000c1c1c80301c002c81f010500780000210b200d083c40702d00d90200b0021000000b0144e0700c0c0108090328440d01510402400c003200514410300804402d0503806005c240c85c2ca107601d05110300d010441d581a6038a0f04100b01c454184004101c0d5 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 649997643 1250 649996393 649996421
    0xf030c0c031903030e10110702120a0218130501050f06012007060f090b0d0b10051e09040b10080610080c04300303150b0306030c280308040801 63
    0x1d00c901e602c82c07580014003000050107043e500c2e01c1c075007010f0000380152a41010585d03410130071035154070703a001030517001100b040e4040c0c0780180c081d521600b07002449401103600207008180c0d5004402c4401559007004015031448040107001707800080003402014003803113030100300301c089141107000148030101001c64402c401d020901146a071304004240c02069941d6440c28450034200440207503054000d6500111184000261540ca0300541c0d900070401a82c080302c3d0b548446240c200e088816005948010034001e440c06900da44080c09074009080c4100c3c05400800c41610400c0040e0041c108203103d000800d070540104101403824105490001e000c3c2d04107040c0e41c3c20241c004100d82d0156015031040c081c80100c0c941d41d60000d4601140f203000000c80c000c58000300e1450018041e12246954603031400b2048400325050100e0002d80344911070180007051810f00240800611100420320114050ba00f11041410703c9160008400514003a00c0e0030740c0c0d030300d20f884202421035a400c000406 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 649998893 1250 649997643 649997653
    0x50a0218031915271103030f040905060d061b091203020a0210090e0405070807060e0d170f0d05010e0a14011a1908070e1903080304140f030c0c03 64
    0xa605000c014020381d80c0c64002d0000b200c072080b080e48900040000f404182510242d2504c0704901e0760003c9610f081c0d0502c62201100380c48241c030180340d0703240504051206013a909100901070f40071941e001962064000341004104030f03031078a0703080448589072a80c0c5200d0880e40040c040b000d40084610008180031540310b2843d0f60315444c025140d58410800910640200c144884514441c000d0704015041540c1101c805060030718080c2d0741d416040c45084114015020001801801620318600454000e0f0a01c2415a4996941140c0406e074a05a8404e1601442407540c0c41200cad8000d010303250040280000d1a504240f503410b66848010400c1060300c0c10102d0000300ca5240e010128112003c403444906032078404910100c55010303442007840a1614030400c041440d9024103224003501c02070f1601c594103200c40060003888003602202c400e250383c20744810000189007000840d07125006440400c003e907455a42c040c1000541c404641e19a0720102c1e000c842d0714828424900c0141049000300 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 650000000 1107 649998893 649998913
    0x7080f0301082401061b1b030308011406090607031202030a0c080901060305070612020c01060e010f0e15012a0b0108010f1e1e050a021803 61
    0x3a81480b511002d400c52003072000c940703d10200f1002c001c0300c0f144c1c208503080e901c00015000c10510b06020b02c000401052003040704c1200e04900a001001072440c6041c014036006045c2c221160604105070b900c001c070b503a48400c075001c2d500d041d9000f80c1c880000d170030300743c03000000131301140034242c000000c1020900aa0340814a04003580d1a2401c860701c0f08030f8201d0885146020052840d03110324001e0010754010040e91100107100d400251070004240c51190070341d5180d40c800e18000d00004010311040360780c20107c00c0604480c0d8200b030103a14040383c443e8010425541d429045c0700c00c0d40740c003000581d00100d40034174000500d8512030341601e8901d002c4581450034400d02001d54640781c4c124014140074040c20102c8052100031100294103a400c400003003049074101d2200031840f41480d4654a07907401428410f1551460060300e44640003618100f101c1c030300e407100e4401e4020383c1c085 = true := by decide +kernel

theorem cover : BRFrame.Cov 649820143 650000000 := by
  have h0 := BRFrame.cov_init 649820143
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649820143 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649820143 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649820143 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649820143 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649820143 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649820143 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649820143 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649820143 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649820143 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649820143 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649820143 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649820143 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649820143 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649820143 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649820143 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649820143 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649820143 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649820143 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649820143 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649820143 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649820143 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649820143 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649820143 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649820143 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649820143 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649820143 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649820143 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649820143 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649820143 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649820143 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649820143 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649820143 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649820143 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649820143 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649820143 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649820143 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649820143 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649820143 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649820143 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649820143 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649820143 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649820143 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649820143 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649820143 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649820143 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649820143 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649820143 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649820143 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649820143 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649820143 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649820143 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649820143 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649820143 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649820143 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649820143 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649820143 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649820143 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649820143 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649820143 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649820143 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649820143 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649820143 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649820143 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649820143 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649820143 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649820143 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649820143 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649820143 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649820143 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649820143 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649820143 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649820143 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649820143 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649820143 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649820143 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649820143 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649820143 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649820143 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649820143 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649820143 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649820143 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649820143 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649820143 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649820143 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649820143 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649820143 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649820143 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649820143 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649820143 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649820143 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649820143 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649820143 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649820143 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649820143 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649820143 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649820143 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649820143 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649820143 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649820143 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649820143 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649820143 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649820143 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649820143 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649820143 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649820143 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649820143 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649820143 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649820143 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649820143 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649820143 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649820143 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649820143 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649820143 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649820143 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649820143 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649820143 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649820143 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649820143 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649820143 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649820143 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649820143 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649820143 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649820143 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649820143 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649820143 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649820143 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649820143 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649820143 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649820143 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649820143 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649820143 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649820143 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649820143 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649820143 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649820143 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649820143 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649820143 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649820143 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649820143 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649820143 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649820143 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649820143 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649820143 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 649820143 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 649820143 ≤ n) (h2 : n < 650000000) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
