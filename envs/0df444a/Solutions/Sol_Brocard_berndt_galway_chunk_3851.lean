-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3851
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:52:10.233715+00:00
-- url     : https://prove2.me/submissions/1a0610e1-306c-4a48-845b-162bd04d3fc5

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 692446043 ≤ n < 692625899 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 692447293 1250 692446043 692446067
    0x180306050402120f0726010c0206060405060105091c08090607050d0305071b33050a0c0519030b0f04090b18011b08040510090305130602060705040b03040c03050d 71
    0x940504540741030804603865a15000e462070b03480c0c012010420102e01860101c1c1386c0c00340304041c0c02e4408951310841c6821281f2011481025810817003c2040c10b140510556611070020300341107203010003050001c1c80b0511040524020241c402800d407084c00749400981d04151800707450241d441c00c0301c0c10055914181c40c0d41c440000390815002500041c032900c001e41d10500071000540c24010a603440380c20f02c0040c6001d01c0e07040112071040085416000c10f90058082d0310490000b65070030310a00c1681550752407045002408001c2040e080e1503841c0341d0421000320803510300040d03007009203400122a2015410303595070140c01c1c1409035040c4151084454007540101d0b019802c0007140c403203e5070030b0707800040101e111400741c0401e1400e21402450340541c132070b05c540d00303454100203100d0b1184112a5801c20650011320085440b103540303e9100c00c040060000c03400100303001c0c07074501d1000703000d0701c614083c0d20354908000c004a400c001c144425940696440410760f080f04402c0d031002807a03002d0511b = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 692448543 1250 692447293 692447299
    0x7062c0d0b0f06060f0304060b0409020a15090801150621021207080a090309090f150803030603060c0c0a06091e081306050c0a02011b0804150f05090a15180306050402 73
    0x2c80810303558645032048408140c0d42c100140d045580d2915560028268035141c69002030700c81c0442c50051340d4580125000e04880742c207541007a2000b48000f07080a02e250402c0803143e242c2103c0c41042e148045c003a07030032150700f80b41803a80d40310703556542403d21500e51440603001d400810380302a4079800b8010a403141c002c9070341e038a4071030740c0e450000d80c01e0760b010710806004200303c07000501030011160002ea844440800700410301404d030b0880802199042e50014032260404828011a8501401916009034407488031034104041810056110040f06030b00808030f90b6203040807800c05c07920008820000101c00356942103001e560a1281d4107030311140685880111548021600314018070980c0c0429210034001c103d19a1160300540b01c00403502110050b00940300303200000218414000c00180012148002c0d01072110407000c2e00d14006003540009000c0144842d055030b489209180c0c04441610441044d98203850a043d10b00a00030180004079803400080402030080a80001c2d008900c2070b = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 692449793 1250 692448543 692448571
    0xc010b040b041e05180a0b15010c0b130f08030a0603050d0c051506030c0d030509030c0d03081b19031d030301030206041403120a0206041407062c0d0b 66
    0x81c20401250b0600456004200c0e40d05154200b204550380f105038000341401040400c1034a50040780e242401154049a0300c0c000d42040142100c00c8803d060001507017820200390306583c1d5903807035907144401400c00c1d8a82000d181c0403003d0185080f025000e10780c0114020383d032418041d400d0006402c0f6400262154410344859429841c0300310070601d8076a8000d8081c0001c0060a01a482c000038084d000036854454860051081c2c4c1d41c0d9800d003082e041c4691580d582e02c04458041c103041c2140c3c0030200744254913843c0444040b94001c403505034082c103c020500c4000551181d40001401144149081c038040c11244202c265019400040c00074a6140e021440e00711a02566589c0d01c024000203400400c180000c00c14600707801260350a0041c010166401280c540c81800002e400000104d00164041d00510003401508104180c03544a00c1c2c000e40b000900307020014018000034414100700c2882c4003908a07850f0b080b50f80302c0c0640280148074100201c000e06018810030000d46800403880c440c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 692451043 1250 692449793 692449811
    0x309051c0210021602040c0804031211030f0702010603140307020301050108010e1218041415090106050f1e040609150c050d0e0d1704090c080c04141201020c010b04 72
    0x14000e010045095640c0141180440501c0c100081c0d00915005040003900c0510403005075682d0081c0ca030f03242801d40da030945174989800c0c002c050f00300c46118002c0d001c1c80c0100f04c100c1340b4001800c50380d005500f070f0003009440d15240000c0307006040c50750000d40100000710400040d00ca01000512a160007200240314990321480a40d08984040015610702d41c440100000c80b119210007824030f00c2c52103400807c8481c40304002c1002d0350300c3d07688100f1a51f4004410009410140c0c14509032600c0c060380c140480e98140000513001d4403650200340e400b084003041000d141d41e410151501d4181a8a410303c3d203450740d914000d4841801802401c0700341041d00b103000c1d065840340380c00c0254150032034010080f110088505841c407800c02c25515422408013200903011490680381901a50b650b401c0e01d650799803a080b4114104c4804440301000c01c01d105050005000301ca0b8103a4090729a0103001295070096200091403c14950200d1403003940041070195480d007040d44184500e101c04d450038004151 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 692452293 1250 692451043 692451073
    0x111030603160807060e120609030d110903060a0209060412140d0f3c0216050a050d080a05160311010c0801180b0307180e10090807080d1803030905 65
    0x406004400c000d0b44220410401c0910850b80d00381450340203410101c001d1f040d501a14105030080ba07044d49a9840002c1821400085100b6404000d5440c08030900341a44030000036120f40340070b800d40b2409600420041000d0351100100d42c0200100707843d420104442e490402120450080000c0c4107000d112001e95030715010b0000400d0f42c40d81c03a50340d81c5c80b016041000e50150400000980040b2941c446071408512840070307982d00724244c40e00245042e9001100903202e41500350802c500a1004100802a80d00e400700740c4144117a0081e5801d4446801403c11681802048031500f030003032052120f00d041c03540004040e001c1541d0790000b80a040742010098900142c00e10a200b10805005581091032455600600c6d0301c1c84020140c541d1030780c0e00c000800003400c0f0b004800e07101c556034291030034000504025020380070796018002d006c0e10300039840e4030b00140035401d0003400201c400125228031148070f52208025009070901d1803e9042c89050060003000c4401048401d4030403034003004075440c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 692453543 1250 692452293 692452333
    0x1209240a0e070b071b031e050f0106060f0509031606080103060e030a0c020d03031407030213050d02030d1116030b040201020f06040b010918020306090f06150d0b070e030111030603 79
    0x241004401c0b80303000030341d070b94101913122417203203100c4401646080400084c49035000440b4100c0a03442d050042e05a170300301142001039850100003268075102c1c0c20000aa040b0580340c2c0c1061440c24020f40b180000800303e0705203024800c640c20350340f140a0001c220940c01c01400c0341a1303030003284108000146120065a60321030700660341c2c00708410060a07001813030f08024686095110349808a0904810030460100250544828010940118042c0242d02ea42ca43c170b0130081c8402c4804031100350143c1c0119440c3d0f040c070782e0007204010000d650640c0304201040300d000a00303902000d0000c416642d041ca4481c40300280e604038010b0052007510721403400300151050040790041041c0103030b41d1a0104d500000d20501900c4030012200081e1007015036014407036648608507550103040c28009070703540c0d2401d2247c0200070800d26151480b0811040e1a155404440a6032202e0b800081e500d0360b503c10f50b58010a0511150705600701803884103a06102000383d40549002e41c1150364400a24100d080b000d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 692454793 1250 692453543 692453549
    0x6080706110312090c090f18070b03062b030e10020102030708011e0b070c03020108010e0721020408160302010923040906022101060813081209240a0e07 67
    0x5980180090b05120301e903800c1c3d01d6013221055080f510345100c0f200110f560a0800c40d81c201402d480502000240d06a02d112442d03400380d4100500b00142c1421114412404040e200e940120740f204140c6050240d402c407646400b081035415071442001e1460000c4c0221690140c0a002c0c28401c01645806070050090f01c0c020b00315038861280326820a0b05448003000708004882030400c1c86000000c45d100060014400c090055080c0031200b802d600001d09244410f81c000d81e0b8011903c4200820a541701024880c00404c0303004040c045000f01031502c020380165045100f5034003846901d07072b44903c0c07030b5254001202d20030b8880354165582d5400d0358060b180d03040b500c0b00030402c5000010341a841e00d940304052a0344104001400c010360036801068048580d0440c008a0200308010b0020a4100380301030740c4451803002e00c41c41c03200c1c80e59600780c00d03010301c062003181d40c0a00d41c00708000b04401d000d078400c00080f003100b1f070001c08082d41004072140340030b072038840043e40350100011040d2004a554000c2d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 692456043 1250 692454793 692454827
    0x110d02070308090f12034b041a0c06010806010803031f030c0603020d0506010e0d02011b061b1e120c09090510050f0409080304121e08010806060d051b041d0106080706 73
    0x490130050091f04180080c46c4c03070001e92080c0030400403d992101c800500e10f242d003042e00c00e5445071150b04595241c104180c101060030341c0607800400010750000b08a0360300400342481c401083c1d400f0940f01d000c0c0403d03500002c00c0d1075a0704102040c160703855400741c00e14a9000380180016105c1c240159604034540c08941d070003180518000c805540203154840c04803038420107881e5000c03026140e00d4103d8548007500b142c580c038006004031141ea803018440100c0c048600082030307001d8012002800c44000020f06082154036041203810940c00b58070507000815903640144898501001a200c045145000d820f108040032503108225003440d1280d41041d56001c100d02d03145803502d440309441c0396902c0a0001c2005880407400051030302c500d0b07001c454011692111491035051104050500030000c0085002c1c00c0c03840400c81c00319600040441d203080c29100c456080070340110104024099140c044035072003080e40030b9800300d010b0540c071480840300314509440003180c5034541122001e10756050400e03 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 692457293 1250 692456043 692456137
    0x530060409080d0504030201020903060907120b130b0c0c0d0e0a26160311040e0a0204020d091a0f0c1c0b0609040516110d02070308090f1203 62
    0x141025407003068201c0c05440200c0c10807401c0403100d020b0301c404903801c500503500400c0a480d2800c0800c41203030410000d9000e4042981440c0c0e081b523410030810005880245040e01142c05514101250042d954001962045500e8941e240f041c0c0741e070101220708007d12038145221a107070f216061115041b0f10040001e40080c0c68507020b202d02803002180c0c1c0b00082c03105074003812080d5003080800d500c511184551940f252660a083c404507003913003822030046051036070300c04004201248490b207042d4100e40c01a2101c90f12003032076008020703074040100010f0300c0100c00501d0683c40c1401c00c0c80303850600c0241e811035440c03108141c03250107202074201d281d8055103911841c0e000c20340c001d010381d0007001d00040c1c100b451340b10000341038400907100b44a488580480e050303c0203038040403520000000d0f40040c800210500c0b4029541d000b54400608400c9002c200c02c8000c1e5150002d200c3c46070001451a80f040d03058402003070326a44042036041000705112281d1a00c6407414404061542c1444c803103007 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 692458543 1250 692457293 692457301
    0xa05120616021e010f050f0c070330051501020307020123070209160f030b010504121b08060f0a05061f110f01020405011403010803030402150d0204060530 68
    0x285003070008520440039030203500d090202e000810b195400816610380d0010409060f110001011200060205443c0300100c3d030400240c1c005a0302210002e99051400c042990749804414640c1200d130301d4082e034440c2810706111000074440c5c1140d8000c1000c50400742c0d16000420040e030b0b882c401c40200a0209a600c01c020b91511940031704031a06c18a603030710309450800f040d0300107061140101d4000b81103522010b5160070096000300c03622207400503400c04201d130700e100300b001800d94002d9104006c0d00b80c3c1d000d201350b010403a07944910300e1650041c040e400d101c81d0300c1719245c07030b240d210403290f03c00301e43c081c9030008806151600800b40135000182440024801001901045044a8840c1d00074004858a039280500c2c0400440d440c0c030329a01c00060710740c3d080100040c0700461302621a902168188018880c2c0d845c04011240c201d5412114a501070620764182d95031801000c09446041d4404540080c15a40201c010980e0203500340c030720304001d4202c1664000c4107180c80f8808440c456040009 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 692459793 1250 692458543 692458561
    0x1a01140a1403280c1d0a090e010608070e09060a1b0f021507020d021e030a210e0102130b1309150f0f030507170303070e0f031501050a051206 62
    0x85810450b0000040b002d8903e58500c410300c08401c459004510b95545500507072540c1c08520810070409012482c18564214000206828414050088000e40c1d521884c000a9025803110300101b020000740d503030050340c8951110104000300d906403228041e4200280480c401e602c200381e40c811039410100003950b04407400704c80000d4400b09410030341c80f48074032007039004081d90101d51168455a00900c0700c3c0d481101c0080c20075801c18aa140c0d40749200c203012101c0d10000c020b0301c0d8040040c0c5000461241410030b4a0150540402210f050350b00d0045042407144064004200100152028202aa590307100240043c070030400400752000540300b0074000c1c030780380760003860001d9041c16805200300d494200f44155845c0036405242c604040346400c0007044014810301c001000030803a40080003404030789568907440000e00440c10000408607003c0280c2d2240d02d82d0b002200084c0c100c6071a43e41d115062050b081080c019503110b0510030200007580d00e0030400d000824802c500240c003113612041d80b4 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 692461043 1250 692459793 692459797
    0xc03030f051c15080307080909061c050105062b060504020a0b0d1d03040501090b03040222201c0b0f150a0f090b090904151a01140a14 59
    0x403400422508120300c840c112840728480105041112002072200c81c0074001d1100070300e16902400c0713903420500100307011680c20300c2510f130114803d0b01c42303642c1651003400041c0c2056172159101030700f1407820184800d000e8150b1040e803140b881940c2c440c0c41c0c00302c079140000b03184036140440e640c0d51110003842400982d8680041e90410310143c41110541d89820048140d60046078040c54104e0752040b140311580c03141c1282c00038040800000d5450039081c8400203014440c075001c0d0743c0201c2000804a01107450300c112803100c010804a408103001c1306180c00d4000b81041801c50000c044180403a0343da01040c4504482c0b001844451100c040c220168140d0041d142c00b413002540504005502100740e05c4800c20400000e1006038601e94882c00c060700035005940d1040784804210311400140284802001100d001c4103040b0b6243c1e4441d5650310f495890400200200304046050102c0381c0020580745007690340c00c4d9426242c540b11000c0350f81c2c1c07000340c1e809203926000020f4502400d41c03000c05200740c0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 692462293 1250 692461043 692461067
    0xe0408090f03070b07021e0603010e0411090403030615021518100504060b0a080a0308011a130803030601020d0201020c07060c050a120c0c12020f0603090a0b040c031e0c0303 76
    0x1026451031014140002d04000701c0707901150764200c0c000b404170118541940c030308803d40c6400c00c6100c075044400020407414001401010701c004510300100c0d051008240c182c0c030120f007000f4083c140074a0300b807030014058034052080d50140605059200401c0e400840c3e41d0449100f401110340e155607405851161150004d46100000c2c010a541d00480074074a0040c1481980030300d00100c0c41a61a500780035842480d0382c8002000d801c04000300c070002c0e43c00140581120451100b4000c0e00030010100900b610030440400c2d185561140005240c4038040040e600c1420241c080d40c200c9003080340142d090744290340301c116554020380c00c14070450b07000e0030075190414003a02c101e170b040031303030a5941d1269800e1013036a90340401c2880e4440e9007004500d28029020305002c10980303403039074425404110041c0e148a000e910802001c000500500c0b0204440c00840c2e422001040240c24641425406c0c64000d000503142d44501808010743c20444010102c11140d1003403450102d40d20303540313044850a40c480 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 692463543 1250 692462293 692462299
    0xf1f0807140d0203090d0507050a030f1e0905150a1b08040b120105030d0302120a091e030c06051e070503100e0c0a020610060e0f04090b071d0306010e040809 69
    0x1e00040c101201100241c2102c0c081d00038016540d05000070420300c3d058074004c51078100501086846c00141001c26202d0215905007803542e07107440e13010001c3d00c0c042c039043c204070303403104004180c1080a0b038000722107001c9070001e403044c800035812540003010621035034202ca00820400030071038400014480729140d240b80180d940b24200754503085c005000303900400303210001001981c014005031a007400804480015820110715200e5800900d442d40c0c0300040c50150055a100d0411081c080c2ca030940b60038001e400c0500d90501460351802401c0fa10401030300340c401500d820000380c0310990800e055542990f00007410b80c203556801c081102c07584c0c402000511054410b0350001548a1b008070800d00030141510348030703100d0100c03110003450404010034411003070b41000310401400341c01442da00d0038072805584d124003481c60003000c54040e0922100041c5140090400c03c0380d04c9501c200c1c1d01154081440c0c04d40701802c11141016640c4000307009070b0b13901101078408900007030b000c5401070044060107 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 692464793 1250 692463543 692463557
    0x414010518040e0717030310060c051f27020603010329040305030711010b210a0818030d0905100c030215100f0608190e030d15050f1f0807 61
    0x121000c9070590f8611908100640e0051600388405501044403108038903800d001103003140b0304002c0000f800000c61182100303210b07a130000d0009001c0140840400850300904007108a0341c880945001022481c1245001115000b00544c4203c040d116064071150001c003402d0030740c0d0a50b21140a080c030810a4424481150390f8140348144000003440d108070b0081e00e5450f100d15201c200600354000c0c0c440d000030541d16109012185603174041e0300001c82401442c03140a181d082c00d4071a0f1419504010243c004400881c040c4191529540110480b400079025100c030000015416a00000c4601a107a1720520f49401048d04500ca0103600b10610f02a104590200d0020482c181e9503080c2900e108090404801041c000040c0c02c851000c028034032890300412501d0410200307241c4940400c811054a912402600b425040800a49413203080b202000c0002c2192821344100000d410302c5810b00540a240b44500385140c00c1d0000070b9041031021000e600c0403041242200c40b000c0040c0f00c8424401c1c4 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 692466043 1250 692464793 692464837
    0x1009020a0e180706030218040e0d0807031d1b01170109150521010e070e01030b041406160905010903080702090c1603020109062418091208060406060504140105 70
    0x1080102e03100900d04d03500c2c01a80e9850060640005940788130803135025a0400110700410b500c0003609880e00180f620f040020340c2c07030f480c80480c05002c010b9214803d9215815056a148001151520312a6a4010944c0c407503001c0e6001034410f200b01c030701c00381541e05c2c04038010401e82c6c00c03580190503860860406c2c51311954482c0006540701e051110888020700d0180031080316401c003440b5014500707c4100052440302d107000b0340d41400c100140002000d400c0c5010103d000c001d1003801c1110040324900c182c540a16014480740b011091040301980006c088100001c1d9030350081c021101640e80001c0c0251030030429800740403410801a03e107400390502000880c01340803058218041300c620a50010035000310034100842507554526401d200701d540d5002ca1a00300f544c419404c0d044030605100310012280c0b4200c1c032070091181e400040c0a540004000c40343c0c2c0b03680041c090b0704c0b410085808110700f94803444200c2d010300450040c150710b4504c018131102d0035030168015000d040b00c000d008801d2244 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 692467293 1250 692466043 692466091
    0x2060f0603070e0406020d0501081609150f03150507081302010e22021209070608070c0c030c15020610031e050307061a010f0c020a030303050402031c020f1009020a0e 73
    0x10044800313036500e46c0d000c00c103240d01c0c80450180b0740c018000701006000d81461a07a0001c04000d6510940000710f940c1d20710030b45121802159a0000e040c10f15800111603a242030a41c0c54410221100c42c03403e00d0000000c1900e40140d440f50300444803520b034844003011607401921084011210035074424400301d52034102001c122200403c2c1c040112015842d2010b1441071382e5501d102030f243c802281c015240500505034030030340d020b5000b503140c540762805c4041c5040c1060110b20036000a013030804c0142d40807500c0000888050383c18100c590032581035543c1e46621112100180c0001007000800326500c501c3c506160581e040b03158000c41c15030313203004480d503609022503c56008501141c074a5444490031980c0180300590182c006040c0f5504510b105e82c005840350a15000c001c0505950341c01140170340d00c04100c3c00034520152540900070380d03083e5001070354601c0e80c00e503001054404e142030561900c40e2406200c41c4554040d0459503914140040010440700050812504550a81d10340b05404 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 692468543 1250 692467293 692467319
    0x2c010f0c05060709090c080405280b0a091406070f21051003060b060403030801090f0f0e06150d080f090301020c071508150d2a0303181502060f060307 66
    0x12010303440d5091118a02864003046e0307614011200d007400000d01c104000b02c0c2000c11580754594184d100f08072b00d480a00f40921001101d504080d1411014004121000c00d1039440072941c0780c00b4251030540000002c0103255109400c4880c6c03800142901c2d03011441c18040c0721301c00295950822003094115034034450074100ca00032a0300050581c8503950400070301025109074003d00c141540d0440c6440d003162409401c01030f0611400f49065a21642102040d00d55840f030084440404004c0c82810f81c04564160341d281c00756560304465038601d003180b0305850950020714106910941050416404904034132161300001c0543e81c02d55020010007c2d414410b101c1e40002e0a071000055419018421004041c2000200041e260050030180e41490f5a90a1200001d4075888030b071009051904c409802002400034404500011005401004041e080460040400c980c0e0070303030106c1d503941ca41859114014620a103000340e0094001f0a85942402402c0c0b9446400038084446555841580204c4c1c0c1c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 692469793 1250 692468543 692468551
    0xd05090c1002060a15150f230711121906060e010803031006080103080706020304020307030b161233080706080a051005010207090b010905040501060f2c010f0c0506 72
    0x10303002181041035522040c81000300704e017078030f10011a40d1804c049130514402041c000c1102400480509090304a00c0b540d119840500580c4940482c00441d40030f03002d140c0c200c102d0480f51518030580049e031504000484020100d55000140030101460002c000e0101c0003000540c1d1540d11607801140200b03002031114000d041d0391000315500e01d40310019141a25007500400108424500100701141040054950f8140c00c44030050303483e01c807440024a400780c641d10040241c1600b42c208101025a00d9104d070740c0740402d864080c5500010404081121019000031a03000380403240c015103100d150044030034034202102c0e484500f607180ca4986107864100e40c00040040c04c500100860281c10b030280300e801c84000207005446505020010b074031040e180c040c0b808a03560b02c00038812641c4c400c20b60000209005802000b4658454000908040030003440c44085410a078048082e060480c2c1540b0400b0b100403030b4825640c080000445420f9102c1280c5000c015000101901040c0705112150007 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 692471043 1250 692469793 692469797
    0x102101b0c2306060109080c0d0206031f15022e0507110a060b0a05030a0201140306131107060b0613060c030c050f011a06120c0c03040e090a03140306060d05090c10 72
    0x43d914010000408984064000c164070350070111100e403446d2900c544004255504989181c0c407a17030341440d80d0000c2d241900c00450320340d4030104001140c080d84120322200d035032554240d0700700700041c1d40c0c2030a030307000ca98126001081c110750351401224581d07030189800114a150007480304032440a000e00e8184e44280540e481d0795205005829840c084e06000020107007034000d4100c000f45030300007a021a03d022000414142c0001c005001036949101480c80c5c000140c0d010000d0807070b910044601608000c4c1d00300d51040c5460210041440c2c220156668080714036480b5011500300f820446000b0b00e01030040b070501c03040244580000b131044c440081c0445515000003404c154402c2c103036800020f40c5030507900035003040014188010700c0800c46984540101c01940d45d031a02d82060f24550b2103654003030b000340310101040c00b0416002141031380d20140a0b5580301820900c15034005950300c42a01d1003540484108221801c000300c0d500000e90020110090711a800c0c00ca4011070003880c803401800f00 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 692472293 1250 692471043 692471053
    0x311030421030605030303270a0305040815131104090b040b04060b19260111031f0e1f180212090106031e0f060213050102101b0c23 58
    0x20400040800054400690345000e200441c6130002113526440050408000c03c602901442c0401c0007842c1007040440541040340d900e2451428024a15000380c0101d6880780602d40c0c81c0200d210380d034200e680c0540400c00019000307106642c2c0fa81080124801101c3e0001c1d2103038014408aa840d0180920490051001c0c285620741894010b04031907014407120b01c148044155100c00e80200d05104003592a82d0760504010801d203405c005083d07a05880904081d801c2c801c0003606140018041c50203600c46418821201c22171110f60400c024003030003598400301800380010140f140b48a200224140181200800161a10402c01d0038401d45003500100a400081e5000041c0f4142c03255a8081502070080040314256a00c604200000d406c01c00324030440d6107646000d1040d641c101c103162aa01400456444c82810010360f442003007807140501502940500d202c402030240071780b6900c404003260711012181028800d5442651140c070a807410a05d940e45414905030381c0e480882c1c0581c240d40141 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 692473543 1250 692472293 692472323
    0x1403041b0617071706060c03040b0d09030f0207030302030f09130614100305011a0703022503020a150905151204050c09160f050706141603050c0a020c0d0303110304 72
    0x4907040c802420f030f54104005110000d0000c003007003c2c840e802400840707410756140384580308240b41d4000c94104d608913210000343e002444101760f1010380242e10940703880d0410300b116a4282c1e221046888080c015030000c0082d440c1200307440c8014007101c4401080c00080000c00301c02082140e0582d00488400405124a80b00c0d6151114040b42c19002d00e190074000c0b90305213400b0740412504041c80410b640b0000c01c120003014024046810b003040c030100281d04134070f00d60f81c1131130600d4410300c8143c0c00307070841650114840c3d00d8803840e6041c00c0e0503a101da034100740c90705013440720460b03d11804111458081c00780d80c00038128110880c0c01036024100a103040e20b06201081104180506400c000075000056041c1c86ca4000000301000109410541c1e2074032140e04081c4081c1219509802100100504010110002c80103058805660f40d07001c1006680700c00141806105802e020310142c0e1064002e15410715002507100281c520921380441c042030400c620011a400a80b0101d41ca40100ca07910 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 692474793 1250 692473543 692473577
    0x1603050402041d0a060509030405010207031e0f0b01060305180d0806060c150610020309150d20070b150f120a170a030f02090d02040e120c0d08010f061403041b06 71
    0x46c60304292403101851800b4a0000042d40e9107100d44001003201002a106580d4401c10a0b09014211340103840d003105981103180150710340100b406180c0109107402d0126242e03564001ea403225990361640100040e0118400940300100003c1040d9400360080000c0183c100041c090002d0304920025000c00368185202000306070307903041c2c06200441d4000c0c0501c505603510000b400e0b10a981c075120703842c1c2c0d90102c01e00c001e014100c0d030f0020101c0d04600c0e04050a10100e100f005118040c0900344070040c60b00c841007070740d4112a40d010466404000b1415004491030700d486040c2203900c0e80c408888444986d41c1d211546420110108081c2007008543c0342501030f010b0282c504e5034400341d1411131404c400c3c6000240c600d0210343c40070340600c1c0d903080345c440340710020028500e10b00e4003410f074030380c0f10008824210ba4030207003c80c8400c0000da9540000408803540400401901d11940361040c00c4e030365281009440390002041a12980303d1985503103059181d04000501604030740d80c8400c80c40c04040c0b02 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 692476043 1250 692474793 692474801
    0x30213060302040e100612050a08030a061a0319050c030a0e1e0c0310021215040902040603080a0905040902060301090c05072103230114030f1608010509061603050402041d0a06 77
    0xb011360007105030140c7e140011404100040d4495000381980d82b40e8070780500c0080100302c29040f082000d060303000000541d901800146109002c601754052440d1182103640d0140d80d0300381d8005803404800d00c04108456050341190340c03095480c8003104d01c1801e004218440707268002c284010706030004501004030f03040034081010703038010b989000d51501c4502a011440000c0c01089080845d40c01d00000c452992541c100014840c4c0003003007400305648078240324204d603120302030f245c0119000140004460030240968031866400426841c2140e10346010300c80030300741c110006e10030420200102c0001450340349200001e940c1d034851b0700304820100320018044a0b24028510f400070410015000e0500d480609136054900198034017007405118000320380340c5200450445042c0c05081104002144821481d0085401c0800244402d4444064060b1600c0c815600484100b000c4c0b141ea0403014000d4000940083c40584005020070b0001c8405510b40c0c2420640303403903030700071021200520040780a = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 692477293 1250 692476043 692476049
    0x14041202040c14070f02011707030b0310060b07020f0a0b070302070503010b0f2101020c0106081f0c091a040b0705030c0c0913020409060b30010501050604030213060302040e1006 78
    0x404420600c0f152110700303514002c0f04c40c002d1403074010b0001c0c1c03000c40e481100b0b4041c1d059035500100f4040c1c00c0503400980071f801c08007141d500a01c81c2c051070f1a4000c0c528025a01150320551180c1e2425416809024041030300001098106026800001c0d1114004000b04280c9000783d0241030810705140800d404d4401c841040c610414442402101d2030b40e0701c4090880039030800d08200112114894154064043c00d060344029529055001501400100d84040c2914603040c030800032903800d861003000c882d21110024002000f00c6002e01085014080d070300e00c1d2060310202142060780e07030307040c9040d99405240102e4117500b0204071010111020040031b08c1c5500c0031038051040c1d00e401c2d01c00d680a0841000080d20135134554041005004003a401800381c1c000207002202d06400200020103104010322105c1003104103d044410007560612401e810b807034000b40914641850340d002c0041e00760890385811006940c8035070000040e59144070b160580c100c48006081c0050b404602c0400b00c0300c00354 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 692478543 1250 692477293 692477297
    0xa060c090b0a030506040b300d0807080403021603061a0301090b0a021605060429090a060f0b09070315060507170313080f18040207020f1014041202040c 67
    0x200512074640c900781a101ca070780341840c00003810740d41c40b070019000d4031940e108113800460804082e1a44000e515403202c0c2c141c0d003480c140c00e066040c204065a41d07000803490000007105103000c0703107a9a114011942d0018003070b00c1102d10204080d1a000000078859100300d035050b80c5c3d42900711403001307113064010f05240100e0081041c5280740e02c4201071981e005110000440e800204050000608003200c0c0016030058110761042c41e0a01c0c003000c041c2102c1c000e0070300e41d100000c12000d8608454481e5480313040c11502514082605030f6031390010307000c03105d000001c00307840d8080d000c89503c1c4d000c0f600340704080d41e64020403d441c00018802202c401ca4004a040003010001c580226201c0d04080042e41c50720411140d480e9500b91803d074a45a076104020b020007400506a142c581940000d0003d03009003807090310052041c0d0702040224458010000d422820107031101180d881d03c2c1c1c9011244c002d80e400d0408101c0080094850103074072503040401c1c0c54825440850541c1407511802884020038 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 692479793 1250 692478543 692478557
    0x601030509030a08010302130e1f051006090b2113030306050a0302150f0903060411030601140108190f0e1605311d030c12043f050a060c 60
    0x18030001c2003131905001c081e0041c03400b6840d103150998150302c021040c0402005854910b000d002142c0703031002550070480395003070520020500c410343d03401031282202c1c0542c650411952a10b08501c086420010740e900811071f8488050302040c3c00c900c0c090780310b01d000005881d80e000071803602904075865a00700a004070300c950802e00043c0c07602c1964015070501400400c3d15100d0540480342c0d10300c1200c00d05a050301555091000b0402c0d80c2254240c0440b044059800d13a03030300e4001929003448140e01d90350006a8002c0452070100410560030700c0d2001071140820007144218a1809880d007610601f4480c1e846400c00e024806107504200000d090211046202c40103452002210400d030030300790000103c084d44000703103141245d41c410b044500340401c2c01458103079814411616a003207117640c601e0328000c45511b0320f000c13105001141c041c2c0302c60300c040c2c00d10f180d020841d540b082c251000742036248444500e058880b200080000c101050300c240000c24400d4601d2520000395110450140240112 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 692481043 1250 692479793 692479807
    0x203010605090f030709110d20040509070e0916030f420603062108031518040501021c0501060e01030209010201141504140f150a0305070608060103050903 68
    0x881802c0b01c003101e00803a5054582d0052a00190400c03425a1000c107a040c901030303002010721040d201038400c4131188242080070103a0b01c841010340050207041c480c95000b04000502041c64031007038264100040d8a060441034034a0000b0518884003680c4065400461800030024a40e15000d074203440c1542403400c1c82101e801c0d071036000c217400503c2038001d480e01004044010103480f00119421640710b5074856109642e9441e80a4010441740c0101c658110b00c00e03a5000000055400e40d900180e40040b00a10390f9807001c0006145625120030707107511180c5092005100007002002070f020714040c400041c0e0302d140c4108030348402c100c041024500c0c5802c0400411496410403030140300844282800350340c0c0c910b8800102d00401d900055500341d034a40400740f0515a50a13201c16804120588040003100f090b41d00340100d101d0304488610306944140006152100c650500e0313602020064418041c2c83c0d201c1c0d80d2542001a2500900c000450740350070089c113580d1601800360400380030b0014602d0b1400b = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 692482293 1250 692481043 692481047
    0x81605160f02060708030a051e09120f09031014060306130f030e0306040510050a0b06031f0e0406020307030606090b070b0c1c090605010f2403020d1b1202030106 71
    0x200e10009800394807464071103419501c8910441c0c4040354000707500c079520700e020031904005020542e40601c2a0b464104c1402d0078181c51170311a40030710070304401820412000740410410b42d10140a10f120364005200c034000e513442c200100d80e941210810301103195202e2055092840c2e1000307004a12036440a01417080c000c400001c0c0310281504003091040b0503c4905060310052a6010b0540c0c061103003d01700424010b0218803c4205007086a0a00c20750301c07410707806401c4e40c000391003943d44080c3c1000410306452111000c5944803002c0f031100140c00d547d901c007030605403000300c030181c0350183c00000304800e1f140d0600c00c0d100074140da410805d85103070a2102c03200341070055441c02400c2820807400301e03c40b00c0794942030320703100c08850301d03c801c62000004502e4042c0140b130000329405070a040011801d601c661080d0403e40351410301b20309001c20b404098111071529111440203056081100790504880380c001e401203613151891903900703042c0740e05004140114100a602c40c240c814001441295 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 692483543 1250 692482293 692482327
    0x60f1d01051c0201030b100512072a15050403050d05060303270103060f0909050709111914210a0c0f030b060f0c0715030908040603020703030b03010606081605 70
    0x41c0c4000b140b15034092005034001c00715140441e5100503080000345800d948900240b41070104803003a2103a80d00d41c1c550a41d46c0d4504681a807500d00c021450460504480c014012144c90085010098619050350107008643c8240e0f0160001280090840700381c100c68040c103500040c003600194a084040b840c3d1000313050713504540d00c2002200d0f0045201e182c0c441d81150024182c42d40c2581146d580e03844082000702519001100d05000390f031340000715020350340320300c1002c042e5240c8058548081c40303510800000c58200201c0504c848820080e40d2940d075800a4034019450b81401c20101c1110380d1000705861000f045402d840d0f051260061410798402001c3c60b2031065418007007040340340c1d030002420318002d01a04058000000c15851400d0300000340c084216201e0300031182d10910341c83d100710261000b045018ac00440100010803e40748254003d2170700500901d40014803c000d040040d0a407440c5601c100b00082c81f00c02800042c041c441e2a110f001603060a00928184828078201ca0007 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 692484793 1250 692483543 692483569
    0x60316061211070c1814060603070302130f230907090b0306060c0f0a03030e0d082413090201090506090a0e06060c03040e0907090501031e0c09060f1d0105 68
    0x1d545524101000700c036442c00b0340b280f1681c891001c044194803242046105c2c00c180b9041c1410504100f243c181c1942e1446c0c0e03076809007170041c08503861552034107010744c003950000c1c6c01d502d20340d041c0d0903000a0102814241d500904042c070a0103051b410042e011120701c2110000161242c44418188038180790013000c1d1600304d41445003d6903c03503a68000203075040c015286003103080d01580094111004000c102130103070701d04c2a00e080018400229529650b0f0002c40313040c40c089906040032414024020b0300403604042020f1540e0300b0081184042a40070141100e00c000c0b040e120b09001b42150781000d401006030400351040740c1868015000107180e40507078801c00c00c0d14006080400c081f138407040d0440703901400c44411260345a544e00440e1150381000c686031b036800c2c0989400851480c44902480307040701e03004003842d10811b5840c00091003107030500c07034125140841c4440000c0c0700e460501035400240300c402c40a00d00d0754942039910080300000c80352014800300c4000140300d580e54000c08040c007 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 692486043 1250 692484793 692484827
    0xe1216090b060a03110904020409090c0801020a08041e210e060c0a03050d1103010f29070605100f060e0a12031b03050904151409091c02030d05010e06031606 69
    0x1203445c00307180c101c0c00752080780071298000f8000280407034150310307a402480c2418490b18000c030078030741d441c5942801c0b0b006e0703000ba03c070000d2001c2010a0104206600e4081a810002c4428040c25515039418030034603c0622a01034620385008003070102d9802c00e0603100b65502c26903280d480c0c03101c1102210f403a650450b500505000c004101200c5041495004803043e05c103000b03000344e682d6124034007804004110301c28464070500c00d00d03500e05050b0880d40344440c00c0b1a9941c0300c2e41400d0480d0303505d02c090140180403c0c1d80400303000300040e88850110700d48005020a458030503084200c503043c008600c5c0349800021a100c0d98040e4880001e0384086841c0700c00c184420800340ba20014603084565100d051a2aa4001d04041c4144026a10b003e2040f0890389101007059a12042d4824828000001c8855519540000d5289107045560300c1f00f0030801e44083c81035a141c100d100030700500301c0320280c222039051f035179a600f04122030800f000460720001400f52035000f4986001001000010f0401032101 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 692487293 1250 692486043 692486051
    0x6030c040b0a2904080109051006050a15170411030d1814130f0203060109210209060111030c160501050f0a05181206190b090f06010e1216090b060a03 66
    0x40b0307034070650011440038010b03803c0c015035984c0c3d202c960030702800c03403014141c40601614001c5400812588288021540090f140004040c60480009000c1114040250512110400003885100f103411040c1c402c40c407810347c100804105400341442d10301c2c0d89001600307101c0c0038584c0030a11000f480c581011120010495a000b020040108840602407001c40400c141028499050611240c02640c49000280c5e0780d64800c075075036110404410076080500701010b0101d076580000d0300300390400d2507000506041100f0280100e2076079614542c022060301c3c030aa0000c00d0318400e00c0e0342c101c1d0303054020034007403900f175007028a2440901e990788a100440400d0000c0007a038030000d036004000100000307000800e07201c90140602030791520f41d041190040c2c4d65215010380d03074407410100d10131803030840400745c00c14801d5070780c40b030828002d81005801c0a05021060700301c86a84d0341c4000086605013061000792000006901078404416250740007034103014145109510641ca520080d200a1074083c9008a = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 692488543 1250 692487293 692487329
    0x30312090c06030406090302280f0602091203070204060b131e090c0f08010b0a0909022101060c060c020309010c0b0a09120e0f0612010e09030408031206030c040b0a 72
    0x249048503520301260010b501004000501883d40c0c03152081c580a83c0a40b99510030101e03d0007440754010300d5200010054101c0040420812048186541d2289500501d410003a000082070100440400c00d5190710018a00302107040600500c40100076124146003800180d40d840d0000e00b500b401030420b16034034107820720046100c0c51f490704000d0140702410030141040c0c020040c4540c900c4044a004101103000001e40c10394240100c911105c1d543d65846a440d0038840c6900113540424095181c21000480342c0b03004a00c861100c0d4000c20003911088000180d6144c8802a94040d80e0380c030095400c00d0000c2d00303c030317600202118000b6070300c0040b900ca980e407200307000f000a1400c050701801e1010841c00e0448015009503240c4d41c038680845800020004e40341c100039403842020801c18120140d1001000740860f10820300f41c03c0764204c1d041d01d007004e885144003455608010190b0300030002510038421642002d01550240c01000e0700c0900150841c0c5000c101400d07881c1c850110443c1d00b19900c5 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 692489793 1250 692488543 692488561
    0xe120318010f0f060303170415020d1d03040806181e240915010803090436020109050301150b0901030605030f100501291c0207260702030312 62
    0x85261052402c00300031000800c1680e0000b0005404110003044200001020207045400101d2203142c0c0720280f590044c6810b08018040d4000c0c0060414443d00e1b80b41c5001152840c0181c655020400c0b0000c5444034070740001580340020150100c840c40c40881520341040b07001241001c1d02e445007260540c03898115940d028075040b035160308000c913102180003141540c21f00c000c41038002e1030000c08403114007501d05490000ba42d002c0c0300e0502c01e9032003040001003d007402c0e00300411010036a800030000f0050f20170b440b119509802d60580c001180418002c04540e00410450094070040d0001c11a849040740380000035030b030601030105070382408180022540e10170307003064018003000350a403207000030420901565400003100040110b402c003c008158403055041421105051544a403c501e0001d13400d0301480e404410b0702d5502440c441011003c1440c07e000502040d840340700d4000c0024103400c0501921100d5920201c00843c00b0004003002d40c2d4004140d900e40350541a410540e91035100007 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 692491043 1250 692489793 692489801
    0x20c0c0a0b0726070b0f070e0a0e040f140c0306070c0201020a0f0204020c0a0507080105091501060e1306060203071a1504051e0702030c330415020c0307060e12031801 73
    0xa612030448000810600300200f4003042d6000381407141c06e000064550802c01d0701d000c400004010f4225820560803c02c2c5049100020340050083c13a485042e103c581d11180941070207000e004076107a00010040e5058101044601d6010146240c403089210356940000d48414600382d000d020b8120040c4501d042d580c66034112003d107811901140c00291652a106460390400c0c41440829460803000440003800802c04104910b0201c01088140c3e00300f00341910030307940c1101300326040440c41c0ca0a1070022028841c24018000c2a00215110f180c42c3ca0300034143c4082808114440307201005015402c0100481c0140070303002180c010810f0b90ba043e4019440c1c40c0c0050741415002155000d002e980341e000700c0101085207802e002d441c01d40c00480110380c400001e03940d001140603800440300143d60803000145802510400d208040307a03494614010a0b41c014130340d0f0351082c1d04009100403c0042d80e00c03c03058401284070240c11340d10441d030004500d41c0402068003800c502401c81d038810741e2101b0b603c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 692492293 1250 692491043 692491103
    0x90c0a03060803161716022715191410020f010603030503060118050a0902030a020c0d050d06060219060e0f06040b0a0b22150e0109020c0c0a0b07 64
    0x1181e46030032809955140c282101d410980784d46880e070b401160b08060700b40449a0141c8031440a00041c00b15038244600d0b0503500840428684903240c0e400308c3e1a0303040350402c0c0101002a07a01c50000000c42c00c01c00b10100024190201ba43d4914081040603c820b00c1256915412111400c4100702410305074100301c0340105902c0154a441c2001c42016002400346008610a9a82d44002e01c00600c000a204510b80070315640300b01c1c044c80070440f625064005507802500200e016051504111041d443c003001ca14208000c11030100342c0c240c05007100c1c4955801400c80c1e100801e08540010559040884501c40140c40d56482e07a0a903980700604210315070340c07010204100da940d4503090406da40e103940c0030b0311404078183c00e141480000b4503050468070800030440c0310b6400703144024080d460091000000700c41d48481c0c00c6400050104517855014001e10310f2060241e03560a804500a040000f411402d5219030804002480f580c7c0120050f5101c250b8407692000c0142044903008000395601c203 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 692493543 1250 692492293 692492309
    0x90c10020a052b0908060f070521040b0618042a0909170309191104020c0a1401090c0b030a060506040303030b090a1e23040507060914090c0a0306 64
    0x31024800c010400c1c0f0340b59000400400c05078294091140c02c94075603440f440b44034407990000d030118002e0030341283c286030045a2410101d00d031000e101040d007a08644030000411400d110010001070000b80410f5607448882103070100b040340d182d24410744500e4130160010b40741c0d0490901291a4026031525000b40c1160a4040f0b541030303660f22580c00c041c009640b0304441c5402c22001c00c1c4c407410703c0c120550307002e903142c10080c1c00c0500340c010f51a1a406a03000d010303039881190916030403542d19584020a44031b10010058240d22802d0b050403519042c0b15040c1e142168540006038002c03c010400380020b541c2c50780403403940d0351105410724014140c0c680150382d203c000054000100344d0503503c20708020070141c0740c04003959600c26040044038080f014141c420300b5441d04500381d06405900c07003e881158070820002c0c0713004040e07419803582001c45040300c2030350060009101503600051390a0050540c0c1e003440b40000b02900c080b41c426840135122070b030400000306004012900075007014000d0f0a0030 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 692494793 1250 692493543 692493553
    0x50a0207080c0a140120030613060f0e180607052d09030607080c0d11040909080408100501051e1f1d04020906070209041703010e041703090c10020a05 66
    0x10b8821511007444540c03c4803200f50f100e010400d183e07410700800780480544c01c8440ca06118014000360f0543c0020081944140745103224990000d039842108081c00100c02640d0740701d13003820b01103080d00c080540f0408010002805040c10100000b4038241d00407410f18082c0e8136a0000402c3c000044a41d8a40d904264082c290801104080c1c1740507181d20343c0220125502c6480e0304e00141e641340c4082d20346442842c000c0007120503141780c903000072010f200200c942614103a07035500040d080341c07040c0301c0454040780002020080d00d00c0c1040340346080b0300c81000030001e40d4905000903112002040d03500b0800c4400e4540d200c1e0a81d2044450382c002503449000209040c00320300010030056a03568600202d0301c004680a0341407d2510a86600d95400703070115107848020380030024800c40c020011919516414a4030320703510200c80c00b460083c050740030b8034500740c00e151400d1600b4502521504107280024810420f4016000443c101d003004240c440b0350b54515540012803c180b10550040d2452180c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 692496043 1250 692494793 692494807
    0x30602160f060b090c0307020705010e010909060f03060c0504320301020a0f030510030c091116060f0f0203071d06040503120903010638090d081e0c0a06050a020708 72
    0x20354010010f841001c581600441d56100e031130b005207000c00c1d202440160301202083c882c65000710700c00100200d05051009910741d079180e83d0419149641c000d5043d150402c4010420041c0d20301580100200134101541001d04145140002c6030244070000134200b1504000c1481c039031006001c21030414003400035555a4800d01010b4003000d0028241d0700040d00c0d001c00503070034007480100b020540368446002c1c019280340145000140920f08114501c8010030003058048403241c0001c2140310303204078000b04030201c0d081080c0e8111032840c00780001041c01001004403c5501c008040319021410480140e45c200c90404100e082c000ca410650f010321a000002d0907401444014010b81e540860092114544407a04500181011002004d2001c00054040c84030b6a1009401856041e1666402d050640001c0003030301410b40c1c0d41041c1c900340303000030b03112909801c0c0e1545240b04440c2840342c14900202400d00c20303510140004041c07d4140d403180815228031300313901141d91140d041035205813100c80c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 692497293 1250 692496043 692496053
    0x30203220c03150207030e2205090c0d0f2105030601050c0a0606090902040608010b01020d050c0c0a090507110a020105090d0804091d1b03100c110d0504081204080601030602160f 78
    0x1702c801d0054000c100d40a880f000145001c1800d9140650000410311901078804441d00c080d10025200c100030b0f02a41401d00c9641d21a8103603800c449010300400d034000440c50500048042610f0b41901c145e19500c03881d146599000070807250004006e207016a0b0b80c045000c0120305043c04004010419803d0440014146405402070341003280201c80400c04035a032410958201c810141c2005c0c0503812540c4072612003070080300a059120340c4a4180d41104140c400000d402a8041c1c0118480c075698800380020964001e6000411080c8071004040c15282c523000a0024051780f80c0051107201c10100d071508000d52401614010984204144140040f00c41040c000542078210860284111023112800c4c0c2021428240325800140c050058800302d05103c901400a118071b0b101031241d410a0200c00e100b0810140e1081741c096920203071a5800d22070242e0505088000d241c4d541c4000340000c1c00410702c0812400d0451703620080040ea5107081c00310310b1805c910a8640035044440c4001c1c841d040c40 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 692498543 1250 692497293 692497297
    0xd05010e06160504030b060103050c070f0506040605070215010b0d0e030f0408160f0b130302100905100509010918090218010f0b07050c0108150604061d01030203220c031502 76
    0x700c0e01c04003180b100040014200d90038000d80c400645880e80a001041881d4001c0d88142d4000241d020700c0e91514489071101001c1e00182c0780c04850aa100d242040280a9140300b001d401035013510180141d21200e00a0504881d010300507692000000a10080300421561006100d0b491000c2641c0d181c43e1000300e09486600300d0310640e0014000d0718020382040d903195840e1815140c1014400c60079508000100c81c032500301c04019914000100004800340e035481c8104c0e2a813500961b11000243d0070041032040540302c0303441400c240003050004c41d04c0e40c1c0c5c01c07814510541e45070764100003d480c40d40c0080c502900ea000b4010f9003208508512002d4042ea415207603040c0e551950a19202503031f5142e51a043d4440d070305000e03017150440c4051641d103600c50400d054002200d91070203104661503e0000b11540d01aa01c070a01051a142414003800c0c2010907100900e00242411800d500c0e20245801c1550504801118010402d6402c0c404000c03583d00d581003e16000101060650307004034100d0b0084d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 692499793 1250 692498543 692498551
    0xa21060b01020f01181203020a0816180e060307050108090c060c070f03080c0c0f0d030c0c0504110c0615030a030c14010516020f011506050a030207200117010609030803060d05010e06 80
    0x19820509038030b003100c0d00134000c9505c00103890356076000ad5500d161041100074195000344003086426000740c128107440c0c512800151005181c450038074100f0700d04241c5015015405141449075134000c00c100e520700820900300154007610741e0b540da004060b4045c0e080600a810500b41021220800b0050045007000381c000040031504541149508030100034a250b0a115025403011180800d03100080c443c8404007030051080c1c0500100341e890380002815280c045001e6806950041401035980e0f00070440d443e040724035050b00c4520850088042030b1a00d501d4107001c0c0622155448041c104081da0909002c50282e4070000c220310b05100542c1c3e600040c480c80d500b001440b031034614070031252061040c0143c0801c0001444945803800006548036040802042c09141e42403240f400414296000003030a0400341c50980600101d42002401401e600c940344001d000d071300d0005020f80f94001c1100e07415a5000fa000d0b60f00c84da10800068450340d0502030090070340d402d01c00140c04080c40011000d0107 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 692501043 1250 692499793 692499803
    0x90702030a090e040c15201b0904082b021603030e060708221e03141c0207150c030516141b0a080c0a020a21060b01020f0118 55
    0x10b140c1d81e4070140d0419400640d40074211a903550001c021074a00c080341e0320075299035030821501d62000401e41c0d211043d0f117070b003072a0119040840001c102c3c9505100715140b901c8100c400c01c640c1c0c1003e88403180207006500c06000d54061000c050502013403000c0b81c000c030301c41d50322006540da104078001981d201c5128004c210302103070901c2c0c0420244000408d40b0740c4540348070703030380c4030019550a048104013806a072509920340d8414641d07400030a03110310580b03000b50308900020b400c00205260040c004807160a440c003600809000000b260802d4501d0700d25842e20020025071121030380c0c00c180c0307180f810307203500100c00c00d142159002080d0b8040e008144038502a24501207440c900700e03815a04040c207441e544100400802019680345005201e5400552140e02162080805039444601d9503002000c40ca045a0201a40b4802c5140c0399800344060911184100fa584d40d55642c02d04600ca03044500030048ce440d18014200da074070800940800b0021030303009115110390080300d0b0407110f181c4102918 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 692502293 1250 692501043 692501057
    0x80a0311071a03042015120c04030c03080702062713110714100c090e100b030115030e0712110406030209040f0614010906081e121305090702030a 64
    0x2c0c981c00c0480650032040c1000e080525640e04e0b43e4074075121455840c0c3d03544000f008007580f01181e41380c0300c000c0038102655095095440060706515110201c004001464801c0704202c00e100290800700c410301100d5110810548481c503520001d0381a0081400c41858035403001e038a20b07035207038440c00701e110411425a4000124002007500e441a1880c803006454021030400400c00016001151001300711107200070345041003031100790701e02a5581104000c0025002400c2030281d03442011803a070b0011a980c000030b072102e01d0280c00320010b000500c507200b90b0540103001d141505000c0d8001a81900800041d940310301c2d182c0d1407a9104164803941a101c504c0c2500351000355040500c603c0090f1390b0001d003251881c0c0e0702c4d91790b403c5025221910403640c0a4458028084510307442210324040e0000580109030113003003400f401c0c0780c101c1e1105104044044083ca0300a0f400780412810040c546190849a45d098440950b840b103006541c04645c000c07444c0c504102c0d003d90b0206c00340602c0011551110 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 692503543 1250 692502293 692502299
    0x30109110f0a0e13030212030705040806090c0108150f030a0501061404090809121906090b1f0b09060c0a0c061e0e100c021807022413020a080a031107 66
    0x7010002c00c6020352150000d110000c114150391030f044030040c2910070705c1113a1a0b48603450b0310440b45d800030781d04500450710206050000c0082800b000b41c0c407032801ca000306191004803000030000744000e8a2004412840181e035000d0fa00c61003441e102000014003121b0110407103181960003845e00340300300083d0607400d6442e05024900350140c1c078a401c0e004140c03c8c3c10103420f54100608115501c2103600c2900c904a000402880f5144008107418082c02e00003030280800d041107405503c00500300d100d44281404a4207080084003000f2081d00c00c103402c825101c0c089075010450390b2050030b9415110740b0450303424004002424005005542060f035462042c030450851880c147c40301c80b000500807030510f40103507000303040c548000000c52a00e49000c1c0c0c2c000c01d258010480c101c620345000c00a1403101300402c030350160104202c9078071200306444960b42100365201e20000c004040d003140c4404500d81724988c10342da0342000d01d0f000b07400d00360140d0f00717880344c645009031440214454180090082c40800 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 692504793 1250 692503543 692503549
    0x110307080f100f0b130f0324110d050c0f04031b050d081c15320f0f04060b0c0307031202090d02130908041205061003050a1709030109110f 61
    0x101d412119820b071007000c51820b00c0c0c00d004c0c1c142c00c04c1144e04e0000d038169800180c8504501014001140101201c21426910407070382c2e605560982003c40c002ca0034071442006402044003142c4114080b044001825280c074007410380a0f00c180d0800c501005000b140210510105504480240002c0c068000802d5580c02c1800b80184640c1e030080e080c0300c030900c05950f030403c4072800c4411400944900041e14034855044010902e402d0304107104000300e401407036548629800d000f0358543d90f42a11802480303a000000b5a20318651551103015546914443c507440d101c0342c01074409028440c1d541a2104800c400041d92500181416000181da90148003032261040c030071a040d482010303000244800154083c0802c08001d14810024030f681d48841c500420031b40700203803000e001410032017450340c8040d0034064a001e9000d0300d00c0100e0b0144410820000b5030014507900402e42c04072842e00001c02003a260f400600502c44c0071a015420320300c84d40f0410405820308400b0240c201c0380101e1420403c0c00f4 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 692506043 1250 692504793 692504821
    0x609110405091624050d021306050408010c1e0f02030702040f0c0f0302070302120c16031101030b0a08030a0f090305070f05090702010e1209030a02041d06070c05060601080a110307080f 81
    0x2007444010200130720b0a40e5602c10801080c00045404000d0b00c1c00b4107142d1344c02e28443d015881000004d40c0443c040c4104082805000501c610f5880c00441c481400c0100400d1243ca40080034148065407a802d6401c90090003941c00d950340091040000f1000d8202c120060055a050345000550754446040a94041c0c03003a0b50002e074140c5d0042c60300101075034481526a008070701c0035490f4032800342900303282a0300070b00140207144500000c290074084c02c400503094076200c0ca00c07140b140890000500c11070b0800001c2d249820083e203450759502d15118810744250303035035800140c0f044c06050404a42003042164040c202c6000b07545c6800203941d0302c101282204e1002c1102030f4150042101800c20f01c5400703000e88000700c0010140c03200034407070b680040c00702c603c060116100010403501c0d085500c00280001680002d081c1011a4a003545566840d125100102024180103424000c56150180c030790158400e10311041420740c3e40c1c10311500241481c9011200f10090b8200d41000820390031510386 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 692507293 1250 692506043 692506079
    0x10210b1e01151d010e040c0f020705030102071e06020405060c1b040b010f0f2106051002010905030301030b09070509010e0f28051e0112060b0a05090406091104050916 73
    0x2e00c124102400120b050303482840301030340c01d0402c180b06170b2501446e511442151741d000c00540343e5181e064a10f03000030f801c00c0d9031580b1240c405d03407042c0b0590002c40ea45510120014020f404038490b10159071800000a004a8204035040303d00820602e0b0348a43c0080c200a0f14000e802c07500c100c01b203031042004255a6202e030b0300c500142c00d07a500c0101c1c0c01c1c01a6110802c00040b07081001d889180143d040e40030240651044041c1e0b41c6481d4100006d05181c0001c0386075074460b2000340105211520392a40da44411711000305000c50b24400030b95414010300c2030b000038181c0140581c0a550317507040c50701810101920901d85207500c007000300708032880718491800d8012130007080324140000003828000810f0000d114541c0128010300030b27801101800005806428690010030421855080520894075000c100e240540c4542ea0284600d03500c204526602550189020800000c50300e0080f007555140c0c1c455540150910040c000c5103000890301480010040400420590365048444420181c00d2 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 692508543 1250 692507293 692507297
    0x120b0406031101051803030c0d090e010b0301051c0b010e0406140906060f13050c0c070e10091d1e0c040902060304120c051203070905010810210b1e0115 67
    0x1458969554000ca024045e5086014030782c000300010680847d041d9801100700d5000354204c07807009030016421a184001801030f05804000540c10001040098403040c002c2c03501c9400000c4100b09050340c42038690625503400158040350b5607640112000b15141603034112102401c0070304129140098040d418840c10007500149071507215142400181d010001da00d49d00701d074540460700c403c4002406514002d07503402c60105d566030b8070800a141800c145420084c1c003445842c00307014801040c254000706940a041001500d80a03004d40b25116050490f0100340c81c0c01402820606a06420001000144c2000580cce009135651020042103a22280c0f00941c8a0001d00c0410041910003040300d418160500300080440da064540618061000361348500100c1c0001c04c000340c041c0e01ca5030f620000c0100b820301041f6410300e11040142c01110f030180804041d41030130350881072541d10601c2e4800d9a044074000c03142d82080e401407158031132184071490010301d17060000140c0519000300701ca0349000c03507 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 692509793 1250 692508543 692508563
    0xa030c03120908040b07060e0304030f02060d060312020601090e160e181c1206031212020d090c050306091203011401021002030f060a060905010c06021c020a120b040603 74
    0x40e5800d803040d400d50760540d44030075a20000d46001603d800c006002400d4040741581d100c1c500380c50704405072100c0d80b071030015681050100f0000600c0403103001c00303203c0e0304807030a0b0340341c203510b580500003883c0c10341c0007408000749185031102032174010511074180d510044007403007402814580c06030340d205800c0300040750f900245420401458070300c1c0c01075002454416000c04400c414441e140c42c0200c49580b4003604801481840d12580d0802884690000740450074421249152110041490540000f20034402c880108800c40403031941100c568441424003005003486c981800d54007100c150244c24003a1085a0202d540b02a0028919445010400d031080c0f03035038201000d9036410b124072a02c460651040901040300e800c0c42e400518407501c85140e22140c41d04d010390803c06120304070f074451402d00c601c0c2035040c002750340c3c00281001080e410038809a0303110040101c2e840d0071405c40d840c040040b4400710f00002c0c039a60203000000e41610036a0706000d08507070001040111116480300501800d20 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 692511043 1250 692509793 692509817
    0xa051816090e010605060301300b1315180606080c030705060a0c02030303240411030a021602211b0a12260c15040809090c040803070309170a03 63
    0xc0c0e500540507520702440040313082c039900d802045881c3c0081c0c204541002c0d40a80c3d0b44a680101030202d100181c00c5251101d0303101c0c42d07403904580701a000d004071054080008651060201040001945014110342005904d48a480b58800c5203003614085a400c0e05120001075420000030f58003a00700b400034058101c0510300000c20411740d01507140d00c000c2c44251240300003d030f030341070001d0761013418840c100110302500041040040c90384031000c1441146090200e440d2156040c1c1601c1c4d000000e81401031741c40d0802100d1094140440300020340c801d03d9141501c280d09043d1002c600d09601e0003040340d02203021024007000100c90000e001c1e8100511203001c00041590300085c00485014003400c4c04058203202e00480c8031407108003d80541500007030388200e00c0c0e80030031241e2840c004820306101941069620070300d086c46112400351081c501400031909030241941110010106081229514001490041d2000a01c0d02c0b680050f000114000640300c2e07000305000100c1c03a819924003030700c80c6d1 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 692512293 1250 692511043 692511059
    0x81b0901030c0b21150f19031e06050a020904050f01080a02091b190207090c0c0204050a06080a031d01090e0a0e07150507060b040209031009020f04050a051816 70
    0x407000c01c1c00a55288140e840700100c0791440b03174026000000d460000d021803205100004800c08011800783d5045c40b104070307100722244009030540394400f10705004000441c181941034100c0c008054071191a000a21100d4055640100180c0b0000c1e5000d006a03035603030039400c00e000400d10555102d40c000c8880c1e00d0043c034025121543c4502c42003201c02171400e2071142d650300c0c0c1d000300b2034100b88080d01d0400190388a404004040003494030321820301c16050102c00c020844810342e08000c0c0a2903c40f4041091101903800c0800030305521000c68204a806003801000da200d506840071007200c08420288603540314503048000c5d21810060a052902d422010700700074111060b0840030350050800100792084d0f14a217101a0482c681e0711191105001d00300070085500081d21144a5403040042d5001070310003190705900441c802a00240480980c00840d100040340410360b41d2003413924003008800f000690019000f0380f01c0e258041c102450381c85606a564454843d071003d10f0850b61800c000a01b = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 692513543 1250 692512293 692512297
    0x2c090f01030302030d0c200609060906090d120b03030f1210060c030e0f10030f060b0c07051903020a030c0315110405270906070f030207080d24081b0901030c0b 70
    0x70450786013003502c0d0000703049141d00700707c2c65020340000c13074210800b4410801c0e420041a500070300c2ca10040d03c0542481016680ea90b200300034420306100d80d070200c914080c0d07590ba11a80031410060256503842100202c0c02c10740d40c0c044002e9503552032a500c0415a40450001d024094880944840c0240ca1460302c1c00d8a10b01c000154207035001540b0038080c0c01548072140840801c440d00d0f10041340703280364030092606889154200300c40e03022040c0103540800c0310005a0500f00c03007090300d5038001201103d109e91060401078102a4006540362000001c21900044040482c0e0192840c000c0101c003200c4000107841c1000d149221101040c0000c0c80549000441010040002c02d0802030a20030401071124401c011654101c094109208100f8469080305205811080a00d0f04524002d265658096140a40d0b250681440d90b91854822031220610200140040b0781201015055a4003c0305545a26804041c0c50101407220183c200c6d080140100d8140e0b603001560031032031070810308600000c0d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 692514793 1250 692513543 692513561
    0xa0503040206090d061b030b060306240c1506061305090c040302031b0f010203030417030a0e010f1b0e06030c1e031008060c0a05192c090f01030302030d 67
    0x403440c10404000203544003000701030514840c001c04076a01d4404040c502414010104130018103041c0240c8e0b02e0182da580d000c80e54007610480b00b0000005c0320340d62155104200e0302c21080c05c40c0c00003444e881a10700c00a420b1200ea0300003201d484a40c0e4500007030040c18001d0324613401640100d83c0d0b007804a0701d0400f404075840110100c95034200340d034940009240012258452171144244d4480c00701500f0400e49c00018a5400c0c00114554102030707440505da566005940c00d86220040041007154889401164018008070b0003800440116a4001c3c010010724038812440c4103a0032a101d641802002020380d840c0d80204640d003940d85030030300c80700554088012071091550152003040c0b1002084090b500400d04d40c2490b0760720a082429041c031704000506262040c10050210308449603011080741c03400b203040305581812220103001038846c10220040c11000181d040a4145030259021001d10345103c101c4440800f51614900c144c00319600303000260061700b0400071300500030010342000400c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 692516043 1250 692514793 692514799
    0x120503031f081e190303090c0e010b0315180718090c0c0b100504060b031006030212160e090c0909061005030c16080714010e0706020705130e060705030103031e050a05030402 76
    0x40d4606040c8131450001c0c80304110007099680703104000340440300341c207075020300880c1442c40e28550504000001501000300329001e0400c03050240c00c000c0d2900c00b03440340c40d420740540c00820303401e0210001d01401c1042d04c1e10303191002241000200c2240e240151800e044a54403104d0310464543c680c00c0c09200010a81660a1075029001415440701e01ca500000c0c061041c035240ca07030400001c2011424141d42c40301081500500909003a5050a030740725401241e4011980840406002d0585052416440d800e602c0301c01c0b2010480c450300c2801c000c00528204a541c140903655040400110094103042100014011320000b54000300080041000c400031020002c188141942c07100001ea004400440700340c0c1c52084064503040d0309005102004144002802c145403c283c2c00a50f41d03081c81c030500303103d0181d40450042c45a0780da4000c00c0ca81c0d04100a542d20ba180c840405480740d8002c0c48200e000800341444101c0c10102885007034820300041e91b03042d01c1d112090310115841e03000648180d138 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 692517293 1250 692516043 692516053
    0x303030f05130809040e0c1c0201092c04260d15120809030a05030a020114010b0306150d0f0204090b0108090303070e01140c0d020105010e090708060606070606120503031f081e 77
    0x140b540d43d4410884c0304812608d003c0001d694a5100041134040603a010420071403412140340c2c429403007110b00c0e040c3c0e20005103400038a07a5450400c0042c00500111103925146a20340300781c60740340d000d0b00605029582c50004d100c04480281c0c8111551054402c4132102723400304455600181102c0300600311540000e049440074409030300e6150071580318251500260f90342d0344900c0100001c0c24403150041c00c080b91494250718048010a40c81010749130341026419000a102040307581e181e000b010307140050780d0f0442d06e8030780ba01c8008004050150116010a01e84000503a46030400402c403849000c07a50f842d035954008420044d21a00080c4c4540c20055034148011100004100502d0303644506a03400443c4070b51416800c502c1424026043c0419604410414403a99a0000b007080d00500c042d01c01595a82c00c0e4103001008040f03580101c614440610640c2007800000000385000c1d800003854245100b000070380424804540384100c2d000d6411000d003204800551014240b00100b00d002911 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 692518543 1250 692517293 692517313
    0x70501090812040b070e0f0d0519050303060901090c0915020307060f050709050a0b12061309120f090f120203010e010513030e04020c03030c0c0a0209010303030f05130809040e 77
    0x401290042e070031454010031440c08010030301c91074240711504030308035040c40d1401385410700c007203410a4600c0e00700c0d6014140804005040050400940c000c01c1c0542c240000b100d000e40c5040c58880d4800d8130003078447d410302000441d49888a1041903000e808985a802900385811001c400d400601c1080c0c03800e40c0000d0002002250050007003e560701114000081e140c0790500014090000c0e60b046a1b001e901c15901c14041c01d1494000c5031a00c04006030780300d1107590340398002844451070b1310440110a00745a500070412202d002024036040c4103031102c88440141050454001030f1510410a84901201c01007001300002c03030b52420403d00140001c0303014400b20860a0070b4031400d0b105010fa206104508000b416402030fa160104c3e10112030540c030b0407000b03121a5a89000103011030400300c1d40010090a960b6081000700c0c00198082e1490700d0710740e52804c0203002010f080704883c420318240800562030642c081d0114000c603510264143c1400c14200502008040220403401d040c81121100 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 692519793 1250 692518543 692518553
    0xa0501050d02090a1b0c1e0b010902090d050f030405130e07030b04060207020d0b150108090607030c0224270d18050301090b1b0f270d2102071a07050109 67
    0xd41c1c403508940f03e000546e8801c1ca030101e0015900e001020b003040c000c07503c040c000b40c00c0760f4070b03241100c092010142c8c0b10720038a00005c6500207c264018518411075840c1464440d007c4040e00448004850201040d01c0090001d81616038031201600035400030b440900c006400017074125007180c02520b005081c82540e501048407652101c509461401c036000400c2400c5070180d426000c2c1c98420b06e4441c030142007034422150303203020181846041c151202c406001c420701c00c01103081e0004901000003640100e500c000c41035000309842d0564031240d03411009145070998040c08101000c540001d111580d00c2d05812240888400703030881440b0001480015155000d000d0350403a40d0150f03a2030050380c100130417140c0803081c41005a200064082c0444001d0345280c3d070a440312003010340d402000107194a4040c8030303103202150415501020088055042c0912030b4030410360b5401d100d043c01d4100080010a81c3e44200a109078035140281c50300030b86098061001610040b403190b000416007400c0d42d510303 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 692521043 1250 692519793 692519831
    0x3031404050606040e0a230f0d03140601031b08060411181206040b070f050d051f050a0b07030311040807060503100504060b090108190e0c03060a0501050d02090a 71
    0x800c1d41d80c1c1d80300409010252400d845500080046000104940d810960790340192480710031103600b18401c0c00156a4580e4014001400c9084110f008d0715820300613464090010045203110100e5800c0f03150014000354003d21880148403105000328180d08040401180d11030b400a050a800c10381300d001601e11901400064050801d0100c03c031100c2c003000c5801d218a09282c0f11030031400783e01480500c03000c030f041c0c282c00c5070b00022145044049001c1d03108080c2da20f486102070700304440d441c00c1c0c10804145030341c02c50341000070f600d21030104a09aa40b41040355158a078020f0382503102c0c04000210002e400703a80b0802d244200102100c0c2442e1b40c4188090a2940f607074400c0d0301060300001007201512900c1003a1001d0b21040f6010000b1905001c2008010f0041f421100e05000103140490f001e0b5100c0610b0030001c45200c04103000702030440380c0c40b82d1140c002d1002d03980284200760200b0708040403402458144c64015109858515054007008040000079000b282820b43d81c400c107101181d52011 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 692522293 1250 692521043 692521051
    0xc05191404060503071415070b0f04060902090106080411030604080307051602090c0a111216060b1009090608070806130c12030e10170a0e0c120106030303060f080a030507030314 78
    0x1443c4001c046d82041c8888000514000d000d00c18042081e880020210742040d40c10415542450045940f10301e40030f0000d19448078041d6000b09071200028040d03600c060100d103e21303c07034125101500c20103018036a44960548004161406c1840010b02c030521400192101e1032a0240ca9480710b85150040307100f0101c262944e40300050000b5070300c01c002d500507950711029844440181540c5040f46a42050343c02881e807400301c0001080031020a112103a003080c103040c00d008040740c031810b000410160240d150340c81106980e604001000480d0389000c58664204c0340184040c010b543d96180c0c06c441d040300c94500446406200b850041030b102d50100d45040fa4500c2600c81c40741d000050001c1017982e100075428001000301c40803602410101d550030700e030f0f044048420003194882c450101c1c2c0c0d08200c080700180d504040036a40f400012201508807204a0b0b001c1c0e1010001d4640710301e401c03100c242044c05500b01c44e6204080450000741309030b00908000340640fa0021b5581c02420314900003960981d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 692523543 1250 692522293 692522309
    0xc1809070510051e0c0606102c090a05060f01090518180f07050a090603020609010c0213021606060909020105041512050106020f0106060806011b06091e0c0519140406050307 76
    0x305e000c10b002041000300c603401490894071a1315016000030014000a108201900c4030300701c1c005401d110b6500710300e003006110001004540b2507c3c00d9017030000100f108031122889036180c160f0b200b45550080c07003400309690300a00032042c040d0074000243e0621002a252140501d02e40a0718042c0c070070180320320072861080a01500b009440c0104024041c8c46035001110f0140c41d183c1c01f0001170b0ba4003403c60340b02c17000c2070070411007441842c00018071010003118207034900c6000199001c001120800310000f018803405082000c1521444094126034a5150082c04104100f01c144001501d020225159410a180c020340c0030400045040c00e8410030707400800981c0c031480c240d00d8820001e004540c041c24461908900a01c1e000c4002030640261003480300810401001d04414401d40741c00c60000d080d0441400444004c0c3d90441c4c014010ba00b031030540d040d0010400c04996450b241c4c5141d00e40207642c1a1078150b4a0800402e04080712aa1555aa0043d44c0b50000581c07030b20244500d00c0148201 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 692524793 1250 692523543 692523547
    0x30c10090e0601031e0c030b0901080109140f1504050c04060b03040b090d05041205030d0213030c0e090c01032703080702191527050c1809070510051e 66
    0x10401c4a075500c0340150080d814941050060704074800000300c44520701485010200307001c841e8803815002003501d45c0083e5084544100040342c2c2c00015080100c01a1140700c40300b03642410002020b840c3e03510302251500a0700100743e03400004106480c00340d00140684140e9602c10300c140c0000e0308031a015400f02c00b0004000c8104070a208901614542c0f0503c681d014080018031031300300400d148903502541500601125801045c0700e4100188d0303050700d00c0d00108641d1001c40040300c0003050224482114150450305022540d01558258540164400ea00401d04441e18138010340161140d0402c03840306503004010001c102440d900d49405e01c13030003512038640d1802c02100080c100268030340a8014491807200e03910000c5c03980025450903907401a000035083c0384103aa010018115140089000a0510711400512402081c0041c882038111400720107208400003200e00e40c6003c03102040301307401c00d000810850605a1000180d4030f040c0c6411072a02c0e583c060480300c10000c10350a142d8500300 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 692526043 1250 692524793 692524799
    0x1c060305010b150310180603060f0b0f0d05151b0327010c020307080d0617071e0b0d0b0a05040e06090c0d020d030320070501050702070b0f04030f02030c1009 69
    0x200c91031468080300c01038886451864110700c8810700303c17003a01c1094580c007208103220b0301e500425802003019507406a800e200c80b0b50301c3c40400c0064030424071400c1c031424482d48030700b0b0103140c4a0780842d5000e42c024042c106a059240440490742d90040070881024001c0e5143c551035030ba40f000a5110b00300c0c40c1c94031120109404217075036045607402c180842c143e03d010781311031001b034001040c2d90320305074803417005c03961403042148130780c090032182d44161410082c1c81c01c03101d4540303400310f105000d9410901a0550540b180108250082c04510440c81c064008001d00c80d40ca4207503810401310b1800103000d4110319540c0e840800c046407400480b014403a0030100c107000e103401d4240800d520b030301000c0340c01c1841440590006154408140401000d0507130b9142c1d1441ca1500e555007010a1074100e034000c540703515403414020301a20003120b0714401406081400701d44074801000b44e601040f2110420340c103107400d55232034207200c050500b000da902d40f0801c2011720603540c0d2a107054080c4d207550b0f510320310000c0ca = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 692527293 1250 692526043 692526049
    0xa0204051c060f0c02070b03060f0301090b04170a09060e0312040f030501050c0a1413150504031b060509010c02041104030501020915071a060607060e0c01090906050904081c060305010b 81
    0x3c510050700300c03404c2c10701c100088559800500a001e66003180300a550302e881d0f00d0009404d60070071f0544641c06501b0020040c4c244091140b0032807156004045c0f400004840503000e8480303205000c0014041007004c0c2080c07000c01e203c0d4108000044020703045507204c0501a1410705103802660085110713506c142414403c01201b800341c560001c0c880030016040c07803032401028094003403a40403010300700d40c003103001001300c00c44025000c000c24a0903040d6600b440c009100422550003800184d407219030341c2081d0514000540e28031401c80c0c2066545609007000e650045032440e920301000c0e41d100e40c680601d4030700c045002006200840c443c800060351408010188901d85101401c0640c10240502c00030001c13405075007102d030300180c0454021440703a80b10000600207020b800c001070300c207a10b001c080206640d000200c129407510240ca074200c040759603203e0041942c155000b6a600810043c000c03070300041d0030b2801340c1052501281e4043d02c902c84410900200e03049680140e44ca69105c0c0f19502c2c85007 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 692528543 1250 692527293 692527301
    0x71502010f0510060e0108041106090a0312020a06051807090e03090924030610030b0a18030801080105010b07081e0f0a05090906010c0b1305160f050901050d0b0c030a0204051c06 78
    0x5d0000e091008043c9010703241c40c2003c0925495040c05040000380005d020b0f610282404040c40d44290110542d0044440081da9507803009400c4542d146854082980c40200b000b100d00c82c000f83c41d000300311490621410801500c2b0b241d081d9030071440280440d240c140e0354400103520452b400c05a29074100286081c040309010032400090081d0440000c1c170170074680d4400000244c1c0c2d0000399568423a03d410580000a2003a9028840800207480e0b610042580c0210003030f04903000240244000c0e43c854400003082d209850009082d80340821100744100d00e0300284002e16042d1b104040e09040e41c039240520b480c2d201085501c001400001e480c80c041c6031a0b602070790414400c3c600300343d802d241c40d1b50355450b4040140040d030383c100101d001a81084410801045500c84511266075110340c1c0302400400c105407409100e00c0340030100300208160515840d40ea003c00c1e0421001030f40da40340d01c0c0c03130703602540d10241c036298016408200204903a00c0341442e224010189000e58440a0602d08080e8126 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 692529793 1250 692528543 692528567
    0xd080c011a04060f05030a121205010b07020f010813022404061e02011e240807140f0904030c0c0e1005040510080d1404080d2609071502010f051006 65
    0x103101349003480f00351030006903010540d0b8420707040340c10a0455581903401040070100c103140c4038109000420312aa2286c098064180709456684201c0060001900d01440c1158540e4500800200d010090b01e0410000b000307101ca0030701c24552105480080302440d41c86500104040307011448803030401100c4070381e21442503040d031008005080d40e14091000081c000f1200c18082c5845218025480d00b10317998540c541c04004040315103050742c40c981c1c207490307081e144151041e010342d4640b80d091b14146410000301c510300082185a5035a19968141c0340c500e000d03601507074012801c1d05e0104086510007003c2d4001e1400010030346102d8506010401510303401451400661091441001900c1000558081008081c1003124a10900d60440c2c482ca00079a40244600c0c0b0400b010f1182450b0016014841c103540302285205090340325000d4466480259240041640b24082c2008134000030b00c007031051000680b0001c1220080e100c0f00500303883c800e5030b407e815a00103100802682e5000982e15800b = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 692531043 1250 692529793 692529809
    0x50702100b0904021e13060504140f060d14060a02040e1f0e0901020f070b1b190e062808010503160515190806090c04050f0d080c011a0406 61
    0x6903820700012510519001d080240500340c40d4890b00a01e5862001764a0401c6010f4068034941e003a030441c0c0c80203440d40b480750b0b03401203140030b4041d26043d94800400d0322070801201c10018984070300086c080c14165a0301c080d078034140c1070644540028000d01c40710340145540400540c590b402c00441c11010b00001e07102d035600340011000740d80718900c00c1006030211070100311a12019a522224940684286e8070002a1080700040303490802c15070350700c4540a05000049549041607201c01034503244075000c044107000b4050000e058490b403086012000d42500600200d081c0103442d1544000455072002c1d60300315417000c0b0100c042683d4400c2c440750051808500510a4030b41c1d0030751402800160340103150040400c09240c900403a45481159031108400b15459aa90640c100043c10302c041515564424501003001c0340c0b01a00d0441030b581911801030200c001030302190100b0008041021040b50141410300007400400428031810030300b8500703290841400032844040004a42d855000542 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 692532293 1250 692531043 692531051
    0x607030501090b01091503050406111c0b030106080304090c020a150b042a08060a031a01140402070213090609051e280b0403050f0f07060b010c03121808040905070210 73
    0x109800701c400a015000017903050001d040e407102d00300b03840a440c00d032f03404800c4d0300d000280c100c80320100807541304440e100710041000304010940405080e64128801d00310349600500052026001c66841114050b0306401210480c150503511048203c010306006641550b8400490807141040c0c051005403140041d0455000e00c1c26a40303a03403e954820103000e0030021804002841612858407074405582c00000d65840c4413410350484100c45424001c082002b00403240c80301c0b090504d40262248035030700030040d08156100c401060001e00a40e031003541e025031600c852070f004c03c2c800e0040340d000c1010030300002c0c9040f503000d07465803a180407144204441e0704141003610b8038104c3c62000514a60380101001e00544581c241181d10340210403c03510100e00c0040d4030001c02100c540104060f07482008c09102c084050001900c0101100d0300180201d40764541241c0d000720242d0100c2048500311060701190760081d20b800c1c696400540140b20802c0d5164103116202c1c0c0c040040b0b900070042454180 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 692533543 1250 692532293 692532299
    0xb09100f0915031d0102030105030706090f030308151005031e0f1303050d020a08041106071a070323060906062d04080a0b060907141801050c0607030501090b0109 71
    0x1001020203100701c000c0b84654091411a1600c030382c11002c1c002c0846400c4960405498900c030303000350300038441d103480382c8a9283c000422500401c0c1c035004446020089030304461841c0c80598201500404452041819001ca1625591030141500d40b030200c42e9102e5482b4070341003800104402c943d400121a40d4071260401c071280c1d038107141040d0302c4003180d0307900c0d01c3c10109803030161850b00600a840340f0f040e0001c100c200c0c00c00c1e03101680710b1081e80100000204038140c0014800e940c0714451003d4403e02400c0030840c0c040e025949440d41040083c5000500c151a0001490ad00c640001032041a1340008040c480546088000140c120304103c8542d89450182d051a40718654440e180d112040e0341172802030300440340881074400500600381924145d0b00b46140c080740e03c002c22903605125110305404103144c10f10450329480301c0041c50000c4c9260003519004641243d00010b405810031100300505000080240001c41c007505080d01d02180c55410220a07500f40d41000d03c41d41d0400036003800030 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 692534793 1250 692533543 692533547
    0xf0c050102030c0703080a031e050712090308060f010e040e070e1803030f0408041701020c010c03022a0709020c0703031b02090601030f0e1b0310090203070510030f05010b09100f 78
    0x19130102c81c5e100c5145980ca8940b40421781c007034280d0001a168004216200b10100c01e074680200e8407039021503581100b00034030f00354501c0c1210f00460307000d4005078078440050b4050903c11080d0f040e54105040441480300d194001400f502c080000700d08064009130010001c000086000d0b5411010347d1000c0502c424110200541d0303800000c0180d41000349260210b0103000c20308080340c0c09007020056080302c0741440ca10305800b030352002509042541c0f90421400300c5a20900c03c2e1060003a04100308620f1080c0072050100340c0ca100002c4a223680916000010a01814801464060518805010481e1650602400ac2c40601405c4043d2203208800000140d40f0500400c3d44a4001d0030300050f0703204850034182c010881225048141c2c030400440241028a81700c413007580c25000c40484640840160503102034645480009406510404062240340340400da510290401841c00003440c02300d034907803034080d04c4007a84a12010704000a810605041940c107107420030780c0504108510601d51000 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 692536043 1250 692534793 692534803
    0x1140315180f2217190801050a050103090503251202060114060c011b0207050a080c0a0314150f04020103060e100b090a0914060906100f0c0215070f0c050102030c 71
    0x414040303c08030919102c5203402c1201541c078480d08182c03030240000040800b01c01541c461a0b1045c40007105200380c4d581284660400740c140c1b078001c0c2c8590185480c000040d805444104000c5449000610039040f1003000380e044440d0509214020003064115400d0100f0705a01d4650381c0700440d00488010300c05251140482d0f0000e120a50b40640e46825480b4a1801069002c8001490340050001c0f14100b590000350740d0169001224201c94065541444990b81c0c030103510f82d660001207500c0c0130800314201118100c102d240d84401d0300c803400c0c0517114121580604440002c20b0b00442c0081c4410355a05106080181502c000e43c40114201030060801070404c5204080d038004000403032600303075141d609215008003070901080c011010000a820b442c2d40049408500440d0a0304c00500e1901d400d200d890300d880b110b600c0d0742c46100c5030581c040310001110070080c1e800034841d5590442e19244000205942d6008036014080700140d0326100d05a80c0303966110070304643c000c0c4605149601c3c0030030303 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 692537293 1250 692536043 692536051
    0x90e09060f06010e130e060a0b03060c0d06030803010609090c05030103211806020c100f050d02090d150504030e0a061205090709051006020c061c020901140315180f 72
    0xc0424072540c0380d00049518141400c00d8981002c0c4401840003881c51640207901c00708003000a81d802a65407003190000c0300d84a42055070706500010100b012569040d005214400d9441004100740da16030321500c40715802a40440c002507140c400070414141d00340f0581e4210309880c9000c07455549180c403030a948500400a1044e4869800e5124204a0241003200070607242a04020489a075840c1c003e500c9003000c0b0043d6000303d006010884041d40300d0f070081c1039580e00070707200c20341084448943c45000703400c844040368102110f05500b034007284402c09503401120200802107031300e00e8607150050140b11020007450242c26003203001e000e2236402c0300b040e15034643c2024001900381d8444040307924001c210b80c408400e491811041c0a1140c03c0354a481e4107803801030f0204c0f61060709400a014152189211a002e910300c00c00c03264203404000d0300180100380703051410071240301b030603102681d05910541d02020001801805500542170140010f440e00c035800c0c1030a80e05181003402102c0b1044014 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 692538543 1250 692537293 692537311
    0x40f0201050a022b0e030706140a030b1327150c03090c030c06020d0503010602030a2601062712111f0203040e011403120d1805030a090e0906 62
    0x41480c00103140708006101181901024510340b00021400c03581006075180c0d0303c2c1c8006081200c1c0030300c043c1000260300c41298015521681c10386001c1c40d0414441d001480b507102051b8588000544650312207072011060394840f103001800d078542d1580340395551007132035881d03d44420b030305c000310082900fd81c00032001c47c00d440c80120300d6a548039421801860b25200080111854500c04001c1c0b100d107014003003c1e0344051b0215075940b40f1341101507415020900c0b40e500107034000c0100b8148244600043d4140d0221550115000c9501c4c02a004001509800410010ba50b05140b00e00c0e4a003000e40922904c030305030300f03580301080c02c0040441e41081e00460207400307146100e8414080352030b0200304514039800c1494201140800c070000a4903540584250003020705240004103000710072001207103c51a000300144100202100c03001c002f0b812420516404603581d00304048505200c401c07050910f4822400f4580d1984002c1000d4042c1035075030000451f4400300f01c10001c084400203107050304401c140d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 692539793 1250 692538543 692538547
    0x5040902030c0f011413060e012a0201030e30070309050f030c0306070f0201140c071212020f0d060f0b07060f060b0703031505010503090d1b08040e0103060f05040f020105 75
    0x1006841306144400101161880011514007030040d1901006c1170302e080c0c0d0780c0c805250300d10000450706000c581c00300c0031960b86c92491109014850307580280c1c030740384103040c042101c025520940d070501c2d0010101000c281c2c00501c1a250304180301c41c110300d0325113030481420700b0501c15441c000c8c0200340d80c0c02503600641c0b1010104409070360400c072000302000003c085a5032480d0221005000303503802a41080558284208510400e5002134401e101b800403c0c5114201280b03034a80301e2a4628288802042c0040f0107020300c0940742500051a0446030780c41010b995001e0a003014085540592000405810721700c1c0071300c41c94602e21704803070ba01500020045803035011800071600508032580026003034240000c03a00304064164010100504c1c4400d10744002513600d10041d2030364402204d00030955000340917008001d5026011401685a0708540c0b0300f0900d01c1a9280201ca9000d0b4004c241d00240c8600100100440d60064501640170f80d00140b1250401d0396030940120102c68000b4180440 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 692541043 1250 692539793 692539819
    0x60f030203091510061119080d0b0a33020703030f031503031115090c010c0618140f030c07030b280614150a0305090a0501090b010f05040902030c 64
    0x401c083c103100c4078120408507182c100010191103d010911038000803071203500800d660b4500100b4002407810324200401c0e07404016942c0e40401c1c1c1d12072181d40300025514038103803003c2d8070b0f400d40c81d070045e0140c2c1030003076030413041c40c00760300100c0500711403201703004200c11240c8078460340c0402c21000b20b07641402c04207428469007000f58044c0c509604880b410b0a640c5c000001455071100b00000d0300400441620044064131a580b81070880860301d4044643c0540c0c2e0307046041d4441c0345041d0003280200000a54165200e4480721445d103c8601601d52a094000190100400f44014203054070510015480e1004481c0c129031075074000d02c409841e20040b54005090079250780010f800542d500c031502441c0303500f15500d641c0184454090380e201c030490031002020394140310700d008441130f40c0016040d0034407813154022000382070000d0040300c0e20300404203c0f43c0040c00c24002c0c0c080c224072840441c1c21960521000140d0510319070300492045080c5220080542c03004a400c1105a4058070100e00801d1 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 692542293 1250 692541043 692541061
    0x5060f0c0d05031501030b01140904021b0d0e0118060c110619020f121905070f080403210c0308091f051506040f181e150906060f030203 60
    0x200d112000c000d009140d160040140d22200941c441c440c07414540c10115003070300c0114103c2c0c00d850b41c2e0700e0100e070b205090800d50f10f2001c0042c2c0700d149030003000503140001080310307196088a100d000e15415401045c040003001d420100002da5042d082ca8800d82c0c81c1c0c514607200c4503840b07680c41214148843c040407403007400101c4035030082c2181c002e8000c55482c40450092803402e0000b03940c1900600132440408071424000c40d0300060f00d45076040060500700c2d10f000c030103040d0041c0000b000134440c0030841800056044000300d48030380e018030b90071a100c51031803c00d861699001100030b400c0d44504150103c50a400c00345144920750103203080c000070355800055910300000048a15051071020104014020154000d20700c0f50507003184461b41801c480c001e20603030307024901440c7c1c6499a04003040c001035400041200a062840300042244210804032288020303100340d800c0405a100c1c51580c00c42c246121400d4020180388600300400d9291200042221104c0d0001074101500000441c1e542d00c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 692543543 1250 692542293 692542297
    0x2c180a0308012c01090f06120b07030c0905031b0d02091f080304060c111813050705091312020709110705061f061803060c02030a02120f0a0302160506010305010b042405060f 76
    0x1c0fa10010b8032001060f23909003024040b50031544100001c0c00c10140c1d54080c1d116680c00c00850303501600618480801084020307201043c418115003000d040e01d101e00c05aa91001b00c24010104a8602840c0620807908207000c0340254020092aa06c100f004218569210300b219500e0750304900154041086e6200207051248030340413030610001b00780240701400305070001c140c4072a1310500440300c18680e0344c0c0038415480d00031242c10724812400204800411441c81c0c02220340d0207284141c1d140785403103d8201003100c2d501041c0700410b100100f102800c1000400c03149401c070544511040030142500b0801450f00d4090191000b080005400004000482e0400b0740c00345604c01401e02041d200c43e54025501e0704003da242006200c0c581c0a09044c800c10411a050360064202c001d00d0684035880690207584503042010b4045213804050380071400511144d4081c52203000085422020b49003040140d0701c0720070030161850001070441a454051506c0c050403030310160350f115100c01c84100307921058 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 692544793 1250 692543543 692543549
    0x80d0206070203030f06130f0225050304090c050408010f1b1d150c120c121303060b2d0a0902120115110f010b0102072c180a0308012c01090f06 63
    0x3824508c00c188020706a8000d041d582100803d000d2100304102c128040001c03d0b580c1c0945030b604100002d02c022030303054028003003415141c10000d1800356944115801c603004030750b5108845907104c5907017880001848a607035002170180360200078070b408465003140c421064600e036449540c0c61130940e282c030008c40054421020f07119042e100301100c03c100c0390321541d100f00d0b0000d54600410507900030045d039070001e81d00041d5400100a5840b415950792070300800c10b9450981c0c0c40315081c040b086070003100300482c45800c95403031100200c402c5200306108000c0b25a030403c4d0265401841800d94041d0028a52811106840003015500c13890305004c1c2d40d034840882d2800700c503005904502094640c1504070424060003a800c0b142c80583e240c100203001c0540d4070a00401002c46007004040043c54101c0641064207051070305203403030071a01c10903e04140320908801250740003004100522111600e40200c1c00e00c0c85130001094803090010030a0034050182010030b65071184503e8107080c0c603070320030005 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 692546043 1250 692544793 692544829
    0x914072301051213410c0a030b10060309030c031b02150703020709020405010f030b04020d0e16060c0c050904051203070f090503031602130f021b0c0d11010e1f050301080d0206070203030f06 83
    0xa450308c90800503101c03002140c0104041d010310200194551080c841c54040c90b030141d841111008956400b207a0340f09216969610b2101d0080407000940e0380c00a621441c4402181d903555241003603c0d01a003090a15070042107220310600c01006166084540d803510b89602d440c00094844c0140f0001d0000c2c02007800c0280103510b000007501c069070700041c0c0d1110544105100102d81580e4503800c6449030a49034004042140c903070001c10107800e00d0a941030308144280c0584424402e0241c00503c5900304903000030000314603142908a083e00300c858100600810b40165140440a140655101204540007805004175102000e510101c40d4064621186100320941d55203003a002d5810400d40010300d00e1003180241c244008081c039002490107102980b11007200c95041c03e013801580c0750711002c2c1d8003135041840519041580040c052a0440701103907600d8003a200d5060008180c5810002d159020039503018500344401941c0001c03e499210400751000b0000b5500d94021800e0607845080f0550 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 692547293 1250 692546043 692546059
    0x71b06020c032b020a05040e0421020606120c0d080f04080106030602040603140f04080901030b0a1d0c040b1602060c0f010914072301051213410c 64
    0x8840414a0910a83c0f499440c0e05030301030700d41520345104922500007080085407040104002144130400f01c00d6110340200c80a251850a00508034003054400c095032005030000c508000051810078684501040454010424800303640c011840141d004030f0080d114103804148000d040035101c00715000303014010021f005040e582d28140021f90098010440807a04207191805d1541e0501107103440303000102d08905c00e645454981d117500303602092041d410940ca417108200c03181c0303800002d400144021a640c0480380e0906a9034894800301402441c540d0404200c1002000c2980c03040c1c962049000b00c0a1911014510000e4110720910040b80c1d054012201210030350351066006408883c0030310340c0180b00014601505484134202e00603030040f05010003589085148a10320320f00c041c401030400c03d15200c240c062400403c6d000302c440c0845024076070100300401c0b02804a480c01042036640c030440102d0200401c004810383c420411000300d03510b40c0d50f00c08060082000b26410354014121139 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 692548543 1250 692547293 692547307
    0xc0f03160303030c08070509061e0d02040f140616060507020a060c020303090c030c0102150a0902042901050a0c2402030c0a0215070c0f1b180b0405071b06020c03 71
    0x280241013241112030200d044040010b032024024400c5508000000341814075104601c510642070803000d00f10b105100380244100c0400803050b10003040074100c1c584c101c50341c080c0340c0301d0503a0740304039116541d5000720710605c1031100914080300d800512541c002c10201d060b42d030718030b0100d00e0001c8a00000c0c00c9141070007480d000c250380100043d401010502c042e10300c09000e200505684000d550f80392401070344142d0620080f40042c200f072980001c3c02c41008161210981c0020b0286c502021080020240c0c1c4485180200004082806d101074282000e6007814ac80f60300107004c00c440c004000e04424a03610024084542101400c02c1901c2054411902c13403c0ca07850301c2c4440d81000c0868400351152945403000110400c40c514070840d11944c1e00c00800c520380d6038420f02c90590340c0c400c807420407040080c1c80e0b40507501007200c2d0142014490f590510441c0361116001c0c0c070300942c00345008038900418891400e81c000311401600c07140074141c8aa007107181c80d1000c020b105c0c08065030458000443c8403 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 692549793 1250 692548543 692548547
    0x603180c0919050619060f14192304061b0b011e0503060103260409020d09032a021c06060b09041b05030105011b081206030f030c0c0f03160303 63
    0x348502c481030b9004000c141d0740d5500744491140345040c1d030000030310304010401c00345100c2c590401129005250800305190302d0790010185800210b1140030350308840d401510000d5011136070042c4400e403030f5196040001a411007514038451030103400200481c8800c45101001071200c03022040d40d0002c500310a56950310014010005440240d4850342c1404400050030700c1d0008145060707136005921044000780c0300b1290480700403020413030002480280310024800015201800c600c81ca0700c0d0300841c075031841e49001083c4c4d1a09480480c4100c00103021590800d590303c910100341641901c5101e034030040f00c8201c15500740f003040000c3c592420b004020504a480b60060104145e041e0b405024040658680c02b410f020f01030010b00009000b03000400040d8070601c0e5080740148210150b81d00c42e001902c07400d01542c880c21601c54681d80740c100340700050a041104002540018019605107042801c049465011801005100d1440301403220080e030380912203e503482e6100c02c2e10003022590380c680 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 692551043 1250 692549793 692549821
    0x31b0310051f030b030a0b061e0d050c03070b0703020c13020417100507020705030a170d05090d0e04060b1803030c19050601060314010501032f13080c0603180c09 71
    0x720b080040d0500a00e8642400c0014428608a92107160700096907209400e2103c14801d400d0006c0200e180300c0ca1920380b176120101c404805078000e901a0049090031000e040c44e00680d070388242070001c0d0400c9034001107540030818621a0004407a1042c05062102c1e0410280c051900150246140311080b00100000083c000103010f44210080c00581c0c2d8000090361141d91911500e50190001c12036240041c400e03910514403844100c0e0707880d040564040f00d0702c0844070200d400c00c03083d03480780180381c00c400d410041c08602440211400e001203800d0800c910030601030151950b1041800d610241c0d400e503028000e4402c6030312030f207003203400080c1000b007102212800c00805035000e01a0400105009219020b400c41c0300c6038140c410703031141c0d19001c0110010300714a150600c0e000c40d0070308090f407020442414500d481048550043d1111440011a000070640344d1117484c5503400b035510011552070314026281c1c403504a9003590103a05080c19914282142d001d4401d40c040003240801485502c0d90300 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 692552293 1250 692551043 692551099
    0x150c0109060615030b1203072d0c1706280902040c050406090b07030e150c0f0c19050306151c03080114010e010c020f04060302180a050705031b031005 66
    0x30341444442000000e00034151010780c6c24513607540081107084d0103da00310107600700c100c20b0300000440c0c02a01c0d0000350424140e51000702c4a5840b83c501c1005490101c006031280b60403001c0140070725040440c002c1009070740107494030b0707a2750290010004610910341d0002c45d11980141082c41000c052400041069005000b000045450710314041001c0314040d003520180d650613120b201b82d1f40d56600800542c0c64686111071840350041003104168503041c08071306c0c604443c04004040340c2e0060310810400e0301000325074014500c15403101b0030480d5800030f40b9a07002881802c0e680b11108095000c01d580007480c02c00342c0d441c1ea4000805c41f04042e0701003107003412180c0351200c0c8041d600c40d800045405914184100c1c3c0010078000701c0e0009460284000b2800c00c1004100042507562540031452a41c1b44094222100314618100030782104540a01c0380d200009103095441c524040d008404501a00744640319032480100c00104030030040001c01d8080d2100038140600030000340c001d0660710003181 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 692553543 1250 692552293 692552297
    0x50a0602030c060601230c010903081806180304080d1d0904050a170d09060e1009030f0c061401170d081306110708031003061a150c0109060615 63
    0x2441030310110940e05926095400b6118584600004581e0441d0f061840b0f001800e40303130404529018810001c000000683c40041400911801c0c0540f8010009140d0740d540e20070000009001c000c08507995900060460b00c100c00c400030034140c0b40c69070181e508581c1c4c06114500040f5401030f0844200f0036074052001e0044a528119405e02000d6101036038000d007680e0280011800050070104191900b040001c0c103a0308101e04010138400383ca07201e8a042d140c46558424020b48844103005040c00605100d000b40070341641964020101482001071408102610310350904102c0183c0284803c3c14031001c0310344403542c4503074909561501c01006402984500e8410041c1c3e039005190882c402d1640305411044e0311446e4a9500c007500040050b00829801040080000307034040b1b010314080e40e40e03407201c80130710341c103600d000c600312a5031045480060403001c417034481c2503036403441c031480d01541d82c00a035442d500c42c4100180504180c1400520560610b00041150072140c421244003806035 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 692554793 1250 692553543 692553559
    0x60e010626011b0c02041b0507150506090c1303020301090c090f0e0c06070f050604030509090901050f06010e2103310501030905070306050a0f050a0b0901030b0601110a0c05 76
    0x10103440b0b080b55001e07401000b81c0c8103406900034180b8002d41841030103e0010b03002190082c40860800101e4840c243c8100c08507a02203007400610604220031001e024030320004205500782100000c42444004048840c030701000141140c4903101d41c40140020741e805030080c407516207545401c0c14480c03014002c03420041e01c2e0080f02808540c09000b152640000580980300b00550390051056990202c02c0c181d032004010340009002030310400c60248114080d50f5401c2e25a00e01c031041041c40c80000d88070030402ea051500380071585807a12669a040781007402c1c004d03080180c100108152a400300348044180307000d175090307060b4080f01200034004a00c4c5460300e1040540f142a2480f6401400300040040610300081445130794080d0740500703103250150f004c4510b055603968520741600d00c11a00c0400080c4c441044480d0a1002c1c0159034010030314220034017000102038041381030210144405080132941501080550340600c81c28030045924005448240100e030a180762541c4c0b1034031469001d9005 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 692556043 1250 692554793 692554859
    0x6020f18090f01030308060d240b0a030512130e090607030c0f1205100b0415080a0b0d0b060103111315020a080d0203100506070b19060803070609060e0106 68
    0x3140c801c0300d1152050080000703079a42140c500306c58013203004203126001007400980d28046118461046045840c800383d179600010143c20b807030240c0d03e62142c4a40078140320707001403000680105a80c5103480750304c031001b9140c8060a20101c645c00540d03102c040b90560603011b1041b00000420424801e0003036442c107100b08605150b04561001c2901454000a060300369480040508da4000941140d05040d002160a031102c0c0c4402040e40240d20100012280418990031560001c1c2602c0c0d02c001810820491444040003240c00540c40c804002d01d030900003000191168040d5021164001c900210032351640300d42d48840f007200d51180109180c00e00a14050400c003840020040c8074954031008a0b07040087d0119890041d4001612090b0340c0200c60b04049056110107025101441c020410030100381404c031001c40100b141c10403102545410720703006002c060b2000017100d45955104100140095990400200402504011990b15420b000e000500d400070640d00215440b443c4400b0540c1000d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 692557293 1250 692556043 692556049
    0x9080a230c0c1c14060403111b010f0201090b07090504050c0a02031611101e2c0607021c0b0903130303031a090702010204080d1706100c06020f18 64
    0x240704420707182030303110704545002420f200d40000c5181d207544411400107a6582d60300c00c1c1c046449207207446070303600074001c00003419800540ba034040c80e41600035001030300c200b02c80401920f201004007410300c210062000b019038404d502510b0480c0e00821011514182004010108641846290311481c204400310700305d00818811100400050b4005500c0c10b5060b4060030301259004030181ea0310940c1c6c0c818203000d91a48001101403000c0e6554201003502e8005e00e003c11220b070145031b40d0401a2045103041d282503071260100e040410885441c0b82030a48200060141c418144001c0d0402c900d0420021401101e152241c0751a2190304100516600c5a03405642c030b000b6841038040304d03c0202c10400109000b540040d001c0c9410f1035180450900007004a503201c0d20584030f8800503907000404016012080c82145920125031900c0412034203400700f4888a01006000d1610400d00f801d1608086401141c58110b07095100c0d8065407100809000040140c00c841c51103142e1541003c900304880c6 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 692558543 1250 692557293 692557297
    0x120e0601090f0b0922060e060f0703090506240a17152511030a09030302190b0c0c07050307140109090207050604141f061802040806071209080a23 64
    0x5420002c3c160b980740c01d010b481400d00c0c40311802c05c0b4082c03118100420301074002c403c140980f01000b07096504001c004e0032540300b0000c040c0c1007054074200110380000d40105010303420611a503d074200359240c2044946252403c4011180d000e1556280010b82e40d4602c045041460140c6058034065001401820100134048484000300d04440c1c1c045620140201070000a003201c600d0040b503141c404004640c5035511041a820215003048420000c26604001d850288020000c030100c5e400c500d55181988200080c040700120000420f5100c6884400c200c40002041d0040840c1c510580d41c401d130828040c860070020340000d203265004a0306c81c045000319542164071400a290729900d41d1100d080641d10100800194000e16940e407003440c8039035407980f1000601010009082c0c0c500385040c0094030b4025000701e4410f006000030055403601040e46944a4018105855540c09540c6004001e040344400201a15402318409072210f40c880d4240414560842c2000c5402801100c40d0000c0c2c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 692559793 1250 692558543 692558561
    0x20f01090533070f020a0f0b100918020f12030403030512100315020a0e0a0f0611010908161b09020306040e012912060103210e150a120e0601090f 64
    0x3030a40b40041601248650b03074020b80b582840c410398012109940c0e42e00d00d181d03162002960000b05d41824400d030051222100310090803100810010b58003a42c40070550340501d484064402c00b10400103640c561604040c000860b0a40d00560351303200e444c2d16010f005030308032070f0b00c10395081303107080029440649001031402071702e800111085107403013900010700203903001c0e62900081000c403144e05061620741840c0b40c0040c0440e8406240c490381008002820310740c1e00c40d9810201ea04110a00021a80140884101c56498041c80942d181e003030800d0301a41400524010401c0d05000c030018407610b45502650050004840030302044060f00030450a03030750102240d50001e810424903280200c0d0015041c9040027002d04110581c00001d107800d4200a402d80c8141c5a404400625100901c42d100d4001300041c514106146401400408111911130482c2e000c0c880300400604005024042d91041c00e02e201c03c1e42c0c080c031444801c02c469035245d0300c0038400e810041e070410002e090301c0a050700500210f = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 692561043 1250 692559793 692559883
    0x7030902090402040c1205160e030102040b030105150408030f1206011e03020c0708011a09060109080703062003090106060221030c0a090e07030504031d0d03030c020f010905 76
    0x7a00c0b41c0e000c02004090200300d40c400d004d0301004016a0030014041c5a11659035114990381c1c070803140d10083c00400004a0441c030a901c100414041403d0000640341502c4c8103a5101e0000031403880b038001c0902c40d41d00020400c2c4004116850001c403d00010500c5030240765104950352036a20056a540c0380b140f00d2002c140030380781c0c24558041e00c01d90107003202042090440710f801c0c2d6640c40c01750840b80500d2810509000b40303504103420742041d03010207811110a2802080305403401001c2904e40310503010003000785843d02690444680510100c0803a17100b5480d03c680d0b02d090202c000c2d030003040c2d50320415000d401491050001c0e141c240c15000407050800299514550325a4441c079401e80c8450106002d1041005001c80c0d00482d2904052048202da1400a0359084c942130180ca0b1841204030910101d00f203840440a035290441044003960b40350901103007c521541c1c003682080900c07101078030b0035032a00c0320f0314044c480000381c0c1e5884d0004020506400c1c0e504400d01c2c082c8102588000d0030 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 692562293 1250 692561043 692561059
    0xd0b0613121e0803070806042705070e06010c061a060d0b130b010e090621030c0705060901051606090b10060e0a0e07080916060507030219020321040906080d0807030902 74
    0xc5011b0041c1c00c1180d00010003803000850f9003150420400e07500000c2c000d0316440610ba0014810001c00700300340c4d009400691030140c0c0f146000400208940300c03000e4014a1240c891040341c3c0f444007d8039441142590040c111911a4036405103a4010650701c108503119a424600100031028281300d0310182c18010b9550140b0707900d502050002c06100504229041031040d0660440700c0e66a07176040c1254070090024590b038800c0e01040c90701d00080764200904c603d5041040b456a03030b8100048852045040c0d1401040c0350660074602c004184810014190003000c0707040041a500f8409007600707030303403142c0c403a01d225901c410305210b2600414026000400384000c00718900b5400394400c50f502482c4c80c0e04440d12409509a82180c0c00c015034449400318001107a840f003010b405100c240318a001c0075480440800c0940c0000b669040c0d8a24a444003e010101ea00d211411150442c2c004d48841e40091250580c0c640d01a542d800840d1502d0f40014200e40c04036401e50b205c2d000e040c42003900146885 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 692563543 1250 692562293 692562301
    0x4060302010e190504020c06070f020c01120506030c030d0302031b0909070809030d060f03020901270c02070e010803070201170910020306040f1b020106080f030d0b0613121e0803 78
    0x1003911809000d0b6400803640710f4001070315030740ea800240807120049001d01014101000301034030706803801c04040150341100b40c000c10b960b6070003001d500d4541c02c00503004c101c0b0745440000c04d0034031001074007190b0075001c0c00308515500d0382c051700214090a2064440c4280c1c0c17030100901107203030156084095000303140a01142403c0d2080708666007040400068914042c082d1780c0c401e00300c032581da00442e41c80c030b04414104203503d048078040340104502c9035a01c11500c2c8100c0283c00c010041b10a00d08811fa80b070b08511400c906c2005a0360151001045011843d61901800eaa80c0d402040d412800105407070440840c00b44031141c0c05015040c40c2004003480c02e25040342801a4100414254000c2c1d554108001c402e82240184d5680c02d41408200c43c825a00c4540282540c0c010f400518440e030103d0a8600c0c245070000845264500440d400115640203800003079562055a024903200c02d00b4440c00709280c14605400803040340b00c0c441c442000401c2d040ca14890342c110070809801800180006 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 692564793 1250 692563543 692563549
    0x904120e04020f070209100b0c2a01020a060e07050a06020106170a02030d0c03051903020a020c010503011202121006150210050708040303020d060b160b01120210140c0a0f0303050604060302010e 85
    0x83c5403c81f841100712031010b502c0b4904503001c1d8000f0015046140e001a1000c0b00d590401405100605203001c1c004d010744a2920010390307524101c2c100200110703501c1303200b02c2040d00b040c4076002c0505001002130001903a41c20009010b003d042c0034101c4132042043d4080c44902000441e902134550181c090040c28034480750545802240301070590500004000c0c841d1101d6030403402d005884595100180c884641d400001d10385040e03581d206040c80f00400040c0060040346280ca5055503045444030203813025142903508001c100b0840800c01c82c1800ba001c81d41c201c2c4085003a8040596a0032140c0c1210348403580d10a3b14400e071410008129010042000f10780300390010080c01441c20400310341e0960310b1204908551080300c1001c60f00403001450406c01200304038450050140f10a195034a0f80140c00240c442090640100240088640c000d0b088005400541d94035031fa0f400180c4003500d00d54142014140040842140001d1500c00000c1d22460b141c03103640240d0b60180d4406080a11103028 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 692566043 1250 692564793 692564809
    0x140a090b030a11071a070819020f070b070207150c0b0f0402031c230408030a08040302160e040209091b062d0c010c0206010612020a0e0904120e04020f0702 68
    0x48195030b03680b0b40c034800700759038540d000815a0038490b5582d03a000303820140c0d900760000d0024261204200c026014003142c3c0150780c10611364919048801691032400038007840c1c0c03612400c4070007000b558400042014194012524400b22840c0201d02009180300840c100d41240881c103000713203115504d40118503d035103410f101e148d2162000e0100c0714800e81d100410203d801045d90120001038160028521a00b0701200100208030b031100b507030f400d140c184211103072a402175061110800001c1030010307007814420041941500001d03070100040a8852030250a8058103d400340d02601010010540b280400036541c20720081f80c0b450842c002d00088100f1800350311500b1002001c20381d01120340c1110201114107054000788140140d66801c100017240e083d00d10702c071107541c150f40020b001042580c2c2c00c04812240388030940d100595a03400d0780815212000c03100000394000c150302c81008100100110115402034481d110400205000001c0100f60302c03488012005c1c460003444005c0042c104408 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 692567293 1250 692566043 692566051
    0x10806090601060318080315010f031509020906120a0207061b0c020d0204020c030406030204050f10170c1903141803071b09110d0506060901090b0705011b050a140a090b03 75
    0x844280300c205c0359203070401240c005440c94240340e0f9900034200d40a40c0c002c0984120303c4224113080c400315140f0b103140b0300034030640c1c401c5141554000407124915542c030b41c00c03a0101c49851164440c00d080203500e010003500040c0088415070720303110600e03000c1c0c00000001503c60481d65144c403814451030b42440459510700d6422600240c0911543c140321005001a2000c0c0c1941e59006803140d180c203041012050103203030814024241d0040380a0419400f24217801c001000001d40c0303155480b0054001503602c80c2d40140b43d2010201402d01c07903a00c3d455004011900c41010b9100700075242d88101c405904031210314100140c0c010000c0600260303400b024210303001107174070042c4045560340c4600025108005012400d200b00054802d00c1e20348030340b040395007200c02030b11000d047c410740000117042501e080c062240c690b407021a0150401074250040e86c41c0310b00c0910404d0340c40c1c48041010741180c200e2041c503c0400c06038800ca00101e00c449013990311500540d5540003ca900d0b001900394075a03c094 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 692568543 1250 692567293 692567321
    0x240e040c2102030d022b0203031b0c150a0b220906020705070e07090e0105130f0902030a060203100e090c040510170d080105010206100b3a050108060906010603 70
    0x81c1d8000940c1c0c061214129002e600e401034442c4440c90300011240102e00c1c0181c02140014020701910598000300356031b407008966041400101034003024441a0181400c440307101d10801890072808614820201d008111001c002d120300306c104010032003100c6084500000181036160726000390030413608078021090150400502d4580c0c82d4a540d810f20380207400c07004c1d941c010f0205018940e540508000003c000500000c111541000c0000d0a5081c2440420f500c5507100c5000c030004580d20707442410400e80c000c044401e002418a410b6019400807200302d0907440800c1000203a0722f00d2640c249103c1d55200c4060652142440100002400c01030f0500b14485d240045c04203492102034000003500b1079100007011201e0307800300018421041604541d046411050070f00540720000301100098407022606c40352a1002180080009403414101034400c60f01001d00d03084d84d07041c0c00807144004544480902090381ca40c011690303290402e507502031113035101000400c81e044c881c1e80300c040111541 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 692569793 1250 692568543 692568599
    0xe0114040b030a0207030e01020a0c0501120e19020f030f03040905180601060c06050709080613051c0519091d060a03060203070201050621070e1801240e040c 69
    0x5014079003480d0700122a01059243e00240000915401c003c080e01d580c002403009241c040b00d5543c6620704040d0310701c1220b062010701c5000701540b000740d80203100018007010484450982005e04280200805803051f40204025058144282400f24101518030710390f90096280034640b00c60b8100904000307100303801e1524030a0084950040511026000308802d0303480110b0203240303041903800c482001d04043e05122100104000c0582c0104045074010103c211840401601b800d216042480003429000840d41030007400f003015400a000d03001c1ca4080c0300ca010310404400c0c4040d980c11025000c1c88442e0011079144001d601080400780e83d001502605401c00c0c02e9890744c40312305a07001510f103440907035100d804104240c107104103141c04564401c08141d546801d009406911943c20b4010a00c021141744001215080b07850b80301c04542400c034008019844290b180484d0724203071208090b11800001c02c001030100340c2c5400e440c8c06950845c52000c4450700e13108804040e08580558420384180e0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 692571043 1250 692569793 692569799
    0x21612110d0b0106080a050709090207060e121c0b01022d070308040302030f07060e0f21060103051204060e0108130609120f031401050909031314011d010e011404 71
    0x2541c0342064058482c4020750501d5040400c050b066041c0207104120044c07801082041041d80710510768102c1d0b640c5400180e4520090910501401034003541407000e106003850641040c0b0300b20010503076015248400d403802030600d12440705441c0c2c1d124a050041c0d00080628000300b80f252081c0078180780580002c4480d4103464509030070103103160700076509484081010000e506082c0001d000d0b140c14440903101c410304000c0050480c05e400304140d40140070202080f02c00c0e803103400303a078419030340f15007400c00361851a0080d441d6036590034082150140151041c0c844442c403200c1c02c1c1c0c0c0030303a0102d0321180c0c4041c540320011140c0d43d00040c602c1411181145102020481c0b80c400e031100e540c01080b500d00c00408104001e07050000800d0804105494044090703441a83c4460413410f4070400c807120b00b142d882d924036141c514020800e95109903070b118080061002d005001c10054484280c8680c005114600461409800c1c1c4239109400705040b803045d81203a6201b21100402c94421504180c2000d032 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 692572293 1250 692571043 692571049
    0x1f0e150301022728060e0d020102100f2003070905091603020a17162309061b0d02030d05010f06050d11040b180906040504021507021c11010e0102161211 67
    0x1030754040201d0b60101c0c4c000f0311149500115615005800b079401d10f842d8115039000075500d104203a406010140d03200f1606d55601c64030b401802482001e12204044200c2001d00c2b403040307510580b113040c082141218001802d0422540f0307c0c0c41110400100700100250319403e402a5200d0300201040006000f40e00c0003541c540c0d0903003406801c04118140031300b40740440141141e4905444012500c00a039880d51b40d0034a0311048500c409800e41d070a54640b0b00c40301d6808941502c20b036144c001c1e40101c0066510241d4000058580300394048020700540c0d0742c0d02040d10510006008142c0003800c10415454660b800c1d400402c400819000040e203030a5440a50031a9600314440c82c01e08440d07000c01e04200d03441e00d5942140c00c840102c0d001c0101d030520b6800500382803403001d401c00d11508003240c0f02d015592034807040b95429004241d503085100e1503183c11601384403001082c60200d0000c002e040015440011507801007160002c054024504080c1e061304103aa00c15800c840347d5102c40d900036102c0c0c03 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 692573543 1250 692572293 692572339
    0x1703030112031e081e131502041505070512090603062103030106030c0207170d0f03021c090203100504030518030a020607060b120307050a0b1f0e1503010227 69
    0x40490751000681e0601e0f045001e600d20701740c80c1500444d5160414040c4175485031486009559004504420f0f07203420380b2030750f006170040d0b81c030205404c56045440b0385015002001010024403410036a2031075001d01510044030301400305050740101c014400203860341410750b520ba0210342c180500080e04102c1502840c038540c4240c00040000307880304041800150100040005840701c006c18a44006104050955401c0301400c51001c010b81c8180503038006029504481c2000c4036402001c0401b980c490418001d42440c0404a0081c401c41c0800e0340c07140f1262240501030703070741595000c1c9000b11030100d40e01c210540081203607060050390340c0c00006075030300380041000758414074022560136100004c004441403104518030043c2c00c01c100a500042000c80e46541c1c49611035880d8045860700c1c48204089092205a0302524100c01c001049400d000c482d5140b081c1c20001c1180307068890002814243d0050080303025102d0703502c181c216441c00390904100e41070003001e0280e04008040b04000c4610b4 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 692574793 1250 692573543 692573597
    0x4170c010615170603030a0507030908060a0606090801140a02030c0c10050103020406080a0507150e0414241305060d0803040c0305160308030718080a030306050a170303011203 77
    0x500b40d2422800e00a90410203554422450b465150214075042000c07940f00e01c2090300f201e00300140080d0340c600f01406401c000000d4005030341210114641103121000801c1caa00a00021a0fa071050019a280f01402400c0c4034034000c665680481d22464088006900080c010520044082c00548866182049254050030943c44045210351550060004480850304131040d01d41200140740085100001d010048403c0c1e226070b100e0103900c0c4030044440303a20f4400c1c42d5900904112080c9602c00c01400340e6801940c40f80906500609000321480d90304451901190304814000941d803900300392079100e0344e84440b0240210b85084260380e540d200c03950003142d0889251a000fa802e0090000c1007003114600403c0c170241341030860460315a030250b80002020348082105940140d5075009274940900c0080c50311008031490221145406409814140207960251420b051b0010700c0d050300d105042508601b410103145140d08211507031a01c00031014013036081c8104081c05543d1100f10320000700300 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 692576043 1250 692574793 692574809
    0x91003110d090c0806220c1206020a0905010801150804081e07260910140f0a110703020a030f08040308040b0c06060315070c050703060203070201020919030b04170c0106 74
    0xd190040c0c9000d100d40821904000c4d40d942c0900c040040c0c05c149103103030b2480c4880310500917011004a140c0440703030a520b07411800801c1c128040b00720402245801400a0fa08961a50703c90181c0b61001128503c0d0240314140d4080c4c803602c900c540440c00703001c42681241c06128901d162500e892032441094100c2e420765a11031f18009160414440a00150b501c0c801001c10003102c100c120000030491802152b6001c0c7c4550346020080520501501081800c144c120702d005482d01c5039018000c1c01a0004c00c4400c021646144181800090200301007081d83d07402000c20004600b141c455800827920760f81c00311403040d020000400440d40110141c0003c00000f4481c641d0ac0044c02d40d110305010000c0c05150003a400900d482d602d80d101051401d07800205031401855400c2d031410540e140807440d078001f5100c01c4c0b001081c81400f0340d040d001440740400503502e020151940c0900000401d5240c4405000080c0741008100011418a4506448502c0700001030425840440850031104940c1c45a99 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 692577293 1250 692576043 692576051
    0x109111513031a070503130210052205041409060f061903050a0c1715090a0605150f1509010e0d02040e06040615030507121415091b06091003110d 64
    0x1030001c081e501410750003000d1740341240c11805d00009401010b405c807500207200d00d21114945a0b01c510640c02d1b85d0110f820b1072684640c5000200304c9005030b11172400f96502071400c08803a01020705e003000801e80240340d8200101420351b1411508000c1110203882c095000c0b54070620390350304003046c00a90024500542c0030b03000c0b01e007151a00540d96817041d4090580110030408403180210007042e5000f21500240e8041869500e40348481d0412008042c001c002a2600b01800285604000780c2c04001d00e081e44c1e9513008080b80020040c0d008640c07031008522540402407980d00703510581d07180c9c050400190825070103030b44690004045d114500340c80003903644041c003000180041402007404c513468150400e0b2215040d91140c3d03480700c0d41c0d409008280c8200c12a01001c01940802d498010b21010082e03402050600036154840c45003030390b001c00580718a4540f02035194a025003261855401080307145080d18113024800d40c08107040d011800d140c3c1e250507440200c2c00b210700500290008450000b = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 692578543 1250 692577293 692577323
    0xc1c0306120501050718080a0b0403020c0a080703050f031c0c260a0c0f050904050c2217071223010e0706090803070203060f13060903031d010911151303 67
    0x1c15060004e0006c000b00f881010080040200100d0382c010b00741d80041d18401580d80d02d04041c0d00c0c00d80d80107480e6030040c0094100040c0010f001c640b500c180c82c0310340103462a0300c0310100310340e03524040c0c40ba03101510080480c404ca66032034140d0024800c4d18050400801580c490786400901400a2140804003182c04041050080c41c0e8850a01c00341020700b48045411a51407004110b4020b10680c14051661940400d11a6072a0403c1d038156600610306240c00400c220802c4603071180d9882503032035200300c0509010207905c0200300b42095403085d4803a0961102e03691140f2403802c03000c1001340580040482c480a00358020700640060400406c0148919841c00400408601080c1c0c08105941c00c1400402b0060b41c0c0442c2c60343c0c000200749000490ba884490b100040c2c0b10002c00020111450300c84000101034154101501920b60082d400140542d0641c40e0342c2610340c40d8500426071150600407002614151f0035a1400c540c2c0303500564140490300c0c0a6201ea01e400ba00180d4591116001c1c05c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 692579793 1250 692578543 692578547
    0x18010b040903110d08010e07050a0c06020a02030a14090603130303020705010c0e030f0f060106031e0c0c06050112031202130801061805011706010603020721120c03020c1c03061205010507 82
    0x144c5114a414a003020556250107d046000400500303078000700580040e80e0980507203c0c041061016800c038000f1584d0705074840b0069500d82c400c05042300880c8000070f81125070f2000c402504c041c8080942541d281d1784d01c00c1c02d9800000c001410481c10301d40d0078414030020038001d10420f01c0022050f1a4003020068203000c2614000480e036180388254421203106d00480d80100d0002d04490301401c002c202c2ea659034082103484034881c2c040205880c900401c410f2410351004a460542e401404100b00d540d8803200c0100c460303803101001902080c9002c00d14a51540305030700500f107000e408003d0f90609d07a1035201d0242920043c1c1c0c02003005200d0240d0b40c0002c0042d1748616401132440841200d00c06161050340341c1c03109414810b181c1455404211a800d2245c0078000510005945c0b41c610f40c0309034803c5010300601c1c1841605141c8034586244c041c2e80500901c00c03204418111801491041a11701c091080704000c411028105601c2310750016402e1100800b01688510410021449190250b00 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 692581043 1250 692579793 692579803
    0x40f1a0f04110d0902360604020a05090d0305160812060406081209130e0609100608030403230f150603120706051e070302090f061218010b04090311 65
    0x2525201d035207042c080362802004a070840312540c00c403c0001c03409040500000e003040300800c1e030b03a941e20244803e441d03007602c2c1c0b43c040c452006200c581000880d07807500703000d21040740100400000810000c0042490034500301c00c0c1c147e0034030301c01c1c82c02510345800e83da03551118014030441190340e4040800c2c3c0070001185030081903032140d002d071070401c00c0d145400320707259803410030541d030044125000510a000761107103484184504810f002c148148454841c6040d40c0d250200d035080014051641c0340aa03400050141c0e0741100c8466000b141010f046840742e4429054040e0981020401d0550b821034800c000c0c00b030783c0516185034000d008a25100301150451400080a42d0303c2600078194007050046817009031840325410041c00a8903644080404120310419140c10300c01d0844c0c6010448400e074190001c0404284c182e9003014854400020311007940205482d100000344114000790b030107080c0f4510764850313208110000c580701c0700740c102260403240008802e030300040414590880041003080 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 692582293 1250 692581043 692581069
    0xc1103010b2823120f06041103060f0c040b09031f0902011409090103170919060f4b0309020a05010c03020d03050702150901020c010c0c20040f1a 64
    0x40721449001e0204120070000d000c0810180c1310303100303080c1e5000c05880c0401c02e9102070801502118000d040c9402c0039040840030081c118400c0c0321f0200000d604044901945e07004516074802e5504143c200b8030304e040150000c40220350180b052003449a40b01d46000c60640c4401c180c00000205483d0034000186a00c1d0440a0f90804900800c24a4486d07211000c038a41100e82000080c0c201f034021b102103060303900c5407455080d4031521100b2035183d01005d490340001100c40c1922900c41558001e401915920300c1c00070241a8a00210050380d20481b035100c40c0b04200c00c03e900115014400d04081900050621000800096807040f03104118200480000044e00c002d00b44030110280507a4000e41c1c0b90214103c081c101070f140c0c404980954000c000a404036401c02c0600300592034208410760003500f0082c5040c40c1907092601711144a8050030b0509002e68000b40c0321540c800c1003011030942c0c0040b4285403604580c4d1081c0c2c1e1000d030f0b1a240300741d091018071400b02c810203041f035a00304240c2c507900c82c2c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 692583543 1250 692582293 692582309
    0x5101d100203220615090b09061c081c1b02100903031e0506030d09030308040f03090305030f03060102163215070c0914010b0c030f0c030c0606060f07020d021305040c240c1103010b28 80
    0x37668034009290000785201200300300400c04117a52009103021006480280b003404544002d840d0000d060605d60342240703101c1c0c3c2e0190708640ca021120601246c0c010403911014010a00e100c012030b020948a50030081351501070704000280270f42c0c0741d482516580c8540b80c2040c2c0407034048180040e030b40c0d06001007800d056103003203040860b604194030146154000d415000c1c003440381154000c10039880c0107a5000b0130800401080308510440f110000c81d40c410715040703a2084800b007010404003410b20611071461806a070341c80d04e503800c200018540c0c4d03114100301d8440b4801882110120501d07a4000c0100c0c0404e41c01641e100c15000b48403601e85807026080610401041c02504400b00c07812060f191b4180c1c0454070007d0020450000c101b541c0c807009080300b80107050004000a00c071002c01c20008855070941030703040440c3c48041d04045071a8044045001989500d01ca4001c955481140d140003100240009000b4803113400040444022142001e0341130b902d0701c03d4001602c1c050b81c0c0e21000380a48 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 692584793 1250 692583543 692583581
    0xc03050c060a08010b0319020315130525020106031b0e0a050106140703050403020405130b160c02062505101d100203220615090b09061c081c 62
    0x42c10141c54040c050058844013400800000d4103400740c0f148040b003c051801c4d045580c1c0c10070409100007101c2000c8a24080d082050941d100000a403040760f1090124010411510440440d0001c0d00030f06030750004115902da403000320114007071b4038070007043e44090260014868600407605500300d8006101725101ca180800402c60680c1000c0484e0820340540c507207554807440341c90241c1e1180500d400280d0024904420803101d224400c00360008140034460800ca680c0d07074118001c11443c5018003020001703002c01c0706e900c01824080c2c0504119400100741c0e402903022541041c000d008524000d40d5980c2c089850307008420141d02ca001d4900f01e40c8080500d200d110704001036584e12058820080540c1d0000c00290040c0d204200d42d03030a01d0072042d001c548074807681803080190104040690241c070001000040c002c555224480c43e40802404041c0c3d50f0750fa00081010302e02038200254cc004040813021400155010010100008020078040500c0034030360100c001c6510b8400715200006035 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 692586043 1250 692584793 692584807
    0x914060a41070f020f280305070b0310030b060d060e0a0209010f14101806030b09070e010824030a0311010509120706110702040204140907092117070c03050c06 70
    0x643d158458141d030b015505082d14400650208172440001c1c0c0a501007581c05107081385814500c00c038010200d0740030f4422140c10584801c2400b0f042d11043d207200c851000c0c012070400008107d40d50741540a01c0082092286200341e84440d000c2d600180e00103080c581003100303201c045180ca040301c54050080103031880015410050344806000c0b640413083e1148407490f00c0c0c4072009200e662100d480e0f145801703000702c203176603640c0c40900508203000b1158840d41c2c01c100081c0446104200801440b84140e460080503129040c40c103290b4400c41c1600e00c0340c111141c40d0031a45840412030780055a2003550b403000e08501e49511182110809003481410307400c100c101c00c4900000c10107030b50441c0d800074030004884021003c400c2e400e2149180080d0418000b2400160a00040c4c004118859041c1ca58a1a66540d0302c01201e580442c0c4c00340b044a080d07003000000c1807442a840401e1443d105100d0301c0403000480c8030800c40754209103803c644040100905004208081c0101d46014006440c500d041c005 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 692587293 1250 692586043 692586053
    0x11070f051e0715050906091503011a1620030d0909050a09120518220506030d0207121112030702310908130e01090c0914060a4107 57
    0x4803e2141008014012840c40c5041da5040215101014000c04400d80d69000740440c07a0301c1d400034070403a451281e80d07000010000e41c0800c21650062081c1c00700200e0601e840e0384403215040b00d116811b5044201c00e032103611603101003204031516011500e4061210f464842c2c0d0700141d50b00149a0740c0d10f14180b40000300064040d0750064616081400d00b08d840d40500e506490100c25207001140d4000d9940f030002010010410400300c1c4241d25100500540d650361047c1561250785001c210700507405017034200038049202907111031407886119074041d50f00159000401440005103202c00c20307080048c80d0800c62502190741c8000c031403800000324401043e20304180d00403030035182240e215034803441088104003540e002c0312401d40300340c0c50b020030300c0d901d03180b5000c100c050074003491019510b00440ca030b812600402044040310000e041840034a1086000e0142030307000b0700c20180a001c1d0074105004085c42c40800c021555050013205048850341c0d20800410314000712030300001010400180020403 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 692588543 1250 692587293 692587319
    0x40f021306201c0e1008042a090f05010e010e0c0f0913090606060216170c12030901021005160c2901050907111011070f051e07 56
    0x260841c10101816000b1803075040d00401c4051034502c040c040c2003d044203030030140841c40641d141c0c0c1d68600c3e0604420300113102081100c0882540810400d6001600180d120b59070304182c103200d101100c0303c00c0c0001144205200264000740241521844403211940c0701d48a00c0b80105001000c0544030b514041207402d4251004c1c20968444600051f20903441c1e0895007159000790300503144030b41203102c0706071443c002e10744460f00b203400605081d000241c2900c001780606078059507080b1280c3c00c074600480b941c2c441000350800c00080c0141c0c610320141c1d41e1404258100035003080d01544da25501d8034002810b00291050140c0340a14200500c00194880a00c18890141d9410400300410a0f41400d0036041d0800c2080d1214442554094202c800b110b50440e04984050f40c080d0a00d4545000503035405803550b100c045150b00008940100f802030750007003050030152440151074410789031101c0d640101000003d83d0b56501106554440722052002840c00c00c0681d4003400c07500d818811030201e41 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 692589793 1250 692588543 692588549
    0xb06190816030b0f06011b110904061a0103290f06030f070318150f110c07080c040203090a33020a1805011409010e090405011b03020c0a021201021e0306040f0213 71
    0x5134403c08400c004011230b01c0c00304ea0024600070300348001c52a0610701035010341031303480c215802c42411048880d036550081c00340491004040da134a500d0705c14804c0c1c803a080c4070820960f9560180101115a81da600c5540c0254050503810a03500201d02d0184409020750754042d003841d01c0d16044400302008514081c00ca080818076085011601040d03005844028003105c184000b40814009020402c000380041c0c900129084d042c00d4640715090801084101c2c0011030f42c05020703070442090100000d0f800d003000088885188642441c4058450315401450741f1403090400e0568001180c486040c0c2101800c01c03298546545110242d0401000a01e09000c0f2000f16601c0f407000300300c95800d80c1c00b5011030500118040d007031404d030b4549410301c5400b812603480c07071030b12810840c0f0001e12018070030300031101e6614104009241001c025800e000e2211082803401d86503540c2031240b0461320800d002c0e0b411050484841040d121300b007560812040380e103140002030a00c0d104111014450407074a00d18821 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 692591043 1250 692589793 692589827
    0x20c01140307180605040501110a021302070503040915090b090601021002030a1107060606030c050717090d021215070c050c0d140f06150901030b06190816030b0f0601 73
    0x89498450702511404525403c07074080c40d105290204d030b41035000780034204450003680c5800c9101d210714400c80d00c13400036001c040e40100a00b0490703814800070b50014111944a003046900c0c00d035980c80c401d0200c1c0c082558510440f050500c0410080c6c1040c00b4420b07560710104c508184031300381540040e6982c0c0d08502105129900440082c01e00740c2182c0c01201904034a40e109903a0b0002481c1c90f400030f180b28040c0d10003183c41c00c0340034031040d4820400d5410881d4409a0810002d0202e29a2000c0340c000c0703450103a101d000184d40000584410b0018211103014000915100c800002c8a00c003c400081c2040704000440b10604081000002c02040a100070369103001d4403521800c000d03140f8a0842c0d0100c400384142c07510002ca02c500000e100b449540c91042040303c0c102c018041013400d4600388005400800654007040c01490303c10900b002c201320034140341c058159980e40181c10142075034640180101070000030404d1005200519601c602000c0c0700c1a00c520740000080d007400608410b1110b = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 692592293 1250 692591043 692591047
    0x18020c060703200a050c0f0303160c020319150c0816080613091401050604060b0301260706020307020916090e0403050c07090506010e0d0203060c0c0106050901090209030706020c0114 80
    0x49402c10641da43e030038207803007090440d41e180001c040240c0b00c2c0d481103001145074880e4501d400c602c241c0c040250b900030a0000e2007220351031140081200e03104a8520280c1e4940100e03140c030074990b4418402c4450040c4030b0300380000000c05661035001200c181d68800c1041c0000682000081c418001c2c0014500d812410440300320380f070f000c0100c1c0c12040c10002260005191200d110700384480c1c414078a4010500740700901c4240c6c2e401043c0000d4034800d05c01c0e81600d90f41840148502a200004100c40c0d02091280c80d400b41d181c40d0400c0d1411505a00120141c2c100140780b0042d4102444429403003c40c81600e800a00b4a40c0740040c0603d034144185807921400c1d84c00720301014807682c12622003c01040880701141d864000483c0100003e45407140816448614810a806c041200c1c0b540590010081c1501c0d99902d0b44071242c6a1103c011380d4122b550b5800c006c640713592400641806800001801078660b020402030500d820050780142c0290341c000020300405a0380700340030713441e41000a002d0301c1e = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 692593543 1250 692592293 692592311
    0x2070e16020a0204050c12130302030703120b2805120604030c020111010c0f090509040b07120b1504030b0f1506090a080d020c03100c0221040308040f18020c060703 72
    0x28240704180394029401030400040c461811311846c0949a40001890a05180d407108854141107440c42140180585c1040c1300c254040784c003400020f1180c02d402500454103402800004003901048035007550084059403000900d85100314584000d090240c07502c0403144c000d0b2030015a1008000c0c001010440d0701c002c2c20045904c20620701d00c2000081c4000d100980c841200a4002400003401d8000900001340001711464240c0d81351b80900d8203c01001a0f81e1100c45e411a0724524040e81c01503803a441f06014240741c1c99400640d04400c1c6550300e29510785055207410304800b000500b100d50300d18490001d004161b124181c00701440c840c22500542d441c007501010590340451030748801068028188203003241500855203443e03081c402c90680700c0781041d46001074115105070304c400005138400c0c1101801e030002040300c079030030740101d02055041980d2640c400040d5846a00301901100d1058004c102080300040d0782856540e0007182941400c201c0304000740d481d180101450b0406450b05215 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 692594793 1250 692593543 692593547
    0x17010f0b030f031804021201080c0301050c070b040627030207080f0d05030a0c03060515030a0f2d1506021f05062209050717070e04050604080d0b0a091b02070e16 71
    0x203c018081b007c400e80941d6a42d0041191034049580d0a076000c3e500707100005960110755000c9601c040e50001603082181c45544071040201003507648141805840c209018201c44030703030341030b480c82842640140407036400c2c82021030800e4945030300100c441c1e00c000b1a500b8403c0d0840181d0350b102007805030000340c196240f9411005803020b94410354200480000c128046a0342c20021071041500c00024404001916039101c21211940d08900201d411501c2006810707070b521010050701e01c0900c070301166100e0541010304d101120b95001802503030146012800c400c85940e0242136901d124a010002031a103000410000c05101c0710007a4802e0100d584800c0c41410355008540f420340000448541940782c0c00861020700d0440d400d80407510440d00000340862100d0703002c512441c2d01030090034032901e45580b0b41c0d002d500444041c0c100c1c03907100c000c4085e068459040300c0300184031989003c0b8490391a009900503c00c1c50240e203500315085003a043c046440406d5450f5040300071206180300c242d80200003 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 692596043 1250 692594793 692594797
    0x807081e121305010f1d010f260702120f0406030209120105010b0d1118100c0f05150c1303120302070c290c2517010f0b030f03180402 59
    0x100d804164000ca00b40002640011908042c0c54003030700d40d810103d900403801d44003007030098500d0008145160f1109165445000c80203500c801904160b07144011000150601c00c280d03a013010304803841241001122a41001158102c02c0d9201800386450740e0070780004040e100342c0c0070781e0f8185900001c0b030803202d807101192002e141c00d245008000c0e550b101d0100046591101c440c3d01c280b2030824501882c1030110904603642020190342881030b80e0003031024407010001d4012030800384a19403413503202182070411101403051003a07001e0044142d891a01002490002c2c1c984002201d00340a01d1400c0a41035400b601502d401100501031000c00c00401c802078460604000c00521150700001110000000b603070103010a526880e040468030001218514025105042050350042c151010585503690050701d80045180610302401e44514010455290455504466030340d16441408245154403401c000001c044004c0c0605029411440741d8030b000d41041c00d620307212000d243c001c0d1a03a0f2581 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 692597293 1250 692596043 692596063
    0xa06051206091806040b0106030c03060f05190302030312010e0f090c0906061e03060a0518041704050405010b0c010506010f090303030e01060512100e060f0a0b0a08250807081e 77
    0x40301c0d0139240074900000014000c0c032401d0003117400e020650900c030b8040d00810050702c08007a5520103039890481002042c14107480f4544031410308000200150710180020041c80884170085401035151080304007001070300030710038043c0d8103401c800d0103c841008648580352000445e01c01581d83c80e1800080c00d20700c00c00c3da01401d040c03c0312098400c05404c110280d4410a0200c0e118881d0a990718140003440f9507103c01d0b511031800400003e00041e100b10f0400805960285100e4202078540300032808072751080e00f040c070040c01d022980c004088003d000b000e13030200013841d100c07032207607580361000e0310701002c80c003000341416202e0200b02ea030030350258002c5004043c0200010030541d00d502d0030315199414084e04140a40c1485111803034000009a51342c060f2030840c90011b416510040900c0040084112095000e0345405000031800000c10920680b000c01c044d0440c569458100c0e0b40e410300c3c440b54440350080d04032650421002c0340c041100546102d0b400020203a0b070300070640c80c50800180075 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 692598543 1250 692597293 692597341
    0xf05061c0903111608190b0609040804090207200a030b07030b01020a230f0d090302010e24210405060601081003050f10060618031104110301080102090a0605120609 72
    0x40c4002c00001004c07480c422618540144e0754508122404e003440c41c0c64255028108044040c0070a40904042a0f000d9200780903110b05130800303403140400b2090b84c0c032000d000d40d8000104000b0030620745802e110aa1000c804640c601016031a5175902030203500000c05010074142d481c4030b0501203900a1045c26a00c990003000c2144100070501c078404a44802580c601051060052000d944580000c29640d0400a0780b2410b42440c950303401101d41061041c00b07075410035000071180a07030300030040b90450400d108681c035584509410b40c0808010301d100410749005880c031070601000c074501095864201d1380078a8003032440d030340c1c1001c414074141441d44014035900c20a40c4402c1c1d4850041280c00c0c6003840b0368400d020159075a18119420311442124804080d0848400c00000d41e11215807180d0000150011610840309402882141c1091740003d4050350000b0f0500c0302880c0c46c0b00001c0141c422400c00300e091915030401c07900e0340f00d8010601d40c065810f42010805074111610082110640b203 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 692599793 1250 692598543 692598553
    0xc030f0908120f0106090e07030e031b0d170f0c07080d0b0315090d0807020115030f0212070317070206070f050a02010206160c110f15040f05061c090311 67
    0x40d207060300d000c0e44a80c24040c10b41810300301150008620442c403904031491a580c1c54803042c2041da801032501c1000d0b0801007495030300c11111281403000d00140003002d01c04031054031944074428200741800310341c42900c0f00300320440302c090101d407600d0540c8a0b0045103224243d0510341d10810749034802c2c4100303003000d4505c010110300d03807101c00320300c0e00074440e0b241050b01921a1100886035015000c02c00745c0b1045050380001440c24181e611440e10365034042000d100102e00240400107040c031344c50f000d400c1aa01452800e8004041d03086c461000f48021211740010220319146440c0e0710a500080c6400750501e0800058003c203640e11030044e50306558016044807040101c070b1809550310080c19000b240903016000024480c5a150700100d10b808095890300c4100c1d03001550355031000c0e0f29444c4016444440d5120352030803601c07003502c603440c1382407a29811035450341445e070050742d01001039000b90321a410400820700c26030300b01d11820311511520400031460300190302e02511800341e27003944840544a2 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 692601043 1250 692599793 692599811
    0x130305030f0706140103150213050405010605070203011b0e0d0303150608090c0f1e0411040905010e160f050a0201021224011e0813061a10030e0a060c030f 68
    0x7200003080002e102d840b0401c003c0981440b0f00006803000d00c0090300d108607145400102c40415001491009001041c070f0205a4031b8400290860b002a04070070001000450700d5811424240316a400b10415a480a00e03510744110380180048070703050905009103140010f4204041c0640c01160b1301038070313800d42031450540314580107000b84004c50300c0101920404401000504240512010400014200802901500841700090310700c45081a4009039502d0103140c21142410103070021b084d100d000410039501d402a10b0f4003500000c2c0820030081750340c55070109515002146240c80d0707040750074400d45404400d10283d00900070060045c22a240300e00c00c0100919034841104003a92051000350218500c1900460341009142500400c40580001040340b5500074449968407003c841808043c8500c01ea55031016625407501041c68400c1c044652215450b06613101c906110755458200720b810040e40e08140d51304039018010b4220356441850016803403080e040761034260741d580028800c00c10 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 692602293 1250 692601043 692601067
    0x10e0102120d0903030623060c0c030a060b01032012041505130308011401050f0c0f030c0102071a240f0301020a0206010e011208030a05070203210f0106022113030503 73
    0x1c4000c030002458070b44045008040c813013040c0307117102c0140700807c400b20080b804d1042d80e0f4800c5141c00030710b120b0b507000c0d5402c07aa03081003801c006910030345011030121044030014083e150001d13003030300385c42c029028804000320100d415600b003407620581000b410340700c41c10301000002c03480e03428500403410f110402a066200310004d181162003030b03a4100d0325a07600c0d40201107440380c2504090024030100580440240f201001d05031306a401019a48a090b000c4039562950340000324148569401003100014000d00c014138444813a8140c03480c076100d15001d4640701c0201320512110800380102224240181c680301c0f0b2400303c80303c001d07000b1582c07010020000f17561064240715820703042090b00c0001c46d1042c40c0c55400c0340e040b03030b1000f0b9460031900c82680010160800404003000c51000344403081c0c120b00c440c0240c00c40c05032820707400e00f154140b02d56400c19500b0305070450400e540c41114150301c020a10b04901e8070a100d007070426078943c29041881c200c504110750010b08544008035000b4460a = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 692603543 1250 692602293 692602301
    0x306033711031b0d0609140706090807080c0d0b04170409292407150c080a0e0d18150e010206090a0f11060909040503040512150105010e0102120d 64
    0x200440480340e0040f064400614000402840150019601060034000403076940045130654851004100c00c604880000c03498007000340d11038000203c8812042100180c00c0c01f1207009405180c1c040d29841c882d16000c01e02107914000010b0505451000113418803801c0880200d10540176544907a8490342c400360398010307141184020043d8048441c4003034040c24001180c0702000400760000450340d8001c0446a8200800004403104420800403000002c0c40c4412201110b211440c1c00a6030b4010644010b04102c80104002e0700c0d00d10749410b66802140005d5400c0310b40404c0e10b025001c1601c03445003002004044e034480303c54040c401103804050350300324a402818444c20703401c44103169103540d5103660780c001c040d00c043d0080d605140c0003c049010b41c016444c2040c8040c11180c54112003001290b881c80d01194141c88581001c07130241700c01c1c0b030007141510409540400a159a80308519504078001041c42454140540d0749030030181640284088811400c016070041d4598180c030042d44050 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 692604793 1250 692603543 692603573
    0x409060908090a0f030c0608101203120c030b0f0609040e0a1214030f070f032d0c0c0b18190b340c050c1903060506040203060337 57
    0x102c040c3c200118070402501004001c40380c014060b03034a0a440e014040d00c403d00058000c20310451450301c00b050b081c01c00c01042500c00e10039641c049014945900480886801c49541400c150500040b41300c6070f581d000400c9a108030440710641d0703070001000080d00034a0103c0010b000341c0100d900032005d1061000c803503642d240b060303201e808440310402040300c6644070407105628075205c5040802d844501c10410346800400c03604001403140b1302e1000c6030a542821030380024020342100c282900c8201e45000701241c541190402e812842c1d1243d540607209a001030a10340041c83c03400100360305002c10005507003100c2d080001880341e4002c034205103000107800c0705c00da00d20014414205407100c0d0040509001e07101d0101e660050180e48403c11903c10f282c445043c2d90798411403688060303603510005804406040c0380000300b0b0403451890031006803a0f0080086200b1803052042285907207000c1001482d8851824084401c0005120b1070a6030316040141810310100c0f14103801c0803c400081045e1107 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 692606043 1250 692604793 692604799
    0x31902040f050f040b220f0512030114060c0c19090b01080c0a0c020d08210a09080405011b0b01060c230d05160b1320031209040906090809 61
    0xc92200500003005407801030700c144030307031030b03200800240481c2c0700c8203a20350044078000c03005d401c03086c0071015000004400201907840c480001d030070208010041082e0750401d01614046c0d81198500f013848002c08492900e11402500c000411240c001d00600505003090401064442050401c4107404aa0044c9005801c281441c0031800e001c19801515014400c6100907503161400154500071035405220744401c0381c000391401c40314000205040c0c050000e001c20026024070b08860076928507100d06c0041c10b694405482c2061050102e0014000c481c150713442030800c001450740781128800004030f104000780001c11480004191035900448080040f070282540b52110001c20041c40801070044c0b03181c207901d42c0441c09846009020350080c004603020f01c03002c0d52040c2d80caa140c1d03640c91041100c01c281c41110245044040140001543c510010744580c004c1c50f0300000d0340426031f00c9001ca5480c0050240104d5040c0302580e80e5013120500a512150034003080a10303203001c00f41c80e000016a188 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 692607293 1250 692606043 692606051
    0x3030f0a1805130e0307020301050f0901060b031905070912050d090b090d060b181329010b0706090503070c0302041a030a1b080a1407060519030e010b03190204 70
    0x940e00240a00c0e0140e80000300211241c010f0041da01c0002c0c0b1840009404034001402288056902031041c50f10075081010b10465620300800310b0f40c03c40308540c00010301070105001380702c2e4907043c2810021002e19062000202501ca1002c20703030340c2c0c41c003541c40018a0a61000c2e0761041100205909180305c800f81c89540110307840790400b40c4a40503551a40b50040321680c9000c1c040381103900800c09801c0054120124454000c1d040310740352000b20313003071303c906125070703d8001c00c0005c015248041c007040c204003202001303004175540904001c18401ca003003805000c180b603024400998400012981e01000b140d95556a625001d860b50302a0721090344124034006143c3ea171180c41507850100210020301a141c90712080c0c0c1e03200f045031008854a40031140c0e400012842c03140030048003400b0f601030228106801e0004120500c2c080f080d4101c0303000c00000b40004200c0015040c082441c0d06000e0501240c4035030b000541c0c03030040c00618403541c4c0c188a14000c00c6101c041c010703030804801c0e0080e24280 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 692608543 1250 692607293 692607317
    0x80d0903050c0a06121a18010e09010207050a1103071d0f09032104061b0203030108010b030c0913031715010212160813030c03150b0a060e0d060b03030f0a 68
    0x2120041e510310801000c580e20200c18030105c5204e07804024095415000760005d0070f007040104117291400420f0407100d00c5000f005100e40b844d2028203a0b48a02010000d51401103280e881d15100c0c00d032500020584003a80d0906d0340c95680921060700944510151840c03000582440c0503451034042d02c00f060510540c0010070038598001c02101c081202d01c202e11583c0c1c0103802c980c1c0b071084100401c2a22140d584191000e58030300700ea003500848610135401562039505140b1240c0c01c44d600c1000daa4801c0e40700b072407004030540723955501c00c1d44590424074028183c1e0702e50400b950400380e014146001400707844100100c01004010703102c40c00d00700b0307400c07a443e02c418011840780c0c520a84003400003116002e2000400981c50784024103400e0014102500c81d6076496039040d902c82c40b031760000c84614200e042c3d602d20310300b1140301c0c90003041c0d0102d410300341603460803201400c80c20481c508240182d2076103159409000036070b042448610030190890b56104007660030b80f400c50300000c0d0b40703500281b0188088 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 692609793 1250 692608543 692608549
    0x7051e041401020a121b171c06050904030f0203070f061d010204030b06040c091503050601080a1406060f040f0f0806090f0d1b08030f01150c05120a0207080d0903050c 73
    0x41440641c2c0701340120007074405540e0559040c041010403901c41c5400e85160b01c0015051f040d1044801a43e905040e21a50341040c0003040c80040c41c1182c010030b20b008030030804d40d69101d84203a04960107041400c0c80c0303c92880100d04501c14064064071101049100c0170401a80e0307480b184518210640c08024012510202400d034852071002808203110781000c50418585a8401180fa4419041010096075123461414040c180c807006440440da840d02081125600000c00c107a00c841c50a60420074412001e12004921001419160042502103104040d1240c48000c95000c0c141015200310601e9480c0b031550f020020a00804006015480105807038000001c2c40200e2038041c00b01800608840e10b004561128901042140c0d240803854400b021400d0f0310f000314064840d14821503440c1d03040100d00004d481c1000d03524820400c2010200c00899004209280390b03180d42255141d4400d00c00408030b00e441c2c01508029428090b62500304104c0e0340040e03a08003180d100b034041d104050400420 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 692611043 1250 692609793 692609803
    0x30204140610050f0d0b0f0901060305011404140a0b061b01020d0e0c0a0315091e1a071b06090c150e0312030105060a0306150e0924060307051e04140102 67
    0x8400400c050a1141042d08a69600406d5184002920004200401e0b1001a04c01c000a0380100c0c00309075900e00510800c0c0804500060017681170742c0900c0080c1d00e400799000324450040c4034070603055031600f81c004144d6900c03044070112038a084a6401007500411100d0003544072522227103447d07142507070402030010085420710101394000d00a02e0340754038580710081f45020000003510815511000a00040c25020070742043d282d4082c4001c107105018a40302a0034101000c41c03403584e1405004000c0b08651014000c0c180240071b103a0038442d041c0520300f802c0039241c5031200500240314000c012500c1c400240c440c904050059480d8a60340e5003000c1031580306c04840034031920490741040140300b982000001000162682e150011b0000d540b1035054007941071014290703000801100745801a407a14206d45904603d030040c440076000ad140309018100211800307a28020400400081c80c4980500151065181480c21020001250310b0f241c0c00d007031b407060165148400410006031115440010 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 692612293 1250 692611043 692611057
    0x170c01170f0112030e1932100201110406030213150e010507020117070203031006050f0306100909020f091f02101a0a0305030d181101080402040603020414061005 71
    0x281c6411a420003400714102c4882c11000d401340040205130f4521521a0002195902441015408a2401e1000c4081480d43c039100c85481e010b8180d03d88a080081c0103001c00c80031004840c003408160420078280d001d0724075640c00800309000890005480343e0160002d104425203c0d1042201a80b5410a210b8002e500005d0000240c0404124603055000c0c500034030060307005042240c0041030340d407010000c41c84115803080043e000401030190305506e03010140d01038280343c1003180c2015001c00445440c0c1c08002c265520035080b04e040c071880d1500a02c0c605018100c0100103540da001c11808511081e40b26024590040000d200c04203c40b40c0142c880640850f450b1740601010b152402610014000b00ca28281e2007125413290f442a903a40c0c0e0002074025440f440c00366840e4000c404985007256005000f031441c61100c2040400064a80e50191401100900341003d10f502c40780045802004c03203030002034105207070100170406001e85050729845640119134800894203440d004813041d0007111 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 692613543 1250 692612293 692612311
    0x109211107050108150303070510052d0c120a050103021903110909120a020a02041b0c2d030e03060601020316081806030c03010305120f22170c0117 65
    0x901c180907541c45085595081591200b0075030342c1040d52400a0300319844044216020760003031108034405051402107561000046140c00400c0d443d80c1100039aa610408140505445406c00151100d0850f0181c900015945212034083e10741502c102005000038002070344214452200806900c01908180058983c880715000c41009801c0c00e000402102414580303540c014800000180c2d200ca1000d0b0443d42c030546d00500125005d40107202c103e56180404c2500038846070050301d01c0381d0b04080e850072003561050800304c4c0e09098094a02415200d200241c146a4440d4485400e0580c03100c11419001301c201d0680c0c000e44c40e88001a6624401e11114501164041134854045405100500b84074046c0f00940003258503040c1c005015503108031000d540f034040100041c403c0c00b504002d004042060707c0002d601e808031062294100340a03030310520170724403200680c2c1410a00c08800020040c10101021049082003651150b11289005282d500251001c030314a1050800e23603c0c5c6a002d02594 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 692614793 1250 692613543 692613553
    0x150406060519111014090a0203190c151e030b0108071202041e031e0b0f060f090103060c0e093108030109090311010e0c010315050301092111 62
    0x41254090301c2110150420601c5004800c404140703c0512107004510940c0304005040003070b1444001c0120b00142c02c0000300d07031000340340c84010384002900c0c0805264890f0000f64400b45841c01c8200e20300b807600310060304151402c05900441d000807540b800202000e03803174440c0c101c6420081b411138103a5000039000401c200045150300703008040343d03845144461741c00740c58141c07100102c0100006003101401c1069901e0001c009111340c040040202000c00c0e03e440b00c10f034a641d00c3d04009113001605411242010002140d099038035070355503460502000d40440300c3ea603075030f003481c030002c0c0300380e41d40000800d025801707c00307661901c02c041e14450941d9503c00c0000c0b1403a0710408048682c203840c10340465071a030050b1400703d01c031080554024801101e0108041c8402c0c0750080a030480b4296582d03050381008456111044082844a02e4130400e1a0004041d84c027a01d80711010540d036840150113528102d07108040c0413000503039402001e410301d40741d00518100c4004907001d448103000b410183d00b007 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 692616043 1250 692614793 692614807
    0x7020f01110f0f06010528030b100e040614060a0605120403050c03190212030601081807090903050309010506010801051503061f03020c0c01090503100e0a0b0403081504060605 77
    0x40200e48085003411007102d80c0c1081240102d031810800c50815502e5030301250040055140a0324a440c400310850501c00c10390140e4101344904c06900d010081420703004000140c002d600a2402c0c100408902d0a0314156051600b06103004041c81d034500c10340d490050700040c200d414502102d60032500982c3e201450840320601c58550080c0140089080000c10040019500300400280504c0d4140c1e9000e18101c2100c0d07034010f0301c1c1c01c600144038498140288104401a80c10400740c070761100b01b8610700304016194001c0c0074180405900300c100d0385841d03d070000d0107150740040a54130541100c0001c0020761246e80042d02e18035000d02c620b40e40148020f003140d41c00d07091507025640119000d1300200524072440f043e820103d803c00d0304240025030129080e0f0542d4800c101c0290306050030308184255a08103400f0945410344200300200040d00d0b100010380400c0c08001608911f50000040303072441c00d29240007800c3e94800d55180e011503415a81c54030803450948100f8088400e1615081d2814035 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 692617293 1250 692616043 692616047
    0x30815060915040e010e010816230103060902030a150e0412050c01140103150506150a110c060f030402100f02070303030e0c040501060206160c0c2709060f1107020f01 73
    0x6840c1d0314580350b0140502c000110001c407086024060854038007251125070405480c04d00d03086c28020444124035810100b001701108000004280050001c00ea4240d02190b82c0147c0140189a03c2100d045100204109241045900240034100c1a04005549139a10085841620710641d4080c14451100307840054540c0910014005d6000c1c0100100e9041f141d8000740810000981c42a204500c482c0e45603400c1056520400da480381080b203903c483c101000d5501c0c0214094407008205005d01c04011480040041146403071500340109003540c1d9030500080c81045420981d422400303141a4003151003582d0240030300d40103055182d4000d00c00e151275500e044020340700450200c1454058035041000b40e8880b40212130107010140c00400f05070410182010024005c1003414081100340045d840005d01c2c80202c90b021110b891000303205104a541600030080703903071441440c2451030320714503400b04a095041140c40d00d1040c10200205036080345a070303800d4420070b2002944901d032040072214545c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 692618543 1250 692617293 692617309
    0x1903050f0106081e070e01080a0c0f030c030b040e0d03050606040b0d020901110118050705060a080a0b0a08030c1606050408030d0e01240810062616120308150609 71
    0x8070210782c0948204807044c5000f2800c11041c1c0780038000544039501844156004500140c204400d22420003014400314001010380980b045c11604040e00c50310413090b03a6200303802c1307102e4019001b081002610200b0031b505d5902c44c04100d80c04042030400001400501c1c000c0c05031801c0f01c0c0009243c0740383c0900d810242e40250f2004c05403d060005601101082e90000d21448400d824201d030300322101d121a0410f246402c0075940076602c0b80c0300030018070030042c0d84003001a820002449021400e0500000002c118045582010a981c4008110300c0056480000c0306060f4411100c0c440183c41d894410854041c42f40c0e0143c11480d40c002c203ca58602d83c3c1a0340241d185001040001a9100071380c120044508070740b120381e410355a15a2000d0110720414003c054080d1003481c8204480391034840c80a0480349a4603220b603074090107495503405428180401415080302c4044040d41c15299181e403450071206032001d0780090907a40001d42140d41c400d02d41c0714104401001181068000070400c4a00d07 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 692619793 1250 692618543 692618551
    0x91606020a111f0c23030a050c0106030b09060f0f0c040b09010c06020d0e01110306030a0b09030d020a050a0206070309200a0306050c34080901231903050f010608 71
    0x21004140c1a00b9070004160800c522080255840e07800711001814141030307400e106a8550040c5e40a4032540406941c004120361510289041c801c1c0c484841031041801050507038000350800d04170f2010818079002c04207456119000c0340d221101140c076400440303100301c50111509441404204400d0141514441c0500114001450241d5803105256215016600a12452880c1c10b0711051801c681c00400e00aa840a652100115045113030001c00079607a43c160400141c4580c40001c0481d041c08028000c5a142c03184102c0c080d0355a100e503003030007000382d480448418014041c000c040b503030640c030a0041c0c0100301d400860401c0040c140204003110446500052503028001c000000300007599801400c0c49654080415916002040c0c0785a01c80c0d1461182210400c00740b0300c0f0707c0d1145072340383d4046101c0d86e0132602c016254030305000166401e0802c003000ca0651f1001c0141c0034452640c001c01005006c031081e185070310102c155131060b41550720a0380c0c108000c1400800510513284189190747d44 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 692621043 1250 692619793 692619799
    0xe3903070c2307050102010b01081b0721090f12030903110a1a122203080606070f0c08101a0f03030f0d02030103061407080402010c020102030d060608091606020a11 72
    0xa485201030320307202c086001e01c1484080303800100040203290703020301c20708404100c00e00b44000140713800d1034180c00ca81c250b404100d108420100300d0b2020f01201e8100340b000d0b8001d061180084000340440a003080045110f0403c046448100104141800e044449801076054a51680441c2143d45070244285440a44c0303400090754400010500c1d08403429401c880308802d4025620302c900a070360303582d40c14010318641e000c2100c3e110500880005100c200b0403180c01d481c2080c06a12480002410b40c46403040281092454001600600c41c042401e6011144d04508840704000c515281c0c1050750a10a24a503a08e07a0701c03c1010a9400c04a403030540f114070041c00c1d00d260a00ca80d5030800550420704c0c1c11a003103030b80480140200503043c81180310311920031626444071b1520400c02800414010300007410012480d91640031a4001c03c16200008088501404030a8541100422000c411174058840b071280c0b04136403886410001c101c03020345100c0c0d0301902d00d482c49030f1285903002e607010381000e030 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 692622293 1250 692621043 692621063
    0xb01020613031b08030907060e030706030f02160b0601020c030c0f12070302030a1b0803120106050d060308030a021e04081c050d15090e01050606041206060e3903070c 73
    0x605010510720108128403444c0500d49a04040c20344a18180300350304400140030710321104e903100781da0010303158048030701900d00030444401202c01c0e20080c2c014403c2c1101c008100c01281c07810002d030b91025501c0b5a0080e803c4600c0002c85504055031000d80084c650b0300000301c81c01d10f08203800c201a40346015150307007040720301d0345642e0b5002c40d01e40041420280d920300c51031410b200e40071801c104ca0030000d112031360046d410070191043c118100501840b9042c103000340050324010309021600041d00458000560a0301c92400003178540107076001840c2c5880050702490040d0390240c0740e905550945030400b0081c410071900c0d00d0044e0b0a411848052000c3c01014000035688a1b61030150046c203440c0c04003080740c00d91610b0f000d10152011900504096414101040000e80398002074604650810b04c12035603480c09403c10b82c00a040903040048810600d1013008409000c840d55180da0030940c56141a02c41010445114000202e03000c80b05101b400304082051644100940c002035409030405003 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 692623543 1250 692622293 692622317
    0x61e11191a042616050703140604020102030301091a10020714120604060c050c010207230f1b0609030304030b22030206040f031215091a0d080706180f020307090b0102061303 76
    0x101d010130b0078003c0310b8a50242d8030900800039802c00b0340c00218001030042c901420309a001035100c1c00140500500740c0d903202d400034000d1400814041d03031030384040c04d100c000c040c0070007000392184028000e0301143d16849042030b90508000002c1c0e801d150003d809000151915610785004e421010100c408000e000c0c044406041000c1c4001c16500c1c0c411a540162040180703401d00003444103100c1c490282d040801d801c4000d410100704207449003408410b0704c907074140700e000240c13180c0030b110782d595094400070501200308148003441c1d42c001c1e0314040e61018041050a20f2040d0300200d0440140141c00280101e400146aa4800d0410500c6414209004940e046503031084a082200030100d205030004208031060359442004000c001d000c0701e100e482e0141c800820345240240d000100300d204000703540c20601007039502645c407070b00c0d040030b007102c1d408042c0c1404810348840e0076080e40709000c3e14900007103400b010b00c651303002e40c441a0040c00050341c0380b959224150041c07000079024000011844 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 692624793 1250 692623543 692623567
    0x51e06030a0207140d021507052d0a0806040608010e150604111204060f020307090314070b0a0503040519020d060207020d0c06020f1501061e11191a0426 67
    0xd80601304402c00240017000d600b000080c9010485014030103200c0c808420302034003a80c01001c0714441075841e0400510010740000e0651070400407041c0b540d035a400410b800f5101035200040c5400303018216801d01c84151100d184600b210602c1c2c0140d00c031a8820b03001201c0703520420b0b001c1c40d030200000f48005000014513080001c0c50b8403c00c009071103004900c04110401c00c5504c6100800e03041e6440450561801c00c40160002801d03010260080c4200c900020030603608000703403000740001d801004d4072006c2d125400340c0f2540041d101100d06024001400744900300102d10900d0080d0000c1c801401948152101c20007548030313000aa030040c0300f04a017a000f007922075295030011310360b40e4000c0044400340e101160030721542001c0d001e4a90031130401005156841280300071401001da4008054424014040c1e171307000400b0114010718095140495040082072010180590096200d01541d410305003504c64811801c48004000826040013140810340c40c41206451840b8a00b20f14500361600200f = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 692625899 1106 692624793 692624813
    0x80f0105150708070204020a1e030c020309040509010b0d031805040240030804150f0f050f04030503030a0603060e030f0307080403140a020a0c051e06030a0207 70
    0x59801441031140413601016801001155200322031240a8540d1030301840070340d0b06160b008284d12100340079004410054401d580918030702074084040000600010300340703280942d611401c02c0100d803a0001c42c54415406a00d90000600c4111054041c0b400940c1200c0d000d0741c014410a075a100c0840e104c8100000189000b88005400502e01038108a0788141c017003102c80044030000078040c0440090050314145543c102240040796019121904103034002c00010b001c0c1c00e101000188503001070080d40600303e4020749030956035214145560001c0d01d44a00555562804004010b070604c203071062440d980000d181005036040441c1000d0000030180c90502c003e46c0002030405114804024179449002e1b803050301d0700c10101c4020755504180408070b8080c001e05801045525240f04007160306071401a100b0541100e070801e016a42e000507044580440e024007011000401d180c2d0 = true := by decide +kernel

theorem cover : BRFrame.Cov 692446043 692625899 := by
  have h0 := BRFrame.cov_init 692446043
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692446043 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692446043 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692446043 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692446043 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692446043 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692446043 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692446043 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692446043 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692446043 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692446043 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692446043 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692446043 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692446043 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692446043 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692446043 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692446043 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692446043 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692446043 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692446043 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692446043 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692446043 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692446043 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692446043 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692446043 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692446043 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692446043 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692446043 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692446043 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692446043 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692446043 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692446043 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692446043 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692446043 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692446043 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692446043 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692446043 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692446043 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692446043 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692446043 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692446043 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692446043 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692446043 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692446043 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692446043 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692446043 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692446043 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692446043 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692446043 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692446043 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692446043 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692446043 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692446043 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692446043 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692446043 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692446043 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692446043 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692446043 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692446043 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692446043 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692446043 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692446043 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692446043 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692446043 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692446043 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692446043 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692446043 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692446043 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692446043 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692446043 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692446043 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692446043 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692446043 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692446043 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692446043 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692446043 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692446043 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692446043 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692446043 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692446043 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692446043 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692446043 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692446043 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692446043 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692446043 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692446043 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692446043 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692446043 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692446043 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692446043 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692446043 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692446043 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692446043 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692446043 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692446043 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692446043 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692446043 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692446043 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692446043 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692446043 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692446043 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692446043 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692446043 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692446043 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692446043 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692446043 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692446043 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692446043 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692446043 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692446043 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692446043 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692446043 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692446043 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692446043 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692446043 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692446043 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692446043 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692446043 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692446043 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692446043 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692446043 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692446043 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692446043 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692446043 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692446043 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692446043 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692446043 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692446043 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692446043 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692446043 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692446043 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692446043 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692446043 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692446043 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692446043 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692446043 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692446043 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692446043 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692446043 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692446043 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692446043 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692446043 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692446043 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692446043 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692446043 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 692446043 ≤ n) (h2 : n < 692625899) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
