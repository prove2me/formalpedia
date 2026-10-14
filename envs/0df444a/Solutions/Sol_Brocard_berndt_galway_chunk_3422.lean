-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3422
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:36:53.842339+00:00
-- url     : https://prove2.me/submissions/989e2b62-da0d-4e54-94e2-7f024990590a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 615287769 ≤ n < 615467625 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 615289019 1250 615287769 615287801
    0x2b0207050307030b04080408010903050a0f030e151816080c0d050d03110c0f060f07030c05030406020a050c06090d0206071b0f030306050409210519110106051c060609 73
    0x10800001c4c03103080219900910401c10319050540d98004107085da200c0301e6044021aa0119045203002d80c461420106542c0d42d2805101c400c2c4490300e0191a4244802c8003042c21843c640040c001e01d803202c00e8254503042c002c044816002001c2464400031109024071000c5014286003203119140405011442d560404090000c101b000001500201508001d5911407102442075880911044c404004109800005000c1c0c80c40c1a160803508044014034540c18186061808918103078844c055a0380a907022400503075905d040310040d1260301899840b2110b038410402000f50360040800e282d00e1100359a0210b9941e41c031a88416074111458070440c0103090310346403001c0003103007143c00d540c26864003900b0b00150464442e0082425500c042105481c008244400038102c501400d40000d80b5000a00e1301a007070920151242d0803214040e956001000700300490010310500c02e60001c0c0091000805034002c000006000200508491405490b002d150810024144049019260440c0c0c0c88202c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 615290269 1250 615289019 615289033
    0x152306041d0915040303051f06120f02041e08010501210816050d09140301140601050d060b12091009080409020f041a03220308041e052b02070503 64
    0x61440400c1000400507002c512849400c1c00b0090b94440102d070045010340d401080900d01030340001400f00300030700d541c0d4868070f0007403007007140a41c0003048a204c410038102c0401c01c00090f41d5142d01074020340d086000b00e928100700003035010000004810403036006a0003404a60390b83c0282000641e10702003141308000588003604000707070424004080010108601c9510107842d81c80e002c0ca80800e41d410308000ca00d148500707101c01c01d41101c1007010044201c0083c0300359039074054404002c0d8400752065040c0039020420312140100c540000c0090200c0c040203948861003250407442540301901c108519000c2c0901c018081501d40c010070803540d41282101e0b103000c1c6014100c2c00254030100e901c07030406905204c0070504401801050415107555a682c64403410804000d4101880020030b80c80010141240d01c40007030b400140c019031090300121080088843d0160700301504070f0800300108180a4085590030880c00c1520702d048402c04440624001c03640c500c7c060b60354212600905501d41d10600b = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 615291519 1250 615290269 615290309
    0xd3002031812010f0606020d030e011509050c160b071101090f031d0d0f0302060108190609060621030e0f0117060f0607080301090f061d070315230604 66
    0x80d566641e01c002d86800040d01d5102012044102c0d0f580340c02c40e000681105202d004a2036140c02080a02e85991008001da0300003005894004c0881d8820503039216120782c005502c50814406580c000c0380480840300b00607085107001d02e011001110508003140c1684040c0300200014401c001a0f0342e0300c13803910714103403500345c405840385072411520b1200500c03150410380c0c240d1140c00c1c014015901c40d130b4403d00341617810315020342003120507049440c00303601078240100820070326644410441d4100c00c1c0042c0b00007090602034058812504402d41c84102d00c1c8401414844607881c2100c4c06010740c1d02c44182d2040301042044c3d5940e240241c60010740400110401d02c3d10320b050403504000010304500d00d4980800215a0642001c3c3d81511014404070040242107590300882d0090941031200f0003404d4106004c5004821402d40a1003194210000003900c0c0da000368044030b03100101280b105081d44d034403221201c10032480401c3e0030004501902c490780d80d0801c14191403d4440782d40c0345140100c880 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 615292769 1250 615291519 615291529
    0xe06010c0b06030c0a06051e09010516110924010807050f0d090b041b080715030203150a08030a0e040213060c11100302030916050604140d30020318 65
    0x103490b90f641030240c010622000c3d82c82282140041000c3c0d241e40e80c031050b14000b43c45006041e4011400c0004041200c0b4100e030703a11804944510038003440004840340d01d400d0840c030200d801550761360007a100c54103000290b0708840018504c0c180d82079400c2410700e0804011141c03e0001d441180202e0340500042c0801c2aa440141c6400340c084080060b0001c41e0fa00c1c3d994800c40141e070290358140701e681c030844421039048410303000f80c00d50380d004058052426603040703c3c0812101904c0c0c00c142c1d010006c20003c1e41030303000c020070340035005207010134582e04d401c0700700c0e201d1307001074000c9012800c0d000204987d0b040078001e540c03d0105a03207000032510f152403404d0707803461807100040310140c0032050b0780000c507034803134914040031001d90b50b00580300c0c6407004210b0f01c0c0035a8403625041c00801442c0400055442e03008880555a4036242c4000e066060400f0803110814002c1c000c0c45591400004105021009403c41e034400c82c103840c04d0f66640300e840c42031b070b101d2007911046030302e08811400c590a1800c01d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 615294019 1250 615292769 615292771
    0x1b09080c030d1202251b080f120715050a0209040b040501051c050a08070501050604061e03060b031006080a050601050108040b011215021308071e0513060b0f0a03060e06010c0b 77
    0x20019100f640d550700500d0f0700302d1751000350b108940032500000307121000c2403881403e502a05034000106101510303039112507511700a41d000003c1441c07000681004002507002040b0005001500500142c00c007141c20f60302a402031415240102c0c50318000c4103042c0b03000e01a2234100c1c0c001400c3c1d601d2380710400824146807010620140e403507101e41c014003030010300d4540040c18094001c10000881d41030580411040e29142d40c05510380303050040903c51030018040c440f0040300c0c2c0c08900050440103240100b81000e822042e04951300d4600313a00024444804122000c0c100e2040064440d580e803100010f43c0d90720820784001e045021184c0040c4640c1e00d205195820142c06608403000c0006005075040580e030054051110458021404120400d81000001d010f45592186c451058041d054004403003902d510555208910b407071a440210f4455600c018050981c18000580d51107a00d010000310b984a400300300c001a10345040015042c11040e42940100016036400d0041081ca448a441e0480 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 615295269 1250 615294019 615294037
    0x170d0f050a05090f01020c1c30030c091203050c010c1e0f0e0a09091a070c0201180b04030c0611071d0a0f021314030615131b09080c030d1202 62
    0x441e144044525035940950008c0344090b840c4c20902104491908074502141c0c18850700004002c2070300520403148110052503003121520300000c440c9001d00085980d10000e51054800701030b801511000d050b0700100401000030804000e11100c641050304580c50740d03c0c00d075801c0c840030f1030032150015a84219400041e0340f41c035107000841c142d0440002000d0a8155000485403a96144002d0401211160703514154092003c40b440398175090390054503000e00c98070300a0401800e00010300c0c072010405000c0c40a0200450216200c07500c928183c00c04845502840d000b040070b800d500f5601d4500000c4d2001912201e0b04449440040c0340e05c2da814000c4060a554485506d400c46101c00c01c029201030100f0b44d5030815044040707868a0000c030340e400781803401d16009810070410060401100003003480c00080070b031044082420784194080040c0302d0040c1d64081d16101c00070125030580d005078000251810748060b9441e0039500c50404d50f688485007454404140b42d29813040c490401e039405410109 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 615296519 1250 615295269 615295273
    0x1602010204090515091608130201030f0e0102030403081305031c0e12040f0504090c0605070f0c0e0601080105030a15050a09021921110402090604170d0f050a05090f0102 74
    0x54a9080c8101030b42c604460000c00700400008402c6a403400002146d0828130080300200108480783d80140402002007070070440b40803061002c01107912980c0700804400c094102080b181301c100c13030054040c0d8401d83d8241c0c000340c4180041208001d510500c1b005507540000158544038445800d2801c056500c405240c0d42540e035500d070020708005009480b10a0120701400386d0395410b00c001c2030510103290300900e0041d4942581c040c00501511801415603001d0300702680c4a4400340351521a00c100d00b0401088002169000159501c41021086c05000c0988034480f0503a01c41c414559658094680541100603020b51882d4203d800d510a81e0002c40a000225852910b5000310769500e41e040d03040002c00380ea20801300300c030004903d240d130301c0006803c080345441050317038489900c200718420901d80b04960015800c2419a0344d441141d00600103017845145482204d0521500c0f0301d21103c140c40825602c540356000581301c0c070b007181ca840c229034860a04011003c070078400e030b024600960394154 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 615297769 1250 615296519 615296527
    0x1080f240406090f0303051f0b2d070f0201030c0305090c101803080c1605010c0b06060403060608010b0310021306110f070f0303090602011104090e0a02060a170f01030b16020102 78
    0x411800182c10007805e0003600e000c40c0f1070900700002d200340c4136215050040c1e084000d0061000900c110101d95065400d6160082d181d0300e4030f000c0d0203100040020071240c0c410001041020840354040b201500c0d1b0003602c0820000c40e00200a80940f2012125082c180e0014079401d20b19140c056850101c02d0318914106081d402050442e81210009420586000b84081080014503c0c20440d40c105040700542c6a02943d00d490b0020780040c1030710b40010001c015040028409841e8501554010740c0c01030790900c4440e81d2008240e00821040300e44501900503522071003124803c0b40201c2e14a803600c080d03030710070480c5041c030119924890444d000481b8005e900c1644440c0d40c00700302c91b03009000c500500300c020714514034014104100d00d41c00030082d641400c0e18010f8416040054030201c8010000105450324500140381c240000810001e51004012840d03000749903200c826400c15802042c40c4002c107071a01003191400b141b0901c0018001517042001584094a0039207419400300c1c540005414 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 615299019 1250 615297769 615297773
    0x50403020d0c2111030a024204080c010e03100c0507020405010f05130501080304060e061327110f09031005070e04112a0705150301080f24040609 64
    0x7400e9100e182d00680e03c0c0c0c9404484180160540b0141d071000c0110014404041c0940c00b00c2e0104504480800d01d0504851915154030310b1880341050400880c20040f950001c04801502582c0250080c14814481c120b045045035004214174414482c00600400124a00c2c19512002e882701c07550100070060240071000058440f401070740e02078500e00d4800c2a100342000b080c000c5801c903c1110000d042e04240040000d900080112801d42e2014030308403070103403000c0740860030b140b041c0040c00052605964000440014611b880c00c000700c0c0c5186251040b8554010f80800d903048000300003107010040101401d0384074100020005100040d0503105500c1100f4801790480c1c40c121443c2000c0381c0f5202c1d03050843e01e042d110b5020711030408500b0030f0400040340204121800418004030400c9504108414807000401620009210040c070044100f4001a0441541e070000c0c491040c9a20031004c00400c1243c02045000f442070031805c509450800c150b0b1080080800540700343c0b15541d070741e04000c0c0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 615300269 1250 615299019 615299039
    0xa14071508182b0e0d0503030f0c0703050706110705030c060f1e010e100509070c03030b060301060c020f12030a18050a15080a06150c050f0705030a0308220c0e0610050403020d0c 78
    0x20482d401b0f04003442d12440c00103a00000c03440001e022842c0960100a850002900002a43c4840b82c10130700c0014480840c2c09204c84610030814040d00c980f0000c101e141d410100000e0280c40b4616060140c83d070394584240d0b0081180c8006030004450540100600013000b0a14445500003004503c103805035903544003203041d85000740d42e010001142c1d0301341c003000d041d0140074084464205642c00d51541d0f01d0318000401030440d9990080c410000c103012106d180ea00d00715101010507082d410380e0340e91100c0f003402422074400c80c803401c01c404036040400603441c6000e6901e03404030f843c4090340c1501240c10100849404100a01900907242d48420100d0355020301070280d0804d03d2244c41d0006558880d05086140500540d915500c9a00101e424400da032001308641d02e82a1b45420b18540c00c0d00e4100c05011b8403007515440081d00305071081c91105005450504000700c4034600307400801602e5034024000000c0030098800040b43e001c010410040c1001507030b6145150103020312014140e00c2c0d5842039 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 615301519 1250 615300269 615300289
    0xe0a0b07050708060105061306210e0d0206010914010e0406240617160e0105041d190501050907110c10030203010807170a14071508182b0e 61
    0x144080d8040c031001c0c0b2070f0007010803059004d01001c866a80c100202c0b802c022024107454054201000440ba0040204175103c8503540c1403004001800c4c0f1408030b01010059440ca540f500310f0300144110700000460024611405003500c1c00843c88200c980e081841c0d50032000341c0600304840c080da4036a45001d030458418010a403a200c5820f0000f01c1c0c92074910020301001c00704c2c09012903602010144501401e4400c0078007000f10301402e1010940e90440c006954a0040340d016014403a01c0b02c412501181600a00d148102d58103094420213810f01031046040300d13024010310307030041c100002040b040c07801442801d240300340540c1260106011207000c20180000c1541800100703401000500c2203160600020000d4640c03c0c100d0b5040d42880301250303940e008216005000700c0c20030f05a1030842c441c203209840191074a24a00e814031440c0560081200b01d0450b030400c0d22010002c40b584ca480d90104040000c40c0707220824002c200700409180010702e144c10b0403001030120080d01c80800381c440c10414 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 615302769 1250 615301519 615301523
    0xc0c090506011e0206062205010b04090c0503130312020c011a150705100e0a0c061101050717070827100b01020d120f0b090a0524030d0e0a0b07 63
    0x208490800c10700161540030701050308001c0e0425400d00821499000603459071000d02211140001003402c0b82d0014845003000345008103d00700400420600c02840003081140c1c03a03080d0030807425000380b00880700c0380070175580311404040c1040b0f40350200e071165021404d03000d0143c400520381440103500030b0840e14055500320080703100e10b0040085150070060580d10750404c0f801945849030940e02c00d611103074001d09038000e195451841d181403005c1041111140c56011014200094031050080c00344155904043c400390b08100c0015011031283e1110025010402ca000c40d00e0380b0f0396a0199451240140030705210804d6a440510650030b004d860003190354448044c00c001189405914281c070203001140781590301502088030356035401a43d41187c1074810100084072024581000060101801c11a501180b44024084e00e044254001400303814240000050000b10420403c150b090986030250716800c0f03c0303481c1180c0e500580715490300c800024004001c850303e503010b08010390020081 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 615304019 1250 615302769 615302771
    0x2211030a050709090e07050402031f030506040605150a060f1701060e09010e060a03021e0301052d0108030913110a08040311010209030c100e09010e07200303060d030c0c09 75
    0x42c000c01c02d4001d003e1070064a000881480301c0100401e150382c1d560540e10403540110350000c00100c10701103005002001d00411803000014540d43e003400c5660304000c4d01d00390359061406000c5501205100084032040c4806441c40b501c15280130819214200c45400f00e0341401285400f2050100c1c941911134084d00f40384d1160100b414210701400315071901600b120b02a4003c40c018020743d550380d15a014110395044a0382c1c0e06450784074281034038001128142581542c24402808048010780810050400150300e0313081d0000c941c41e01e1000c0c241000c0c800d5400e40c1d00b04224070802410800c402075a1900408808621010a1080a03030030b94024020b0b0070004200800340410941e000e000c64012980402c001d506202c3c08500003512560f583c0c14080c820310200740c0c1c03000154083c12030300000300ca0040080500e581d5606040d01c129004461400000328900b80184c68082200e00c241280000d00700110300b0360352180c0a0181921074004260300340300b01c00303016200044c01910008050640d41070 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 615305269 1250 615304019 615304021
    0x60d0c030b01080d1b0219090e030d1811121207080a031b0f050331020103060503010c050d2a02070603050f061305060402091314070903022211030a05 66
    0x240c140c24420103012080410100794a090f000d82a084c0f00d510417160100c0381c02240d00d03500820240c01c0c807181d038450900d240c20464903042a000100184c040030010030800c0c800030321001504c00f030101a9110040100100368030000e07082c00d245010700c408652400480d40c0b90b0341880c0016003030360090041103860030380000b451117242d0f515009840d090003c0c89005800615402c0740030703045104d2101024200107010000402d0344405001c1c0b00403500303194050740012107003041c6000d4203556a0302c0130b03030129003084000991030505100310142d2001036512103051046008114000d041c030603510320000e02d00305219050800c1060140c480400b500d400a11125191082c0541582c40c0200498103441c3c0800070000a900c07048898030624101410008281d614440060300900403110080e42200e0400d02d9040e007184517070322004c034020f0200b0b4003250740d0362048000c40f900c407a94040290000f41d01d089000c084405a004402908007146000c10615100761801039903401c01c0303410010b080d031504 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 615306519 1250 615305269 615305279
    0x100207031b060203190201330b0c0d0c0201020102090405040b16050a0906121512120c080304020907110303130b06090919030504030f0609140d05180a0b0d0b1512010509060d0c030b01 80
    0xc4c4d4035030010143e039003145040101090380e60740c0791403032400400c03340011001881e08680c400c0d030488401c1c4000910401c2503081c2070a00380e01c80c3d0012030f00f400f110040c01211071307160ba00480603100304441d581c0d00c4841c42030a010003118940910707107980c0c0000c1e0310740326035290100000301c072113020300170101f030b802c03244e10081c01c10718092108900040c09000f03003140b205021a80b00d204403640030303806a03000051a2540907040381c003103200c81e0807041680400300501c11a140b81c10301e0f2021141c0030781e4078800182c0740c04081003402081a101d0740c080e42d0204a805c841122107080c00c4031500d00138100507041c1039503a112006222154001180c03140c0e0744684407020094075074041e4a000c089507000f45255000034001610794860700d010004001030041140100c6d940c0e40480701c0c091300c44481010b48804400043e0400f03440d440883d14402c08030840303c3d02e603142c800c5041c0c40e41c2501107081041141d00e000244010402c2c00b410080c1c100840f2000c0308081440410110019032003486585030707030341c1b503e = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 615307769 1250 615306519 615306611
    0x705070c0e09030c460609050d022802210102030c0d0609020a1d030109020409111503071e0905060a0c0506071b150b100207031b060203190201 63
    0x240e10f1014904450032802141344010301400741801c60105044454421170460000951003180b1004001c181010305050410201044030001c03820710703400321443c50811300342d940030b446140c9500c841c2c18204050420058030300401c1d03014480c201c1a80315890886d81d0060300c1e09a070301c229039612050400080d1109010705034440da000610f5080070460411300c0d103c10050640059085a04c101140404800f01b10340d0203510980703490340e006004004010041c41d041e44000c91000500c0d20440c100300722003154607815030880f8131507000b80d0f465440c0d00001c000d8990309031844402c030f00100400703060013003940e80b2140b00500c02600b1a0700c3c2c11a42c0c1c407003464440c0c90280c000b0100780400100c8090400403509252141020715403201c40c02056403400950900200140c41c0f0603035000660301110320b41590007180031020750740144550345221243c50307170480d080d244500c0744a0042e0700c100f041404201e4001000341c03809100344004140305a1013021480e503903100050458941c1c9208122101c031000ea = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 615309019 1250 615307769 615307783
    0x3090507060807121431060b040c090b31030302011d0304061d040b0402030c070b0606070309030b040f05030414040509010e190804030b2404060e0705070c0e09030c 72
    0x1070729400e0045c00c130880c3c501c00358203c01508545070540e090440c0e2080b03c1d40511030840702c40490490304d1544407503003095000341201d849280d018901e0604042c07a4180701d414243c046d9a08040f4062030101711240a840d01e4110050807980ea0b81040310615091801501c8500210302075400458a5403555244046d0742d510301e083d4490345d500c104010805c1075081406027404448501c3d80060780c01c86000420003800e059a04e550344180700100704a4500c40190141c92d0b0a801242e084060b079440c103081c4065841100f038045c0100c4c00080b402c00010b0603503009994002c1c4664140032485c040c80d41c0341c610310380141c1c000c0f0804402c4498000e20b83e00b49807244542c0600c2840c024400105e80c0d20051382c40d5001480e0480783c00c0b00710f194510501107120f044800860f400035030602607290002d040c00e20064000300603200420301150328021071416000350001d403243c9184030354681e100c07100151500d51103080120340840c090300c0d0001d04107800e80780c032a1084038214061955030404240b82820301d46 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 615310269 1250 615309019 615309047
    0x6030c040e0d050c010608010c110d0201140f04142a0f0a1703130e0709170607030e010b090a060602060105010903080a050d0905010c1d0f03030f090103090507060807 73
    0x11030040d008500690004080c0641c0540f820565038800f00310311210302403c200d8211038450360038052600c074032a5000310b00204013003c03031098614034a04c040d0b00705c2c02c0e80c404c51424001c2031135403404140050240c910300c680107071041d6400403003204805800e904204000700751010303140c601d003043c98030b2079610f03c04030700c2c410f0048a8051403c104130000460407500c0340102100850001c1000481c06010403c45d8421502107100f15a000c0d960403036054408800c03542d100c00036101240006079401f0207003080d0301c0071741e11001901c42c40d540c2c40d40c00c400a00020551f90302564030b030180700b5060380f01c00440d14010400183d0214046003014006803510f030041e40958100b200d404010000300e052031095861034078443c505690344550030b5401a02412000c203003d8075075460301c0e002d1501e00e0340101600904113003003400400441c4074001000320300204a0446500343d0820428100c0c4818180f004080e0604141000120101903858140c034104460b00940040754140c000c0c0100c0036082650b0804440e = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 615311519 1250 615310269 615310271
    0x5040c05030607020a020105071b030b01031b120f020f061e04030b07080c030f07050f18030706030209030705150c060c2115090a06090507020a1a09031e0c1506030c04 73
    0x3c08641c0c0020050700c512718016098482d12254100e2022501c06500c0041d07070007800d46402940c49081000c50440281c4144502c20113400000070031100240d14491040d4100030700a0040c880d0b0b800f844400788220610540c03002041242c0c0090b0310b442e9417964440341c8015000d0f5200da041d031411032000b01010346804284400740b02044000482c1c0c1044a40c40400c03a51181e80c0c0d0703128490181d900e405210300400030584007090a80a05610f40400d25503c1000c504880d201d50355030300198120321541c4551901500050340038086410004400c520000090054501d824400300032a404c00708180c40e0a550f0100010301c0103001114074840c02202440b400c059a41c90900080032005c8120207045540649100c0b800244270340060f9000f0802800f0355070050000f071138012002900c40199520440d4890101030304660303880c4210300b103e80704e0401c0800a610b0080c290003000c3c540c070604810203204a60421004807260414000d00c1a485028040030145047c80c804240c149443d4141c028002c03 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 615312769 1250 615311519 615311533
    0x4021b030d0c0e0321070507030803040605040204050609060a170c03121e180103090201030b031006062d140c0a0f060b0f130f0f1e050912040501051c05040c0503060702 74
    0xd42c02d4085c0078040f8401c03090f000d54420f80c0b4501075050003502d60020b8041ca5000c0100300500003181c00c214840d07072089400f0081540d94504200c89030b2015100d05403c458000401c2c00304403559220916107110780d00441c4c503a440d04c0d60009140510000c0e5020342048041170404900040001009508244945050030116016141d401d4801c516801c54101a12020280d00b9640254001c400c0420054180c90444025101c03d10203007200d071150900044c000540702d1222030360742c0000030551799001c0d4081c0603012102e20468001685200310100b40c0c03000c0213842866441008014921440340381400c21086580c1802c0048a040f50b400601844229460040603910300c80c0300c4203066100c80c0e0020303484c20442c41403030040c00c4029030521120b2404000300f50450205e00e240c0424010500203100b01d40d64040103030344030b003002102151800c0b410b200c20f20141d070080d805004c020408500d295024005040c01500340c0d002500d040da410044440203010601701405450351248660006280c0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 615314019 1250 615312769 615312793
    0x7080d030b011b020906060909040c030309140a12080c07231e01030917120619030c1202151204050d031107060905100207080d0b01090e0604021b030d0c0e03 69
    0x4240301e80020300c01c00c41703400040c040390b13541819503244510280851446180c1481d1016008aa074041900810140c4a00090524074140244c1d15060301410f0196402d141181c43e0300c00707041c2444100c60000c01881458100401009510b0080581036502c8100303440002125511155401106010341d10340f09506409900c0403070148401103003807800088610305410040c40c001a4003888000340107000036042c1c80f1505502015005202c11a00c1d03105242c900394080b1142240b500c0010400500d0260400c1402810010360740801d0002d45000c405104011800c00507038884012981ca08a1440074001401010001f504d0b1480c0142820030a41c285e07160415064002d807c401000281c5691008081010030303c070071100c01c1071410301951151114600303138240d504a0030a200106207009110146503100300710345c0d0708803894a404400341b601c801e01404040c1d804200401134410810a00c045a801c00704010007250780710101c0000e0318081d4001c000c0500c0190450240701e58810048182 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 615315269 1250 615314019 615314057
    0x909010b5a010e03010614130203010e0727090e0c040608030421140a150605011403040305071b0504141501051308010903050d050a0c0c020f040b0307080d030b01 71
    0x5101e060040411034400102004a40820b41c10100940550804600003406c070410542d411101e54100c0d4440e06110b005803284040303010074420243d00c1c3c00d044012031b0000b030050306000c0100510f261403030b000e44209940e1004040d8150710141800355034200380c49090360240400b0031030711002c071000e0120610f80005141d41c0d0156000d40b0300d030007608a1189446850840103417a51a500031f10185d2030145060441c3d4079500f0103603003030700e03445403020060100c02c0b128412641901c5058440030032180c1444418540d68000400c1282401003c000041c00b05042c40711400c8803003010030a12500500b4402448161001d1000c14510261010140310070542421480c045054082ca4240d441da1000d00e0240320150803644421419440c02031030509040d4040000c108204242c0c40501060302c918501104840b480c900283c00a0b400d20f440b1001494411120079030044000c001142c8002e00340006420160036910030841b035030003840580e8056030140140840401c0034207045030341005081100c1 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 615316519 1250 615315269 615315409
    0xa050402070c090e070807080c09071701030803061c050706031118090403090315090302010c0905180a06090c021c0c0c1502100905010c2c0909010b 65
    0x100310b013130300c07003001c9284030b28100044070003410441d00b105c1c0c03000d40c0d03500010b44030b0b07081e0205640954814000100b036607018041074078454282010001a603803868445540e21380000e02095441011404680144a0003d188104240c000d0002d40749480c68020041c00f00c2d024140041820b100034488000c0c801d0040884440c504403c0c0c0d6064556581c503c1c0442c0c08226941001b00f00703080e080b00c00e09646916600164403103200b50000c2011030841101541e01e10765520641d640302d214501910328030030800d4441e42d013000800c48040340319034844039214152165001d000c00141d2040611543c0c074140d4520181c0d9000103800d252181440350748800e500c60f03803603000d40c594140241205011161080121080804110f10200000002071078818003030030030801442d0004650b01300410104090401c6201d034003079944200c00d40c0340454018420380c464020f100a005560b6090003556585a404c003800380b159a212001140e202c40d00610b24010392503e03800204280c042202c0c4070342d0624a1050 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 615317769 1250 615316519 615316529
    0x60e060f130905030a02060405250b090d05010218130908030f1905070804020111060708130201020a050109060b130504030e0d060902031203180307020a120c170c0a050402070c 77
    0x2491400d8031045440181028070b400402910000402c02d01c040d9020a9043c01340d445441503410003c5030f10b01000058001d0241e142c05010004c000304801c842c44c0700140401d2901078040c0c02c88001c44d444550880e04041405482d00081d200c103550307240380c0804080d000d101e0b410002c00182941e0345916106000c024684a0035400030750200b440031404500d403815050070400300707010510781050028919202501d040b4041788806802741507100340802c40710310540e0550303501d40d0169140c4d100da0750b800301040400e038154065107041e03001061081c01800c014500508001c5644100d103400c1c0030301c15125540c001c8410745404103010011b90b10015031001050111040040a5940c3c28484000d0111040003507052140b003403510302c20102c08018520406510a2088501c256000041c0d12485022002580f051800105100c450041480400340e54043c52800401c0f6072200d0056160f00c01d40d100300d42696014a48180007482c0c070607000c2c00074001c2130b83c095003805095981d01c06010514050 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 615319019 1250 615317769 615317779
    0x40603111504031203140703050f0f06011218140604030c1502040905090105040b09070e0412030e03070c03021c020f150c0a0308040203011a090a0b030a12050d060e060f 74
    0x8001c40d9001d070700654010b0743c0c000c8100c000030207a900025004000c2548684c1d96010b88a0009501c0c034007a105542c803410510303240d84002d0751030003181b01d411500100030340d0500003c0c80004014105600c110350741065040040f61240c21076040c00040b01c450007441d910f50340d005c001080b0000b40d209031540183c99100c202003180400003d2070700d029001e140c02c4840c00c913143c5010130900d02015000180100d00840390f415032038803851441a1516418003548451680d980040340005140c40c2e050010b2420a240002d8050810000d09041d603010b6031055420140c6d62002340194a001c2d2020204c03280c28841ca01503003406980454070800000c1d07420762044003503400002980840c1c900300d404120101c01a21381c02022880c0203800a201510f00340c0c001d40c6042d110b010524a141d0b002d074502c4100928034841039449410000c0a0400c80c5680307a0036010302c4412000091582003003117506002a01c480792103140b0410b44c1030440b040d903444042040b01d14800d000b01c030744440c007881040c5901921 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 615320269 1250 615319019 615319039
    0x4090b0103020708070501050406060b03010b0f03090c15040303080a270203070503070909110402030c090d0507030b070c03020c1e15090904121b030e0108130609050607090504060311 80
    0x40140c000f800340034809043d0341000681d5004004066100a00c81c3e44074030002c125503522030142aa090209016884020100f00042c55181611001465001e0903031412900440300e014040b89018001d0301210081c04000301c3d0500402d50071004566200d00c3c0d5540401041024840300c000000e1041101d000181520100805540301440031710003500028003121056076030746599a0061003a000103450006075091384c074486140c40c1c000c4a010354010002507003854504810000c20703803250042254144903100c80040003982800000d0300c81d56158840c413405004e581006414451650080c51103504401d203c01d00105204800e459040d6041d18148048502c10824800c0c900c912a4610b6004171680100010401c0c00d1005442078509550b03016218182950303810304d0700c070031940000c2c082400d0702150310095104034002d682c82445991164032140d0326440e180111a0242d0742030f40c0da86c025500f0895110b800941200080005036001c105052441d2204a51090514850b91040c0e420300 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 615321519 1250 615320269 615320291
    0x8010207051c0905060d09141c032003090a0c061806030c0210020307180915080a11093705010f06140306060906040f26030a141b060f090607050409 65
    0x1a0004c400c0300d0b030005a0b034623500c4480c0b0241d981c6840f801e02400702d449600c1c2a00b02064445e001e84c040e1450820140e24880c201880c0568407074000414181c1107101d4041c154000c14020141c0200602a580b21b01950811800b43c85040c500580c1092051500313140d00304410b00d5001079034008801e440800107031603445071802110100e12001800055180341c240c08103000a0541c8000c2d105a80008000d12050b80c580c0c0c1651034980c00e0101401d04a11541d50400302c0c2400482180d1003841440000e951815000c1d0b2100318244c0f081c1e034012a111045020b0035605079520500703000d040b4400f8a045094039200009241c001099418002d094001c03001c83e8007515140241da021f060000d00e0703180c54076150414444c181010b80300f036100b0f41015880340c2049806288900e80100c1860000d140741003010141502c84080c7c0c0c0496480c422400c02400c0740d90700e102030005131420314000c041e110701d0401461124002d5406451403504c3c0e003010040c007204076001400c8408071246d003d030209010350f003030b = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 615322769 1250 615321519 615321521
    0x24130f060f1b050405090a0513060209061908090f120a0e0a08120c19081b150a060812091018150801080d17130c0f08010207051c0905060d 61
    0x840b46010322801d50302c590844064100000d00240c480550f5050f90381d956945000c8192070054541c00710300f150342a000c601040c2c454000f0001103802030082498803954201107041001c00c804031500080150007441441c0d01c0c14841c29256208031001000b09020511800380380d03100b1001a003042c003000d0240c50312035465040320743e4001c00342401660b01d80400403003609125403250001c0820703405400d080000380700b4502c500c0d0704225040a034240c100070302154100040002c8144004152042c005d0540320210720300380b110310a0741d01032004149640307006001e6140401003c04440c2c41c0d4400e1119003803039110102c0040d038001d0781d41341540059036032110340040c1502e0307500841c0180d103400303c0c1c45400503048501117040321403000403902140720070b110450702c000d0340c18106501c01ca00341003c12809800c03403070b0302920180a400340100c03003507499000080d4849070381d0102c5602e1350046864000c0c09814806150b108164030183c05000126000c0145962a1405003600c1440d020078016000400c0f = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 615324019 1250 615322769 615322781
    0x6030e01110409050412020f0309040e1e0d0f0e0f060901051605070509180a060e030c0f0d030b090906270a0c0510021209061b24130f060f 61
    0x103210140c2d01c580b0b0398510380150008031790aa41d850800e524042440b440003488100302880a4040c40c101042d0034204000380640000800039840380940c00c258480700c0c0c9211000c0d6041c800002c0444c8100e201d405001b0740d42000c0030500740311455451a00039164032642c4083e908040310206d13a20300d0301d0307401611140184001c0046862082800100304000001c035182541c000300c0c0c489004e584c418010384100071158804003081e030069000b9000007511a00109200d030740913425a0709140c8130702d0b1140e10700741d090788003202568060003440c1c220381d4042c451007110031410381e0780404a02d00105155030f07512020b0600403203640c0300382c4280600c0743e14000103000c512a0105a0f9488006800c1c40740d041885401610312030421000c081314030900025078805400c03038184c11a82000492010482d15820207801e5560b181090000c003455101d00340012140c0b05801c0850b040c01c2c00038804d800d40c44410042c19040500c14041c6000c3c08240310b0950b0180450b80030310007080d00c4850070920005056 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 615325269 1250 615324019 615324041
    0xe04080903150c0d06090b010203090906010e130501150201060305150a060b07150b06090d06090f020306090732040f0f060b07030813030e01050f0f190f0309030906030e01 75
    0x22504042c820210026802004d8030403800d01d040c000d454840700e0800440303000c41d030007a025a10810008500d4100107904030761050301410202403248012003c62000303410820381d041c015980b0001880150495550201d0700c411610080000500303507561250b403240030080c03811103a20070000090f00f0107005d07049207028181e042a425140c06907443d00c00c00e0102003800b42840a0b003040038030342c11400c000c0300361002ca20000304082840303507440d1a20030003400000340079580e41c556010b07540c0244c2c60030000b082c01400c5d5000280b0200386419242e80007204c4040c002841d0442c1515898107454480c0440381c420f4a0499000554504404041c001800900583c0701c0050501d4070000b0303042003290107401c666007c0e841c2c16600351342d040e141941551201e0f4001700030a51a048070121544120050401d9110404041745444113403400a42150006804204c130b0301503d80220564541c407001d001c2c0c00602c1804d06000d425561303607002d80605240e010781c108155036401040c036140400d4000d20380e528 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 615326519 1250 615325269 615325303
    0x3270210120f02180108070c170d0b030d051b2109060903010e010b031504050d080402180a06031718120102130306240f0b030a0906150602160e04080903 67
    0x43d06034402440744d4620001e09000c240c20000003440d00d40256002d411f035640c002d808040260010a10484c29080318254036000396907200d6a50180d1401c0140c40069805a01d8003511415008186541c002001c2c0c0e02d03888680020304611211090748002003807002169010310303200c20504020030454001c4180040e415030a00d051000034080c10b50106801d00c1058060340c1c0d42500000b401029940305844c020030551003005140d2100d44a00051500b00384014000d19001d1000c6090700c03061300f010b036220703090b081d65810208100050200f4051241751041a614100400040b506002010b40301e0054001c984007100350f2135001080d8111100840c452841c2d81045440c0e080c000003d041900300c52112005946520b0b0100707422914410403242040c5071201c01504240e41f5403007581024000d61860780c0c81e0303001c1c800020010f0189481d4041d104203010803851401c00002d14151011424440000903440240320304291000d034964055000201140d85a2558020910744400504036240c05 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 615327769 1250 615326519 615326527
    0x103080d05250318052d070f09020c030403020a1d0601141218030a0315140d030c030c021c061103360d0804031d06030109050613050703270210120f02 66
    0x504000314051b180000c9200c500114880354524941d0702c906600688035200c0c40306d50304208040c040c0c1c00500020882400b0b682c00d06030b8030350105810150980040c514100203001c50038821805c0352445500800c240380607409d10300b000c503610312a44034034214019038031a0103002408101031900c0911090384507100312556502c075424014001c05c1d0803031582078950411a40090424140072800311800f100030840f00e4480e01d140e4064034514604001101070140100881016996140180d604005640b4904446034020316001088136124902c48038034017424018402d82e4142c2c10101036119040e035891074a40b19110b410105886000b8001d4038140c071811401da01c0713043d40b2400380703030040d8860b813240c0b4958401030900c000b044072880d240d40d0b0040310500c01000040010341100750044006000c03003e07401c10843e03042e0203a40d011101c03040480d4489040c04014070224694403000304903107620001d4080c107030b030004080301c2030f140c8480300300b00000f00440720245541d032150002c0280c6000465171 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 615329019 1250 615327769 615327793
    0x703060816051f080c181908060f0910180b1611012009011b061508060408030a0903120912091e18090602030103080d0525031805 57
    0x40000a800303182c3c00340070703291903002e440803040025807640d4249440c0c0d00643d565940941040d604400310940705003944c510680101c1c0c0740d4a89003501c0075040b8600020160901007060301e090390140101c1182d4030158200401030f0004198071164038002c1c840071864013400c1c2d101540202d14200b004d09007520a90511402c1100202d1403088880a52140b8558560a40e03146080307800c0c4000d0001b0401890407544500402100203002e10360050400d503640c0d5041401d208440d0741c000404a645c16a9054840b0303000746140f16400051140e50000c2401d0711b010b42e074903601d0f80800b40020030301301c4e2115214003c060040c1513401406000c03403c100f0840c030701410100b042440d056032180c0429131241c00400d0380360590704100542c442d16000316054034541041c06010340c04603814992920f980e003840300e00141481c00254001c5004554040d26074144143c184200c40000d00401d5940081d040303c4441e070000300740080c2188103c0c0c1070000b1217100070300d00c00140c3e6007901c07001803090003030341c0550503 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 615330269 1250 615329019 615329053
    0x4090204050f030a030e010e1507060605090c04060e1c0503120103031404050906010e060c0304290c0d030e1509030705012d0f14010602032205090a0507030608 70
    0x320751007191841400b0240d07800341519410722a20280000b07000d81294142940501c4403041c02010242409001840300c11800f80d2542250340221a600d07154201009a450403510384d503005580c20426a1400382317000005000c0b400c640c3c0f0028003c1d40808013082d45007480c40c3d2603420461f0040160380e070b02d00a0310352f2500450401d0100314041800000c01203d000c0688064805541c8003810707003035864039030304015603d0045120000341e11440c2041000a0b8020500140006080c0c22601454500714000d4103000000f8915003210780380000c0c850780c00e05541c00600400244207900b80003521254994940b400d2400004a08448906410a02c26094400001040c072140200001c01096501c0154510004a40b114502000e101d500324071401c0d0b007459006400044001d9400500c040d004450420740340c000361b00100168002040101008503000c41101e00d22401c4c40d14004007604100003d212154040d10f5154081d503200005400c65002c0c1d0b1100000d41803c2c401c40b0441603900000314 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 615331519 1250 615330269 615330277
    0x210e1c08010317030c030402090a0e012f36030102030c07110a060203250f050a03080106020708190f0507090b030f0613060e1e01140c03130b060103060b040902 70
    0x12022280511143c076142c1811059900540c803220076186142c855408109140f07201a203c070f180940d4440034440905024800d000c00107001c44a9a180c21922003030051510742c01e2084044454420010011590403070a0036440c0710002410300c0101c801c120500008005142003001c3d010740c40042449440c9015402510741c3d035124803450003100719250b09101d105099840784101590042c40419200c20a400300d2052280c0d01200b0303c0e141e200a07407600e05a100c1c140c40c0584807504019400c2c01810b50000000380500b60b9400108061850111440d94402144040418409180060b80d040044401c42c4201c40342d00003007142c410035101c6e50b140e0024aa1031031902c1c424807890030381998048d408030f0300611500c420540c58616203816290070f006484550201013650150381c01c10312450651a1254164041c160000202c80c124001d0300d0031564006060242840b0080c0204411107240c4140b21183c3e83d807000a01d155030302c5010040e40582055042001d240d0000b09011451a210f64098 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 615332769 1250 615331519 615331523
    0xf03061012150204032402162409080c1e0c0d030306182a05030a0506040603020a060809070e0135030f09030709020901090b0703120c0201020901020c01210e1c080103 73
    0x101000e002503000d41c01f00d119180070300c1211302c81e0507032200100300b0303807044502448400d00e00c0c1442c4020303c04800c1c00321203041800f10381a01000c02c40300d80c05502044000207003296030300c58030001202290700c50b9030b865a40490310f1003241605480010144030b50071080051403040036034009000041c9420001e051099840101c2c031014402503c1e400f0420341104807100d4050b19201d2079901c0e1001e5403009004010017a6401640740e010000040c5c455154142c010041d943c0c50303440c1070500703107121400c202c0c20303030300480b10849900010304c1702240821047e084150400c69100c00d41010011002304064484604445800007241c140324034500440200319107002181940e01d040d494a848100b240951010f042c0050284041400700000b000002d041060003070400010440c040b85009060310729a070030560040c0d402040e803404030758040004007020b00c1c090a11a0a41060340c01600e64054503208030480581c44406036140c9490a100c004401008882d062040303130803004004d401307040c0038401 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 615334019 1250 615332769 615332813
    0x305010c02150c090603130203030a05030f01050d02010509010302030a0e07060e12030a020a081e0a0908061b0f0a0c0813081203011211010516110f0306101215020403 73
    0x70b41402280e14003038610408100510604082c042c0f81400f905400c010003008443d40080e01c1e50300175960400182454054275035809603286000f444c28400c81d881130f80194003500c5c00d10403044c0140c0e08502550706011085c83d0043e240e0ba01d0305d840c4c0c2d018100070350700d440d96402000c001007111030f0300030343d071032603100041d1780c0c460000760040d00090b03980c42094001030050700907140c00000190341e00003c180c0b060107041e0454a415540f1307280081c560010b18401c0204903101420040110300307110a83c2d025515650500f500d102c001091001841055030300340c00b0920004804403103c0c0a0070101482c9504060619183c400c040940d0103c01103500921030310780300d42c0801c2800000b41030101c03816900514030160864042c3e40c0d515034410309007044030303040c40400e008001c00c00504003600500c3e18080c0c820502801b8044c0c051000030041108158040d0304494100305d040d02c0f00d04e101e0f6040b5500141e98a10390080350402500d150349104103d98290300004001007400394003610402d1840c410301c1 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 615335269 1250 615334019 615334033
    0x20f0d080408150f0106270e070f0816050d020c06040f0b0609010b0403030339030605040603021c020315090303090d080103240e0d030f0b01050309070e0603160305010c02 75
    0x9003140f02c0c50110760010302204c4900c014030800c0c0c450313004808800c1c42501c50141e82c0500709502d0001c0400c0d07412034507080f0288400c00c103880341e112052000341c15803814154903906211480c2141070000701c0040d800d102c3c000030283c2a08507141c0c1222840d510100c1aa14242000d2030a10903200e050710064450f80c440b1400310b1950720b0000284c0d0b040399103114501e454240ba40c0c1e07017900502150b04a80d01304081c0d0094609410b44e8040740e9072a91502c51240d25800780c1c00300800781c1294011707009640100d1034840f081c00182c82d8000584102030510001603144c0403940b00080c03424039804040b0754010407940900c0040f8074004050342c02400c052046d1441c4550b000021503078500240710241000740b00c1e14140b01c854414203590a5a000111000f00c2ca03800044c400900e02556802c08100080e41e03080001c02a2143c2e1058454050742480c1c194614200020869034a1516005001c0c050821102158160f03408002820780c001c40c01488941050b41d0f81030003070080c0810360780034016000d441 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 615336519 1250 615335269 615335293
    0xd05040320010b151c09050304090c020d022505011202130b0309071a1207020a0b0c071709060f0a020c0a03150c0c0c060f020a0501020301080303061005090a0b07020f0d080408 77
    0x1050301c3ca07101c008034010048800b0ba17407842c005400e8840f01518640010040810006000e0051440001d51500140b107022410203000b443d1281c004140102c96001d00204009981c2d903001d1202200d00c2440e00c5600c5400c100e004400030f02c90454080420a1020400601699003a000c0d51140e003484003030303501c0c0070b55500c01c45401d48044241c00661140400c0748070514807040c1740403a004502441181c0b260390003599030451105050f2401c03c42d8010110387c8100700024003220340d1400400030903c1f418005e5501c042695070040b500801c0145401060740d24040c0d06c02c200c0000b20b03083c02000c00800556078101240c140261450020629003041164079031a8002c090100d1b110354030543c002e00b2245891421207030b400102c0030342e60850041c40b0fa0040030a60900241d8042d01000018681d2418168104000d80650030350041c2403002c00e11054206d60741e00c00000c800c0f41d451003d03055640301c0a1001030040e80e102d064040d400490624004248030222024100340e4054008540001030b0750 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 615337769 1250 615336519 615336559
    0x21006080f120a1205040807020d0b1014060307030e10050a06091415060a02011d061005030706080a0218040905010c08220210050c03070b060f090c0d05040320010b 72
    0x4541c0324022480e1380650684d4554543e0000394401d000380c94140c03c010b040e50000b40005a20001690500142814010100241c40c080c1008103849034548444a0007040480c41d5400010114410305503903040e80c0400c98410f2110b0600060f00810400c102e2400c807002c1c2c0001c0006001ea0400315185c40c0044082c0388100342414096032042060540d021118800c00425501159a40341155242e070007240c0c5c0d9140e040380d42211142c503140a44500c1c5800041c1e1072000c00e0541c8501e109a001a6081040c035810148541c0c0201c00340401513070b501c100000c01c4400041c140580ad400a1416881d80c085c8001035004402c0344000c0d03a03c0003401c2d140c80700c90520403210300142140904614000b00c0051824941000c603210440c00c045003003076400900c2c5821070b0001201910080e070407504002040c07601c20380000004104071032a000d05e08007100d00c0c0b8054050000604603140d600c0c00071806240c000c1c050150009100f82c0c220074604007143e2002e000c1c21035003401600400d000380f0010603164103 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 615339019 1250 615337769 615337777
    0xa05060105090415180b03010b04110a0305150604240f02030a0804020d0b0c03011a03040b010311150d15091a090a09020603040c0e0609041e0201021006080f12 70
    0x10507590141030030303002c0c0304001c014030403019100d41c1c0c04524000003e4030380c1e031100c00201004401c45c0028600500d02c082c1800d503031080d0f071614411440d08800408003d020340548000e14020302c1e0000f4141d90320003420300c1c1e01c010341005684c030203004200080c11201c1442c0c1145144920f91700308d660013040c1d103400d546000301c03c070a00000d41c00030b02c10381e5425480341d040d546c0e215000030445403d00043d600c0300140420305a405990400000005200d020502d20342242c01c0c143d03003040c0600c2c0d4a07140d00d44450056044c00001c10010355008000c0c055a1000e0042e088030f081003503d40c0d607030742d003200d4902d0082002610042103500c0415001402a00600c51140070203994034651a22400200400840c010b0080420078640d071b603400c4079009602d03014042d501c500c5c0305801844c07865007001d4a402e00098000c001b03074420822441017000060303070031443c182c1e10034103d0442c0301800ca03a44010307030038409030b401000340103072401c1c10009080d640006d003031140803240302c01e5495034410f100a603080d504c1 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 615340269 1250 615339019 615339031
    0x60e010f110901051309060602010603121b1403090909030c070b121503071206140105040b10050f1b0c100801030309051e060a0e090c0702010c0f050f0d080406050a05 73
    0xe040c002c05280e94080c000800e01703241c404004950450b01c0b0203212007100c146801140043c2e540e90b605004000d40110541c07041080c074102124003c1082d03419000180514000810079280b1001440c20240100b00740c40600038020000c8119161280701503a0301d03000072072494064414040000395020300d480454510f10200b4900490700c0e91100440b84441c842803100e00c0d0107204445000031504040030320004060301ca90710105084000e0020041c098030107030003080c482d514000c1204040d40e9a840c054001c00715a04019031203044500516440c1c0c060762408003141101040041394800001c1800d03407440c0004c4401742d42101c10340740110b440181c00d010060108504c00814060340c941502c260f0b141a0701c450680700c2c1c003021034000ca4995002020705c40c000c96003803540310b4014604040d08560045000104030b04110072600024158041554080e10b208000c036031410600034180108401403248000310b0b0310840d4040da00800039041190700750788140c0303080e0125100305964081d8600800c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 615341519 1250 615340269 615340301
    0x30f1017030708030403020c09040c140108090a06050402062a07060e0d061e090b151f0c0615170f0c0108010b16060c050c0f01020301030308010317040b07060e010f 72
    0x4802959041c3c6681d1010788198150f10804180c0c85c020740d202d206d09885913118030540c160b1246040c1d1601807014bc0706842d541032100220411222440000780751018542048000c2420b03102e5002003881071013810300f852a6020b60410310004000ba65141d8200d2008420403181d06c10b40d02c14085501c10a0140015407254004450754041034094100940100b019000e40ba200200010301e4002c440083c4030480701994208100898a4801080707a000c50100390b88544110b620390b6034850002e40400a0070081c4150703030020006000e00e5078094965044022280c0b1000380d00d420380b01c1c0203900b5900380003406114000740580061004a582c0c010903c06844d00320b15a400d040c0f003600240c01030082d07501c1015072038014001044950080281c1d00e480c41d124260b4500c0c0003104181848420036251442d0780c01080100000390784410340904580e00107110f00d82c2c8446501011925101e117601084c1e8170180400c1c07144c00d110390f40d48a11041501038008102c0f0800c103502c100113841620520701012 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 615342769 1250 615341519 615341527
    0xa05010b03010b18040203160206070c05030d0c090518040203070603020708030c07082106030c030106230a0f03060f0b030c010c080d0906060b0c0607050f041503060902030f101703 79
    0x5801c400b0098501a1340a03201d9240c0c903076200700410201d8000f05c0c2c00400440b220760490608a805000e420781141161400310840e0342d883e101c0c29901c1c80380340c0040034155504d4680c80c00780340c82900c0550207400010442c56013284107800355541148151001d03803281c06107400c0040c21034081d04c02c8410b42036121031064110f5880201144282c1c01006082e280c1d403208000c920200560548a540d0701020101e00b8061030400c4005e0600e8811840305403030181e0f00d4110144840340007550f503103060081002000c9019030428001c500d10084076400000c0d5003024800c04020000942c000070040100304904010700345036070f400c044d41c51000198450105151224000200341d904c1c0040404d51214180400c5000640e9246c1d41140c2c0f0742d82c001d61800700c001c00c00040b0407400b8010184c0003882450880d007003552104e0440c407180705a201c3d0120031640768003144070540c000d402c00001422800801c540303a03e40404950311f81c030022200c8103c1c480e40340101240916466000f41c5100c02c01400841c10 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 615344019 1250 615342769 615342779
    0xa0b060f0f090c0a0324050f04090204020706050109181a060607200103150312230408010e0609010902031209041b0e010e010801080a140a050a1b0f050108070818030409140a05010b0301 81
    0x7408c1900c1c07400e80e0007948a038010340141e290b9000811600c4c0c4a054002001c1d85400600c108488105a42e41100078003241900c001c503810884000c1083d04d001140c05068482d10000740c203134442c14400501120061421801451012140c1a1141000e8030144408140c2d0400c81000c0541c070b010003840d2400c0034a0540507544155200c4034202d00480040d040844031200e03062080d0031a0b40302c40c44e9030f9107480410170b20720002d000d80303a0009500d5000f40102c00b51540000e88403501c2c2131107010301c3c4101040340c601d5541c55402402010003020181c600b0603e190070020840c2d01e03865151030219102d2901916a035101d03015042c101d4480710003030110a00c0560703035540811032220041e1400c0c4160031418001c55014840000958403d07000080c54210b00c0c01c189000d02515071005c9000350301004204900e076041001e29a101d503041c0b4142c03881d990361014000c51401c81c9c0f902007249101c0841c0200c1c2c080c249501c507200200c101c010003116607882c5d800c908183c2d00b090103100c0c40b140041c801000 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 615345269 1250 615344019 615344029
    0x909060e040f0615210215040e0f04060207021f080601180b0a0509060d0903110a080d02030711060412030e070807260102030f010302120a0b060f0f090c0a032405 71
    0x1036089941c0d8031300070b0059070703020702c81d07405082190300e90700000e00104070340f007185040143e80e00710304c08018009040ca8034040c28012115002419000c2d0314062000103010410140d040720002903004010150051000d00301d030360031b82c40500030180400c01030804501290f0281d1000240c90a50100c4101c2c81c42c01e240c824442a006213002109000007071008020765035480028003142030003d0340000320f420844c10010001d03008940355a980360841fa4812021905000448810a01000c0e01599940300ca400440c1c48a0320140601024000c2c00240010009482c041200d208000d0790140102e650300d407602d079180c4100b80310f0401c440e8004641082403040413203188041302410300380780a0302c015840701d540c01d82e1b00803101d25040c1001c0800500071460401d81c0d0b42501c11226004164179030041c0c1c0d4008404002800040c400c0707186807c0700c01030b580c5850743c5540c1040c002c0c26022050a0440c09408650014a1501d01280c10300d81c182e90322003030500461480c00b03407418000012901e0942804 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 615346519 1250 615345269 615345281
    0x20d02040c050d020c06250206010608130b0411030f010e071a07080d051902030106021911180a0b011e05074404060e120f010c0909060e040f06 63
    0x180a0080a010405400050344091701304482240d02a14641c07408040390041045100542d00c602d82c992a422050158006020740c19250241002d07085512841e04074400d44881d8500100060f034a40204802c000c0300c8041184405825021030b00c00c82056501242600c0070b2003116034580c0e1290f0340810080b904c3e031440030064009206400d16200c4181c0710b103d2180d10980c0524003868462003405441600060141926412a1011270840d4103000009441c2d10258400d2a4000c82e902e10b12004e03c0009260700c0000340005004002036070380d204844810700f20483d8040340e410315082c4041481d500890903d9107220680c4040c0750f121610300400d0f1682d0b00034900544603000d4261407800d41c44914241c407840594850141d0148822a070103011910520b400040400b00c0140701c1009496041144080004021524020003140786010fa9180c2080d02c511201a036082c80644c0c1e1600347c211554034280c3c2c4070b8603030500440740c0384c2c0e0500b0340c80401620010140203410042401255860b4007107 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 615347769 1250 615346519 615346541
    0x100812070807020a06021e0d0905010309030e0406060c0b0117150c190905040507020705011b06090b040309030c0b040e1602151f0f120609050a150204090f0504020d0204 74
    0x8603081c03441e0b58004c508201190f03009540568080342c010410100c8030600d820940c02e85030010700140d1124980107207404103900c0340300d0606499005020402d400b504060b24190000b1b402000241e5540b000100156480d60068401c000140004980e803d40c941d0100d024603074800c01044621120114000c0c003080c010b0546440d04414003010000c00011b1001441030802a954483c5840c2400c080008450303014110505541c802c0700100010398000d20380044845610740f1000e50904c0e182004800b50085040080c43d00c1c81840800c01010b4005044006490181ca0211007481c8c03106130100580c819405168140c0031114002558115403007060343c102c28151058a040c01c1c00140002c0b40d001d02603458034104400c1c540302d007034501c0080700958028207003440840d00c141e1900e480800700d07014040d0702411190315940940b003481002c004003501c01d50b000714950380c0400d230000028020b400501981111900b0102801101a05405114000c80e0020705040020000b40d0070070000f802c01d1441 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 615349019 1250 615347769 615347783
    0xd03030e0a051605240301031b0902040b041403150f07051e0409150f090510171005160503010b180a030f02030d05070206120402040b04110d050708090a060b01030204120f060510081207 81
    0x1007850ac5090024200038141e1440d865180ca0501445c055140040e4149a00035401030708040714070413500c204240c010b18900e04040c0d2036290704104a0705441611000320301c21f100c69003c0440201c490f07009108403610031700d08000d000081048080343c00c40c580b16241c900c80307001800b401404056842550010b40044000c0e0003542c0e512201d68040003040d0a900392500a600040394820080c00340e50741c0104500c81450250340d505502503c103000601494110350f00100e9941c6c030324100b5541e090742d01c690007414400480e0740c80c505203c00301c180b42d200303d0003030042c01007400030359009405407400c0940c020049414625007a0741a0484d030030003032050382d03c10b803550350344a1300f600c962054003442c002c040304003560f0304000650007041d1203003d4481070802425204000c0040000f20b80c0c01e40090344214007080803006840101c2c0640101d8100e040340481c04a055000c0001e261a9202114403e14003888540d885ca035403403d5038039851040303030502c1d00094030307403000280114000e29840744a240 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 615350269 1250 615349019 615349073
    0x503070801110a210e010207020a0e0606040b1c0e1c05040e510a031113090b1305010c0207050a05010302131a040501080f060d03030e0a05160524030103 67
    0x31310134182c80524400c1603069500203081c00641c20604540809081000c00d003030300c5c034241107000c15443c0c4520b202d101003101011519800c0e04121403024a082c40c00381e40240028445080b0442e110810820003000a1030190800c0b00c400d40a04150ba0444c5c2c007007210440e403950340b0217448401000e42c500303454070b25511800300b6040140c2d6441540280c2440901c0c1d82d6261407030440044000c100c2555984240750054003000000e01800400000e11010303281c40900e0426849000702400e05118020200c42e0f0b80410004003e800e46210701d2402e004400902c50303c00c0340c400c01c2e0f031034002c24019035401c4100b100d018031440d4003d1300200403080d0b5000140b00700740c2e59154055841c900003d804c1143c1c2c00000703010400c3e580d01450039900400b12000540550a050f070005204100c4404003e050540300d250302c49000c001440700705041504401500c2d4400321035a03c1101804140c040c051164401900360520340f0420f445030b0381e103442070605d50f6107140d0075600c40f40726107507000100c148461040e03e = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 615351519 1250 615350269 615350327
    0x80f0c0601060302031608010f1a0705190b061c140c04060f0608060102032503090806040506010510090803030f0a060f060504030c051203030426130503070801110a 72
    0x1080078000d00c2d10350790058070b0f801c0c00c410301c07030212071441044c004005000c0014000551055050702c00c40352003174a0410034260031044801c1d2070242100140c0b1f24020080e01200120318a041c3c0d181c0340d80704085081e2039960700740030070050300c55240550303003215100c030584000102500c00d402c0e11403c846003104c502c2484400000e058444a80250905800c81c4100b0881c864002e480c054007d2402d00256090004a0714985418000701c1e80305031100d4945040c90041c18040c10040c40608030b0308050b43c101c0c0c034007401d24990782e220a1181500030000e2801d80c98540b0b208001e1401a82d2400001e1803840e10741203c030f50300400c0c0c003403c940c1c406a6500400551148000081c00040400e502c8480e20b071861801c3c6000f6081c0b06501c180c0c040c55280c01910071442c0040202c3e944198400c1d680c403960200b40600450000c1782d11048140114001400c044800c3c000c1c1001d41250320807000c0310203140d00c0708121800d9450341900b1050045007444a074140d03c1c0906541801e00c2030a0055406410841c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 615352769 1250 615351519 615351523
    0x30c04090c1701050906040326270601120318050d031d060304020f0d0c09020d0605150903190314030a0f0b030a050601062106061e08070903080f0c 65
    0x19210841c0c1941a03036034200310b54600c21550000516602000308074515010b0705c10754660900410040030030000780040d004003d9400e080a20131114904210014540020040c1c40510780002d410310075075000701d00c0e08072000002201d03810381d0030f44a40500c1e5a0200daa064030103121071040d0611803010746101042d0fa0f00c9022220742c0c040e001c0d0707481c203003001030503004040c2c0c1c00ca1b100a1140156001c0080002603142c0c40110149401c040d541150f1085590505490f56003a0350443c2d041e5a00000c1c10043c064030303540101c2e0a0703400071115030214100140c00341d05540316001c50f80b80c0603048035100b000203100305182c0003002030190030308800d058000540d1801d1580304549c28407680d65203a0103420030061a125840c256030083d4024081c520203610b80981c1c484d414820141007211004045690011410144040c00c5a2007403d124541d2540000f0b442d502c1c52f14003805c01c40d00c072681640702c1039100321581402044030351150344e00e01341191680052588001c1c4070300340c001010000114142c0003 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 615354019 1250 615352769 615352781
    0x1c020706030b03103e030c0307021501091a01051c11070f050304150f091e03051b0f09010f030204180503071101120c05030c0a020727050c18010c02030c04 68
    0x1031281c245000b00342c601e80c03811780752040965281c4c0345414031113204004030b00da0308480d005054044660b03169a00c0c00002c07480c010704443e00b0358102e01d64500014800c81141c000342030243c030001c51180c0d141404001140c0c50b003e0a03d420050003051040c0f214400f00701d40c00401d101d91840155441d00041da1540c02c81c4540500d001c441c65440010200100c6032025296501008146085905a5030122004000307200301d009951142c00d140c103285100340040a508002075a120701640d8500402240001104501d150b00a0240d52030750480d4000386044034001d8169000301d480c10000703908540a000040426040c511000940f100240e000301e4410400703055010b1007604110060410300000618903120204202c032040d09203c840000e0b990000180c0740d1003072049000c40c3d01c51500e11801c82c9030488652065910320100ca0000d07448811040d02590380120507071003444103850f55040070f24144034501a40031034542a868904081d17204142440145000900b00d446014182d4009421907078 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 615355269 1250 615354019 615354041
    0xd0608030f12010902040302010f030c020138030c010c15090b010801021b120a031104090e030a030c142502150a020610031106070f1a091c020706030b0310 68
    0x1c08034410307841000e0020725602610b41000154209455a8006000c50309a02603400500d5150842907407124400d60146d41030140810704003130301402459000461300307c41d0082e000f003600d191452407a10f0400050706c286580c0d041c0e551441a03005038480388a11100700c5580704090707032616002d00104040d022610702800b0300c00300042c2d95800f08442c015016089110000c1150040804d007159203041c5015149441c50f41cbc10045484490407070711559500c6990030441d08246040b1f00c10100160010140c14449682c0c0c408000014080c8001d0320140240c8031801c3d100c403002c210540c55505003509941000d05c040286216001a40c2e000035803110903074041c0b2032060008034902101035410007503242c02c0105402c00603400e900710340707c80b03000c2c5040048190040074002000c9040029120740d0b062099040f0703040d541c9024014401720060314065440d07080c0c2d44100301e0b000515600994030344c00701d0385182c0c00804032507140a0094016158402d00250301d0700515090540c049030502034904440 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 615356519 1250 615355269 615355297
    0x8031e04080a03121802130906230f130209150409150f180c0e0c071b140402130612090203070b0d060b0406080403030f2403050f0d020606060d060803 66
    0x1250b040520200d40442042c5c030145485807900c036001d80c03201d014401100b002c400000c01c0304c41c45401c04502070440c10f00c0d590419807043d084c076910201641c03103043c00713100720100c0c101d07050321507849490288614010180d40b0a00c840c020031300c4058807051000b2080780c0a00042010366454443c42402041204507100f140d442d848a401c1d415524481c0403140340d48400c14a00905154a680705d500001d80920540000442c0108824041e03010580f2805a444644102e403110140c4814642e8130a40c4100c40d80942140c0b4168000c0c58180252201d254907104d0840032a4541102201d009401e60203021840381d071408039001507181400003201400025508a82d81d00301a00034408851461740021b101c00030900c000c1c402594000f1403103400680501d03010900c181445d000070f00800300748642c101202da50050b81c041d0490309992000440b03002e030302956a01000c00c4d0995803225007040b88500141c00801c0004c80502e0620041e200c040c09201c40052040e4030f502441e0b14503404415205009 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 615357769 1250 615356519 615356537
    0x504020d08032403030a090519121103070501030b06071b080d08010509070f080406110409020a0e15040f0302210d0810050d11040f0e030f0a0e090108031e04080a03 72
    0xd03e44a5103800d070108070540046141240c2c009000304219100d00030306100b6444601c640c42d11558800e00d00e8003400140280c440049060301d00170700501c60300000315010b8003070440c00245940c000e101d40001c0c264041c006625103c66583c44074001c5102006411600c0c000200100e8a410200500a255540303916501c401c0e50420701088043e00340180607104010440940700b01e500c2c1e22400850708164003000104105403075542046640c020350f000f4204051010503804a095803000d5049064941034426040c00c0381c01c03151561081c860342c0100610300e03c41134070810060074070070344564001d10114100c02c42d03030000c07509035400c1a12400584002a0382e22041c031203100d010074500001800c0c112016042580c8503500d81c0f682e1004030050501c5655280c000b02e1480c10207401c0f4000c0c142d0b0b81c1c4141d0360f5031440d03450b242014ad000310340e134100022901d1040c0100c07810544a29030580b80e41800640c20044030500f68031004000710f0b040b020070b40d0188000500413008100010600340300782c1340d40d494 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 615359019 1250 615357769 615357811
    0x918150c09080606100f030603080a030219090b0412051212060307121e1a0c180409170f07050114011503021315090815041b06120504020d0803 63
    0x11403007075801c2030640780c02103424014107030364501041c81002401d04080e1030080280b441a4020042c0313070300203400c0d4100040c6010000d58942d0003807442401107902c412030060503240c2160500e0032401030022500b01004280540320b201400e103110b4074800c10460700e120140c40703070541054011010404080c2c10100500449242c01d2100c003010301343c400d441d0281d61510f901d40343c84000e5048900980d46030480c401c0824001040f02608903690354450840d41030400d0129042d45610002c0f01440c4100704d1707110701c2c40500d400d010300b45140e600700148e11612810b000d485443d50340308501200c5c1a0b00100900340014000303000d140840c02010010158640c0b6010954540d80b044406003400c16204010500203e005481180c065600d6840c11600401a110b410348140000b9088a0341038071504884402c00381c4c2c2c0d0349810740708901c2003e030101895001c030b001d4201c48280d070045034007159400e4a41e46401074958400d660140c0002e01c440246542611141c2c07042e8401e0794120b9910002041c2025 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 615360269 1250 615359019 615359027
    0x507090506031e0411030a1407270c0e03100c1e0f0f02100e010f0605040903050304110d020405070201090b060909030d050c090307080f0105060a0608010918150c 71
    0x20042030140c841c00c2c518903088400002c4000ca60005100e5400c0c5280420203000d200d500d60003603108040c2c1280c42010050030300c1c415021001016120034031031007401254503000d61400130503819090100c00d01d1401c041d032065026144001304003007088840e070100c00d290342d020015148074a40315500054041102c040c02860000e00d04c01d912580e103601821100a00d0384030201c2003490155180120400c0c001d48400ca003000031001361990070604003c000581d160301940804100d2581d95802c010304d56840060106480c880307030026021030b01c24070000d00400c80c0c1502d00e00d2541c20003400c800155200e07a000400300c80f001c2d00c0307140050b95a00d2400c010064402d90b09034009004130f13035190852070310b18181903481c1704184903840c00a8484d00490604113014069844075036000b000e50322a0394444076203a68038240c17800040f6a96007802c01180141c18100e171201c003954865520060b5030381c2808015400303008811040b041480740b103031b0301d00b022030000103c44603140703801c0002040003503010360014 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 615361519 1250 615360269 615360287
    0x324090a1221060b0304060e0a0212150a090503040611010921110a02090c25080c120a0905101209060e0111030c070b13080703020102030a0e0a02011409130f0507 71
    0x403441e1883d252040c80b09889000079240d0095210b01c000c9032646122031614248170381020025000141c8500000e41c082011031680c0304c050f0945005c1e0f51584c0c4130106c113410381d8004880a80544c00820080c440d45210741006041610300d4000412100c440c3c1d510307500007508400b181c0201081e02a401d02c10180d000d94000e90042c00b83c0018609052207800160884030081c00c00c2c2007028000829054034220b000c80d0150300840c0076040c548584060419041c1607000b208402c44501804821ba820303c862601038840701c411070b40d41c003410b1034200001d001e0103240d001c0c403500a0007440031501c01c05803d5401440c0c030081c840e04000c900c1c1500900c501e425246102c183c1d4402000c00d104000c40c0141440503980070a0700090301d580d8a8599400e51300018600d04c0b0301401d02440080c40a0501d501500158098000c1110401983c68240300c4142c891120f800b000740042d006804491486460030b01410011400412030304a0310703414180b1000302e4047c0d200c148001500c500030080426000074400c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 615362769 1250 615361519 615361577
    0x2040e01061e231204050d0f14070f240c0230090909010509060f04050a02130f02070f0b060a05060f0d06120b10050324090a12 56
    0xa090700009451035080a08104104001001442420441e060100200070003040b5003204601c0d03580da40c444c29058030030408a5094569129441200c0f0406205510b060903801440e60b4031130100003000c5410a195100038400c0d81c402410600c0c0c0300200d100090001c1c0884d6581c180c41e4442c01c02156400244c501c905041c0381550090014064050803001d000a03070312100300c00d0408800720060b00e214140c09101c4201c2d820038604001c00060000550105000b814003000301c1d41c03103540d8681a05480e09086400800b2038000005a10050502c0d5952850150703100f01c004c180c844181003d18100d0304503500640369440380490090600c1144404250010700585540d400d0a0501000c2f408502c507c0f03036200c40d001400200c644284055500560150000b4194546031950b41c0c2003010002e1b00540308500642c0c074003039001849103030010721504220007080340d880c845054002c203800c1008001b00490814020000214005039040d00d5101d41c081060f1550070301c40401c01004070a522043e9a4 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 615364019 1250 615362769 615362777
    0xa0e090702031e030402061e03010f08120406051c1109130b0f150708030103110f031c1b0206030a09120914040c17091c021609050705130902040e0106 66
    0x1c0d0808103540714410b0341c5140c003c034641e903682c2e00ca9201180385440740c0d4050071044203a030400b40f480b003504a0001e40c1203030300010b01141a10307101e1076025200c00404086c0034141c2c10800c0208a02070181000d0300950060040d12130451140d1513606e02603403a0042e81006600c40001c1528061618400300751000c0f003805010030008c030f400000f02e00300f648880051446003060005010f40340310403d040301c0c8e00a520844e8a0345030b59581c0f6200b00e1150300708001c20722038000000024454100007400440340280c06105e1b600c0740714050002c0d5100d10030020a40081c0022280f031b000540c40c1d01d40258002c04101c00001984212030502080342038081201c181000500b000801a8880500210503184002c850024a140500d0019500d100520180c0c0029800000802540c3c101c0403450445503000e4494811034400004d1080703032078540940c41901d41d00d100c2c0340148400c80c11681b2840d03024040b401c1c00e5207000084848020031000702e074000d101198001609100119801c1c42090043c000750070 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 615365269 1250 615364019 615364027
    0x503090114100b0c03040314071a0a0e06090f0d052b0c020108280902010219020105031b07022d0603190e010609020408010204080613080f0d110a0e09070203 69
    0x10302e060585854400c001d00060081004030020300280202e500544c1c2c4400401400482a0481c1d030321004640326041c40c200901c50340c0c00381b003083c0310b08075001c031002652803282000c800810002d464200b414060307080102c002c041c80498640c44c8150183d940100300410200001009004035104a030016440650380c9001800607641c0116091030034680c2401c1100079503480010750000f00324040840c1101c902c0001c4442402c5815074880c0712054000e034240c0385c3c0f00801800480554641000003400280c0400015122a160b642e6900503e6107184e0402d00d0511260000b6900a841c0751003e1910402e8090b030303500c01c9070b0f906203001e504003080e18810b046141c60681c41c45081680050b0000b4961120102c07041450203501c824080c0c036409038210f440700c4c1c8030140c0600030b4220b4003e00341c4510a04005c10303d002c188a244200e810b60004015241c21300d003028082c40c41c0c0060040c0480c0c40c2d16066001d03610780f6041c010700ba151900e6658204210010340030030074078400c05880c26095400c100 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 615366519 1250 615365269 615365281
    0x2190203030609090c100503060f0a03030f17130f02041103190c0206041505060406030b0115020111030c090618041112061e011103090a030c081c17071e0503090114 72
    0x20354101e1b00c50030f65007080b944035030b190800f1034003038490b1072016988090139000200816400c62109000310340c1980d50700c070030040c40d445020b610f10360a5034550381140b0328805100010b5107c10448098a2000d400411403402000c80400c2c5030b0000d941544900d150802d01500040c11485160103031003541c4011700d0103040c1516002d03008485070300421705150300d50000401c9511642c020340000c41e84681c540d1229a075030b03c2e40b01c51110740000e64000650800551210300401e17207003600c1c050464060b07064540036400d020440c80340d01900f0324500d0051040c01030314199541d03105442c0c10303040c00c00c405550352440d4400d014640c1e01c0200f00a02c00e81d03000350410301860340100480790041081c201680740300201c1e0304080c0340d801102c0802d41d2000c0900008401c00c81d031009200110341c040412280500e40d4880c0d1800381d40b022042010020780000e0b04240c010001c2c1c1400c46d00a2034a00740b80071503002628904802c011030554840c0032520000038000404400d114501c94440300c0800c08490b41096 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 615367769 1250 615366519 615366529
    0xf04180c1b030503010e180d030203090d080415150b040f0311030a11041505030a05160506030403080406111b0109200901050607060e0708150112120305040602190203030609090c 78
    0x600424080311206d00001e5620124814880404100d4038111461341c0c1200034024080c0d80216600c0400380905020401d14034040c0d07407014041c44d0300c96540a0341d02411075550340104444107850f21140b080d07160001d51008000020310242481c0414012020304608060361380a2020680700d0007648610300e00c00c045240054030043c14141254045281a43d1422412054107039402c55585401041046e60801c117000612508001c0c4026400d0341c203580d074608000550004032805004220705600140c0080d900c0e5100c0348142d0305010805013041246020041c000d0030303800b00964640e548052210a028131035450009003080070b08942007580d9800302240c6103810605c25a80604004105401003001c542c020b0082c004882088590031581d131150b1980d103c1c582111b41d20703840c02000000c640030604500c2d039a01c068001c40344006580c00300404500402c0000d0050f12815801c3c88069003071442c041c0d20a0600000d9401151a07007040800c200d40182c0c041e200d000143c2c0b0038001c858441e200d03 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 615369019 1250 615367769 615367771
    0x6031c080406090303020c03040605030114030a120509031606120e01020307023c060103060e033f0903040f051e0d0c050a0b28140f04180c1b030503 65
    0x2c031440100d162510391070141c011b40250603a0030401d000105010a403035038032101a5040311892004000741034044020b01d901e03042400800380003103070341410080e4424040c0d8010f0a03100c1000d01200c0600d03150030300d802080002e540090001a007a102d11100114680c0100c45045042c20021807a50030421800796507a103a00502000a64105090b41c81c070300c9082c2442c2100d07103808413903e0b049680059200b91607540c01d0208490052410030b201d800d000c4004180c645042c0a071640810849960f42c080d40d19581c2140c20b07290107544510240075003400d90300064045c0e40540300540e02e030340c10503500d84122140b5401042c001c06000c8400b080811a00f03404104d0185c0c00d481041607202141000d041c00320340d41e0051600500780b0b50002600c0b8911000900c000404c2d035800d80c07400c105039103d984000d5007685041000554003560b0b00d17a4100c889005190000c00740003154039103646e1741c001c01c42c04650162400d52280c2d40300c01c0103040720b400032001e610741c50000c50301d0a031400c4241e03405041c07404 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 615370269 1250 615369019 615369023
    0x1b08040b0d14280605100e0307140a05212d0303100608071436090103121704060b030706020601210204060e0f01050f2d01031404030806031c0804 64
    0xf000240719009080244c0c065000340c103015012110f5001d4010f00a0007000d04512072a00174403540704009039070525541908107400b0010050107034140380c00b040080740c8402c0d00b2007400c511101c07100304803d02c00821005543c0c0719840003507081040d0405604422130800d101c40720a03504100304100580d0200d000400c203a52a50600310f0741900da04400325003442d507042240081b15000151049140c0c1e100403c0080365040e0814503d650030024004803030030b0700818200e6000141c41005000013011280028015549460030b4568080303c03200848440c0805c8c1c0e404c0e1465035907000809440c0c1800d001e14400b800d45400100b42e194940f40070912600d400b003c1c020100701003619104115a07458101200400351200c1c3e98641c1d00300660400f0300e2080038070a075442016045141d15003800c010405040030922140c0845d09040390050b000c23440300e01071740114101999030200e08404092114206e00940c020358401a003860b041c0c1c00e0601e024201c89661004807000031044010f19406024143e00c0b136 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 615371519 1250 615370269 615370321
    0xb030609100b0c0102120c070807030e031914060601050703300c030506010f020d0e0103050a090804060f0201050a1a1002011d01023402011b08040b0d14 67
    0x541c8040c54111804226040000660000160b1008001054021b0b040d042d0b2000c021003041d440302c0407010160302c200c520041960784188041800709010b8030201409181c040c055484211703219140341100a00b0314002c0729000d5071a00c11440c101c0e0108100c40e032200c402c0c24a00d1070b1017841d89001c1d25a0b0600c030805920008140e0b10b000c4140c003103207440c3c0c0401c00c0e0b5003c00d021400b08010090081d140c101c07090341c0060b07089046244190b1002a82c0041c1e019103407640b940c80c051003401103010302002080128029142d5000b0000280781100500003040c417a551400740760f9541c00000e0a4a0010f090090118240140b0000300b0350710030441400b8510440310610a030402032000c0e07014040d482598042000359101c08803046406400620b030700e0300364882e11708002242541d6243d5144012001d041d14010501c0300c04019409071110f0001c404c03074605003520f0b20f0900da840301c5040e0b1064011018020b000b141d0002841c5050040d0402d00e03030803d118100c07524203400d450744003d01e20f41c83d8401d40 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 615372769 1250 615371519 615371521
    0x90302060a0c05030d0e0118021f0905130501030c1d01170c030f240408090108041a09010c080c16020112140c040608100e01090c050d0f0f060f0b030609 67
    0x125000e403201800050740f1000b6641c642485440100c024a03800404441950034040001c5801e52541010440c443d40100314040807080305984440303248548400005215a406021810b83c0c1c1d02c06244912249081021880d5815442d201c0034414881d84450b400103092008401000001414541900d8001c5280d5910341c6203509150b207440c0b4908034603501030140c1110111028000b00e03940420034103442c50344640d4007414141c4041098111030107020500240200d602940c415401c6580003030143c854086602207151083c00c0c1c841050340e03003004580d5140c041c841b4640e00241c0c00c6134003402c8010601d00340700203140c40e1004c042000c02d0003410000e101e81c150480b1207541c0e224008184120290102618010a001e000b6521a0203001c000c01e80c2c000005241c150211500e00541c0c40300b400d010080e0b40781c148010b0142004a024009001050081c0d5005000c00d1280c1c1c40d00c00c90200c008a8046075181c407060854041da0420f0311400c00e425418401e4000c00801c5a402020503150451320f = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 615374019 1250 615372769 615372787
    0x2208030d0c0e04050f040b1806010302041a1206150f030307020904060e010218040e2806060308120618060117060d0c0e07121509240602101401050109030206 69
    0x1101c0038100060383c800d207008103001c0d80f940b0200d68036200e2407003030040006a0701d41c00a2156040940680c0017080d0780305c1e00040c001414607421001008403080d98208036100007000050b400400644003076081c0d4414400c00107000c0348005100c8805005440b0404a19001c1c0d01103916480b9203e00079015400309400b0070204006984032401d0042c0100c003c6481380c3e40e400b12113210061803040507105504044000d200b8082c04100344d5030449001403000e8540c0d0000341541c0c40541540c105440103035546100201003403c11000303014550701c0203000c21540c070b403080420101c40140c400111032a034440003006010b0340c200040b2001c00001c08940308036940d036040015644a41004000c041c005102c900040150b106d4203a20b004c1d00040d1625440400c100c6507200c100d4003584d0a0080c0075338070b10010041c03501550700030214035070800303169801c221445080c0c0da04072886d80d103c02c0040c0d018100e4066060b1052080311701000001740f40810551501c3c00081c00080c0d2030201a104180c00a04058 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 615375269 1250 615374019 615374027
    0x10c0305130807060302180f09040b07050c2e0501030b061c080f070b0a05041a06060d1103010603061403030d0e07090c09050a060c05150a140c2208030d0c 68
    0x4080b0201280c1c0a19140c00d401000381d001071044900980d07900c41680a10700c0d28911000c1c0700c50014000d80c006580d10303103072803404060152940f420300c5400c000e558038420090000000c44001204080010581c2c2e4a88a1845a00340404040076142000510001d019040c0641d0401012500704144542072010401d50040c40140100408000625502014102806000d40324010307101d02c42a50b84801d4864243c0703c0441d801040c07202c42211564910402d4014250000d4000d8566400c0c0703180700d00c2e0760040347c000380f1441c005000d020004002d026814010640a0440035291204158111021a950340111050802090345503940b00d04031540400100004281000081c880c0e4031207010003404440013405000c1c0203904a51020072004e00402c20310080d15030150040910542d041c2d410122110050106a02580c42d1482c11880300b03001c0a009000d005c10002069680e62455046c8074112003c02003a41c4e5070268180401c02c071724002c000d50b5108502c03d070000c5600ea5901e50111 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 615376519 1250 615375269 615375307
    0xe070801090b0106030b031605130b040203040b040510020a14033105010c110c040e0f0a11040b040605010210020f1306020d0207050105040f0b0d06080a0503190806010c0305 76
    0x10116629040180d020300900b070000a040390034544040002a4110b01890744840300741c0c0c100a05011450303402c2000c1d003442d1030301900111a100000828520280018040c0da005031025a08070000205002c01d01c80140081c451607040c0f000704510b001701040020b8003420022500703030030703070b400200001e1008005607882085e00d401c0d081d016040300b0300207910b84080113080382081da8a58030301190031994502a2121074090641036000b8800301c00c02404000180c09001449410b600818444a191882c200b2000700180c0c450102d884843c0e43c41401e0008481601139101d00c11414030500300041e076000724001d052101403501c00350340c903083d81702072100700d1140d040f1a50541304081000240c2d55400301e000903014006a081e160400c3d03480e00110b5582c0218043e0004c2442401000c1004103464001041c24184401c8045800c0b40d55980007801c0040a06040c0c409402c000760750580c001014520300d044998a0506c10340c0e80c1890f50008040300718030900101030040c00281c0c0685c00102d03100d14 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 615377769 1250 615376519 615376529
    0xb0604270f0204230c1e0d090b16030b0306070c15060515040801050a0e0c0d02010c0602070804081005010b0f0313120932090601050706150f05061306030e07 69
    0x14410038515120032003149004100d510000c0e4582004609134602c10021143c02e0040b00c4054046ea842d45520406ca951144041d501c0b041d580300740240003d6500042c081c403a02203410003c031440d001801c0039090390442490b1724840d0b0019010081ca241e0010120148e07550451289030b119120140c80a00030062900a03c1d4414102c8a40602c2c0408550050041d146104021700080c1c80c1c01058009644001b02c6030307899900808055030311400c1c135814800342217005252003c00b40d150354680404a0f44420002d644010b8002424041c0da03508001101d40798000c808100807941c0740c100c41c94258010317602900300c480300000204903030741d0050100d1780d202a00800005c00c0c40d0080c0d500540351460b40e1050f52106500d0b102110306880340903100001c0c040d034038079040c98850703204420400d40040003040305061020900c482c40104101c0e10940030302c5801c0141180c500ca00305041e070312506895506c028841d03003040000c04100c03081c0c9080c05080321954100801c902c0b07250b9000501381081a008 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 615379019 1250 615377769 615377771
    0x30b060d050406020403111c03080a06031b0504060b0c0c0409060f14061c0308130c0e041109010918020d0303022214100203040b180d03020a0b0604270f0204 69
    0x42c0020311020f030b401041124422500726401c5600c8506000c0541000042d0328140c0c00307455000030109016003c1e0f80c0d40a480c200c80010b070f01c1d440745d9a00c84c42008048590f403807950746070710a100604207441114054808442010b0900144250607540c8a000c00c5038103009030703110048541001401d0300992f0450f10558401c1c800c0040519114074500422a035140c82a41c0054945011010468041c4609030709647c034502690f603500d09020f04154200011074035210740440c00035941e04800e5099001d580706122a4000c0c042038020000e0031941a080006503030700c0d00b0003560142084242c0c04800d44d50556219034601540d0070300354001c0c041c0715821a50301038032502d2402030f00200003050064800c481c440014030b031036071410b100c00c8440b900e1200c1c000d03038810003050200f000c000b00600604032001404140921001010922112450320114090391004443c00201b18041c0440d9500683c140c0d4208030007072410511102c91581081050048840e41e13107203400340000003014542c990b8001e04 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 615380269 1250 615379019 615379021
    0x2030102210a0515060405010e0604080a03020d0f02160510020c0a090917120f090f0d030c11011a010f0c0606030c05010f1407021c02150415140a030b060d05 69
    0x541c960441d0100c4596807810f2400000500c5498544221801180080c10007400d05081c60015504070b01d1500c004e550040c42400b00003000c0034204085030465219501614140c0402c80015004072030011004055400174008808225407240702c03c0300326481116071092582c2c01c218241e051022130450160040c101d820302181c208125004054030300e1041c0c5200c14030b480d0f08030f402e5019015a841045003050780b140842c4a001222000607003102c0c01c4401e40b400581c01d000c1151824101c40d003c0c001180d00c0303002c241131060700000b4076224185404000d001587d60766014407824242c3d00b40c0541403000440002038064030514000d8040c552142c4100041e60312810b20080401003031068a0000c0c00c4000c4102ca564442c0006103900c1e010740581c6410314107140c0c01c21480042402e0480c4552012001c4440580c3c2d8070841c041d424803c01d4403603541e5905080e880c3c5100c071006d44e601d1040c4001e101c4190401480701013102c041c2d11075480c1c0025030014520010301c06108826404d84083e080030 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 615381519 1250 615380269 615380317
    0xf0c01170a0e011a030d03020c0d080402121f0c110a17041e03060608071d0402060c010f0617150109050703020712030606030501050f06031302060c0a030e0f0d0c090902030102 77
    0x10900d40c08130320118202d898185078500f0031016445454902c250300d800a000382250a4012002542c12510081001041400e40c0101d181b902161011010381c40c0e802d4203004220368014841d02c00c10703140b41d290109101d8214108541d545d4181b84004001c1074403401075007013002c0303507030b040c1c902400f580035000085042c903200f00c09060b0b03000c0c002600e8071854860300140b11b0700000f0b000012550040d440c8820702812107401c0c41300c01c00040090381c0041c410400c00c4003002007031240c0011004c071940d00042d0300742040ca00307101d0034a407040000444d600c425010302101d02e0420f981c9044500c081c5010503280e44141085020780565903008092100d2075070b4194005800d03400400a44100756000c112070f070384e581e0800101b5054903d107290002d0040000c1110a035945401480312400500007500d032081c1350b06103518052038000700740c000a8a148440c506450003084060f420b2804179120055940c05031540340050b140307441030444842e9039079200030441d01d0a4069524440701410300ca10780c81044 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 615382769 1250 615381519 615381551
    0x108150d0b04140f060406020a02100c110f12070b130206070803041104060324060b030a0e01061a12070e10030b0102010f090c09110d0609020c0f0c01170a0e01 70
    0x10b4800b01c0d01112121400f2014120008061014000a000074645900c858907040029071016840c0c5046014030444580b140c4424064100684003554441d8080e0310002101400c1140708001040142c10907041d280403c41140147c410041e004042d402e040c0c1c032405444d00c3c1e8080303c040b00035007064010175640203000c4408080c40c82a809031000e01700d0039000504005c1203c1007030000500c0d010b00941101e954044c412800d4010030074500e000142c0f5515684079418075003088803280e4540d5100c2c0c0c0c00340003085c030a0103144018401c540041a0340440701c018400d15020b032149103001c615408000484461054005556422010b044172007102250000200078098402e071450140d803c04120000b6075000e44500107050b038100c0e00d00d031482400c2c140c07030b039000d071201300318108030100148500d01c10300560f0b20500c4002c0c10300d2440140c1da58200035541d42001840a091880c0750850907034401e01d80d800c0074a1160301d450454403d40c480d915078142500402603950840881d40c078100c5480b12140c40 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 615384019 1250 615382769 615382771
    0x10b160f12020601061103040303050309160b1801020a15051e04050604020a050f0907030f022a2a06070828180303090509060d021009050f0d020d020108150d0b 70
    0xc580e080c3c0300d0a03a213805040d80c012000c0401403c256004000401c04240710f23802030f41c0c1000d0440250b4000b070707401d180050041c001d15040905c00c1000000c603000c410491610090140c4420300252000c0400c03500c500c824a044814084a510b481d100014036007100c2d8128081130f1813503440140d409040c40c0c02d01e240d0364801103604034081c521500e4041198034114006081042000342a01c00c80d503a084005c030701034821146035a407280d40070701128441091060004019194030650144070700080821300b0b160078281464030040708800300040407000600c0124110604081d01d1650f91401c1c01e14001c01b00c2c0c420070490012041e0580c500d51711031100c1c00c1c103169150786a07581e01c1c0b50700c4201a100e215540e980e4400240414600c0b4010440d50a203d6078056104000a00403a060344640c4c0108401c00503448a41c1d0004240220030301040c9403500f2211050001501d01e50245801940482d2203201c04840281c140003001b80041c0220030094a10b1304207030006850510306c0c800d180f40031920110 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 615385269 1250 615384019 615384053
    0x41e03080d0504061d0c040e1207031d010e01120e0c061206090106020d020a02122b080903040308030a2a090302030f0a050a0f05100606050405042003010b160f 70
    0x81001407080e901c5e01d00c485011013010020300603183c002019000c1200801408490200314014411003900c801e1a490240c201d07036009845005440340c905e8201c035120603001440d103040c4005850310360364690740003c404100d4445098001010003410001c5031402030107800340c650000700016801754550444410318040c0c40240c030b0070304e042d98131a4016601c41c10340d0114940103030b100a071a640507184c81e03070310020101d40301820340c4c03e00092145d40ca03030801d0710b506240c140b1000769603955030703580c0d400b850095105a03031002860609003503550340d00403444090300744a1420740700c440c0c01508500e400340382d04001e41c09121501c180b44c148580078100151910080e031080c002c2d00716103001481c1c0820f01c41000c940c48400b400d07442e40c0176510001c140340a0070703041c2c40034414000115012203a9118202c090b120b9070f01d801d81c036117140000700010364140c04607500900b00000070600c43c0e078500d24152810f451370031007410703202c00442d0007030368000342ca01c6006010305100a40010600480b2056030046d44 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 615386519 1250 615385269 615385271
    0x7081c0905010b100e04110702061206190608070e03030c010e0708070e1303081308210610020607050901030207020904060c030e030a0806010c02010323070221041e03080d050406 78
    0x24954600b0007481e245044080342c017203400900001c52a1800b584000c4a051082d0510b9003840c0041c0c0105000743c0107484182c0401c5070b12024000103245c0222607810022507911300400341c03410001d00420300d0102811000034481c00000504641c0d41c1402582c3d610f81320440208680d059140d0300b142d9880640c03245421900803528045145401d448200348a58064250000005200d40e0700312008a0010200a2841d000241180014a4107401030031400c2e104642001640c0e07003129001d807500c00180c09584104160102a580d10ba0080f0b0b055610880f80d0a061782c48041c9100180c02034800e0b0740000f54000501c80410040007144d0f4010303c243c14a995003008be0043c8d00c0c000a60724400c03000c4e00c5010807074000000301150b115a40c0c2d81c060f07600c10303d80813030600662800000c80d54120b41c0c03034608001c014810020429070400c40c220580503e040400f0b4800407a0b801600c2d01d00c114050341000007650700740f00c1c112000a0801900441d0720190003991200050b40c418000d140a6400300d40302 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 615387769 1250 615386519 615386531
    0x11030a0c0e01030b1c03020102040f030f050d0516020d0507090603082a031e090604090912020712020f03153102060f0c0106050a0b13080a0507050607081c090501 71
    0x2548a80704840010001401c14216107580c2c0c001d17491040310403074080701150b408102c042100001400c05c42c0055200700060b03200110585004d0b410001c260003a102000410311200b08016120100120701c0e07a0181c602c1940100c003800c1a60405109400c0b5680c80c13802c0480c004100300c1d8a00003800902c00d43d03540300c082d00c0c0c44440c501040754040a180542c0b41c0c42413002700940c0c0c01015500f003207041c0c510341003031074031b5078260200c1c8064016a001c1c100059858280200748400c46030040301d030151a20181c00041e0400c0000d407440d20a41102130b000b408961211005505c007000030155840c4c07502d800880f00d1910101c41c21000032416401e0120b2501614151507451040000010056006220b142014400c83c5640d195803c000348842d0303d50b496170720015094903103000f01400f074100c1c100c600b547c40c01401d01d940001160f070b90010750135a01c1907039403030040b42010403280c06a40b030840b5100c0da154032a0a240c0d4980c00381c20b114504004070f0040b54040121240d000c210f8881c8980000d000e8 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 615389019 1250 615387769 615387797
    0x919023001030308010b030a09020a090b040b0f100f14030f0709060903050d050a0c06060b031f080c010315170321060109061b0f0606030501050108060c0d090611030a0c 74
    0x16035442844014040341346100144001c4981b84091980300c044081d001170440307860f4000840c00d100683c031404c00f4564400c08603449081501401608007001e0394a0452449400e0109982c18200c10003c410010f4050b410302410348904400c40099030640f0032580c5030308200e80c010318080825a100c402185100741c0000d0750354000d00300c600032a50800e001d81560030891000390740a5003d049421b0030007903c011b02d0000607003584149070103080d241c58055128901003604841304110705404e40ca40d03580e488030801c0310400001c1c121014803028a0701103081548504030303100d2142d0307580005c1c003420351304520b2030352180700040600340340d5107452514001030000c0c6c802280d5074842651a14006403500c1c4042c0700c0d4a00030402c000ea40705d04460007000700c55682c2c0380d036003a031901da600c1203542030703110300042003401000d000b180c2c0903018107009003640d03090454131402c1070310400d00c2d50a4486c0d201c003814014005aa0300481c0c084107a50380d00c65507890118103010040c80452581c0c80841c500c0ba6504c0c0c0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 615390269 1250 615389019 615389107
    0x2313090e060f07171302220b06040315240306090512070203061b0f1210150504090f0f1109130605060a08090c03030f0d060605090d02091902 62
    0x10107064261038040e540c0e036000258804844c00142009000c4c0ea190700107000686031030460481c0080c1d071151012495640d040c906050300c101d061182d220350020321050002c600180880303072402032882000500395030400961421003003040c0841c0030b000b0f902040041484426040401900d205800360b56040503440704034036890050b0308010350503902120005091540c0e42d28120600341c00c0181c0142031504001440140d980f060f800151005905414046284000c00410b4040c2600c148400f111815105006060f400b0380c0c070541c8482601c510f40c04c12044803079404804400c0c0e038982c062001c20200c1d40300208650010071194046c010810754480508668442c41e0f0645200030101460b0840c030010440d800b17035020b015001a8042c85140c422541d130704000400c420341c010b0544545660032082c0352400c070303a5164403403814020104403101c1c0584e02c4080ba1545168125480d903616100c0442c9003001d401240c01001c001d034400113105d0038070810000ba0308621149100c2180c480c40e50501303400 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 615391519 1250 615390269 615390271
    0x103020708040b070201020a06050a1517120f04080a0309060e0907091401023a030606050a050706140c03010f1d060105090d0b0c03011409072313090e060f 68
    0x20704444002e1006028403400032000300755403801441121242800e0b922504200c3e9401c0d180ca00703145944081e485040518160100010420300780400341d91400809055219545c00691142d4054000b54065500b1003c500303a501510384041203441d0700c500c4d4900036001d04454055000450080c0286180c18038100400b20311401c00359448201c42d600d850444900314001103200340c154041d51043c8041d00103240c4008070304616001c0d002c0000d5a900c00d4001c001e40b941441401090304142d010710400390400110340d944201391400680c2d61010741401c0300100000034154001c205840140035100f4200400755040e92600d964405003160ba411401d030654510032030b141001c54800000484541c0200b01030320703100f400900420680703c0f13207948401c200e030400c50300505008404030050242000072407089018101c01c1d0b5804526042100024000009640401c0c0e007820000c00040d80d21a80751041c1c400200400c0c68040031680c8901002e00a04500600d03c201c03881010001529080450401 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 615392769 1250 615391519 615391523
    0x406020706030f092001031103040f0b0606030f012106020a0806030c0d0203122d07031d060304061104080304030501020913050c0706091a0a1a0604180506030703171801030207 77
    0x17140d803481e94070801324000308400340c242d060540c1c0e04520030248800307000446c4640c1c414820320304251910f19140f04c40e080c005d400715000381424010403c10114080c0c0840c1501c403045100151904450282142c240382c1140c02002240085107490305160003007000e60048108a060741c070303204d401ca41803180c11450748034040e60650086150000408500c40100202465030441d24003810401c20000c24080b81d00101c5040c0306000294a424140d101440d04240c01182d030481640007003220000e6a01e0001403c09004150340d610398402030007604c02218002c110903000d40341c68556a080440c000e4218075403070340c02968109030302d60f59040750380300e407a115101c1b020400d405e00c001d6498a5000307142a003011101d10380140c00c07103000040034a00c0d0710310900307032000e012445d0071b040d8843d030304001603c400c12801400c040c40b06204122901490310f10504003040001030b0384e56500c0020385003405990001e0960415501a440300c980250002c182c0390303205140070340e240a2800e004608038801c030080 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 615394019 1250 615392769 615392783
    0x11040c0e0f060c030406080a050c040609050108090705031608060c031017010603060f0605120d0503160c0b090a031b15020f1b060a201912020406020706030f09 70
    0x100904a280500d81c28000700c0700a02194108030074a001e1070f2942c0c5c801e821807000300b0000d00410817502400d0164582c000702c02d81d211403c0c02e26010010303169200d1402220705003c403201c00694450360402c401b10082c07000600b110200765000d440c0c0c070002080c3e4003901403240104c1c000103841e42d02500480c0d00464107032403c400d041d40340a40140b0b5100140d220f40c141d654890398000040744060154010040d802078000031960315110401c051803c9084003260f45801c2075250b1054141c20205499209904010054000c4085042103d2404044c00002c3c6031284a4040c03114004c000074408084501c80c1c4c60b0201010191405003c20701c4400000902c1800021402500c560064001e00381e0400040c140358200b010641055412a41030108620594800703403c10101020714040c1d0100e420030345400c505801c0a5405038104e500c6180ca0070410403c0e0600341c0c2c041144602a5580d0800c2ca00c41c04544075500c9001c003e485455521500000030f01f0030108038078800051003000b03403880e80a01 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 615395269 1250 615394019 615394037
    0x100f0f0c0f0b10031b060e12060f130c0914060102070812280f0801050d020a03060911061602010201270b060f0a082103040506130206070804060c11040c 67
    0x1940742c0000500626045451205a0340000040e0a90141070f1103040d80800d011451420000c00805801110391030600c52010080341c5800e000c0e021031419044440310208640315503580d100c00c0c0720034088040c000d0900350701e2600001c28000d294020000d0012801407010709403a958012a941c465074002c44609401c6005840c6118000b0b400401480000b0f140c0301d11070b0503401f00355200900180e085440804c0310803501118440e4042090307405840101d8400401c0640c54001c503030075030f1250100810341592800c80f0420311039103501010104400508030b070740e0f4885448280c4401d00550104034095824110090300b085007001d03901603d80c10a5408e600028580d46a4060031900a41401d0700300040c0044030613151601d0518402800ca68001800c490010307508200a0241926a00111030b1007441407000140010030899003040301c048503a186003000e8000501c051203103400c02420740c1400640040c04540224a55420b140610102122001118244005d4649031f40e00c100008920079 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 615396519 1250 615395269 615395273
    0xa020408070b1317150a05011a07020f0423011211130905070803070c170d05030a020f070b010918020102030d0c053007230703030b100f0f0c0f 63
    0x2d024081e0719a4003011148001e9841545140c49180076086110ba50400c0c1844690304504042681d0046c40030101001113602d000303101c0c205012909003030300c0b644600003400d40c15980c0301c0c0007022405034014400c01c50f400942480440c41d42441800b808982140000010300ca10070301065030034960401041d03510480d5410030041c001e000c10702071f900419940d0302c417400481c4041102001a0646400550b90341049081000300e245283e48000c28100700503100401d00702020604482089040c1429610303078968407031b42d4000c0e00500303408600340c281c0070400d00c0a0203420f00803035040702c0b400b040800c113492030100392104a1505002c068050790082015003181c00b1241d0258045010034600141091042803c41c0100d540303944100c41c1c01c902144260b0005c8200c552a96040255130403c01d05041d189100c60f03d070381c50740c2c0070b800e5840000495000107241c0290442540218010591a00d1003000301001d030200240d046070340000703060441c050030201d0141e500340b072a4540120014081d01019 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 615397769 1250 615396519 615396539
    0x71106072a050f0123060d080c070801020705010209150307091e05031507080705031311060706090308040506010617010b09011803060e0c010f0813050f0706050702090a02040807 78
    0x880700820014407011044000c2002407200325070303084400001040d00010301703a183d10341201d852501201c940314001132001603511386000841840d84607004035152034404603e03604110310356004841c19400040e1141c1001070660040c541c0450440708044a242615445401c80c003045401c81d0110b514500c0a12104c81e03034900c0d03004904403112034008015120f60100341012820440003c0b003a0011007071001640e0000d210a6005d038007440c14500390b203005d0101c3c10304c80602200150031101d02c00342c0410a41c071030404591440387c0181051100802910380184542c0c41104c0684040c0030303010010a0240c4141e81071002805042030100c1a41d0a0112240c02648000e0b01281171084c00d0350704903004042003030702d00000e41c0109800140f1013140c425540c1016458800c1d0340c104410448004100380d000941e03a900302d4810b901798110ba002900e0700503d406003481c0100c0007442170300c1d0001502940200240312691017550350150701d0316088441ca06a0065002c0c10050360031200341070001c1c0d007035 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 615399019 1250 615397769 615397817
    0x6080601230c0102130f060201090201051c1b020a0312180206031f08070f15121503150608010b03030f030601051e03010f080d0804030f11120309010507110607 70
    0x201581061810302511081422680100ba0172403160224020410100d000710100c48002d2119000a0110b0041580024418443c088210382101c07403425020040c40740301e0703001400d4403408080b181031208041300065034070b60000d4000c80000d120700750305242e80d1440307008909150b06c0c88020696104100c0c0e08206103604010401084140341e613a12301c1c0d94004100c0001c0041c400d04003c5c02989050184280101900f030b0401312184108042d480c290950001c0b60741d8030b4000c10240040e0100c1d61000052250700c4a6102070840411200d58442403421580020115482c8200810801040d0420b05842e070003003c152102900342840000c405500540c005d09480d8031800c050701c600c4c40030308943c1034107030803e81080001d1401058103200c918000c0114500071686824002c03000d161640d002400b0800d0070a0303500400080c01ea040e0520801040180b00f040420080c03291646000c107040381c020300088803007600007440c40f0500c2111000109800780a84c800750b40d00d04074661180f17404880000 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 615400269 1250 615399019 615399077
    0xb01050a21020f07051b060403060902012d0207210b0612010e0a4202090405180706081608130515060109080c13051503060907090606080601 62
    0x1d045092584414218802886903a500c014510348610305820721a1a11890042055a002c10320748400000e540d004240c80444c1d41c003240115002210748012a800e256203035101030400c015204c001050011071103102d2440c00d042c3c0c00c0740e01482d43da0052a0f205d807140e44681840c4c1030843c0340003000c510a44580b950100f005804040f8441401c0b10342c03821038041400000e8982c1001c0c0d6401c0420010500049003010080740d8401c0c0403a008001c124038081d0308850303481e400440d09000400f40141c0e01a91484c03107000303004000e0b030b140c95418022002c051119030030550040d0341c404101c0c60b0080c6462400b6020811000266000c440d0303041d44c41c0440a440707043c0d0082d401400307100261042004030096151a50340e500581003107000900480b045800c600080d42104032540e0140c2c40348903507444080074403074000ca487d0b120003491030b41024002c01004d415005410401c0042c40002441e03d00700c1c1c1400d8010050b00c0e80d1048101c59414054030503600040d1140e1b410750003001e80c08403a0319080 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 615401519 1250 615400269 615400307
    0x20405060a17010614010503070e0909120705010b0f0409030804120203040f1509050114070b0c0c120c0c03070509040201050d062301030e0a08030c03090a0609140f010b01050a 77
    0x1c0c1d01c9a180c1c01210304050780d40ea88aa4440000b03001c1c0c40c44d10350345140b0524082c03c0c01c90171420700003800740440c80c103031610b1030056080000103241c084040040052100018071a43d60301d05440c1800d0380a019100380060140c1d501e4030032110b040c2480d02c0341104d000e800d50342e00c3c28141c590303a41c2d00c6081440c000d000d0045110a12000c5180c00c89400c1c200c00800301c01126152040c81103001070100c0b0220b0344903d06110102c84218045880d0034102d407012640146202056a110081440a07009071003914190b442850713000c1c0d440351843c1c80103080382c050031011035400303840c64420540d844200340200c54020030583c012800550041002d0010604150070210b582920382e0150108440d50f05a180c0c07421042000703140180d60180315400094a44e040035051020076519248a24031014007065500341c000400280404d20078010780300c1090f4072040074400c51a150914180c031100fa40b0301040c040c0140c0d441e11900840502c00d201e4030751030607160380d07040071202d40d8156001c116250a0020304 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 615402769 1250 615401519 615401539
    0x180b030d0e15041a030114010908031804060b0c032a030702040c021009030947040306050a0209090108010e1506040209090405060a1b0c12120c0908010e0304050d02040506 75
    0x50311030040e13016110301c1083e030349941c0350184e14440e6400c0d0019650600c41c410100b40700c03804002c011071f020b10942540c1c07444e50246001c0802d00501c955440f0f048a040d020440410300c0b0301c00700082207241c00e0081041120b89010701c02c081401c083c02da117000f0b240e20400c078002c010706254000300c0200e001401540d10402d8104880426542e00440440000700b16120500c802500f00d0443d55511002c0e005042004c55007040c2e105001c0741e0703580c503903c4c48001d03124000c401003600703800c079005036521901c10301c01c500304600036030043d402021099115100300310011600001c14825203000040314402020902145008010f24a01c0a0300d0250015020410a103039a15075020b002e0046200b24028960761501001c01012220340400c80c1c00c00070b02050742950b81c2a0303c11104c0c41e030346810a1706502a0310b84c468003035131304032000001001070506010401c40307500c0e040b0103010200c0c1c051a0092042407044011140c49114030f001c5d155111031000c01e61005400d29900183d4000000b60000c0c0e84 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 615404019 1250 615402769 615402779
    0x40b0403030e191220070e0106020a0f0209090c0a080609060c070201050306330c0105090a0b04141c03090203100e12031b071b09090210080a110301180b030d0e1504 72
    0x240840c01c00b01500c59030109104010007e90200c056004000c188050310382e46a16940703030620001d034080068465180c80c00440c41d4000140404180d581d0010f00d00c44085a440c100c454842c0400c4a210405000703182c0090b0746406000102c40781703581e05a45a0b450350380c400b41040380c92901c44d0200302c00307013650010500040204d244491036070400c10320a2a200e0440c6c41c02182520802040d001540d00700302c07100000502c0c80085180c00680c072803100804000f003002c003180703010b00c45602500e90305008280c01d80166095401180414001d0301502d401d204a40441070982e8031000030b104da20f0380304000221212655001544d007000b00c507259140c19006451080d00c2c5900302c00020346615803161004200340204e902c0ca40000e0003012014040e000f0982c00090352044040c55500602c440d440000b0613101c41c0b070340300401e960140d40c141174895031114104c031004040b10a440781403a10f08000c9020a180c00103100704035411a40d5144422060117050205100c001102903040784020b00020075 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 615405269 1250 615404019 615404057
    0x141305030102131404060b0a0c0515010e0106080f0f060607020103090f03020606181012020409020a060e010f080f0703020901090e01120b0f0f04080c070b03040b0403030e1912 77
    0xc1c0039603d1001ca01c070b0703d03092400e030302190309049104522662800340c040007640461f00565500c4d41c22401d04100c01c0f0139506046e414030014030315010344c01112000110b130315659000c0c400d050328481d5035800143d55a10070f100402c10b0302900c041400041440c005552881c2200051418610616000c079042d03000741c0da20a4064a600070440c0540c214004115a50a050022038803400702c0c12101c00050412408095011520340502524801c04070b6000b070554981c0c2d000f904025501402061506943e075200030031421742400c105000400b6010740c4103034a8483d51000c2c0c05880482410891501c0b00300c010307002540508a0b15051003403516002404e132500344000c03130003041807002500c80c0362800c0c03806034524480100508020704030403003480310313400c03078483c14039849036014490755074a10004402070300d0410907038091134917020000104002c004074180381900951003030b20103008000c4502546a00c03049080d81940040c21000b07200400700b6040307a024100d620550800505100038150402 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 615406519 1250 615405269 615405277
    0x302070c090c02120f0d050912090108151305041e05061501090e09010515010801060507020909031b100e011b081e0403020321070c14070b0c0d0f0f141305030102 71
    0x5c6141100466070b184042440d01903a603120038105c0162495110900c81085030307001e4600d160781046410400581001c881d500961001d030401004405800840404100580004c03039085404403078140140c545050200841c80ba41540240500000e40e2104003010910f14400f0750141048550000003c10344c049404481c0200d041702c00101d0240780c00d10010081c04102c5020070304105000004100c1190b001040d10310f001d40c105d1b1020a5a160f01c46103603d5070207a078000310101c511038400c91108131030000d98600f102c5180f0109000105054805500300d50381c15012000382c0d41e020909140702d62244034251751250210518124103400c4d15101d41540d481250200c0160303000107024139402038101c0340c039a03400406140b000428600100c0042412598a10080c8071070b1101c41081600c8905105250203082e0100c121074881800c542c0455450b1004240e8001103071072040d2030008603104040c5103404d141a6203031107041c2400d042c40d035443c07903010440643c1e000003030756400b00340350345c00380024 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 615407769 1250 615406519 615406537
    0x909020d0c0e071e08071803060f092a0b0d020c190506160219050106050907050405120a08030610030e070305010c03060902071104050c120405011b0302070c090c0212 73
    0x102898580b00002604e542600e48101e4441a4542151909180c0c42402980e0041003454014962100c058049011300c0d00354000818aa0404072002c903804203646c4100485801075030f0b8002e0b40c210008031041101301e403010b2140c2e035003150030042c00b1a1801600a0400c240100300044c58180000d00007420159410040c0890405c2c2862550034404204074094000e4075001d1060060307200c00d81d001e5641c800030085603030f503090340401350000c0c00000c0d0310401c01003401511801141c83e01c0706000f005540300c0c3c020113110f201150b00c00c074611040010b01052681e4800300441c5076440d444208800318003038034400810113450302d1800e09005400d00120004501c100004121135012000207416183c960f00070344000c078811b0051101044560f02480e00051050710001016203480e03400c840c403445144d810386011020007080c84200007056100d8141da40308100440103040c00310008505a206008020742000a024424070000350554413012196480d8011100203503c00070010708240c01c180780c8 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 615409019 1250 615407769 615407789
    0x70c050d0206040201031d0c22060b090a060c0f0201120b041a1c150207051207050c0103050c03010e060f01091d0907050d0c09110702041b021509070909020d0c 70
    0x5100440d6058007809000603580c5940c2c002e030307142c4116110307500d502c007594282c427440711100941301c42c0e0039002d400c50480801500a009080d1941d0000c915a40418440ba0040013407403400a03c6500c50f4809450340e517070001980e00004181d40046035112040c0903100e2245a0f43d05904e0216aa6480b40b90040d00305400358480d07501904040008458078840c1845900c40a1b61941e4000340000c03c00f06180301128030016104c00c26410401d24000c08aa842000d844000841e00203100300000c581c060004241da003800107070b94151a040180c0030a124400d6001103c0c000b054041c900501c026440300c4040c900450076031754030090030b5550085607560010001024007480000c80c02445400050001a0746005155889680b84c0710b141003148100d41010390756029600348801c00600301da0304580c00a0080c01407906084040135011102c00919000d4802c0110f04042c014910080c00c2c45928058040d06d070701854002448080c3c0702942c1c080360b000b80c4d0320b032003a8005102200c114010b8080100c1d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 615410269 1250 615409019 615409021
    0xc0603050103240b0901180b0406061b1a04080c0d050f071e021c021c0b060607060608030d020322031b150f05061003020331140c03120f0d05070c050d0206 68
    0x2481040394104072317900d80036500700ba006000c803680116240f0100e00541c2203080130700f910303405c00c80710b0152007e040300c6a4441903c00d01c030a002084000d02206202c880c10744040246003030041d14079101d210702015048006110100109080e980380b035a415081101e900450076030b59000800c00441c45807855500c0c262407014109604084400900750400d10f074140341c50300361a489a44513410000c050510400340041c80904000840e00004020030021040360f490794a0040020069041110b288103e21100320b070310342c4042030702403290041345c1d095143c402800500c000b080381c500200c20300036030f14050940d030030100c040054442c0d1710801200303100000e99420488200019443c201e0b0a81003090b0051040c407126440d51103403928642c0150519400244424080311054083c5c8078029203d028401004140c4803c04211100e101f102103060f20207142d0303440c003440020300500e05e140c910440c0600943d000d41c2095880103810907803a0a008450a190f45d64040c901504043c0b50001604400 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 615411519 1250 615410269 615410309
    0x1306050a0e0901050a050402070807170306011d0a05060c12030109060302121b041a06030406061e29040803360f010e041d0a0c0603050103240b0901 65
    0x2507121036805412540c072101c5514140003e01444441c0c001c86200c0c0c1e900281c1d420800c100b01c41141c060070b500000c0594001c1c080511208640c00071902140462040b0041c0008200f42c80c03130035609814000c10741c2d01c0d00c0307040c030007071040070b4101e80d0502d19680b181c001c840c4020851140514000c010f10032001c070340582144180f000480c410241c3c603000c0e03806602c0d01248281d400750000301741d68013030304e000400c146840d00d0804076440c00510a0b4200200009120910446801140030344800d0b00d46200313000d9803082070030441e0000f48141084400164110066200f068000d840f204461181807410552600d070702d02d00350303800381c10040e0074003110703000001c41650740003805400804d19200d01a00c1e81c4450300031902d07902102039024100003181d190001d8507a16588041c840454020b5841c410242c8480d6040c0e90749040c1c0403c0d00d0f100d4284400041c2e50b80700e8050241039a600c502c03250a00840305030b494410f0440f450004409a032034012407080c58480f54a10b034000e0410b070014400d280017031 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 615412769 1250 615411519 615411527
    0xc011a040e07150309020f0a14030106051215040f12050c01060e0c0403110121020403020306060603061807050f07030305181216060e01090602190201141501051306050a 74
    0x24040388210740000e10700b000580c1e2843c000548140745810040383c583e800c1d20020f000028558035050b84422080d001181454003c2080140e51030203500801800b61175504120741c0c0106030034529003560003100d0300415800c1000c40c541d04184203271602e500d180e00b550b58041d2804078140407280040c20116140400742024001e180040c4509510062181013040c40c0007a240304900014002100c1c1c0411001c00da4460300746201c282503166246d4482c06032001c10781d0301030b50062000741c2c03084c0300b418041015450002e08490150790b00800000844040d90b5922300700080061403503061003014405152a0b031103120040281a1081e600040d56117800d80c1c40c0100740d09a4404c400d200d40c060319040314549081c00c1120100100c0548000c00e0f060359242400103002100c00b403005550034400b01008001041e0050150f50100b44007600090142e80b030224200c0305422038003116810700c0804550726061030561404244018034003240303000c18081010f041d81015510040c0080c000003049185681d01c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 615414019 1250 615412769 615412781
    0xc0e01032f0315071b050705030f01060e0105040c090902070503030103140a02150318010608060103030306230105160602030916171005131217060d0f0609080c011a04 73
    0x502144001e8a04441000c295201d60802d0000080010503010030440c034041c00c40e8611860203141030505804940c60803d4480d080341c400d450081c401c00034100b001107010f00825080e00d040484912141c0c0c03a00e010007000d0005182d481c400e2000b41d00b00415031b01d030b09000030200d590052004680c2c0c1c0d459464184508155080d5101d20354005111100050b542e103025041903101c0065010345030384400101000c900188203070303480715610b0120000752201e00801c01c1340c1201d0107500c0c1040030baa9111400581c94201c0700031010a6020b00d03001401c00d44c0144c01402020421f90341100a441417556210100e07403041e101141194800c40e0315440d80e109089101014000c0b4688240345071038924001e41d81d50308024101d0f0000e584800002e00004c80320f80c898840c19411001a0340d2401504801804106e044070400701c0100006001074a2414160a801519540460210842540d030303211000100703d458422039007040300b004110031a9500b405500f0030100041110300810006404000032504 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 615415269 1250 615414019 615414083
    0x100204080d0e0a051207081519050901090f0602030a110f0405041d15150a140108070c050102040924030f0803040501062310031505010c0c0e0103 64
    0x401000280480c40001c0303181031120700681030900b4403201450010b20b02d000d90342c1156420012000c0701410040c00040c421045529140580d804220342c80c001f1000c11604495031801c040c506080b8107103068081c1e01140e80b06505400003c1e08465650f0b40003610b20072110240c03100f0780c000c070a101d4000d44034410300841e41e090414251030480700c2c4102200600561181d05d11517503030b50201e02c0750560030101408048012105a940c0f040341c1040e05580d950341628201d840710240d0180d00c41c2414000101c100366013000700001c0201940740e004407888800100381230100191040c606000480c240003030005400d41c1c00c00891100d0b40e440310220079941204111342e99400c2d00e01c080020400b20b08416803010f0b00184680d590b507403541409800341040c0d50100ca8400d100b80d070149114401805256030000046480700482d1a589404030103890940035401102050b081c0c04202c0f542c010580e5070490392203038024041603582d40507106c040c51801da0080c3c0d0b10001030b41114030703120741070140510002 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 615416519 1250 615415269 615415271
    0xf03020a03020112200403060b09040b220f0606030311060705310311010e04151a07081809070503072106050603100303110f060604050a0219020f0105090106140d0215070c03020310 79
    0x328090300c4cc0b8441040140a10076408a22050f560002c44e0301d203d021305403030b0072110300c00c0f0007451807804800a0810b4030054001036008000159111404650309000361460350760182080b46181d078070b6074020f80307a080d20000c204044194144280c80400c90400941c020f940b1420329004e0000054401170424501c240f00d20310f860035400d12266141030500c141e402c10030000c00700000240c0c24043c140f1940c600608208c6011130b0b0307411214010f41411100c0c80d070176100c45186488440007135555000076103071640825013940c480000d41c00000030709040040100000320708039942d031000c98910ba1003941c01031203514902000f802810f0700107a007410030b200b03410000c0020b2003d8152550310707101c028151510880d1030b0404100109a940c060300c50030403403015a403a40c602c5107980a590313490b240c100e01e901c650070034000800300c00041c8030b0482160f0682c001c078440304141d82c04205820745254012030344010040c140f448c0c035910003400703041001c0c4211043c17250b441c00c50040500d030490b0002c54180d81 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 615417769 1250 615416519 615416521
    0x1608090703080f030907030f0501090c2c060a0b0711151207050703032a03050609091e01020f1210080d1d0a0504240f03020a03020112200403060b09 65
    0x61a20340460340f01d82005490b650b1240c4510a6050420000f44d0025003020010100c18003032020641c045039505104000740d22003d9925800744070080340c0ca0b00780c1a400004164141451528044202c0d80302074002c005404050711640305aa060700070480a45541054483c001038a040c441c800059500c0e106100a0800300c130124070341440c5000030f00640c01c0203004a03044007014000d82244c041351480214042550030aaa580d076401c6041d800c10000017414400400c009040140b2a075000303481c0007018003241c1c801d41d0402e601c41c064001603c199598208041c1a0700c0048030080c01c00e04103241c41e425018123060030800300c0850036400200307040d0880002140516005011208010000044c804a60f541480041c0348582190701843e0000d0034034a089903203695103441c81c0b218070b61500000070310640b42d0140740114042c03808001c0d0842c0f03110320140301540c01400c800b02c0828116802050b1054001c0203001d03911440543c15110101c041000d104011107400f52200000050b0b40c13000407 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 615419019 1250 615417769 615417773
    0x1e01080615030117280308060d0b070507030e09070c12030510050108060f0a0b031909081b070909080403030f1b08091311030a1d0c130b091608090703 66
    0x11403106206004100445103140903d80d00103100710485c071200d11085421200038282c640546400c210030841c00261a20f00080c0c1600d04000401406504000315402d01d40c8e43d40001d9441c6d50103200141e050000040703016610342e0740c0180c10343c8241420340c1c0e29030305184079207448000c000c981c1c0003106c10f040c07d00f8100b000d84c00103440c501d01146d20902e480690381c0c544001180c035038104904480d070005080a000700392202c040d002940030303d44406a29000d11400a56403045503030742c0c0c900401c4094204509610201066510b181421301802aa06411740c4d410200045070200d46088505000109c0c082080c59040b04070340da440c003002c2c1130621605400d604a201c540c0000c0350000c000b0900492864080d0701c3e9041001300c4c01074042020051101496400e0781d007070304211740c181346d8a070034011103035501e003111560b03000c043c01903e000700718a02590f000c0055982d462124403a120b65154007608507a40e4921841d40982015118652071303400901c0014030003400106248020b074801441000 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 615420269 1250 615419019 615419059
    0x1003060b0d0b1303170901050f0604020c150a0b030d0320042103112b02010b09181009030309020901050108010501090b070c05040606090e0108150103060513021e010806 74
    0x540000c0b01c0040e03188228840c581a10001c05c505d62071050401c1d05820400c00000552003d40107065220350075005a0b200002c000c10b0340708100303801000c0d4002800c020800c0385503090702a0001ca0000d0049041c4d11140046403900701e031082c1d6040009d80301d801100f113102d10240718054152207801d4161919040100444840410030a0301001c60345402e004402d040c0305a5620204110100948200f5401d002c0c40110001c2455041903034040e9940d82a034440d40140f24507204020043d1181c5142d5840003084007102c1c00c0b0302c04040e9940551254105030f900c01d482210850b500c661070028110003640144640d00c00141c0040b410b200c46c01006001c01c1c0c0c0c1091001c022500c100d035180e5512403880c0342c40c0949101076480f0541041c105000440c00075080400041a150200f1080701070707a85e1054802d59480e031aa2420106240e0980184045406074200f640d0254a0300700b0b01e0820032843c1d0209450103050503400130401e452244454140d0f900c503010b96007001e012070b5840103817149030411314 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 615421519 1250 615420269 615420271
    0x504050a0e1503010e1f141614121e04051f02040305120c0f12030c0a021c05030604060905010e070c0f051006140303190311040302091003060b0d0b 65
    0x1030440303003101c0002e42c8403440c00e119840c8a0400340c001c1c44649000344980d603440018826000550300b803000504000c002da8460b404159103141d10985c0d29841d039034818070303c86c02001060010820041c0178901410501c000809143d42003e6004546d89064200d081c941903090402e0200342c04420203200100340000784006c400442d890071311000d4000025602c1c000d00c43c1c0d83c4004d005015494002101c1c061f118090007108071030340d0a8074001a912085203441c0d00d1071035890515010180041624004810080d00f44401d050040303609040c01000a003050202e65001180040e40001c00c100184c1094090304000f0041e4090600141d41000090345400c00018403440400c0703941c80195050180703001840c91000c0e0403c080d01c0c0707421160450040504094051484800d4155400102c03d00300042150180b1000251000210000d56021400b6000b0030113505800082030101201607500c40710f14500480d2101404100e4a00c0e6243ca041940c1c1061400c070b01c80c41989a03014080fa00740302543e = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 615422769 1250 615421519 615421529
    0x9091113210c030503071403070b0c030c0403060f05060a0807080a021504030b0708070e01081314100c2109030c1403390715030509030c01020f190504050a 68
    0x56a2003a0034203011844000034070000340030b03504440e40000a01c1008001000e0041c0110703101301d009850000c02696a1203903e20040c00110300700005882e840340400918ac000c141840002e1810f96a034940c002952203410010140c2d507a40c1080c8010761901c0b110072030023021524048c6c101c0d10b29029034240c4036110031901038001d42900340300481e003207650b8086501465200291801e5810f040070020140311084a54102142a01e4260320040d0b004148151103911400c11045241010b0b65810203000703003c40503207860388a60088148203080a0080d00041c0c1c04a503510000311040c02000000b55010b1860a1a014a004400c4000c81e50100007461015040301d401030002803244010340c99880b850039156000c018043c040203c00315071140c0a54180c90a0001d02c040c40940131040c0c1c2c48024500c14401030340342580c040342d000350107500000c0e4807100301020341e402d0180c0c44041d03d013a40e001c0c9501c1e580941001500306821000305129600a0100e8584181040d0501c0007040c071400160040c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 615424019 1250 615422769 615422789
    0xf01080c090f0f0402030702060106120b060706090f1403090108011e1e0e04060e0d0201050c03150301060807030515010e102d031b05060304050a0204050702150709091113 75
    0x1000101c1c0c5581c0f502c3e003c03811018100b19520701d40000000e488038820300840000400e62048000035200d907000c1e940402d0001402c2c0380c540045942c0e071000805070305800301c6100c400d03480074001061003080000510350321301001e5a0b48044100004012180517085a19007540300d0500d01041d007280740e5110191156a0503143d294081d250408a41009680c0003c402401000400042096581052440150300380482c0c840910140040e0300340d40c011110002c040f031007400001d4140079841031405011b04040c0000a2845e1520a6107003032540d903410680781c1764001e0040402a120303811166005140300a442201418a0740100480d502607218181c02501720141203009001030302c0c0c1d68240c000d09100d501400c01d56901d04191100060300e02950514880c0d00001038505000003124401c030392002c0984110b510940c200070003000050078150462140390820100d6140900501e07008806986403105034078600070b0040e00b610480403071b541c00b03540305211151082a487c0e898105039258120 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 615425269 1250 615424019 615424039
    0x20601080a0803040c150504091109010c030338030d021b0907200c03070f030f06150503060403030f0b0f01120e032506140906040303230a0b0f01080c09 67
    0x5260300e1a81c0c035a0802110b00e95556aa00c2e600c07174011f0b00038030843d16104024400f0400d80003240c42c59000e042c050a01042e481c040050000c3e1003a4002c290b1101400130082c00c110802c02400072403010010740c400d0a44090500e2416841d0800060120781454030082c2317981b0b0003840391641003044401446001c1d800210110b083c0c54040c500c4542c14205404030b00e20441040d0340d446d50340300c040c51945030107030080360f902113010b408030318000098941220a624001c4407030f81d170700030050400c1080b10103243c0c2c14440200d101c4c1d4040c03220134081e9020780d8001c00c0b00d8240c240f04808846c030300340e40180300748084580d07550a640c20000703162600701c521100242c0f03140710030803944c1180305044404007401450748240303a40d1200440e804200758010841080704d516012074105049005456100244e885000007400007442500062451a0500101d000c103903200461540070500c240c03021320449845260300c3c070f510b04000c52100c0c003000c0246051000c2d41000c4488003158030920001a01941c1c03504 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 615426519 1250 615425269 615425273
    0xc090b01170f07110601080c0114070f1b0b120c0307030e070611070b040602070b1c050a09020f0114030a0e0c060a080702070f06020d0509130f0b0f01020601080a080304 74
    0x400c0030106107a02440e000c5103071074192408031050300111000d001140f030b018107403642040300040442c1603481e01002009100700b064015034107600400c2d60548002c2080015a00051104030350810381c0384981c41c1500c028081d081821050350030380d000001c01c420248805c0c0307203000d0b08100381504114000445c555070b8440b00c030700714058017040d402002c4500c14003000041d42e40c0d000c01d9428070181403c0c01c2c0c5007110b0b240c1a116180e4400c0744100d03801640080803d101c10800380c4010181550795603401104d84405d400c1c0030307054076422030791410003942c2e5501070030942c1098080d20680300710034640600100d050690814172404094010521165581d90500f46250100103500d4241c1c070043c0003d07150051b400d0000d105880c101c5404006015100d40024840c00b43c0e0218010b942094002d48451850b02c1d800f154aa0082000b043d400156465a080c03445d03902d10501d40c6000d41e0400101e07948840c90140100d0740154501541150700c40001003022001c0464600140c0f54044801035a9403035034 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 615427769 1250 615426519 615426527
    0xb13080102031605032d0a0b010e03060601030c09181b020a02090a0515030a0809030c1c03050f0403020409060b04060b04080a12030b0a120b01241202192007030c090b01 74
    0x803107051102007640d07040c0013440018512241d115543c82d00341400048000c800454490ac010200260541d01000c0840c08035030094120244160712494030300440c0303540e40c41d0696041200003004a0700c503501e80789802400c032250001414507807507000400324900c07564080384c80304400402d0400031503500d40116000024043c510802d4800040444100402e503041c04240340e401066a91311a2107040f605c00d5031800d01c00401210302402940025000c1c5484d1010340705540030020710031511004103c00320059549104603210b9a0141c0310015000b888101407104880580d080b840600600744401c104510001a1000b4000d174040c04e00041d1808c0d084054020b0885110705640c4030014043c00b01d0380000026004498a00450801c480380c3d0340c45000c1c4020300c0d82041c200ba500c0c5403044445070b00601031050b102d00072407111001071030000f10f92030402d0200c2c80c10700b9100004150300c81e2041e42000c21460020310145103009001e2291035584ca01000410b6032140703904858640040b04544da020b = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 615429019 1250 615427769 615427801
    0x90b0915011e05090310180609111518040209030a110406030b0117010501210f02030f030309031c0209010c021306081204081c0905060d060b040b1308010203160503 72
    0xd000c028640d4800c1511018115401110449020388500c501150201c0e505006600d120f2451fa0741c1480501c8803071322000080c0191000c2540c2c0711140c1040000d0070340380e40d006500e050150301b800c503444070b81c00c0c4125103841c0d24401c503461181d80140098451950080b40c844034041c0c0c401e0400c41841c3e50600401c0c003411455001810000001c000018104040c04c0400301580e41c820003001a17a072034030081c054003944043d4080f40d07602e45c10400000210b00040c80c2198034002422120a00f02c00503015140da882220518025040400c0c0c1e517a80c16035046201c00a14009002942020802c00c0002e05135044500007910030f0804c40070818201a95134840c1e0090440c5c0703410303502c1e010a10075110065a010344107011051044481c440580c81034460354640a80003561241c1c4064078040400149401a80ca64035900b99580c0000a030147d031480180010301041300c00ca900e588180440c010440003581c032122099004004000c0c1d609040311401d42d404509041170342e12511102040c50110701 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 615430269 1250 615429019 615429047
    0x1c030e1c0f090519180c0e0906010201020c0a060f1401030f230304091413020a030201230705010614030a0506070f0c050d02070314031806071a0c03010906090b091501 73
    0x8600c50418488914400750420380b105d00410480240b1a000c07480106c4071110f4202c400a0061204c4030300743e04d000040c4a812000c148005820184800203480c1040b01c803403021505135076150800402c441c214000c4c0030b28403000d6050780c4007662640d121149201034a4000a000e468284859204001d0341404186488403903000c0340c3d11a0388490100c0000d110046035406108050170001d184040080810000c1035409801e02100e00e103543d0054036071070941d10301a040440260805c45844200d54042c00d8100d01642c0045402031030400c4551030f00d0035104410b40070b60000050bc202003040040c500341c2012440c50104c0d1148a140b2040b1401d075002c3d000100a8002c800c050b0132255030004d601d00580e401942c42e000d0101000c8002d5540784540070320891241c1100c07280745a949030000150038064001c000e0410f0303a445c186020641c4000c102d420380d10802d00440103100d000f81d14464540a0010442c3c100141d00744280020090f0000501da400e145580380107290445e40f0501820740710306 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 615431519 1250 615430269 615430279
    0x80306060c1908030403020c0409080703081515030415050405250504020a180504060501021906090501020a0503041a060d0f030c0b010609080c030102130308070609051c030e1c0f0905 80
    0x7000c00d103040003c0b03078410b880640061086605404142c41c25200d503446440c1e000c0b004600c0e141450350305a50700f0a0003032103880340503419404a80c1945a1a01e114911241500e000380d1341d1400d40b03441c0051107020f0040c42e1002c0c4c90901040005640084c168058030710210465000c00f9408108555240007504035941080c008544030050640082041006d100c0344200d1260f5140c8480601c8201c820070304c40d00303006901c20703031200404002040804e04214000d4902042c00380c110340307405003a42d10003003134840080c0b000010041800301c40d8240310665031250b102c241d22400c0100000f5007841a00001400300c5210030080d00406000d000c1c461690b9500c0300c1074941035a501c2030040c10440ca00c0c07007030450902070b076050a2101d00c0c040c421150b048100d49640c592183c2035131524582ca422540d800c0b00c1d03143c2c0c1d0300107080200d4400c000301580e00701900306d5002230300c05000004040d91505000725060381c0c016108526400e20141c950800000705140158182401803421690b403503090340125000 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 615432769 1250 615431519 615431563
    0x9010b031902130602010b0d0c260a0305030105090709080a120509040903090f0b030c0f1b03030114120105090a02090a230612120d0b0d060f0501090f09080306060c 72
    0x40c4490303d0640849800341c000b005224420400d02411316080d0314020002407000c1c03004d0222400040707000314040342c0c0054221081078800500340c40c0528841c0c064000c80e374080300401a80c5012428143e0244581c5455000340e8a400705480d62003400b210010044424043d603500b1507481842592003101c4010070902980160b0304015180c07021078012900098603a50000c41e0b041d44032004c9174040c1c00304401c054609404411346801c0c0b0b0f040000c0241c0c8207101180c20310b140d40c80400c0614064400b040c42504450005020402c0c0020302201c0c1100d1a41450308118140f01e001c110b442070b260301610b000490350b0300c0750081d40062401600503d00c0c0d04d0b105615212014030040b501e4450303e0b040d078601640f0806801e24503a03c00c10240c045104034020441018a200c10360461349504401070701030a06041c25944282c1a9204200006102c41d079400040001c19010b0284074112240007004002a0303040361175183e000d203c0200590b000740400149072090079802c10006131804202c520500c44 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 615434019 1250 615432769 615432787
    0x5160b1206011b1a09030711190e040303050f0714121801060801020403060513050738030702010605061602011b0204020a050d0605041401030303090311060712140609010b031902 78
    0x11300c0b0504803220b500c4941c0900015042c0d100001100c40903600003682d500c121940b84204010150301c0000b003038042c020003c0010ba201d805016441c0194441d0310041864900340003402c02e20840113003a58208140c4414403019092620700b101c4d280f40790f05070789a1103592100e05035103c40520758130940c2c00358a014000900380030198040c00a50b4440c01080c085902c4820100141c1c0c00c04400c05084c40c0c220180c03c000c09800d1000030b000c0c56070320304419240782a5104480a0000c14800f00d004001e200004100040d9828070400000c0c200440703005007880022140b041c905641004004e05214060580a21000d0031090505440c0d5005105540e504849003006129400c1070080c25402030601001040500e0940202c00b03002c50b008480000c607030b1070368a0813005030060040940602440141b26052500207001941c42446261100c94115464007501800c0740e0070f1046006550345140c00740085a6030b00100903044520351600356449880344d41d5091012103464803003481c4e40c1e100050a07a6 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 615435269 1250 615434019 615434033
    0xa090f12030e09040209070c110d0f03080601110318030109060f02040303140c0a03030c180b1e0f0d090203070801020d09120309020d0323070f05160b1206011b 70
    0x2822038800d50707074111090509010300c8105601650300943c0152540c0006045500c58007201c8d00840c09500d000a0321001c03070012a0308001a00300070340d550b03d1a0070000040c5904000e0143d04440e0a18045808800200e02c19480740a83c00701881c003600602d150b001245d809400c0316801581146080044c0c074119074401009500070301c02100031544600601200c0c90851013582d2032500302c48041c01000816030f4040380204449142007060100c1440040121581d05403400701030701300013001075954405101c44000c140e241c0421328120007405c024070710038109800107883c04c021030400041003c6910b440000d0814090b5005859558030108500d0226119034000047c2c140c0145682561355215141c1141070312070782080690400d0081441d00d000a114070700b50103107131400210412345d1560303018081e105c0e50300101055a041164850190030f0040038403030b14081c0120014409001031900d101c00109014103280740005020030380004500b64015650540441c1e40c103000c0490000301d40c60304030 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 615436519 1250 615435269 615435299
    0xc030623160f1403070e06040b0a02010e01110c070512030c0610060f0806060913020c0703210e091f0905190f0b01170a060314150906060112020a090f 66
    0x18001894001da00b64068000c4074500420461000321501d907659414055a0030b000311403249030800401c01c00015080c060354041d210101c9150b00106420400c1e80d2001d0948400c0d001c1a2240c10301004140075152000441004962050701c602d0000c0070801400c130300750b0289203c1c0d00c481c0d01401c010481c1c00300e00c423440c0100340d81c03a50300d400c01001c7ca10102141c4601c0220340068001d01e08000c0d048240c54042c0c5a40444030590402520346400a8a0141003002650080310305801c41e034407421003401441081844100b141c034088400e6802d00c00015a00380002c0d0402c040307c4118045501b0131270b070b034108440180914030b805000e41d040c80f00402d04070204d18129241114035040716178400e04a1800b83e0040e0440c1651802460216043c5070204454042c2001c8681507172144000b00060350004e00190300c150a0000d0503c08a075400b001e0b00c4100020000012504180b042002e00d0707820030b00354464075855503030040c0c44280300e410555049081e80c0140707644110300c00c000100d14401c44044 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 615437769 1250 615436519 615436561
    0x207030302150f0c031b04062006060d0b0a140414150c040501030b031c03020702090705090108040f0f0c030516050303040f1202060f0706060f050d0c030623 69
    0xd6150880c2d1542c00c90725140b098920300c0e01c03c00c103400400c0d00504080003854001800c00805841130780501554070030f5a00c2580102c0100b1241074620594217445030703110100090315005492103260400c0068405100c07098000c1007900307001e01265060155a000703803c0c621502c40001c4440c141400c0c185154910284001c40520407000a0081a82500315a500990710503582b86e041c903080c01e00540283c10403642e41901031040c3d1808000c0b040181004900300c0165440043c0ea03031a10780180489264001c083c8810f21400b000b44600341c0c1d80c00803d403070f4400d03004011030f40465003074540a040c4030350380c41d80940710800940e008410300002090001c6402039124140c0030300c030b03a200241916805030348516070540c5810842000300621892403154440c0c070052010f460034030000b8a214264100c0e60007611403690780c034018041005250001006480c04481034100c00e00f02e5a070302e65070504103000040046440b1010b20080000390056514041c0c03000030b007004103181407444502e14064030210 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 615439019 1250 615437769 615437773
    0xb030a0b040e031305090a0e01111809010f050103180f0b0f01090605060910090b0408010605010e041e150b0c0312010e010e22060c0c021003060b07060e0f0304060207030302 76
    0x10b0142c444002040320b04440d01c03400c04180b01490481000701c22880100078840701a181c03901c0a58000c420303c10010b200f0400408140c68040040d03582c1d0b6082500d0040e103028160400c01440380c10340b400f5401044cc2c0c0240790100c0c0f20482d1021000107200c080d04028056010001004104503450070f95920500c9001d24000650303981d5018230781551881e100c0c203500150200072080b9942840710281d10704500b030742881c42500c0e0741c940c404180c551241c2d00c1581c45954900e4103105560303008449068190007124144140410310034101100403003000d02c002c00302d58840501c0007442074941504000c0008940480d00c030009001c00586a900c44400038044810302000070500304008940309050301d00c010007940b07440c0d03aa020140800c000d10311503aa403020700c00d0a00320000da118000c40f481c0304036581c0c413184c8006491041c4003800344100c000710f040c10308068042c4a00c100c0c0c03a050b14182a04101c0101d005401c00c241c16041011000540c4d50b83c1c0400100829500e800180200c200d81c82982 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 615440269 1250 615439019 615439031
    0xf0a030531030b0f100612020c073809010807030b15030c0909180a1e05070b07051905101e0504080c1b06161515181401120c0b030a0b04 60
    0xe40301740c1e0211900840004c51840711211103900344581c080c0103280c40303001c1213460f55038403140e441c8020308522410141c10656811110030203040648860002403540711058200b9800320006482188010107074820103507242c4041c0361537503800e04075240744101100780130396900384000e40b098240e001c0c0c8103160044000402040180a41c0d00400b006002048040c1006100d15540e01014561f00c2c100e407030700c9449035440d140102e00280300c02c10050502c030f51101c0e51020107182c07860030080e103201c80410044401840502044001c544145140c007000f40029440c0444400c0322959561000914122403802e4100700412406000401c106804041200d816030502501c0030300c0901001d10503500704500b400100134540d011040207446a1041000701c0c012080c120203c41212088080400c400080c0241088401c9144154003450780c803044043c40b4034015800c04110942040c407800052210032050300041c06064a40e22000e03101c080e022070b950341090f0310300b2000707400d502d0944c0d885149044 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 615441519 1250 615440269 615440281
    0x315070f1b0c0506091801080309010909051303030c2a2f15220608330a05120c03010b060301140f01020c03070303030e0f0a030531030b0f 61
    0x54000004140d00500c41e0411030b0602c4180001d940000c044990000c210940311060706c5c5844800c2c5000e4440c450096454240160004111040507030040010600e40024480d41840d40003103068155014240400c100d040c00104841390750400c004c00b2580f07110710300180c1895129a180036079441c041e14041400b4028041c17410b82c0345580340c50190641a070480701030341c42d0420402109000600c0c075051424460030340604000310400761014000400900c105000040d0060f49281d04040c0c050038907650940000c850301a403101d003940d001d407005440c0740307407034400d9440240070409000f000d004020f152481d0b06405a40f4848420010302c42d50078204542c4940c2800703003c0e42d04840042c0d41c02581c100410082c05403442412100c1411402102c885101c903460404c40440214440daa00144000d0780b5070600381001042c440c50145034021024580100340e1040558010750346460b881e2030004c0d4081000d82421518440c0414001e4880c0000410b006c20190820302c030300602002c0380200e950b1a = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 615442769 1250 615441519 615441557
    0x606010e030f0106031a1602060103140a240e0304301e03030e06040201140304030903200a05040e1e0a0c0e0f07140d110408073c0e060315070f 63
    0x450450340180e000074010000313301c0d509010183c81100c0401c5e00c0103c645500c0b12000300402044c0401da428180000b80040c1c0242e1040481c502d41d000080d60138030b803d0035090064498064100400010070506100290000000c0280d4142c4d0001b5500a9046104507250040d02c421200390007081c6072000c00001e840700481c40501c1254160b50f06e1340c0003031494800555540003d00141c080000c0f174440800080c60320b0b20042c016030361011041c0040903115003001502102900494011424034242c0011502c1c00652010200d014090998904040c202d8051401d5030504019103402030903d0300155a20441a0050007003581600402c0c41d50b580420a580c0d21310031544415080404104100703400c1d5160b4000c001e402c0802c099149000e5484c45841d103800341a810455a5902c0105265030414541c4200150855110f000b15110455607244006d449820321401c40c116152900003003180d5014401180700c1240084040316905140304010880207501000e81d010408000d0040c2801200d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 615444019 1250 615442769 615442801
    0x7030804150b0603012607180f060f0e073c0203070b0c030a18060509060105150d0b01050706180b0603010603081803011104030317060604080606010e030f0106031a 72
    0xb0142109103180d1030324904900400b0003910001441c020003050071554801030041a000308182c40c0348503050f200c01d070004012200c5c800c10010100b07103071020030444045000c105504540c200d580807080c1e6500c1110540f40e0304c4d50004a004901c07a18000304c1e110004009000722480c800010500c0c04134200320050340d4030b1040400260403c06044000f130b02c0c40b80c02c0c80081d0b80c800115080410011130200100303201b00f40d40c0070110348030f0ba2944d042000e0003808102c102d0040c03800b2240100345120381d42e060101846071260401c5603949501c1403c0c1c0590003107044a05055010034104851905600c0304400c0c00110001201c06411030b6001c9415403605018070402d0741d801000070303441e14044101c89058108000f410035095500c50900d04445108000036100850103070302c0384510201034012201961070000c180c140316003c1800180000c8000007801540401c0a00f000c000b40c4840800081c50b040b03080c40c0580c11036003040d01c00310812049400f1000054919036440304d40f031320bc4100f403016a503d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 615445269 1250 615444019 615444041
    0xe0111040602250b2b0501150503070201150b07050705010521040507080d020718140601051e04060309020102012a08180114060117070212071401020703080415 70
    0x200207000040b400c1d02e1120b801c8a20860542e00704025655406010f005170011513164a880c0b07807022100241803554a0612208140780c402004658142200c49018041806444003001402b00026841600035030251301d81c103a4240d2440d03e1030303070745003031001455000d803200f20f0f054001e511000130254041c00c1500c3c02c4106603035103000e850013108021040900010010303030300c42c420b8050008030804207004c01030306148075501a0284c20b0a00c80310080b0761240008480c3c116280101140b81004608132554103e0400d1030034940c0d0b0400c503480d94401c007030a8030701d220703015038001000a03030940c05520181c0030b18402e8009100c80780c02e01044c4030107600765501d6480b11170041c442151000e841080002d91214012010a580e100d401c0d00f4942141c6040b02e503070441d48546800c0c81030968004450741d0028051070b5600c0c2c0360b894084402521801e0701250104500b0020410304200407054499180106100c002152030305194100200b181c4001d6400b501c402070301e1405459a04558000c100c0480 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 615446519 1250 615445269 615445273
    0x71a0c100504020906040b060712050406020607020705090f130c140a0f080303040f080c010507021b040509072702120a0e030c030306090709120c1502030c0703080a050910030e0111040602 82
    0x10f5176120503c07001c1c045401100b9130040d000c0280d070000480481c048000d1807503e60301e1940b42c5040100280c6003540160944065500c685020400c0d40e4171a42c17442d40c4001410386058940d01d49440c0100060001e036030041408a0f507086c0460800c0b0307084c1d6100300450b42140c10090a659503140409038000e103002d410300b25041000005c0100d00c580c40d02140051041408600d00110b2840080c2110b030147da40724010b820030b13411004840e000c2c0350140200c28003120100545e0030481004c55407900e4511a5080c00b441c002c2c2c0c40103840304200710f208500203a0b00400e41d0380c1c2d00218184242c10000b01c0700036084600d80f1260f04101e50f40002130302c00c120000d500552854503400100302d031180d4014542c40400007410801f244214001403070168451260307a400301c3c06030400030390761009071060700d04004540c4103002d000d1342c050300040c07140c04990b00000c2ca0307940c54241c00400c6400e0300c00e902084e90003411062450740680d078550300001c406d41c0300e00001c0140ea140c00e60312301050301c42c0d845030f0001a = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 615447769 1250 615446519 615446521
    0x10510060c05072d090509061b190504080106031a1f03060b1c031d0f0d081612050a0e0a030206070b1e0c18040c0818071a0c1005040209 60
    0x8091243d0050f01c80c03c0410540c10307450901150b51001000307903017107040003548500501001c03000070410079400000840891049411a44c0001040d02440560510b289911402030703250a01800403100070300111380c0240a2952282010001c0602c1801e5024100640100044080c4401103491201c840c0c1048070000480ca991245805090281d480d980d22110389205106010a040c48074040684291610300c05202501540140c85440081d045c0c000c4020005d40e030700301c1e500c2c0e241411090340c1c080000d0b52106181540840e0303441d44040c0080c100222401c82802594012000d0504000c0c10303500c0e0f0140c03180140602c04074804074840250402814070281c00024030024141d640041d02411803810950741880041c54154103403058000701c03600103642841c074200d00302904403080d01500c0a00490910310401840588014800e1002e45468490410006400e0041500410750306821100804250300c802c40641d01207a00a601071103512a150000941030080c1403080f07400801d0028a = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 615449019 1250 615447769 615447779
    0x6030106050a02030d020a090602060a110405040f020d020a090e010f0e130302010e1b041416200708070f0e0709170708070311040501060c170711060705010510060c0507 74
    0x7054010300c6101007540030a02580340c1011451000d041a208640c0d01c807180d440c074020001e0f0a045000e403129407024142000f9030052032241e4225001c4030010349002541c8040324603854000d01540110f0f0542034000038180f404954000f441d80c0c00e03100c2204100c4400d980e61071038000014658412500d0140101000400b0a88040348880e0101e000e8000400c1c00c00e000c0070254240211059091003030300c600880849582000d10803100302131110b01100105041c956038402000c404509040104016106100d4030034a0100702144951019811100d1064840d92056150350b00c90140c02a401d81840b000070f4400541d105803401150582c413810710700b90138801c03541941c07008507520b088940302d400390000340d180b810010400103501400c10450450b054008000c191041170b4456010440d07024107000101d1240c41c403c102503464007500561380d81945c42c21140c8a030064494662051011580303009120041d08064441d03c940c4403007050b45500c0d440240e81030004060044c080b40d1262400707100c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 615450269 1250 615449019 615449027
    0x5100c06180f060e07090905030403080919031103120304110f01031b020604050d0206010e1311090403020105040507050916031a0409050a05010b0604060c0f17130608060d0206030106 80
    0x98400429803090040744035501c40e034560040e9000210b407001c1d41c0d4002c500308400f0510038000613141c907490901c0615425150103a803405140005000d940b000a5000c44540e210a0340b002082c03a04c2d6480300380c4980e00d0802000c0b0302c1658903828000d00846400300b03403010b030703c0c011039210b5a4880c040c084208004000c2c032800b0307a01e122170141030564440d4406005c440d1041d4130454086941c0c01404503180070300d0320904124491520382c040d03500103001031001865281550b83c0c80080310b4a449203103903590401c4200c03030303064049440e0405043c0e402e000a0642c10f40201c1c0c410f9004d0411a08602d50310001e002c0c030254211043c00c540014a600e6550b01c40c8650845c401000003040310f0000c95507424009011aa1841e40448055019030500f02c1004003c0c003a03c1034002040350b03181d04180c900032000d41440d0342030100030000b241f8410000100403240a4400514110742c107916211846070b4110400e0a041d0700070f600c041042e48001030490714040d900314280d150b0103440c05003140d00c1e1102c195 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 615451519 1250 615450269 615450281
    0xe0138130203062b0c0e0417030723210403080a090f0210090302030f0111040312020a060c051c021806250506040627080d140109051005100c06 63
    0x144c0d0102d4a00c09002c610009445115602c505601c82c0f44c40744038103460044400103995212400d00c000d104108000700342d03008100d250303910031408180d40d00e41e9075040840d4481070802100d00c0f09015a0f00e28099884120094041c00c5080513640f400003244d0301151030b01d0501200c00030300158452001405050140e00310b100c00c148a41c1c0038000020090303000074107001504a00c400058503010b800c00c00e42c60104901040340200c00001c00c5640103103216a8030500c41c07030202406030140140404480b900c00c000115841e5000032013008031299030301c00140154802070840c09051104404801c5155441c42200d040352016410903142c03504030000d1000306d400c65100940301400c402c0c0e500001980c0d2464401c01a40704402404440c500303403908600b280c550030041c18a60144000003055640120703001180c11f0b400048103900d8a1280d00360001a11704846421110f5400d0400018052102c0e0809402040c5850f244050355440300c00b449598002c00030750500095404100300d000c03c03810b034040 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 615452769 1250 615451519 615451531
    0x5120a02060d0f0207052b020a030e060708280302040e0a05060d02221a03030702120f101d060c180406031e02040c0e011d040e0138130203 61
    0x4500c01965059400880e008034505565513000038448a51441c040100002c050001e450f032055001c7e6400d4009503100c002c2c4000a05101048040da0101e503281380503205459405030606503034a00071800c940d11003941c42c03090220010114100c2004074000e0080e6070035514075541710345942e60380c0145280035140291040d80c2150754091400090388401140c00e01c600102801404c68a07480d1002c1d4040f640e04d135a60420f04040e42c420050f1650740401100c0615404a952460b005590850305040c0300741c030420841140301b5a681e150182c00d1603002542c0000c0c174103110303e10300000340e061140c41381c2080702e40001c110420400b81490100642c40507542c640c0107040040e4003926a66a20340890481e400b0038101d0007201d04030011854035019a04003202e81349080d80c010044240007030b00f0b503080035003039030a282600e103400c09181d1181d5002c00703404c801040c000e012480301a03001290580c8124980c0708a40080e805280d107103401c5012800c1d0084018100b0140c4100d0312102c0e0009420203001c07 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 615454019 1250 615452769 615452771
    0x11b09080c1c0807231c110106091a0312030601050f0d06090f050f10061d0315160207060e0d0b070e220c08270f030408060f0105120a02060d 62
    0xc4074011904120140942522502c5c07040d103840d08803601003441c032584502204c090362040d410038461106109005240c0e603001d04040c4001e829092005014010b2500000301061070018400d150100b1030003404034401e0140d081c2c91141e00d00a0340c01c10b99100450f003483c04a00d01304200e4074804c006100801d00402d000f080040c80c1500c812440b01658400f240c0c5c540c0580e1188240301003c034001010540100106210806241c030788600071745800440150840010801c2524411548090011108805c801d00b44071007181382105000100215400d2180010b206040010900901030b209800302c84000030700080c1002e65650310710813009001460281080a8080c54003a20303150b00301c01307214603081d000d0360310780c11154a0900011581c60b0440442000304100505c2012112003440d90a1000744e411440003517001c20042c50310f000302c2d1440003541440009000110b40c4004600f40c2c1c000c6158201e1707480e142c1d903524108805c0c0d001344c01080312242c1007101e9110052410380001d10401150005c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 615455269 1250 615454019 615454069
    0xf0d030207180207171e21010306020c06070906090e04170a0e0108060604050d020d0623010303200d080711070e040203011d0307030302090d080c011b09080c 69
    0x4100d0544102c40b00311040360f0042003402c200112009003194441c0d940b032106013441c228a64040030003020b00070300c21403120000b50312084c1c208003a20f840b5000404074921411540d59240c404000d41c0031810401c0a40518008100301ca0300c20380d031704030481d003295a40c28902030038000501c0007044e010b0703c111403003242109a102c82d1010400948043c905545440b005500801c0c00500f050302c00808041c840c5504000504c01603031241248200e054040d80e500503401e14500c0c00354000c1c0441036160504148110780e1385103201d454034040741030724170079a2105d410000503480461998990b46805038103400c4580c0a0103103d20640529511505a160088c0c510441481407820305090783c001940100d0b04074104425814240900310408000408181d65440000c00c03083d01c07401011001000c0503000900c015140e6039224041075803c0e0440d21042d40da07100c5240140c001c010380004010740b0640c2401301ea510a00170400341c4216240c40d00079041a200000800c0006c691856644a201103665 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 615456519 1250 615455269 615455279
    0xa06030c060e040c0203040b1b0f0303130606080114130302010b0a080706030b0303071101080a062301020607080408041205070801150515090a122f040b0f0f0d030207 73
    0x20390880d00601450311441500780c2450248810b503021041007000390341c8104400c00c080403425080b0b4101d80c000e5140341282d040c1d210383d0181403280c0d030b00310b2034034506c000310030320854012449403000a1441450100400d44d07450611a0990f82130032412808103103804000740781140c84c03d00041c20b0074864400020804420300014a140555130000c40b100c0e4032886052058541503c01d41c011403204034001c3d41003410503070354401d12404c41c0d0f9680b41008010004160044101d400c820041c2542400362082e200c0c01c90801c000f54580300c086c1e20b00510070714020503e068081d00c0014055608644c60a141030f00303014413610040c590460407034040c49880300011f02d054080c031940c444045582c0040070154035050800c0808404081008142f44080011400507519040a00200e507500019803540d422141403c4802d9150104846400700b80003c00700941d54600b1074001b4030b070204540401039400c035881801544c207050700d040c64102800302200341d885d10b400c007290902c0318441d10484a42689030 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 615457769 1250 615456519 615456533
    0x60f090409020a06030c1b1128080a0b010e07120203060607020909030702040b0117070f110a051005011d04020909010e07060f3903050f072303040f09050a0603 70
    0xf940c8080000783ea1403503c2e10140340d00074114144030080b40580071001845072111421900002c80051203405007200120700c074164403607400010b00344507140d81561f036070714448541c40e02c1d0001d000300c03000d50120001280000d4580c01c0c03107000d000581e03a00600c05482c600700b40000d610151415a00c0103003480f4001c01a80c968498500c20120407000e90b40f50000c0384180303c1035943d100c0e00c440c180b0101174101c00044840c202c0142d0b1280301c0d8540304001c5006040c0943d010140b1408903501802232958100500000041c0d0f4540155000c03410080e9a9a58000c03942c4040f8a510444003c1c0710000443d01520308070910f10340042002000150944100707581c546042c02d544c0c00304010540340400c00040310380002c54005084008106007a2540c0760403800610852800d4680951880c1c58940b90107140c860000d07141c4e0805912303181551041c0a08040703120050070400c0303200c246c825400100403403402006480c1116054500506e031340f410301e01c1c082c0c098040200318041d802c0d55404000003251750 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 615459019 1250 615457769 615457789
    0x30e0f060711030106120803130222090b0a06080d1103040b0301031406070206061804050f1f0f060302010c0b07120c050702010e0a2607090f0506030d0e060f09040902 73
    0x100d6003078a250b500c1e25105060030b54100b548a541c000920303e45040100744680201c0c0d80c03180700740c9000000125240f000a0131625050900d0a440304e4550b21034606281130380c007904c51103025203075001d02071383c070340d100c20003901d802d17001c0e80301103801040300f180d0300c203005020030b6004000305c10503282026128481000349130800d910944010b9141c410011240a0a2040c41e803c980c06101900507850701d00c000c80c421401e0051400401148080014288501480284448101002a03841468981c40b080c64011000001e00006500c0c10414003403507446481050210395040c0c480300b04c24a141e8880f1010002d00030450814059030034811030503161203102c0c0141e0240248c03141c070344a080760f000050140c0740e0041c401d401060007041c10701c00e020104c2c8a080c20700700c07000c0c104e4001c0240b00040324100314441e8400e00c400303030034441d581010403001e400c12481840141d08035032400c03010000c00c60f2201e40c1191401d4011208100d1580c202020900900c1001c0f00a080860460010760108d00c124036 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 615460269 1250 615459019 615459023
    0x5040b130e070e0a08060c1c0b0409150e03030405100b0d0507081f0b03060103080d020918070f020a030905101713020901051801140a03020d0c03260304030e0f0607 72
    0x880c01c3c0c3d64100900e0442e10b030070080d2598030000c0c8000e107803034001c05655104204200c1c80301451b421700711102c0629600310300580d0034080c10900006078140b514115643c42418680708a606201d80d00d41003c400200341c034801c1390058014982180080d03001c1c3c000b080d148a801d07410113450921600482c804010700002402003d00801c0495500c070f03004043c01080c40b07154101d81d8102031505250303a41c001a150b0560360003000041c0d40341c0407012100c000f0311405105039088a145103450700201c18150b42c04e4400e00240d204e2785174480d4104001c81e11103400100060100b07164100c2071083d824070b00c10503528ad4405092848188401d1070842c503909204071510700c0e1510320f0910070760031802c01c4201d0500511060f18550f0080301c4810480c514901c05024102442250324001b440a94a4401071402907802074842a440401400d0440303031600305002c15600581a03040350f10794842e21003140e0400c40c0c080e814135800c1d91181d40d401c1b41e4039090141143d43c009040300800200e50789060040500714 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 615461519 1250 615460269 615460277
    0x14030309190f112701180209030307060e07090203040b090c011409130912120c081302280807061803020d02090a09060204030f03110105010605040b130e07 68
    0xc9403281425290000a092500c40410442154030001c1c101a03241c0c840254002030068141c080e440108a020341690250380c2243d81c03806450005444003050702d4141e440500302d083c140c0854481c01c0c02070b8441d403d241d541552007041a04040744443d805100c680410b001034034040b580e04c40c00c010a0360010303101501c07004100e0043c460b091508200d1301e90005820700704101c244201b85044041409a560180d000e0000c4005a070b14260156025501c155400150003180900b2400004c01c03403401e0785502c800140c5400f00b050702d0f0702e0007991603500c900080a02900071090b0780c1d00784080405124142c49a00280c0904211800045070030440078101e9080100000ea240140081003810510140006403030314031000c2c00561200201e0040e501e0301a2004011900c0e2540d07214010541802d02610352840410f0201c00c10112280c3d9440f41d0b800780d924628410303c03c0d0809800c980080c45140046107003004108002c42070100030342001c40221110300b81081c0e464a680e010a4021100300f4009 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 615462769 1250 615461519 615461521
    0x2409080d050f070206070f0201060807060201140c0304080304030c060207060f05060f1225150309060e030c07140102010212010314070b0f1e091003060302031c02030910020a140303 79
    0x900041e1091030360200c90012221003504140c01e02a480300300150110041141c00d40907134042900035004007004041d2182168a03013542c504000b1b008001e099800d964070b10300107001c00c0c0c103500e1200580e070003641c002044501e19225640c0036030f01d85e200c49004070b541c0c5400b0f020340b00100c1e0440c481c80c44468101c100210b0b80c0d00c0c0c15420450840c0d0304a0940748a0403000d804003031101800216200d0009800ca101821668151803112000d4200e0b48101846001c100701114616450b80180d07070018440c01090083c1030f072010f90942c50380a0502ca00c40d443d40b000404015200c0d0070420031080180c10700005103000683c1a000031059000d030400d990092082010706c000060401c06103008100402250341001d00d10032514445200b040130550000c181d550504001c80c00c110111010488000d181103520a188480038015044611082e40704e03002d51440e8500000700341201304040c2459a02461400c007448040102942440201d00114464800010000703074640c0502d803170f0003c0640040d501d03 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 615464019 1250 615462769 615462787
    0x604020109050409051c090e040528020f210a081e0a0f0f050d050f04020f030d050403060f0b040203010b1c090201080403082a04030506090307080403240908 69
    0xe2407154402030203940b03845101408500003061800c00036000c80305c00c007003c01004108440366446034010341c0b20380c01f0200511041040028401071840b00d08440520142c181950340c005481105102a4200b580048070300b0141c9440c2d5a82004406503550080110204904640c031380024408202d4441d82c000403603201500315048407210080750780140518108080900401e051000c841820500551805856011340540c0645442c440c00540c02c1245250075020082031001c02e480c160b000360a00400c940780c5080104a4403440c0b0358940711a8a001e10b55a1114024075034541c110001c01d0303a5a40442841d030300e50004500130400c0020032500c500013883d0742c16140c407000c241401d907a131a20020741c0060b604020f64035400307509400c104815684020807101207625201e00244000202c1c20918410407000014205507801101200c40c00d94580f07080c150749204981015002e104240030410005031507207980d00011190110184240c0c1c0d200c031011065070a81c1c00100e070103e10102e120b0034 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 615465269 1250 615464019 615464027
    0xc12091404020f09091302040c0306030209100e1902040906060203040e09030903070e090109060606051c0b09010918050102161e0f03030e1e03030a05010e0709060507110d0506040201 80
    0x80103081214210710b005a10f554440642c03007200d065a008940010004640f81092202c65810f50b8002c0c10901505000305070080040c01c0c540400c81c0300301205408180599400984a400e0703504003035000003151100b00925034100a440d8110000700d40030000403132414658018000100502c0c0c00440d10385080009051940c0b40003071020b00d45a1040c441ca550a0b58000340100441d855005005400d40f03802e011903024184000000d0300443c10b0100011f2801e500000502c40d0140d03200c004040d12580d200048191181501c2035948820034600610540c8100d07403000202c0c110800c1b15403982c4200347d50b030500360703041204810310034035260011400f4000d03102c841451221907008d016070001a580c4c5e6180007502d03119030150425546005803410b003c4204010302420810207640c00d41d40400c000c0c035076580e03401155030b00803c9050000018400d10038941250042501e41c07240d202045c107050089900303030010321090b244080c02c6580c1007c1d98032040c0c1d62101c1035001e1405440c85181500002d8 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 615466519 1250 615465269 615465299
    0xd0506040b010c05030403060f060e2e060c080310030b0906100909081c02040506041e0e0412050a0909090609030f18030b09030f0316080c040f150c1209 67
    0x505000c16080c0c0383c80004e502104880c00e17a9401603000440800c0115000010011508a500720035000c00c00c0c4101e04051001d2040341c00c0b04143c40d21076200c0714800703100c0144001e20880000c1400030b0150400101d26801031079011040380341d45070b040c42d92602c5240c1048425212100b840e0800e200303012804001d046650050081e480040c013500c522665000b9941c840c402e40c409910390204603a00e0244590f4040790010400200442d4940341c442050080012484030071102c48207143c0d60000b044e49480d00320620542c0c003c008150000030f510300035581c0d40d0083c12070004102866102140170840c512508450364003600c4001260300042ca400380800344040c40c51010b1101803030300c890b15501c4280c408030039a58860380355206900d401291600d9400781d028409100740000c020441c502c1c0302c4c030445c24100c0081d503450b202d007a110903c0c803291500c07850080494512020b54203020401d0002084c0c860300300c80740713400351880120b1b0b21030010240e42c912900d070000e05d40300030030000c0d1f0031a00481 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 615467625 1106 615466519 615466541
    0x924060b0f1209070614071e030807030e07050a1505070803010b0702130207080d090203150c0d0b0a050609040b221407082a0f0d050604 60
    0xa81d610341081e00201a46a2500002a41c2601c0000c0e05001c944568546811215107800502125448440182c80c52a0400b2065005150007103111460794041d070f441d0200c60904840080a031001c40c200201e56a1140800b4401a5a203d02032400c0741c856050702004038104c0a411707501d0380035441010380895008800021040d46030f800810565208a48100c40b540050280348124002ca00300a0803032030b0113010400c81c8103a507500020506000070121160540d000f100d180c0383d140e0485403011008404950044402c81500400700b5440b4122228503c09040c80081022383c01081e24440c0b00f16243d45080c2055120700c05074000d11403098030f0700c880d1240e4a20f07015004e0322221038441070341c1d050385000989440c07080744554000c0304c0518151104018480340780a280405095000c80404200005048400b40b04001e10701c054941c180483c8905d0034000300b02c1143d42014903 = true := by decide +kernel

theorem cover : BRFrame.Cov 615287769 615467625 := by
  have h0 := BRFrame.cov_init 615287769
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615287769 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615287769 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615287769 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615287769 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615287769 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615287769 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615287769 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615287769 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615287769 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615287769 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615287769 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615287769 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615287769 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615287769 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615287769 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615287769 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615287769 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615287769 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615287769 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615287769 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615287769 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615287769 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615287769 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615287769 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615287769 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615287769 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615287769 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615287769 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615287769 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615287769 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615287769 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615287769 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615287769 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615287769 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615287769 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615287769 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615287769 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615287769 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615287769 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615287769 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615287769 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615287769 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615287769 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615287769 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615287769 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615287769 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615287769 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615287769 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615287769 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615287769 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615287769 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615287769 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615287769 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615287769 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615287769 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615287769 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615287769 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615287769 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615287769 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615287769 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615287769 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615287769 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615287769 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615287769 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615287769 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615287769 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615287769 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615287769 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615287769 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615287769 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615287769 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615287769 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615287769 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615287769 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615287769 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615287769 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615287769 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615287769 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615287769 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615287769 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615287769 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615287769 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615287769 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615287769 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615287769 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615287769 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615287769 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615287769 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615287769 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615287769 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615287769 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615287769 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615287769 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615287769 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615287769 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615287769 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615287769 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615287769 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615287769 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615287769 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615287769 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615287769 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615287769 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615287769 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615287769 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615287769 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615287769 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615287769 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615287769 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615287769 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615287769 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615287769 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615287769 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615287769 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615287769 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615287769 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615287769 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615287769 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615287769 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615287769 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615287769 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615287769 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615287769 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615287769 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615287769 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615287769 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615287769 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615287769 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615287769 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615287769 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615287769 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615287769 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615287769 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615287769 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615287769 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615287769 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615287769 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615287769 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615287769 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615287769 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615287769 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615287769 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615287769 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615287769 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 615287769 ≤ n) (h2 : n < 615467625) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
