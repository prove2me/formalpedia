-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0519
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:13:08.793489+00:00
-- url     : https://prove2.me/submissions/9e9812dd-754b-4c28-8750-8158d40dd354

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 93165468 ≤ n < 93345324 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 93166718 1250 93165468 93165481
    0xe09071a2b0b010e0a0e0c03071106010f031406090604021009030c03080301030501061a070206070201170a0c080a0b06070b070c080c0d020607030b01080609061c0305030a0e0703051f0b04050f 84
    0x42190008140c1215080d0000b4144406e042d188032000d0300150003440c011000c41d1005016002911254028804582c030541e51480c141d103520b54644802d0f11904008501c0c06507070350011500e107200c0e130081e40040403280c60fa42d00b03100c105a140020310081040c48a00440007920080c6a940154042c41c4100c1d141e5040d4200345007100da072540128107100d6038845c08002c81c003464058441c0c040d011030300d00e9210b0302280010f0741c4070342812641a01c1000090304011a07400c540e8001104003441c1d075101c10240d070b1080d141004841d007492031035610080a000d04000106101000c4d64010440d190601503006036603210f00d883e4005003450341c4250010000c14103150381c100300003940103109150520201107403070300280601e070002d42481d0140030210000743c0141c03600502c0f000d0319244c414505600c06864140104030350400e803417805950342400d008015000e000608013054079000005400c3c4c040c680700103500b030014424161003185403030340c030065000d0b5100e102d014130403880d90b2060403151402c0c0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 93167968 1250 93166718 93166727
    0x4081e07060804230a0819080708010605090405040602090a12060e03030103020f10030b100e040e07060503160c020406060305010905062e0203070c030c0e09071a2b0b01 74
    0x6410220800c004081048049524200b86050741300d000c16580d43c541380040007043c28803603160005008414000343e8a0780c60118007800188104240e030740d120058852003c21101d06c4020721030480000e80c18030039162140b0301a80140c0d0003a01c41d440052401e4100408140b0808443e0b01071214440001c21480c00c1c48206d001d1803240c056240c01841c550b606540c0040d040401d5507034170501404c00c512010700c4040c000e42c804e200b850760040002c40c0700780e1b03020360042582c03e440046500450030041e951256031030008103203003a038038240c035524115518200780400022420440303030104200d080701b00c4003585844c418080070304240d903800318141d0f040009031026214003406503400b40c05004580a1f400107540f00d40010340888003442006003800703040c200d2540c0180c0d0b81c00b0700382c110348000000400904032901e9049400401c1500410790343d000346281c9030300b6a88102c1884003c0152500003c0c80c1c0c0b60700520002c21031110311610107400307100d1b280882c0844240185443d544038161412980c11 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 93169218 1250 93167968 93167983
    0xe03091f0206070f02011401180b0906090f1308070b0a050705191b021c0b010b0a0e0405070c060c1808120702060307030603050d0c1b150809010204081e 67
    0x4034440c50005900403500030b5940750001c0540040040c104a81c504040c07007908903031814041042c0903030580d61504a4440040c411904c9008058580204407089061204034580309079002040068642d83e40c821a25a180c00100020064905003078868000b401000280c82100c0c00f51400e40700500c0c200fa80b402c201c400140000d0240102440000e09100d500d820ba80d404c01c80d140350000204030742460310250941e20080096201403403030301a284407005251450900f50007022103244590ba0303801d03640d41a202d01d07588040003485040450825080542140f500904d00345840d80160506403142e0080fa0744e4a10000009003410303441d0f00c14002e6840d0024050100d4002a0111038000100440d99105100009018100100005d41418000e0348014015904081aa9410b20449000400e80d00303100da07003240d48450381c00740c1442001c400b0114078191240c2c200e01c801070000b003402c01e6455110040c540faa039076400b0040428101020701030590104030842030320341c8541104507580e040440 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 93170468 1250 93169218 93169249
    0x1a030405011404050a020d05030d020c030d06050406181e02070b060f090c070b0c0f0c06010305010609050103020604050d020415080d0908061513180308070e0301050417090f03010e0309 81
    0x2102c14000480c0000c1000c2500a43c101c401e0320405c2c82d240781a078158016502104121803001c10020a08540070000b02980741c001c200c10840c2c070307440e14100811035199021b1840e15108003003101e01901c169600c0302c01514501d6224990203544d245451099a02c4900300301c42c1424040d0506c0003906103140c0802c04c1c045c0803610040549849401948280688580900b5000b5400007081c03180e03603108101c80d501854030f0b100b0b50340c030380780400c010340d0710002031004864561130858001020700d014070910b8140c03940209003900c1c16103070004101c0c100c41e800005aa03c80d6440485190441504140c1002000d01e01c000c0d01d103003c03510340058584007495200c00d82c25008503003042318409004040a0031000304442d200030604a42644034014000c03900b0343c0744802902c0c005641810b8100080901c00c911301d0340e03240c03081c4150800341426207900b81c5000340014180f02400e40c00c46003090140151400240610009040c6c2000081c02d66015480d1a149500f00051102c480e08000b80c0c084119103 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 93171718 1250 93170468 93170501
    0xa0204090b120d0318050709050103051236180105180c0702040e070e0c040510020a110105030a0b15180319020105030c19110f0a0507030f08041a03040501 68
    0x2101d540c2c0240c80700e550b002d10a04059440855070808885003950304101c0e42c22400315428030303481e030a044005047c2800300303403000e03c84c00010308140300d16501158106840f844c0c1c0c2598403a0329007200e62a0080217000380b00c40050005021085444030f00c20088000c001c443c3c04000c0354035241c1840009581e041c1c071040182045010402c9028a0100300d5010507030649001600c41521111141006565000b6900c10490f601c00d00507000a948090400d9038002c07200d01607600035000080e030f625410544000e02d03003142ca9002214560188003c0e50b40044041030114040362442d002820040300f04086a41c04840801c2c0b07665031244d4031407115080300e404d4009100311000e081a55074040302c0131800030304100e000400103103041d42e10800d4911041c503404c041c90348804500d2000d00401d07140140e0310458460881c891550a20000e44051031a42000150a5450030358690744a003600c2a101520000300070000003070465141c41507810080001c003810f60702c0e41041d00c0c00321700395101d6404054042 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 93172968 1250 93171718 93171739
    0x311060718060f1b080f16020109150f030e03090303040b0c0606060f1b190501240f0605090a08030a050a080112020108070c0501141005040e0316030c110301050a0204090b 75
    0x9513081181c0f0042d015100151641482c00340c544410944a40700110102e0340000c2101003c4451320036010b03298a1003602d40c6c01610f07440380051400958007100300f000280404428000c7c03c9d0090f40480825181d00050340d180028020100f89182d002c0d40c4242141c040002e020303219100f089c08416000b82048444602d050380c03210181007540104c4051003000000000c0e8040420010451910140c140340400040000780e4213041c1e0091040324000300540d60b601e02460003808404d56043c003640d003694200c3c01c0681c14808212400d410a2090359009035130402c0210b030001080002c0c00c19034869995480e9900b085001c0101628010303844013203901d02018442e00141c0e00b01000a9020340da03413420f0440e105083c00d0083c090041c440600b00f0b10002030061001c0c0a005c11140ca0559000342c409120404180c0f0f034241d40c03031103021356803582c5000301c02c91800060310410000d04018043c624100c1c95090000000c0d0840d2001e46441401c107600040400c036602107401200d0580c00201c6030790406 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 93174218 1250 93172968 93172997
    0xa0b0c0f06070f1809051005030c010311030106030b031617071d0c0307031b030e16030f0807020102070803040e0411060307090b09120609030a020105090a030516031106071806 77
    0x8068100741c3c043c0a1042c90124000c459140001401c02489032240074420f034206a5024840c100070790161038068090420f0803000f40d40207005400540c001102018070b103a10b0172408400514546c1010713641801400075040341102883e0340c0b03002901c590400d0084000742031000e03520340002603000c0c5050110005004400808074210319074440c90036410360380d40341d81da404210010045000702102c0e03c441c3e02441080e50344c3c942d0204001c0c1051a040720441c1c40041c1c4c160a484107144002090541d807850340d4000188044040c020302481801200e120380d0f26490607174295000741d0025010144074508010500011240300c2d10382c500c2c162090392035400d040d44003c0c11540c26000b0107850321000600101c1c1a21144070400e42c580c6442d09072059402c00d000540e40b41d600c410450b00040d800d010214402d44404942c0c60070f91580350700c0700fa180410a28a4100030300b0300d00c00503414010727540c0d0030600442c000d210305031081c2119a105c2070081c40c0e1b05c0b5004a48003442d0031800400c985034800010 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 93175468 1250 93174218 93174227
    0xa0803030109020a0507060e070801060611030708071b03050105070215040b06010c1704030b040c0504060b04060f0203120115170912090f030a0305070b010e040f02060a0e0a0b0c0f0607 81
    0x56542c00c0901594411080c00155910711461800401c1c0310714001d01d0903144403020940c203098404501c000e019165aa241c200c0309051001d04c61250782d0020084c400010301000010504184508041e0701c0e80340306c0d1501658400c020b03030310944d22a510751041100d45a41070042060381c1800c0780c4480c1c1035003030545480c0d40c4014010030550500842c03c000d2410b001e2490754041e00181c901d10b20540c5c0b40d44a103441122030304183c1d801c507400d9161500111742403400c0c2c0a003d081e91032498085041500e0010119a0050309180480c2503000401c4440e050030351403c1d50034041c0040200710103d19001080080c110180e030711404800143e00f42c2804081c54010540d0144054983d5080d61600a00800500e003080b80c030809035458410325480004060308030024100484c040c10700e801c02607076604420300002d24115070081480110244102c018640714010b0507071164545028000e8807541e40c00b2503403207081600440c042607804550304410500401000000180f684003030101c1d8101008041d1 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 93176718 1250 93175468 93175471
    0x602061b0a0f020c030106180f020406141303050109030c03021b010e0d030201020c060f1f080c040207080d0509011d070e07030c14040603020d0506010c02010e091810050601030501050a080303 84
    0x1040102c4018030b188a2007044000c0302c540000340200142940c0d00483c40c46200300b0400d5045032801c10443d0301d40d90302c091007542c0840d126500d031804030b5454140c0310b207c1644880034030301406212442c04800300d4800d01c0744101d42c51003521506401001d1b810040d10740328140c501a100408540344c0308400c0e9030300981305000b01100742c500303030405401362909a0281c0550b4030001c450307226050070000580c2e4015003460240320500311f58401d0070142d044140b101011405100340030382c0304005006031400c2ca50b00804065008803940c1c0c0c24410902c402d0030540b0400d032b03090941c40e91280c852000a469500a40003e0500d8400401c5101c0c54140b83c440c060307000400e20014555511172031400c20b07002d80f960010304495440b1a60b51551039402c058025008505000101c610b010005680365000c1d9603200c06c034940585424602c01c06074401c020884100400f0100300d02c2c0c0d202815070050004000703a404414800d032010a0354a4040001012070300c050340480d105880d50b060800110f50040304a0307 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 93177968 1250 93176718 93176737
    0xe07180b0a0308030604020d0e0a02120f03040b030403050403200f060705072d0308070308070516060e1f1d060f04060b0f090103050a0c0605090102030a0e0409020402040f0602061b 79
    0x20307880e40e41740340004000340030710310f1a10f80850030302000100307004020a09108641c409c40d0240c44d42910300b00038070780d20310240b102e10005500c104000d011514844002e1640184240b800c240352a031a950342d405134428002c0300041140c0500c401c9107092801c0d05814003d10416150103050120319110b07107541d2017082c07068410354000c01c5d40b940407100700602081241e03000540040110740e0b8901d07100141c0d41c06860181c0009118001180d9207511038401c41302110034841c60a01c103588140c55503001005000c141004d58403850207941d03054a4a9490008000040440040e4404100d010401d0210803158204c5064120908000ba0623043d044c465800c1500840c002507004503000100d803035500f04e2100182e101e03001c01c0c000000c000c000181c0d8600180f1420350718102c166107403000e60716405041d0072240541c005000260071540302c1d000440d50003000600209810301e003500400c049a0068024280144401409101aa804124032030704065500c2051211444d02e5100300418007602160 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 93179218 1250 93177968 93177983
    0x312070b0a02041a041403010501030b0403050a02160902040f0e060a0e1305030301140102150708070c030203120709030b07021f02030a021b010e0f030324030a060e07180b0a03 77
    0x4551685042c2e8180c07005030a44800e100d03007550002c90400b40c01d8005101d4101070310142403810b101400c048c01154103c07940214109580e855550b4160b40d50382001060104512800c1c041e215102005606c00b0000e10018900503a41c50500b0100c240017500c6c0e41042c0110062101031000c0e40d215030101d502103407503440c0031030440c3d01c0b006050003052403040e402801612001c00042080301100a48208440d003d8085038148804c2070300007803014004480360f0001c6580900064450307800391240710084d40c800d1066900d881d042c541400c50300c81040d0389440c0094a0b0300300038010410004081c6410812500080801400d003903020b808805202c0d00c411b0140d50007002180036404590155101c0c168008202150b000090840724002c00046040000342c1c81094500c080361400401224011060b28a62180300d802d03e99600800c074442c002c02d41e41500c500400000442d1140c1f10f240408200c1501401c0c4c1140351041842c22011012209070169180900d000707140c2e65808441000c40c1c1d0701448 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 93180468 1250 93179218 93179221
    0x803070309020a080f03121312080603010605030105010e040b010b03010f09090602040506072f1305040314031006120b0d020411090612010302040f020313060b0a0302041b0306050312070b 82
    0x200d951120540d201001ca072140d00f111845c1c0a1021015007050030004650f4a0300e42d13601c41d120f0f111030417444005404144110000d0060718401d44020b903000401800106603079650b24003003821a00260710035800004a001400704110b01d00441500524142945074215410700d00f00d500c405401c0d00c50b0525003070340c9038900d5040248540642c2c004200050a0607100c0085003400188a130900201103800391603103803e00f401c096a401c00c410144000341242c3e03d18044c4580e0340000b040d01901c183c007032118810340c0d807401049400046110b64142000e80c10b10a2034000013808000604d070821014500302905801c041d100c280101065a40440380891140001103441d40704e481862501500403a0000d5040401000c0b0700c86103040341c0c4261001c00000300208002000c0380030030b0300c00038641c01e900120500410016009501c840400a001511230350740e9034002421600300300c2c43c00d1480d0780c0140c0220308003505441090000d107420ba01400c40e03a00302201c14140c9205003580100074411020 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 93181718 1250 93180468 93180473
    0x60b030604031b1704090b01090b180105031b19020705030a0b07050711030706030603110306010f0b0c01140f01331206090204030303050f01061d0f010203071a0603070504090803070309 81
    0x1040f5135503036140320301e55075540307031a40e9080000e00840300055001c00c40031600041c0c45c10900e000c40d0590407146483c0811109541e0045500e60b00c0035201c0301500d204005102c43c09807020008001440402401805521001901a007480c919901c03c2348240c10500650000c103064140e07090f4041000c0c90140c0da02c417000c1c605003002070011300710305405104507400490ba45405620805c107490140d415200132020340310400d503480c0400d008880b0040a030007000c000c983d100b107001c0c1108460b54000840c0e200c5885018080308881140c01d074030314100c40c200411825000008400072540b6503100c842078001c800c03150700803880381400c6440c2003007896080b031260405142c5c08140038000044096503503c0e62402c0040140c4425900f507200c00c8140400007881c24018041003800f99080101243c5080984d000c01401020418115043d404100080000516220414001c0c04264805001a4100f40041c1890428a0f41005004c1c5260000240204480800b6280d220b107483c0390100320b400152 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 93182968 1250 93181718 93181733
    0x608060103030f1806020f100209030a060b060f030420010e0d0206030618010305010c11030301120f02040b1206010303030e010c0207050f010c02090f011e0513050406180b04060b030604031b 83
    0x2044e40c500e4440084008034005038042601001c6520b03110440e10100d051f401d60400301c0c401c20a207903034554045015030000601c160031070300700001c0c010030035401e010843d045a0078541c403c0b00c0440e078580c0c80201501c80e200e4840000d0303009030000c1c41c00070000110701010907100e02d1003a5000e880780da00407001a00c2c070b6070303403c0e204500340e561100742902c07a5139a881c0042c00782164020040100c0c01104030688110b000006490403030304104c0300b81ca00b101140d1582d50a505442d40b00f41d030000d455185204054544c0005888486440310043c1807541c9581001821074110503164a150307414010344003c91580051005e082e03d1007218040c0b200c1060300010b80791000384410094102d5140010401d00c14680340c00c02e030407100400109043c03055140880c0b40f12225a0054951101c240303000d210b040460761b844035502078030402c0300044901c0a010020303030000e070542c803c0710480c080200304820031101d4040c1ca9202e910130b0380240300c00e080c103540141103d01d420032016400d440e0005a081070003000c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 93184218 1250 93182968 93182987
    0x708090c040603110f040507050301030602071e03020f0d0503010501050702090901090b0702100e0a0f08130512030c011415101202040e0402090601080103030f030b210618010608060103030f 83
    0x780200003a0742c1c0c0b80350051a00d0001c008541c81a900c80102480e50704007805858030500f00390751580d1a583c05c642d82c2c01c009400c40141605c241c62407d01041200301c884980078001d5002c1e0b0020084010300c580007074640042c03a00c04000b00709050004000d1030342c100003a200d640da41101c96000351780e0303150600740c010b002d03a00024040c1081030082c80b080c9500405e82d0070140318407050522140c032080181907600c05003900d0080640c11a00c03880004034603d03c1c003800700e10144080f81d01c141d0340d44a00013584d000c5051512500707074000144205c0142c0d001d10520744030321240303494079070189420100b02c559202c0710a20b003402040e12040303c801e91445000d0719096000e440104540f91278031000c1700c200014040f03074124000e030480da01156141d8091543c80d03040743d6240c1e0703aa841400d01d0900444c090250024095000b40c00b2900d4039076407003140807414004040e0390008169515002802c1d0460801c0b000c40580180d152002c00d04c6401e001181c80d60540341c042c00c02414140303034100d040751080340 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 93185468 1250 93184218 93184243
    0x2150403030c02090106050901080c0313020d03080a06240c150e01020a0906020102030f0a0c05090307030602250305070f0206040302090f041110080115091a030405100b09070809 78
    0x2501004064000a02840031030090743c84420680c0c03950810b99071440341d40740c2280420a110005000c40d1312181c015a40001e0641c80c807115038211744c0c0811880c001e00c45045021138484410400041c049206540c020040941c23030b900c840010000c40720940780f0300d09452040101011044045c841111510860041c0c00d0504201a20103018128000c1d007101a62400182071000300003a0144140283c0340502111003004807a92507001c039590082000200c000140901440b02c40c1c1030f9a001c0c00003100450040a0141c0c0d40c1c0642d45010102211988a25554400c420240404070354044151000e80c0d0703000c00388000c0c150031400041e4882c011540001d601c42d108000300303c0380721154200580564803071148810b102100728200840500010035540014203c180104100042c0e252058113512403810b01c10703006a1a2012418110340681a25400310000814442000410800400d9400700840108001d5540070001191801c02070582e03401c2218820104042d41340030721441c01801c0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 93186718 1250 93185468 93185509
    0x3022a0d080a0e0915040c1718010b060c030c070501090b030a0e0703080a030c1d0f0d0609050a05070305071505030c0a27180b060304020d03050910080612010c090b0702 74
    0x3d400c5ea10440c4490348054030360b020b241003400c580c00b26405407070206291450500c0c4419103980741e0540c0c0c003c02503101d01001c44d564039000000301d0f613100c4000401540f1410405165120a0b80210301e2a00400340d100c1d0341003040c2414204405140e03a030581e80c112403510070200c0c00300e905141d600d01d032210310b82004d09445000a04010f110350140d0003503400ca0841d40f50205920142105451600c9144408642016000a0311201494010b02d03001d241449484009454045512242e2901021000880b0a0740c006c01c014001d0040404c039500081801c10281680c40724180c0307008043d404060304c0c016004001017102c04180307000c2c9004004100e9045c00400c03d042c442002010b181c141c0f4071070300c41c8a402102016900c0442400364091480003e88050319544460342071040c042c00e03e50b425401c00005004540555a48441d17134200080140d58102031420150700300030b14a01c0384440c840f456031424698200080d0011600000c42e070702889010b0f103c5e5a03a001040d81c8000722214011480d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 93187968 1250 93186718 93186721
    0x1803040603060e0709050102071a0d0204030b01031a070f0c030c1b180b030303070e0a0b030a090210020a0f08210c0301080705010807080c030a06030b0403022a0d080a0e09 75
    0x11503041c0d005030102c8000c3c941d10034164940c45070a8812000d940103007401604690000d00c10a0346a429034040a10a803065526001c00015074104a800c0b07900308446124100004209003c10103200107610014078043c0003944c213050303c004c1c1c901c4407070113400c40510282220202c10306002d030390302202081c3c22504ea92240c48459070f880741100c40c1d03030141c0786d561107041f84071005004c9070303218007038007008050002c601d507850b076400a0f140c0120015619602210461001c03a103d410340d030217140160744400010a000b406441005600016411241c0441d488050f8120210380141c140c0650300750024290f907a21807100040101491140300c00e140c110030a0703000d1251081808000314121a81c41058070f900719190001114428030170f94104000542c90401300b0210a2034200454004d144400002800d41e500e55998081900c2200d0590150304200402002c81d49004c0e03281d4070700f50000c90724840383d81d1f110b00000d1074030b16052070142029902040c0c48640600a00c900320080e20000c00c40e1115 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 93189218 1250 93187968 93187979
    0x9030604060914060f0a0c050702030604032d140903010204080f0a0201020106060543111201050f0c0901050d0f1505120d03020f0d05010803032e0504090203010605060a0e09180c0603180304 83
    0x10403040c12901d04c53f07085149900000701546107882c001411a641c2c0c03049144078480350081075000641e40c281d0656003080009070f62902004030420420540d0702a000403901345c0000380c2100e03650781c41442481020040702064030407002d80300d16050030914503d90010749207007501c0000c40c501c00d01c2c0344848600307a6011051048140301c0105804044400003050072460000303a00b40c41041d41d41c3c504000f10344021601c03000c22100602103002041c545581000041d4100d2010b44004410b100c210a5a03070030040c86070390308030038030501621042c2e07030b0205a80d031003001302070740d90a144894108041d40460020304601d41c82e800c07589a035506100500a55031550202c6840b07070300070364104600118403021004019244410160002d50f4100300700b02e6140352005100c0500402e050403a03040d541c0d044045400d68407000505101c4000fa82c45442c402c1c90030702400048240507203016a081e00f004e45207034a2100018014143c0c01040d91040d44036100c0c04041102d00850501c0e01c2d0207400040b801080 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 93190468 1250 93189218 93189227
    0x20a030f150305010e0a03081303180e1906051302071401050702060910050103031707050706150801060501050301030c051210020a030f0b010305090604061109030604060914060f0a0c05070203060403 87
    0x2543d00801c002c01c0096154001c90ba034034456080e008011440080010700c1c500420b07852080c040e4000d00300b0202d1040d0030f00f0a1800d940c0a41c01140340c01940d801400144481c2c901c0d0341a2001c00c114041001c44c0c00c01c000100c2e0344051800c41480c0c5900010240200020003201c0c2180741c034504021301450610310406502d5040071101e43c030007441070403244000c82086001d2581200d0301910388590707c410305041224580e034001d040d4400e00c0820840c01c4000b40d07680c4104c0183c02c0448010030703c05410910080c0c00d481d543c1e4001410400140010300105006009900c04c8842c102c41c04ea0440005880c0c2c039051449022100080b60710108440c04460340580040c1c540c410740941c10010aa184001502124821f0301c0002c032a910403800200016655844581c40034010181603041041c2003000902d4601c007100d04440c1c00e074482044404102c00016008010091039000e030043c0d15248100100580c00181400411502c0d002020203c80c090011181080e030082e06803185840d09007005003 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 93191718 1250 93190468 93190511
    0xa08220812070f05071223120103030806030f060a02070c0f060507060501050a0e0a2a050918010803160f0606120203060a05011215060509040f110f060a03020a030f 72
    0x3008a10f80305903c80c100ea10800c1165916a40148000c0d8000d050b100103c645481640504d4054038001c610032a0911251004d00140c9400d00380d07a4000d0740c11450300030071080000e0304190080e031240f608100c0303000c8086004c81c0d01504c0008010f0300e030300007400d02c0c0d0840035a903408800070008603640401d2081c0c0c010b00400310700740110803c2c001390b40e941040c4285002076204101182d0301c485c01085c0705031800c2d0010980e150303510015520081400c540c00c3e800c0d54a604210000c0f44000842c0c0105003468854014a10803884800c07031035600d4980c55603201e1043c010921032034414038446000700151107030b41145060300701408002044c0c450269490310030417841d051344a88030301400103403c0d81044c0151816030300304c0d0302d1a140b19901d5907292480e01501c00076910085071544000f00e25615580401c500c42c50042d00300c0d0700c0e0361100c6d04000704d400c4c99004042d8003502c0003040440c040e444e40e0341100c4040e0b5403464010b81c0ca1803c40000c40007402500c60152402d400d00c2c081c1a40c0c0c7c8107200006 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 93192968 1250 93191718 93191731
    0x601050d0b032401060f020a080306040b0a05030d030b01030e01051506030702030f0f071b0302130f0b03010e010203060111070b0f0318010e011e02040f03171e0703080c0a08220812 79
    0x48401c0d246c502c1130b0703526440500024065541080082c0c072600f0190801303091510054118805180c44400203800c01d00340320107000000b680c5604290319581d0501a118000401700000c2001d410060641ca00c00300d260390340c0c1c03030188000002184851740300704201e0b802510344811054403281000400005030340800c0c4c3c01d45000000c0048014902100c01d180e104481c1d000380034180092000c1028400740441511440b99951b503680c40054545080c02980041a50140016a42e140200c005400d2892070703d040079155024503414481412060101d03040c0c4c0c03410125058580d0f88a90005c442c280321607d4154055080462403241c0c2041500104020403003840c24440e60f11845200c1000ca00451040303444445034a013080011034026965261301c0703119a00c416242c140e8a001d201a418416810324064600c00a01f050038140d00c448603903086200c40c1c0c48940380c030100c0d980003031041c1c8000e0406a034100c0c0031103420f03601c06121001a018568402e18a5031500b01c0c0913258a1084001c41d0384 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 93194218 1250 93192968 93192977
    0x10f060510021c0305070c0206030c040303031503050c010507060e0a0b2403060a09060207020a0f0906090207030e120c03250602010522020109030204020301080309180601050d0b03240106 82
    0x7160724000f00f80c00c07031820000311a1484011803500c045020f050301810700380500c100b05070100c0150b01c0e0741000754416220524803603500c078a189401002c07075000c08500361021240901c00e0002890101d5541d6142c42d09107840ca840b043e40d810000020590f00b6200200e40c40707110345e00420000c00310100b40c81511078080e40541c100c001d00a03680180d0003188850b5154100e5000100c003070100f079000020b401d0241400504140055022400d901029003100d815204c0c582010080c0500c0350140320060200340000f5802d104036998094144100b0400c070030300c261008500c00d00ca084081204890240d0010120340f9811070300039030031844c908284250144060071b002c0c08038856005000b054020410000c0d41100155140b44003003103245103800403070412610310000005a80e4900146020b00300030409103545641540401c2940c90f400807501082c0c000c50010861560707004026102c40940d901e801058190310000000d0801c1c001c016104c101c00b4000c0c042050007031520542c681601c0b030710b803a03 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 93195468 1250 93194218 93194239
    0x806030d02060105030c09041b0b03090c01171810020d0e0705180103080c0309040911031605060904020a02010e0a030906020d080112081810120b0d050703020d0311010f0605 76
    0x3022038580809018050305a030186000940364205822402c2d8000d00415100d24460943c000c0c8007001c00c10307a809261441008001e100ea00a41030109252407802401c054210380032246801070849001013800c08103080700144e07160303407a005100c4c01510106640003191f40e6a504003400000309101c0d00e1041c0c8070701c00c00d0f17800300c8c04e8200707001d50200d01118510808440c0e803955440ca405030b8080704041285001c00d10019034640c8903400745c11001c0b407182c0603800e400f5000368181450701401d09070021416000c2d00b002c00598681004880300b445044d01e01503035034500d256050303000d03141c1709902c4442071040f03200704024143c3c0720005500303403061075090f00c81d40308405104580c54030f402e00510028020300144a00050701e001e00030039020711a042000136040b18440003072910400c05c0e442c0004141c0701040044000841c0c4201451307807908444941c1d00d10b1241c2c40791552031200b0701009008000040c002c00c1454020012042000d000034003d02c130401355000071130007070502c44c401c1e113024862800 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 93196718 1250 93195468 93195493
    0xb0d0f030210061403032208190201110102190e040608100e070509010b0901030c0e06070b0103050c0a1a0f090d0c05011b201f0306050909030c0a06021810080603 71
    0x81029100070f009001b035040011081d030341c80101400b05000b000074522000d00050340b1030140200e0312413040c20100310481c02080c0c0001351150811356600745241e4410040c12421b0030000316005c042c0d601c0e44c0380c8583c3c3d40b10700001080007400603401c002494402d040d1780c0319104000390440c034101880c40081d80e54413a6990b0501c0105002030044040c120320500c400b0348954407903403010310282c00600d04041000741100110b59694010002620940180b50043c0140070042040d241601025a9031504a41c0f40060707118042e00018403512480708000341c0c40040b00506419902d1000004055a07240b05a0380f0b8680001d02080c8a204d0102d84512540381400559101440c1c841c0e0b040602081030204248400c21101405d03074100e64000d02d4441158210f944000c0010341051030f946000a0300c1c0c0c2000704102c4a5500244502e405600402c0001c0200d0310205046003425884000581c49108003110750041c1e001800400ba0040747c140c0f48241900e5206c1c55141c02610f05500752108050282c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 93197968 1250 93196718 93196739
    0x2030d030e03040902030c1e190801060207050402031009020a121104120206070c030b130209063309040c0f1b0b16030b060c01060806180601090b0d0f03021006 70
    0x32072241180341c009120400c41180e00d60000c6a00078a103510300f42c0f81138100c01807000c0d81c00c01c0201da40f403288004103c7c1c8200340c0d00b0402c0e00890840354103108509614000d0002c1d03a502d070301e0080030302481c2c0210209100c0320102d0302c0c050241152a42c10343d207034060280000d00c1031206800d1020190b0920010304611448101118240e490801034204440116002e11006a1000700211400e441d0054004041181d0080300d5000702000d02c4540341c00070240c010413400e080040e012a01c50110030400640d400100c030f0103014070543c0c00560001d0150b2001041e107060240c000c0b000c0c1c1050411880d2813000358401070120000300151100308041d04a00c801400c0c5020514000303100e481c1c0c0c5800310725802e03050105040202d80a01c0c0115034450344102103510703908281a1004260344800092080e19000d208541c0c0c0310000c030001c0995044120505661190184241d01180b0703610006e0102da0f44654002c07030221500103075080203035801807170000e40d50b04840140100c620f01e404001308204284 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 93199218 1250 93197968 93197981
    0x90224130f0b030c0a0203070b07081608010b03070e0a1505030a050a0209130b0402070c0e040506060d0b07140918101e0902030a0e06010305071a0306031b040608150402030d03 77
    0x10010b400e042d41c2e1a0700d40d03005142c1c06004200c0540c8018490200010104d000d118814940342e600c40d860740c01c0c5081500000500181440280510400184615862401a20b40c00b601c24508000605001404a0300c805416002068007600611655625030b030040e0007540204d07650082004181d842c1e6842208901600030040c0e800b0054040811100146d60494910800700410040c50102155a51101298aa4004483d014000c4108000d000c4140a0254080000d8460818070315403507441281c0b6440c000d00d4007042c0110901c0e203048000150041d544c48004c06005042003460380d500c211289401164540c0301c0e080013040100e42d0703840b603141360b1541c0a88403004000d50390605c0318140c06500700070894425140d0b01d0500b02541c00041040c14021400780000d001c00d030303081030f04c10605c9200d10101c000c03800d4420000e0040540700060760350503a11696000740201c030742c81c10010b006040b443c4c0c40102284a129541955080c4500610380998400c40403100005011203007039003035405 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 93200468 1250 93199218 93199229
    0xc0f031e0f061203110706080709090207050307020d051b01020c0604030611070204020a050706051302100e0f0901090b12210a0302070b04030f0305060f1003090224130f 74
    0x180548180008511500000003140341c19001003450360301c031607050302440d0980303d00760006505141400e2088009008034000350200d45440607042c50704d160040c108206500c1460461a4002229001c1c4a428401d4078010b2354010310b00741e001082030a04a940380d510001107072000412804d403900542c000602d0f9500303284003418090a003407950300ca000c0104030440314509520070420070b00005a0b1588004d1a480c40700e9116943c80789100d0400e00100d0300000d010303801c410152008000583e80b0b1014211000110303140c140d419030040c50106101142600845400a1000e40041030403034064106100c80c11066031211440c1158001c03842e590003442800b001d00307014074075803a01069544d50017490014020704015161031030941d0740600c032050440d81940028480743d50300464507418018684c1100040700d0031846101c1c5000001e100400c1420410b09166850381d800046481c1d60804c1000950810380d194582044150030719000c0d408003010b040100c25003c0c0100c3c0c0c1a9010200380240c4a = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 93201718 1250 93200468 93200501
    0x902090612010624020f0102040501020a02090c090a150e0105090a06080403051209160914150f030304030b0703050601020f0703021507150c0906020d051c140405010c0f03 75
    0x440d680103000c40c0100c050070048880d52244004100d154154241d1880c1d00789039044540300c84441c81000341071580c41c0240ca4982e034010030007084541c2c0c3c00243d10807a01c4d0121207041450f100d9031200078085c400d0044403a0440c1c0d40080008182444000c410054081a1183d0110b00309410045031203104410082d80d0249030700342c2c180b01c910310650200c5e034001c1c4a820401e1408a06c0c03102109401d0044460040544c8442c04d840d40542d51003903210010040044140000302d82000007000c9014002d00c0010341450003443c403106662040c5014020040107816a07945544908203982c4046e4101c44c10700220f0700705800301d181540700240f03a2a00310003640c0038140d0342d0300319400c011940c2e0303d8058880d08044244100c2d004605082000c80514819030000230fa96094010f010b441d6010740d62001d000d40d00403046045100c0c0d08041101c030003410085840744215449288040201220100054900d1108003040308200c2c05501c4903044040544905601c0c03400d68100320141d8001c0400f980e07501 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 93202968 1250 93201718 93201721
    0x30305040e090a020d060501090b061603030c12060e0604051003052a0a09150812041806080102131410050906071a100e0109060510051312030504080d0201090209 71
    0x900c0007810454100300c0c820191200c80185800203000c1520520381590450340c1c501c010441407506119610100d0700c00c0d0303030841c20100031000148055002c0e42000d028107807903201c0d0b405000d215000c03d40b18054054010401682c0701c03801c150f8040d2049035014000c0340b41c6004221400094040070b000c0300d50110091081c0090310b445200c0231608400780b0304d04084140109070242e80d5021910700a00b022010015007941c00c00c443c09040440c5903c0003000c0d1300504000d071a003010703030310840e0141c440002e80201c1c1d511089942c54024103070380d80005425480494a4014885c08900d100708942c190884503402801c00000c0240d880c1d43c8000c85004684c1c20424803009040600290050754050160311503204903807280582e031032404640d40301070b01e040307680c0501800344201600c030f0240078482420800e00f81070101051200c3c042c40c0009080c09408182d05840b80780d03000c1404003504201e10300a5454055140290060b00640282c103030601078031512034403440c414400e095105400a051141e0f5 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 93204218 1250 93202968 93202979
    0x8010c1218170d09060b010e0d110d140109060b0108010b040605040303200726190206070f1e02040c050705150901020d110c0c0a1202010503150907020d020f030403030504 75
    0x441401c100b40140c040014070002c0d030340c1c50361440340000080c001c0720040341d405040c030001400c101807014041e102e980c5024208010410b404000900207006880c950f2540038142031801c001c1c84a96100c1e040da40c00c103100e20b0200b200c5500920b4800300c003071700c410391b4598039404c510056015500500340021018032003040803d10520303044464860003454049040c030b60919070350804100790000c0120300411605a095400c80c031300b401d4410401300707003c1c0c003200307000701d84110b5130118900010344181c01c0851444d003480003c41e20f114180d41d0102518055581000340420381c610070280c240c3c4910300c4d0055000e0606e01841c1101d01083e40000500401055003503903001d1550080c001118540d070a200329809254540703c2c20072040b2001900c1e5071a580c4440140b854041e04c1601280600740381103042000c003881c2e6030490300c42a42402d0240c0c0301d6403196611203181300340c03118103079018a03c0030900550b6a0041403210b655241503094031b200030b0010f501c850fa0392281c3d10000f000154100f008008 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 93205468 1250 93204218 93204233
    0x30108060703050c04030f0c0614130b09010e100c0302070510020303190f060b07171c0f0f050c07050d050306100309050c06070c0e0907031e03020f060108010c1218 72
    0x5010f41c104007000d0170301d0f449485001c1e01001082048400d1a5482c1c400e10020303402c04c90004865440032010341c030b0a00c01d014030407685100740c071402c1489140450b48103620ba029141155020030040c1c542012141007070300041c900990f610094001d402a8100400c00c1c1c2017043d81040d20010342d4000f580f454580400322491400340c040c001410603503800350f010403440c660150b0b800a00c4e01140039521100503040c140056015802d48181c20036003008801c500f0074185e458400c05683d6880b000628840c000c0c041c2014110110040c4034003880e1004004100008501600c01103000d28100c1c2d400400b045410366032071000b614495807204102d81e02d9045c079032003500600d009030b2190090301d41d00800782c00402c00981050008481c1403091000c144220700410348010741c08100c2078001d181072899900c0d0310800c00212a414803140618090044c1418020403880c4400c0c01c2801c100c640ca91f81d00c194403402080410030f0389001840052400c20140d074180a8081e202194150b07080e0a03082c166101370 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 93206718 1250 93205468 93205471
    0x70b0f01080c1008130204060f06080c040501090b0d09020a0b0304030f0f0806060a05070506010e0412050405060a030e0a1a090106050d1505071b05070608060108100306020f1b010b040b010503010806070305 90
    0x10703171400c460101500141c81e1805104001c02d515002000c40f03d040640c00707444224020422a5030803014003017006540c1e4003d1f02e00c02164005100503030394021443c2c011001d070451076006504407280746c40004041c509000210321482c06591520b00b42c2445503012900c448030581010005405440450070a2411000a0070341c4102414150300e4000f5955900d41005400d91001d141141083c080000b44603007003440140030b003d1413801c3c5143c2400c1000080c11801541e01000425541c0c5440681d9054208000c2030515008101312103144424811080c45190841d2111002e5080007070014181c1400d0f040146405ea101d901441c407210852010001014000c0c00c0f5000c10000f40780390240d15900302c0e07071044a60b01510141100a0800b000a0310140004c0c102134104485401046120381100c058581908c1c0e04c940b0150780c0e100d24403c819a207000302c9001070201e91103403200395000383e81503000346a0380000b5502030148801c1c2c03000544240c0800d200d004a01d402820000d00140d20a5000a = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 93207968 1250 93206718 93206731
    0x9060f0e070c1716020a09140105090f0a05072a0606050d0b01090207030216060203191e0c03030b0303040e0906010905061f020a0804030602070302010e06010b0f0c01060b070b0f01080c1008 83
    0x10030603521360340010750098056480801d03595599090350840005085459001d0801600d0120311400c00d101a1078078144020310b030101d025070300c0d00071642c2d0a205680d0b80320440d03107001e0000604880345922000c5030541d01c008661592900900280d5801e06c407200102d00740e00b00050054580ca4400054080e501a0404804602a25001079044004d404804024202c0341d80290f4841c100403c00400a400c845013074400d1052040040100d48031a00f90641c8105091800900054041c6003d60103000d006452582c103010100d0081078069180300e0341486105a0b000f02e80b0542d9a4212220490b0300940d40070b60403148075070b24407480b119100300710f580441c25072049445030f6009841c0d0500a8210340c1048400c182c000584a0502d41d0901490105c000900050011075241c0407a94445120752a5105540301d00420396102141080d403000000b803c1c4100c00030764802d00d52421f069091001c07180c002103090103c1c00443c0d034440014010300e80c0c20020b011442d050055060036030310f090303008200f03 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 93209218 1250 93207968 93207997
    0x711060d060b07060b06070b04080c07091e0f02160b150301110318010506090a0f1526070e06091302031b100806181009060f0e070c17 59
    0x2403446815284100001070405402c150340316030403490600c0580b8070710344520b07205801c1071040300003080d440213160750481d0744150201d5803000d00030000c40c14100e05600c4400d030b192a0261000c06020228144500c01d241440304200140a10312198102c1c0140313240704542ca000304d0700c10400030b008201002c1d000115924042994500d080c0003e0a4804038a00914840d03400700520042c141d000801002001c0010300a10040c030303005020a0001000030175115585480e1084200c4031841e5911201000c02c10010361298581c07600d10012000701d203440e01d8644010719403101c0c0043c020200301107050382c078400035445a03138440070204082110702030700e46078442d050728103d000107a07020000210510f090700d446940781c0140c075017041408aa00c07111a414407440104202060340c40d21002007079000074542c00c103041c3d11458584000088107410544030b9524018000c510014890844070485081c440d140269948101c0c0884605c4540c0700300070102070700901c00c44107400c0040003400c0800c460294 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 93210468 1250 93209218 93209227
    0x30519090c2903010312110d081603021204140f030a050405010f0e030d030506030106060f050702120f0a05210c15060f0a0b0405090702030c07060e010203040b040605030f010503070b071106 83
    0x455a06500a03442207402c00e02c40c6d100c604e10340d600300c1501001c102081e005003148000750880903098540003010344a039011200c00891000c0d010b136054550b5a480e20b21600b46524051a02600c69440b10482c0107407403180e406516210341c0d00101300c8550b01202d98540e42443c0c80c00c401510030000c221180070503c51001d158040d241c804110740c89a14606540104150030b0410906086800a4000c0030410074080c44601400d900101200c45140c0d064130403000c8400d03111001c5040014807403c0d03000c5030080c4020354007401000648809240540f605030032460002c481200424428100b90342c4968120450702c6c404003010325043c2d03a00100241c001d50f180d03002e004c002680e00c99241c0000801c0c0e000030400b40110706142031140d50060032400190324250b85422410390703880c11803280384104032920304980300340e0b4400e00588008208281e001c2c2e44a41c0c40d003d010340b4a80080794100c00d142007840c00011203290000e81c0c54211841064141e280001039104c1005848540b10b800d90054000c20 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 93211718 1250 93210468 93210539
    0x1d0103110c01020a11030406140f04051c05060105090f01060305040521071a0f0c0d020910090504050708160e030102041d0105100c050705040e0a050a03030519090c 72
    0x40241141000d00d07000503614414200050b044407903580c0000b88683c0140400e126240e0800081c03445850b022747d003a91108070381c0f0741c505030b14419a00003c0d00310380c500262000d00d450400751030183e00e2040e41620b0071607032280e05001a614089441001c44011100104422070090f40000c1c0c0060244048c0c2d1030b15201ca00140540406004183c4ad003c48009241c0d4280040600010200c0c0a020f10340f01e51810115503006e040d00700580311003007910000608281c0c035101503040300c100e0038001d48845c0c90f40441d00c1018001e00e00e10f1098034040c604000016180d2485880040e02c51141032045405503010004219054440500000d42540d400c000c0403400540744500f103007090b21003904801031740d07061505025440314041540020310942801e1100024001b05501041e12700035103000804000c99160140f400c540060302034a6801502c1459062640c507030803451107214080b00b00c1046810552032001160b44840c0040c3c140e820000040c040c0900f0404c000391100e84041d42c2800416012 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 93212968 1250 93211718 93211751
    0x20f0d0504030509030f0615040c11070b0913090f060e0118080c0106080d050906030717040f0204180b0a05040c0e0a15050103020c1906020408030705030414101d0103 73
    0x940742600071583c08103041402e880d041040c01003101c8030070301800e41c03401d1070558429503500340c0180e103100743d882d6400d1003105480b440208403156042d004450322039917138008105440d403107401d446000340c0d8010340415070426980540c0b0030880d40f200c54405842031a4032950000c0406030b440900319500d40035403505402544444052840c007440c0c100b607556031440901030855a4070344c40200c0c09d41210a800800d00c0d0000306031060000d0544449640b80e40c4da00d81110b52444000b0030b61801441c440c10f00043c060104600c50303042d40b0a4030f04010b0781c402d00c9144e036860043d841005041110301400118008101d800064000d17100318142c0b517000e030301c9042807200c800301100c403500300da0b5403001403912142d4000c0d01d910080100b800d0862a02a40010f002d86506a5104840c011003150540714200310786503040f24014030000b001d4075150740c4103280c1147c9030783c040e200c0e08007908600c4a2408180c0f8000e0b07240c0300e800c240ca441d01d04680008140c8128401c030500d280d90706165541c0508440e10850 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 93214218 1250 93212968 93212971
    0x70b0a060503150603010f060602070608100b030a020a09061b060f020c0105070221040f090b0109080f01021c02040f0510020c04060f1e0803030c0c160e04020109080a0f06020f0d05 79
    0x202000c0740c5030f80c6004424182180c0d40e5401070440c0500b8254200281034001c03811b04240c4800f031401e26810750703801c0348a50b04400a5445641450400000c01031108500e50140c002c408559a981152603900c103400c9488000210042c0010a01000c1c0400012a80e40c0070f80400300d101c490140c10403901602c0c40303085400031540000944c00c04100440810340791110303175030ba01c0815640c0608007400e01c2d04030f611060380c902071500640d6071204000300e5a8000d180c80001481040c04483e4100030841649011350003031000c650390480c0300c84500d02043c4044c000d4400b55182600c00f120020328103030030050710202c003003800b005500503118201034544a43c050500036248000030300e6030986c078203045001c400303211040e6003400c404492401e2149041c04800c603130300560030444060300c4107000c0c8405410300a41c0384160314098020030000500d05800c2401e544500d000343c1f42d9030001b9586080041d11092148030003001100c102e43d240000503511341c0a0b00740700c0084054541001c4c04042d00c001200c03030 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 93215468 1250 93214218 93214243
    0x20601060f17010e18060f180a0c0f0612050c0717070b0109050708010501020105100509060f180a0e0a0c0306180f030e0f010203040602060f04050109150c020d08060105070b0a060503 80
    0x1c08500300081800d0303120b4501174950035500203003007a1901442003400351401900c40c12030303562501c41800f04540100812075074903820441200c07060f0303a40c031a030b02500000c500c150030200fa2407500d09a040f664070720034140328246100b001403a15440703a6621100602108182c4070002c01800044003050500320340c01d001e02529900003c1d0340c1000303a00a00400d40c1640114116130401e01040170154040804604071801039440c0c81080d1030341400180f000c60a00401038011600c003007181e2001d003160082d54091440c5070340070000101d140d012140c940304890b00240c851a1060360810004615910002071800c1c02c00c0e072440b680c3c01c0c0340d0302c40d01000341443c07040c0c0018004010f008014540582e092802c410240015854103181c000044d46801009110524401d2610005424000290020010640d20203400c1c491003050a92000041520200500051103107034a101c0700030380a21003035402040143c5940d800c1494a40c1c60100c040c01c000e01e000d00141c1c64000029481d00c007004081400360 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 93216718 1250 93215468 93215489
    0xc13060c0309090b0d02040b030712080909070c0803011806170a02040b010914040908192d091712040603141506070b042604051f020601060f1701 64
    0x2810307080081c1500c8003a08115911843d1151141d56552241092210254140d802098154a0500081c240812503000103905440384984804102c0720200401b10b500c4101d0314128141c5034400110745410640d100140521000c1005000075a070000c2c01e00c80310300700c000000c0f94142d100ca00d0f80c9103055125405041c250702140c0301c141146414010085802c07802c0c0703000c1701c1c002e1038103612010032180c00d02e07594010b031760f030f12001411300c0300900c11a080400d2201900c1c01219a00800031f02d0013036089030766500b01c0007044001119950b00034007109080c03240da8402072900d08000c401440800890151305052248040301117820751150060002441513850000c1c0750411502807521404001700005e0352858055401c40c044d07501c0e0001e490380e0981115841005503101d2410243d9a818101d2030006281d101b100c41d02c1d9062404002c2060750011703110010003800c08940100b2000c820f2000c14050b8121200600200348504103803c041d44051801351292540c3c2c04071035a03248000c0c1c12015094 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 93217968 1250 93216718 93216737
    0x190c1805190504020f010c0507090203040b060310020a0e100e040905030a020c01090806131a0112060e1c0e0a091401081501030f0f0819020a03020105060411070b0c1306 74
    0x1045060241c0208001c001c005009038903181e800107000c41813003850360f030500c15082c641c04140001001070801424001e034045580381094105041824811240301e842071060600b03400c00c03884c10f8001e985203c003103034903441041c82c0040b0401a481c500d2299001c10000c407080c04154a40c0e81d402955000c9000b4400f82d139454003002002404d10000303e01040c18081411410081e2190008000d94881700c0135003070150a001c1c9240081560b101500d40081e49020340e400440c0c030500309609247e030f291050302d0800c1101e01d241480c0d40c40d4694040010900c16000c1c090750040c1c1d0043c2d900d8040724030018044400e0a440e81d846400f200c440b030703203c1c85100c00c261005011040003088510020140304d84801c00307542c9180da0391a44001c051800415418000e134400d000c1118a6055814043c117034a2039440302d40c81040001e558045403035040e0015800d1001160043c01d251044103445240c03e40b000c3d00c2c00b031041d00c9145245501030031908081804014044601e03101c03080f07010181140f541d407070114 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 93219218 1250 93217968 93217981
    0xc030b040f121e090b1e0f04031b0603051302120c03010f060e0601090f15200a150513110a080d020a030801080c09040620030a0209130b0102190c1805 66
    0x1c1140f0140305409000000100b80302009405080da00700c0e03892410886440c0540c00c21090050041c840b54111b04240402c000c410402040c01c0281880f41d0341c1313002803034955645800c40c2980c07011381d1071100b5031034550032070340c05410442d1505034507541754800c0b05e032440b20760030200307084a950030f11040010340c0c0c500c0103112184c0c00034a03468016109203000c178400d03400d20501c403021a076548030f459951482c030051a61950b008070105100075a400c2c1c50481c05016081381f072900d441404034110340c03c1d200c2501610510311144556070180300b00c039400c0e40240c83d0729a200d440e051000c100d802d512580008001807209000c2200300e09a03030085c0d01806a650840c68007504500b0180c001403010f402292104001e5100c0c15120b9500c80d82000c0301284890080ca1407040750301e03840d4542d00d1411000030810040da061500101a00d040684060741c0c0303100542d160341c044464034441c42e80140c014895444800510b10964140317140640900072038141d0781c0400d00002070048041020564481041007031 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 93220468 1250 93219218 93219257
    0x90c05040504024218220603061b031104061209080703021f0b0306060d0f0c0b0c120c070e091009050105070807030e0c010513050d08090406050307030c030b040f12 72
    0x12111211081e590404485c1d6035810344481c1d55145c5280039003818100d0781c0c6800644d5200c450781c01e01c220f9040090a849041a0780a000940c510101002c4c28441d1440024801c0c45844054400f401c00207080a04200c0200c58144540c4400944a51150300790408a0020001884054841c0d0020210410002d080e00c13050844039509014592411411030301944000c1040c80c0e0018041310030103031681443c5415103071000740390006801d404200b500801d1a1020314014a0720b0040134044038a01da0010300d510003284112020350081d500a420204900d03c90002a613402c40540d03015101080030400c02c000071180140802d84450391504c0a21214581140034a41c01207464030301840f240d0300441c2800e99034090401618100400001c50800c2c626103282c08001030070380140903400c0c03610b00d814140c002c0e0f04466031540c4254500480002c0d945000a4940c1c2160741c01100700a00c00d18607107901c05401c1000340291001d003880108040024661103e04d401000c080e165038082107030500d0000c2 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 93221718 1250 93220468 93220579
    0x204080312220b0a110c060f01150e040903030e0a080a1e020a1205040f060503010905010e07120c050f0319050c0a050d0504020f060708040e0a090c0504050402 70
    0x8282c1d824903201c0c1c00150345a14004a45810640b50680c60310303043ca4060080054550300380c11204080f8280103050400308003140148254083c800151341c031101c100428054108680003c5020780f40e030860305003020380100c00c190b4002e08000a0303401080341803d007064645102141e0810002401c05451074005842c16462002c490001050140206019607070351040800601500410300240c07021030b2181c070499020b0580c3c03511450301d40c2d90710000940701390000c7c0a00712200742000004162104601800d5215180a5a40d29a8107a0001007e40180342e00c01c045420058100f0102c00c0c44040040114010b01080c0d00845200c201c10320b58800702c030809002030600341010440b441140340e0007015505020003034140042d40741c80d035100041c410041d000c82c2d150004404a9803800740402040500122140403401e5842590748086500449040c20700040200400f0141030205041070b5000303540c003500c080c000315900201d0725400242d58900181e50b4221500c00145903940001c1b40c0c5c1000e = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 93222968 1250 93221718 93221731
    0x606020f0d0f170a0f020f0c0c030a020f090a09060203010f05011205010b0a110c030a0f030f020601050a060c03050d060b0a020106090216020f0307090504050303061005161101030f0204080312 84
    0x180c807011054030090807010010705080228951a02003880c00d5215445031704803150112045650343c0804c00c03500010f400c1003071804a94060100001a14280411078103081980200454250086001040405903000d041d110b042a070f00c0d50080300081641c40158040c001c408075009107145800c00062030241055452120b0500303090041000e011420195020008903081c6035009103406070358540343c800002c0059602d07104550800050104125003010390a00954a18106681041c01a40d85000030302c50b698020020741c03010003260740b00308001d6800d1031091070000e2030300103c01c012809444c890740001c208100000b910b11350703482e0244076403c010203800d4000c3d402d1660441c131000d900b092591003c0d000d0607200c1d82c50b5075a9541403080d03c001d8090844104003d0070306041985d62070300121501c900460601042c403911900802c20b68800c42c51595010080c00140c5e036802d024a03503924095070500d1384403d8148102c02050000c1e101400c4054005c603141c8000030444c1c07031103d2019200 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 93224218 1250 93222968 93222977
    0xb0f040b06040b3f01060c11010e0111330403050a0c020a0905071101060602010e0604021311030c030f011202030303190e030406020f01050a090215030c0403020406180614030a02120c040606020f0d 86
    0x1a0000500d842351b058415070027401c060640d1010140140d4600f03005820300181800340d0b94041101400c40d0f00d0759038140d013900c105074104002c08480c140080d07805913006030200d981440f229903100d20645c0481030140c0b001d496241c031565604d050350155001569460049401c4080d42d41c40c1040910035030004183d81e100170300005584001903600d41c0000351019000d50007600e05011198066041034030b031003444501465803440c1c0207141b03841c19001a900e15009841085c00000c1e11002000f184a486030001c001c0d42c030310f03110310300c586280b280820b2000711116100c4c1a8040198014406070000304400c2d0090a081c240e01010709003101d07001051080c0c01e500d08920b04016845051801da1102c00140e00540d481d00c44c107110300464000d80d0b00c002d5200e401d140c40803440c0b40c4250300000814811120a00915480b0001301145840c041d05468240e0300200c0101c0c05071900242c0c08002c03400d101d046c2d82e4107040c02008075059402c04c0d008100540c1c41190000c10401e4108280d418000d1107203070 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 93225468 1250 93224218 93224237
    0xf06040b0a140a030c0b190306180203040c0f06030b011707020a080703090b0d0e0114070e060f0903030f03010f0f08070306050604021303060b0f040b06040b3f0106 72
    0x14904403407a000303030b8510003030881445001d03495081069024503042000070809955900300e8025583c03042d42103a0041e03284510060302039009000305030581c3c0742c10018040300707040700405000a42000b00283c0d141c3e0502c8a0001c0c0500340c81461001800f80e503540410221802c40000d040301740180e4096401221250404c0001c1d83d012824016483c1c0c0103003605d0355018a41811510010a600310265120002440c0300c4501c089071f1000d4846458130b4024080b41400c1408901b15036811100c1001081041a84064910300340c0018680a84100040c60801c49043c1c04203145410000e80681d2203140080144081030705200d0002c0140340400310460190300345140340b40c0ba0308035032100600903030311040429226034994068603003440b9840080340515590341010300240a120081701c2c02420f503604d90b070000d4106809940c04a1001811b03c80c40c0c2840c2c180c92140307940c48180b184240700070780c3c0240c1e07403046c07801d00c4d140074550030b5a4101c030007907800b034041c0c10180c0300c060740f040007806030402 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 93226718 1250 93225468 93225491
    0xb0301080d051308150403032f0901111005011d090d0507111f03060f080a0f05010b090405010203040605070507020306060111030f270604180b01031b020102030f0604 73
    0x1e41d0003000c0595180c030343d854509041e150400381d200c1d034121800754000c0c000366a1815505503400c138030441c040e0782d060206501c0702406806070b2070b05003080c003116280d00d440002078034125070050098550616180780da4122115030503080207640d401c0303661240d480e03d0040048254032b1075100f0b61509070b8001a00d0030b00b811032490b55140a45046541406404075800c3c0c1481003e15492a4240f0050704986800103d0741c1e20070185000021118007092074203e011411141e03581c040000d0300e108078000d108130085500c1c0c80110341d0701100121520342d02c90070f07000c602c0d48498185134002c521940016840c0d04103441c0030001d5030002040700d020000305103d0000036940010701550003c80a00b0000c8a121122031924150b10441001d1440b2074000100c0500000c0c980305140c130004c40c50541d010701650a2001c114803840380d880340e030104030460401e01c910318100754011507100a0506001034000b200d801d030000c0403103a80d0820030145c2d50110401c85032404100380268801e40c01c8070204424100b12 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 93227968 1250 93226718 93226723
    0x8240103030804020415030302010207021201151205030c0d0f0f02160b07060b060c0309030606060408060103031107080d030207030210140703020f13080c1309081c02120106020105100b030108 84
    0x14400a0100030702c0340c0c0441c1c103545030b59101058808800301c1d500209612818081d008c2d6021042c02c0f40600e003041016418480b0611070300c861004100ca02100749480c229032107a1401250a0940c2d490000304440803941c103040007902c403484001d03291014403951031000504202c0280c0110f030f0135908251200304100141c07401c000291030241188546a030f0150414200411354842a83d030040e50010384e40c001c01c41c00101916829004400300c440c0e9a854005104190156120752209940404010700000e8000c001d038401c10400c00d8100ca1007565a50485880c01c407042d610300d00401e81c0055400e0526605101480c0f02003151318041c0f09102031020800c440c110300910744003c25501040d01050101d20004a070100c000d10908194026200c851715a04d4980d0f04048500c1516500e074000405034803070146202d6640c00041003814015107103880d070090010300c0702d01d5007840c2e420042c9001e02c0742140c500c01e028002c0c9500020f15881c00c0c81100c6803580060f0003200c541d0070305100400140000 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 93229218 1250 93227968 93227971
    0x7030203010b03131a04110a0b070b0a0c18061e03020a0c151416080708090703030305100504140a0608030702060904020f041206090209060603150f030f0d090824 71
    0xc150b4240da0341c0c4042c1010307000c10f05517081d6808040100010721080c4115042c407600301c02c008a804a0f1007540c0c0d050b03190064461142c0040c0054002000139071000c0c0c0f1603108408079240350400040b41c0b42400c150000513a21900401c02003050740c490000c024000d0b5083c14160700301810114502200c40d80042d00301c0a1550000700b009058219030a1a4001c540044251101814800b4a0390901d0750348030001c10740d246503000c002881100081c4c491482401c0460146c801c21015111050464408802404000f060010340c6025408006080d403614031840008104940b20b5843c9410304613503400030b6034040d502414803948140015030140c0e403680111940b206049030010780d20040400b04034030078001d40e400103082d00300000c0c4901c02e005840d005000c00a100312590300790795403038404011040c0015103610a0740030003012200e0407414821400070151034024200d84082d05d406058610b407a0614500300f0020300c80c88002c0000cbc03a820000d0083d82903401c030080300107402d8410b060400070360 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 93230468 1250 93229218 93229231
    0x50a0506191e0f0605030703050304080d2309150a0804110108070203041e0317030403030c0903150c020f0106060f08060d0b06130605030102190e0405010e01060e0102070e130b07030203010b03 84
    0x5031200c0b04440c0403d41c2d0700c410002c0501405944079290781e0306015480c1c3c0c1140c03158000030300801c920001d120f840b90020105485103401c0d00810518010042c1c10160000b10704603804c6840325400c4840d245d902e40207000240c0c0a83c2d20340c00a4a0586800101049011040c0b4103001c00b200c00d000c0025008001d58042c1c651b81c070511039100102c00003000f00c0c21450352010340800c1c00300310407240c4180d01c038004501c528025102403008443c0f200c022120118948401740c400b9001c3c240c04840341e55541c0105540f4916441100d03082200800710600315404c80c0d1011020502d01050394814582200b03c1e240e000c0e008580c45410300007031352a000c070b282d0401884944250a000e0210500110541c0428060f00c006002107487c0d90110384548080c1c0022003802001c1205a40c0c180042c0c60f040c010b140c16652440b5014009910f40701064459140300c0c240b490641c0989040819100030603062b0034824118901315007114a41810b01000f0b07018081c000c00205401000107011690840c4110fa80015 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 93231718 1250 93230468 93230471
    0xe03060601110c0909031e04030809060f09130203010807170304050f060d140a0b030d0c0303110405090a0603031b0c0b1308010507020105010315090c0302120a050a0506191e 76
    0x3000c100320a0520b01801d2419500c14101d070240081c01c5c60010103865100001015008590b40052060805010b1880700420203841004001041d0400402405004030805029814110144009003003200400008012940e0220041040310b0041000300001c03c180281e030b10700c2064500410380c40f8820742c003800d80110303c00c0b03c0501c81521032000702d07002010704e02d404004c3e11451210502c5440810381c0d601501c10b0801d450410985030203e54240034a009880d0800585001d5030260060440c607800c45042c805d041c0030008150722009001d900c50707001501d0001d0101e09610300901a031403421080d0780d0049681c1c4080c40000c000011810aa0f200064642c0c2c454110300f6041c40c15031919005000c055003410123120130203405401060690703101d03241480307140d80701226410440d0082d010151000360044800c0000d401d190b110041590301c16001d0f1026940c3c0394489910703180880e542164150f001c2030420a840c81001000344000c1e41c0b100081c400150f418204107034483c003100ca09648176 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 93232968 1250 93231718 93231737
    0x21309020102030915030a050601050c03030a0507091502060108070e010b030114030c041803020d0f20031b0a11040b060304140a170a080a0209060a051b010504150c0e03060601 77
    0x580c020019180d80500007002017a1822a00306550301c1d13600141d42c81e114840c01d1801080056016409440005e40440021800c5588809068014010180c261001e015040d6400304840c0100400f00b5041c20150700140f040d94506014145803a6080e40a003545030303540d8006112544c0031104403030443d400c003480780d0780c0f00086034002801c2011000f05668030928107481400d060800d00400002d0707038041e03000c0c3d540d46440030a00b40d83c0c01c2c2e01c09041c0300c009054149241880064040c0c030204000c901c10460741040020340c1c00c0308860840154402d03003640b100130960100a21400c00601198007512305000e100c54410204801c1c5c000600000c0000e921007488000070001044021810b98000c0940c40040050241040d190303444440c510300001c0d40c400024050540600071a0000107019003210702d0301200c600c0840b01904a14000b02c1038000368841c03907413040000d00880340664014030340095844880b90085040307869244d130380750601c121740c1034244941d6000f0480b1603101c2800e00341103801d03 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 93234218 1250 93232968 93232973
    0x11e0f080f0907060807170103061a010e010801170c040504050f0601090c080606070212120901030c02030301031a04030c060e030a110a0302060606210c03060102070501140a14090301050a0c090909021309 89
    0x487c600c10410b0001a5020700000309010380d035001000300d01c9148041070318034521f52004440300351500441a0120b01000c0040005094401e609000c4c019203400b5600c001e11540009015100c4c1501c3c140d0b21540040104c403804401408081d00415180100704010944080040c0c490385c0001d080f14819040850064155150b00701c405030701441c0302c03040d102000c000740c410380ca142c1c02841d00240060b2520b41554641400041181e0589422200368541501000845201d0200040007101000040042d031400106940580d100020b48034014580b03031803030414010310402c059403160510b0340c08201b03110003003900030607140c1e045078043d17402e90303a105010711003840005500e040700c842e440c401074200610b0786400405140244800d84c02d40e80580e544100444902001d00c0da24001c04004020900505004802d084101003480418505204a0b030000030301b1507030704462444006071035120341c1c940183d00500d6440681030304807080003014103940208050882d24412040c00c0d540d05c040381000d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 93235468 1250 93234218 93234227
    0xa0602071e0b070b090712021f021606030c080604090809190b0708070b0112030504121505040809040c03061202040b13180506060102010902130b011e0f080f0907060807 74
    0x241090003030b09a5035460920b025030700081e00f00d0f0038264078010400041340c410030440551800907001082c0584000440092280c5102c54800200c154859a0320f56000b94070840f9040c001000c094030300049240310000c0280c540030700284001d100c1c03450301c0210400603207a1010768000400035070310443c03811080e0810125850f02a0070640ca12040450342c0d5040103030103002448410b00c07a161040701a40c1c1c507481140014011400240400c00074401401001c03201907520340911f00490741225441c48407030f50b03035045803400d4034181c030401c0d030008074031055003007a00505071018190310341080b140f403511401041c2e1036200e00000303101e07940740d18003401c1d10340c3c0d004000c803031002186800300a07041c418240c46000300700548084239980981000509590f0040c4102a10640c02424900c200303000621441d0090002d211100d040c401c140b4000341b2920101191000c086440c1c0d12003485141d0b01400281420600806071140c40641800f0040c400801041c420112052820303c00c0301a1143c0344141e9 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 93236718 1250 93235468 93235529
    0xb04030e0a0e0a0b01031811060706060515070506070e1f050c011d070909110d0219080d120510031b08060405070f05010e0906090a0f1401030308060a060207 69
    0x2400b44560005014100286074080d60500c80300340c80400034034455003180d8060f4505c10034003415500d214100c441b090705200004001081c81004c2c00202d0a071514001030507003030b140901d45140070020520204005003080310f03d811003501e09101101c2141140041c9000d466006440010300c0510381c00050180030304180d8988540c548020700015801c440c00c801340c4030180e0140600d40c130a4482c0000e030010383d0710070b00d407086820600c071080300142075083c0301c4d1040900304200c0e00300740c1d4114849030010304180528060080e8401802c500344524100030401c1d40d06850f8040c82e50315100a2102410046031840200ea50059401038103078248480c00880c251507074031081c05405003034100410440c01084070f40588030000206150f050311b5200441d00340c0101500240c07c90000c00114480f4070f0000002903011505200105d62058000440780507140080007041100c244940103008050b0403021180d0320010075a0301c001a02c1c5094802540c4025a21034840c0c0d01ca09a840d1866131104500c0c1030303 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 93237968 1250 93236718 93236729
    0x501050c06191d06060a060906080f0c040306050709050411040f03120e180603070f0e060d06061208090f0102011103040813120f060e06060f040e030d091a01120b04030e0a 75
    0x14002000c00381c01607854010403103880b4406c08082e000850316034003a46c4841c007038883d41d581e0b055036030b0341c0c0104008000f17002400412100d002031100000044e80d42c02070a01c9a105030f81c0c0c83e401c0070310704000d010544a81d0089500c05c00014041482603c1060f00704504070703500080210f00f0600c00c4030060341c0003940d01406c0ba40021142c0d41823510b1240030b554040c00b4100507001c59031443c2e500ca13484101b03042e0034080c0c012003070508804500c051030240c0f0720b60080707800791350300140751552805410090468210121380b04880480c3d00134451078181d210400d140000e00003403100607000402c001461100030001007484d8404200100402d86940560026110713294101c1ca08000900740380d0305903224280d0407500d0504240e25090a510f0100f28140a0074000e4003403000340c0400002c01c00500154803010f8803c0c0b10922400b020000140600c150950281d096001d0b01070b1000c00741d80b244841600210b41c40780c0140700c460300081e081315109903c250145003051851f01c100703000580e400c0182d800b5 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 93239218 1250 93237968 93238001
    0x316081803011409191707051507032703090b0c0a06020d09020f0f010906050f0c01091a07022b050904090303020d0e0a0f03030e1009110a0501050c0619 67
    0x600e0f800101420a0a000c0e03040c0d0b4003194060444240035448800c100d0780d0003003030f403d0358021304000013910300003500010303200c0d40542e048512010858400c9003001c840c0d042c0000d4039423202040c3e01500815440c1c0d030a182282491081403a034a014100b4042ca00c01d1007419180000e1489031a44284000c81d410b40e80010190b640c1c54032a81500040c01c070403a41030780f0480d14920741c030f941031411040b4189440c50685030040310038941042a68260000020340782030800800c03071000e1003e0f0a2090104040c07003401c03155506107801354001c3c1a00d40007001c0b003040d5030001040300ca14408492041011000350208101881c0003e14116001d021706500d03150481d0514420784101505500075100602c44600e041040980c1242003c0c1d980466030005031080342e0800010740030030b1180d0000c1e080340c030300101102c0e50711450110103012900704060a50360f140c074101d83c2070002d1500c0100a0020402440c2407814103185000654a866014141c40b22a013008a0402d91182450700000040004043ca = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 93240468 1250 93239218 93239231
    0x200a0c05150705031206040e0f0d030203060f0d1b0803030118020703050702040203070305181f180b07030c08070903050309040c02160909060606080906070804030513060f0e03031608180301 83
    0x1754002481d4044d20784600c0385080c660342c2156940300007042c040030318060008080c542802c500640c000d51000d00a00d804c044d440c0b50001e891303203e001c0b005a00d6845511a10300c00052000780d2000c91865802c0420341790000c0004006411007454035941c040c420140050383c50199140c01d5a10340b084490003900b141c008810040401e80540c4118410301e1010210020300e401104074035107800303c40480c404074040454184140105961180c1c5103030407450030741071280482c2c1d121203c03102d000701c0b11500042d4840010310b0500b80d019070318940204050030400320345400c5039500d07906c90180d004d5990003540e5640001c25120f1082050445000022581071701d4035441e03241c240080c0ca0040011344042d41082c60008000b4440c81001d44280e030164040c041076241c00c98103c0345400e000d0070a0b0100301040c083e4008119480700407030000c00c50794440e107410180c50b003c05428141004d51030713403182c0c00c1406405010b03688001d800c030025034026041980c601103c404400041e40103445140c1540c41c190 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 93241718 1250 93240468 93240487
    0x20d0c050a030b030c031e0106030807240504030c0b0a15060504090501050607020612151e12060402010801140103110706050417030603070510120c200a0c0515070503 73
    0x5005000c0c025240d034081c043d20902c0340c2807503654102400d80a805900c801c0300002d0348085443c40c951860400400840d4850f41e90301c0342c5515070411582512108050b801c900e014162800d61512541e1201c1014040c070325150b1000b030108a910900580340f513003040300007a00400f0551100052410b0911180110758513500001c0c10364200303019460b03c00340b0340400810940fa2110566142d964000c0882e803401d4805401c40207076500c05030540c400189064407245490340c1e10050303413102c035020044440440c090301040140f0300c0700a241d14031154110005100150f43e00440003819640311580c40d4102c1d45071080101c00a01c1e030009001c0c2d400c000400c55104204071030304014000e44c00740342504070a0b10421419407081c48241c0d40c0310750592169000700000d0501902002d40808d1b03504000c12049100c4c045401a522182e46690000d10800c1103e1080081500b420745071034440070003801c1c200c2e00b035504c0c41d20540b8240103c078461041c0402d00c0c8054214007049800030f992140036283c980583c030 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 93242968 1250 93241718 93241727
    0x100c0501020712020c0a06030e030301030201050a0c050304060c30260405060103030305060306190b2206030b011d13021c150f0e0d0305071115011e0522020d0c 70
    0x4440c0184100d240400c000347e01c4e03200b4003652005082150103546540d1865005483c1640040b80750301c144031600e100540403034000c0c03010b000100959112055182504d103014495000c00002c01d0184805102d85800c20443c40d403031160882a89007010a003420b4607081e2800050044c000703d501c6042400e0401c010000080740960403a4426103042c010b03620380710205034488000b10b84184440040d000f100102c0042c5400c81501c0381006404081200d9001100b1031000302041142405a5101d40e4100704002c00541460300500040038030714a200600040150840c0c0c0c05000c4500c10013103488010107654131000c60703140c41003807160075107038090b081d25208040108400d20244107034642000c1c580c00c866203000e94119940800c0c05404800c800c1c940940040402401582c104208240c2616801c0300803c1443d60910180d15040c0180d0b1415000030180b04210f41d0404c01241400c8080255460340b95410000480c4040f00d2241c6004192204009010b6800c00c05e11542c24034100d0358a00d03400 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 93244218 1250 93242968 93242983
    0x190e0d1107080a15020304060b04061401020c1c020906030f010219030b01020601030804090c0c02060a0504030c090204050307120305160303050402030606040e0c0f060c060109060501080f06100c050102071202 91
    0x65000340d50150795a50ba8040e2500a480b07405461a00d42215007224841c659006603070291140ca40000d07d0501c40d0003260844c0c5a07030300400710846031900002d4107983c0403c8500103580c411100301b14001c420940c0d03c0500c1c507812000034003501004010420310369060001e800d40613a110000c54076680c542c2c4440100d8140c007808103000c68540030030000d041d44040358403416684c001551178a00752601c1d0070b440040c01d9603001c0c10100085080c0680069031030b4801018100001da40d295220b070704504010002034110341c4040110791042104003e1510b0200d00308044844402e051a450402801e0030344441c450740c59203c500003e501022010103805512040c089d41c000c0e000c841982d40d4074010301044401c000c2d100403da5000d15455203003850400c003500c89240010b44180c0c1800d00c9880b4003031134810700fa0481d625440d03c1c1e020601c00c0b544e00849041e8400e0352500080c0745818045c0c0404c064030303801b06641c020000c02650320024064250100c5221503407000e000710524200d9500207450b8901e = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 93245468 1250 93244218 93244247
    0xd02122407080f0c070f210318050a0602031308030405060f0901090c090c050408010e0c03010c0c03050906031003050604030809100603051c0c21020705041103190e0d 73
    0x5003a000c00e41103482050030340d116284110010342c1c15256802c0c40740454100d1201211001d4103a5008000036140c2c08404048850b920079048140c100380c003004c0c040c0c4020423040e410f840614070740100030481c00940c03540c090f41c00820041e941e4652084500400321003181c040c1402c00c1c000207200400400145d1644107140310008004035446500146c2c1c2030b02c41040c005400348848010a00420311243c0c4285502c0003282800707460280d4903140c080c251007030b80002c03400303a820005403a905802c080c001c42d404100e03e4600049401e6566a001d0038900030080b000d401020040000341000700315450310f82c007440d0000101d81c401d1a1902d40149460f50464401c10319003d9040034a58411160203000c1c00e480c1c1c0440506180507190700c4004603046106840420056101d44000200300d0004407054400155040c01c900301132004400b901e440640c0d8816405540350202d070118880300d081c10360760003c420f00d4054000c40c0d0740c8207a1001800c401e0100d14031900400091000da5500b10b01640e07652407 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 93246718 1250 93245468 93245533
    0x12031305040501060c06050a18060f0b010f020a030503060109030f0807060b060315010c02040f0203180d08101202030c190f150801060f021603030507060f05010807050d0212 76
    0xe03165414001070307034400e11900f40071680a10440340054247d41106a000240d4400051000c5100c916030440088196041c1c80a981d2000d8403100710340c3c1406030101c001001c1c28400d207290b501c16002507591445000141c2007140120100e0426889500010003c680007404840107080c24102561140c0c8505001c5400e00e02d17242c4806114180300e01524850024000b0202d140144071005540d5807032102001c0ba4803940d900950241c0440c10303c05507014009030004411881000702815180101d0b1790258070500241e1810489074908841105040e01d80030707024004e00103d184040f0b0f01c0e012403041c90310f40c8060081c3c9014000c1c903804507250121106680c0c0074820a9640e5000c0503140340311824a070000d80008010b00240c0e0190700300742c01400c1c8500c1282d80c140e5241003080b03101031a80d001100000d0001800b030081c02140e01541da959071410108210951410082076611060352003158000c41554030325409541e1200c180027441e482d004162014201034141440c00e01205051983c0c1c0c88 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 93247968 1250 93246718 93246757
    0x30b072a12020d111b060f03090703031112040501030c17091609110708070314070501050103020112020c0c010e0604260d02190b191b02010c0c050309060d0b1203 71
    0x10b02c10303d109000f44d030700c0501030a51580c0c0b0f42d00c07001d40c150701c5e0100c09400400402210101c20400303001140300780700301700190110a09501c0d0003024200c00c09180c1c03100d940007210300da1506c164901240d00b00c480034200000e072500b140c40d094501c140d07901c0c0d080840030f0450080101c0c2070340c0070444078410b01c407100107034250b2925203205038221907030032811040c0c0041c00d10514002030303100001001030310700a050100c683d1110b00b480c03406da5413000108a507183d4440e8010801c558100c44140c1d0b152421110541c141004004200e41d1956004e04c41410003804500796003464880c4002c80c1c1c06040929100001eaa00003103450104102e822010001b48c8582c1c0e00002c96140b002c6200c007108445079418032403c08852700c0e981d04040000e8254034004100d24031806071241c0611403203100000d80b071002000e1401c074900290071110307940420f0050140500b800340000e600402118550302c41100c0468803161415003800003041c0c02882d40d0741204200110242c000d9002011300711164000c080c46164 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 93249218 1250 93247968 93247993
    0x4020a0905130c0e0303130b160f030201140f0f1302190303020c090714030a0f1401080a0c0f051003090f2907180b0702370f030b072a1202 61
    0x59210f02c0c02203441201f1002c10070301001d02c0d407000030990041440501038800e400d80e1100020602c02ca00d08501503075541d0824008412440c0402d54884010300d02c0d00882d02e810380e00000d00c610000c0c0b00980c2c40b08a01d90b00740865403440700071303901c801080141600280d100c0c60065543c0f1507690341584a224000005000588580c01648201880c04001800c54031249828006010404448041c1903100c0c0580c81d010506002c5c12402400d01000400352481c1c1f5003442e6110120725044554450f800707083c00d000f2500c3d00e4804803a075060f07902e0002101351807403d1401c500300c03a002008241324483c10405243e400c03030a900000c07562003014404c1c0c80c0d031241e1105540da04915107804100c404601420420702a000c0d000e050001c2c00503220701c0c1c0e00c10410302e81c55a44840e48558200c18400380750194510118828600094404071440c1185941542c4561952000c0101480100a500758075110048a240941d00c50038250740010381c0100201d00e4844a0060402c0044005102d41c51040c0321 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 93250468 1250 93249218 93249223
    0x1206091a09061207030b100504090309141807140705100914030a020a110103140a050a06050103050c040302040207020a08061311011704141207050c0306091b04020a0905130c0e03 78
    0x455400c10f400a101c500d02d141d4540d4071a80006040d00c011f0780503644009129115030144542e614401c1d0788401c45a410200030744241500b041045008000c9410b99142e409200c103941c035004070542c00d0110310701c8291046600c0c14803c9020050590090008210b03840300690494005544952000c0b9075030b80b841c1c80d00b40c1d62406810101e40040e480142280c0c003041042d21846c00381c43c018903021a94403680c0b81d105039600e07400d4601d101d80c00e954008100d030006840c401c0f0f60181000746024401c070f007020402c10303419015030700019214540c0044c00508543c1c404074070b40e00034a04034056905034903000034005411904404240c0c0d80c54422070000500d58804d1621001d0f909464030010001c0d1074035220011400d000d02c0307505110780b20b10710b031018081c008079000e0541a0b100d10020505010084c05060621101a1546060394080c0381c6100d40860f813000d040c1000501510016140c60b0f102100300d6001e80c45a10030340d005807071548084405a85034102000e4050a070f260283c09009013001e00d607 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 93251718 1250 93250468 93250489
    0x20307140a1a041206090605070e010801060c08030105060f04050d0305040f090506090f0c090a170706020105010501020618030d0207081e03090c0105070c03050f0f01060e060a03031206091a0906 85
    0x80442c104000d1040c1d8a40c000d01415150040c41d0004110100e6a02e003800c440007030303d4250110340030301c0700452150781c004d0140c1c3c0980040c3c5012080864565603624441c0810b001c3e00d4842c5001061842280c600306c41518001d080050003164041414140600b69a02a010b28403c44181a8020480040c80e0050700e014007000303813040201b81c4d278002c2c03084d03109040a000c40c8801182041002d50300d0390ba10140f0b0300a401424403101b0f13107003541c0c0041c51804060b9030108080d6410000104070701d03a0040f03500c6034010080c02d42c04c032884032000769103800c510600d110364035880d00c08210002803000100140240e44d104240c0c108a03001d80441f800c1480c00221200a80c1d41d00540d01101594030a102030305080d0b12036101103c90507244d6580c54103252200c5840c420960049141e44c500240134090f10380245006400814141011008284c29141031300028050143d1610052114800ca6000100070100e00e9000c0121180140007610b0540c0003c1e44948903040c8000803841e980b4000c1c0300d98 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 93252968 1250 93251718 93251759
    0xe011401090b0714030d020a0e04090b0606030c04080d0302030115020a0c0506090a0906090207031d150309150108031804050c07060e03070501050f060901120203120306030a020307140a 81
    0x481c91520000104690150ba02107401108140c101d1945060800c040c06a01e006c66001584688203068000c01c1c0150010000f4441c41c10120545c02040000c4080798200c441030303c1c001c1c0c0c0c070f60307415200711422310950b4464400f51144002d8440e4550703143e8090b505940986200d84910311141038102e9443c020342c1c0c80a030058050120811207450400001c00ca100c00150010100c00d540b034040c0000c031041c9074000c075490b40d000190f4408040d805a0b0350541e20b070326043e10041d255180401b250807184e643d05918540000000400c81e42c0d4020072220011610b481c0c1201190341c4c4600c0126182d400101300c48406c461840200b07012864075001d11482919a048418100411529600003030800d0380010911404108505404580280501885107802d49021981410b00c1401c3c8101548141d00451104090006460060380c01244400b003211302c00c08415200d4a918000904003454544001d5051160140001d11a41505000b0302404070458000700040d540d000c1c40c60b600450695075 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 93254218 1250 93252968 93252977
    0xa02060f090a0204020c0601050f0a0f030f2109081228090803030103110306131a150303070c0f0501080106090306090302030405090a05040215160b13060203100e011401 74
    0xda064403211402680c046804000c49060000c00d0300801d00300c2c0e10500200c1000d0708804010300403801c0848801904075416600c00b0070740c81c648020007142d000c6501000340300d04c4034150300100380181010b404925a15046400d0b01c0b449103100042e000d03881c1c6100b84c0b0b00502a4a403040150035000c0107807190118a15509170403482d204400b41d684050300600300044c44408140454200b004001a41c041d5115903e030a24241381c1c24101440c04100404155400d185501d10713500041c2032200001151605100c0001a0f4444220602486202d0502e03681c1501c004181202404405410002200d905550342c00c41c0c02e84860045402c40e90902440c0d020a018880400000e0700d02d610000e20940a441682d06050311500064080a401d55000c0503807502c0e6001e01040d480c003c1095038282010450b41850248804a5202c170401c8480340604010b0919001030201c910700c00862048e00d511590031980d0349004155000c00d070300d00c1c2c080d40114501040012625100180320001d410005031074 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 93255468 1250 93254218 93254221
    0x15010e01080a0204030506181204030f03051810050a09080c09130606050a0f090c02010507140d0e030304030c05070b0307050d0b01020c0307090501090c0839040906060e060a0206 78
    0x1960796030405040d42a40d940c1c02c01000000c41c0c4144052401082105080140f010544200c24030f4120803c206004001041004000040307400ba504030a880d454148640c803103040300c6401d0885800e0942e03e64020b90202e4070b1001c41641302000b440ca061003500c50000040e1181c3d03000742d42d4403400210b42d80041012004c5148012400c2c450343c00d9074460a00440e0140c0c503680403d00c0100f503075006583c1505450014030401c42d95001708507251106100130482c0d480d114800074003003202d6031484110020f00040c02d605e440c00c689c2000310216401c0e011241d890610b441c009060086e0034505451500a8a60220b40b12413044104ca01481066958074102007012041380000d01021940d50306620071010810306948003880035200910315480000b915616148503101600c1c00440307c1800c00141004001020210304040110245200000c0404040d002c002c1c1404194803900100900c00c0400c00040300a4240c12000540d002650f44400a213541f00500500d802806c40d4040503030080b80 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 93256718 1250 93255468 93255497
    0x6110312060609131406180f04140c030304030c050f0d0b0c210403030c181d090a020d050102040302150906090f0604151d01020c1c03170a0f051501 65
    0x10180068603001040f020020074444c003a2412109000e03190345441c00800200206460454002c9691055988240034a4981003543c44412000200f004013094403004611130401c0f81007104452803080502140d9072a0346900789000d90309040c3c81254032665161186088030305200c2000e448581d88020070710425144d90000c09d40765041202c0d084a051415020036400111800a1501a500a80340010708000720750700200514103002006075441844003080003845001c01c41a01c074209400800046a140d0101031418a0340301c0102a5204140c00d8841051101c10b500070002c4070300c01c484e80d03500b16815a0484c10640645d14042d54000710511103040503082c00c03c83e50f958607034000c00c0d03140740036143c0e031002045582000079900002d400c6a90a004805c0d241800f10095000b4001032008280445c0011901c5e4004218104a04201c5814201301401100000f6080101e8a8007000900c0c000001f90018010356200e51055810700340480c0d03c41e11600f030350020380e0006940d00e10b43c0040d500d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 93257968 1250 93256718 93256729
    0x6140a0e0a091a13150b010c0201080c0c1e07050102010605060f070303090210050c0708151909021003050a14040b0a090503071a06031c020304050d140a03090611031206 74
    0x1844140c034020300c1250498903d042e0044114811181401400c514410030300f0490b130200d080c3d08004e0a400d00e800110900c0303a030806141c0b14181e90901e031070b40c0c850fa5009039032091070055141c0413006110b00c0b00040d00c90803051113950302c0006050200e500d0030365900012030030b860107880740e541c101e40c0410141c00f103640c104009002e030b20301904021403110b41c145c2c003280e61060560003100003d031020668025020040c082403005001c1c0e034005203529180080302c00742e00c01c4c0103001c4000d810403a10081c862101503401c850038041d00140800f041c00c0c00c1034405405028100c51451a4a1619140b5840c3c800c800720518010354101e8848500c5584423411000100381d000c4c0c080d51940f2052207200005202a41005900030b42d0b2001c3e0301182c204481810b15107040032010803100a000088001c195500106460403100300300c400d024075004c10705004418604e45240c042c2c0500071100e111044c950404030010440d1082d41d00c2e0700c2042101c0c080726440e4010780384c10000d00d882000100303190b071401 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 93259218 1250 93257968 93257981
    0x80c0f07050307020a0e0a0c0804020312090102150a050a05010e041101050307020a0c0308130e090a11010c050604050d0e01050a02030d050c040503030a0801091104080d0809010e0106080106140a0e0a 87
    0x28400326860010301390001052000140c1c8440c110044007002c020481e07049001d210190b1103d800d08202c1030400d64000ba8460324219611a412580450000c5044e8420070005944207036101e9024054108401c10201406084070548104c509050001501d0321413440a544101c0c0c1094800e120032810400442b45a800940148114441c07032400c1c00100d0000d20f8010f005503c2004d515590f504003903c0000688110740c8010784102c4070f8010000c402a02180500005a106e03a21051460407200140c90350591410f015009114031000c2000f0481300041d15140c0c802c80d503d86465600c690300044030140304403007030070006030800d00a03030201c080a0741005800903008034a01e0b0034152110301107403a50300700001d5800000c082c02e0042018159602c00c0061000d4900349052411342031140d4940d0300c22900b0012820040502d0000740400c1c82940203030b2803120490300a0040c2c0d43c1d08c0c81c1081c0a4001d5005404199140305a00c000614082411200f202c0c210b0b4019a20307951011206401040c1 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 93260468 1250 93259218 93259223
    0x8061c05030f0d09050d020a0201091818080307030b06090a091517070609050108010b04030803130b0703060509060a0602060f1e07030207060506030a05030405100c140319080c0f07 79
    0x400c0c03103692045540b1101a25995074065030003d031842e00d43c24070a02e449040d040b20025504061690f4000d40da0002d4020103582550681025920490121000500301c2d58141c1010303031442c810800812032400c00844c003404a039902071140607240020080c080c480e4445c00d99120700380c00000c01c50040725401c0a540d07000b0314411030380304965603400d501d07a042503203540700500d4100003018066660801040000340600b03280044030356041a05e00700707680c031980c0006041510003000040084806900c141030965128000d50660b0604100103405402c43d4001c0da8031400740d240c00200182001010381040326610f03030007000305464000301441c40300405481446001415103803a0140859502058003606aa940041c2d03510030034240081140c00c081c0c181c070702c01d0300a00556400300710000305841c00d407601110311941c05907145400f41c0354800d0021005040500c0e056408816141c044050113161169000c0c5542e056208002101d80c3c19040340d0104800d807040c03000041080014020740480c0d417 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 93261718 1250 93260468 93260473
    0x420010e0618041416110c131e1509141e040203120703090501080106020a120807090f0f24020a08070212030c07090605010e0306011202040b060304030e04060608061c05 74
    0x102c08650004d1040300c201e62103000141c07034070008916035900003410114124500080e020071480c5a0005600c2804514000c280756111a43c0c04404202902d074000d00c1d4a0034001002000da1307427550782500000911403207034210325110b03c6070b203400c0340c0c9840c1500c00c0304124415400407201410441441d2405082640c0500c5141442d00515005000810700a8004e446405a8030310700000101401b80c160002c04c11074001001d2080040c1110021480d440c0d1181000612641d600e2000c50314008030b1790108400b540e041c07000040143d00e08607040161010140f03221039044440c41007184074110203040d440140c1c000504480802c00c0070019003a000c0c030081010000d80043c00700540385410908a0003065000b08008000b4a0200e115450081c042820080c1c089588070300041c0e05c44505205440c2880c1c0c2c0082c243d0b086640c1d0394010906950300916554403401c050800030646400382c04072a0040340f604c00040303065130158507100e108980091008000c0c0d0341c900101051095804421140c52 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 93262968 1250 93261718 93261731
    0x6030a0c090e0703060302190617060301020d0207060f0606080408040b1c050702060711010606050f030405070312050706061a0301090c030b09090a06110a080106180e0420010e061804 80
    0x5500402c00d2405824030f0f503004108075040d80104041110124821710265404800400809801002e10b505010203040f41000b1540e808001c070b270191180001d401e580f2440024100b0410140381d21181100c82600020011035490350310030f0702e0129041e94041c2c100740c004d1004103c4418000003c1c01c421a1001109540844400710383c001e030345050740c1e80c50160304040c00b0001c045901801c01c1000310000d200034002145440d601804610490350690020400000020280305003005018019540030425401e84240c51000501e079801c00d003400c86d00c06007040c1e40010b0054000c0003281400510302d20b590320316464101074100801e10098100185615a011a002c4c0d41c3c4400d00340d40321b510008058280101c0d14501801102c00b0030641e007800c1c050600212403550352012030a415030301242407006080790140c500112007290b40d80820b0544088900300300c10040c0088100d41005024100303000680e422800644511015101494010005021b034100c1010074150748003140402401c0010315 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 93264218 1250 93262968 93262979
    0xa0e01060801110f180a0b0702030c0d080a0e0f06040311011e0207120f05070308090312040f0e040320160503030c101802030a0b090f06010e010303120b041d01180206030a0c09 77
    0x1107a0384c1d10030111f501e0b01150240650a0502141d2076a403011500413010403403590340c0401a0040ca0300050400c800908508a00c0c0c8910781b41040c002c00c003c01041c4c0341d42d42d03071030304221045510f0400341c0002d481030801c114804100c030207440702200300e0300030341000c504048141030a004a80015138070b1400e04616040425004e104c004c0145009000969903244000300341441d0550381c03100400d402000704000c0000801d00390b001c0b415100c00c2c60407001c031a2158241100c4c900e407040c0e4002e40101d01c041c03d11800b101d0009141d00a0b071105940700200b159a0307410036840340540f042c4001c59801c04a000b450742191a408918000300c01c0200550400640d00440d140c075182140481e10102c1e5242031140320750003001981003c8071720034024851981080a400c00d405070611000b81400020b500092444000e0382108070400c101520030051801d11440d000c441c440012541c1035035510300b01d07102140d504101d09081ca241d13005031103540f07152501d020040042c8002c542d00b004100380300802284 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 93265468 1250 93264218 93264229
    0x140136021305090618060603060105210103020109060309051b031e01150801090201050406122003040213150618090603030507050607021906020a170a0e01060801110f18 74
    0x20212140c400041c0e0007810101400384001018048500c5401c0582c00280c1c0b800c0403c0030658886816640da545075141e14006a8050181001c40402407284e21118117440c10900c10380ca0480e03000360f94070585250758444c20340469022200150041e0071641600366945000a407601e6000c1e40034040324600b0351200e500c1009000ca4403620441c59441e403c034445504803101042014181c004000c005a038640c0c0d0000e0300900c9148102014481e00c1c032909911040300e68440d82c1030300980c40300172000c9120940c0107142c2c0c5e802158101e00c207402020b8008001103251081541d01400d549060a050b800c0c542c050303d4a000c1140b0680c0800d841c810013017a018a83d0040c0320055100e41c990b507454a141d49001402d2100007804102158006611144400c072408080810243c1040005a40c0c3c0c01004080f10903101510604d141e0300070f030500340004185154810350040d440310008020054940c1c8400e0b00b038410062410351410424000106504070301d80040003020010400c0390102e801d1000420b0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 93266718 1250 93265468 93265477
    0x117100c0201020c0f010e0706300501060206130201020c0d140d0504080d08061305090307050706020f1b0f06030907120f03030b01170c090103020d0905030c0114013602 74
    0x80060f5004207540042080800c01000c440f0342c000000d003c40c0d07500e0018a0b41d501d00302d100300c20801010340301e245084880741c2c2001d042441d0480061004500015902c80076090030701c61940144520000155943d01c00e2894000d490381c141e01070158001d0300800c00c124000d10403400d03143c80c050440340d82c0d0490020016a040044240c0766151124030345003406081040ca14008802d00903000e0800078103035544407032100b200d0f508800004264482210051541c01000d03030007002407007405404242d49400103a0790784807030304000c202c8449101c40030780c0345160080700270311640200d05a00c0791861031070100065540590004110b40401da6078840d4000c0c0030305650380c15160350700400040c80a0543c1030291581e502c400382040b421980d103042c0c00c40d8400070f00400790070496202181c01d15140e031182d011686615507c2c44d091218242354104076881e58845044020198600224543c160900d1960141260158400c580090b034054001041d90340180d18102104038100c01c01c1c80d0003c8043c400b80 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 93267968 1250 93266718 93266741
    0x120a060c08010e04030207180f09110f0f030c0f0f0a030c030b0c0306130c050903030a030b0f150f03060a03080d0f0b030105010b160804030606030b0403020c0409030503011710 77
    0x3040403a0880c00c09000708030180c0015200d80090810040800c3e00003c0480883e102c3e509984040b00390001c6210040402100340800c03103007001c40316018002480e103581c00000c1d007140c40064440800c0100540c49100d448200e070190480a5000050b2405504584031460060441c00c5805a2040020303034003002a0001c0380c048104603014820700c1054031136154410048040e251a44c20040000360640e181c84d100000525121114820b8181c412420b8949004001c0c085039103603048840c02501800c40d905200380910401400070109141461207a051a0b0320300344803c0c0b80c0b41c034951008906500c0280002d4005401d0b2000100061280000b004901c82c103800001d040d440109500c1c3c2542e503403c0d0000d110360304120052040003404070484040081849041c0f8500b940e5107400030803402070344d001802c2546040400002c1c440514a114441c074800d03400e031002c1c540400100800c9500260b000760000c1c2c070600060200c000750a064500b80d54180e0202c0324044001c0c000b21060300d81c1d10030300 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 93269218 1250 93267968 93267971
    0x7020904030f12020304021f090806130302151302010c060204180209040513020604060f140307170f0f0f0c07060914011505060f031003050106030503270907030b120a06 74
    0xa0300c0c41c055002d0050b064003c003680e029451170038640c0004028a090081e045102050b0b00340043d03a0b1802103101d50010300980007900c045146c00d00261140c00102c2006501501940c4060494490a030190320300c54081d803008001410301a030011661602580e0b4220f452590800c804901f100c2d0810074a816088403040160741c40d00c40c0b100b40000e03140b0240100f00302880040040c001a60fa09050300d096601900e45070185c00b00e001c07011103400e02820710306052080f00205002565500c010b600107030960004115410f91030b15928102c200c541283e0442642c24860003156081c050403041e15041180c2c0c520346800d050560b1103034422100d000b1002c80b1501651f82c6a480340900a002e569540290340e0300050740e240c030f880701140141c41601c240303941d040c10000002da0f01ba800c0c005410302440d0090001c000b2203842c1d00c1c00550340d074000f100b201c174038009540c3d0b11100d02405e0f280000c02c044000d4014145034036149810b401924040d94003ea0000a407041001400b40801c5030701c40c8540103d20 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 93270468 1250 93269218 93269237
    0x20c030c1b040e01021201090506030717060403090b0c06010504020f1c0b0a0501171602010603050a0b15100e0d03090902120a060806060603040b0405160905150105040f050d02060702090403 83
    0x2040110f48081400d6002640144400c1c608038455820044c1111501c9001044503a984c00c0000e043c000c1765003040300340c011b6200500c164640b00045a500c03481c0319494075000c0360344405010003103014a600f5280540d00400040c0201d0030650003400e01440d04c0c1c11200d050401d10242440094841500c03216079560f142c828130079910b44020380000038031003800c010035103100b03c80d03608404560040c00761100784419040c10145030320035441038008541103400e0307904101080c03500510508040d242c18440200382c0039000303000e02d0001d95041c15039485403202d90419070400240302588094041c2641440f001903000140500d042c00107201d102d4400b1f01079000c0380740c1041c0090407500c890f0454003544e48490104441901c8000440c1d8204ea0400151000d5566900c1d005140c00a101c0d5849807442c0c901000040d480d0480d040b82c1d00401c014000b801f50305140744011203407402684140c80c442c0900500811041c101200390f64141d0340060300c2145044180c0c1c0104086c010b0903902100058074020307 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 93271718 1250 93270468 93270523
    0x501090e100c090608061507050a030e0411040603050a0b060f13120206040b0304170d0e010506091b2508070c1a030f0a090203010c0e0a05030303010315020c030c 71
    0x8207a50718050011400c0012040d0210000d28001c0c3d42d000d25418001a600441c1042e80c41801e103100481c0c1a284aa40d00c071200d151003600c94005440032030100c0c2c0c0620503040203150500030380c621894081702c0f0310b0500703282c01d01c1280605400340c03500621503921601d442c0e4030f0300ca40004200d030204021900e90b039052028001c4541481c075500c00c400520707043c100100140c2d0307140d084030100d038a03201e03400b502ea482e10f0520002c02d46001400d4a0703040d00018a040e506406030300070140058a2800030462a980c0c2014416504000c480000a403041c0300d1800c070020749450302800d41000c00e0144000b800c1c060705d08691521848407002c1d2181c0c0d01c0450706400b0043d459454802a00350013605203911080008102a03d001c00f03405520b09400010000760001c03120382c882a0381da50010300030301400c16100009083d25007038040d054000d521030f03030020505060010499048075404a113001200010181e09002504810400201c1d80010007005042c403d0030031201c00541182e520341c0c0107254228 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 93272968 1250 93271718 93271723
    0xf0c031202120301140d02120a1b0806090c060a090f030804080f0f1002070602070206031302010f0f021932160b0315040e01020f03060906010c02030a0f0804090501090e 74
    0x5601d1558003450410041c0400c0100070b4640b085c22000792010800e410552000070048031008004040303d100b901d51060500c0108441c0843c100c591043c0c101c4a0f988581c905034a581089503603e0b40c40e84401c02e070341e816080890061241d042545000342455444810850300b503e0903920540707148202140030300c6128014480d2220301c40304080103090340c1d524450215100c926004030451613070f60220700e04082c40007680449600c954002c00030382d03481c98031041701c181e8413003411030590000d400244d0500c65140a01c0244034442801c0d0010414005000021000790604d200308890000f6010181500400c2c1103a00c46c500000e100f43d19444418050400b520749030403da4a54001c01c00c14004000e0704040e502202d070000350b144880855224880c0200c0c02610f0703807044040382903100040d1940d603124008040c601400e0304558800c1e00e41c440000440e1807420081010354181c001c2802c80c0005030030103550100c0c040c400d961075420107a4a195010490b1800d13809400d000ea214003400050321400d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 93274218 1250 93272968 93272983
    0xb04061d01080a05070312020c040c0c0302120a0507080319090507061d010c0303051003050304080d022109100c12030e0d08010612021806030a021c05040302030a0c0f0c031202 77
    0x5140080080d0001c1e511101c5d9114174074030000e40854000d040052170a403080c0a440d12040d006407040c0103000308101c0007403407800150740c2a001402034000b805034100011085400080d003565070729042402076201c02d4520360000c0c0c1280e0081c2000c44030034074498800e015124015010704080c1550600d0040301422504402e21415040e0240e500c1030341c0103a810401c0c038040c0b1a09450002200c4d95002c1c0340e031454110382c3d00081c115110100c2c3c0092010360000b6214101c4d1001c0c1c0c20b65581d254074110320860301002c80c1c942406214103000444031400e002c00918031403c0355160064080a00c0d8540b0011040940b0640c4002030311080d01901403482000304541300c105501d8014025803624400405d848209041040c00300c0d00000d440d00000d0040c820720043c0c10006100326a44c0c2016181c8000070351124100f082100b01500c40000138158034460503100e0340e0582c021354a01040c0590860300e4079251541100c0805100711000f0200b031450340e0f408007541c480e0840e0030200038450006482e0000 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 93275468 1250 93274218 93274229
    0x525080307021003090321060906080f1009020d0b01090c09060f0f0f090b042d031a040309080102070b0a110702030a02090702030c100f1a220b04061d01 67
    0xc10040c04005840e0404520200b403000d10b80000c026480385011903034116035802d06903e141c0b020503801d1040c4107540c0200d044920703040007000942e80d141803054039840701076020320290308900d0021300d1080168205644085c4010081c03009926241d4948440001c280c11030300c0e11a0350749443c0e100c400c0d0001240000f42c1918100740c102c40b44202d000805440310005500c00b000b40c0400b8081c0c420b0701607000500035241c1c120f00b4a84580e2a44c21441403010007031b14064001711710f44840070702c480c409001481903036007101041d8009896841c1e0303140000405003045040000c901c0c00041c1180d0207101520940344200100d1023641440700448094800050203240c1c1450208600e4005070b50004000a4055060314007190359519401d040e402c1d80100640640d003030003000b0389800c2d4500154424079080b0141c0c00308111014040490100c80028280c801d9005080c0310801c080d0030008441d4410302d0740c00350070081021300c414004501569040d83c48000740da080d904540200601d86030740d81c4d01400 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 93276718 1250 93275468 93275473
    0xe0a0f051c021e0a09231602030304120903062a030209030304180b121e030307050a0c111203090f090906011a04030c060f02010510050108150d052508 66
    0x4041c0c0002e60403c41641d180103009900000c002c2142d19015680c000601c0b04160812500c460b45400055a5840e80c4103101000d5034200002e0400603129030300482c000721b0358001c0d42541d0311903940f0242194400c1560f0280010540f0000005903103000d4000d4040c0008440a2120311801c01c1001810b41044420141401848100c80c1902c00209550403210f008602c5649141ca417201507000b42280d00d110b5810440d004654015000700141400700d8040f0b0310155900b14804000260300c0b03000170780d40240050410000c010000e40300e41c00031117a9a0080b14450264191000021207010304200c49410381d400105140c038541c41d00c2d0400040c1001c01b500c100d0082d14214030307816111300e41401100d07514180e10300468400440321094901842d130101941c00c0030f585466000e8141070225050034015820000012242c4010103407200842d03a060b1140c0107aa16049440d1000e28210b050103500030300da103001c030400300700b0403c401002c4041b195620516660384c80c00107256038885800c500310a6 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 93277968 1250 93276718 93276769
    0x50a240506100302090a1a121f0e0601121505030d090302090103020607080708280e0d030e04020d0f02130608040f0308060a05030307060e06150105070807030e0a0f05 73
    0x50311025a080410b0006107070040c2c1d1000d00000003100f00101e40c101c0b82501c10340c0c00446000c1c40080d4010220388422100c1302c0318942c0c9842c500b044080302200201015885c0d40010800340419031000740d005401410070900f5042c2040c003c0b01100c21301c4017040d0f404540c3c403104000380d080501c00341402c0c02240c645204050300b55008500aa1010320000340204400200031090181c0407042d21021544070303107030b556101d070740b144004203090b0b6046041d02449403441c0c4101c0c003140039100c0140d0b00c10000d0491004c0c20075584058411002841c00c85410540802c0880f007100143d101c0d90348a1108200e0058030307004100c2c982c85001c05150490403d201c0f124003030001141803042f4008403581c1c5413900c20480e58541000c503240315003035030140381c0520010425000b04071343c0e90803003820b9580d00c6c41118640c1e80e5440b07244d0324280d140802640840c0341005a440480c0d0014003c011203400b07814020818031050000c6541515a87d02034114002c0e00c8400b40701c0340c0f902012003c0c80c104000030031140d0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 93279218 1250 93277968 93277981
    0x10503070302090417040302030f030405010e0a0e060f0105191106010b120c070305040509040b19022d070b07080f0709060e0f0f03010f0204030c0b07050c0913050a2405 74
    0x40d00303000341001e850b244401603117264850940040310059680541642c8050344034811155480d000b50250901055142680c5e059504220244100700d625030b0040d40303450340b03d42d000d01c003003940c1c001611030401204004403d0a850050340d0340c071000c0c2003592030114452904941c581848410782000030545070811a41d2a650b00351480103801010300109945e58188a02c0c040d55140703d56440035804c042000300b004280103100c21441d02c038854107c4c029003c000c040c1c2d5800200d1084151006941c403808090070a207070505c007810110000000c41031841d00780340c0d40b240c1d10400000c031859000204003104201c016003903450b40c1900b1003914204564420304256015140303109202c1c0e000d0040b40d01800030140d90740d60b0903100c1c85000000c6d000700706104c40c00b800c00000e9440340c0801c0d91600394031000001c071103441780115880160030a02524440005404108060a002d05072544007000d1311601c4002c40c40c01d11400c0c1e41544070302c41a03801e900311918508507002d01d01e050314181902d450b041122 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 93280468 1250 93279218 93279229
    0x1801050a02090916050705011b030c0c1e030e03100504140303060109050f040f060906140111070603021b0303090c09060103090f260304150e0706120207210c0b010503070302 76
    0x101320030080940510a1085401207466010b1140041c201e0343c00c2c06440003451203030712011030360380c15103503418080015422400d0b00c10a07140d0703200400013000c850302c101c001c060000c2000c0001d17100c0c3c42d00f08196045600080d01c1c008203176a485030f6091751903040c841000a41041c103401101030801540c03d51408000203003030704d141c901c04c69000e45400c0c503030010555183d50100081c0300034a0420040c0c591030707180d0340004050902405100c50100c0e580c0070425030113900c0040e2100030500c014800282054801c5029404c0318001240c01000c03d050718400010034030180d03100d00346d040010300c0514260801c125450384041c208034140b5141000300804500d0808089910325009600454540044002000045150703440c0032034414010050104201c507075040a403c00f00001014000040c444141e1511046107200b0300d4089100240d640708501815006001c1b643d01940007a000f800214030540c842c000a0f1039080c0019282601c180308005d01014201d014110950041140901f564003058 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 93281718 1250 93280468 93280471
    0xc031d06010909031b1202100204030809040f1d010203150405040f02010815041505030f010203010e150303120109020705070902040b0a030f0e0a0c030c0614070201050a09030602031801050a020909 86
    0x480c0d8980343d0320500180340c00b03507507501254800a06040780041c030600384115902e0f2040c0c80f900043c0914200000c410905000b545c0640c0d401c52280e40c82e01c2600c8080000030486100b10200181c0c075200400090791480c0c002c80141100c0c4400036960b454070300152201c82c4055601184543c0c40c0100b800b01240702d15070042d00b02a0b083c00e005409454508a9180440030140107075402800d2010301007a50002165000446a0642c2211191400c40700602c2c2030f40024065120301180c0c141c002240c21040c034001006003040501503d26219502c42040c0c0302c0c140076001600c9154001411208020041000d540204507401e400c50038a8100402c4200a00c0b40d010030300100f40c0c6950090444d018640d00014543c0c15032821980e0b0307440d46203000c00c4015464403094444880c00000000c5940c0910524900140001c503842d10300b01c001d500548040e00000d40c60800c001600704080000788141c40214050a121011143e807103454218045c2504d0005080f8100750b4014422501203883d0420300c0d9 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 93282968 1250 93281718 93281729
    0x1a030a020904060f06030c030b032b0306151e020a080d020d060b16051005090604080f0c07090e0705011805090403020a060c050405010e03030306030a2409060c031d0601 74
    0x96510040c550000b00641026048807080c42208240028100d4265100c00a406031a031030521282c0c0d100410543c40d80300200080e030b034000410f0740d0303a41c902c03100f03e24410080102b4140003c90076114034100044110051303504000c00c008000000403030384103020b44050780c0d290388001e0114042316074030400d5a008001562020340c1d00454003000c0f24440760070010185c1002c10070303a5200d1102203d141c040010320442515030b8081c0781001c03945406070b8090b01e40b04502e04001041c40d80c540c0c1d520040580d212480710030b000442403110814204050281c00b0007080085404030320f40168890481c10001c85600c00e90503c17a0281e00c050341c201000c01c0441c1111411110188180e030746040130390914240340c0000345440d00d82054040d896801030090020380380d080e41d41c0c01800d070300388062550340c1c48180d4000d40d00d0360060b40c0540000355600758920641000c45601600501c50794511003d40b0100c000884810343c0328030b50ba01c582035140c0304201d80100803804002d5140c0d96a9811501e41c241070142 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 93284218 1250 93282968 93282971
    0x1412100c0201020915120c0a140703050909090c0a06110601050d020a0e1f050d08030a0903031d010203180c06041a13030b0f01053a08221a030a 63
    0x40021207000b94140c412042001e0150a0601000500c80b103003980711801012102e4802c101098000e000300341914104044c6850710445100c100c3c0b841a81504280c1c001c90421401b0400030700345840300b501c0640680c1c5098024542a003004d4204146021146c01100c00c02040701c03194100040c0000d030803811070f02c0940316105194014008915021001c0d000001039445c0c0d003041c400c1d8a0700d50288003007040d175404005405161500200f048071880802c1c0603000840600c00314200480350b0344600341141c400e040025410b515400030b02e000005ea600c143e505a5400300c1082402002d445483e402030700b10101510307000181c8000104030740a10f00403401e50500c104c07089195041c00c50b0860306192645d0b506408c0e015601e00cbc01210001089500a072807030459400081c1c3c600707103284901410b54214140d00f058051408140050194012010401d114030f5125800480d03035800080c03200b6006c180c648100100035250103584000741d50320441c001c4400b00d60004000d0950000d582e00140345240 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 93285468 1250 93284218 93284231
    0x10c08030604020c0f0d0f020604020906040b130c0507050c03010501030b1b0904110a02011b12020708090915011b03020703031b20041d03090918010f0501141210 71
    0x702d0700a004072160b02c0181d108028202800c21000640a030440d280c640c0c403603895001040d0200c0e2600000e80d002500702601c003021038a5441c1c10b4100d202c944030f000e09030003000c2c4445c04200b82a6802e0691840c0496000200c035028094140031f418807841040c3c0c001c2c009545580e596000c0844004c0c540320020646460742c0c001e0403840340c11940300300b600030014495030880952440300c59100103104000340d842c240714040703403003c602d0b0703c90700c2041243c6640031060411001c00002c0c0d0b2040404845c9540c04001d0843e00380c1e501c45019004120020030400c1e407080510015110150044406190356900c9110700c00003980041d003201030320ba0601d42840d0203104240300c00a0740500305001403580001451480ca00c000c400403005d13a035102203030184403880422558044901c2c0511200039207402c02c001c4103686003000001e03680c000030780103010130003220310b42e0600d42100e141102a00007103440d000100140010007110030344400088440e4907001c1c4038548200c1d0b0b0703210540c00d8804901c0c0c2320344d03 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 93286718 1250 93285468 93285481
    0xb04030c060921110d050a020106050604121a041e291f0305031b03040e0c0703020c0906061206010e060d050f070507050a1b320f010c0803 61
    0x103118540c415801d0020725054070b0220409820030b6104000001261001118030744214a03030f09010703100c0005081040b400d400100c500d40d00c03d50540c800d564130b90b980040e0380d40300c0744000c000414003e441e0f21400d5216107411600340c030400b24100d080b80c41e514240008122000390382c02d00d6040c1110314030f038441e1161401d2040c03191442485100c0c17032b460508240f0280801c401c1c080c814188020403190340c00c840c0c05e4140c1808058000540f09a0080c428000e8080c011801081320981c039500300c0c1d05085e55080298008002207460300020200850a0810503404000840c40080c04039180403076440d0000210380d082c020f000800300c1035100721010503c90707402000e0012600c1005045a03554040070135500700942401eaa4450064a09900080442d8829402c0d12646076100016002c1c0034555101c2c10400c405400b1896000030007080009035000c444104404d01d9500d1b4642403c5403001d0203008526560744400c150b024a04060031440307643e03072282c0c011070310710f5000005586079110f04 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 93287968 1250 93286718 93286727
    0x50907080715051315030b03060105031c050d0e03030106052101060507020d020409050d05090117010b0f03220303050f0a05040b010510030207060c0c052a09190c08010911030408070b0403 82
    0xc0d80401c004401e0840750590740c5c0e6064200601142080d02240d00350390307030742041c196a10f02d0a80c44a07001071000c520a1200e41c4950300500c1d000e94908004280e1848060501e0308644c001e03804800824400a21003084060100c84056a003030300c03c1c9003110315850304030003514510842c14000d10401c3c0e1000b400c0c0440d55150301c804030154120f4100e170030380d0390b080e030014056511020300e403804220103568007840030020110701030684103401a4036003041204421613505400180c4440a440d20110401d200c2c64003c4182d5002c6502994001c5000d007011180e020629034041c0202e40c405040000304004282c0b480c55140c11154256002c3d641c00001c00c17000c400a00503040c0007404142031400e5070114030780c4000c071410824000c100b9a514000c0c2c1a462011312100c9028030140801800c1e40d0b0b40d250b14055401d00d602104000a24010034000364a10040715100c8810001007081440184442e1645211340034045900c030812500d1070405031a00903150041042c0244030206005c001010103118 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 93289218 1250 93287968 93288007
    0x206010504020f0c01090b100506030408070605040302070b0a080a110309070308090f0406090906061e060c0807050d0207081006080a110d0f0c0602010b060a082e080105090708071505 80
    0x260b00c0201b0280c540ca21381041203940c00d940060310081c00c0d00012899150801c00c4902480d8020f240c140340108617500c5101a0400920035000c0d40030b0b0f01d20024406150740c00816004245950b01c0c00d403450302c00100001c441c031a40708108508002d0080082c21000002d0040640380c00526081d1641d03884000140c860800140840d003007814284001486a82d50b0072602c10140711b000d007881101c0c4c5500094000c07100c492a080074a100141040001c0da01548101d20a40e0040c0c034003515082c0c0d5501c54929040c0788c400140f005030710410042107546001d029035900c072694080103210851070b040d6a50303643c000c2d01001905d907600e140422a4640d446080d952102a4403146001080e40c2c503041065034149076216030310155007403e40c460041d1074440c00320f5002040d01d464803042525034844903424000d4401041141c00e90946411002441c4101600b0040c4282e80012034980ba10729661800e200444e4040e05940d8030044007400002160714082c4100c44d45803810301d4030360b4801d1130b072004040030 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 93290468 1250 93289218 93289237
    0x19030c051b030f0403050f060f1e070309060908030411030d050a03020c010b030d020d09050603010e070e030c041a1311040b030403050d06120320100c02011b0e031c0206010504020f 79
    0x340003030000100900410340004c47ca02540a071202c0d0b40c1c0e24841d03484205011203448100074078103040d40c06c14000e11051540c029040e494000384155040da50501100d0a248050720031080c0803040008102e5041d14041300b074002a0007400310700c2800c02c1c0240081c00799032064018117402141d89440a5000d500540c4203403c01403c40707100f100e107500040c1d1108808100707900054101407010900341080f070b00300d80c100c0c1d604111168941d0b40c3e07a0022240d10101d1416203506010f03880d0810700307568031401b03042c01401042191090303a20703165003001000030720a02c60141d00d50505030851101009079050300c0403104003c98456aa40d968503080f18a0b10903500302220442c900100442c0c0700000c880e00110091180e140d81c03550108251051010255161a201450307111000e41c004281c0143c000ca074848982e40000700c0e400010444905c2203200003c0d00c40d000030341c046000d80081c50100010303000796940d22000805101e9004000752039074014000c06000d030350000b0724450051907034021070702c1180 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 93291718 1250 93290468 93290497
    0x206030703020a09060905030d030506180c090f0108040213050915041b060507020f040b0a17010203062b02190b160501060815040b06040b090c19030c051b03 69
    0x18200d00040c0003074000301c202e40d0004202c00004034017603018080800036200020000d00c4030b114800403c83c090100144490f80140c100742c203a428203140520140d0103001d9404805032a0039040c0c003441420143c01c5041410081c81400313101c056118026400f41000c0c260002103a80d9585800451078001d04800000c50000c0721810403040c014000d1111080803d04030000743c0382c5079100702c1121640280f80c00170794400c480080c00c0c1c916152644c070445400364094010070700180d407941364842407101d403001d06c1c146035000420004149811702510b610340340308000a00e031052003600350f50403080300818001d001e4420007030b586a150b482030201500400e00c42c2c401035665210a119203030680c0d01840704851300c0d03003040c0011a050001013501003108028243c01e9401d562284c83c1c2c6941e480e4040c180c02d801c56510b0640d400d5640320003a0041c840c0f10345441c3d5a5a48071884821100d04840441c454209441d0481810b50726a00c00304984000800d56286803003149524040c1d420752262440d1a00842d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 93292968 1250 93291718 93291721
    0xa080c0106030201080606030408030a0b010e040906050f13050a081c09050a020102150106171308031003030e100905040504030201060f12140106060507031103040305070b07020f030c1318020603 85
    0x1060541007001520310070707a58110700b91540018001140001d403001050ba00d401e00010fa0440c0301e50780f140780000e1301454007101380325100012404680750001d0a440c260f80350320821032008000103559410941e01021003001c090b0a46455403640407d0b000145840c100090b211480c0c06202007441481510300380c2040480c1c10340ca825962040b65480c101c0c058040c0c04000302042200f107004030304960040d21400044508070354846071000c402040d0f04256071401004001003485207010354440e024101807040001d0840c1000340880c40f1070a5490312500c44112a0b040709039001c007160049030810b840c003107850f44580c54140e01406d01508040d024842c40e84000495400d910104052140070b442940c0b4120000c1051038280c1d100c030301070040869000c1140e41c000a20035500501e1044800c4156070a103500e03039580701c0c20490030340e100354200000800c0e040305600d0076102540b03035003c2c00c50007070017020b01e04030200f03100c007420149144070b040d03840461054042c407240416100a0340103055a682c2d = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 93294218 1250 93292968 93292987
    0x70e0712060e0411191a070b0c040513110703030207030e0d050c0f0d05060103080901020f0f070603110315040e07031a0720120a0302160609030206060105090a12050a08 74
    0x2c401c001c84080d01c0c5840210320481081c286501c90040c031750482d11041d070105041010411080500014144075504108032800204808654450046140c4000c1c80c0d40d8906c3e003000c112551800146548841c2e1505842c804038040510845040c40d500d41005a180c024504054401c10204001143c12400200f884420480082a41003410b94111540d00011844206005c050101d58400420540c002c00050000c2480d84003c1c0c06904414812905506071602c01982003c2c1c0031140342129911500b81400701d9a094007510b00c0300d9000000380307400d5141404c00b800c04406c1003160940600c0c0e650080c40d03525002880050091130f000008001103014449840c411004100c030381038006556000c00365131150260301c995a2090000c0010500804a2080803019521040c10300c0d050540c2008030100d26581e03101c540e0300c4580107070000211400e06080180c1041070042905041080800c141301c5030b80d4034890b201e01950124480d41019088a207401d0340381001c02c601c0a0b00050340466101c40 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 93295468 1250 93294218 93294239
    0x1803060515040e010f151206050a1b0905010f1d0112060b0a0c1406040302060a02090109150c05071e060e040e06010b030a1401121103011401170c03060108070e071206 73
    0x40c0500c0c3c1c030b0301001b15400d80ca1806d884082203003d02d2002c03883c4840060b001c11540e4211030341180045200085a1801480d91100818007016030300203e04e08203401c02c41580c01108480044c4458100408000f03010401040030000e4854900d040c40042001502c0c40c000303c0c3d018502802034849032645d18000f86101412001c1d0507441120f103002440620000c3c200007041c1940120340c1600242550b842e14113030f54010b034011080b03850410221410014050716200c2d680011620107444410746081e1506041d400d11038650810b288901c040341d0264050003005c1a40310440e000b5142c20010000600d001070058910844c8117041486241d00115001c0e1100b80254003175420468108540408000c50f004584000d114800b405000d00d0040800b103071090b1401000c4003001400003c80048500030880c00000a0704004480205001c151100e07400c208028006108100d0090100d98500140c0e02c0d5511901d0103028503212074540400d1459004008204030b4404201c002d026442e1a4442d003103 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 93296718 1250 93295468 93295481
    0x3020717030d060b09180403030b030304030309030501050703050708190e03040e091b010e010c080d0e030306030d09050a05101407080a1b0201200304050409080705010c1803060515040e01 82
    0x12060f03d800c0000551408110484581c4507002e0320391380b0201c24620f5240e65000008006409158507940384001a0341d041c0700820242d071281e21110785060840c1400c508507074004160303c0c185890b013800d000364203401800301070f8032000924145150010f10035100000e403000e66080703c1d07603100100300862411444807100748100d01c40c9089036412604004000c01042d030f000348040c08506001010070b00ba5106207807110045001d00d561910709100c003492002229100ca00d4140907070004070034041d10785418410f94440740090701d401c800c42c600300f0001402d2140380307100d000d110b40307201c2002414450080c4110f100007440e2200301500c176035407410032800175448405100c0c0003404010f40d01d10142d2040c104010f850b5010703980c01e254000314800040070301d86001000005032205200019044d40c0b903005801410703102c0c44006486101750b10300741342560203600c5090140100700d49031010005007005c69504032a0414004110b0fa01c4002201d00c80b0009452503513001030518010352600c89054002c070 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 93297968 1250 93296718 93296737
    0x8090705061803010504210206011404050601031b02010b040b0a06050d02030403020a0b0702060402010f030c1b0c1a1305061905072105031501020313092c0604050114040b06010c0302071703 83
    0x1f00222068071070120f840b00802d010301d154841140c8003840c03090410f588041e0b489070b810b050004810301c5020200243c3e8000501d62350040c0c4d11030344540c00504083c05000c002c0740e029a401c80105e800c105001d01503000321b03001c640450342d0102c001424076108200d1f180003150070055500d900c2c2060301000307445403003c039030503400f0039040304d41403030b16502c60322490003880741d00c2c4d80c1d05086e02c02e4032030260a450802a019078210b0320004000c5540c607102540d00081c400c0010b441595010403032100041c45a95a00651290409201c4005030185440780304907030b07020525220341e0b5580f440c5000e800c0c0036003440950b011b807a40381d0f650f40e820680000055000c1e81c1c460f80200b501c401c2000049a80e445aa001d0305104942d0300f10402140629421200080111206034030940c4a5100c0f400c1a41d1841c16520040303074080c5041c0000d00c5801c0c4651403039001c03410346480b02890301d6180d0400294010f04041d0400003034912450602d8403d02842018103216888014000485200c00380c2c0c0383c0140044 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 93299218 1250 93297968 93298013
    0x807080c12120c0310030b010f03060e0105060609010c1a01030b060102010e1b060a02070e040302010227010512070e1009080c090603070905060102070906080106060305010608090705061803010504 86
    0x20003051007118000d60381c1000c2818048552566200c51a1010b0340018020010440c805080840080d24252070103020740710350000030024a182d802c000090302c0d04400c070034005901d0002407007810b4030b448046440c010400c1c2001400403e0603e0a0562140d60160070820885c0c0c881c008000c04c03444401c128001d10003607000b800a0310381c50429649a90b20456190403284038402d0070b500c1c508104014000c003014900680e0825a0340707086555030000d040f94211700617580083d0300c0d0907625a08404c095144601101c64070750000c540c0020b003252084039680c1e110074105400044040d0b10605c001469590042c002c00000e40c4030503009002802d10b800340d18868016400e255001d81400020580304020040007001c02c5890040305600400c0007601140c11400380b1280070824051a00584c402481281c000090342403030046c00900700c80040e040a010030001e0820300100b0708000070004281c48003260010382c0c80d88244007403000c2c059400b95064140d401c1c101080140840c0f900049038450b0722852 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 93300468 1250 93299218 93299233
    0x31205010e090a060c050d050108030d0516020d14070210030504020312070206071407050303040e010e06010801030312053d05030303103023010b0a1206090807080c 72
    0x1005041c108211200e5516500814802001c07a240d90081207510b4031900f0998501030301c02d60103100340c2c5c20036007198009510000710140c3c034102620507a90701c82690f1444042d9030324507100082d101c3c04e0401417201006881c10800300d00241c6a8212800c0aa00078441d810400700c80c031000d00035110490302a8800c1c0550001400360030304281c1143d6050354020296440c185403550366034086904c0360b20507045803241c4513004c40c103074030704200130405400644844121585481d15022010310028001e60400468200400000f034100b41c0030364450342c1c1500c1c0404c0568400c10340d040d1101c400040d818003030042030f010301114800755440c4040c450100070211046911102499a60700c02034038000c0340b00c89013001c101301401d004100040d804150810f4a400103c01e001c005170145d218400c2640d07500c980400d001290701d0715403000400951804000d21916440c400018075100341413107218001800320340c80408024841c0d01c481141640503000b6a00c8010354180081c0399001902646c40704d214184 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 93301718 1250 93300468 93300479
    0x3011a070215032e060c020d0c0801060308030910060e0f0403111b03010f09030e06070314070b010501030c020d120209030703060e0106051507080a030c050903070e090c090f0105040b01050706050403120501 90
    0xd641000d89010f500c0b80e1b0341c1c3d040c8990074410b14038102101a103611000b808040b50107030081c064a0010750141c100e158032800d0407030900e41084c000104401c2c100e803900104000c1c100000c1111070388141240141181c6079510705050741c081032200e1103403d45003d40c10344005960702d0803c40020540f0103500030004440780c0800c03501200c2001c440680401c540140001851509100500143e442480c0194200e8900c1e5034410860b08140d00880d4034404200050100313590602c116068407000d84000c14a22210300d4015102d06120300540410b0782e00000c0c0c2e020319440402a5400540d03010074204107100c400700c0c0b107074020300c078502441784949a01c141c0030544460310825104500e41005405240c900707500c5064004000740740700c0c5414040300340074140080e0307801e00c035413402495079070040b400380d16001180d9410002c1d2042c600f40700b03100200601448414a11100303054500650307000843c0e101c5200181c8540c014100300424941c20701081008065102008030701c16040c0e0300c400d0280340d032200e = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 93302968 1250 93301718 93301801
    0x30d0e061008071208070201051e030f0a02030f07110a0f050109140303070e0f150c0109050c0102010905030306041d030705070f050a05030a020f01050d020a0306140603011a07021503 80
    0x602c62500800d418164203400305d21840300406a0b90300c1410305070710302502d500c1c440ca4442071140266100e07100100c10404601810003100f0b0384a0740c80c0c1d9007140355290500986070061000b90080341000f0040100c4215034004122250015070000f40041c404401d03490031030b000e402120320480d010070111a441345079400020540f07008000c0e81e12116010805c42040c8464101c610085613400014140350041c00310a0701c00500101000c5030022a8020750790074a1860080c11002c01411a0300d0f05686001280340801581e4104800f141d002c505251400b00107404150042c1080449002c009845020814002240011541100d90b0f10048581c1c03a1304019121146124440d056040741c2c0014005142803440140002414103045040c4609007424a00300d801003e10000804e0f035542050143c22111080c0d1405141c084424a145605003920400c40c00c030704540e040a120408509201199118004101e03a85a5510900c0e01c03440c190210380c0c56407070324419800740d0049101754503050002c40d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 93304218 1250 93302968 93302983
    0x2c0a1d0405010e01061d04031e02100b03061b0d1b05070302060601080c0a0522090c08010b09180405030903010504031e0c0c05010c03090b04080c12060609041202030d0e061008 77
    0x112010180550306c00b21100d00c04020007001281017040031179078141c1d46035204000f0200c00f4550790080102654400c08241240c1c0b40c0aa5644294010410051510a580c107003220421407550110740351982654088048c0c04100401c0c407030560050050781d921940a000303065118025400c680098850b00d006441452040d40c0602040f801004031400300c6004400801c03400100700d00e00b031140c079040e81003078a1030380032a00104001030b260100c1007820f9a102d404140075201400b0000d05c0e03c9030010014484441d0319085403500607603000010144807062064405d9600080c2c02882580b07441c0c500101290036500040409010503406090110701c01d0031480c04181e0f2200c00b2401503410440159046c490081c4103c04000800c0e00100f00d141444000d40b00030445040102041d1440904112001c81c01502f036050035030080302007108580e581c11200d60016000300800702e168400810880c1544140203000307121900703003a0742c03080301c03400001e00d90720a4030004c40c000002c40d12180d0003a1210b00 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 93305468 1250 93304218 93304229
    0xf04050601090605152a0607120b030c1c06020301030b0604180201080406181403090f10120f0b0303071202010507050c1c0504030c0909122c0a1d0405010e0106 70
    0x495090048594909500614401d18031407070389031b2601008412003e0800b8030307060b0401d46400000602940c241c11500c0d0303840b8019a240144814a0948042a44d902404800610440000e485c24040c0c0a040d88000c40203500000155a04d40c1c40341030000251505032040340c0120302e080000c0b040401d84c5400c003000c0c564160344111440d107440e1205405409a84551000f40b081c0340e524031700040507081f0102c04140c501c809580c840006004200582408170b0b07481d801602ca07403910440e415480f103182079018405880000740c01d80c601f800c0748024401c50121941612001500c8420302450400c1d405d490001903000b40182d527102c403030132562801400120300c0c499003d000c811074008400c000360300700c00110345052420550780b44c8510000003001d0b44054100d40e0344811043c00d1010300e411542809940c0d0816013070031455280c5c3c0e0490ba100c200c400d0b40e0303002116100442607544038403807003000308200c100d1000440300c18500e030146404190780c119a00d618044100910b880d060080c1c80c00c445 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 93306718 1250 93305468 93305479
    0x10b0301030b18030c0a0c050411030415020a0516060902040b0a0f03031d0301050f07170f010b03040204200901111203070f0c050d0504060f0905030606041806050f04050601090605 79
    0xc40d00c071007a25040c1400d03142003c5900060104542c0c40f101001100e0005006c1e05110407464600028401211041407220580c0c1030300700100720104414080c803101840c1e01540044c1c0c0c51900480440305030040c0fa9500080c1003031000c04209218058102c1800c0724000c440030403a8824000420042e150703540701e1141c00c00f0300c202003080800d000300b0007059054100480c501403454140b000a00311002140c81d8402030210f0340c144070132140c0c0204204064980d1108c06481d5040211010100020501c5031110000c00000000e003191070301d40000802d2020100421401d00480038080e0060300702c2601a0b0001c0d0180e601305d0b00c0e0980004404003500c8010401a01e10b03205d0510440e607142d80c0c01380300350900907a100c0310400180200700078158441103a0711907446d00e041c014010000a82e01d00d07a0410800b220005003d03c1d40c002c50354541048084034001600f6170100c01c410b0b10082d903080c000c3c044902e01420032103c0018262070303511803441001507895507a25440e0f40c00c1214580d01440741c000 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 93307968 1250 93306718 93306721
    0xb090604031d010c02060309071508040b0f1503010e0102040501030c030b06040306240b040e06030312071b140c010906020616030b04090803070c02120a08070623010f030b010b0301030b 81
    0x2420b500c03911140180061510384030504043e0089000d40d4010f90b07a280311030340900c50400c400c00d0190001603072104a460507100c0c07401d0070780742c0c0b06460b9405440e03031000520303080204584d0619940f100504840c09402405280d49541032103000703401034801c0300d001c41c0c10252a0f90701e55100788200350f94254010b0495050a0554503018001c0c40012000d1142e0b9110b8803503041f188102e107076448001c01c4103105990740c41d81000030400c004a03010700610f004c1d07031083c0301c0c40028100301416154840c00034541004462135011080c3c02c0101051000b5050b90000c200303814890001080c1c45a8080d42030b241c90385825a00c40080b03980b031104072102100101601c0d180d03100c061080e00b200b0ba00c4440208041b40200140e280c0e804180d009660b100701040b2029110310850a005034030201242c85480038299040458890400701d2064100c01054160b0321800d4421042d181040c0d04507110140008249640e114002600c0d002001d0000396a5004120000503c00c41144200d9060b030f40d00c14002e82c000e = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 93309218 1250 93307968 93307997
    0x30a0507031b05060f03010518130b091c090e25050c072c01090b03030409020f0d0608060717073015090b120c090a0b0a0905040b09060403 61
    0x1420040c02e095411480711100002e410396a82d000703844404034540c110340c1e99501d0a020040c00c0e20034a68802c40ca81071010400c1242100761a8030706aa94000460500e255190b4190b2428000900c003541c0520310b1844541003510791040070a07060b10184001440ea9032192a0142003c0d82c40106589c910010380c00d0b03012a0754424800343c800c0d80079003400c4034070f682c1d290100140843c3c02c4500c0715400c000160100d0402c0d6114903015070042c4200e00d01046040321005c042500c0384118094142c1d11600092409801c90084007101d8123502c1041c0d0822203992286c0c1d140e501c80354182d8100c1d000840303101b0321030b600000341c40c6501c1c010599512103004001d00c164003000003e41c0300d0780c2c0c0c4482091400e0a0043c91705140540803458035880d00360100241006002000c95040415060040c403805060b4400600000f03801e5a0410742112000003560f12281d00401070200080007079000141c0c3c1c1400a040c01141e008280220f108408080d07050340e80c48682a9a003400b2a0080c0004403001c0340a00c1 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 93310468 1250 93309218 93309233
    0x15060a030210090f0603050702011a03060714070c030b090f0712030e010c060f0b0103061a0f28020607030b040c0e2808030405090606041a0d0e0f0601050f030a050703 73
    0x10090140d0400c0f10480c1d6982d8540303090b5008a0b407010020a44a0781001001682803040402031048403031801040c00ca080040707956860018120342c01d10069014140007610741e041944c0d401c40d482035000120503140c1c0303403800115100366624000c910035500c8080b220710700410700b10280c41300303035000d441111000c0e18100c4101c1d03140c00d58941800380c42d9503c400420454080d00205488190001c41c08416002c001000c4410f41d07800080a80d5020140c84000905041200c1104000050380c0c2d4403891214007402091017050982c203400c80000400a0b401034003c03650502c543c105440030801c0e00d80d200140000c0e01d20781c040e0300c40001c0445082c1c2d5000d142400130540b011a088040360246e00c0c00c107584035284600c9400c094055400820104003d1910f00c52255010ba0191006814146041c0341c06075001c0100c0d048003009500428440c048030740d16440785101c9004203003141c1c0301420f08000c00f40c0300c82c001c0c0103050060104419581560400140c04a0303129400002014030500d151203210 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 93311718 1250 93310468 93310489
    0x1080a020904060209030f0124060203091e060301092003060609010f030204080f06040605010f21060b060d1409120708030a1d0d020c030a120806010c02061b15060a0302 74
    0xb601c0513402d0108140d1078508001000540f120f40c1700024150024070108400c0100c8800e24681a42405005103c1d069010099620a00c001d9400c0c107a03203000d0018501001c0140c840054000c80003200001c0d041c5200e802084103907011801c0806208840d6080520512007100c1c4c0b1504204200621541035119054004152003a03140060038113403542c022505089401e4a00b5040791320290030f20090008511440e401000c4900040021a04c0c0400c101c03581000c40c0340400d440f6101a0007413062100c0351300012250030b0018602d80c0e0b00c0d03400c18030100080032241030313450480542c000022a200700020700003600031803084100b4109050341c0c2c1c6a1b000e95000629441840781c84014404440c1840c400c04808244c0c010b029004520b07403010000c0c5445c90305080c0d076109612020300c01000c28401c0f03843c491855054a04014250740b1307800162031818551030000c0d000100060441c2c0807905003412046410000380a8500d201c80d1100c440c0d038000c00648520b035018a27001c10400051510b041e040 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 93312968 1250 93311718 93311723
    0x2040e1f080304060c0b0f010602070611030c033603030d020d020910030c120c08060607031106090c0103180b27010911040e060f010b0a090302031b0a06050301080a020904 75
    0x854900d5201c500381400c40d00b282d40b10300082000e84404d0401c01040d03a07102540044a40072174001e562401c1e40003951124030b8490395041c45510220703c02051410710465019450710000c50b82d48400300d40e1002c4d1209034103104c0320701d4100030404400c58000d8092003020354800080086042000320340300c4c8402903110000f40740380340c3d90812101035141c46001c4cbc2c0d90b0448003030f9140041c5251041c600034001c045042c10002e00d5a1524180380b2041c0e4110070f4503508428150ba8880e02d4201502d4192240180c3d103003401410b2150404108142100040303852054000b030783c00b44201019030b4844203805144c180c0040403c1420000070f0400e6402c074404816280002c081036441400b490b8000e401c5850001c4250380d940960400d28a41d03007050700900b4000520030300203043c2860301e413800030300303002040c0910310104d00e0009040a40511420642c2d024540007810b40d400703000c000d10110b90003105a00c3c0c0e00c3c050408000d0026401e4000d2040d00d04071510364007e0609654603074201f2500b0704004004 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 93314218 1250 93312968 93313021
    0x30b0a030b1303080c03010609030308070314151e010801030204020703270302030c0d080304020f030708030408030301140411070f05160305030d050f0601020c01080907090207150f02040e 82
    0x2092804449a000308103412000004040c0b50600414000005001e4000d038501003004005aa90007000ca02c2104d40518150201d9191101d0440c06001040c2100204030201e41c00e1040c0860100d48000501c0c0d01103c0c545c4004500e0050040b000d050b0004031400b20300e000e40104003600b05a001858414881d1a044c41610f4090418294150305000b50320441c0c000e007403003402182010480140c2100c001c0b24641304140d42d564038600d9130302c40140002d0160704204e2142540b500c2c1000303400b025040100a4070b4507a0380b91400726039250001d1050b450304200035510000c07141024810f044070904021011460f010258803220192200000d0440d490302c10b08040c03c54514001080d24091362040c405180d403a0460840d0b6001d03118050b00f541c4560958005126030740c0c2c1c000481000365002800c00b071003941c0e908160141054015841101c13050b000040c00d00812151358800c00110505400c10403682040314148800c130f000310f000307503141418040c0201c0c0e0380320b42d00c140340c80075800c1c540342 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 93315468 1250 93314218 93314239
    0x10219050114070f030e0309060a1214090313050a08070302010c031112070b0708010e06040e0109021c17120f09010e0109030306050a0623090105361807030b 69
    0x400c031802290444280f00098900052100b07026814028454030304184802582007600000010751648030f84911001480021054411102c07203542200d8000c43c3c81144d44102407821024140e200d07804503c2e0701040c4540c034a40031078103140c40c252400035503111200411205c0c0c00c0da0b0065400c90f0180505400344044003100c0041355030f04000040c030a050781c4884135243c10702d9117801010450003038400c0701800300130700040c0204411884441c0d40b00c40211800304825035040e02c1540100440c1002a402c03144848801c41207100610514000c248661180c0b0b8071004000c20031440c1380643d40d50003458540c00c50114003011101d481c41c5420060107000060b60700f10340030100f401c403021420200c01003500c4d00d004101c10f20b442103a0f10300030002c90405607101d188103e2086512115800100d03801c80001c81d010510307900c100b044c0d0301d2028119030010900079207150703040c00d842d0290b96544202c81000d00c00386d61904102c81c881000303460100c2012a580c48841d0300b40d0141010350707503140e0031218000 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 93316718 1250 93315468 93315491
    0x12190303150905131202010c1416060f02030f0912030a05180a050109170f0d050403051606050610030b0d021e030a03051803070602060a050604090602030403020f100b0102190501 78
    0x2c5010b00500035103504e0384000346107141c03d42e440c8038460380700350940e4580740004401e6500b08070320038148c134000ca03210390f80d0f000c6000c0f80c1d10380c0349034a5401600941c07801290710741046440e0700440c0903c51001a4020303c2d42c031014015640c043d4014042340590341440030440c40402e60b0404c80d0020100e00f4800884409114042d1901c5082801555940c4d1243d86034401d03c62080740c06118403410f20181850008035242689041c4a81c0d400b94001507030360000034040c54130078415114107102641c00098a4403160a00c0005400296807107407080d1554000da80d18180a84076000030361002a04800044819408001071a0300395842168a227155181c9402c482e50140301d40f66546220362079258546000a0300307041c0c40c44003401c0c0a0700a601000c8180243d40d000074003152300010420000c540b50b0b46100110300a00004c40004003481d0005c414001059000b041648610703c111080317410349040301c540842a504001e80c45805a040641010706140c10044140b040780d008500128180d200305 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 93317968 1250 93316718 93316721
    0x1403070e060414040609020a080d050f18040516020c06131701110a090f0803070b0f07050d060605040501080a090b060105070204020c0d0804020102070603060305100b010e0901090209121903031509 86
    0x100d07030454030350750344a07012011440c20b05100b41c082c01e1035034010012b8850840001e802840350540c81e0004100205100500c020a464094006da00c0540203201605002c2d6040d456074003e1201817015014188603817025090601c181c43c80078481064110701c072803500d40c804404030500784021400e55252106920103000c44001032626040c50f51b034640490745002d0140c58ac011150300411856001001440b0108150111840d00200503108100003604c0d00e076026109486448a407041050810b07900003400c0f5005405002119400c0c0c8034050166a00c0d04220111620708400610903510007020591651141c000340c515184040c0006241420070308156180c8001c0c03030134020019210310200301c11541e040c04404001c2c8000d003400d1042600b1607462948918112480491149d5a110311b5085680f040301c45c00344585010b408606a5610f907200130b00a07600c40c5a84900400500349000f880c0345000620700c0d1003c04d0340369210801c540d19642180a012000301d8500124442034001c118131806 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 93319218 1250 93317968 93317971
    0x2100302090315060a080f030d151d0403080a051603020307030906020705011506140403020d0c05042301050d080702040c0507021201050703050c070210080402030708070605040f1403070e060414 85
    0x1520300054180c07500b00304005039880703071b50001801500b18030280c05083e1740020036101201680302010445900404140b0740c0006035900c9090040030300e0721207040c0400c05000341342c0164000d54030000540d4400c207071002542c0003a14101040e801901d4100c1c2e00303d203c0ea002d10780211091402041402c03003500d902003a60003243c1d050791180d40d207807000f25214200044020007081c103424002880300d819940c080c02d0b4016880040e001c0c1942d00c1400c8200041c080c8149e02510006004000a14500800480854036982400c1c4850111070000c102071400c0c040000d60590301008841c40d150700f541c00d01024060b17040c9200144141401440016552045450f40c4507500c42d00000300f074940804014159032010300700d040c0b000c6041150401584412882d0004082e141c1010001501c4074408280f50102c1984050b03600c0c0903810b80803800d507034000c0040007292071592040710303c3ca444050b061582510301009940c194040142007000400d80c2c410a80e05c0107004200280c28224842c44104100d0b0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 93320468 1250 93319218 93319243
    0x20030c01050702010605060d0f0b060304120e03120a0e030f0f1f0603020a06030504050f0105101404050c041707030f03120f060e060d050109060e0d0f020303090a021003020903 77
    0x41222a0200424400c195000009200a1081c1803900d8041000c0f4402d0312541803080d07440b8291600400c2c42d503040901c2e681d4026102540d41c0c030706400e104814280320341d00440054074001c004a024030707000501d03107010000320911924045112a00b5035102c6050307200c280c2c050060f16203800300d100040c84000c441d45005400f13000800d80941d60303203000c080520b00007400b40b4540300090000d61a03d40d60030082e01c101d420000f40546450510b01e06c4d00390070f440001519800c1c05e003001140c07981c4031004411588800a90040b49101c00204415600101c8082440c0601072004010381501c200b4400c444010715029a4841038594a400c5a220380322001075010952045041e18449014410340c0b0000800c820200902410007848070f00129000d00001e11401d110300c84402880020b42c002c1e007400d90b10101c03c01941070003002c01034a03005400304020200c0c405034084403015002004a9102d000498041c1071014865401c02814240e09208402056800d11001c80580c400b0000c1960248 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 93321718 1250 93320468 93320473
    0x40b1005040f09050c0d050402042a02010c050f090d0f06020a0302131e03030e2701080c091e04080d240503030702010c17090a0905060a0501080c03041220 68
    0x5061490400c4041c12503032001c07080502e0201001405a4940141d8106c1c00c0103000200341600e840c000a00a0040c5a841400ca4501c040c0388441c46104050300d013685101c44d40007409650b031080d034195850f0090750420341c05440d08100c020010301d80700b034484494511520000c00d40c441300342c403031100f20f030803000c001340c08290f0010362034000500120746013000f00b041100e00420403c0c5883c2d45007404da10b03072100605000c0140c001c4000c6076941c0704400c140d09030013800800b00242600820740d03003520a105258850040d01d41250950401d0f0404500c101b4100c04001c01e41990495141f1215100078010f503a00c041c10321080c7c5040340035015103030200b2840380c148080004000e003420102c610662100b80f095100704100c80060341c000031044005c50f00007a03111040b024080b4111800e10654090561040304500046845d007081d0b80075502039503003034038a07005054803800107491201e81030300d80c5440c4070828000200001d0750040758880318903c1d4984074901c1b0980342c01619402002d40b04806158 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 93322968 1250 93321718 93321727
    0x1090807051c050f1207061401030201301e0f0509300c25060e040519050f0406050901050105011d0a030b090708061b0702010f020a02030303152e0c02040b1005 70
    0x4000c600820801043d0341181c0d00741275141d54006800e03008051350300601001c407450111182c1a54901c1c083e041e00003004d09000084c84503201c24044d042410f04030008500c2e203040700741c82e050340d4032640d840744606000a0a03000c24100d60350f20714041207640d0740700c05a190404c080b52055100c002e071603040a0100103003186201004c8c000c0d018100307002000000c1d910340808010607540503100842680d02500c00080640303540d0844048440640b80c1d228807a41442c050055024199140e1403099016000401c0183c03660300d0000d099500a1240c01e00061001c5074000b01c44101030a0344450318001090311071544e40c5c0e603581c840b00030f00480c0e00b03521030342164200b00240201070290b2540540c5420345490303040b202010024083c0500800079040000700c3c2e00e000410b600805c80b03218026002000c40307480e46416184c0803601003104409601411560040c01070344042040c245a40e00c0a0040d00720600a0b840004c4400000199050741c3c45a11005100c950b51191480540d4030480c5580c1e542c1e54 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 93324218 1250 93322968 93322973
    0xf0d0f05070c08030604090309050301090305190207030b0a02160204090506010510030e1506060d050a1e0506090106030f09081c0b010c03050a08100b0c0c01090807051c050f1207 78
    0x2110001040c601c24031907034800c114001440d510850358041c008850000e0741207103a08007283e10b002641c010640541c6009001000d042c0c00c2400340c0100550341007070018031704800304202d03103d514501c00108040381200c0031580b04821038004d03044040704840c40e85184041900014252200c0443c15155030304220014130050030106d80c82039032400705003000c2c000701d401c606069680b051885503e8a05805645c00710703d02d44c2e01d60301140c4404003010030a1200381415a00ca03001001d40c200c20b0040d0300a01d40d41113030104006c0c0107252056000074250078a0740c1c44c2000c1503002d4102d03010714520465441300c10b41c001445c00c0018012200d031480c18240d000148103014800c4407104502c1c603051082e0b032400c2000003036101c01150703801382180c580100c1646490794160004031858005003141d00300031400d454081c00c001207020344c80409a0f5000c8119980b07544240d21002d4a00841d9001200d81c5440c12060081c0e64542061901c102d04441840c4a0b50008a05000760320710518502d00e40042c1a600303 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 93325468 1250 93324218 93324221
    0xc09080c060f0d020304030201020c070f08060106030c020613030306050a090b0a0905040f060207020f0d0f0501111e0f04050901030b010e01060e130902010315081608072601020f0d0f 80
    0x301a0191041458550041c00041803070180305111090740307030000b00040415100790142e400315840a406c58043c107840c0e07080240003807198000c03000c051140740000513074140700740240b182a03034650300602143e484140540031800a0301000382d0078903448840c0010745031503001c00400101964400003492380c0c40502005154801c03640a045880d05080910001c65042103a42c840315500202c016911350301d0b072022505240d40219115482207128602c01c0522030402075002883d44100002c2142c803501c04038603495405840c0000f00806051a005031000b040c0d031006000340e0b0440c00e116030805e0782d200005030301c04100740c00c00c981c0042c11000412142920882c80c50141c019810712029503814240466090100b05000102854030f99868400b564043d90000c01c1c00f15a60181d5100e40d84ca880507180c0e03490154028500e1510650b00c0090701120100d10442a2046081c0031318451001310b1140c5a0361464008420303040d5400c02045601e28141c0b40201074464071504041500414900e9510 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 93326718 1250 93325468 93325483
    0x102010e0d020606010c1a010e0f090706091413050702010b01170705030703020f0706060e16020601030209041704090204031b080c090c1605160e010f060903060c030f0c0908 76
    0x100d1940c4028400400240c010419581c07162084c81c1810011502c2c0c00c10491200c81601c1940c0140000800400c11000b1b03090341a01c1400c881d07120012a45034105130581e104c209124400004402c20410301000c1023146440d40d038250b0042c4119108041700000c0c104a4005658240140c1c0d900e400b10b00d040d503000120460444202c8030002400e26101c0006015848001d1001c410194000380061a220b4a9800e0390b001d145c02c1103042000e05d8807030a59000b145819100340545060f005511115030780b0004050f4141c0e0740c09041c0769503a440d16030355080e240c020b172a105002c400052002080902241c400303400150f000391082c00788003501030f510700940200c0f9004450b06400650201280e41c494840f656006088035000c55a94038280f071144c68498150780c8001c101d07010700d00654501c0c143c2c28a0a0054a00b012042811070760f0f03418410018454a114110108035008420404038405905c0910041450f04010600b8030b10181d1842c1160003a820380c0000c01c40150050001c15401c11401 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 93327968 1250 93326718 93326741
    0x12200f010507090509010f05060702060403080c010519150b030411091009110a0503040f0501150605040512010207030804030318171809010803040b070501090b09060901051e0a05150604080c010201 86
    0x42c0c17081d410501c0e03079902c00009009641c003d000000b054070440d1151000c560045410003541d54589a46e1840a03000c6c3c0360655055240807040c1c0421140301c84640b044418240c40d151040110038034180000c0e40f6500020300c1550b1144035910310000300e8441290329485170300d003140020304440c00d040340300d4201d41c0c0807e00c10242040501a66900741e40000469400580180e01055070840e54502180501045006800c1107142c00e6000100d058110300980f00303441080350741d2101078408403002d600302c0c01007801c042c001420320b00c04600401c0c000c1e0300c0103819060300b24101c0071154240c0c40d1070031548c1071150741c403001040c002400c01341c900c40303130009083e404000c64800d0850751404200960300d015070300620900c00400955042041401d40c8505601c80d4451943c00451030040c2881ea02d0340c03401c4507101540d5080a0004402d061010001340344603004403884c60039030315444205030040200810001c0781c0c414031404482c0070784e58800076000803c00e4000402c0c4141900b0700081c203560b00c50105 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 93329218 1250 93327968 93327979
    0x606080d200712030c0203100f0e01060506030603070b030c070602040b0705060f07050316090f0807030218060603010b030402010e09040b071701050a1712160201081312200f0105070905 81
    0x7488244600740b082c000151305854003040ea080c03035000007070800510125410b4900d00d003040c0f01c44510002d81003c417601346104020401296a00d040c0320180c4070803540143e0581110f00c0c00d020026200020f10b81002c40d80c5101c60414090b6980c0c03104981c0150020100158041000d00c10003d041000b60b900c9041d00c40380c5001800d00960281840c0006814010707990044000003404c0d5201d02c44100041012801809017690f503208400c2e100c0c1e03520b00080c0d0103040301c00d1f048030091041050071350084101070078162540c1e117031800000c1d0720b07000908101c1c100059140f20140d0342da00e07100118041c86c01404080d54134107040c00054080c4904107110200304148100411583e517400218000303c9802032104040521850109400c02c1005030100c01ca04801041400c1d0703821128400a481c81c0c800c0c1ca400c4000c0d1199240c00000001c400310051201d008441c141c19400d101d01c4481200c642031401c2e400594032141511810019110000c40090399640200946a5404007038036009007801e544 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 93330468 1250 93329218 93329233
    0x61e010903030e01030b0301091103280219080307140d02070803030606070c15020a03020c0f1c03091a070203070506030609040323040312030e010c020c04090606080d20 74
    0x1034140d144510001e410301290309048030103130340203402184c80c600005000b004028603601d04510003803002410340d0b01a01c2005a0094003180a405003015a40e08107016040b4407150380c00c1021750481d0710b041c1160013141020000b0050403c0001e00364151103410f014680c01300d50540245020039120080c02190311100082041c510040b0407250003405c1900c241c0da40784070f5401d001e01516850b03846500440c540740c80640a0175408075002c90032521030360070f451101e480d03481046015015240d0940d440410411081003848040b1503000c0900e100b414040030059a0311014040c1035a1000d40c4007150100241140451030305000400c003030a02110300c0c07811401e000300030581011008000400340412203000703120702c91210452402e400f401f1288559500e07203c1c6004448150102003803400309041c40003415075400c1c18020134109409550060880907890303800c000103030030b00c550301341c400395542c0c680411003040c21f00030340d81c49460b42d4660340090036441442c0000480e102d0041e45c100d421209 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 93331718 1250 93330468 93330529
    0x9030f0c010912111c05060f0106051209160602010f0b1c0f050f0d030207061503021318021003060302010206130206090402030a020d09120e04060b03070c0305070501050f06 76
    0x19040b0640351100007458a01d006494500907101032880000da000c0248450743c2200c01050082c02c02c204d2288007544c1c40b82e22240c000c440a0242070186202240f01488498084d1640c0c86440b544600300c50119600d10350600d40c5804440303095000580181d454000151041859010300303c40001c050b50f0200500c1010000711460148601c0028000483c0c1c1c40342e882802420401c00381d42144200542c1d0307072905811005802544501c4003210018208501607020705003c0d4450b00c00c80b900a04114014180e24112a005003806103920f03140600305403244001d6200c04c80c4c034890181984e02d00092441c2980000ba01d0060000c3c80444410045842d010050310b440054682102c03040d5400741e1640c031640c00c0748010f4040c10a00010b418a00324885040c0008580d58104000154070b4240b82500e0314828401941c03814094000c0d150300c20004500c00303c0c0300303000a541890091403c281841a180d503550709480c4240e0b02174141007510f406200c914944100008000c00840400705403144821 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 93332968 1250 93331718 93331727
    0x3010b0703140705070b04241d0406080a120314090a1205160507050a060f05041202010203040e010807060801090c020d1206080709021209030a201f0209030f0c01 71
    0x140030040422088510b203181071480c0300180d40c02c06500c1010b4030901034442c400750b142500a4030a00c1c0103640044000c584840b4118410240c01c010307903543d0f0320520003541c8005615060100c6a5030000e90702c000005200c441841861a030314030a8010a40034410f41d200213040d00d00d4400d4a0318100e2401c02400444040003c8010000d6400300703c010180048107000d99031400340300151320005582403142003c0100201d000e0b02502c0b021900c0d0550702e6101c05d02143c1020340b5a6606010943c200801d11201c0c3c0c0c1c030602100e034140b0501c11a840c00b520740116680c2128207a00140442c0c2c0034090920005400040d110b001d003150032003c2022080e018002075035200d281005406100c11072178003107a8a041500040044d1004c0f404aa1030143d48004100003540080c1c0c440645001c0341000c910303426404001c8820303020582d541c00c0c43c42c0070043d90481c0300e01711184d09504140301340038503000901f030a8042c032603000440b181d00503101c00002e000e040c00c01030002460805a00401c4992000c4da800 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 93334218 1250 93332968 93332977
    0x610110303240604030f1a0606070b060402090409080c150705040e0601030b100e0906042d0932060403021f0b0d050c0118050d030e0102010917030a060b03010b 70
    0x1000e40042c00100012501c03800c45a07200c2c8007034000c0400100030080c051044840c0000700d10904295801e00d0300d600210b01c0c50042660082c0d807045041260f44041b032909aa030581254006100501c0d0081c1e6100090845101a1048468680126040c014040b003800f011804100c7c0c5045100070b81352514006100e84111b00500d00d034064072401298540e40301c1e90001d81704034005442d06005111000300580007545000001e807040c0c920710002803082c18a8010054941c1e690b000059005500c0e0480c8008090303101d581d078480681c1c1d0508500441e015000001c1e9100f440c0141e51150b0b001401030485a88084503030301c895911000502c00007030f40c00901d5a002c80e101c101070b90031803090f0f0010980a09031041c1655402160b04c030514007402030101300c0e14140c00b0240c031005500c50190740d001040032480e10405511010840550021074040e48070300003280385c14400054620119559045074040148116022078804010800300c03440c5480f0304030140402c115010301795031505c003030104d03d44036 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 93335468 1250 93334218 93334231
    0x30a02010c031e02030315030309030c060a020a0803010f050a09090b060f030c180603070f030f0204090c030f06050105120102040e131a070c060b061801031e060602060610110303 78
    0x140d0141c46018140f04254403c0100c845140f102072103500c401000750b80c1d800644400c40e0209a000d00c0b1200d5140c00012200100700190182480084a4003041503c1d0420030040096005404100c0005001c01000390b010b4071030400c510104030f04010030300c0300762943c41d000041c2d59441c0440c0134001c50880403000d9402001151640700764180b034000b080c1408210b02c5015080b48250495900104201e03440341e12905090301100d03409561105510ba50b00303039600c03000d0240d1031440741c02405400c0c0354101c400da0f0781c028161004103e81c1e0f6643c0c171300c100305d03090010345000340d894005020b546803515a00709044140701c000e605060034901c01d08220340c005480d500500c0b0440c40003108000294132110541d038683c5000d45101d150045001d00143c0302c2410407110079140c40b48503451490900260703000c03200040c01e6202040440c4006400030301c070206c0341c1c0440e000e400e414041144c1883c0a45000703880d483c0d01400150030080c01303205000c492a503c086c2030080d8824903c0e01ea44000064950210 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 93336718 1250 93335468 93335477
    0x10506091302130e03070602030604180804140d02061c050109110a0815060c0a0302190c0e040311010e0c0108101208030a2c0d0815040e0c040204030c05030708010506030a0201 77
    0x1103064104011324464121003481c1c04003140361803d10125602561241806960501c000c0074a001d08142c10324168800410022080c84180002c10050410040c1c1c03c0010b4001002c0740f1094002640d1070300440b4113540407441036821036516005130302841d401080c02040230300144010301d811500d54007844105804214480001030041c9205103c9003541c06c07409421503950b002a40306064036020102c03402c4d005407040c0018a0a5400ca0142c100070b0b25400c00c0300c83c3e4600b802d04800e0414100054012b0b02082203031807500481480a20500002606450040c4501c095000014145480040c40e40c0305107100d0031000c008451182c1811401a6400f0211a58070303039a50f540403004000c1407036184003980d0740421103c5140340f80c03036020610707128240840742c0042c00c00340101e44a10b000c690851142214205000081c20180c003c0900801c00c40300350380009003030a005c2012a00070354800d5440880e40101000b0b50304041c8a600042c0c00050000e11861806c0303000701c0d640e40e02c3c1c03000090410 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 93337968 1250 93336718 93336739
    0x20d050901030207080c06040c06080906040f02010e040509010204140a050901060804031101050f0615072001031e0c0908151b0903010903030b01031d1c050c0604080408010506091302 80
    0x707a11a81c12120341550207810b0a84850300181616074651040301c4c112201c80c000500422039038010005641301d02810001408107035142da603010031180d00804228103111000d4440040b6a035140142072050080400040c0c41e180750a00c00b1010b401c62424ac9400340c110507505025945401c005681907a80d01d041000301c0e51590301d0308641020601e4000981035280005000300c844401007624001e54080717030b00c1d200028030051314050f00d1080200c020b110b62a4407040110140203a035500903416414140090400039000aa019196007101a106140ea581c020a01e07826000116000075001c00001890084140701048201610141010403132055107490b181a114081c5d08a44035014081d0003403001e22800d01d0b014018002c0e1001c0070b80404c0c140722583c40703121840d401c19100d808000f03000b401007040c4c00d0409000300f030070034130344c10200101000b0032038030305900708602030040f0b10401c1c919590700c0c9000701ca242141c5003d8000c0b885800c1c03050074404420419000c01c00420740484416498 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 93339218 1250 93337968 93337987
    0x3060f150d02061b0f0a0b1b0922020d06060201140708010315091b140103050105031b0f06070c030c0305060906071409010909050a0e12070b040f110a090203180a0201020d05 76
    0xd1040e50b17829013803a0321800100f0300c2004110081240101c204c03043c0041e00f44056480e08905000d040e0420f50414402c4c6201c80e0228144080840b18450b8040c0052810300800b413464142e940a810400160f07440ea0a000c0426480c00c098560181d107501d44480035506560302e0341c100840c0d16018454094035040b200041c040340e007100c1080d103e030610301135000a90300d00d8030031800f400d83c45d2654042450600006040d0401180800c00b028100201440b16a03451007089100c0341c40000c5a80c10603c14080d040009108043d0070001d980600c44440c0880e145180003858403000170701411003074001d1000d00940075044400c1500c0c0000c560307640341d22080c2240c01210049029404400214241420300c0a00e851a40c48112402c0c800c00c1540e140c4c0141c5241d149092141d0403004280d005484005004901300c2040d42e011940b040b014510032070b42d150b0006624000136004040604c1c1d002003403000c6c02d24010082c548582e800c038081c1c281e000340c030f400203900c44100c170740020180500003500f6100e = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 93340468 1250 93339218 93339223
    0x114190c0c05211902091306020c0f07030212010603020a05010e040f060e150a05101404030503030408090109060809060106140c010e0106080c2d040b03060f150d02061b 74
    0x24060250003802680d503040c09030390102440343c522581e103000d08425440750030585848880100e4020b4414092074031240340b030400c1c4407200c00080d9003c5a0a200d41011f00c00184060004c02a00d440207240090450040150340042d01100208680c9000310030070060311003d2150080b6102401c04801100c4c0c42d801181c0603081980f11441001d02e44940442e220b560040072600031207584006038604024881801031814560003500d50210a0382c02c48c0003c41e21440c2d140c280340c190007071081c1c1080d549a03503062558005550449400001003010b019039688411910020551468282c025081409403640c5440043c042d01040012444100e00480445002c98000100c010300070407a00c01d061408500800f841c1c09142e1a5006801c00720185140100d000c019441807800c208031131a2810724541c40801007882203a805c00e4440c404801d0740d60701449020b109100760900c03140d04d4900607030b00180c1408078014491041c002c000030f400151b140c2d00140c0740e460342c00f144200c48055110480704d1 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 93341718 1250 93340468 93340493
    0x10e0c160b090a03121a0f0103200a121e0b01091214060c04050a060507020a0905071106090609030f0304020a12050307031202030105010e1009091a0114190c 69
    0x400d141c000c641406840e0760009216803625019660351080c4400c5c9000e41015103c82d1a90503c103600d02812841284c54108400c0c10302c01414107000030000e00d05101100b5160f0007400c910741ca45da02107860550142c03ca1000c10348482e400f00c0400425081002e00c180c60f88940b01e0b9040125510001449140d002d0284e540190501042070040036115143c645440c1102044c4130015009150100382c0a12007242901c0913504005d24150718642804c50482d1250800c0d00141c2e032108050030b00240d035080911545d4024100360350f80300700c4030466028003450b1950160500b0b01583c0010b042003003050010050310f03150300b5580001513803911540002102c044007508060301c98008c0b142c40008001d0004002c1003090304c40c0d240e94030b481c82c905084100300d000c01d1190a020440c208240951494002846014850982002801161038078000401c03940090720320020004013a90040c42907822601c24644035440394030180c0b0701940c84d500c1041002110401d02c0c00e200074858107a0400c4481744004 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 93342968 1250 93341718 93341723
    0x303060e01090603110d050a0305030a0f02030c0405040e07230307080708010506090708010612020c101a010212030103020d0813080f070e010b0c060403180f030c1a03010e0c16 77
    0x4207503100c50009004092a1100325408180b04224a6403801c003071580702502c1e03401c6006014031312400d803015079041d4001041c445020383c1d140c281ca5900d2401380701441c0201c3c0342000c819112404d00d02070004441440150074801ea11050041080010b18a11401d4000c040103520170b402009070082854104136400003086030068200c0400c2c00501540083d00ca0002121080c840b80c40788030094840107000c1c01104005004608080c60302c05880c0c0080510380c1c041421510081c0c801d000d01812501030a402c2c000c80040860030740600e6904000382da00c001d80d292600d500e10351541d80098820300302c1c600018401c06001c51060040301c85090003200824029090381e04c03079105410816100c00721401032824940741d07100040b55401c5502d0942e10030b107030301c18014562a15035071404c0c0c0394201580c00a02c0500a40000411440001142400254490304076903c2c02810041c00911300c80d8106070350a01c0843c1800100101c2d044040d100741c2002400100640c3d035a0241501d11210200c070744003 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 93344218 1250 93342968 93342989
    0xb040e010c03060f0602060609040804080d02060a0c2c0f0316150c080304060b0316090603060c0203031003122303060405070203090a05011119031e090f090207030306 73
    0x10854000064105260444065804209403601d0b9903003106105000d0260b00010f0303201100003861405d00c0044250418002c024050805945980d01c5103810144e603601d000503040314007403200085150054100c1ca901740c2c00c005000d911050008801a4925900d0b900d080300d02c401611803540720a80811400e180c05015515114541545004403e85520407408020070300154014610310602508001c1940250780f0740c910b85070341d11954090400108000d506000f68038604082440c14410361000300100310001c07695618500b0301100711040510300a09542003002084203a8000740005016642e100c602c4000c1c04503007540c00c8442c1000c1000503403400e4409103001c7c440c10907003405184554012a0203100310354a20b10203d03140e0003044106500300103080d00900056000354407602040101c1d030110741d140d440b80700030b000701c641001405802040085812440c0390404a8030250902040c2c00c01a409516040b803c84519007648030708000039a000c078406c820584643c001c20000d001883c034 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 93345324 1106 93344218 93344231
    0x4150510030615090204080f0105090705031509030d18050c030a0b0c0f0c01020315090112080406030e100609020301060f08040b01030206090d0c030f03080916050609040b04 76
    0x2441183e502402e00c010682c0d4035644068401800084014542603c40c2107105084884c0500001402e42221006202544000030000c04039141c18042039401c0ea0b0390083c1c9410341c02218100c620340c41c20940f01d000703455030080040d44400c7c0180c042e50f43c81c20b407402c201507488000308001012421200c00080c01d1940362006440c102164010b164a000320b0107011900b280e1048903030240300140840c0e11074041c09d080109034007400341041c0c0d4001c0840d994072001c10358001d43c807408041540390341d00c000d84040300780001024008001014400242c45000d004003941090241100042c000020a021603100d070603654042c6801581ca0700b0f840e400d540078840706602c031405007504404264401c00010340a048444011800707000d4000b41442545401003048202415500e1503511900740c140d00f4624126000c01101e07421203000c1e139070741c03017480c0402c0241071019600c0da4020714025 = true := by decide +kernel

theorem cover : BRFrame.Cov 93165468 93345324 := by
  have h0 := BRFrame.cov_init 93165468
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93165468 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93165468 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93165468 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93165468 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93165468 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93165468 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93165468 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93165468 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93165468 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93165468 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93165468 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93165468 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93165468 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93165468 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93165468 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93165468 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93165468 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93165468 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93165468 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93165468 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93165468 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93165468 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93165468 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93165468 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93165468 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93165468 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93165468 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93165468 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93165468 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93165468 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93165468 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93165468 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93165468 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93165468 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93165468 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93165468 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93165468 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93165468 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93165468 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93165468 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93165468 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93165468 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93165468 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93165468 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93165468 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93165468 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93165468 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93165468 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93165468 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93165468 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93165468 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93165468 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93165468 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93165468 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93165468 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93165468 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93165468 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93165468 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93165468 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93165468 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93165468 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93165468 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93165468 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93165468 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93165468 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93165468 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93165468 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93165468 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93165468 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93165468 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93165468 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93165468 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93165468 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93165468 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93165468 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93165468 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93165468 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93165468 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93165468 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93165468 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93165468 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93165468 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93165468 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93165468 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93165468 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93165468 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93165468 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93165468 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93165468 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93165468 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93165468 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93165468 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93165468 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93165468 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93165468 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93165468 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93165468 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93165468 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93165468 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93165468 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93165468 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93165468 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93165468 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93165468 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93165468 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93165468 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93165468 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93165468 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93165468 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93165468 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93165468 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93165468 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93165468 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93165468 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93165468 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93165468 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93165468 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93165468 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93165468 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93165468 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93165468 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93165468 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93165468 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93165468 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93165468 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93165468 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93165468 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93165468 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93165468 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93165468 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93165468 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93165468 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93165468 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93165468 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93165468 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93165468 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93165468 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93165468 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93165468 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93165468 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93165468 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93165468 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93165468 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93165468 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 93165468 ≤ n) (h2 : n < 93345324) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
