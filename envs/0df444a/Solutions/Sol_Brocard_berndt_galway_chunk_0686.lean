-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0686
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T21:08:46.708593+00:00
-- url     : https://prove2.me/submissions/6abdd27b-5665-46dd-a890-afe54b2fc8e2

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 123201438 ≤ n < 123381294 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 123202688 1250 123201438 123201457
    0x50408060411032d0d030209030601351501080105150609040e060403091809080403031805030601120302070f0e0403050a0e0402040b09030c0d0206030a0b0103060305030d020403052802010302 84
    0x214074125815010f200342c1c90b10724201c0d4030b4820031079011100c3c4182c2031040d0001142c17681019842c0010341c1c3d00207601d503101400f6a0400c00c14080b004a20140d09111690860000c21050550285250b01881c0c0d00d18080802c0341c0c4050b036200003c640c41c20103015150050101c405c5245650404208000c0d454004043e21034000d607444c002a81e2140e400c2181d80c0c09180039440e80544542000c415a0081c54812440c0c20494101503d040009200c01c04032811a0f030946001400700c103940074040222175440e4003240e45803080e10008104030560761000030341c881c400d13000c840f0b01c0c99841d00c0c02c0592900ca440340394000b002c0d000008011a004e8002445960558034010244d0b444207000201283c001341c0010744060004070f101c400030b06040141d106890030881b2400c03924a09640004e0b4240302c003c0c01c80e030a8503100c1142800b50b90007074002d41d000e07550001c181c9403140c01540b0b01e40025001440305440034454910074042c2094060a24500c1d8440c840c803543c960190354006601952051410 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 123203938 1250 123202688 123202693
    0xf020d1b030b061b0a02130203070801090603032a020405040b06040c0816080c1201060e01030c030e060402040b040e070b03100f0b04122307080c010219200306090102070b010605040806041103 84
    0x50381700603070b0341802c401e401807240080180c9a007017030200200003180507080302c1d00ca540303061800d0002c44e81101c00c2018400c2c1c03684010050040032248151507620765000250801d04101c01c0c402002901d0f80e2840c03045409540c100840e1b0403803001102c0780d4205a40e40e042d6201c1d407125038032280344280c1040d03038000400d000b05440d1040031824055400d40903070003400052101d6411060341c1d070b8507000d41c4000510a207018080500250702254a90201a000034880d5544d0414034645807580e800c000f6455038620306440b41c0d25510207030407001d5401110504a5500b20060108401c65078680c0030081d078229544a90500d030034000b600207105660038082c0c8060b584412460062915080307101c843c041658007505045d440c01c160310345072a008005050541d000b401c00041007101c0d600c5001d85240d00010862500b06400450011760122401050303010f0149108100000205400425400307201c1d00c184400d0360790345d0104480c075001d5400341d424160030510201c0c01140320740d2040c01d02c00400030705 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 123205188 1250 123203938 123203953
    0x50d02030127030806010c0b240d080403020909060103050a06020f070210020d020d09120326010618080c152a150a180b04060f020d1b030b061b 63
    0x26a88044a0041d0002c401d00700d11020960405038408034142d006203084c01e20300c0c1150760a41c3d800c0c44071000106051100c00742e0b00751150395010000c6640c0b5038000d001d041841101e2450800000c0c5074464001070b80584440c030081680300303178002072481c100c3c1d4220000e030000707080d9561140c002c3e40c44480d0340711822005000c1c482c0503a0f2170300100d4040105540040503040c0c14494003074104116200b9000500202140420100e407414840030b10840c2d15180140c140496081943d00c00c1480524280072801050000305060303800100e8101d104114480540000341c0c0c07100550782e1a031a80c29643c3c0c100e92880490100c005951001c0c0c10740e54800d00e10000007500503991072901248842100c4040ea10180750001c0582840e0040d5400041c0c1c1d0805014002c50507061001003c0f03d80d80040410382d40030001402d103c5640c4c0403d082c1180900295521010b14014401405240d00340030b000d9600301c101c44100034007901c0750303000b0204050b1146080c480c2c0c4100c03690f40c5401d4054012003034000e110 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 123206438 1250 123205188 123205211
    0x3080609040309030204140601030b0904050c190b0d020901110c010c0f050a02030631051e160b0703090501020115030b0606040e1906060207060212031302041401050405100e01050d020301 82
    0x51701a1103031903c500d0982e542341903030004080d21a4080940d0050103242c040c000401d10201e4082040c00f0183d84650820044840401c1d018605900c507800034440400c1126983e038007070700104074204007640d61104807192012440e8481d981154918081208500b12200140c1250895140c00d03004200f510901d00058000c06e0805104603a00300400502403214510031103405140c0f030715200104a02498000e465a80c1551000010090911103100800ba080c0341e18041003c140e180317860807240400700b95140319620040c1c102c08401c6000c200c6e4500f002c00c1651052041c100c9420500e103959451300d1039615442044c810140c1206e40000c010040031440d6050b031042da5008a80c89160804002c0303660a40038102e420340d401c40000c6400100d02000b00c03503400104050006002d01d96140d481c0c845d030303608070102541280c0094000c2d0401500c98110122005d8050481b0416181400144d4441c1003c152159260288003a01c2c09214014001802c1003682030030040e102900010741d001102 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 123207688 1250 123206438 123206441
    0x601120603050607120e0c1e030a05070305060708070305070c0f02010e0d0b04140726010b1002060414010c0c1415090a062304021002070f18060503030703080609040309030204 77
    0x855100003c079091091031009103840b8450180507056240c01f40c043e5001d0000050b40c03000340940821581d14441082c0302c802d54080c010420302c20f0b4032408448039683d0381e107401900c410b02254050045a50040080c2000e802405a82d20840d0181c0d22088280e145548100c041400c005099040112400140c5001d4640610202d01c150090402821600e4545011001e1039560341048079690002d1100300007400b80b40034141814070396084140840e8040004041c01041b038005c000d54419084034588207515004140b8a02440c003e000d9544c029081100782400e03200d9070b80444000440c00250040401e0740604100322a03034401c4c080c0c4101824900c400740240b00166204980c2d60030030611001000f41503c19154400c0c0300141c2400b2104044050150054006101a000b0380350071420b1000103100f84036030409014104072220001c0c0e15980901c50070507090340c1604046107020804105458000152013200b035043d40c0302c0c0744554900307003445a4003e01510031070a00440135000310040c0d445 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 123208938 1250 123207688 123207691
    0x904030215070914040c08040206030406020d020a2622031803080a180323010216060b100c02030a06020f07050d050901080f0f0a0b011817070608010e06011206030506 73
    0x1a981c039494500d04040403241d41840b12813003940b0451130031004624031600b040e07c855205030103c460b02d4a9a9403410950042c2c0f1400c8000c040d1240700042124079030313403c45034400c19070420110b00c0c00b40154502c040455140b041d81c5103400703410501c02c18407c04004844001c20036210340341404241e9150680f10680300c490b60011208500c000c10942100343d4000e250140d601c0000400c1007049280d52a02c1e580003d5501c148000342c01c440c0c0d04c40c82c40980035012159007052944045040026a04008005100d1580c08a115001c401140581a481410040d40554004001e000301c01a6076070303590003d622000c0005240e410601103280400d100784244041d40d206521000c2e603d10303c40000604d01030b0000c0020001108910600c21f001c0c412840e86a4010034080c4000303498504100140c0c1c510412000d00201041c000c1d4000c00d0710444001b20607041c0d07044004072185c082c0c42d80016254160240110101c034241400000c03d00c2d0305c43c0501c805524418600011980d443c2e032122400c0920 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 123210188 1250 123208938 123208951
    0x60503060f09010e060f150a051003050609090309060306040903090e040f030915050a030b01030213030f050f010902010c0f0c0b04091d01060b04050d0c050306160e01020604030c020904030215 84
    0x70001c014072502c0a004060148003090b01605161500c81c14a105090003d8503856404540780c00d0b400181d01c1e40a66000a8a401407454140441d0485c008014180c12030380b05004603149000f0404000f0000180d401d40c440040c202800c1d40c7d20441400010300000406900b0030071040400100d80c03003a0b02070303240038600a80d032103100210a03040c060241c2501e0391000307107180e02d440741c034108190380107042d56580e240e5481c001c200c031010440103c01a0003054603149501510400010400283c10b90403d0314600c10400c2d036146010540700e090803200e99420190202d2902d00310100020b1010344072030f400314840d810104900d5200c010a80039030304a60441120340742e6421440c4840700c0d0300e501760780c45014510024080c0c60b08085c800c4039940500d2080d940aa2040c000304e10030421a00814405410701800300c2c0c01a00c1c181c41301088100705a5046400700328003411400440d44003040302c5e0301c165003503116200c0350043d40d801e0000c2104001c0003a4118010180c1c0507401c0003400c54030354001d00 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 123211438 1250 123210188 123210211
    0x210080405011b050301050105030702010605100314090309090c1b0607030509010b0306010f140103060b0a0203030403090e060a0b0a030e0f06100801051504020903030c0708030301170d020a080d06050306 89
    0x3a051621a007100c41203041640d001100302e07400b0315074642c801e00701d906503042880d007148c0701d0325507441c1640035181320703040b80307034414400007031103c1c45549030384101c1201a040b0a02907281c0c443e018600c0c0c8910071003c901d50022940c00004401002041c01015800350b00c480110030f40c03078080c400900b004001d980e144002a02c8005211100000b4004c0307980101c000c401030201c55242106640b814916031059000040841e004440c05a00030781c0810000c11140c5804c9a844c0f5030224000c4d1a5441150201e010440591000c01d07046140201c5520031800a40103c1d111030802d07102d4402600415140d0007090b843e034103040200703001480b4101c580c04010000341083c0c1440b0040d8840945a074020514131707890a410001040400c0d20200504001550010790f5001084046030440c8584225599107101d03e202c0003d1044001000311704070f80c0140e03070390060350b10f055000d541c4501000d40240d00592103000d80038041440307100100510040c9100014002c0c3e901e6011034182041110f0851032038 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 123212688 1250 123211438 123211441
    0xa0602040e0601110a030f1b0c0306060b071106030a021b060402011124091c020304050306070f020d0806060d060f0305060709300b010e10050a08030901080c07021008 73
    0xc0540c4484160003150909140441a045503c0996100070005c001307020010200c0e050555140915180240902c0f50036120b00500e03044c0c180109091128801214624500b803400140f445086045d01c001a9020410964880050007004210b0f040504500385c0a68200212040f103104210811034a202c10000361440e4500f41c000540000c0706103180c010f40340c1210300000d0384810030b055130b102c0010311150300100c203803a001042403512501c0c100d0502d403852445185051542c00201030012900b084003101c00c55600c171003080342e030194810400e5003d40d0003107000c4031030140141c640c243d01c2600602582e00305044001e25009859441e8410a800000f10b1014814000c0030f010444d8401ca090800450080c07405104001140380f11340c0c04049440d0048400d9129148961210f074410340100002c0a02d58444003190705000041d00d5107030402c41d242c8000520740c1401c01c8104211040f00000d1750400f0660001541c41d00401014000c0440c020801040140d94200f1700e10907100d40b0b541d40300704e603 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 123213938 1250 123212688 123212699
    0x1230409020301031101030e16030f050f030c06100b070305190309150608070e010e0105060d380301111603020a0203060103031701081209040f0b030d050306031002090307050409050f0a060204 84
    0x40f100e0480300802d1039004a004c509e8080040403107801142d90001070740003480c00174200103003050820809220b8030f0100150700710907000e000070241d02880c403c4824081c9d40d40ea40c102e8602a204210b8018003194040c8100b10f000020f01007088043d944908003c61140c1907a0b46001038504006640200150348010900050700104000c001030440030f105070178030f941800711040081c14144a11441100000745a0f2042c140c0342d00030400001070300490750009040c0d000b10110108000c010b40c0e15030040740e81550036600c0d05004010091100d010800c1c507180450300394041c4a212240160103510a031000080161410803440e4000c50107555400364944400b00982c10040701a0b1113440c01d40c1c02804030100301005682266402502141c0000d00d22410b100d44101510200b400660b1600912030781d04c5500d5042001544520310840a461040d003541d2003078822409910003094059126020610140c00c01354003008000e0300810031604c001541403903841c600109607108450098010408214 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 123215188 1250 123213938 123213941
    0x20711042f190801050604121a0f010510031b0e030a05030c0c01020715091401030e030304140c03070305060103020d0606150302040f0e0103051504080904020f0315030c0123040902030103110103 85
    0x35042d002c1d1801102c0c0b945800b000030303198011802003588140425011008012610101c403094041c117400151561810100380d510104003441030901400300c0c1d0035020145d40c42132240d440081c802403840010361000a0046035106010340d0865090700c00d07507050801182080018001c2e24282c40000e1020a03880000241408081c0c1d0000d41c00c0c1346d0700315501c0900d64200d040d500a8030000040d5211100810004030080e040d100701c03049039404000148001d00121001130540c107810042140d8110000c0d40030f050b80c0c0c982501c009043c0c0d8104000500c014600384640104441c0112408148030791116910001e402000c9100d0012941c0014204440c60035961044001c103462030b8240910b606d127445080e2254800d40740800001d1590700004d0030445410b050340c3c414030000c2c00c00c40d120b40300048841d0407513000b55071f401110160702140511030314002424070f00d540010303549c010203c2c50408484010f0400c522400055500a10000c2010b90310791014500a5010f0020b81c0c810b001c62100140 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 123216438 1250 123215188 123215227
    0x30c03150303160821070f0f030605061206043608090901060f120c050d0902030709060801090201080a060b0708071e0f02120610140a0b0d06051003020711042f 70
    0x140e0086240d01003240c0a47c0202945403003020b603061446000e0b80300c51084005290a0300b002d58071800c04902c0c1e01010850381d140a10401c41903030100b1004c102250645440c2c005100b041030304410000c90010080c40c10b00d00c004030544218a62030514030b46000140e40070000340c00207400500c1c0308514100007a48841c1801812001d020704100c92940580c004113103210328940800001c2e107500c603487c11034608110f101c0003468840c40401c07440d0b407220a518064040350078140d00260300038000c6030000c2d03041c0c45240e0803900001016031519903140e0b1040312541003038101361034444548c051220301405240e0500f0300c8512922400c140d080d047e104001000300900f01c200c000307600c2079080102c04903081c4d103141c2c00d131403081c10802c10b0208407000040141c095500003207215180442e45002041041e0414070940300c084500c2c0340703021441401101203001e00c00703004d42071601c640c20100396400c143d070151000c210188280e01200c000c203041c1d41c1c1980b030220002c80e24104001504e0312100b03060010030 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 123217688 1250 123216438 123216487
    0x3151e06050a120b0f0d0b2d01060e010c061506031a01020d120e010e060601021911010c172116020303010306051005030703060c030b0402030c031503031608 69
    0xa040c03002c602001400340100d140c0500c0e503e0340c0c43d0744418036030755000e2600d10030420003001c1241400e11031804040f00b44095404a1809401c0d94000050084912814070214144820008140e103000030480d98205031100050602800740700781004241075010b10640f0390b00040190002a1a29800500711964a90b00c9141e40c1c00041d40d290240c0c3e8045a035618500561030850203040007001c0c6000200020054030100d5840d10303003d00c001610109525209007000d809407054404044007004190707030a510300400e01c20911507062400c0d070040180303901c0d403405003804805840d0400401c8003558490144038411910318807a568424030f0300e180d42a4000310b00815140b01c1c050f02c4202950324041130000070181504c031000100400d074000c2c0081c009000c0181180c52507030b40d80c101400104000708803038000074100b054809680c24940212801140040c4403d440c5540b8134016244204220312074581c10b000c00c00519043d42407202c14000d21034040c200ca5551140d0310080100d41f400c0107802c0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 123218938 1250 123217688 123217697
    0x62b0213082d0a140f0a05010e0618070b070804030812040c050402090f0405060d05010c080109060609061418090a020d0b030703210e0a0b0403050c1f030c03151e06 72
    0x10b036900e2008a105032190340c0c041c410154140300d0b000b4070b80c101040300000860510903a0900310038440150002c1c02103004150640740c05c0d0300c81d140030021803c41c0c00643c150692180b801000100615402011441d00a4040c1d9080580300e64585480e90b1146070202da008a80806100500c020082ca800040c10200ca0031490100780402080081c58005800c07441140e4510000d11103455408400b00c0350742d4400020440454107070005801e0400038000c0d000a01d160070400f00700e040c01841008250740307403074460050440e24102c07072590940c0030302008011103603484545030498484503200c40c00f684900c0000340c0c40e140703842d091004031220301e58454481e038818081040030410003601409080885c044c4007008407140d540542d00c1001c2200b206030040480d000c0056103240300c03009402902c0c0b28506840481184100300310225000c2e682d0703407044401d891a1320500314000e81c00f012181140c0d04010034000482c020340f181082c4103034081141c04c0c5044000266003003580284002501c0309051 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 123220188 1250 123218938 123219013
    0x2a0c020a0f0e060d120f05070c0e25140304021f030b040b0102160b07050a08040305010504020405240108070207090207051e03042904030b0a0e0606062b021308 70
    0x1c59500362165550005e0621569004000d100d5200c0d90440700c0300c0740c2001c0c03184d10385e554603642e1442c0352000302d940c41c80c1c00ca0418882d00c00c2c40c001e010b00b650020000d5888101c4030754001d002c00100c1d403014104992144e46a80110603240180c03000741a5505ca80d01d0000311a000002400152171005500c1411500f0650940c8402c005080c000c100b59180f0740ca80035110303800e0f841e040b841c206075104040e10310301e0b001c9000010003005401440c440c038801d56051040e0f46441c00c02e09581c2e081c20b88a50745007841000c075105c0c11352203070707140581c04544d61048440860380c94541c603040703034046002a04c4039085020314005030079840b40d50050345900b580045140528005a42c12a61600c80000140c102c0d140c400880c01c0365080f09490245802400e100458204220140d0050561065810283c0030b25000181c0a1400b501640c2c4008010a2481004015004451401d002c000040c02810703909029a0203010140c0740d004001c1c0081900500d240490310744503145802daa000246102a030400 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 123221438 1250 123220188 123220193
    0x20403081b01090b1603230f040201020c04061d0106050307080115121d0d050301050f010305041403030705070302010b06070807020d061e0209132a0c020a0f0e060d 72
    0x3000ca0300c06106151403640890307041c00007540501901c0c540507010219a030f06000e444240444414060074070b9171000c01c64601d90142c080c00345201900c0003082a24a1400100e240d013013030031541c1e8403e2051058800c0902c02400103000c480b100e80040c180c1208070034101d500d00c18080b40f0240500410f0034041d0840c0341c0108000e0000205020b8581d100c030781c0e00c2c58514018007480364120144031400d8103000b1042a0034080114404520031065030307104202c10845d96502500c1182e05031500504030307003001c81e0400d0066000c0c0001810031a420310340d0001140c2c901c0828000355000f03003d5592800d07a52030003410001c1c291580740d14200d109403402c002d148000703007005085542e5103a0503178007024944550304011004003480f0b00300760602900c54546403c001c49503402401c05080868400a05c4a000903040d01214032022489603900702441d44894482000003e41d18014468078120031031071450b0740822008006c9612815082e050100103004001380d45410550210342612800304109994 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 123222688 1250 123221438 123221453
    0xf0b03120c0709060e24011409031e0313060f09050d050309130209191a0702060d02070b010501110f0a030e1306080f0c09040f02100e0d03020a050f01020403 69
    0x40600d6025144006841ca0191505022640007042c42c19020000d040d9202c4003404440401c46203910304c003841c2045000100c07412940800c0d02c0006940f038200109000610385125484012080d500d07225400d10343d800c101c1d031505c443d10390040000156440c0d0840000d8115500c00b541c01500511400003090007801e40d000454004582003112069104903090410768150300c034529465410502c1d8a8400c602401950001d08040509a661591a035003100003805103103840e0265000b180c0206001550300390480000c2d000c0e050004100c54070f0301608107096412031307100b0031041b101541ca0100400c019038010301c80191101011000d0185908003d1001d40c5400c008100101070042c407120103091911481e419860085c4627200401046842e40318044e0703130340300e4134501c1641c0c0d120b003950a0f8494100741c0c0c1080d010701ea10007040044202c040d800c01c025040d0750480304c000c001c00034241c04220f948668014900038080e4018190450081c01c0060608030540c2007003103160b004120420000d0b088 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 123223938 1250 123222688 123222703
    0x2090f0f04030315050907080103031e05070809030705090106090503060109020901050d05091c11010b0319170915070627020d080705010c020d03230a05151309060f0b03 74
    0x624000542d82651300002c5503c1c0c285400031030708816440c0411004541280e03410f410b0324000c0c0c0341e546206541c3e100320444224600450380000d4014001d10000480c54009000102c40c014103481c11161108041000010241c1c0100b001a820010070812410140300321030150050801c150b140408943c000b808601c51080c1c5001c104d903503000080c140ca0018060345614120400c4164110320320004c0041c4030300d200d400d418144d9444c1540b245014900001c50803a580301c2080d00640d1120262101c09100c10404102070140f081001ba44100365130f000b55240314096110b0010f030300c80c09103080c18002c0f501791580c1401d054400d2511454a40488410404250340c100c4003540584680c0c940540c850040c200d00600312743c28030081c2c40c429a00451f003e0b2904600d41da040018140d982107042c0754003070340c0301c2d0b12517038404180c045401a90140c000550021201100c041d5118004001c40e40c01003512524141d0310303654480e1070081050ba030250803021562a581407214a1201c80003907103d640 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 123225188 1250 123223938 123223943
    0x6150301060f14040b09010603020703030e0114061201060801020a0c03080f060f120703020d060204030b0903090d230d0305070e0f03060a1d191a10150c06050108010902090f0f04 78
    0xc95002549035031341ca6821805c26080050300c02c10007941c0da00005000303074001840403004207007400e004840f03848052161241e840c04088034241683c43c2d040c1800b810400901a01d5910b540b070301d60100348940b090004119406d015a1200002c40c3c4c507040060280d10007500381602501d079a01480080e5039aa09400c108410817a000b10b014660607101c0d9140c482d1580c0001d400c401c0e9030042c2d1061012a601030400c4a0045800101541e02c84000540300d2040701c6281e41c2c0403100d01c81c0d0300042a004000c03a0381d0600079606d281c24414603854000e140c02e2010481200080c2c6178020800a607522441007000302105482120b500b410031310002e9242c0308010700e640c00d9070307030395500711054120448507801140d9055419a0b9000d0030164920303001c5c0003a0740303090781c4a000c19410b0b5048d01c620400c0240c07150780c0d44840d41402a040514a19400150b45400300401c00e202e03402001080303291003564001d20b110000080c0b901c41c6032043c0010804006c4c14a600c202205003040340c01c0707540d6006240c1c00366 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 123226438 1250 123225188 123225209
    0x2030a0206010911070c03080d1104060210020d0b21010e0109021513231807020a02010c11030f060906130203030f1e0409020a030e03040f03020603040c0e0906150301060f 75
    0x60300041400741601845c1c40241c101009040c00105000740c00c0c005020151041c40c0a22601900e210100380510841c42004010f0b480009a5200b0a8666003e051082d400300b401103105030090001a00341e40303808a01e415900200c004440c00b0312001d1007221445507100c0001e00c16803066400041c444420302281285980b0002505038107401440d410201a00d490007203410301c01c80340390036440d60300000d0081d94000d01d801c0c48041141e80352410454815001d65006060030144c40c2c1c01141c0b400301138030003114081044110700c0e60550f41070002d5440c0c80c0540c0b004040a10303110a00d58506100a480c0042034400314031140051b03200482129000040d0241c0a42d4411204031403c001131180d54655403802d00115010070510003c2d00180140c581c956018800140d00d08042c68070380c801d0303100384c040303544049500b000141080409903601500809203400d0315962000d0b42410001c2c219485088c0c3d800070401c01008103415401080041000d030020003c040c03c1c10b80d80a40410f142c00f50f00e500c01d = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 123227688 1250 123226438 123226451
    0x11040b1b030705030c070803040f0b090301110a0c050613020102070605130801090c03230c01030902061c05161806120e010c0207060e09190b060408070602030d060602030a02060109 79
    0xa28159103001404002041102d0351110981421a26a0001d400b032044501601c2c1000912210003c10356040d41d1804080503409031905005e55865804062030755010b5496190000c00b01c00d1000151030b11a4003074941c2190a00340703240030750900c00c00030807138404086c03000b44042c0540d9001581000f681c20702d003800c503511010b065002c08000715580c06002c0560030904620f0400c50b043d800541101c0c41a142c040003c0341a4071000c1c6c43c1000c407042c0381400e62040c4110a1158070030b801c0000c8003400600351610304228142c6410000004005940d0110344440a21a51100355111482206c1851801c2c1101d81c000425021819205204100c20050042e81203254030850754003601c550000c5000802055840c01d40281d00d42c401c0d407003100c0101d81d800e903440390320381400900540304164070140460f40604440d0010020500c0340030301a000b000520002c61010804c001c000c004d00350300d070000c5031150030314410031040d80c80030740042045400c28000c10007100d40018295040d20f041680c0440c1c407 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 123228938 1250 123227688 123227707
    0x130b1213050a0b090109030f02031c0f020405060708070c0b0708090919020a0815040e03070b100e010801140c0702100f03150906030507060809030d0f1409010e070911040b 75
    0x341420742034081c3c00716800200348640d5410560003103401510a803100d803250b10b41030702e0030303605ca00030031501060300c0200030030900d084585079200f220310504c00000141402d44810100d4001c0c0c0200d002120b44da00002002e00500851496800c01000c2030450545004280e543d02c03800750098003010383c0201d5038003001c2040c2d440392440500310002e50240440d294088010000c014140c241d0b0300f44603048800218241a0505005001000c0140d40003146020704607990f081c402c00005000c1401850a0324000c50001c2149840c14004c25400001041420740c00f558142c1209010b820164262810042000181c40320b0a802116000078203264000740380003070b0154003414600d503203084407090803400821070031550f60010068034020b404030707000c5c0358880500f554a80010340d01075000c0c0c2d0081c000f281075100140c101c401c82089500b00071443c040e50110304c84044405a46009050351200041c0241050801020004025400d010300040d0380302003c180803441540240c1410200010b2400e54 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 123230188 1250 123228938 123228943
    0xc030605060a1a0a030b0901060504060810030c0f0608060906130b041b0c050708030705151305060412080a0c050f07020102010603020a0b03010302090a0b01201908130b121305 77
    0x902d0f103a104000440006160400c0c10b901a140000204e841d125041c211030800211141c10707144542c56551a190034400181c0c2c94010007401c0300410614060040b0003d1107a055500080481103104181d40781440c0024240040003003a41e40600d03000810032220755284508542440204e5000041c15a0500e000c54040c101740042882c0d94a020003000c404e40c4d0b440403000805074040c209032254a07854041003a240d100e800400f800326031104140e6030061040402d059008004000300300b41949896503020f040240c1100d00742c1c0d80e0006144848a290380103074cc81039002ca04500200315415503044050013900441b40b01408802001c50a10110b90007580114091a0010169004196541050b4680d54400d000480c000c2400380081a200e00c0c1a004548000f14161100c032204d00c0050b101d98441815040c850000340301d009540c420401081c100265218040c400c040e90302c014041d0000031074801507019490902d0700f0803101003072510b808801500080c42c84407026241c000d5040c02031 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 123231438 1250 123230188 123230209
    0x40e0307060e060601140705070501080601050403050703060c031a031c0509090411010f0206100308310303032009040b03030f0c0f0106140120032208010b0307030c03060506 76
    0x206150b1404200895418001890f00e01c103480c26619142c036500c0c1500341c07040710f00490344d00070000e40c0820003e024940c010100329034131403410316081d410203a0b00e86825140c1a501d9109071002ea0340c500c5c1c03c40b1015418015000034035a105d0410b104c14040b04d0210355140101103191a1010b40180130400340e40c420800c840301c000c40144a40802d0400b41010414043d800c04540c0c0441e40300030041e00c0c0c850000c82c500c0c4c0b007980784114562046203103446200859001081040c040c40d596041281034041460300c403503603035648501074a009811403401a0845020307210460a40882c400240c1220f050103007120100c030381c10303a008120002e005c00468074600480c0344a8491900104054005100c0082c000d8010b5074402c0080c480e041c1c0d14402421008079040d80d441c0000e04484c107024203c0c4000b01c1b00d0322111076810860f481c044c1c2100c402d0100e01e5001005103855052084200187c1900b4041c8580c408400c9000c2c2c11007514650700c0e1190450103220082156856000040180e41c0d403e8495 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 123232688 1250 123231438 123231443
    0xf1305090115090b090a0e07030308060112060e1504061a0d0617060a0b15030a022109031b1b0d0302070f03061407020a03021e0c0a0905091e0a02040e0307 68
    0x90303400640f0303545404054006071860710301403898000000d00300340044c0608201000f2100103400d069045481c11070304d444004081134103200c004800d0428510f41072281000500907120785000506220101c107a640c0c40f092205403080d82090001d000c070002d074680c83c1c0210700f00400c0d015a254648440c03070000c0d0035141d1112822198010780c0813607111303000c0f038018401d82d0b40c584104680654481040130b443d40c10905d804031850140300083c8207003004c1c0d00600c040d0005400401c0600105070201c191b0041c21100680303640c1002c14119214070158501e0328020b41300c90050580101800c1c124130400c1d641c07014051103100800e00c0d40007414024002a000340c001c0300c5035620110b881e41412710141416003502c82c018500440003584003880880c00c104100d5050b4050004a62091442040301c0d1600107800d401c0d010340080c90708560b1b00c00c0e180d60001e2810302c401290340d18241d4440c0b03052134111b1802c20390030369441c0c0c082500c0801c0441c580c10794550403100002c8455142c22014911300480b17000 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 123233938 1250 123232688 123232721
    0x100c0213020c01050105030f12030c07061503080d0e0f06070c0c03060f0204150503160503091218040b101e0908060a140a0c0804060504050a021005090f0f13050901 72
    0x99040002e8190007850581d03105800b21880305907070f280c10903a00c1008041c07100010100f480412058041d0800904100b40500c90125031030b00b400c064070328136802c3d5510484a01c0c0e000620240d5848050103010135982810011f049501a42840c164607150014900c60030001074103000010445043c41d004051030700141d0800500004600c0c99000b03512074080c0340e08080302c110007080100d00c00c104484c80741075601b4144844035001c00080d60180c002400409c680d000703140101410302c040c034000c1c02c4500422840070001c204217900340000c65055488172401140500e106038002c40d0004501d030001074405900d0070b0035040400781125101c504d81c119144a0084a0070311990420701c2d000f81313000c0038828401c62110b464590682c01182d03614824100440d04d244002000710f21141c1c41a54817500400030340c0e0303640046030700042c1074961900c015804601c0c089480c80c500c2c1002c0400e414000070982e1075007660541c41000413686102e030b030304500500c1c0d12035002619041742074100304841c8405041 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 123235188 1250 123233938 123233947
    0x30f030a1106010e0405100506040216050703170c06280903050705060f071d03030408060f040b090c1c020102120406050c2b05030703020f040902030103060c020a02100c021302 77
    0x92202810514403240c5119100010404c80c078011340301402154000700070001c00740300011940141c0f20040c41180d009909000644400d40b500441140052181c0043d000142c154544042c900c41307030700d043c01d400303050038030410004420008804c0d07004018019603400c1000c04180100c1c242c01c260000084050401c4040c0d400c00d03405c6801362980a00c95070940309282d440340030546103e0b104440d03c50004000c43c080311800c2c1c26609400c47c0014000d810b907440c1903203d01809107172800036202201c490740d81030100f0080c0402880503071741001600014000401002002800c1c002d405041c1d03499036044a03028008680c001c0001076842210024169140c56983c40d0103000c1e0b400101161016020f01e00a1080e94851805041481c1c0d9441050241682c3d0a80703007110745410082c110800e0683c200030450603201c05102030030080120742d20143c3e980d0306518240d0300741d641aa0034481590b100c0103900006aa506d00007190b00d941500d040a6480e1250000a40c14088078011041540c800103 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 123236438 1250 123235188 123235207
    0x403060603060b0d020102070501050c0106031703070f02010504050607050904090b010b0a120605181e01030f03090e251205040f05060145020c01060509100302030c0609030f03 77
    0x400c0201241e00510003003010034110000c0c054103140f4000e00a0040e0008001480298000e10213881d16008070ba00001c0da041c1c030780da10080f01102d81503900240240100402405582c859543e0075000020f100a002e5428a80e90740d680d102d5014000304140400403500c602a6180d0b076100080c0c0c17039042490703d81c003540e40e1102c202a6621441c4102c0c0000c5010307078814003684441c0030750000c2720782c050228480d030790200d4544070010a02801c29091181700c16014510001c10501c25030207103005544e00e1811444a1401034a68281c80d40140140c3d18081d04022100c8500741d00b81280c59141d0400e4503400c07074400000c0f192052000d403560f64541c640b02c14041801030346201da8900d40c0c800c0e012200720f07076214905040ca89200340e04402020300910042c0c00351001e89007010300d00380c2d6040007071904150722242038416071704a5a40c043c05603654440c10012490404041a0014080881111071074255008640c8500070844410300032680040e050750542c5042000642c070700d508105517503d03016a40c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 123237688 1250 123236438 123236441
    0x9100305040c0803070b160c050703030809061005010e01201209040506010201060312110a0c0305060a140106050703030203040c0308040f0810020f0d051905010b1b1902012003040306 80
    0xc1d202642c4060740554080f0340f210001040303442d000d400420810b42e954465800c60440c01403440b08004201080c51a107000403002c00800002d18401e46420304580340c600b420034a410002401c3c01440d510018080003075076000384003000708441c00c1c42c0800c0c0c2c140c658ae034010a03410500710800841c4c840c04c030f002c0c4030440c03042019000d1390301308580a01058886000480c2610498040a010301640f1032001700418003410003405900d602c0300c10390350540250f03150184107105036842511070360014010030440360401c0c81303200356401c45180e11241c42e50503d90010014000c5a10060601d82c0c00000700701802101c40e0460010740d800b8043ca50385039200e49041715100c10b10711038407065100d108160400200c03640282d41c9005015001181800c20300240b81c005042c01a10000016000061450301410180989400f0f041e6000c1c0803940c450202c00190b071050545030300900b07981c10060100c8005803122018042c00c07502403030701000c0b4444c00104021140f10b083c3d404900c0c2d10002030000204010f5 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 123238938 1250 123237688 123237691
    0x1103040902040623030c0c01090b0a0e06060a06020d030c091703090310020405060d02181504050109080f07060503072106180219050f0904020409060807050a06020714010509100305 79
    0x44d903116042e0342054000d000d400c602c8081308500903941400003503955507220014244400f22200041a203140b1900c844810301c0007510079104554503007688080b401802c11071581c00042c00d540c0c0f425a0340c54200000d458280360241001056103a0780702040b003038402e034500c00280883c0b040e10f0342c494003c41c010aa0700d501a40d001da000340074920f20900350300454402e03542110300c01f41c546890000070012041c000d50080450b09051081106400b03d01c1d140c02081214406960f100c680d0750360f0800300050200031190340685004c1d1700c000143c190511020450404070b0b0b84905000380c5030340f0b4140c0103684010000d60301c50208503074400300031007202c82a00311004032507070304007840034580449180d0800d0344a42081499090030981c2031000140c8120010000042c045a0707490514441e800058160707401548040d2800da1103000038000600d0038007070940100400c46641c4012860840040d4988000c2d1240ea80030908010041e0010703405202140e62101c00100b084a1840302180083c005040 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 123240188 1250 123238938 123238949
    0x1080304050a1a0301050d0303020c10090506100803070b090c100201020301150507031709070b1c05090a02010c1e060203040302010f0b03010c05120c0d06420807110304090204 77
    0xb0884005644089140c2402c081e641010210b49560308107003d02c030721280601400c40030558200000e200c0380c1740920241841142407007003c00c034002281001803270700c5406450843c000748007100801c10280000b007201d46a5a200c2035041c29684e41c40c0c21142000c480040c801e130051100b070504034145a065000314140c50200d1f40e2070310000b4640c4c00031213003401840c2c00100410780e14202040c400040d10b0409500000b5182210308064071840955281e0b0842c000038004007aa41a42000e505014010b9903401442a0001d041202554000074131aa030b2141000e80b14030401030415114240303008160b0030a603084030043d0341d030341000c0c81d00078028151401549401031602c0800301180c50180100c0198500690f1018206003c0040c00c200d03610300a840c50703a120302d080008400e400c0b9135024900060016403400344000300040001135801311480311201460618030384440300b00016002d2240031410500d000012076803141400d580000027a41100305a100200380002d200145170010001c0d5007 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 123241438 1250 123240188 123240199
    0x180f0606210b0a0b120a0c050f011b030c02090c03071803020907050c0f0d0e01080109020c031608070c03111302040f060e0310060603050f091501031e05060108030405 73
    0xd6803804000340c800078221a04601e2151514681c0118542242460300100e4156001130b5000550000400401c200d0310b40c0901608803440240c00d024400140304014007003519096608140e50300004c1c00801c040b07a0307401700d050703602c03201d6803c0c940f013a80000d90803035001d000d04400d03007425500300e10290030885103a4000366448412003210b00000345190300701e9901809203d00e9488040d004e49194100030701e0111284903034140e9120401c1d0030040952845403c1e100c02e0842c0708070b040010500d0300140c02008100d4010884074240701000000c031800f1035031050302c1151004403480c00050a03c80c514001d8401560a400030041c411840340510700002c00f01d449442003035003000c0b174001ba4015403180009042d508141084000d000d0340b510203080746c000381034441d0501c590010030211004c0350042c0b400283d40380100b120005507035011039000003510300141005201091480204801400010715817100c003032850384403014030440c558841c0d6018050302c6642d0f0b1510078580d07036032308244515032003039 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 123242688 1250 123241438 123241451
    0xf030a060b0a0206060105220b0711090106020a08070c0302062a0109021c051f0501140109030f0320070b070203060a0b0a1208190e13050702030702010c06180f06 71
    0x75690354084582e03108041e005402030799a00c070010b480541211510548110b403c0c820841501c1605902d030300606840188035882c1e0356981450080c140d010f2030000e003d005070030300501041f80c002500b00301d0305a01820346076450110f85444c9264140c60381c0025000032000c101c8031602580b0450820795401c1d4041000040010010300e9070a032090500042e4116413528040420005210000756580d4000c2080301c510030510b42e83d00308002094154130405c0341d9510010301c410f9201c2c003283d60401d18240b03811501d5500f1600c031041e615141540003414009041c0d4441c0407021126144903007004040191094299900c034071800c0390384248000c0780310b030060f40001402e20420344a4404e000e500a020f41c40d5a0381003c0d890031070395402310010764442509001c80501c03045c180452a0030702c2c249a8607003e1041c26401445150b61040c1e40f12110700c0d0a0900700107180d80d000066600f900d40901e0b201c0d20360840c1d800c0c4140180041200d0200d425405c02005041c030008585801090707220b440c0803c4107 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 123243938 1250 123242688 123242699
    0x4030b0c0d0c1e0219080c0304030f03050a02060106170c1b25050d08040320300a120507020a090203040b180606010e0d020f040501240905060301150c06020f030a06 72
    0x841c0703191500c0c0c0081a00600517500400c411002820f0050003c4c41101c0c1340a489494280411584d440e0442c0010b20000341844904d45c18040d036401449942010790310b40e8640000c81283c49001010440b1841011488500c888130004110000c032221a055411307540c0c032602c980080c40d10b58180d0846a428400d0001064105205074060050301f04072078500349810350380d44004038940d41c184803041c88034290718070903540d0b9242080903860700c0c1c42c0800096081d039051090901c0d400c3c110f02c040301d60050701c2404042036030486100750403d02c074074100f035485400380300003001038030f554004544091003c800c000410085500190040c24904643d28503250043c403041d40c0d80000303c5465000400036040c4001c9130134030181c07042900380300501411502c981040450102c403002da102d800851100b4030491503621000c1c94003116071f074103854004525818900071401c241700c10310a00324541b100046c0141d4440c0310780e80190300d1035408402907540d0f0300b0034001c403c0240c10070b880c10140341d0b151800010b107 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 123245188 1250 123243938 123243943
    0x1401020c062b0f02070605070f170606130f1716060302071707060902090a060302090412260601030f050103110918120d0b090c04030b0c0d0c1e02 64
    0x2000c0e1001801c5618040c003024820780d4010440300200590030840090040c041040d0048400400c8060b10041e110300303040c1480016a44090700c0c881c20f000c03072403d000014541c0030100010300082d0a10740802e9844c1c41300454101e1280d07828002441c0101b04000c100305c4808070406045600c0e00700100380203d080580c05840d02c8400da1424a2285541800c2081c41c4c001e03000b82030354a000b00d11610780070f02010a0031406900010003110203a035141841c104502c1d14005058121820390b10401240342190b000c41d86115000d400079040301c1d42503400881c21440b441c0d0100e01c503034030b6000c2e800038031070050301401030742400b585d940740480e00340700c00710701902451300c02c2034104c035005408082c808501c01d00340815054040c1203085205c56075890b10342c00400810509000754250b0b01036642e1405a542007a0441d0302481074039100d60031080a22401c1c80c602c100b540e00741c03a0000c80741070650302c84401c22841880b178840e81061207410a00d1468640f0b4104110f40c143c0ea1321810b480c0c0014084174000c0341c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 123246438 1250 123245188 123245203
    0x10f0609050612090c040204080f0d05041202060d23070801120312090c0504290904020109300c03020306250c0206040b130302030d02010203090a0336140102 69
    0x150450820321000d500c1280e0164000d8000400c0810f40d1003400d961707008102640c2c029080350005500614000106c2442007211a4181e410313440c28034141418444d65000036010424040e104410210b50000442040e074407082520b103082c5081801900b44101d041c0c2c51210445034000030583d80400001c107503080c0c204503460941c0c1551000204484129100010500501c003942c1540c41440e011071251140c0c41600034038091080400da41920030416940f46614020540e03000c0c2c602c0b5414000140d130016903031000d51f0385042d81c901c0307075080300740044030f200c440316010504040d2200300c10400d0191341c20010302a68000d6095481d29640e000c111400c0b04003801012802068035040d40310fa0328442d0011140300f510041900e4a050344e904100c04568100703261407801d4841c110020030452404000c0c0700a00c2ea400d000950031842c141400c280c0f0b03452441070103414480100714120b50444a554040711070451b114010709496145442505041c0e6580640c941c01d03481e800d5a06019070000803440f = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 123247688 1250 123246438 123246449
    0x11b030513031419050c010e031303030e010c05030403031e0e090402011809050a0204090605010801060507230607030506040606021209060d0e06090c0a090501050105090f150a020303010f0609 84
    0xc0a08074840d5000c40390b0000c0e03002010358214041c07154a45544d001d086803010861942d886985808030501e6450031070744410221081c5a00800c000401003a19166540459800d41007003814081c12400503501c40c0407503140203185000000d03001c4209078001181d1800e150a442500c240000001d6081e24901c803081c0c0c1c01540008032000040c0150b218100c3e0f4003250300c05448266501e5542c0d480802503501c00d55036a20055000714082c007580005100d0f81d0014402440d241c1c40070b5240420180c9036205008010b420503072155031900f03440c40030f0244001110394030400c986051903c0c1d540240105000d0392003510036410610000780144c80007500240354528041510b26000c030210422030b007503003c0084400502e880b141003201030402406040c0c4070381e802c480a402d098454004009280d03c40c0c2d00410110391400e07005111a0742e22000395888094182c990407408007001e0b0018084074000010400d09640020700448140d0780440654101d9091003295203825403a107405665820290040 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 123248938 1250 123247688 123247711
    0xf0209060712140a0305060909011512050111030103030c1104020301080d1110090302030304031107060e040218031006030c0e010b030f180d050307020606010801080c190905010305011b0305 83
    0x460115001d1180b00801915034200841d03061040c10010050390400301100000c03c0e611420020a401c02d031401942c4030503680001c110500284260521040e880d0107100f210000403450038042000951000e484244c00080107500d9694034500200340d040020403c07030b04520318146503203180c107140c000e1b02c0c141c0f4206000b61289020810301150b044101d4034210b5824072884510032440c024030310540728042d000784e01031552840c0604025000007910040800103034002e0358108005a400700e07030300131800c00c00c40340540d907048000d14414102055a41c0c01b80c1c18090303444001d8480f4455400202120303c10300300c1021055550180b9a80c45009116501c0300380b00820004852400344005194080f01c400031810300d02480d003d0361490205500e00c0080460800010702c0b0420b601049955401034091a010a056040c10356454949004407034160180c0403808501141848441446010b072107504800c2020713607940d0a215010f0440e640b00280401a0200c2c081c1d00c0324402d0103074a00c103c140521 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 123250188 1250 123248938 123248947
    0x4170c150c0d0314060f06070b070f020d080601080c0307021501080709180203030a0507140a08030f060906150f0f1606060f0609050f0a03060e0c0f060c060a0510031509060f020906 79
    0x1808a401011903546da0700000400c0b40d02c001944161324940607610b2651051611004040060b03c0d0081c050032000a00c021391040084680c0d1007031029070300c16280041d181d00c035114507409070b1a1032a240d09202c0d40c104503400119041000054000888640305010f00801030303c10307440f10303a59219000c040c0d0103030820400c80d01014041c1e0018159540f00700c00c880602c5002600322401c1044803c000c4545403000410b0285c8410b0640e402e68100d18110380600082c28540d0000309250080a45001d5003500481d00a05407500481907446d101584800d07583d6074007107c00c0b070b08100340700454200d4045150001c00308900d212080c070503066600e0b90321201d0b401810301c000c200021001207041741e800540d090380840007603d00d0080d1100301407040002e00c40450098108458003c00d142058080d4409101010420390001111600701c04400d400292586404d600c0d45c41555a41c6c001600380c4030100c0c009202c904c83d40c1d00141ea4180a114208956013842d01840181d00ca803220050b0320203030610 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 123251438 1250 123250188 123250201
    0x50706030908090418020a09060303030b091608040519080c01110a0503192c0d03051b0d0e0321060405011a0a020703061d1b030304170c150c0d0314 65
    0x24030155905c1c05003500d4a1030000d03e940011038112560b00b00c41d01590325804104100340d014001c000e030401d821038000c40b09203000c0d031001d0002c091104a640c1006220004a42440780078000c070f0058150602c0c0500c2200c54606140d12203a205c0308900401d50f2030b248141e00c1a450280603070303028107880d60f902032441e00c0c3c59041c800c01c00c4080342c0007039005581d013603507200404409140101c031002c0c0d010074501d003101c0b411030b05082c0b490701e0800c10240741c10941003207500409891014000716500351625190116100b030311006121358030620160748030010b0744000c0100c40c00040c090100c0c5042c9400c0450f0340e03500a01080d95001e108028540302a04043c100c2c3c000380101400c40c40100340304450b2038580d292500c8041e50040c083d807080c42d41c0c4c1c00030100d290304400d22020846800590800900e294100c0c040707603592061340304c1c08640403100d0700d0080800230280503441e80301000800ca62550964102e04031959400884000100d1003000d4085444074024000c0c0be001c039000c0d400c642001d07603e02 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 123252688 1250 123251438 123251441
    0x2030a02010809030c2b08070503270a0f0b0711060109050403020c0d031101060501050403150b01090801020a120515030604080a02010b1f1713080a0309050a050a0507060309080904 79
    0x5094101540801c2c80a0852105c00700b007045555800450140074044440c104c9481080d41000240304129204003000300c5160050120703600650780903843c0960021008186655074201c8645150500030b4040d84820300c000c0c0c0c400e501e40300d402448903052035240c03e501580c0c0004800200802c58102d200100114500e950040d039201c0d000b801038508002c0000001540f030300780070104130302040301c222540d420380303e00348105009814207003801c074685821502d54181284000807402c42072922590f0390f6500b6403217030080e54010200c400c005c0d5100c41c8004805030039000d0162140290340c1c038040028410601c1009100f4903000090040e01494685071240246c5a200d0750340f02096640369180c480150721003d04002c1500b074070b1035002440d0050180014a26401007440000c07a00501041c4012484110201c0c224541d0140003940e031171140c031000f42c02409200c0e402400c14002c1e0003070381092080220304260581d10450030f41d03914580354841601103581d448406007025105000d0714000e410036 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 123253938 1250 123252688 123252691
    0x1103100b03180d1808030903031905040506040e061302120a050a1503030c0c06030203160c020109051210110a2a0b090f06090102040b09040506010309170912060402030a020108 77
    0x107036109455000e00340042e06180140b075003285000180c200325003d400844244464014041040c003844c901002c400019070360303005080703103021180e21030707019050b100303000e08112401044007405840e110380e5507042e0890100740448000303000d5150410300d41c440340124401c640c036200d5110110360003030311074002a0008140c001c0c0800c071030681c0c980b82d005400c00d0000700d81c0e00641c0320380d0f10101e440032540b0300b0349002c5071240d0040c0103040c014824802405d01403070413035014486528040d0465401800100c030000e207644c0c0a15017207091904a00007a15001c110303500311400e0100c00b80001800310302c0d80d0043e8810101403400042d50115282006011441c002008021108071221304220980f0b41200303030107081d00d80c001d25030312050100b0b10502c030500c02140e001c20714000031814185045495081c5125078818103105541c0d50000801c41da00a9001c14480c0b50000b482c0f403082c1c1200384111005521041005110f04030b0140b2203038242000048491040b903028014000381f1866500540d0590700 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 123255188 1250 123253938 123253951
    0x9010e0f04020a051507030e12060408030702150103062a0522030b090c10050408070306111603020601050a050d0c0b03060d150501050a120b071407050109060c031103100b03 76
    0x450200004c0307a544403017000511241c010809982c5641519010300030225001c078587c011010118100c45400012030001d42c0f140d04101200c0c1d696403a50000c80c00c0170f03d0006c1c20001c80c0300340e500200501c00300f5030001d4400621260f440846601990440c080030b0000501c1d40005501045815002003103140010040c580c50300301c003c05d080e203940c0c0e111140c3c031088401070380c1c941c4440c20401107450601e41c500b81c00c48040c00d01c20319082c03c10003460b480d66014000944a19216507a104003105484200ea103140382083c00c2600701c050b1454001c2d1206028841c1c1440741104000114040ca0503c0b00c04404684c8460083c48440c03404031981030540008200c20303071100c00c5e40c802d000841c01603e00c00388134040e01500018190705010401c4000001500044a07540540c42e9620001d480c4420301274110301e860030080c0d01d00c048428012510700c2101401000e070350030b0058030710411040303420400390b042194609000e580030380d000021982c04122050203598407020420480b4019190042d5088603 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 123256438 1250 123255188 123255199
    0x5060906100c051002031b031603020304030c080d0903020f010626070b04090623030607080919080c01060603020717090609060301060c05010b03030a0c0809030f0106080a050c09010e0f0402 83
    0x2c0c240d4071864202051a4515041e150300041009440da60042e03001420507000b20f10300d400c40c100120081c4041d42c13040e03810428540d00002240c181400350320b01b035a04c0d0340e200703c080b6511200301c2e9880d0068407000400b02d0251040d15069213031140c040c080d60060742c0581c2021000340164000c6119242c00803400d079206c6000301c50010503000b82420081c000341965180102d081da161201c0e0500e60b025508506d009003c40f01c8241d4030903900802d156030080e02070300d402c1e80e1540383d2110440c18441e440e1142c1d40c1d0004031841840c10418903502500d000c14002008014140e42d401080d400e0344142c0d00020b00320132001c8410b082d6440c0d07942c013804c040c04014101e2030800000c1000318040790300a030000e001044941840d042044424082e503104d0120550280d41010709021010f0008404c280c0028a84080411001c0082d1000c010300003030070304d211001388181a1b854400076240c04103c4001c1d503450248014900440c104045894105c1b010b400c440500d075035031303030030111075148015000b2603000c0e = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 123257688 1250 123256438 123256457
    0xc06020d02030103031707021207020d02041b0309030314010e0115030905010f09060b0a0e070c050a020306132105160602090312033103032f13090506090610 69
    0x40c640d031001d1800303140300703441310180060030100f0041207a4004040c0c200310752090382c1c44110640101c00790f84101c0e0341680c1c5840025014400500a03190100310082e0002d812185c42000f1503040e005074403202c1c003d4808200c40c08140010000c003220034040c240920040c44010440c01100b50518850305084e0301e00040c0c0402d040e03455500f0b59441c14100c600842d100c90305402406524400e030164000c04444e100e4600385092211083c211009081000f4404508404c03414004c00340f00e0345e2901075005040d1245494200d90020390034032000302c01e44454106c00c104201180c5654009031081001d40c88d0f11b401c0c1003a44060080d1241050821030300913400344001d007800c4d00d0070031a03072440e1500c162007030b0f8a03440c2032107030f20154020484c2d145140c54a4207071003009103100d1005000e45140c0516001c100c0030b02c2d5044040c803000d428001864028a4004010f1a18400c0b6000e482050500940140184d9440701035100740c03101918219400041078011032003901c0c000301c00b15040401d0f0b08110984 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 123258938 1250 123257688 123257707
    0x5011707031e140a050a150b010f08100504090b150d08030609070903051c020607090311040207170a03020301150f020c130609061710060303050d0b0f0a03030201140105100c030c0602 80
    0x4d1003040c680440313465002c000c4e11002c0000e4002007140c0710107041e108004d1030b80c4840000b0112140c800000b001d000d2107801084500c04031541400203001c2c085d10501000300c1601d00710031a203c04031407216900c2040011a0f04524106085801a43e084850542551200c804016400364050201c40a219002c3c0f00007000400501070443c49121100c0c01485025031048040d081c8440104503008214911030180002020641391015080098030010b84519403440c008486d044007080c030380c00f01100481c02c803c106500d900118103031001d032014040c10089402c8251000c08040e500c150250708001d815440d142040c07c00301c9078a589590012407032507501c441000450b54150011065404001a03000055000704010a020b88240300200042851510700800f07500070329070b00c0c0c2665500c8180d4017071160348111300c0201c001c0700100220041d60707403440c02a0081044c1691182e00840b554000507103881c20110014903c1056102d901d6100c2031960129030100b03160000300c8031701b5802d00c0b14160 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 123260188 1250 123258938 123258943
    0x91707030b07080403090f081015080f030309070603090807020103020904090b01062601060801060f05070506070801031e050309060f07050601030f0317280f05070305011707031e14 79
    0x72002c1d5281c411681c00c0600b402080f01d800c6411903c1d24042c83c0c6020001c04070b000951641d02549803c000035850320449100c1d8884410341e00c00344030381c851190f240f04401004001980191800300071207014503a02c40040c0c0503600c031400e0180183d20140301a402550098000b4003c0760301c001c000003014640766481d0400d840d000e8010400040030207200058001a06400143c500641c0c40c0d2140700358503105000b42003074014010107080110b0481054542c500800584150300d50020640d1a43e10b8100c00040543e1400d11041e80c4441600f0345103480401c29480d1a000c40c5d4002015500d81645a02482042d620440c203811401c401040703170030301013041400000d0203144075100380c0a03000d00c54240140304090f000501c12203501844140f18804000e00589040d1400c8504c9440c00741d00340452003c01000191100031609081c00104100550b0551100d8143c81104009560207440038020303e0750f4440380e000c0102512908040f04864a61000360f8100442c82034100121a4035405440390 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 123261438 1250 123260188 123260191
    0x20d0e06192115060305091c02070e0a021314031b01110f0c03010e030301120f02040603140705130207030504050913020a03051501050411030402010c11030f0a0b16091707030b 77
    0x1005a80d410381849601c0810142001130400e40703014000b40c1414a42647c49a02c0204070300d13110500001100705080c02808a0300040417052401a0341d4a8103c1480d000307984071b25031141c000f03024258046104000011202c0402c4000b400800001ea00701f0030000c0d51500d0140e0441c1800700c0c60812900120080000b080c00354805409098207041d01e9051600352120341d11020019017003480148424030a1014101c1443e0308070210310080c0c40e65001080003049907400c0902061080003c07035816100c0010b60000711042500c0d007100440301c1d00c005008901480b80010001503003004100414039188851a0b00300d01801106010b9042035800a0270400d59940100c4443d00f0842500c0c8900c225050402d0060030107542c14480041d85000d40d03a840e100c01400281800303019558003060100540000e182c1c00c00207401c80d00d4030240c14810a940e500000300840c0e0200e10800040c50054144084800d40e400c1c6132a041e8406080c001d605112061030080b088107442480b000201043c4541e200c2ca = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 123262688 1250 123261438 123261497
    0x30f020705100905040c051c111603021f0c170402030f07030b1509040b040201050a09090510030b0a0219050c1c050309010e0a03050d0f1407050307020d0e0619 70
    0x40c034a501e001c05100c2607074000f00e01002131090074052102d110360040003200119403006030000f00c4580d924010049d901441d40c1c1d41a0240b2842c00c0705040503000107031502d00c03480c40042080d2005000c12100f00340c0b80401000340003d4400307110740b00e8a80040c2e9400c1d801600c01420350700f6450703620300d0003450131030284e0055509254a0b411702c2031003544c000044115a0040d118a02c0310b240640314101c5901024200034100100041c1d01d013519841380d8072601c09002d0401081c0a9400c260307103060074807490740c0010307141c41500c0400700e51140071509c01c403101c001c600220005001468001075441e6040001030132000c0c000c07000c0343e20481c8484514112075103615203034641c4a040465599003155110003858802c2d9000d81e00010109401c6426581c00c400000c01c003040c00b141d11a19000500040d01119464488002c1404541c1d500480950f1041120741d00300c034401c1c1002c1c90119140340c0c0342c908060304050104040c0920341850410300c92801030074109403c8425141404207104480391009 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 123263938 1250 123262688 123262697
    0xf030a0209092d030906070201031b08090c0d050a030804080409050c07120507050a0213020909040609021f0801060815120f0f0307200109030206030708010501031506020a030f02070510 81
    0x69540b2403c10350401a0011070605071501607007005403613601c0c071584c1d1842c1c2c40f070580131440354116071180d00000c10310a904154400600c10700c1d000a0540003050307440349650302a140c00090f00d414410b00c440d1041e07070010000c00d402c20141e2401e8a41d444060b009a5800204100121744c1e502d01c2d000303d80c010407545000301d0b5548018200350b00000c0e42d00466104000c410000413001c00d000144084c290368044640803024108581d003c80240f04181040b034010041604020030300071694880101c25000b6141c22880042c800d10001010006444250200d0317030764001800124440c41044e83d02c500114000d42c4407031440c50008084001c0c0740d80407440b6510111141c1c4e420300050003c40c3ca101c481c10015410241c09945032004480c0c9508000611040e40300d0980c0c982c0e1045d800d0400030340d0003800640d56400d00c0350000301801c000740901408a8203207441208100f210090100c2218680c1d800740c200940245d40440f1381c1e044290a2004521032458003240e0f0340c0d5002440c92240302e00d0b0301d4 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 123265188 1250 123263938 123263953
    0xe030309070602060115120509071502030d14010302010507030c03020307060e060619050d02060c1002030c070521070b0a1d011d070302010e01050f040f12111e0f030a020909 76
    0xa2400c0e4058028a202c0c1c80039011880c080358101050140329a111f08002c115076850800b01c52034506540c0c0104050444009034201d01600440240b41d120044682031261030190f500c030358100c0e203080c4402400941300300500000309104840520701180f00e40b06903841c2c00e43c1d030788035402030354148440c01c1d445070401000d1001070301d45005a4004000107505000383c041c5000f0005004811820b40a07024080026640304a110240702d00c0004100e0900c0442d180d04203860034001e290400242104e40c2d02c03c44c0c1ca810b584900324407005a03080d9000d035610b881d1014950f59110050301c0904003003482d0f07898406802000424481581c10500558000030b00741401d0800c08500c110142203502c1c045d00080c000340050317680901c0034604203100f82810350350782244814a04142c4116030122494a00120700400c20101c10340d842c403d80c07030085006550411613901084039a14808411760807055100e00500c3d07680c1090f118403000c1400090980388202e64070703004185485001c8400c07507440d40080e070 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 123266438 1250 123265188 123265199
    0x1302130320010f090b0d0e0f0d02070e010f0603090203030705060103080d0645020409020a090b120115020c030109050304050102060f040302060103081305040e01060612020711060d0e03030907 84
    0x20103020740400d2810100b0720b80000303800741180e0518040c01c1ca001c0400190b030041c00c051508040301115440742102e03142c800b00b005540c0c484205451120042c00b9403c800100c50100401380b0781604c140d01c4030003000914290007a00186841038049070140814400900821001d201d0140210700603141c00350344000000d0a80d040301c095401040341401c6006c5e602c084580713481141d911400100e4003d89120b42a41c2c06911076103004c100a0081e140009404201c1203800e40181c100e2000c2a1281d5038140d4541390312262a024075000c90300540c0d00b000040188070b404020520300806240140c64210031810b001ca0309442c182241594a0ba0000800300404d503070420070070307900c014a03640d0341e0032504103030354020b494130810f00c4041d1410b04003240c103540340142c501d81c80c801002e00500400040c41c071040b1240c01707403455210f101d001c01c042c99400d484145141c0216a01d0662084426a00640110412020f0f8121a980f0761220703a071480e00a1041c201000210300820385500246001d52810 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 123267688 1250 123266438 123266483
    0x90d030e0102070803160908160e0c0a020309360124173c01050319030309050c060309100c050f0703030507020a05030307090806060409030e13021303 66
    0x100d005a0240e031042000101144245080c0c03904401008803081c080c0d03001c04c9081342e29205ca90400a420300803c050242c1e0580c0256413a01210040000b00446a8640665034483c0c0900c0c080ca1026030405c008101031403401d40414049100794102d100520b1603003000d00c1c0d4040c2c2800c4081050107030b80100500020700007220b80220300d03105007101036002103800801012822030030004414021004041821f44107294469003950754946928ec103104030588001d401c018500b01d90208590500c000803e16003004601d811a9001c5c0044088924035260f4040780240b0110500380c9480c0241403034252030366100c02c001d6000b103084100a181c034455501240c000c9403010681c680901100308041c2099a5048096904081e010300380041c3c7c6a48201b010381c2848000c40008001340000010070200b0782d000300483c1c0c15500400c040758040d643d1182800211501d801010f00402d030113100310a403a02d40a0011030350035804d500c1c09400c0c0407182c1c07104640039070507400840b43d10801054001310070140 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 123268938 1250 123267688 123267701
    0x309020102070537030503030a021b0d021905010b0d03091505031e060f041407090b0c070e070207120303090b0c090a03080d11030901050103030207050a150c030306050405090d03 78
    0x1290110101d104590307144045564842440d420000041300c4022003d441c0801e40004642200c01e4960324644410541c009500494040501c02806984002c104000080c80c0001107010b800412091032100700c4400000d808200031100e039900d8100060180d10340b40c280151076172098640c01300540c20440d40d03031240000c11a0000c2000418000c008240d002c0c0001510280c0c00e08110829648903240810200f20b07000502580040c1048030703440e03451602030589486103481c0d0399464039507030f1140140da0803842000728400c0e0650007004248807680c10b66401941003402401114201c41da5005851988183c1020940c007007980c41c81c5403030038440b4945500d580b2290b4044c0a41c40c10f03207008002896001d00340005861000041041501c15405501c1000d01c42501c00207140c580c50b01a903198040c120034017040b801400b071484001000d060840d100c8050714117040da11000b80845410880c1ca44601040a408064803403e0002d4280c40d02e21510b80107500c5071014101c2c1c0c0e58101c8001d02078544 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 123270188 1250 123268938 123268949
    0x601080609030319020901030b09040309050916050d0c021501080f06010f03051009030203090a0902031506030408030406050403180b0c07080f100207080c070b03010602010e03040609060e0d0c06030902010207 91
    0x20400400c50903014560f8054644481c2c1100146c598095800480c014110002031a40008550003030105040e045010700007214012a02d0300015900c0303540100c02e80e4580030088010540c10f1200d0250030b03546801180c44000248119914240c0015884280100c2079100d070081c0e4101000310101c0960034003040d8050010860302107400e615640c1e071142d4a9007002d240902c19992100c800301054402d20403103081e824014135030000642c40e288003000a41c01590940c071a0042c0c0f0301c19091504007401681d1055402c0401d60b4110796031622504050703e0014021000c0204602c41c69401c031009800781c6000c0c0413243c01d117035103504c1090b000c149866140d8001007417542c81680160400d507800140901c1661020102507191582e0b8540340e8994002c05a113030045003e07100001c83d414081001442c12541140c0c000c2c0000c41002e0440c40c1c481c801d42c043c10300000c440801c103000044c000d15110341c2d01c0402801400c4030700540d84603400060415042000000c0c0c80b000f4501c155a81040414044c09 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 123271438 1250 123270188 123270193
    0xe1908030403150f2c01050103020f190503010507110c0301140f0a060b03040c0311010212030a0c02010905100203041a060904020108091e0c10031b0804050f0601080703060e0d0801180b0307080601080609 89
    0x14127540018031400c94405425214600d03c4002d0301c0b201505100761801007030050000c4c441801d155074058410f00c06002240242c1c480c5030b11528492505004900e5901c03008900784c00c080d1107203201e410200308002c0400340e1843d202c54000442080e29001140f10360700503052a9100d6045142c050820380080341054110740c00082189911510780702101c0d0484000c44000401c00d81c900c5040e0b0151608034805040c90040448460b500002e503002188a917104188a81d25900c0091681c1e440c0030041d00c5046c0c00120003000100194083c800264108102400b2139141c2c404940d0b0022944400302103003600c54001076108a01e5050600a04c0e10319691405c05110804014170281d180040300303070003181042400310100e02800814810300344072401680c1624181c4d07840d0248503a0307075034841c407040703800310315041203d010404003144620b42d0410710b60750120980d1030103c00350004680e40103a00342c0d0075901c0342510201e58041200b2002081108054446c542c0f4164103141032800c005d1200803d0b4 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 123272688 1250 123271438 123271441
    0x2071416050f0d02090a180b01030606060f0207030c05090c12100f0602010902090a05070c080d050603060a0e03090f0402040503070e010e07110d0807030603120e1908030403150f2c0105 81
    0x1a519009640e40c01031b0544000903203100b120446054140c00104050405280d90002009200d2107400120a84415403a5500c503c42110012a40c3e04694070002c0d04005500d6000c0c880e525021041d40d4000f01000304081c20700100d00e14109201178261100032044041ca28108850000c02c1151001000c290008102c03c40711600401c0007020002c1521200a61b01c40001d16514000c3c03c1014582d5001031010742c90340c840e41200c0780285030540f81c640c0309110340c0c00042c08010bc0350280340c16121501e40a1030034506d0f480f00f8005007150b030801042c1d0050f0244404121610200403040041c1050440d404c0c0039490310b4010001458090640400c1000185070b81006410014600d9035a0010346030000c03003561801300440c000c203c20707000180300c440b070080c0d41030781e050340200d8031441101d04891124189504540f032210048491041d201a6001480200082111848100c44d03090101101141640210b5135820484104080d481ea0390107500b0b2101110040c0368280d01d130350381c20010080242c1d = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 123273938 1250 123272688 123272693
    0x5040b0409020304141c02011a06040b0c010e01020a0302041a1e03071404030f03021c081617040501060f080d0e0f03010e070605030a0e061902071416050f0d 69
    0x10310a0340180c00703680350000041800c0011a1405c01da038050342e00103503240c1c060300d5101e2510301c1d10320344000801982007019a80d039105409a4400d188803005021518141c0380580c8200650080100ca841d6550383d01c601c40110301e000c2c00141454405641c0042e079842c00d201c11410002c00c41021a05145418000c40102c071703600c1e01140d040c20500000c810f440f562800c804440c200c1300381202984880020600004000c08810b0b0480c0542c420b40a407140403e00354071082402c5041d00b25800011207210116280c0c0520809450701e030300140c039200d6030340e29102402003034508040d80c04580c0b40c2e56640c4200300b00108200d4480142510101030101b400010744000c080c046221115841000c89446114041da4254868000d542042040d90300c01030380d822000e4110740045850080d0705040800303000040b440450054411042000340301c0040380c2c15561300d0000c3d040701c0f50450305402c13650800b003280001084110317440c1034030030301c8070446a0130001401840e92041e034440b402601c4186c80d1400 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 123275188 1250 123273938 123273959
    0xc0503040f080304020607060908031b0903150c09060403112704120e04140115030207020a1e08030309210c031804110d0b19050d080a0504090203250504 67
    0x10302d802074000c6449131030300c1c0001409031240e828002d00c0d0b245419845010400000091031062506080c10040781a4101107080c00744284059076070b2581016080d47c0651035448090398004650183c10b07420001d41c0008250b0b29841604292003240030b4502507801440c280c2103404582441210211500c0c038903c000346031107200a00002e2000400d80b89101c0010701c07500042e000181d0061052008480400c9a00aa404203000385101d010410603600d001a009000300c0390460350250180703a0180c40d00d50548943c200c88d000c185c80748140d00e0300001e04080d040018501844600028101c80307046012507510b075a40b001d494803588001800003a034141d401109964000c02d12280d03100b40500d8060029004180f404814045050040b403000c0c1c00c0715035548403441c0300c10140d6405542c45202143c0e00e911407803a00c41c0301e03442060020a4400210120007600c40100b05080c1542041d80310704001060342c1048800142020300c18401041d0082c2108503800800300c0703402c281d49007074288443c007003 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 123276438 1250 123275188 123275213
    0x1051e0403030506030a170909060609060409090f0b01080616021209100c0c0605040f080a0f12020307060c080a140705090d0218010605040f080105070c0209060415090f0c050304 78
    0x74145a43e600c0010860348050010003100d1f5400810016000f06030036100d400d90b001162940d0054080b18005101c0307003480d00441c2c070f01190003462942003600d846c075900c024200c000412524429402d10700c0000800f0030f60703002c0c06850324030058601d80c50044201615a40c24040c07240455200078200d5056071054405c80d042e0704800d03602880c44404c2d81b06c09564000d007c440082099041590014850368818090404c5c0c45840f0205007041da62140142d5540c0881d000c0034003420074041d18503001401850035043c514009006a074200300d00741c0c5400c030450307450110000215401300100645490b443c425100705041624640c081d07810a00b100800a00401155a002d544608107078015507031207020161510056014942c0650b03100d0f0401800b58120b840307601c0840c210301001184400c07040c090148140c540340d54040210700150200003a802018280a80065541c1c002514a9512101c00f1000e000b289001180c2c290b0b00d40c0070788007103480d403500b0101082000c2c811702c00000d81019008 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 123277688 1250 123276438 123276443
    0x60a0908031b091f1202090907030209121006090c03090308070807020a05010f0f0606020d020c041116030c0203061f1203030e0a1a0a0204050d06050a0204210501051e04 74
    0x30415481202e494041c0f44160301c1e0013a8000d000c02100b004210020401c901810b400c1d0b542c0700500711410840d50281d00510f001c0661000001c40082e03403040c42070f4003401c1e07040e0f40181a840312480fa00507440c1006240303000e07030f002d1b03a0f2507450602841015004851442000b841c0820000d03030551030040c801c503c05014041000040d2011840c01c5208200065101d50010001c10072000c0300035411000340420065070459505081d4000b80050000c5400e000d21181c81c2c000d40b24906510781004010807810500c0d20841000348816a13000712501d541c8183d2a1080d11140800300150040500d0104002d10100842000c45020125002c40000100443e00c14010b108900d840310f10741500035285144a9007998401c0010300c030284800300100b0051600494440ca125880d9034070680140d06c03650003100c1c1c10010340811440082c0c041d611003603012003500c60041c20580c0300d2001141503090740b0100c442e040b030800101c40a2010a205598009003119118140c5043d85102c0401c2000014000f = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 123278938 1250 123277688 123277711
    0x504090c0c020d030e04110a08061201110d02090406170c0a0e01080c090a02120405030403030f02010605061602030f070f0515030403020a0816080a0903030f0809190201230c060a090803 81
    0xa050f880d2600554071007807c0040b400d868402c110401404458111210340c031440b00d1200c91446414188540503d0f06009030038107260601c4042000080d42c040441c1c2c40e007060390340c2c0000416800c001500c494951042004c0c245242c00e600c00c01040d0398194000c2c0301c400c1d00e90001000729a10003e1074121420055a5089841c1e892440000090040c8022010080045401c000800402000803c01d0b2446902d07548104810346104074200c4419004098222404120040c41c3c0000034194400481c0300504030b840c0c820311000c00a00705081039100c00c1400401d404c00b03200c0380ca00b18081d4400f04881520241c114549501d00950303400301590302903c0341d040003c01c44080800d008104048941111041d03980c2c40c0c50003001030254015100540c005428405060f4100c0d02c038800c7c4c04d018402860003020350110442c1999031800341e403d000c80c140000702d00015441c000c00c0c4d0800c121801560903840d00d802800444a0501e0b0000380300c0c4806a14200b02d04000030729050a507500014180311 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 123280188 1250 123278938 123278957
    0xa0b09011203090308070302010203040203120c0705011b060c030b0102010b0d020d06020325020c0109050103180219090501030c080c0d0c1421250501020304090c02120a0504090c0c020d03 82
    0xb0140d45a003442d800240048000086d0a014590150001c41c00f03a482541203034000900760024010a00811101151540000008020a61064001c00e1504075214102e143d2558503541c2c100403103400d041c0078808251039003410700042d1b03020310039003503080c0c1c1c1590713007580c0303004c00d0f6000500c0707500c010000038002c0c0da020000c00c540429099461001c1071041c0994603484141000182d510072001e190980090380600001c80d03e54424051110094040d14449005040c81d40c01c010786042c03070000c202c040028600e0001503004083c0a928002c0d405030291071243d50078401c00c2030401c003904026900841c0c06550020008245c0609042102c406c140101130f40444000011030382042c1e550040c8520580101c01c0461403804261a0540600e4510410410b1448420560f41421500c203503800360b041440100300c040416081203400e03c0503881034403482c03c0340380341e10040e83d0403c40020000a01c0424240f1800c6118441c00341096801e0a2194004030550b00080c0d070703034800001c001c0400c0140344 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 123281438 1250 123280188 123280193
    0x1209090c041a030103020913050c09191d1006051e0117070809100b0f010507020409050a0807050f030301120615050405090123040309060c0807080f030f0a0b090112 72
    0x40d240070305820b40507500c00841c074904911160304280400d80c03007034500c94003242c80407020f03032242c0c040f8030740c07250160039021b8004d0108403240380d000f4940c0d4005d880341020315207010010302c1012111550781c070304403250040c907123081e9142046040c1e11080b610f1800d05c09000c0c6a0752405032030540c400b022003502c003101800d4012101d04a01102c0960a400312800b4840801d80000c03440d44543c503c50210783c001c0340b0f07008105003500c4009054603000404065151f040394070035802000345034005000440c40340d206940750b525100c0340031020f45400d4000700c1c1e0352040100030b01a14016503141d900441c115418440c03002d1985000d55070042041e030741d4803800b60f18a6850740c0d01c48014040204100468030701001003d020704a10080507844941c8080104005906040694020303034241e80d401040d06c1c00d000b400c1e01c520144082c25211500140007200000340400010110008082c144903241c0c1840c1da00c40d064418042d0028100504140b02c102035500c500585a04503042110132001194150 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 123282688 1250 123281438 123281461
    0x130e0a1e020313121110020a0f0801030210050702031c0203030f010e0103020102030d05150310020c010b060310050415080a0312050f09060c03070c0615060e060705030703030f021b0109050d02120909 87
    0x1182c14a41400b80c2e440880c2d512100347d001c1c001d01c00d52501c82141c008458102220843e07004d010080d400041908601c221034803500141080b2840a8100c824402d0303105a0214500308101213000141d10000800040c1d010324a80240109600320000000c2d50540c1e002039201d001e2850218171082d42c0d80d0000302c03103120b840e84046102c02c000d01550104049104c404010b940204081902c641c20400c0301c0002d0700b00201200d00c6401c68901c071201c800c1c00c042c10040505010740a00c205a00d03c40301c04110300b14140500d40f01240310b40c45580b0300390307100b418010680c5c0000b0200e1400101c240200504000013203001c81e4020500e525665885e40c41c0b40040e200740781400f0001d040d8a241805580d03103902400046000e46039151940185036404c4000c008052240c0d4400030101e0b0002e10000000a0090b0090441400240c00150400780c070300c02e0110026920f0070114038607a4462a10800b4808140117201e14000d007840644014141a00c8030b4513503101c3e034468680a078501074005010035106 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 123283938 1250 123282688 123282707
    0x61903180210080702010510060c020409020402070213050405060105010309050c101b0506090606040e1e0106031a04260403021203040e0420030703030e0105130e0a1e02031312 77
    0x2045100d80b0070310518000c1101804903208001340d8a8a00403581c2c100e1030070166821140c050f515001c402d9140e9007803102419103060100e8105409101510041c0d85140c04a612104030110010700d0386001c1c06c06c00d01c3c200c01070707001d075040c140b800100c0000311300003090030188080141c807190103404032a9400c0700d603140e9011415101e07804070360b140340030450045072860188002004480c0680c4440d81001300b11040c6c06038201090b8002418540040c1031a80301c0b50009601e4000091110707503a840350501581c0348892400c2c000107140070001000401c941e811048442c01801225502c1c114284500c1407081d0f00001e03104950440e4000c0c0002c03001c00c11100606801510a06142480d2030284181e210404a07c0c865500c00c030383c00701c454100002d01c84102c1e0f4156403490b40f2840340d9001964240d008a4402074204075800020904180107109180a0021814000307845000948030304151001500a0210940100140203281c00c06400c0c0003250342d00403050100d8100707160780503a1403150 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 123285188 1250 123283938 123283943
    0x5040b030c0402041203030e240405010b03060c0901110a08040504090606031217070806010206040305030903070f1101020c061305040506010c050106090c0e01050a0f0f02070e012306190318 83
    0x4000c10301c0308100c0d0040403030324407071f40b01403000c0c1185098850300c0716600b504034584d82c40d2003500c2002407041015040d820501600002828001c04030110341070001c01c03034039203407503150028180c5039650780120005400458980500045d10386661a170001c2d104900c16544565111241d120a01015500c4003000b958440e11b01e41c0703001240d14002e0421000c92940c044031a088200090316079010700c00c058401d041c141d01520455503141e074141e8580d040644240035612040c000c00e00060b98106001c02090b003c1c418094488265400081c03401c20b5184000e80502c00c240700c00c8620501004814050313032005c81d8080303956603d100040380c40070b040c91400751466081ca0000600c0c02c08580c00100d80c3c514680e01c0e1f07166450b4103801500d030b82c07044d02885070000f54004503882da8a4803d003e5000221082d105507000ba66494141a842001c00c0c0c1154620309070b05d103555481c0030801201010790b51000d4a12504081c0c0580410561090030009d01041c15240d9003030010380d050321040c1844440c3d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 123286438 1250 123285188 123285191
    0x12d05060a030f0213090506120a08071103030c0709050108010b0d0209040317010b03040203190201081303090b04180e0c0102073003050a0f020f1b0d0b2a0301060905040b030c04 78
    0x801c1c1c0b400070103825401b84200030080b46000042112401c0514082e900c8180e85001066a0010341e82c0d180315a5116500a41d086068100350008550b01032004082c8074078044004c04071541030600540071100180e025043d04ea00d4600c50390015140c40380d0f5035010b00d8045038103440603500e81c00c0640b0b1040c0d07000a0700e0b5a40234140000301c0e070540c0c0c290140d40150700a81c11100541c0001d041601d02c8403c811010340442c1d1040300003041800c4010381208035034424582607051980d070321165405a00035800c151007601c00d142c809001005240308205070f0031021401001044480c400207520f540d11070041054164002030f101e0586680c0e29500d1104038406001401e10440505004029820020200c0001521600d910080034400940e10801080c01405082d00c0482845064804040d40f00c0326600403119203004000305440510715481901c06031604401c1b4601280481508800c020039002445828001400680d920441c0719081d540c080d1000550b0090a500083ca40f50444c541d00768440e = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 123287688 1250 123286438 123286447
    0x60b0d0302030c06090d08040b06040906050702011a03060106050703051315121416051b010f1409030307090b07080909100603060f051005091c0308012d05060a030f02 73
    0x3550000040041e0500681034888540b2807102083e1240141c03250719001610320804070b40400c00502c0c06c030f50440401000007a02081942c6c5290684104803000d01c0035175500c003d0500014061407084081d190120041d045542c14114050300c00c0c01580b070054200000400e1190603142daa440380400360590b003107107010316182204000c014008460bc00c450071418110741e440304102114484d4020000c00c50309292814945404583c25044640903080c520304800c1d0152074244203125408200030480f00100300e40c1052403000c4080307070000e007074600254000c00401a100ea0320103141c2044c1c84a55881c990b4615050400400364028103005c164080b100034103200d080060507070100c0c2241c68546060225130b80c1c80094a00c03c428901c90240c008070528041c002c254400c100800254100400003414654440d8080d03c4040c00031104034045145403005115100f220114101c000c540301da100d15240220126041260400d4414503002c3c3c41c0203d11224402e00130b420601d04100b0b109000c5498 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 123288938 1250 123287688 123287693
    0x11433031e16090801050615180402160507060f0509010815030d030b01030501080114011206110a050403030315080a1704270b0301050c040e0c0418021308012304060b0d 74
    0x85620380d11040b000700703800c0b90b000258204c1c180100c42c40b50710010080c241d840d1107003c003000a94800d05042e9804641d0303251403c9190354038809007154452007000c0a048904c83d1034110314105142e0800c409010044501d000695440b008580000b030b02880c0804240e11036a680c030341401e903201200f640c140107025023940200d030b042c0d000342e55147d0241c0c1e0910442e41c1c0c6000741401ca50071441c074002107612510052000600c1c451440320094454100019400c0c900c0516440c40e03045100751000060000900300203150703060040c3d0342c09981c1c102c0f6402400d45040105552501130320802420210420031402070306100340180d030010b03c0d907101c4d035100c03400307200842e5407088000380d501c041401d01c5c2003201013050074144030f4144102000e203042842c00d8104500d00212001c01810184a40405c12000c1941003440600408a0a0035000541c4803561070080c08200d04e541c0c0c110031241e80c900707000305c189283d90b00f075180080e0154101901d602d49403401c2070405020102d10403034000300b101012408 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 123290188 1250 123288938 123288961
    0x903011808030708071806110307050114010e06010e06030f0702120d150b03040804051201110d0203060108061203090d060f0c0903050f010c050409110d05011433031e 73
    0x22074060b540e0313103040035924594140c9401c240e440802c400b620b00c01e8010b005150141c80840321203a0040f00316030501105688090a450100075603102c6c0e8510790b0010840070301207512194005109081c0010700d00114804074500b8000141044c0c41607030348102003404103000f4447c011f02c1032000188176554446141507403002d0003c803148100000560040010712072a500152402246c2c05004107207414502020005528107502204c8a01d5581c0e80e03120034002503440c0103143d417018070100541c0f42c0c50883c001401401c4001c2520303004810344903e03041c584602004450004804880c45128030406092480003405000010041949801c08820519030071510000c1204c0c03281c402c650f100c140100d906400e90f5180194140403401c10b00c802e10160545e40c010301074010a00709170600381070390300c1c500c80d058600a9000e61034000f0410030340305c40b030f051182c100040a504000300310380000310b03d210109248601d80480c8a500d8020011031182419a41d1040102c200768550101e05d080480b0000d1 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 123291438 1250 123290188 123290191
    0x4051507050d0f0b131b0305060a081501210309030201030c1b0602180a03110d0f121e050406020a0b0405071805090c100503070c17070503040503071d0c090301180803 73
    0x910800070008003c3d01c02d0381c07900078541e00c25150b85040402900b06c100c19406082c014181c81d40c000c20101000c0f503000740c108022402407000400500701c55140c00681401070300b150812400ea0b0340340d01c1d40c003008242c00c20100d90480c1d03428a80003900c205e14160032210581c07140c1c01c8542c141c01040e0941c0503c0241e0300034114410300e2040e2103404550040030854080a648401010020345d40303c0504140b4202c22001d4406001d4507041200045580d01c0307418083d4010044804200390300d0400d9890701c0e2034601c80a0444560410b58541400c01001a44e20b0002d0080100000448000141000400d00180e0300a0841c5140300003c1072201d400400039020464a992452145250703080140c90454020040c0244640701d031403031b4dc0c4505c0411106150aa00152050700340603541546023840c10008050440c040d4010350b840b68107000801d824100a6400064080c102006417110100b80710800d941044805150b640d5410986001c01d000d84907014840070a00c03489100401407080400045 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 123292688 1250 123291438 123291461
    0xf0a14090316181b05090310050406091109220602070506010602030d0b0306010608010303031a10020307020a1403070501122d0c170c090f0904030c14030304051507050d0f 75
    0x55408148044140302120b056010244d0401d0030103804061550050f001003441030f0b40503054640c0000305104a906503a030039a42154440c0e80c444541c414414841d25541510100300c51014003420071001140e50b200803200e1418202da207407a01101044226412a0401c0380c0c08000e803002903035949006512500441c0c0c95080d01070510030308210300d01d00803540c40e0607144552030321856a400c5072811070040501c6600105206411490000e6550343c400d041c0f1040c115a500850340c0d007074944140001148c1075400303034001c040d0b03045d02d0840c5941c011501400799602860404983c8842903210f401904060b103001003400c903c01d0020401500c1c040c001030292400325010304c90000141002c0707401011030440055408440800b00b4240000d02006200c0900c0c024101c0344800d9040300060712800d0262400c4000c101880d4103e4104554650f05041080e000703030141d0b05600e02500e50640740e0031216600c00c1200d4036030340020742c55400344058810300d425681041003821044058600148141082e0303 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 123293938 1250 123292688 123292709
    0x2120a02040302090411300f011401120503040f08063102040f020904020d0c08010e0c0a0807121d0601090204031505040c08060403021b060f0a14090316 67
    0x14642500a00840d07044035030241061409940c0d41e02c442950341c421819150344242e6600c80301d804071440d41c0380e05940b03441c003401500d2500004000341d89007850b280c1d1800110f90401c6100101711012400311411205030766040006d2120070b01e0428203610a9420050117000750740400318501c2c40c0003400030b02c111402049a044c0a0280901225585070401c8a00403041d4600c2c10b00c00505154210f4002e150f10b164015090048480005050341c100340c1404141d1540c1e5074140c001d1682c004c4655005180d8a0004d6900f410115240b0407140f2603005000c00780481100410340303441c4070300000741e41040904c83c2000f07400c1c880c074010358100d1001c1e60031103114454000040b402c001c0318400c90381200d602440b00544440c000e80b220300a40750050041e550203010b210009040320043c8140c91255100e035000d0306030700034555080c01f0450850700c10703e406100b080c8641507007154500200c440c8022903003080750f60303106402d00000d0389205d4220b0058260180080403d524a43c0405085c15900c09851 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 123295188 1250 123293938 123293941
    0x20601060807030207120f02031309230403090608071b03050a02011a030d030b0d02030a0c03060501090507050a030914070602071406030c091903020a030c051215070e03150a0212 78
    0x100f107041c1d000303081c80603140e0005031b0414003080b07019076124400c1a0250043d641498000109030025020315440400c51903100d90400b003025601d1540c0340d400c40d0034840400f1090915860061480785180580000d0242003c00300c0d007118050b1050041c011210b40340041085417529004119400180d43c400240d0b007802c0700781c07000c922050700e806981d03900640104900c01110104038082e087d0301c900030360400998400707580503071818050000030900540c42c2d13071075085c6075207080c400f191016401240b90600d8001400402580030342100ca406407185008a01c02c141800d142c00046900401501e90f485a5000051202e80128041c02100c41142c411021490440c01b80065403008031143e0018500c1088000b189180c07020604680c4904c6c2d0000b17880303a64503a4041001d0061a400a6800d514030083c10043c0e841d00303002c105081c20800024000d8400e210126130031029001c0d01d401d0501a02c07903400701ca01e441c01c201805003003100602c07400c454240002c0800c000c0d4004070715850007052040 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 123296438 1250 123295188 123295201
    0x403111201050f1605070c08070f0603020909040303020d140f060f0a030b0c0a110609030415020109020904140109020d0f060506010503041a07120e0f060a0b1f11030301060206010608 80
    0x8255031103043c100c800a030003913607000341c90000107030400c03001000d0020034801c1c080410103141403213016001c03801c0200b6425041002411421810754090000c148c01000172080c291a8507c1c41500907a16081c0540c5074201802c0d030601620000c2004d810140b010010071551501d10411b8030302807841900c6201c42d00790000c0501620541a001c040c1280358101e0200f02d03162845001811110b98610301001e4403400000341d01d0130201d05460280b504da00100e401c0c4403401d12060560b806092a00007004004c0d03060b800304190300d400500c00f400643c000c0c0442c103030207002034100342d581f107074020300d1025880210720340300040e89800c5009803940b0b032074500003030b0455000d10201c0b80501d82281c0c0f03805011002046680100d140180800f0030044007005400c00c40c0c0c1140038480c40f402c860727805400136000d0340c1e91080c034003840241140d2126040c0650000700780c451040000d84c05c2808040018034002c85141030742d00524a1002100ca40700010000070940d0713001c202c207416500c4c1940c5207565900d802c1c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 123297688 1250 123296438 123296441
    0x301051501030509070b030117010204170f0139030f0f0e1b030a15090c0306090516061709070e0c03070314070801050d020a0801020c161508190b0301020403111201 72
    0x5006106c0d15041c10001440008024a40c040f00c5144450016142585600002007201403882214040d988060348401d00d2440078041c00e0304884040402d02c4008105a600858a2031007041c044800c1c050002191341861207a0802c00c51409090414000b1100c0406a80020409248441a1401000138807480c0c0584aa40c984007003000400400c0c0c0c41415881d42c4001d003082c0300400f00c41c0c6a4a984480c0001d01071030000e001140582e400040c3c0300a0f90800500740610004000c00c100d41440e001d004003030700102d14985550703c0b2060b400036a40d0306071420f4500f41c0145c02000c4102c00c003034100f01000d20f0300b1f00111300c21b80041d034041c070095800303040a00c4001002e64401020402074070051015003000404a00c05030f00051610400c90341e02c410280c22a0f108402c451515003085071152252050390300c1c0140241b260842c902d1000008510080c05a00701400e2030390308101c030b100c0340003040496030090901d030400103000711356440e500d140040c100002c050419021708580c0229444e0080103 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 123298938 1250 123297688 123297703
    0xb090d230c03030f0708031003050a0f0201030c02162306161e1e03031b110f0c150a050c07140406090b0a0506090607080403061401080a050712030e0301051501030509 73
    0x113040280d81008041d0340e5541290704000c2002c1814050402d0010124204000d0710380c20501440c6c81200c03103e4680001006e41b80d8500c201d40a55220f0039904040c0682034001d1421245d1072403200700c42d546034035408040e001250034035642c80321000c1600c175889601251103a058901c45d580d00d80e0341c01501c6490b01405d522001c1d014014a030018980750400c1e4402c10000c1c5031034481d01d130010710425260340031840350003400c0c0c0c01c40c0041c4949030349411001d420030800b020340d99190b00404c0540150400107100c0d40500c0c8112609940105200c0005401413060f00d51101c2500161042240c440c0c81816900c10030081103403090b41800b0380003602c01054455040c04420281444805502f048140314260344141c2a20307030002c000700700103400b060400e000703440135500c18030700418000708050a50346500b0060300b1079140c2e5041002400700150002810714111212181e410701654110304080c3e807100741508080d5015400c1c0402c008485506403660001408240ca0400191710b5501c0c141c0e68070b810307 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 123300188 1250 123298938 123298957
    0x40606080c1c1e0e0d0201020c0c2107120b0a0b030318010207120f020a06020d1e140301173f0d0903020615060909010b090d230c0303 59
    0x104100d03801c1000c000c10604544619001030100f414981e207080c1101d000311009503841e0003665488500141d007400d0103900c0c10381c25184029030900d03002118081d2601d85500081e0f20130142d00305000710100130880503d8400751600c0079103002c65900e903a01c11014501c020700300c0300c084285e0009413624419100c1d10000e070328054011402c1011161154040c2c6a206042031f05600c00c45400040e90000b109031100301903c1540840082202841804418881600104c0654218030700705910154000d002c1e001603c0202d440320051400c201c4c0a41c0e401c404c1406000c0e510b10000004507075002ca64801541c07104465003214480c0184010003190700c540d001d810003400b540e150760319143c0007071556021041030301c4000e80d03490003c2c40103e8600305e4007036200807805600800c00700410454821101100c1c4101034450600e0f1508d15400108902814015008a408003207085909a1201d84024444a601400d8040003004820100240d051000004034241c491403004507000d05022060340d42420 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 123301438 1250 123300188 123300211
    0x90602060c03280c09080f1b1302090d0606081b0603070e190825050d02010309050a020a14030c041406010c0f050a110405090307120e030a06091104060608 68
    0x111401c2452400034281d10111104001c01c1c442000021201e10401c134984481c1c1d103d40c2c0c003040c500704135142080d000e01d880c010550403401d049904000002c4400840400841d0280149100b40c0c103110020700a03901801c0c0c1016030362000302c0c2040304660000c020b503040f8000316103c072249007c8459002c642014100d801200c2400419440d5024810308404d51800900b840b90700700f4a00782a207a4a0341c00ea206800030b52000844041d140c0746406440010301d08201c64620203401c08020134802c07510b040c0000d04056840f1031400030301105020304460345600404034200c0366920440e500c40c0944001181d40701c0d0240403080746982c54940b02e40301900d00366810f59402942e8a07401500c0d80ba4001740180c038080341116130313000056000d01c040a1014442c10740036207450500ca0900044600050500c42c181d401044640c0200302e2008008a11040e1403601c00301492080d0f02003070404010000092045040c60101010450355118048041034155800c0050b950b481d00101c0b50060191001c0540343c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 123302688 1250 123301438 123301441
    0x304060b041e050601030e120a080c03130f08042301030609021c090c030203070e0f0a06050310050c1903050405010c09050108040305030603030f0c010207140c13150801020f0307090602060c03 84
    0x898050704580c0d13001805060000b0003044845400e41021100810080082400613040c000c0c0c81c1c0189455070040302c008a0a8150718144211040e01483c11401910080b4444202c004200b5414110341c040c1c00d1607140c4400c100142c0c0526040000a00c02e600d0210b0300703001c0d010071040c040d4030076129550110190200100d40900c0040700529400780c00f40c0d2002c01506005c8050f0728104802d000602c00c250707105545181040146ea40c010000d4204001d09040c41c504009940d400a60300d04201400c81c0000342a41307910171610300303511455041c141c00750510100c019419805a216a2103180580000e104480200d003040310440e0250042c14082900c01d0042404248204e010390760003038000c2e04580c0b03001902640e0f0040764200552070082690005481c50401c1120500e201903142420300905506042d00c00043c22400e070309900c50041642c403810344400314298081e4400a00c0c00200031560b40300c48110810442c0e004607803200220394410000205a84001aa0303449409089600d0b42503 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 123303938 1250 123302688 123302741
    0xd111207080c07080303070807020106050a03080f0a0c0c0b07060f0203101802070f0b060f01030903200a02090103060c110c0307051c0c06180602060606031305071203050304060b04 79
    0x80c0c2c10051500c400c80c0b140b8500820441c0c0200b00560150b106070b100c840992074102c030003e09503413641c4c0115004003100c810030000a0100800e840548800700d000c5500d44081c80001c607040c020a000240c1640c0a034480000c04c04034000003499014092101070018400c49040344042e40310a0301c00d1820070b03594010401010020301b10781242d071030035403502516200445c0c8410310558503151081d144a505041481403918200086142c1c440081c2820721045490362005000340e203800940700920040c80500d064500741c00d22510154a500038480f4900f0358407424040010320143c0d091001140c00030a49401003480050103441114000300141092030504051001400400a1810340c4280700c1c041200010700c090088005030250356912155840140f82c118121001750703002030255044041405a0341c1c81c0e18040700d03070052224540a0454101d482c10614059099011800c640c121840e00e00030154880011405a4056401840281c01c004108011110000182c1e0b11039900845442c14 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 123305188 1250 123303938 123303953
    0x1801091808190203040306020f0a0e011107170a06090506060f03030f07020f0607120c051e060f130b0901020405010e040506090612010f0f150906080d0513050604080d111207 76
    0x4014035205990170255656102821b0fa0010346450300c5070748002c110142c180b90700c60781280c0141005d02e03140844055030300195842d00218040c00094980000030300c82c2c00b0a0030030045a4041e40040c080280000f1420020380703c3c081a1381d0719218018901d6040414030b00001910016142d10b9030b401d01d010381503801c0150000e1019411a0000820b00c22000425441d00b041100712030303a92a80030300c11600349801341c04c00700d240c1d50b01d0324005202c032070203803051a0004400da4041c4503803010f94801c0e00e40070118002d20381c0116004200014a40810000440c190040d000b01c2d038081e02d4841040c40781100704420b490044034030700d070801d5444002440d0f0340303424044e808210101c4400000c039180c0480300d901c03c0e100d990501144058503016034400d280101d201040040030008020000c083c108481c0d103440b00c40d201007030070070444003058118484468156004c01440b005114907a41e50356807220b2915031502108044c0841c40a4a804840d06000304034440d905200030007561a249056440c880c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 123306438 1250 123305188 123305227
    0x408031b120f030a060605040b090607050a020402041d070302120f0a0b1c0c05030307020604170304050d03081801050105030d140d0501060801030203071508070509010c021801091808 80
    0x60520900349a04000d5502000030144030703440300c408983e030389841c042400039100240c0c0850208001004100040c4400300c00fa11341404007140d03041d94a65007401c010f41340a180705c0c00654881d100040000b040da022800c016015400000d500301190786806042e0100d005040807981444243c00001e0185c0c0071000c50242e21900d90381001402d49818008124811003207100501e402103540c030b124050118210300e43d03000704030403030040d4503045c40e59011071514080c1d88904121440c19200102038540c0500940e00a01000340802039403c9007814000c203009416210514541c954200142d02800c06000300350680d50f0240080260003240071b0f00311354055685103110440141030003890410328150043d40d000305030950b0b85000c0c2c2c3d410350041508000c41503005443e1050340841081d0010f40141580307a00155608140e5203c441410041c0ea00c070910380e5000358040d07840c00301c01c0c801d02c203c400c1c180e05840c06c0040411407105003280f040d00f80c030500d50025004030010b0040508600c0c1c22070a84 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 123307688 1250 123306438 123306487
    0x423060708090a0b1501030f0e0c1009120302030912010207020109031101050d0f0b03150103030219060e03030702160501020d080402040f020408030d0209100302040b4905010b040803 80
    0x8503c07240c0c042d141ea45503c01d050b80c43d503c400f0807040c0060714940e814000c0000c03841c0380c2581003265945407a6280d40d604143d4000a004103040c500003407116000368a04002000c92940d0070a429042d031a0094590f40310403a031602c0b407141a141e050403000c0c14402d0301c03142076060710f900c070802c2d08580355104101c0c48082c03554104901005419100381c16802050000307680d445020860a07004000c040c14020000f482a000d08088801040441c0c0d001400d079249044c504d540c41e241222506218000c3c0400c01c8569503240300c00002e2000e82d17680004e1440c0d074018091040c80269459800481e15151919402e000141c0101c000c42d0140c81d1940c016503001105107001840d150b62920200d00707582150803015502c55003c5040b0185080005544481ca5954a0f0442c40d0909000760480b031802481460f800000e450174040030848000d01034010461409c0c2c000044a941c211560080004922402c4000c1400c0000001315080c020054400b503601c0c8001440c103040c4840d15021200c5400f4109 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 123308938 1250 123307688 123307693
    0x305240904050c03010609090209061008011505040302040908030601080603010e0307031b0215040e09010606080a0b0d02060f0405040b1c1202070e010303200c10050c07030c0806042306070809 84
    0x510004d40c1c0074401d5000404016001003034016250040100381744004010301c2c010048103440c071012560005e18141940d00a4054028202003002d084816000d0b03500025080380c03800002c0c0007440300c4203020f10b119003c08d030380d817007803554640003030509a403044a190100c43c1d000f48040d000217030013a17814151956455000f541d480300150005400b000619945883c5040009001e000c18403010f035055030b000507404000e0050038a041d000030118000201025800350390341c0c0c1c511496664040c8095095900205a84d8654103074400e03d2925a100703110f581c6c0f160340b4140e03c8141e06d040c8400400c00a040350025241c10918a0b110410901c8a10310340c4021402a5280403880d031a0080c901c81c0607500039030342c0181519080e81c2002c810040390516913042d51106480708025510f0407a40c503510342c00383c40c260fa1224588031000d460320003c2c0c0c2000300441c101c800d0204041d000043d50610850184a844020120150390750108d5840c806d001c5a00da0406400100910b000351041c581201c1e60108 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 123310188 1250 123308938 123308953
    0x409110414071404050a0303080402032d0d030513060b0d0b070c020103050a0b090703110c07150305070c17091f090906140307031106040b04030c0303030524090405 72
    0x40c11907078004002107042500d84180711409501c00c030111410180b40910615190901c0001460041c076844000d041241081c009421500c05214410f602d44a200b403450510b105880c144004082d0203140d0790042c441c01d072182c1d414901c0383c017401d40107920052410401c000e041c0c680f079000c1c100c006885900010304441c90000126003402642c4520540d5071001422000c0744001826590050102c80421f403c040c01d40e1003e0342c0341c070800c580018040c00e00060b00070720502800094050030a0009042c01106c2e80016000e480c1c03001c000c10310400d654200710315501c20b5015520b8182241c409400a180301c444561650790000003403d4130760f40100604000e4010810b51000790014050321400240c10704020026403c0c1805044003074861002403c0c0215103100120f036076000c0510001c0c00007a607480500758140c80340c0c0110307001380001051555560b62070b801c00602401d40d901c0200e00007440e100028002e181c0e101184080f0828100d05182d10101007420852004405841500c4c0342c002c240 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 123311438 1250 123310188 123310223
    0x3091a12010807050f0907020c100915110d03060605041701140a1d060c0f030406180309031106030105060405010c060b0415030510020a02031207052709240409 70
    0x30031550003021602e0080107a0750608003032180340b03075030030301200e004800311803d000d825034000c46c80000c980c84c1500d1400b2041407072031013207449140a500c00d010564241520a04050340082030302d151000c00030407520f01245135102113080b50a07034071400002910600c0184601c895100081c0d103600c0f0844000320340110a000468410030094615103c103e64683c0c00c040b4070300d0140b81c00b200120107480a8101c51400200306141071083e0000da9504103000400101000501d9001d41d007c0040102584c4010109141c058011f09150106403000c0901004030312151504104480c140d60028000074245498000103681ca02c81940e0100c40083d2a200403c019807224415090620600510100000c6c40d40c02d00900b8171102280c07080d2014010000700b12019000000c0b600d004082044003001c40e03840801c00c075128003400c50654500003201c4c0000d2013413000791400c44004001111140602e4860004d03603200c2c01c00842d2511030400c0394280e01100c1c1c0c685030380071003c024001c40700740c80100d400340c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 123312688 1250 123311438 123311467
    0x9060f060703031b03050403021e0706140f0301031a1f0e0c1b1b040522030215040804030b0603031303060b04150b0a0201050601090e06130906021204020f030a03091a 73
    0x180ba1031340040d603182c01308001d05604100e441010900d040040d1641c0280c91440b9840d24294020381e0184601c00c051140c2c581e040c0b03000c1729403040e607505259442c2d584900d00340c402c0501c00818281c072150b01401140155071151560818400d8044000b00f42600d442c03810202000d00800c1c03611101424041c000785e41c604503a03456030044008001d400b10313612114601c1c010000a20307142e40103030714000070007a00c1450f1640c40c00030407840c8000c81c00152007528080780752070140045142c8001d03101040c80b042240c40380103842540e200b0440081684e650100340f640d24003540401580300100c0860810100c3c07004d9000c84110100544042034040340f502c40702590000c1a44000300b103420015540d4542e940c280704482e000030091800c07140141c5491a82030b2002e9019042c00c0c4150060a02c0c002c03400099403010400a41c001015074442000d100034003801a421541603000d1275041c484c181140c038000c40c400102d13540c5510748840103414092201c60180c0315911101d5000020414500b180c2c000f03 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 123313938 1250 123312688 123312731
    0x3050115030309270902060f0d0608070e04020904030c020111030a0801030b06030102030c040312050d0e0a05070b0306030d0309020f0a0e010603060b19120615030e0c09060f06070303 80
    0x2040103440e0300d60315616006111200c294000068000b00c40d4020400d0b210f0074400ca0990300c0040d50203d0340318094000034050b0310800f0286445070000213a40b00140003950042000c445403002900c2c0c07107581c3e62520401310394003110003d522807602c000083c00240650b4a0080840c0189400c8550784101820f0500c1d507404841200085081030004004105600803020303880740091303000b0b50035070034041e003080464052400010252200c45070805074092062054442040c0500400d000354899204203503107405000303006842034090f0040102e1504c420300c0c100c1c1e000d0301001d0010300301d242444d4011070083c201c19034100d13803000c007040920140b5561000e4060141c103c918030f07244154503018025040301d595074040c504800083c0007580070500d8203a901441c41c00c0310300300f00d503001e203640307203a20000c0142c0d0300080b0400b0310142e4082d001c01d5040d80181c502d080002c080301c100042c01d20400c10814800c686855200010761004942410004d028021803446030402290b0fa20030821b540007400603 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 123315188 1250 123313938 123313961
    0x105040902130305032b090206070807080d020a0c1a010302150c010204080607030203010503150f04121e02010b011b0b06040908070507031115030f18030d2c031c0f06030501 76
    0x11b41c000a4900002000e820201500305603404001c07001250340404e9041c003d9260103400e0100118001c020710a004045540e061961181156a0398204601a004001c214000c1d100907220304910003840f511200541d06803a001400c81040308600c0c0c401c0100e550040940060a540a0000084035002000268003501d00d0303407000360f160340c100414140381c00e0960400d1a0044048410302108003821044250402d070490800c2c4d980080600041da042c50710500c40451041e6001a00e0345455070662021100710001daa9000303084645500841e141c0d01620400b0304059490030115079103141507441417035604d100300700b11828030030a525800d04140644c0d00c1070341e0701150801010f41500e02803100d0a13929103448400703800c2d42800302039104100c80081c41c800d500c081c029240e003c091020020f4a1040030703506018032202d8981e1800b880d07240f40318848105c1c3c01528604604094401000b0750310105c042c400c4003088680d4090804016141e84454014020350703070030380840072500c2800360b10300703200 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 123316438 1250 123315188 123315217
    0x2030a0f020f1c02041d0316060506010507031b0302190605040b0109021c0b06041814010501090b03040809010509090103080304050606100c030c060617060103051605010504090213030503 82
    0x98280c01480802ca8440c45080d110ba001001c50b181200c10300302842200da5010303600060b5003040c108421111189680300b00758140300229412000c0000410303071808162090308140000d13114035006403154040c003400140032984160540809403c1c0c030740f19000c003601030f104072103003008200b0003044c1580400350240c0b04551a0001c120500460b50043c600402081e48114603000c00322000e044011825142d200c0c0807900c3c5c405144d05a500c54054030701030000e1004a99042c607254103020000c0002e80103890b24400c028000181d598011800e01c4105d400044005240d540d4581c2d49140790380c0115000c17814130800b4840c0403c16191546498080c41c8601085d40c1d49041c582021131800782c004103424400e01034111006d003056400b000c403400c4d09a050425100145403403500b500a440c0e1038005140c40d04500c0a05281118006607943c101c1c0d014200f07542d0b842c4061000051170890314020700d8049078007080104900c20540c1d0017440300d205211010f601145e05da80e81d090650f407081d44100c0000 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 123317688 1250 123316438 123316463
    0x102070b1315170f010b16020411031e01080a05031c06082e090203030a030b04020904020c06070f090b04050f04090204090312060824131a0f090f0703060f02040302030a 74
    0x1441110f0070150025183c402c01d610546c51b1202034034540c811081c191042000308a0071604640307442d040318005103010181c90f0748030718048044078440852140701d2887c0311740c0c031000020342c0309012444c01e8249801c40701039442d0a11104d0f04114222025621300e008a0380c1e2000029461000d00c030005075041c000074001e1003a5070341e015102d0f0030f0b0410794261000720301d0444100010383d80007046500c00582420086841d1401c840060b000780201480160450300000719a020500c002c03d0491056045403284030050b01007010443d0300c1c800601425601d200100320600c1545820600c1c41c403060402800800c42c1042a4003140030740300801340440209401240d44007100042d030107650090f017a0b05005100020f5141070070340c000000200c0200301c0e1103d44000c9040d108007210000251504104082070b45890540c9560000d0000c0321000c404c407281c0c4000c16130560020171078a2135081441d000388116030454032018003c08000d140c140e10203500f003100000513107080c82000000c2e030107250a010034 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 123318938 1250 123317688 123317717
    0xa031112160b07181e030b01030605010815240d0501090b1504020a0504031203090c06050c060c0403050606100201200d1401030201021203040f02130b03070f050102070b1315 76
    0x1000c003074119000d0080d070f407445840c200c025161450071151001c6040780c000d00c14105c0c000050180d504060081c0780c03418004401d10a081c0c118038100e802c00811141c40e2502c203600303010080d0060710400d40c901242c04025049003003100c03c0c500703c07070b400070b0400c2c6001c00695281c0d42190124002101c05d951040b040003085404d04012041b42d40c0151419850728448120051840c800c0d0300009208605031040f0721140c40c40380d4400c900e920f074040e502407081d80d2210030103440f81d00240e08260b030606c41c8e1000903650102c250240d80490f0340c40f6000b0074054807244100f041c502c2c4645d8180c070071590382c1e250210f400705850110408031000711a5040e650203140d0318580c1520b1644a0311501150b800004100507640041c564107000440300520f901c0e03072158507249140c0400a540030303502900e1301003014503d282030b502c5180c030900b044045481b496034503900380c6507081041c880e0350302603040084208010001c41009003a68014a0300402e8411b446480800d42040703a101c0740f0340003272014101d0080 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 123320188 1250 123318938 123318953
    0x17070605040b010e07050a180302030a0f050111180f0111060a0b030f0a030f110c0901060e010810060f12090512070b0a050903090f190e0a0c0305090a03111216 70
    0x15004d0086125840d10b05140090080d1144146400800040130100c00152807524403180c080c0d07900905803410043c10781004c0041d522010816140d40d440d000102e54500c084000311192419480c106522506800d803c2021a29155007601e06004108003103604084052010610410450f400020361910302802d16291402205c2c081e200342d800304040001003130300400b6182a081a0b0310300109403402e030a004905216854905540100031b000c000b0500c56000102e40b00740010030b99890095030b0710b0480504100c0f000e0312650300814803094002c01100d1091410458501009101041130901651a5490000e5a03444440c102c1004100c00003080960b12040c0d4214000324000d2003035040c05251613850348150041c00784994041803442e1625100e1005002000740b01c0c0b00e910030b00300d980300c0d01e8028802003111140f4a482c502501e03001090701912515010301c038520028036404900355015a06180c2c190300d24901440740017100b10556000c480141410408103c44e001c599815190404 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 123321438 1250 123320188 123320191
    0x3250314190c2604030908070602030a110a0312110705030f0702041506080112061d0d1b0b04020f0307031509051506031005180106270204051c17070605040b 69
    0x10450a42c1096103c21030400d40c410604280c0c14480b01c554071146001d99044001c0d0307004812038000c50324001001c42d00440900550201505d409032001c640b54041c2d91501884000107002c80c200224686690080d5400303505040c0d1403040c3e1038a040b01350741300e5a14580040680e8035071003400044034821814580206002940e0100841c1c5d0781c5400e0043c040c01c0f00780c0500404035596480c15040e1300340407280c0c0042211f20509540c0f60303147e4124658050300d98041040364000700d610071510350382c50b25091041d030303111039084010000c00791116402c1040f0b034108516141d80c0361145860210110317807644000505040d02c848009046029884d0007401c00107080d24207400c0350382c440204a07403620f001c120f88103040301502c0c0014041d035501c01b5400c910b031100001c02149602e484000b040b211242c01c8080f0010300104017802010640e60001e000360301c114001c00d80c00c20b41611130202d108004064040610348140d0000c1c40d100d070803103d10036241e00070480549200c3d0305c403000c0c88240901d50740d079103 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 123322688 1250 123321438 123321461
    0x711010315060c02040b1e0a06090605040b0f070503041509050a0509160207030c060e1f021906020c100b100206072a020d060903080c0325031419 64
    0xa1012616058103407000801e02e22805092141003180c01c0115540c9030300003010004000c200c0c006a03d03001c9151010f0f9021101d45901503103181c480800c0080c0902420350031102c0d2503492070711701030130b180e0720708115008003c198411600501c48400007034014009000038010200c550952802240001000605c031684920700403550742c001400b03640c441c080880c0e030203010b403c204403035070099500880c60801d4070740c03003d424442d000da8003040d032542c0321400d11228001141c00c00c0038448030010240da030501c0040f1a40140c0e21031280700f00640700b880b030302504840c0130788001420b1078418103119080c004c645108641d441e950b034402e08480c2c41e21100d0544828110300c01000d451400040c003401c2100c00003880c0ca1600044002d0b1810a80d14441c40d004096011389225a24140c0d454110060303c8009012404950410700048141c44a0402c0d24070441b024108070390450140d00a000e2800d841a60007130401d80c903021413110380c5162164060140210b0080d9001e04030080001004440743c0e400c50 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 123323938 1250 123322688 123322691
    0x90b18031b010c09270203130213061403190b091606120c0c0309170c030f060a0605010816140d020c0d0e03010204060801030b0705040302120601030302011107050a060507051e07110103 81
    0x140c10b21220031845007441c942080c0300181e0748c0d01c960200c011041000080294041a00d0320204065070302d0b81c020340100c80c0c55800c0401c210030b01004141e1913111400107010002020b100d4031002c6624251042d8002460405840e20b1421114250f40c90420303541280300441c1b4001074a200c074640501c030711000d0a295141c001d01c2648241d80041c00c0f80003500c5180d82060030481030345540071003400b5442c0c1900005086844131a074a84100ea00c031003003202d024000302e1600400140f154040d80c060380c0328250b00d08030001039020092003500c0801d41492080c030601011302880d08030780f91031300c02010f4080c4841c004080c02c2007082e50042842201007074090207a4010300c410132000350080141415a64800328041450b03441034012a80c500507640045d62200c04c19813074011224001c90118180c0740130340c2c001c0c0b02d4500369002040d8540315840c1d005000d07522103200c0b00b0107d04681d0199410401500d80140341c0031243c10a4041116070034203d0641350700000e03403c810450310040003141c80400713090 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 123325188 1250 123323938 123323969
    0x40b09250f02300c070306060503030703050a05031f06020c19140f0d0f0b0415020703050f0717040b0d060e01030203072102060d0603020112090b18031b010c09 70
    0xc00a407102d140000c1c894802459640940050f24841c849110062105219603140d0b403401c0da50a9660005200c143d0b5038502e8050040742c103080100c1180c031119015281c8914000e20484111503a910041400900001d1422800c8a0b03500b43c0f999000100110380c000c100c1800d080040000f071903450100c1c40003c05440808000481c4035120300610908200e640c540452055004a44500c81400c0001c1102d01241c84000412145e101800c2c05140139040000c3e444104084c521b0882c801d002020303011840500010402d20029030090050030f11961040302c680200109101c04e54100e600855541d1002040f11803603545144130b2200101401103c0300f0440d45580c021030740303414071401401d0314281108170428443c184111007242450780548200d958075040c01c03c1e00024241404120b0000d42e11020031180c000d2503014211880360001c40401d50398540d0a034458041c5010002c484060100380b00c800d072004108546100c0c00d00402d000030503600120341004080c0d103065080f10545010220 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 123326438 1250 123325188 123325217
    0x120307080a0603030207120c091119020604110909011515020d030612230d03090201080a0504031e0e130203060f0d08070602130b0d0b0a0914040b06040b0925 69
    0x460710200c2d451044803403090f402c7d074105034000714010f0704402980b40c241006411461003030f6004240c94503604d0b41c00300c0041040359049803500030a503030241107186801c100140078a8030b00c1140340c0180070b182c0001100006d40803511a10a8968880c030f040c81d807096080c0c04025010702000c181c10036145400c01a440c10001c0d1300c2d0031b110303a4200141007102e002c0160300309044050030b0800b6008600040f00c081e00389a40009029106411089000842900200d003010b404c0740100d5005640c15120304402d00200c008801c00d44040082c1c9a00300580803904600300d13120805121010020030002603540d2800c1d0085c010189001d880c4035002c4c050411002e40410001419150320719440a40581d4480303003c0f10180500340c058003ca6801b0400003421101c03040941c2c4088071008003501c0c3c81841903960b003480300c101e8141032181000c00c44d12100080c001421085055880b20004000045c48008003010954a074011541300c0c50b168000e520300c08044011107942c0c048114240307005a0711a80c0c4d0b5 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 123327688 1250 123326438 123326443
    0x115090510050d08090f120a02040f290102010615030b040c050c031803070b27030304081209061315031113092a020c01120b0108220203120307080a06030302 69
    0x120015004c85404603a9901d540c1da0031404084441c001801221400c40400380c3e81d45840034140100d104c1c900d44107071102c0c2d5070464002d070510b60139081c0380205c2e032411001000c0e400c501210500b5045540c1e8031804143c12503041c40300301250b0301c1a5000210030103c4801d1104076119443e03950181300d000e20021010f030400008031500c0c003d6030741c040440440349101285c98000203030422407201c140400d600d1001202c0c4032040b5143d0f041096100704102d500024540c4a205900134101c06412801e2202c00d5449050b00825000a002d40614034100e616a194426601d4540001a0544c20035031340c1c0030882d80c0343c01002d0f02500c0700c00c0083d10740316402c01101c000c20b405104d4140d1441d00d44003800b4070703602c00c0104889032800014040404000001c0300944444544000c2d031301040c0301c17400030000301c0082d11a4407080704040e111540381d44c56504140c89420f040180c0c0c0c9101c0d004580891005031001d0110b60010b004150685440e8200401d01a0411000400308000c20346030200410100780d00 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 123328938 1250 123327688 123327709
    0xa020303030705070f060f05041104060b041e080703060c02120f041701021e0903011d15090a0804090b1c0b1b12010e1503031207030c0302070203011509051005 70
    0xd040099031303490f0601e0002c1c18003801910281206140c814035013120402030708082e100d14461400000710400000400040351000c0c0a08014000140014024070042c00618151b40c882001070904c026595400749242c4100354004031066a141e4840d002240c6e0100104040405001a92820240e498502213483e0045204038401000072801c51002644294116080c1500980c85d55141e09800e924501c525401039a00701d001b58642210b403020101c0a0303131505003201074000504814000010107041d0b410000d04052030b14018143c3c14000500f400e802000204840310002c181c44d2507060801490442181d03038500d9102c59410003030005868142c20ba44c0c8001c00302c0450f0750362850304040d0640781c0201e150800108520700000700d0b000d029000210302c1881c02600c641d2504c0701140c285610f90040a9400064406000104502d075000342c00480a003805840e0041c1415400c0e00003c6c250b602e01c090325509803031804002d01042500d40030300c84c0c3c0b1100c00542d051540c0e02c2c12000c41d140d04031 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 123330188 1250 123328938 123328951
    0xc03010e0c0901031b0306050306070207031e020a26060f0402010210051b070803060f1002100b01170403181509051302070b090f011a0a05011112030108010c02010e0a02030303 77
    0x80080c03001c426a009911174585660703452104800202e903400058018080c41c01140d209104103030005a80170b1000941505507a4030481da030814600380c40c40d403e01076020420492344141e0220001c18110488454101c401702c50b0f20380810b02d88800000c45007491000740088040b40101d40400016076000074140002c02d184002c0001c09680b00680d07098000000c25100c09501000101c800610500c600914000d030011541810403181c1070040084002c800b801c2d01c005070f0003200b8038011910080d449148881c0040c100100c1622024400c0c0b0f0080c0c40484007100030540d540c4588004a04009500b13001e480100a1003049055590010380058050700c0381910405045040c1c0358400c1e610340548440300d5010540e9442c9003001d1586a0319141ca0030002030156283c150940c101c4546404580ca4440010b08105003041c2800011900c040c09050303182c4c25481030700c07407001d1040c4820000b54001c1c14010000501c2d6420000001d0a581201c5409540c588c090b50610016076000700c01c880c0c1088 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 123331438 1250 123330188 123330211
    0x1410050a0c09030f03031103070504081002031e0705160609260d0c032a0206070c0c030b09011503031110060b120714030c0304020916080402040b010c06230c03010e 72
    0x550034942100a00303007c81e00c0040b064404000d101440350414054411740c1c00c3c10003607954441b0501c0701d260481c0401ca621050300c0d640000021001401041c41ca0f800c5580c3d403422a261840c0d51090405140c403140085400507502c0341034000b0320441402c6c1e0100d065189070700d140c40c48403c840d811014040d0071442000166103000c00c030711042c0254080314000d5144202400700500528101c1c2c1c108001100e5603015006000c00940980e01c81c0141400303140e0b1045246244030b0440d240c61590210050000c9169035889450541950190040d040114442d43e03540703801c0b02c110000719050051800341c1e2050b150614400303112040d80300b800d0316901e00b20503450307000542e600c1c0000c6032840758502d52602800d50000070701490706001001140704900a503a031081e2506d44981400d611103c0c04800800100b440c170202d801490709410140130321a05151084915007240c031410111140702c080d00304124244501c0c1d441c400101c4440640c800d04940080d420b56140008903c01300800614258500 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 123332688 1250 123331438 123331463
    0xf3b011e180e0108030c0d0c0503070803130816050d0c0503040e0705091002010501090b0a030308072f0a02030606030109050a0f020117010b07020a0503010614010e04091410050a0c0903 81
    0x21003210000c0d80042080b28a21105543d407074800c50380301d6002c40e0b5048550f000b48002c087c00140250126002c56900000940c170f03268550b243c1d4280741c0c0001d0300c1c00300c00c120694681408140399002808040d8042d941030b01c21480c1600c1c000380b07403030b40c000c2c000c4c424000e0512100300442c0001c42620304860f035040b1240070565036003108a465105128020b5805949910030323503522641540800c2c103a580d5117604100c000b1090342000b1a805075480010001800c00f000110068800c0d00c1402c0312000c1d2119851900b8000f4240d100c4c28107a80c07541101c0c079803001081506501d03041000030b40040c4194020441c650858072026101e0003412400f80c100d2113407252072411079102c0c0740c0c495490800e00392025000e58658041030400d901c50f80c001e0344035140112021034103103010f1044408442e01000d1101381910b02000549403038141c100400d03403186c0c0da4440c0201042c10005402031005403100a0524111607a014074101c40000e8a441c1c5410310304204a013182d6000500c10007500d40141000d44070 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 123333938 1250 123332688 123332717
    0x7180504051306050c0c151b09030c0a090b040518030702060a02031303030806090a0c0e010c0f1401050709080708030405010806040f110319110301060f3b011e 70
    0x10b140304900080410b454601080119007201019041e221300e520296902400d221101a15111055440841140d0320b41650519209100c0060940003006010b569011140000003088030400745c2c402e00503645c45480310481ca241a00c1070715402040e600da000d514100054100e03940e4000c07214020b000300d40c0000c0810303c0328000c00c282d80c148080354483c4c6051986031b1a00030f01d0f4135801c1d45c103240500c040c0c0300401e11540c814060040218140d0340c2e504205070180b8011035078040c54003404d60311083d0840358180882d401404401540260350000304071800c0c0790000518122642d0303c0700361a90841e16042c40442d00c0441210b040351005d01e0030340d100e40c80d204009401460034400c040d840d2031426114641c0100d02c8406140f14121440500800b84407200303080b4195907001070080c5040d8002c10052100d24003800c0300301c9042c5107500e401514841c2c214810380070515482c15040900b180c1254a0010114113071a064540700c0a2900818207103211080400104440305848107000350314041070700 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 123335188 1250 123333938 123333961
    0xe0a210c0f0831090b030f06070f110609010203010e01061106010605090112020c0d020f07060219030212030a0504050c01030c020d0305041b0e0a051003020109030f08040b07030f080718050405 84
    0x602c009051401d01a0020680380c1071006883ca100d14052582004081e044a00e00410820003007c6813001600840e42c5404007241d03400c1d864846001806640b08501d205640c04020340751040c50014001641c2e54104004e403011604141d0000081100c11004c2d80c1412402003031690448805082894413581326a0040ea845800c54102080d240d20210b02c20310400f40001d850404d5000c1034003610b05c028003a94510340c40d80d0140c0110000350b8001941c400c03100311041c07030042c1094000c1c416201c0070880c1b101d000c082c41d8415200407200319140c900344410711034240114174001600b4242040800c5408001946410b41c1a464106055440e17000a0600190440e0029a060b0a4041107800398581e0ba0740d0341e0501d010340d07040c55000c0c035100000e01310601c03d080520980750141c42c0d000740c451965036903040d071300da90580484d0708020a1000280072400359003c1c0065601c282c459140f25604400b000b00341d100c0090403a8200900c25652000071281c014900e01550b1050341d0102e101e035a89924040c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 123336438 1250 123335188 123335227
    0x20304060e0429090105060c0a03270e0708130c0b030709030b09010c080109020c1203040c030614070315060806010302130b070b06030709020406080f040203010e0a210c0f08 76
    0x50400824035100c040f50184803003040304404684242950f42c030391040c0050748c01a810481e107598001c3d420100031a0223400301222600024112480560441d100e090200c0016400002e1520701a400d003c4800d0b0003115056200f02400045021411103484d640c4005d0950310900b1010075001020400b5140301d00020005150061644141800c0040e2942d00821800c0e2141e4002800322001003041c01c0640215107500c0722100003443c680d501c10340c40a480c3d46c0041c0040350001c440801c00400075200e0300401c0d4407901030390290348961412640c0602501c3c0703108108040e00c903503907000b4015240c00652441e04000d00780303001601c60b6a40440540c4d0030b6480c3c0c202404035040455070310200b00c1d0084880f482234009030300760b40c0180c2e5100a103000781d014500501c4042908480001d003080d1480030082c0d40700d400280045020501404485e003030903c001401d076103803045441c1e100c12922028240703845088043c42d0002d00584192603104400d4440e19000740b0307004001949446064400c01a00b = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 123337688 1250 123336438 123336461
    0x807030804260301060216080c1011070905070809030307080f0a0609020d0209040c02030304080d02070f020904050d081f2c130506070f0c020f01022d16030201020304060e04 76
    0x2400d414000e10302400702c0d40c009118201c014412044505207034041c41c454002204c004200a00d0791001030390800c40307a481043c1a0204002458104100d0b80c04100013460040c22080d2000806c0c0c141161300901c2d010004142888591040092043c0351f5489810a903000103014034406407610395841c0c80014251035032000914038000319084118100650040503100400c44041121140d0303018143e80b039010440b03001c1e02004060000c1003040000350004c221051140080007007000041e800148011005d0340c1c161069840041b80b50081074004841300c0d0010b10030310303900020390079101d0034802e60b500360300604c10039034060f8581004d010342c90901d4425000c0d01d105200081d00d40301385c0900c076244407070400340c0340e61080e13401103000346001d607048240300c41702c998030b01e0100200c40c2c09110414041d00d00043c110311902516000c400107240520a0525404000441d441020650641b41c103010780c91799407481124020820060780c0000898080702c8140c101841d44400c1e2100003002003a056128 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 123338938 1250 123337688 123337733
    0x70c0602130f0e010609030308011401140f0703030b06130501180305010509211804230106110606040501060c1e0f031101050a0b133305030607020a0807030804 70
    0x411403a0388400e019040d41c5200d0710020b0380c0d0ba17031028101e4014646200c080d000c9400a401404240000f000c600008a4107040c01c010708481094041c100b5400680d1107940220040b4031241055451b006d902442c0788100d80712030a20305580d144a003218028450035050011049509038500d601c118007000131074001c4000c100c00e14080d080a500c620404410400280750b000804a01c00b05010a41d50010b035140020241e04142c2414000104400f240485201d01c0f8404c0e1818002c91200c0024041c0800d907941c01090440c02d03110902d011405800e541c400c508290040c000e46500240c070107078490700201009043d01c5c3e00d000112055003001400341c101c105c260703030a406264102c0824030450003448020082c1d95551902e2008651311411800c0d40481010003040c81115140c0206049100c003058040280c0c0c444500d005844202c80c809040c2d107402d09108100038502880802ea1103e0b103800607040418081e550201c01b8420001c0003020b1100c0c0d80701140501031240144900b22180002d03 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 123340188 1250 123338938 123338977
    0x307031523090a0201170f040206030414060108101406060901050906040f0b0a1b0b07050310050a080c0a0b0304080304151b031a0a0303021203070302090307030f17030c03070c0602 79
    0x902e20f84900820100760302051030004281200c10400f40144c1c031402c545500c200860725940d0801c0002e90014006480c0c500e2414400000b1500600c8410300826071200180f6028076074a0311042078500c40c1c542e1aa00c198242e007080080d40780d900498444c00c6c42403034025a1000c541001a14034001d80e0817140e4a203041080200b2a07520000080c5050031b015102c038101641c51440c55002d00040b4207008055010700700c0403802d200d00550180d41c000307041d01e002e02085505c81020400ca400c503a405400680e12140e2036060500b4403c240001802c1080b03201441c0d4036180d01c0742c850b00d200250000b0721900fa540b2417082d042c260b9038004440c028480c43c0410800b0074182000f0041d080112407009010200b520b650741f1460110851004c480d85500a041500c0700340e01f20308000d82009081605040d002c01c002790042c0d8041c45080051f510031a801c2a8600c4582000c0c4036400d8140181d039002c01d420001d01c8401450f81d4240c0342d001040d854800a003000030301c0c04101038011301c1203e002d80d103200c14 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 123341438 1250 123340188 123340201
    0xb011107030b010905011202030a030c0204020405150310082b02010b0a14040609021c05060415060507030e0102030f0f2a0106030317060609091e07030204140307031523 74
    0x103900c50480b11300803401d01c0b80b41d80f52000c2c07070151205850700950560012011000203405440300d00890743c0000c00040c103181e55400410440403401ca0003250803d4004208030070302500420010140c80c3c41001402c0f0b10001c101c8600c4142c080f65003055071490b540300703442c08140c402d4100010010000e03001a031519580d450f82c02c0f02d1400c05010314422802d0000c0824030211500c20f1354204001c03c03000071164940084200010003020700201d13001f5440b11540e11510707180b07052402c0104015a2440c0c4d48024500780142424540d0346140d046400401001c20102c3c1080b003514214504001207a980758440c1d6108150b2040700004031801c80c0902c0501008400194406403c0340c7c042c5d02c903d1402a500074955000c0748040ba40c8940c840010301115455080030100517600c051181d0015000309005101000d40c5007045801100007500000c040c051406400820007c032841600148495401c554030200078804401d6062001c0f640c40046001c0301c8465140c47c04814614403004005043c0903 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 123342688 1250 123341438 123341453
    0xc03050316030e1f11120712090f050d022701150306120b01030605040312020c0d110307050d030e01021e04060206010b0c0303160c0210080720060105040b01110703 72
    0x1d800b0b5010940316000030b490f03401c00509001c2c82d81d50055800c004440d0703680081c0c1e58400302c1c451800892003404c203840440c400b030000070242180135444407040c07110303442d200910041b030542000ca200201c04000700240e8641440c030f442c00ca941140c10744401e80c00744070b18554a184500c00c0700e039074105c40c00000034007964070b401d0020025096541480707503580b5150301403745101081d00400d88004e03500100080b5206500c0070360003902c280741ca040c42c5800c500498050760401142402c1540020404041c1180c10981c7c40c4280c0007040003641c14146980c503407540b1521300000720010702d9120004030031928030070350489904002c2940c0e00304244030300c40b0300341c03a040c0c01900900025104031400400d206402800b55440201003100070351031640e070403115941c1c0c80c15065264091004e45580040183d40f0605074503503101c02c5540700203a43c50000c3d00101000c007041c8001c41c038610b0203030364403002d000c0c049181c0c0d05448083d0b40106280d2500c9004903881013000c2c10600b40b81c019075a000c010810320 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 123343938 1250 123342688 123342727
    0x20304031e020d1a100e0105040b010201061a030108060a1802040b030106120b010f0603020f0f09060412051c0f2007080102070311240a150e0c28020c0d0c030503 71
    0x90001c00c0040c0d85e1a0702c441d40c0d0140031801501d2142c00b40f400100500e192a4022651b00c200620020440596a4141c0d012041481c51828106d550103c018048070704200007103a44500400000d2100c1c01e210f07650758039216018000071b03009585a80e03101805480940040d0014a007038030040b0b48002950820a8103880d00703000d684c141a6181100103541482802902e0007861850300183ca81041404c000e107441d80080c00382608800d05201c0021680c10b5109000119405880500306e901030f030150241c0c035040075003259014402003845142c51540d02015880c000e0340d64045021400e030380e2010346450051642c0c002005503000103001d03070030168000805040816007904803180040030440000759090100c4460021240450021300010300d9078200e80c204408245d4601c2c4030648500c0104010321080b58510361400d0002151484280c004a5861124500c852141c1d400044004000d440b1034410701402d02c201881c00110090050144101c001103502c9004c9996400500c0412201d8901 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 123345188 1250 123343938 123343973
    0x9140609150f3a0305041203030608070308180102010c120e100c050c0d05040513020906130308041404020412020603061504030c181406010f02030c07030510150303020304031e020d 79
    0x2510b4a0307070302143c4511004200140e0741501c0e40303410282401c902602020b0006d20a504051f03c0e1500011b00da0741c14040c4001131800351000316919041410310180307070500955010b04581c905604468610750110000c600c6901100020441c0400c4801d080e180c544010915807801d032514104145540d000001841400300c2842914601e05180c802602d240c003030740c03141c0350704849250300d11288215180d008101e41d400080501e41000c02814200481480035001110a02030001d414403a41e00180c1c10b448640350100d5042d40340074203000e0750410600030802c00900500010020882c26600d21950508106000c0c458580b0744d6900e0400403240c0c1502e100700105210180d0031083c2454890240810160546070130741d4042d1280320044804155507421074045010511030160003c806100410007180600000e01e011250f0000d00003c86070707201071010034031034071720b60400c002a00030050b074003240e07081080c0c10408100007080d400c242800b00c00c0250303c0b000b550355640c200031024414074a0403c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 123346438 1250 123345188 123345259
    0x3120c0203010f6609080f030406050f0304060603150209010f08130f050f10051005010e01020d0311160302060a1415062101080709140609150f 63
    0xc40702811540359002201c0c0c1801c1008501040108481e041294952214100c8a840d00044000e130101d14481c014104820002090500104002c9004004598041c070b5508091842c1908d000c601030101c2c41581c0c40017004a038084005002c0c00744e6580607d0045400407881c451984924400800940c0204003041c0414009442026002d2040c1031884c402c81e905440c2c03020781c19081d114441000511081144d00d481900e0481c030ba81c143c280a00c1d8084c800c0800003151a003031012400c80090901e0700320f40d041201104490000e40e86c0001d0108a6910341d060000310051260300c1c00c0610302c54102c2c1816115114441d40c403c06900040d854032a2001c03407804c21150858031000003003040143d419144130042d202d600c2d402403920000070490b003510f2540700e40718003000c0b58481102800176031204806403c102c07420059409240507400d0308000500d42d141c0c46240c40c1d00003030302045c8050010352614011030500e280e6906d5583c1c544103001c40081084071381c10b0889170307015288211044402002d4 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 123347688 1250 123346438 123346481
    0x5160f08010608040b090705100c020103050903071208090a0c060c050d0e150f09030105180d030606050412030309020904050d0318050303150a120b04171303120c0203010f 75
    0x1a2240203440d069440c940c0d18000e10341c603141ca5981c443c001c05813192245018824000455651700452046000e10315110b40c6d13010b034081d0002600715100182000d0791900100000b0001a400002d0325141c18114201452180c0380c0c0468240b400c00041b0700246948403c06003c101d1603042824561810311070412102106509042100c240c02e03c00b140642003501b02e04207100b03003011034000d040b0304904009401d007450403000c0001c0c01d4440c2640c92415080d0641f141c0160070a0a00421340381c0781090400340811807801d8070050192189104000026030380344205400c05219400c4074038a55001002c000d030500b02428030641b541c1302d90118801080c645522079901440c09403101c030402e50444051800d41d52080c544090f00300c103000c800e0398840001000454403030640300072800b00601450b030030398043c83d00346405c2d6500c03424a0000c40040b60f043c4800c112030002c6428060640703900180103a002d880518054842d42c0004038002d5055007400c401d030448a402e54007a0711004d10600c10702104d03 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 123348938 1250 123347688 123347717
    0x510111608010f06170d0e01020309180601030e1f0c11060403030b01110d0207050f180c0a1701050d1203020c0706052104020d0f0c050a0303050a020f071401080c0c010516 75
    0x10f40c40380485c4600c94000799140e000c0140242412421020180103507480e1030741c0100045d8a40b00650500000c0c802220305004d001d5a152003990464541680181172a600040d10304441c4402c01c1c1105000c02d071911024148203100303814849078981c8440803075440d403c0510300134000d00a07480e1001e000511a40d1140501280000d10b0340f1120b8a9401400010703080005000c801d540c8124642e8100c402038084110401c1d0032468503200c1c48501c4a51612920480b0303005000307030186903c008026040b0401031150f50394810025460560099081415446130030042d8080d0282d0101203445004450002460f19089402068500071031840b200c1d805030070000b01600100180d80194114441d01b0b58840011046908048114046d0a044440d16600c4000401c101c02c603030070841c001040400e05802075a0100007003400c502c1210007800030113092500c03c003a1602d148507441e04201c04003020800c00c404001c12520031208590003403000e0b1616540340558182110003c800040880c10304110 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 123350188 1250 123348938 123348959
    0xf0708090303101a0c07061d0a050f0402070f0503030114330307050405030313050f0a0501021b040213080601081203060a03060c0e0315010518010510111608010f06 72
    0x10401540c0042c501a81c2014180c0444d81901034030111030031070801c0302c04050007007044040014492940c0d10740d81d4a41d09511500c000524030001d0f4041c0617200c0050205550318000c1c4c02f112030702603400503240d80a90034010103d002800c03020381a4000080003107082851082d13204408403050f2400c5000099040c00c05034108619420800440601c1146000025010000319003141d00c500e00581084c3e22080041d0550b4008120368175401c000110410042c28100c0480343c00791400c0710881c80c10b5141c400043e4a46038840403849640101004d80902da0f0b135281e043d0380218101000d908020358864a1580d0303210400e00920081d8072481c60095045860441182d200345400350840c007095103186c0d240f4010b003401042c0072081c8840d0f20100d107295101000640c40320103a6000c01542c07949000180005220303000c88980711000c400006000c66120600c04004040b0245040042c1800c035030880d50802c21a05d2400c0c0038000024030010300703000150000010651075190410081da074038040d001d03 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 123351438 1250 123350188 123350191
    0x1060f080318010c02060c06190e0f0a110402070602030906090613050a020603100b0a0804030e0d030516081c020309070e01050f01030c111204090f090308150307030b0f0708090303 79
    0x4006100002d40c411a03500c6441031940961000d44840d0030400c2481100781440c10450b0400c040c0703000300b040710140e9069800760b5400048220081c044100100d80250b4a40b10044005005441d40034044581501e80d5811100b0705504141d085403641071100700d02d519240f080d9004001485000c0120760400700131f0340303651000c40d03003c1300519840c0e1080d8280460303600010001001c070300e500c2070001640304042c0024040d10260381c0c0c2e078685038501072038080c1030021601702107802100c0041d140000a80c00c50200d5441c330100e402411a065040c1c80d00b060785104264144880440c4100d0308103504e091900550302940c074030b4040e10310303040c0c86100c0c2c2d0a0384c6501348225980001c2d4800301340880e5000747c0c003940340c2501601d40380d41e80e15003250011303140000c0340c142007140400008080050f1405881010903860940405001c0c0c040306480060040c1400307002244285c105969001d200d50b004c00c01d520055501060b50300140c500040e0189135204c0440702840070419040004607952004130859 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 123352688 1250 123351438 123351457
    0x10608100608070e060301030317070201152907030207091b0e0d050c0406060e1305150112060e0106050301050301050708040209182103010618061d040b0406030501060f0803 76
    0xa2828a003400407100b07114040d00240510000951400003500d074a0001c0d406140a5151406403803859500d0740c04481c13006207207904692500300002c1d03800e642c0d0240c0c00d040b141800d40440007181120710654844498941310503110300006004020190007181c443d04403114110108098503904480c0e90f044458600007000051449400ca216490704541424019000c0c6088900344000040850101d581d84c3c1c22103c042090000d03031030202d1900c00814000c210b4000c00500090902d90185842c0f452070b0840760703060240d1100200c076280c0b06035200d00010866a08240000d5079a0395003e08182e20038081c050084d4241030020706034038021410039010365400784c41c44003aaa2030031902d206480c3c0c004c0c03115405010300a42a2400c061400001e444132400d000c4495607940741c00d0014061b44801c80601040550741c1c40e08100d0f5030341210354051800d40c20100325214216007000600200015503029901c140380030008028403805520480540c0c1c4101d4000c29200d8890020076030301c3c09000c500 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 123353938 1250 123352688 123352711
    0x4060206010e10270902041a1c021c080705060a050604060503060601091a041706070e1804060203070302040e04060b090702120706090f140604260a03110913050f010608 74
    0x10340c1c14030480c50040401d980b1010380040d020305c4d80e1340060280c3d0710190700c1030301c0143c0e01078820b0000c0c0340c403652081c115000c41c00704070903030103040e4003080c02c1c81c24848000101c0705c0c81405c10340501c42c2100890b5401c0d43e200c000d9071028030700340c070007400280741c00e036046402145403000c0418182030001b8010300510303058584038110b51410300c01c1000c0503804441c09480103010702c4005080b400c0c540003180e4211412015180c6854100360040c418455044924410064107064030708055401d0902c0750455044400503960b607968080c01d6000c5c0c450f5074090b03810012000100070500819901078407190710100e0b00c0c1c1130a501d921100703d9a03540c0034000803581c4101042207000013100c55104030114ac0c41980c64011003040d54554640241d1942c520030400e4000c481088208031046545032240320710701c070f01036080488954100c0010302030302404c441415500c03040f4030003c16001043d981c2100c80103120107401c400e41c0401901500b41a10700b40c203c11094000860390318020b10b542031168021114 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 123355188 1250 123353938 123353969
    0xa09020d0b010f0f031109100503010609051b030417030402030a0b090a05011a0a06110109060204120501111e03130b090a050c0906010e01080705071a22030801090b130204060206010e10 81
    0x81000b401f1000e400240b50003a200000505034070700303002d40d00c0109080d040002c0d40780743c41e408070034403a0014508000d1515040040100150300c83c6d405960740500071213680e8680c4e4403440403a20745541c4210107003581011504000700c80310000780640000744118005c0c4400c08104000751001400c0091595008500b4101804220700c1001e0348022000a01700102c1da010294981804aa025030051500c10104009820030b01000f4056280c40c1c0a04200c1c49150107040000e110030140030300e0590035070300e4001011984044d24074059070a22a00580808118100311410584d9a0000e50302207869014206107103401d40740824240b0301c6114181c40385100c14074004011104010018036000a0180034084900416403007a10300c04414444040300c0d0060078400e0704c415001e1054071424155003017000c0380000180e0310000060440b20300d600c0105000c232080e00054402c1c5114041d46c500c2d64408900042d80342c0c0d00003600c504940030601e0031482d035120f00c2508000c2031002d005120011750b0044c03 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 123356438 1250 123355188 123355223
    0x1060602061302040603060203090705011407150513050106091a18070f050f030405010606030608061306050a0608060a0c080708091f0b1008010602070501091406030a09020d0b010f0f03 81
    0x42949003010710040000900c60349a5a81f42c00700e0700f00340e4402c80940d214040034429540c2001500c078006e44108406404c0c8485581c0c0c40c14000320035100d0001468491010550b980d0407801020702a0b98040000c0c00302d41d817543e036104018054408000075920201501c035032981480300404410102d070344502d411b1382e0741e554020303200003040c100c11600308042006030500b511000e8014501451203070300081a540e143c0800103090f6281c035001020146c01c40c0701030011101c40301810700c1809910160104150341d504990f64001c2c40d84c2c0e800f40c0010300a010800c010b20109901c03480c0b58403082d841c3c03e821a01c07115003c641140c403c44901c0020391080c00d4540380b03441031046940002c160580041601e00710200818a0140015500800718a812005200b020340503c05500a80001e1802400721482e08034500c4844400390705072030142c2400000305075a090035810240d403c0750081c0401d02055503c0c5003021910101344a208218010600301095116100d00c144041305d40000e1900d0b101c00f8040b = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 123357688 1250 123356438 123356461
    0x14011406030a0b1906121b0206062206030b060307060c0831080609010c080603070e0901020904090c03050c0d02060d0b03070305060901020a18030807080f04240f020106060206 77
    0x1d80c3c045500c5079061006054080348001d44d03030302400c51a81c40c2ca111003c842104030913a0f40c0c048060302501e031155035003601e080c3d000400b030380c1c8400103c511042a1400c441e01c9031109030000c003101c40050030001c000c02801000e1f00454080c000903812288441c0d40c80310100c5122488010042c01c880d010801d4400703004420f08048031030380390041007081840c4901c9045601c025141c0c04181250000fa040100300002880703045849085400c02040f14941100029100d2046016444899400e58003007910240250305448031850080d20400582c940c90800b1f0041410a120443c0c041c030621842c0360283c00d01c00b454501490740034040c0d0382032141c1c4803690400b070036428021580510507600e0001c0410410408503000b480c2a1000503904e100707840005080f002d860700403803482c2840d2002000000d0003081102c0e0104c2c0c008080303a03215462006d400000c2d210b164004c0084102e43c0030407840034030110040d030320800d000e91110b04181c008801c0503400c1e50b05a12a03880036802c03520000d1820902c4 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 123358938 1250 123357688 123357701
    0x603091707172b09050c091501030c0e03120403141b0402070212100b0f0a0509040314070f0b060418020a0306020c0f0714010806030a0b07120207020d0614011406030a 73
    0x1040751081c24030a50180c3d0440c030615110440e040d00e5151070303803403041c03100038030070140c11080503100c0c0710a900d01820325004207503032411161304056032616400600d520400c00c40780380000040503541044007102c2c41101c41d4000e03000689014101c400d000e02440e40000309502c2c4c0b1080b1912504e80e64610008020094110386011f81c0c10680c00c40b4007184405042c030594000041d81c400020f0015528000c6c042c00e561480720f6240164810003044c40703540d0301c042d8200c0d40030340d02d031401c144c00304043d44045050f801070701c000804da580440d03404002c214007004094801d00c02034a0400540e03005001c0400f40440c0b200d80603400400d03c020074008a01180c00800c0c080245030101d0f1001041070300071a240814640c08a4022401603103040d45560f804901c0c1608404100c008000410b0746840340080f5440181c078800c140041400803428141d0b25805586025800620040707503658141002005001400168034500000c0700001c80c2c0116004150015450041d2545046689003a03400d4000d000 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 123360188 1250 123358938 123358957
    0xc03010e160e090f0117010b010c021306050904030201020a0216051305040302010b1306050405010501030516110a0209041410020f040605030a0605060301230a03200a090501060309170717 82
    0x4549807141243c2c582c20055400380d2000400c4809a615040c03003504416007010684810340d0410003450b000d03070b83c407000800442e40c04075103034240d6070031904115000341807541c4200e03041480c2c00208401c0c10303010360152048488a03000d603080440d0002c0041840601805690380c01001028400c9085000d60320869000b0304c42d000000786501d031540003a1a641400009018242e101d0717009008a003814001c96005280070b080521840c20603448543d08061481890010040e001100601401082001028203500580340000604090a0041c40940041507050440c404e0f020302c01401c003828070071510361040441840d800d0600b801002c807000c1d800500000f0000c1e807195400300e03851b688e520095008166000380c075080f40046200c685071588000010300d00c5814034460400202d0b4541000c50496034003030458010100c03001000071488503c036000566250b142000103e10503400d940200c0505006a036070903440d484820f40d0519900c20000002c040c5084001e03082c00f082d1000c005884400c4 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 123361438 1250 123360188 123360197
    0xb0a150e1c050c06030c03010e070302070b0705121317090d0c080a05160b0319090b01080c0a08070311100504090c050405150306031b06130305150c03010e16 69
    0x8000400295101a076a0780030031034901d9418200d0411030304020100100e03500b960a1421881c0c0300c480444035000501c41c6080c8218000700151406100c1da048940540c2d00c11040c4015060440009146402c2030a4016400c0000804210800d28a400078501c003a841160b40d0f03900440c2a500200f03540011031410b070001c100c0350700c0030001003000728004041d00894000b402c140c01c0b02e0400a01c0e00059000c1103c0300398405105014011460044035480a0002151100c4000c20350104008187c501000362041c41104004524220b01084084113202c040358255101512589620345130030712840001e085690740c00b00f0500a04011424105801107130500d0341c14250344030340520a0321900355100000807000501407040303207810015281c914a481d8401400c600d003880100799a0034104010103a0b40303600c08049801607071090115045282d01c80801d0900a0f62840e0040c4d55282c505a41c03041d04400c000020719042c206400e803412030707140620b10100c0c0c0e1200d4101103c503c1801c50400f0400 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 123362688 1250 123361438 123361457
    0x203071104022d0c1203070e010804020d08030a0b0102010b040b060313050a08040e071e05030f060f031b13020304030c1103010213180b01020309010207140a03050f0604150b0a15 78
    0x10300d03000e4001c0c04401810f8180e50750380e003070402c003a8200641300744004200700d401e105101b40c040e80102e0aa419000a081622064513680006580401d03040c1000740614000401c200d852a616003201444202c00c1e0001c1c406088020100401e039903210003201e1700000103000041142a1040c218400c8600800a44403050f032961101d41c6980e20079003190000240181c01c0c8110507520200c03c000040ba003180c45040c1c41103501c0c0003030640c44045d04040800e43e02c0004101b0703c1c0d86081000e140008001d0803030389800c5161155141d018850040c05e8425103c0003070a44102840c0c1c0226441903505542c3c2010040c0c59580c1d08090b40316480c0056050741d4240500b0040c000d0b041c85403400b0b00292141500f0701440505030000355242d525019046420502003074030a660001156425564401052002150038401040c0708407041c0e840a0454404e12240d02400c00020440b203008902a48402c0c80d52144c41e0080c00c1a03600040036550400c0f442d560401001040004e0405102d00d90b25000811 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 123363938 1250 123362688 123362737
    0x406210f06020f1207080606070b070e030f010608161202030c0904030215070e030f0a080415140703170916170a0507060816170c1b0303040303051006020307110402 72
    0x700d80204c1d90840c85400e5007028001555046650b40398082c104644080c80c105040d9038208070744202034941c100303003d03c6a14180c40c9036800d022040c040c0b1030040003000042e41e80c0ca4040c1e030300c02001d0443c1007403800080d40810350300169030018010381d40290013840744149641c14018030a400070025001c50150711034802d242c1207440d02e0300b07009807000e035075007031450790288100b40c00c20300603a0740074240d54002ca140c08000340e00d110a8404507251000c03100080e040150041d41d003024408000515514005012401c054008503004c03266803040035a03413000e90310412460350302c1090740d00c0c0b90321038207082d942004000701a8030000780c000111710588090801039a030340d40c60b0087d190402c00c0411040c100b004420b400c007801c4006144024034180e4804604035100c9100210043c08080d6208800a6a510340c43d250700390704880007002001312652440c1500b0010020401541e00c4028112039036000a4110720000c1902c24aa030001d070042d84400101c0d08200c001d501514041d6450119083c0d08100d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 123365188 1250 123363938 123363967
    0xa0305031b030405010207020a0602010c09030209060a05150c010b010f08060d0f060912120c0e0609010201060b0c030c0705090606030a2007050f0f06100603050405120c0c0406210f0602 81
    0xc2d4130070f00026032900c20300d1041081c01040390304140c04581c5081e4580c0304030b9a000c0c050710304481e0107a80481c0c0b40e803283c03800b1410b0840190882504144010f003151030094580000700360305801200204001036100d0011a24041400d10402c001007070322000c078002d460404040c040803440303030700d035404611650750316507013520030700407003968455603c0b02c80c0c0100700e410100c050300403080141d081202d594141c0002d040d60550b42180c5000c3d03100441d00c41d100c2e9000350b01100150905115054403112044281e0f40c0d00c1c0d100c14030305400ba0080290014507810444101809070390000c040d5400c543d038200644005103900600c00c801001e21004245480e55018014400a40a03501500003022107101e0f04d4038140700c0e5068145076078420303c02c0240290058044005580c80d61401090302d0700d40741400340c40d042880300c0550b0900300004000054000002c2c0310300e019001510148402581c689141e640c0071001e1004010703110740c1d070b004500000e9908e02000c800d5032140c4401418003149900345c20 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 123366438 1250 123365188 123365191
    0xa1b030203040c0512030a0302030615030103051b0105031015140c070609050303070c030210020304091d1c05030c0a21020702120604080913230115030209030a0305031b03 75
    0x1008a580001440144440d900510024100540e00148400f802c00c075001d581e0300c143c0d0703901420954040045031041da201400500001d003804d800300d441c0c0d616414402d40755180d605c102001030700f85081c64059540544152440b4405c0980240302c0c45242c50b4002c0300c03921085442c50200b2140842c400c0750405020080c7c0303250900c003002415140d0605601034468100c1c1e8210611039030080c40158009268002200e05072079040d03407205040362108905a10394066074120000c2036044c13003001440c28a40840340b0940100345000c4540788550a0056880a41c610503c1c4000410820000d601d082c450f00c0203000c0c2580d06d1134a41d210220b00c415001d65001000940d00003640c00042d00030640c178011010b504020800c1014200c582065a6045c29510841a82501442d103050703400c560851039a1001020300e03490500071400b1070301000c0d0720507020424012503c6a008c8110560803461180c8241c03260003501034010700b400c00b2691402c1e07425800042c8218440d0308400f0308802e200d1080c10195 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 123367688 1250 123366438 123366491
    0x60a080718060e010e0a03080a030b1c11041b02070302120a08220e090a0213090209070201050703050a230c09030f010f0b060f0d050c19020c04061508040b0a 69
    0x501e00f40c0c890000189405052010740f44102003400042c800300741e1a4045a540018a0900040031426000807a0301104000500c40d24418407aa814080c002c50321603150110000b11000c124504006140c2035100e03031130500b0400184e20490003400142442104035448003400400c0703a240780d0140c2da5130042503004e00818480000071080010b030702469035941d140948807042e944c1044c1c1c0b8081e80321965400e035101d23000e4402c03400450383ca03140c0c00c65a84040529500038000c1030f000d107002d04010740a00030544040e0002031500c03000902681c2d15108902c02d04d105820240e8440d25002c0e000c4c1e401c001c0240481403d10002c11031303100640ea0802c0041c1c3c0d070708007040001c1001401000030104031030070680c1c4c4c0c50052801708140c070000700d091011200755003c0300f1000034460301c450208040b24081d150b00450341d82032210420280741c2e0001984250002d00b1901071051540741da48042c8182d0340e0050110107d800340c070124002800c801c20742d60f406088400e00140d8400c0801c4000354014400700d88 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 123368938 1250 123367688 123367697
    0x501230301150807080c01050a08070807051209010203060109140607020d05070e040c0e160c29010f05091b0702090405010b060304080a031404050c04020d02160b0106090602060402060a08071806 85
    0x700302070038003880a141b550209007055800c1107801000602043c50050405081100400000b400c440c0a00b007501c490f074800604071004c601c0c281006ca4000d41c0280c0340e05000c100d008100050900c0c008035143c00400300038200d60304010007582031045c080740b0450308071a02d00038240c0c040303540706d060084907100701c1c050a0180001403900e14196840d00015003490240011504034140c059081400b04e0251355024140303055060002030080d00d40b50b50030801e0302c40d032003d01d000002d4541c804031903203007034410484140c0006e899460306440b01000348003104010742c0c000d11a2401500d0b2280c0d81d607a02602410001c541c00e50ba83c0002421a882104c08842941c40800c04031a850384c1841440f6a04908004440b0310f8141915113135552689010241c1c030950300013036014031520b40c03601074407002c2121a22a00107080c0600d00803000880034010700f8000307040b217400010039a2000440074010f5401808030751801e10140710480720f0351802400b5000703202e50000603140d400c4c80108080010481d582d41c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 123370188 1250 123368938 123368953
    0x30415090b0a0903140105131e051209011404030203071e0b0301090f06060f171801060803040302010809030a090302040c0e03100b0103110c250f0303050408060a05012303011508 78
    0x1010700d80c0040d51310000c00317160300d4602007100d8500002c0ca19020f13150402c2030040003010848031a03010003189075009000e07004450952031039903009005003195a800340c84900000e8440303c0d40d4489c50103075100203503240c1d0012008110340311420047e074030001a85a0f0410429441b482c28031402d5101703900803485166501d25141482c1001e10801d400b4000503e0149180d9401300001050403a4054440e808801d031040130404074001c141460300003150407030082c81940d542e00100c944940040c44164080707a007520004150460110440da81184d0a45a00140783c1c115020b1100522403182c02d1000d018070740c4c0c00e00ea842d035010401140c614000d030710040792141140c1c00040c1620900e107064450703070805116068108901003001c0240b00c002d46000982000f008800c42d10b440441d40c04040c0d210b900c0440030050580c08002041036515800883d400764965521020480303070244103031641c1c03c21050056400c050780d180300700b8018100a0011401c0604a1400940c00c1c4440d8081c02da00c0d8440503 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 123371438 1250 123370188 123370193
    0x603090604060f0203090c19090606081609050d14010b040929060f19030209010b0c0c03030301140d020d060e0a06060504140609130807030504080c0f0102030415090b0a0903 76
    0x3801e0481d1600f240644c00e46c00c1c5008080c0e924020310191511802d424074015000b0201c08035408001e044590040c481140e8a10300603000030402da4000740002d00d01d40d100002140180000d00444034007401c40300000c40992103400c0000c000840b4684103540300c00c0c000034156030302c0c0035070307040c0c2070248003040700050341345001c075010020109461940d01c20540802010340d480e5a082a0321080c291018038910400070807091902280ea04005e601c038907088004185400d000c006030481c090132508a480500c981000c150f6240024455140a0085a8825421410811340d1585500d2015180d500c44011503a1480140c40d112201105e40780d1281c900f00303090056034020b5500405082e242003108003490b1130101c10160000b8495801082d8081c0072454000f041c6507070b0104070360084452929500070340b42c002d05503401445803510701e100342c50002030f0070700e802c2884422421058006628251520110860f0003456034888002e0040c0450005072415500008194001e5255501e01c603803415407 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 123372688 1250 123371438 123371441
    0x3020a0b010608061201200f040f03050a03020f07030b1803120103050115090504080301090902031005070201060906060f0921050f0d0311040b0301062f060f07140f07060209060309060406 82
    0xa02c9414900ea04016200717501f00040c4401126040801e051140d50708100c0001200307511a41e131140b82040d24650000080c048085600c22038184030f40d098a02084108054a03a1001580000340075120060003013642c80200380103401c0344c1d211030000e581c1048031200d40345074540000da000751003594680b900c0702020340c0c20144031406001d6040e020402410245c86000d06404140544005503503a6003c0c6800d540e800c11103002e0400c80c99906100b18500071100134081c0501d4881d9661103811301d94085041801015110a801c0e455501c4140c468a00a000030601c0088800f1104d0281080d4001000c0381e07051006c600340e5100c0f032008081d01a50508003c04032140e2014003406244240014030000000c4d2041720b04440240c9004000d1881460b00e501d01c00619203246001000a9071101004c4440860824420501c0e40d140c0005940d2701c24064552070b5800d05855030b6207504018090340d000c40381e0040c0581ca400713501c0060801408100ac00c00942c001d40d407410385079000c00200001c001d00c9 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 123373938 1250 123372688 123372709
    0xa0b1216080d0c11040e03071406070c0201020604200310051509010803070602130f090504021206131e05010c200c13020913020d0b0111030406020c01080403020a0b01060806 76
    0x8601c010040070a500310020304a45000000504a002c401c80000480c0d88541000780054009010b80e5616422490419001400d00194000f04e004410014210b50f0290385091901c0c0c0d0103802500d02d60741c03143d65000010900b100386c3c11254003001035950854404000349130518511403030004841c1031807030003c3e88940c4507a007124422040c6078014055a040031080ea180e45030322140150b211280d044008080c40d540b50080e5044001c120000244130700a41c1055000d039000365403c42d444100d00300c0e01915007034111480e204010520b41004000f48079401086407003000030001c00f2510303101e41d444609446c0c24400e55800224400303914102402501025548004c12000500c0c001c000d06021464110a000c0008081c990106046c000c5880d443d00c60185c4503c040700455840c1c080e14076101c01880301071881800500c12001d9800c1800d000404c81d000e130340c0283c000309054505030b00110f80107040108218110300440a020340051607203900e07035010305101d895a45041c5029814018600b90 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 123375188 1250 123373938 123373949
    0x14010e0f161202090c04050913120309030e060c100207080301030b010b040810020c0307022805010503010f15021e0105041502070c0611012013080304030b010b030a0b1216 75
    0x510001004803400c42d00c11041d105a064400b40c4039a503400d428182c46019a520841d081074010041080240164040701127051203940c2d018078072402d040f011801c4ad175403a98014041815804010014640b05019209861541c0c040700d6103898450082d6043e6000100115010400400144104111a403505000d024079915280c1041d02d0030b40c03c0f80d510f82c404040400f00560010b04a03285400a200721884650054941d01c3c0c2d114604119940b20070106c48203440c045445031000c1455881081180c0c129804861040d104a0410202c19500402c178074401e4294480c810b0781c40d2003a203c640c0c0b58251510080c0000881e4540b1b0f08054112071030b503003a07405440f4410031118001500c501c1005064500350301d8001200ca16008201c5c1c0144401c07400c40d00e000c9031640403400c2604e0b4580040c181e610600d009280d1881c0e56011907a80d9005501004240c14001401482011154800b0715480005110003041500740344001c940c5001500e5000c1c061500080300d091411040410305000500 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 123376438 1250 123375188 123375223
    0x9180f0609130209101215150803040509090a020a15080a090201171b04080715020f120901090308040801090b060f031902041401260102030403090e0414010e0f 70
    0x2030141403509580c0c102d281c000b84901407400110300780c1c40c0d5014101c0054034000d5520360075003080f403c0001e18036030131400303201200381000307200d6181c60b00802c144411110b0303440003503084c5404c04041180c6600014403103030451140914240241e0b40761002d110041100000e6000141100707600103281c0c4000903c4c0001c05400c100d4030703c0050341e214480c1441c0c51140d110070007440d110244c0c0e28540324030f1701c840080e115a0100c3d01240717100c0042211000c4440f03074846040702c1100842c0c183d03114a510315549016420281600481b03900714402020703031400514184102c5500c5e07641d8014160483d800841d40340e03650b5000b503000c201407401e83c1034210f001102c8000d2455204400651f07905038454440441c0c0446454280c01c549594010303110382c4da100740c1c81c0c0070325607120921110a403120990044505080e1a01150004810300c200c0380125090381d05d44840d10305204192103229005801164a007640301c0d06d2880f0070800b0711440c0108085100a05400b01d6030758010f82c40c00c41028980700e81c14 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 123377688 1250 123376438 123376441
    0x6030b0604031e02031212150d03180506120613090c05040903110a0303090b13050c010503220b0a060b090310090302030d051501030e010c0f0e03010209180f0609 71
    0x40d600e80c0d065a0403030b41d00004200480701d03820b892610020b04200000d405101d6080003401c0e0014110191140404010100032140d44007944041820389103c002504039030010f500101007031140200c8480600f0145000311101c1d43e40700400c480d644a0f255443c00b503181802800b4480ca0180d04070400340310b40320428000c0380f103551207240c5480d503248500f0303100b1581e80f40c19030b08160040c20540089200c0409a4100c1110303820040c0189c03604030011101419001c0004e142182d200890000c099001002080c101c0004c40c0107549640c0301820880b441120140c0341c0030151406d407030032410280f042d441c101c5281440807015050303034800d03044100141000d1114100e80c0c0c800003201543d0a0036030f1030105500c0102d00b41641544034402001c400d40f41400c007008001c20800000103035402081e49d0030003030f107800c0a140e40e08882000402d180090618103a800140e403240e40608204403006000610381800800000e00c1880c0901510398900380c0001003201d00340f840020158401320580b10760106 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 123378938 1250 123377688 123377711
    0x2010609110a14090d0b0109140105010804080306190801020309010609060b0a2f0a0503030601020606010e100f1412150603041502131701051030060b10050a090603 72
    0x401c01d206001c3c2000e5007012403d1281540c1e481c1500940c00d070071200c81a6a56115425240a0322103519003070000d8000304000500755200b100c45034890703a0444542402c1da100d4400300071262404900491949900440c0412a00d5083c070055000d410340c40c0c000500c50f40b03842800010f6031700c42e5100d400c00180c18003440e0540307500601001880c4801c0582009a0030032110321100c42c0302000303085103540c8074800205081010001c0103500900098080300c1d400e541d02c1004683e414041c401a0350030003118001506140d005030906040b2045604041581a0f180c600c221900d401c4019201d0141040380203002020701d101007210100c0006a8180d480c5140945409500c5041c03803103480100ca83c00690a03c03910b0051003500041c200c8280c2800658005401640c040c0c4000e41780c01d100b0b03045001d80020384040d2a440d00d03031100c1c0801e102c0c0d1140c40103182122004180c040040c0c58543c0c540d4038641a40c0e0710480050028503194468a40361149544003c00c101e40c540c005009140c41c01006881c07 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 123380188 1250 123378938 123378947
    0x30105060d05060301110a02060f0a1104030605070c1b050f0a150c050a060f020403060e0715030c0915090f060305010608040f0305120114040b150d0203070c0b0702010609110a 77
    0x1e040aa401040325254400843c3c010880000c000280b0b0b4000301305800401c1c1d0100f60680103090006d58034280761a151100c0013201c980441042e100d0a08010400001e401908084ea0003d500c1c10825680b80654480701040f00701e8001004145084c00000e200900e071419406410050907a10410740c682062181e040913100c035440002880030014815080000c02c2214055a80d400142404420700c40b101e8140a5007140c002103440b030307050041c1320880d0b5400007044411948900b020051022003c0025070007020000d00d054100400340c5d00100c1e143c120b60580301c41d41710403a5075129006282c074070030700300c01c030179a070803010030142414010801517511000340c540054000c5043d00c0790700c0c1e07145001e44103446141c029099400e0010000075903c0c814943c034440307005042d1401d001c6490610204905003103829418062440e0511078500410032660145500906604000181f02c4213a11500203410045600c000140e46540c01441150524083c3c8800071020f15429400e001d00f03410041c1 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 123381294 1106 123380188 123380197
    0xb0406110f0c030d050703090c0501030519060308071403040f06050912100c030b01030b030303150d0203100b03071a0d0905010204180e0d09030c030807111c03021203010506 76
    0x301003d0180c048c140e105544003402400590400b0b00550041a0281c4040c0101d81c51070101180c0a14600c03a07400954007401301240c6070360380c070301e408071204c00c82c50303281c2e0440d8006004c01c10120381c92981c6081921801e0030001d40b2a42c049020072000380481d58240414441c05c203440e00d00240e02d0f4442c2d8400136055600340480d507120001502941c1d810f15245400d5401080001c4101c013403803c0c0001010002006101201c4032500000e103460080050041900d544040b201c541d4a420801c00c401085400700c0301550312118080000710b401401c00c0e1800c1c00c2e444401c0041040420740c1281e001e0f1000a016400004072681d5150041448001e2904d45101c0c2c8031640c61104d00030382403e17080b40c0d40040c6556059081d40d0703030521603030014903084032412401c4503540e8069640b0050000f008102c0c1500c1c51003211103040080c5040c40f085c0540d83c41e01000c10041c070464403140c0468 = true := by decide +kernel

theorem cover : BRFrame.Cov 123201438 123381294 := by
  have h0 := BRFrame.cov_init 123201438
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123201438 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123201438 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123201438 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123201438 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123201438 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123201438 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123201438 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123201438 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123201438 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123201438 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123201438 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123201438 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123201438 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123201438 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123201438 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123201438 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123201438 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123201438 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123201438 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123201438 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123201438 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123201438 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123201438 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123201438 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123201438 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123201438 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123201438 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123201438 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123201438 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123201438 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123201438 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123201438 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123201438 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123201438 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123201438 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123201438 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123201438 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123201438 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123201438 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123201438 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123201438 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123201438 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123201438 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123201438 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123201438 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123201438 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123201438 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123201438 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123201438 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123201438 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123201438 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123201438 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123201438 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123201438 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123201438 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123201438 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123201438 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123201438 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123201438 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123201438 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123201438 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123201438 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123201438 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123201438 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123201438 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123201438 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123201438 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123201438 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123201438 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123201438 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123201438 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123201438 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123201438 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123201438 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123201438 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123201438 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123201438 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123201438 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123201438 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123201438 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123201438 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123201438 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123201438 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123201438 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123201438 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123201438 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123201438 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123201438 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123201438 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123201438 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123201438 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123201438 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123201438 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123201438 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123201438 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123201438 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123201438 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123201438 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123201438 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123201438 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123201438 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123201438 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123201438 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123201438 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123201438 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123201438 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123201438 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123201438 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123201438 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123201438 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123201438 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123201438 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123201438 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123201438 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123201438 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123201438 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123201438 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123201438 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123201438 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123201438 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123201438 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123201438 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123201438 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123201438 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123201438 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123201438 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123201438 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123201438 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123201438 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123201438 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123201438 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123201438 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123201438 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123201438 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123201438 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123201438 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123201438 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123201438 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123201438 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123201438 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123201438 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123201438 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123201438 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 123201438 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 123201438 ≤ n) (h2 : n < 123381294) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
