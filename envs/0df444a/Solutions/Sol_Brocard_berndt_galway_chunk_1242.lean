-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1242
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:56:48.283796+00:00
-- url     : https://prove2.me/submissions/7dbdac1b-8cb0-41ae-b4a9-d3c47f0ac2f6

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 223201438 ≤ n < 223381294 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 223202688 1250 223201438 223201441
    0x601020c0a0602100e010b120c040b0d0804181d0a030e011805120a291005060a0807020f1603020111010213120317040b060f04051902090d1704030b 65
    0x1401d16610040c1114140d40060900b030220403412030140503800c2c0d80314865035a0b05992426691800c4008103c03400180c0503282c0900004140800e07642e003902c48500651050450100143c680300c211001c85840710b8a1014400d403c0300c2c403034090040b4080300507076600320322018500c020f404604034094921907182c51180510100054560b025294602003002a6a0341e0412060501403040d41049544000f0354a0b2680550340f0301c40004a40710202c10b4460442194412482004030344075000301c003000280100c1c62500740085c0c01c9101c2e1004001c20820b070a000704051038002c000e501c1c6441070340d070241d4441c64a10700b00704841041ca4032060f4005030103519011075030314041c42154001d1600ca0314600c21582080707055031304101007070422010880c600162100c0750089210f00c600a902c2240500c2c0782d814404200003091004081c1c5500c2246072806111082c041c00b0302c501c804600110025031901024000a0a0030480c220701516031054074040b00401c0090800400c140c84c8140c0400a25 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 223203938 1250 223202688 223202713
    0x20105180714060c03040306060816050f0d060b0306040602180103061208070201110d02013201060e18010b031006180902071113090302010f0b0105041806030b04050303060102 77
    0x1240e01212030507411205090088250100e9004108079014000b07600d4515510029440e640c0a83d1054505603079401c0140403248091042c01707038101d40b010203030050a080c8400501c1c59040030b400740e4400d43d06442c0c2d080800180741c000580c00e010040540c0d5940c5820700b40a00a540142c0380c03240c500c8070003039140c0307121340c024440d00341962401021017965007820b503140003095100e40300580c107000f0f0042413100c0b00c0070700b00440a409421540080750b001641203840d1350a801c0700d002541510002d0031100030040d816500d0700e045a4540c41c0c99a400000c04002c5100900801c12103c0c0507807811740003103143c550260046004e052203010a1001540d110340403240c4040c00c048040b802000d80004006151168010781031050083d03040b080e240d4814000551040100d8007110b200035101e030912000d050b028403071a0003601610070140080d8041c3d0000809070711072030203004e400b07542c070320300581e201c66107540710501075588a0b861112504050900650f0f0303030811101c0c1030040c803808020400 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 223205188 1250 223203938 223203961
    0x90303061211120a120c05070512031905090409060603170412080304060b1011070807050f120309030718060603140f06031f020a1704020105041a0d02120106020105 72
    0x80160400a9852082c0c400000c1122030030031640d001189205903d28900890000a00410998610780b10390b580c60900b03281403410081c190344220300c03415003d0400280c0c0355010044481c4500070203000200d950300300300c1c151601c2c007030b5030a410380061030618400c0801140341e004034143c034041e40b004404001c0c1540101845d00c42d9000d00280300552421030310000c1ca0358000b45404ca4072401001c00d001040c82c01051400401e54140d200040482a0b03404403214140302210241103d403000c0c040c0ba5041c400030a011042803600b460258405100702c41c0000014820f85400c140010191103405540f103120710840700c0c030100f0040c542840e125002a0141c001d1041011807504005e007030b00c46668002a101800100901d62070305401525880010740e04160000080314003942c0b00162a448a400010a130798440e1401050344400300d4140030240c0e8200f0151800c5513010162032840c4041083c0782110b9004020646244500200d28081074440745a4058143c8004d68000c01c900c0d42c81825149 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 223206438 1250 223205188 223205219
    0xa02010b04020702060a08040f0b0705120708010303080621070909021206090705010309061407030515030105040203250e0c0414064906030201030e06070f03021305060c0109030306 79
    0x207610100800405c05580e00032514141c1c010b0042c030840c6270ba00c0098955801c1c4080494035040021000a90400300070042da694507005007aa1a14848a605550b0094092800503041da44125100c4403445c3c0075501c05410606040040c80540d524140d0341c03803000024065820080744a50010a0402800500010003910424800d0020a002d41c40e01c001034008010000080d101940c0300c142d034801008805002600a0483e540c000035907140c1060011aa900c2503554103100c0e0341484148805a40e001844050520807400c0c480141d8401040060000a82c1c0c0e00060b8103e4107441003003d1601d50b03201420403039140958020002c1c4100040001c01d00ca149040345003c28451140704103000800a0740c281c00303035007888402071003980403250390135021900e8615403c40c2c1c0b2002d09104550745402010449102d034001000181007220303019002000c40000c1c03800701540030905441220f20601040010003021700007a5403080340c40e0b400350190100c058158082403c0590010740c5802629041c0c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 223207688 1250 223206438 223206443
    0x203192c2b0806130b0d0f020114072018040c03020a09060e07030b0310020706060302040f02031b070303061518080d0c030503040203010605060c1c1701270e030a02010b040207 77
    0x100007070340c49408100e0220034a25400315200d660717103102c18103a11081038090382c0d207000e0340b000000d035a050320006000d150050441a0765400074868080041d45d17820001c40e44000600c00c12101c41c851101103000341101441200650540303c080c40309011946e4540810b0368001c2d216a00312640b01c05440040d0340442c072641003405c4043d800035500c2e5102c0d51040700107000040a80d12200c81c040103460903600404429074569688005c1002149810b01c503500c401ca01c643c4c000d50541c94000f80003070101c1820340c481c0e1805a000100101010720950003940509041091110b210760380700300040c401422410391400002e1610b0021410780000100d0080d2a5415907035440b005c1c032150340403246600003800c102e03055034951201203050368551000d00b00c51427624004010705d041450341030010303190180c2c5c14400e0000314400034086101820304603040d101c0c80d0000c2c81c11018603030003c010401512811030681c0b413030443c45e0004440048020300841503254006c0c0300044c510000c0100700d2180380b000 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 223208938 1250 223207688 223207697
    0x10206071d1206090f0c040506010e01120209061207030b12100c02010b061620010c06020a0e0d0503030601090e1314070b040b03040b0a0203192c2b 65
    0x40090344849421010700400041c054003516011860490b10b055020748031011582c101e1801e04c0c1c0824000c0220203070a642c1141c061059044c8000007030800d40303a00040c0d170304011642d22002c90207600b640407103000e940042c5c40c07e0f50f0b070300b03040c1000e0002c060700380e980000003800c000e030a034110315120101400400c0b2000280046501c001c0000c0c0040141c01c10318019035480f44102c1d02d1030781c0e428000d8071b2031243c6250405640c0c8018544440c1904c000d040f08410701040d10f8540d8800e0741c3c80226880e030b06901200060340d8181002c0246c0300009025112075000b81c4e402215000c0110100c05540600400e0b210403c00d10380711000d400c000d000c00c84415481406000a04000c150f503c40007462a81d405003e6420294880c1219091644142c00c04006802c00105100130017044410f03290344401c80500c110b00f182000d09844c8800301c2c030030700c1c0500e14503103500440c411414007105c440c020404800089644002c00341045d91105540c58140e001811100204c8504200c0c00e6030102107000d60390f49 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 223210188 1250 223208938 223208957
    0xa0c0e0402090102151306050c0901021c2a0f0309050909030c0307060c0c0f050a0b060f03030a0e04110d09140105060d030c080409091505010801061a031803030403050d0b01020607 79
    0xc45d40d280c034004146942e003040c904003003000314865220311802060102c005c00c0d52000701d2000686442c6014098132416441d00c1c0380061901d51004411011510146e003c18070f07000d400b6804003441001b104041c204000030741003542096041000d01c0c0860710300b07644000d034941e03400f000700380c50340100d04110b00c480e041000504000746950384000c2540340c041c10030f02c102d40d905840e0115146109030003142c260340040c0c013182c10b100f6802c0f040c6612100071501d1401c20004107020079100d0188143c13071000d0001e0940d6892840d030f601e40100002a424401c0c080e00c900341007518030060b203074464054a6090302050b40440051060003014822070019080e024104010f030780841d0711003607800e001c0d41c645000f400702082c1c0d0245030103851403143c0554000390766980b150314100b04441040c0e0004940da854000e00300100d11107030341000d03411411458416140c2d580d270310035007035481c6104543c00d000b07004c000100001c00d80c0210281421962021081004c01501700042e42e84a50035110100442d00740350 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 223211438 1250 223210188 223210213
    0x50115060504060c150e0d03050f3304020307030b011209350f0a02060f0f0a0e0c0a0b03040c0b07020603010e04050f01050721050c09010f0c0503030a0c0e0402090102 73
    0x80d086404901ca204034606445c072424441c411124400350702412070708009407a8070b107180e26004031038008810807030300f10391420070300c0c030f42c22110a803025030444c02480c0310075500c90b0000c03004200900000c00741c400d650701d203000c4100034001c00703d603480c15000c26625112607110b62494030881803400ea2141840702380c041440b43c4000d61140000720088100741d229007069242c01d00700c001c0c110032180c028505858182000f00030b4100342c4020020452a140c4404200c060115030070140e4200282d41c3e40000c00c12b1040b45e250b41014204115503130400c100d24400192010304034010b510950164000380410307512049152440d1040950103540b0600034401800b2a1072418584c9400c64401c43c101c4043d0000c0011441c20340d401120007001040050405020030072551031140c40e1340d44009d40401840ca40400030702498052181014100700180c00b04000d401e000e12010480503802000300c0307403641b03804501a0090010307282400f001691202c10750005090600035075400150513000783ca01c062400c0d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 223212688 1250 223211438 223211447
    0x81005100317070501020f04090b03030c06190b0a230603090a021c06050a0609050606070515060a0b1210151b080d14240a12020d080d050405011506050406 68
    0x400306008540e90811041000800034030041502c80107c52200e40c485252001440440702c681058500903001089a0740c501c400c04a6900c2e844100510710003000940880b03500c1c02060350145080d0805e920031030100d40407400307100c81350315035801280121602240c1e0040c0080c9000a0f03400343ca603030344511241030051501d1481e40c100f11000030200440c0110a4417048291030056480c1001c055039048184031018150294aa0042094506a150119a503151a038481c440141d080d00e442984021032420350300d00c43c60300000c1551489068440c041d0000100003500140c4000d1481c020100e000107c0c0d070803191003000750880d161261501020b504540107000807004c40101d403c02c00c108101500e007451071041c2503490b080c0d0f0340400068a004c1d02c1c0203500301d0740d1510050591406c1c00c1c6190043d1b030f410202c02c0c10340300500a2204480914408507030711004511005080320408151001c0301e074a90351201d445640a20000d20620094525100da6901540541c2c000110108400c2c03000c2d6028 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 223213938 1250 223212688 223212713
    0x50412030e0405040f0c05090c0f030a0605030604081b06040b0a0507030608070803090a1a03180a0c0e07080609010f0b0702030a0203030a4a010c02040903090810051003 74
    0x24180722984008050000301169001c6808075401c400340c0c1400014402d1004030b6001910301a80c00c64800d08002c14803050341e0044000501032000000009555071039141c00210080201800300c0e02c1a040526006240743c0100070303a6010001013900d50341380e46030b000512a000c1d0b07401080301074254445104003006001e00401c03a4050546601d0300040307840b07041080c031004186002c05140c490002008000300100103500c0340902e042e10041c0f102c1c01d02e48402c1200d801011070b0034810f02e01c00714604658280f0512420161603000060340000780190960805441800280d039942c441d550307000c00300440b95800b2702503074101000150b028880c80309514014403041e17000a04a503a000750036400245542c2c000c0c1143c000042d402c003409400c1304401405560300d041ea22942c200d8100e07da880d1102000d0407483d4600412309030021041c1240d011301000d410302a00500305024500d000d04001d01500d040d885001170074400c1010a60f9961481d100340e901031618022443d81192035529110884144e = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 223215188 1250 223213938 223213943
    0x7050702010e0307030501050a060b180126010f061101020304050c091905040503090405070f020d18030b250c030903020f0406150810090203070203071403090604140a060201090201050412 82
    0x601650018040e07a00b013200d40c0085114900100c0e05142003180c400585c1c43c29800a0302c0d1743c009014224035110750710003040303800000307180504a140044038045a01c9003004c109020b0905640f0021842c900521003601c10b95280f40c60f100846181000b0003400c07840100d40c082c040c0d810031109900c1a1a01c140d0040d0003540711000300c290a0f04401c050405c980c07080da02159507900004206141b03060502515038418040d0920b80001c1a031150040d458041000c40c0ca0108003480c84000c03d5800000620009580c01c801d00142d20719011500d200c0c86400006064543c00d0401d20b15600f07a0b1040705402d160690650304c0b0156a403840d401e21441c0e0f10020503481c0c0c059107440c00402c411a0070f03060004900d45035500d841070360038043d10521000c20150041503a49004004015031641c0020440c1d003031aa201c21541d103031038003041c040c0d4114000ca12005030300c5080024001558419030ba640c1904c4001180d4440b00340c2d980711010f07400c0319a6000005c1c0811804d10041200440124244010a0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 223216438 1250 223215188 223215197
    0x2010c0e010c110105040b0d1d06100312020715210b031b030114040506150402180f0a0b0d061d061f02010e0607091706011a1c020f0408060f010308030705070201 71
    0x64860030300903a2078208036a5540f0066a032401d0780400c101302c0f0327800000048407201505580c01c0500d11100400d050740005400040d0070000c03554880d100300004d0b8014118000c0303004801035046001807042c42409141d0440f4580041c00c4003410607940b0903604101402002401d120321a0024000160840e0544542c1035507201010703080c0c1c8004601140c4643d1050001e40141d01d000d40c5d0404c03400180b0700300140560b206110000c40d41030031003810380b47c04201315840700d010004500050341c4400182c01801301808003144402c000101504490280c0d600e0030130b10540040000e1030b6241c0c00508a40803036203c60051000e01d404080040c0c604105403c910012500f40d0403000b003a450020140c41003400540304140402c07a4074070383d020300409800c50001074441d551401d5066080b201510390004065500000c28082e034400d5000750400405c1c090a0640d1075200d6840840090b412600c10b100d014002c0400060a20054104060591342d0003100039095460f18401203c80c0d41003204102d0500 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 223217688 1250 223216438 223216447
    0x81815090d0c031502091e0604030f150c02010c0906020a1a060a0f0e0402100c0b0f0903130b071e1709040f050a09060c020d021e07050a060f02010c0e010c110105 71
    0x1380c02803001803200503059005643c4003030303130414403031044182d1041040460b40078410711142e54030802124112500024420200401804e00c022458101040c010501d8900070584c0c400c1c94040d0889092001c1c03070340743c41c2031551355500c01b40e0707c40c10050740c000c08641d01d141000c2d00c02e0344001c21a90700540c029105d090130940b900341c2280c2581850308068039603035900080100310300d131801c1078420003880b91420548000056803040400e40001d8010b440c241e0010780007400c102005c00588821626908404080580d25055200240e111038401d0741c10028002c9400d0030342150600c0010b11075071003440344600d08901000100c498220f41841a80103443c0c2807002489180781c0030b064011410243e0014078134203d450168102c07040c000609081d5081a10403080076500800d450001a501c044060a001e1f0040d0050781020003d400040e032101080b4000310324950b1045042c0000c0c05a0740080081400382a0300f503415600718030f8400d000030051800040040d00903154800c0c0d000060400c1c1e81131 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 223218938 1250 223217688 223217693
    0xc070503040e010e0127050406020903030d0501030203070501020115060509031908090f0901230301060e07020609070b09131d03030c13050907170414060103081815090d0c03 76
    0x15075010381c0c0105192481440144200705000000500402d20144059819440c00c8450100880c1d44a001010903588200080c10302c906501220326100004060f01c0c1c1e50b50711420240018602130000368028400c0c0440403603154014847c00c0c003500342040000f1015403401c0004c6486500c007451070b42c1c03d4080c11b60f2102418900840c0817012500c10100e50792161480c000344040e507422b0703a102a01c540e05c00700040222804031105c0400c00c40d003007a4030140030748240780802e01408980d07104082d03038500b002c2041566580420b940d4081c1c6240d90949644c07d9842e40c2c01110b41c09120381450b071001c004d10845002d1151907020104600c0400181030001000c1141607085030070880f4a00c1080d0300000d9580c0206820300e465202400b01201c0309009401d0500008080003041c8190011051a200108003448401c1550402240c0b00344202c500640c0c403450441101d4210761030300490100c403040c400304185481d60304181d42400c945819400d0404440c10400300014400c0250341062070103502001 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 223220188 1250 223218938 223218943
    0x6030303220b0f010603390507050a080712050301031e0311160801060b03100605090307080703060f0b01080402150a18030614090307171c15030201030606050705060a02030c0705 78
    0x31403e00d00c0440321040d80f5124001c0d0640d8110707a0480990601d014003081c1031a0502c85509600b0320304480c0346600b44c20b2080a0390705120b4074401800c3c1d84911a440400c2050210007848224424007040038110380fa65402e41d4075010078080140540791002d8000c185149160300081c41601918145505d800340d50013860601900039020103050a110304107002d6900c09004000040030341460342d518602d40985802c42642d254000c0d03204200c000915420310342d07020060b0030050002c160658200b20340d02d107400b02c01010003041088500e03017000081c50b265070154010910498011b446540480d140302c0c002e240381d47c8803851000c14808012000c0301034124102c04040070f14401d1100042d2681c58200b80502e078400201014059481000300c603001600715003200d2060288100007586441c1c83d05c80c0003500d51800d003200c02d0544d1602d111000d000c8032100c10102264000e072000c210380741e11240e089070380380320b40c520241065019501080003900958019588081c034841c040e818270801d5a141030 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 223221438 1250 223220188 223220191
    0x9090f06050717060d1703060a0f06210507020c0d0606080a03110708010b010c060f0204030602030f160908150a061d010806010605090f010f0e090a1d01020306030303220b 75
    0x40029034907050300395000f4048802c2e54000508a9201640e000160f4448415110030504a24410b20120119a250301d030b084521016105400090852a444290003002c0c40e80080c0c2c2c028441d0240d03c4120414032452041900820b288d902620071554488207000c151000c5400481d9419904d044c0065000303c00d0100d045000d00c40e5851085400c0c1e8019000e15001031a0000d0a0b542d24200c141260360380c108010b254500d0703120b00301080f4030202c0070004000380140d50000c1d002d50b0001007040441c1d21000121403145049000c00100094480f108036060100d41c0501c0095500c034180c4000c004000e0520039900030030815000c28550788801121084801d40c1e4000001c0c00721040040c050007a05010036800341806152481c2400c4d046400640c00c84007208801e818440c4138600c20106900c2400f6224403402e01a01e08286410000030480003414500701d08480c0d011201d10b00d0101c680c042c000c490081d98010b0003541180c545425901d0481000004100c06020382c0461500040100030108d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 223222688 1250 223221438 223221451
    0x317280603030e030705030d0804050f120c011815021605010c08100602010c0503010603050411030d0f02010c03060b2b051501030515032d03071b0e010305030409090f0605 75
    0x3190291031440d001e0310010b5422601c0d40301750013021050115480000310604040010310b444146611281000b604128420302e03414841d0240342414103010014500510141c503012000700030291590700340302d565070341101005208240d00080c0e440612415005812030305041c64001c2a04000d03683c40c60b084170400c400410101d840714007007045502c0900202c500411003800248050920050028868441401542c09142d80c0d07401040a1011507414a83e1208014007110019156504041c001e80c1c842d5403082d005600703040460340007500c80c2c000c95084038010240380d81010314800040403103a0103c1e0340e009200704113180803402c00110303002d200c0c000c462581e2034074080d000910004099500c010300304408003983c1c41c1c4078003d585000900d418404068902420720581c49000c401401d480d0310710b1400244008034488042c4400e8003920101450105908405246d8558020002c4482440043d0054105010400032105c00c2c0d0803082c1c0c09032081036420170714011540c40508903402070380c42 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 223223938 1250 223222688 223222691
    0xf030f0703060e04030519050702041418010c080610020c0306070e0a0909050d0f0e060a27050d03050a020313180e0f0a030323010e0a05010b0403031728 67
    0x10311003020782621607030000d03180d001000360140c0381a480142003807041010010540410b03c10b0a641c00b88500d0030f03205025801007041c00568000c951222020400340d441c048484a81c0c0c04540780c200c81440351881c0f0501c90346171041a0b503500b004111510000c5420b88082d4002c1d00421461540d0074031415100c0c4d8141c0e2101c1710000e040100380030300042660030150003945865101d43c0403071000954840a000310385005468041410800c070b40c11006a44816003024000c96286070355500607100408200a10b25480c031840f007960303142c0240f80c080b80709030794204080030046070119114000030030019101d40102d82c03601070f2070b1390186150a500c1c0c3c407110510000f015880c0d0181100e00070040021014401080001d85c0390203041c0d20740c0a415001001d041d0741c1c03e00d00d002c084401000d80c64032407004003403e0066a6a904110b0550000c903460a0103a2501001040c00c13000403042c0e4041c0ea8055076050303011a04d84007103180b20203026081144404860030302d10103418030f81241c86440c0c8481c100 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 223225188 1250 223223938 223223941
    0x1213030c080601150f080103080702040f0e010915060f0501051b2d060103020f10020c090406200f0715020c0a0c060201060504020309060a020a0c060207030206100e07020607080703020f030f 83
    0x113800da266206045100130003103c2c40940390903660000c1d100e810340382c101c00398594502c7e8a04c00500203040702e804501c09181010552204950190310051440c0e0103041c101d51100c10500e000802c40300c560040e8017000001e00b40a1189520420190500000300712052000c160044d4401d880e0001c43d080d00500c88402c481001155180b0400c1d4440c100d0401005003c65411a4000b50380c0b150140007960290180f00350004031513200b006040c5c0d50320f6000d4aa150541000e0a280000d0050303120b19042690308400400802841101120720b100c000321055070400b05203507a4106918040c01c015801981c09000c005002001400709030041c0303114000401140780782000180c00e41d0400d45c00b0341c4c4607502c14002c2110303c84010840c0d40d44032204100040c1c0d50700711003400362803090030490b000c0e10403031020503c80100f41e0000344807801003410401002810356900c52511101030115502ca0051300400081100d07607005030398103600100c1c0c5080241c2400403c000071903040d001240e82c5000c1040100 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 223226438 1250 223225188 223225199
    0x5060c0906271008070c03050f090d140c0102060405060f0414161701020a0905040b010221090103050a0c1e0504050d060204090c030902030a08090a170c01030b030f1213030c080601 79
    0x800704800c00b0f0a03040c5140246080c000240440107401c102a0a104000402e07070386140b0b4140450342c00d148010800540d040260400105200640d55407005074880d0104095540d80001049841507501034010041031752680c40000c0f10000103881250114407503000146021020b210762000200c0000c810502117160010022103085607101c00a020f0b48104507404011380c2c00710540d42919030585011941d000321400403490b11607980c001c6044545604500b41031034500724020001120240c0c2d042c801c41c1c507a4410207003264081114080840d8058021f04508111920804003049142c101941803e503184c0c00b04810303100d208402c0311200c0e800070b000d002010061184c016000131500d0f04010303042c942ea020030b0340d030b22800c000500000030116a0741c005072f544140410152000074820a40e235803468642c542d451130788822246c00301b401e000d124041400d0003e8281c0ca020b00c220020030f5454141041200241d002c03441404080700180b1022012a00b10700140005020120061001350b2404 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 223227688 1250 223226438 223226449
    0x1107030203030f010906061209050708011104140402040506180f03061f0e07020d1101020c010207030503070219020f040f02091002160b040b0d0c0c02030a051006090905060c090627 79
    0x145c01003486945420428010b05a0003c4080d40344c0300010300005801c00c10b81001481e20303000d0390101c0d48640c01d00016403284080300c0f019104980007000659410552041000241c4c0994012941c00c0711003403007080048460310070800c078104070282400601c0340d03038080800d0030004201c4080d10b09064500442042c0a880e80b8820001d049034450280385003800c810007034030340000e20b48403001c01c0300401110303420250a504507105850544000c41d41c4070000c0c0f07409000d075001180d00c02d000d40200907c20703074082040c1c4605110603a00a004003118001002000010310100003a566000e03824403100c44541c0780c6580b4942c0d51484e9400400506200350300c0c2003004105500010b01c0d000c000c1c042081044492801c1d11a0768204507008198180d0551007211040100400a541846092611805e110703000c07070f40308104400c01006106903601ca4258005451030f0040090031070344503100040030496200b000d020f505100504040c549861088103141c8012010a00810030f4118110f4100a180c0b1 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 223228938 1250 223227688 223227691
    0x3270608150f032d160e0604050601020d080c0f0301090f060b071e24060f0611030403120908030318150405150414010612060b040b060412061107030203030f 69
    0x100c580700041c00d41e007404a078440c2c0056901d00c07829070700a4070311848100d0403082e41206804e400700f29511045070400c021050304240c46029002c2c40384102082d40c1d03003480d0186510645068005000800300310404a03250407004005104c2400d0a110044004800000560081480c43c0300883d080200d100802c0480344164007009030b800d000c2181000182c00b0501070b198050341c000b0b051548103403c5c04c1c442070b904403000000e1519004c007a07007546070750700c603030301501c2500c003052000c0024544070300056408240c08403140180e40d0044c001040001d4500002400325492450700350181540c0c1c20004d450340e0426122140141d40031400c40440c44000c010711040311580066003c81d03070910b03803070700c1d6112003d00701c240705900d60603800501030002070005814074041e00710007044516511114440241d00703402003100c50320b007041c20010140c50f150048501103a8010011841c107445e00103080c0c269402c00d130045452580300c42d0740c83c44100708280505045802900a15628604112500a040b40 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 223230188 1250 223228938 223228981
    0x3020a090203070c080903030702090c0c06060910091e020c0321040209040209130c15020f03040e01060f0c080a03020a1b0b06060c030405040903020312090105011203270608 76
    0x8140b00700442c26030310040d54503c660b007002840e580d40c8101008242948114074002e50816180001d00040f205401c00600b00ca0904005035503250b10340d1000c005c580300c03040c0e03280c1d4501c10713940005204003440756000583d0700c00030f40040ca040d11900301c919010b9030019000c00085800105048207200780e4202c003c0701c0d1860151007280603141682c0001c104030006000a402281440d0024000741104480711100c60b4103c0c144a16042d5900d00525001004000c1480180294024100c01c4032002041e18242e0340d2030001c4c0103a40e82046c4048a50030780d501210b20410800303040ea0b00c0440d4400000740341d00320843d5000343c1e41d0043d01c0c10241a4081c0516501e40417001d0310861804510320501c6160054804c40701c459031107590702902851405160440750740240307448581c80416070004020890355080c00c103410410780c0e4480780c40b8200c80091243c903852103120850303130b07000034400c150024006100042040c0314104485191040040310303040380e0041880d81d000d1142c80a06140d101c0011413 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 223231438 1250 223230188 223230191
    0x52e0c0203040e041109011502070e04050a030c15050c25120509010903020301050907030303050708090c09040f06021b0709060b0d0e0c090702100507080c120403030605030703060603020a09 83
    0x24060000035035922070351054901d108540c40c042001c0140103414140380d040018500c80c0e26585505100b9a03603448103d0400c003621509100040c9030300340300e40e100d01c41e07034000c805480401d10342d45050300d4011800b01e044030300e02c10300040425100c1a5102d01030054404407c069143d5840007000c5440c40000c02c0780c1c40f10300c5070f0340b42c01c2c6c000543c00a00c0c04e220385072545446502ca203034003001611442c0c0550002941542084100014160b000070000c0481e4001c1d681806a80c0340c0180c03d03903042c2419182412182c105000c8101d590421042298005109a80004090030151a800300301d802012980b0301d408100c0fa15800001d81c00c021141c043c214508003040120702e000d64150701e500c203002c090000641c4070503840a1981040c0401002094003824050f240d24280b4002504c4105c0c2841d00050940340c40007103807000788074041e0148907121442031a480e120219000c1d24022000070021400c1584810300480c981e1024403482e070082d407040030080b035440d055104029500c1d04582004000c2c6 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 223232688 1250 223231438 223231451
    0xa0c0e0d050604171c0f1812030203071403270f030d09060929150a0e09070317130905060306011e1203080f0702011a0f010903052e 58
    0x94804104030f90000e9004105450f02190000c101402d4010504402160000142d08440038461500f05841c0703040b1160082001d0380c1c60500740100c44944090203001840d941c0c4240445030b0180d03006580015090903c075001c1180000c802029038401ca130050707000c1c0d50b042c03250030600c1c00c01c44e0724003801a40070b0013824013a1101007919640f401010340d0101215180c200e40701c1849803583c414901c26070003810722649124207045660b803d444018140d03100c1e000b00d40010b850050800d0490861010061606c0845881c00c4241119001c02804030070f0386005140000000510403525100c1380c0c19000f00c0d0301c0d1141c071001205400614182c1c481c3c010282440200700e0303140c0c0d002c11204c0c1034800400303000e10945100b0007045907a60003034100d0412020f404040000b410303000000c040c411040c558600b4010381c0e03070a84c204d00341c0705014084650340702d43c0ca402411034641041c0040f01080107140900c602542c1c0d445003458041d1507400e50002c040d1140c0414002c0c0c00c01500180312480740c0300c052209 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 223233938 1250 223232688 223232693
    0x120305071a04060e3f07020603090715031e0f02120f010515091f02030d06090b0a120f0204020d0b090c0c0708061003080304060608010207050c0916140901020705090a0c0e0d 76
    0x400c8074045942c0070b154017010b840c0070000032001c2c2c91003281c020700348503101c1c60003400d81e643e02c880500489400034610010341c1303841072090080f2040000e82030888040d0080031013080d00600029004c0602680e003d0003042d58a0030f81382002c1e44100950011002e055144c542802450303a150b80f1000300c03601040003d8046034580f0b88034100d00442000c84003080401c4001c04070b066001d8200c01d010014105500003500190300c0d001080f4801c0100c80c0e040003035545e00114403851000c000018441103101500c4001341c6442d501608001c0c41840c4041886504400010413203d811200d02114000100e80c1038034030542089a4400350061000500352410210700749c08641600780f10090903e100040064100800d03904880700401c6624025511400340e89004d64550f840801c0030307805249070a0019a200d031600d581303400400d44c50344903042240201f804060650b4009003166043d8483c1d039000190a8551111140c402c6405900000d242220040c0080509010401c89446840c1c0600c04001 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 223235188 1250 223233938 223234003
    0x403090f0b03060d061b08090c0103140601081506040303080a05130203060408030c070c030f020907020127020a0305120c0706030b010f0804030e060a03020c100204120305071a04060e 80
    0x20402000c81350b0b0650f04400e403504601600c505208040044645401c512031039402c044124080c040c4171701070b00c4c0041054401102180e4443e5101c8003000d1001c4046056940a4401690803200d07003805d0030003032000300340820310640c00b583c07085002400c0c100070002812007038404d1070b030408180c210307001074013110b0f400090340e6000241000d4075172500000403c2c22440c4480c100c0d895239a1003201014000d40c2d0f801d1100e14410351040a0b8003984d200000103249920612510440c034510308580340c40d400e0031903220b0800b070070200400ca80010b82c1b5113000c000f00d00c0400154014040c28018195189400e100140c20400503520002c00c0c0b5003490b03034a990581c6c111040f00d0034462503250400e01582c40d03040841e0143d0308100c5130b5800c560000340782500301ea45600100011104841100c0c40c96448440c0e8008a02c03440c0708003000c400504030080c0000b881107008088580c0104a45284a49851300988105209a404980b00d50399030b50701ea0070382d02c0c0611104080d10003121040080316103c104100 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 223236438 1250 223235188 223235191
    0x503040b100503100b01030b101b020307031713140102030301060806030102070f050c1206010b09061c020c071d070c08030603010603200301150f0b131502060403090f0b03 75
    0x3030010240500040900800091000003060010102d40501c924598a400100328400266001900b001500b81da1800d08100d070070407070b443c0341d45c80c44c0080c0d0603900c07082c6100400060032a414002c00c0350000c08248000f10584d15480c2e40280140e80d1501c00f1915003983c2410381c07240d28100900700c0d044e182a0b80100a0380d0445100381400560369a6410000e4024456804010300510a41c504642071000028801c03110200a40b06c441c9413429007144640d907601c0034403031002c0d41b0b80d080145081c0d03800c00d0301c00340c207a010707611181c4001b1114100c050020398019203224100d542c80804100700442078451941003c6419405008940c140707260000e0401c0314030680500820030000101e40d039a10250702c00b400464011800085a04c0318111021030384c41c0d2082c03454032940c2004002110b440e841e0118204030f407401a140c030035251800404044c260042e5680140c0074503440c20020b540b243e8841c411002d00b855a01074011450076250240c008007043d000341c4035488200c0002c1c843e6240280880c0d = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 223237688 1250 223236438 223236443
    0xc060f140a08070504151d0f03030d0b01020a12020a06140702060406111e0702040b010906021e07150201090b01140a031104020d180b090c0a050108060d0c0602030a09080a03050304 79
    0x90b00740381d488040c140c2d11340c451030303200b240a0103401200c0080e25502460306484080c103c0c10390724001c8134110801101d51086c8148680c19001000b0102c145c0f0301c564044200c1c0201801540c440f210240c0300c0c0d1a4484944690b030340541c0009018000b00070141c4546011640843e00c5a2001c1c2044c1c0310007956918000c100608450f550011a0060100c1a0030f0b9540c1d180e41190807480000400e84c0d40d450782d04030020072800b441c2030121003e11580201088026141c0d994002c01c008403030406400d28296010070001d105016080000c103074080c1614698440d80c40361380010801000d10300d03200c881c0402c164011011245420b055401a80d80c0a4510301181d41113011850008001070000f00203100b04a10807081034542010790740c0402030840c1d55585a80541002c0724640e540741003035034030340c0170080c1c0c0a98046500d1509200d10760081950341d41010300a000c241d98003a280e0344008500750b8076000540507900c00315000c030b520b55008c2c040401801111001e03103040e203036030354014140d40000b6000 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 223238938 1250 223237688 223237697
    0x5070303060e010b2107080c1b100506120d050a0c03050405030601060f17041104050c0c10060510091a090d0507090906050705071a0702010f05040c060f140a 69
    0x10005140c030a41040740a091854240c1c0c0d020b581d607076100c1c4c0a81d8414002208913030180c82485058039403800d1032a2284c4141d4071032288a684000003100640d1081d0040d9110301d610b40402c44084604000443c40410140c0c030000d45420010304104008080031602862640715248503442554080e041c3c8034081c401341080c0d0740c1e80030586001d40b814025900115098032482000142c40d0703610004007201141c850710341032080078464107005010401214094250141da10039406603003850b40c40740341d00555103003505d801c10820b0f83d9441d04090b95405040805500c1d40e80611072403030298214020182e103420101146450941c21411106000080d801418404a400d1040d0303180c41c01907502c0a40e0200944c0c82580d2940c1100c1c000340400c0b0b506550061a200004440394014401c503641c0c5030700301080030547d0000c0c241e8089200c034020b10407011552507442e0140e50450310300a241c0220b200e040e801c2c442c1406c01c0801003004020351300300803c00021000401a56804808985442d80607181 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 223240188 1250 223238938 223238947
    0x6060a0603181b050103060f0807050d0f12080612030a0206040602030a0908190909021c05061c08090906010c150b011e0201050a06050a0602120d0608070f1503090b010605 75
    0x20702c1c6400003074445000c0d0980c41c4811183c030a81d00303005400000e5070703000d80f0f08102c500d4035800146454009401102d0701503204c0320060000345000c0b0a008030380380c4590301d4440404940c0d6550b01c4005054080280840d400c00c00303001e5945406440c98840d030010704001c3d400e2000710394000355640030142024003660f5000001c02c18102c45900a036102c0c0350800c501d03d603600040c2e071404041000c14091900000d088d5540810081c8203030080700c0303040749070040704410740052900c41c00c0107107006042164005162240312908103055914646600c2c0201811903c0b07840000c18442440e00040c82d05040058a4400340c0000e039001c0c2001c0080206500006503400f4034400680300c07403040b0b0200d540e140c00e91900c11440306505400c464850715071120144400c5598a05200d01c1c0c8201e40161000b507007100e0301030848098048040c0c0300ba107003001c2c0e01081307983d683c000c02ca040400542003012030f124100d1040c41600b4011480c2061141d0500d010045100140c6540504c010107006600c200400041c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 223241438 1250 223240188 223240211
    0x705031c110c060316080a0506150d1d0a050708070b040e07030605060d0605030c03340315091205030c0d0c122912060c0703140a050406030b0306060a0603 68
    0x1140341800b401400315607503400d0003103450907003032400602c0f5400070301d1002c0000c082020b18010346010f150044c040ca440c16800c100481903075045030f42d05c0f140081d660341c240c895a148a0100861060601002e89201c5119080440c00c080c0035400c44911603025810800401d500034089030103c46c0c038014a603d681c0c5480b20110301504055114030743c0700a010400f40c0240b1000c4d40a10111003040381215482d40c1940145901e45c0c03103003a4031540240c21a424030502b441150343c010324511942000400759522036880d2050072a002e9030001c070065540303c02008024200695107030510403400c3c540e086203000d090118140c030402c0349601034107460310b000902007809580b40091071f04030b541d024080180c25940382c6124428001d0400c40309c210204d00301d419814820310445000d0007150203040c0d6959080014442544000c404a0800102105051a0a080c04e0281c40e500005030783c0c0c3e907940c030b00c0c040b0010203983d004040648282c011005100480d40c1c1c1560301d0084645500f0007082c0200d400 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 223242688 1250 223241438 223241443
    0x6090812161e0b0406020d060821160b041406091204090b010302040e040605060a050f03070504090c0b03160207091119050c0a051f06052101020f0c0d020705031c11 72
    0x741402440e83e00741400740300800655802514a819820300200700540d6203002c0207136528030040c3c0129001e02c04803040b0220405003001886900076140084080c181265104020000704645c05e07100341c1c3e0300113554000c3c14030034400301303402160500041000b1980b03091901003d03c15442440b019507518150000c80382d000c1c1c0c06031030003426212424a2035140c90704090001e4402110100c0c482c01821002041d249481c00c0d0503c40c007040a0006e10103941404103101c001c0521b40b00c1a22002078018000032015414001544179900010001541c000311001c06482e0290641215540c0c038105100000d0b08440c0c1015120030014011112610301d41d280801d841c0c600c520200c0c00828014100b080c014040d000420441c140028151210748a10280040d01107545500840740d020f5020302030b5403d0890304820f041c6030080060001464040e41202501e0aa40145082100360300030b9440b005d10320307405000c094020801a80981700c00d5501d40741d400385c048084040f10050084585030700d8500c0004 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 223243938 1250 223242688 223242743
    0x7030509100501030f020102060105041a0f0303070f080d060509042012011b170f0f15060406090e0a0c0807050f0f0c06040b090a080405010503070e09010609081216 72
    0x1529402c000a5850741417091030307030100c40002e070b0240c81018000107260030103100c0c038040440102040200310440d0300400815405645a8545c90b100a010550129030b0010291608070700c210750361a03881102002a1003502c4066110a100351907000822000c41c8001186c0f60000d032162000410f41d0026000203004032641e2190b007240e5611f0403007803000d40b082c0800c622001e000580c480300005010340c5900c4000750030403204019a0380407900400e41140007204982c1d08002d90b02003003501c0242c0c2a011906c29003042e44601300003146802c003040004005000d07642c00c0501103005000c40c924400e000703000c9000243c420803c001c1c0c00604039142c0c3c5540420303a0041c03110000255a96220340703005990714941070703038203550010186000c11400413000905907021544491118100340c640801527607a500020310031024820f0341031003001d0542d10401c1c2540608507603205c80c88000c0c100150b6a140034a21980440018000c020b410503010040c0880444964800400741264482101400102c4135 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 223245188 1250 223243938 223243963
    0x9060a0f20030106021204141507240b0402070f020f0f220c09081c2114070c030e0904020315010f0614030c16050c060f0c06010e04030807030509 64
    0x81005800200d150301c000541c1228840c2e8200c890840c0854810f908a20480c80703105000c00e51174490341d50b181003040003240c203c0c40c452400c07802c1c00c09640300d10400c0c6840e400103000540c1c2141c0498003070f42c01c500c07540c101e101080e2811824030340907548090b40315410050203407080300240c0721107030303280d458815000141c0e6020300400d00500105003d81440804a01c410b9036850400c01040348091040c0c00e04000c484015008201c80380940c0766054548626800c0c0c0c104004031507501c40081d6221000c40e281d0b2141d106800205040e40803000400c02c4800b4004800300090040100b02203a802000c00c00c80100442e0140b036103458a05c0000d00d0060104000071070841e40350300024203002125241c80894020f038442610000b2a240140c0383c030300c030071540100041020301038503002d000445125000c641c4500f040780c0d039168280f00082c0054019403c403041c40700e030005207070941e40d2041c04410b006007103950900e005400e00382e60291103280001c081d0820160f4030700000343d41c001c04001b20b484115 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 223246438 1250 223245188 223245221
    0x102102d0e011d120f04030605090c120f15060d1e0c06020a110603190b0d02030613020a120c06050c010902100801052106070f03020d02030f0f0106030509060a0f 71
    0x1001c00d00301c65960425810204180d0042e42041e095500b0504c0880300b011201202e180d152506669076080101009840c00c88030b48521081c5800f59110070710204a11200c042c01801c040500450b950300c0c007102c2000c0e28101030706103018800940c0340c0392542c1d80703803d500900c814140c1e1900001142d003401d5280c3c01404403030a40200245503500403854032041030103a60b03d00c0c1502c40241c1406102c3c801038524040b4030464851005a15a8a502214040b6001040c450341284207400203803034203505842294001d1101d042d91400c525204406100400810609440029050310381c201003c2451007820107004002a00a00b800401c0d840416050380c02002400140e001f808020f2280c0824000c0a0007044040c2125003080c45401c1e8100b5181c90500050110766540801162808606114082855001d115003165660980007440c0302d00c110300c02e0b0644074544031949000b407a070181d0101e0180340c078102c14045015404181a544288040d4001c101c640360040404010306072001c0380003015 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 223247688 1250 223246438 223246451
    0x60d11070c0806090f0601030609050a0b07050a030e0a080d0209060c1b04050c120c0903030d05090a060c0f0203040302040b060702040c0f0f02011404140316110102102d0e01 76
    0x4000307040e101a0398000044070040e507074030548140d540d0041d200401566000310b004000141c06034001c80d40140c458010f40d010b00e041507603508040407058400d80d000c5180031502c50000c55240c840c2c0740640c0c105100414030072001d034480f20010300c41d0300c001c0b081d4203400286c0c1d0741c4140c4820045413441c0700c6a104aa2411850407290404601a140540d203c1d50625010604460620f01a03d440180c05480d0707007456200c0c4518101300e035111501c2e2542500042c01024001600f174407a40d84106900d2002c1c2c441c0c08058542001140d0610f0200310900103114901c1e41c0030381c0e00100b82ca06996040d100041c1c0c403613010000407003a000304040294894107200b030400c034446d0300081404900c5c400d03480d8102c802d011080260300340c4003c007628010449100300043c0100d00c0e407075981c0c40e140b9440c00940c1e01e44610030300902d91480304080c2c2a1024803040b055010156410010381e41c0c1a010070000300100030100c040c104000401c0804841c03082d015815009580280b548082201c0700a1802000007 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 223248938 1250 223247688 223247693
    0xa021905010609051302030c040b0301230f060a030c060e0103060b07051605030f0a03140d110a020f160308070203010e0d181d06010530090d031a060d1107 68
    0x2078803542c05050901130404000c03401c13041418641c100f04a5000700502090310100342884004d125604c21130794150748615201141044030f03540d08941840c0c01c0340e41070380f40c034090f0f0601011000141c411350060500100401c08501c0f030b1001d8030140d4034036141203030f014248180120701801241e08140304000b0700040c643c0c1080000aa00001525014400745155940c1c1d01010f480e04801800082e580d0411014000002d00c10589c034404d04200c244a103003440f041d4070030a0110b03214461100f801c1c150024040412a4040180196061110300201800f001450013070070034811500c4010031440c03000c903903242159400c3d00040d4041d49408202ea43c034003403010740207210000d400301500b02981501804564001a084140c4021f1b074001d064501503126400112416800301005074000440b442004009103005954015805130b203d411101c3da0030011901414005403562250600d0f140200c41212442041600460403504581d21030311580d0002180c8003824032500c81105c440d400103009000c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 223250188 1250 223248938 223248941
    0x307032a031808030316020d020a03080703020d0f02040801140f0601020703030e0303210105040f0203060d030810030819030b090f06150c190c5307050f03150c0a02190501 75
    0x51204c947c2e08445a4040b00e540a0340c941030444e0010f000102e070000010440350103034004010700044c4040000d001c0c18000030a6040ba0010740001c0042d94480004e041010001c11450341c000b900c4050f41d0505040100010355034180c01d00c8010140592808804400c3e0340130700c140e800804913154910200c44507400000f41c1200240101442289030820f84403500701c036482500d10469004e811070f01d050109031401d41c1c0d070000003041d007004e8084440c0c01200050000b00035000c003001c02a90012601b003101c1c0301405852181040f02c2c003400901041002c29800c0004c0745802c102d05480c00045130300008043d0445202e98040208140302e100c0b0044448d8002180c100015030140d00c1038101300d40c40da806001d681c160036007160180403c01500c5004010b441908024100320000d91204d100c407042c14020740c4060701d07010b030010354012038030812250504454180b40d66000300d0240000d0404c0b4401034180b10b4001d000da0481c014041842040680200700110001c650960114100b03025450b1050 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 223251438 1250 223250188 223250221
    0x70b04030903050f0102070c0902070c05030a05031305060a020606131808120903090603160c0f03110115081510030203161e0b04060e031e0307032a0318080303 70
    0x100c3d81e1207003096128081d207040c801d0f91641e40d0b00400303d803089441c0c500000080e4102c0d2a064a440f412038000080c01c0d17908001d0800300c0b03440780c4051619508141801001a801640010b00940c0b0400c902e40d8225070100c0e149521840c12a50301c01c642f40c929840c41b00a040d0031000c848500f510f10b4440e41880101c1c0007626801d210145245890341c0d6445a49880e8000c00c2c0741e081e0046418400b01d085502441c6041400d40041e01c1c141c02481d80c1610380060400005001380d000c200e448a51016070b10081c011101564020904210098900281d590342c814140c005003000022420228030303007071100c0c5030300307001550000c0c101c4030000340d03049448840e148030b0700c500103034010b845507051150401e0512000c2100d0142c00b45500301440c1440a03601d03010b4080380d00f94113000d111172505254400300c000416031a0300e28004d58841c0e04910f00076011035080d90803244117201c40f11503018408040c0303055a0b9003541c9841c2580c480912240c8030354801d920340c5c1100107103000102c10071511020010020 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 223252688 1250 223251438 223251443
    0x102041706090f0c1002030d110714060103020f040906090501020a0305070f080606090d05010b220b0a030b1b0c01020c0c01030c050c0616020724080c0c0703020114070b04030903 78
    0x1c8060b900d0b2160074580d18080b200c0007169907000410040d050f440c122030408501042c3c0d00541c0d1614038202c511a048442c8d80d0041041100003042801c1400b806142c0c10042c0c504000040c82c1e65411900011810300418280d00d1207691255451030400c891900000c0440340c0c820000d640b100030f0340700c015014201c03c8a88000003903a4a02c04000319111314503141c040c140241400f40b82007043c505000381d42c1c0703c24105544c10344d2690704881140d20b07411088464103034006031800c9141030321403990040d20480391000c1d100304a00d032414004905100607840d0044943c03c82d12203101e00c1c918411800f401441000c1d0419440032412140c481c3c0c0120300c1562095003682c0401c80322170100c20644060052580c0382c94198807031800502d03685440e01300d105421100740120f0708410b0703444003290b0020110052902c0d0450300340858811366500042044d0b0466445401c035410072245000440d0345020a110281c10407220682d00c48180c107007203045505403a0409070888070f500c0d0504010f450092140b004 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 223253938 1250 223252688 223252693
    0x9041a04050903070c05090a02071b0303080a0b060405100201060f0605090f06040e041b050307240e030d120f0e03120601030c1b0821090c0118210501020417 69
    0x16106a40030088400704c2d41c3c0225010107160401d0103001481c1402090a03162590820000c0c0114402a4810b038440c0100340da400002030451500910710100a801d0440c130b10306190002d8002e0391840242c1d000d45106a60800044803500b004901521455100c902c403011048d00200b036280d4031100900c00c0035016240000b10040300018080644994812503a00d14820000301d40090041c6254120b464014081c66038941e807070b0b000184c14001a03038454200381555201d11b0103201d0000d031901c00f0188480c1820808200c125000ca41c035002030128003030800c52000711407600c406555021408420030b41794100300c1515a207045555a60141d980d1005a075003100c0090115842130041941c00110f41e61501d0701080c00c001082c10000c80d00c00b04542c85c0e501070241e540010191203010140c604a0f15140d1494100039000c41d080602800c0c80b5410015000c042c07060290422030018210351082d4158105000203005001c15240035040c010020350000a000401c01e128040084034040303c3e909 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 223255188 1250 223253938 223253941
    0x12031e0f040c0e040c090e1002030a0b01030506030a12050703120c03090302010e0d120902040b06070501020405190b03010e06040f0905011b030501120308130b0403020d0e040903022109041a0405 85
    0x2411080740d0f0441d4018050110000709101546440d04002e44051700f9008440922200303140c020305903042103d161011a68480000c0c00e43c0d84d0501846401c1300c01913010b4a1165010780314440404441821503050080001d420f01c1010300c41c4076801d6065403000020807040da0380744d8009015041c5260706a0040d828400321528514001c00c1d000301c1455191a0048420020042440a400403403426a03105070f58190105031502c4e644010950944540001641c0c4c50a200800c168607465000210740d26503125410f00200c410001203905484082d10601c1c82139403941c00080103040c00043e00030740542014524030410005400c075210070700082e00b0608141c02900411001c032442445009604500e0702c1440021030f018120094000301401454481001151030340c4404003400d840c118010703070080c0e84211410754020140c000749003080b2400e00804000d07841c02036960001d890000b00070344024403010010340e0741d0002c5408100740588240b020358050026000400082c1501c41c0c0254100f00 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 223256438 1250 223255188 223255199
    0x601091508010609140a23030307080702030d090612020306220501090c0e0604120203010204240201060504050f04020405090715050309010509070509010311010e0402161109070212031e0f040c 84
    0xc2c1720b841c810001408404400d881c01400501e1400580c1d87c0704003c042001e1140281e4800b40014104103000d041d82a40d18881031040c903140110b140e00d00020400e00c180d040c0040d661144918201400f07008000d6140e44038100024040e0a5003a22005030241480303540d1014003803074004504030303900c0314010041203e04c2442661081109587c0507030145c001c00c8140036080c4e11801080b0080d00180c0011f041c1619000300203c03000d04100380030308002c6030940c640b403050360900800d0041e0005440c00e00c441d0600840e0a4155900540024030580e21400094050002001090700034030300e14503500484495848043d02650003590001e0083d420900001c081c1000040c4401c212040030b41410103da03c3e54039526004040070420340d0400c580352540307003110764450002c3c101400302d1007010442c4501e28a0001100200356028900070010ba400f000046030f00032420010840741ea10809540c3d6072058004c81c2646640c0c042e151030041713520181302800c001c18103943c7c4544c0c410701d504d005594451 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 223257688 1250 223256438 223256459
    0x30c030507020f0a03050c031b0f0105010605090a05120f060705040815010e04031103092116150f0507020d060506100804050d110a12020606010e0402030603070504050601091508010609 81
    0x1542400c43d5a1024200c2c0300000d100303800912031510100260381c205a903041c3c1c0e1543c0520b4070141285c03d41d000060551560200b84641c1c1e00510030760a010745030125400215071458568461341c3d1042036149800503e5440c213000400c03851148005a402070301d0440d901401da60030900866800b840741c9035086100d400e84240d130f54141c030300c021007800c2030741c0d25981c0885003003411043c08003030780c0030a000d203100a480b1406d012000440441103040d40e0400032044600d0312041200302c1003041c003a42d00410110b0004404025610042d143c41d0324035084103c0e003a213003403140b401e0080d00b00c0c0741c004107a0203001059002d640900000c440401d01c003900343c0005c540d040000c0c0d5020f010343c1c102c407101022040c0641000a4550700482c10f4920510f0503807203404204100b902c4000251b044403040040940c1d02049000c01090220703411030a500b003c0001c2999007203d4011301c1e020701c0e6142d011806981c05520b1550050944180190022000c441300030280b900c207102e01c0d804144401e0010800b403542 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 223258938 1250 223257688 223257703
    0x403121a0d08160f0c090507031e11040308040e010302030c030a0302071e08010c0f02010b01170f0c090a0f05010e0409020108040f021908010b0f01050403030f0809031207030c03050702 81
    0x5249002540342500e86a120f03a000703001480d9408070500e500c0380002c00300e101490295008044c400f110500d4100b400f8261760008204da0100b5161000e9008080c4c1250242c4405543c40c03580013655400e4035000b9206442550400b0f03145820114000541c400c1303140320903040c0da2082d0156804a4031a03024140c0d5034080300002009600b254500348203a045181d0104940342c4a03a0801000075605c00761366007190340c11014000050019490901c0c407075024000e03908811402e18001c030140c0c0e04464a40c48120024000640340000403010400003c148419605c0c6641c000704003264242d60b8a00b40403480d805032081c580415042036881e40213140c00c0c4252140250182c43c1d0780081d0b5a9682c03441860381180b60105ea0042c10f03070f103030b104070040e144100e0400791840e00000268551003604210582c0c1d0500c80365410401c0c100302c00e0000076804521246121440d040002c07072600e51074400c42c1107018420407002203041c01c80c01c00c002d603a410307005240d6500450b01c3c1007007103840d05d103012a141d80d034 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 223260188 1250 223258938 223258991
    0x100b03070b030a0507030621051203091f061a03010806150d150905030408010606181401050705030d1404142a0d0f03020f070b1201090902030c0405040312 68
    0x10140002000c0f04440d40090750b015903686800214561603907403c1a0700c02d42d00280d00c08151084290a0403c10200011007079140d1003028241580ba1489001d41e440c10540040450102c02d1181140400302c0c903000701003d403201d044410014000240d401495030400d218414040c0b00d088081042a5460040030343c0e00340340507181151044440d1102c10381404410030786001d440c5e845020401148041c40034101500541c40040350300742c40d101005007102412410124200c55400d020040318034104400c1070340c00700c03c0c2130142d00c695582c2041401c5006442d6800304881c01c1a440101d03000c150801343c1d100c0c1c0d2107002e41c01803521542e52030580c5c94600000713000322401080c055500c940008940741c076032058020101295a1104e071399100ca011989081100075a100d0444030302040300a000351005020204812070615041003829203401c0303010300c100e011855955000000759107080c070180d003950401502c20f10460402d031400a010011842020b04020b01d00340ca90070781400c02c4001c0703032403449 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 223261438 1250 223260188 223260209
    0x40b0405010f020a060509010605030f0105060306040609081c0b0901060201090f02011404081e1e07050906040204080615030c0409020303040306050a02070506010b0a081506030f100512100b0307 85
    0x1400c04005441c01c40e403401c616825842100d032220000f0b2210300036980301d0040d10002148003231411091528144506407421410390500f4200b2000da01c1c0020295801600140c000c90041e00604240c4040e101c1d15031844104d0000c0c0301011062517003904030101104040ea1201c140b0780c3d031904203e088416201c0024400b200718000d42000d50322428a03841000c6056a200d0b103015551079480d484c010b9000007c070b00b41482141e41c101f00e001c2c180051200399649030740200801c108036440c15100c4082c0c0c01064824102c5d0740100d240d0341c0740e40d419203020f0300d2044111a40c6080a184a0b002480c01741081c0307101e44643d102e0031025042c680204c1e245d40d0380c0a00154101410360383c0d404c000d800c00509010301c040d400d000740c1e000700302c04004443c002d0039000c4082d941c68105110052010f400100f4829240441b050540080d031030320710481b58841841401c664250b1101c480d002c841e0b000e5036024551218031040d1901c2072140100700c207110500108000c0188a2060050584401c0d040c40f6608181 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 223262688 1250 223261438 223261447
    0x3040f0f030b0a2d0e0c0f2103070c12020a44010903050703080906010f050f0406080d050a1115070c0f0602030c070b0f01030b07050a0311070501050f010902040b 71
    0x102c2a070000c0340d543c08044e095142d108021460b07002c0c214080c2e1840c0005548941c03c8400d061001c3c4891852101c003544c0042e550f102e443c010801407040e000c8d1480c4002d103100210340e0707407074030078400d0360507446d480700511485954503000900707044400c0d18143e100e0725080c400042c4000c000c1c2e480c00320b160400c0000e0f40d1960040007050102041842ca00c1400c1e041d03c00d40b0303481901d028800c481c1100d20a448003916030020b4140202403840003405850310750b001000601c011540b06d00a1021240111004100d0083d08404180503082c1a40845518401d1412116405420030040c02500305641d40799a4001d80d44c080740741d075901c0c450481f6014801240081a4514440c030020850240901da0901740480309903240be007280c0c000c481c1c1c01c0c4681c80103c1d02d40300b0040e4102602d508102d00220401c01541103482c0c260028502a00703140c1030101c001001e20880b8020b80104030740060003034400d901ca65490410038040c140c2269807600e0900c40c0d00011400c41464800d03101640d070540400d41c02d0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 223263938 1250 223262688 223262701
    0x60906140708071b03021924020f041203030b03010606030209190e010b07080c1504030f0305070f050922090303142509080102030a090b06040902090a0504020406030b070203040f0f030b 81
    0x1c155181300940171406480403500080c015030b1043c000d800c0c491492164082501c1d0a02c007015030080c100d40c4180c178010056840c00c40c2c001d1098500b80d680d603854003c95003110746800e900908241e40d40c0354065082c8500012070682550242c000800c0c20383e007001441d11108000b44e90140f190080d004c94481150050001d0189640039102003407041444500d1b181003a0070440c07030311146040f0407800245050801c820150300120041d4140030302c1c202808030341070894000d403d000e0f660742d00e441000f1010511001590355143d012003129048804900d88c841c0b84014071010345a030200503404242041c02d0075031107404500318648039940d810b4802401c00400c50000000c0f00748198054100f22203a4030208010320207100a40c0035140d03400001444440e10f02e40b0341e0007040020011881540360404100150300c9071680707a5031110f2010000585a9120b1001500400458001a1072000c002c400c01c01c4d07084e0000b00901c10b4401c00c41c51100c040340d4544481080c54101d000082c981110360011410 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 223265188 1250 223263938 223263977
    0x150308030c07020f0607200904111915080f0f19240806061005130303110304080706260103030f0509010e0303030703020414040b06091c06090614070807 67
    0x202c06100402c008040180138000900b1604000d800740c0350000611940401004080c0d100c820051040d0f5800c8698906078481c1000203101170001401560700741c80c050340b0900d05520550160104171807001102c807010400400d050000c9a0712004135000340301080c5400020001b0505c200d8401e10b0307000381d00b43d421038140044d040703600543d07a160958400502004032414503800142901b40000e10702442c00008215a2186401d11001840400c00c860221169401d844000b92a01400c100c400b00d60301c0f900c0c8a145200e56800385000b8000d00341c021880540c010140e2003d00c404110546001e0741c405000700c6012004c5c4401004114184c3c1402403041c02079002d84880401410407194150545000c02d046038412100c050009600080c00d0060b00300b0301080052008040e2020000c40744501c0102e002c80c46002000f41c42079103000d1000010803e0540c8036078840398051800e026500d450f15041000c3d1010401c0888020480000218600c0c81605990320030300e0035a54015060740d60111440 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 223266438 1250 223265188 223265197
    0xf03031b04051509010e0906240f0406091a090a180213260111031b1303030c0b09061302130209030a2006070b040b07120f0b0301150308030c 62
    0x400da440d0621000072030341c0d9803900d0700003810b903084002503403100088001419200c2500d030302d5200e44140003d0080d10703180d00f8484100140301c400042c200d131000c080a0951070003108102e021841001a000c0707262540b01c40c07880201d40c0c099120f01d04400c0152021700640c000d54000c80d40010000c1410070262061070711200c0001c03400ba200614012010307012402c5100d02e80c100c4114070459566000b0513030013011540c8864000a0001c00101904001c028040d12002d40110032141c0c01005400321401b040c8110b40403a81c0e80712000300307110741c0c0b8a00034048804140040c1e5403041c40b40c000810202c1e0209030b031880395a203101e03402c452265a50030400556020103070000819400d020b9031407152000c12030508501e0140c010200804100300c1e43d151103c18198020b4090300c001d100210008030416815500258490b10820180d95402c1c800c4800c070105030b580d6040d00d0f050000c81180c4950a510200900206400070710100308403416404d00c0003100e21004090903401c00029603406440809031 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 223267688 1250 223266438 223266481
    0x10906120504030509100206061201061d09280606170a2316050f2b050c09071107091b0e04090f080d050901050f04031b0c0f0905090f0303 61
    0x29400c003c12035001c101428051b04040025910031000d00801303141480400010010400c000d00960741000d80802c05880b00f40040041c40ca03510006c44e44180342849407110038400da2000d607000c0c003114000c42c1109442c83c5025242140b500c000442c50040e0710102c2e600303030740c400402040040034a41c1d60885108019918000c00c2510038005500040b040c0400b080c0d04a010388405903090030403041283c0b032848560014030a0b40c2c40c55801c00d200c001c524000c20310025031429115031503401d081180c105405603000a0740520060100170040313030040705044034121480e044072082e075101c0c03403041d08270707640d0040c0c008d10910506002c0c120184108040c074450800900040381c1081c0c0d5980d400307045d50190a088500e1040403600341c2c00441c0f28880c20790321481500007403040e03041140110504040140c1301a01700a0440348030380700030303903190a0084000d9100700b0000005130303240c043d014488403500a60024904040114100150010303104101107440b0020f540703036071641302001000b081c0c8650270 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 223268938 1250 223267688 223267697
    0x40201020f03040f05040b030c0f0112020405040216050607090605030105060705030409090503040317130306230a0515010509060f031003080a0503040221060604021c02180f01090612050403 83
    0x1080721101440504010009404100b0303081e400c10082000b624004507505020368814502a400350342c4141103403c0e441340c2030070001070503440301c1070345400381c411030b0803c1e900180001810000c0302911041542d85600600c2035a466480e01c20080b60441c06911410000071000d0005104500d40b190040810a00c2030040b2444d260752481d030071003500e0600d00c0c00c0d41c03140c0000c60100300303000ca400c01141909003d512098501107014401c2000e01c44c1502010303003c40d030f50704d980c00801740720040002003c0c20800c0c0012402c0c54178203990b034003814041b96005c080580d0201040701d04d50181058410030100103003007074204114116208896000242004d54560000000000ac00d101c40c00501c0e052000c0da9815a1300e11703107801031000e80309210f504100450101d10030407400360004948a504190102ca002d030341e2b0004424229001d030b4241d510382c44886d1002981e40c0f090065810307042c00401d001d560314205450a00015038000f00d0768440c02002c070301a0262958200703940c1d800701e0303402442801c0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 223270188 1250 223268938 223268953
    0x1020409060e0708011512090206090904060b0a080f0a1101180b070309050f01020d0c170c070503010f140703111e0309161203031a0907081e0412050304020102 70
    0x100401a9111a405111000680c03028010244c1c1c1c000403840c0900072400c0d03c800d01d103040c650020300b24000070480c031003850b59445941c4119a5400c2c12500d5030a0000d2500310507040a041480091411810b1580300d0940484006840d4001085a1180711843c201500c060641a280c0118045018425a04110151004900d003405000c0c0d1403000d0710b880309130b05803103400e07601d000b61400b20700341c0066200d1007901a4054180e07074002848036544c070140c80d0103000c051481c41d01b04080141d85402c14103846011910748403c480005d504021500f00310024050381c0707400007024045a88551b42c400ca103221590000384103d000b500700f41201c080816100c0c4c41d1041c02c44400090890207034401390f0741100001400a004020400e003030800c84040003a8190502e000c0c88000c6008482100506240d145c40d4907980e03029846c0010300b410074001e003a0301e07190320b0700b5200100107240469080114403004680911391034107a000c120b104560200c881d0314812a030207000d66054000800881c11803080340c8 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 223271438 1250 223270188 223270199
    0x151903030311130e090105060a151808010203011d01140f06130b0703030903020105090c240705010f050603190c12080d06030b151807050310030b460e010204 69
    0x24498001011002e84d00c00f52418220019425944080c2c0014800c00041d0414440d07220460400301031101d560400c80005618110070070645d20301a4081c000700c2d44040000110b0340c0c41078040d4130401103400a4140c980c0c4e00d58a445541001c0c20405c0e64002460300354080d200e003081c10041982c61a18020301e0340703583d83d0718156480da0b40412811800203407210381050805409026a940041c407200160020401d0078021954100300b040c00201003a0100c01d00419824040c0122203440340c201c4001c0c070140c0000751070f01c006084280c58a6001e48031b0030030081000f0049032076143d05c80354010482c4c0c0a0600d8108504081d101c0218103881d510010026100000b400e8460040214032030200e1613460b103802603401c1c0166a9890403c1e0082030780c9868030306840c0e0740b000035650140950034442c2d1613481e014801419200246c2005000c010300409108401543d0705405200f5071003c1c407821200041d81800c0207840f00c0c0d401c13400c05218008500940d5a020700e401ca03140340310b48000010704082d40ca0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 223272688 1250 223271438 223271467
    0x151303060c111006050f102c12061b030c07020915060706060611010c080f040c050d03030621110103050415090b0402280b090301090812151903030311 66
    0x1c101c4000e43c2c0e039288410040360400e0000d00c2a80e8500b00c4100c0f040c1c403150240902070f203503ea00030400c180c00b451021420f2107000d800003800c1001c040c1c0700b51046030902e00b000c0d545800035100c50b02d5a188a04c041d40290700701800702c0c1e11640c10400c030076052058070380c203104101d03202070b043d2100c4d040e030170b40301910b20345854020b0001c1d179000b100080b40031450050043c100c54455084e01d10306905003114000b000307821112440d00240c594030481855907640c1002413081c203e9401c82503000c10001c045a0500d54140c104109642c0c2c01ca6080d640302c5c00100c030309074519409920080c4040722003602d0364042e60090f03000075402401010749002c44001200c40d881203030110030782203405a019074280700075420b02680c0046111080c00f0011140480001070000600440c0b0070340c81e000c200099951151384003074005888542d800f000745916402040d140c0d406800d0211200c01404104142444007032a00d4200c0300c2c0c2c0ba0710450b0b040d444035401d50703c00f00e01410f048001d00f206004208603518144044 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 223273938 1250 223272688 223272703
    0x20f092215110a14090609150c0f060103060c180608130203030d1e020304230115060906020d0f0f05130e01030615080102130b0318061005151303060c11 67
    0x31030b5005681d840c0542c03006041e80c43c0c40510f4161200382407103501c0752526590200c4040c01400c40721400042000106501c16224281c0d0241040c011030712808085900043c030746c2d059034820388090103444003040c0b0848410320300000f6440c0c1102801c00030042140142107440e0080c0329004042c0c80a0140d8010a1841c3d012801004500f03035640311403101186800b242c581c4012030088154614103081c0c490201c010040302868001c4011b04810010941095005011580012201c00318190755040c3c040e0503040107110f8000940074040582e144a072240034200e10801c00c68644151031111104111a65080b046d0020700403100074101083c4c00c1e40310180c0380e000f10300c202c401099024820340c00300160529548550040ea005004010110444080c05c80071342d401c036019981c0702e0356030300a1070100c115003051000c1540101014000300400140114003036a60644000310340003051001c1c1e6220b80b00340c820f03003000054031038000d00c0090110781180035030080310715002c00485800c00d8400d00382081c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 223275188 1250 223273938 223273961
    0xd0e0102150403050301080c03120a14130306020d050a020306030a110a0909081b03070f0803070903021c1e0c0b070201031b020a05010f050105010806010809011107050604020f092215 80
    0x13003c07004000360003041240100c2107106502410582e01d240c050038000f0b0049211a60501003030083c10101c4028481c1901c421111a00c51414816a2800e090000754080650101000c1c01c1c0300c001040760016000700c80c0035440240090040c0303c0c86803242d05111340d00510b1950b015400200000e48501c0c0ca005801c003441c0078200441c0d49032504c900200d030340c1d14a43c1c2c2e0120030f0340042c030640780820011000703103003581d270016072850742c030744c7c414138100c2e5403003182d0700004d50040c014100e030020001c004501e0180a0310070342201d81e81d403c9421201e1569038450744001c12800f24907505101100c2040c005d0030800f84103060104150403141110340ba803070807610040300160301c0158841c09111090244920391000510204040d50418000070702440001701081c3c1444049000305092074003d6000d03442d1802c150348540d44400481c684103444182c25103040c0c0c072070604201586103a281070795081740103549400403c40003404e00421003484180c15841510717042c0d00c5c004409186029405641415007 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 223276438 1250 223275188 223275197
    0xd0807020d05030c0d3f05090c040c08090c0603060a050f04090204050f090c04020a1202090a0305120418060e041b030c030b060102011508120d06030204060603060f12050d0e0102150403 81
    0x80301001d00c05486c0403a0581540d05e85c4900c49402e4410004015402e0011220000450141d45030348889203488540b00c0d0030764125242802c0d036400310707502c982054010482e8105690b4040c5244040004a0006036605640010448410040c2e480d00400440b180d40c005800460122030640020301111412581d41c000c0400000c1080b000c0725090261940c0154101e80071410b0119000e40100841d1701180000b081c0da5000891520075500e40740c0c0300000f182d0150450745017601b01c00202c0c200d1340061041402d4420340000400c040b150314041c240549800c400d0a111a580319127480c084403184c04204014404509070110200d1420b03900c0b240076600401c0c0b050341c03d041c034400082c00c44000c00c41100703050000380303000e00911401080c80700450341c100f0600781d1a0b480140e0804010103a5a100070b6203d403034840002540ca8060b0040c2c411aa44c181c2c2c180c40316540d80344140260b5410703880082840d0054001680d80c140641d8070514114810703c1102c02d500e2082003c00c41c06681500c040d004174 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 223277688 1250 223276438 223276457
    0xa06050114010915020d1d030f0106050103060501020106050f040902010504030b010f030b1e040b0c0d020c01051503070803040b070c0e0a09150e030d020a0311160b060d0807020d05030c0d 82
    0x256000107001006004c0c0e0b001151400340640802501c0b0120b030110001000092105c140c102d82c05d005084c1000c800050130f5038191549041d000380209003030f00c00e8a02103810312000048540c0117109001c00c86034040c1c9141c1221082e402040001c100b030081c22030600109200100119015102c128041c240c000391552100d42103003010407e205000780002c0e00c510110710548d1070348098945040d08580d1140e2001c080e610382212459460080d201d495024030701c0419030003450001504900e004000c2c0106510b8500908424181c4800c41409035200303d40c0308010421180c0b0b41343c4000c1650a000c0c41400302c4203625144145418181591040003507500c843c4c0c0c1c4000d001a003240e46404034800b100c10003d40c0c1440c5038154881c042e80042440840d03000c125007007024042d801c02c03040819043e07520f40d6110100c45426080720042e0905075a800340c00000a002820701904c00180c1c16082040c107801d0840030b608014500d403001504558501080c0455194000200503240d0f02c0c0e0341540300c2020300f = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 223278938 1250 223277688 223277729
    0x90b040219080430030f110a08160206011d070302090409050109171c090c05032b0201020421170406031d01020708070b0a09050304090c030c0e0303040501110a060501 73
    0x10320f4241340450141d034010140c80131140d000444003501041182404506500d003c40400005d180d4421101081a00000c0c1d1901442d4031001c003134402c80202d0b810100515268008030396030142401000c01100d9000f42180b901500e4003a5503901c048030345809441c0509c4280800c2c199402c40340201c80d2691640e01d503400f00244404007424501e1100c005a0038065007005580b4289092400c4034900c50341e48100380300f0700c2000d0440c0000740501900b00c034001100750184000c010314000c10124481620039042e0315541c410b000b01c1e001c6a11400c2c0c02d00180d12600419000d03a446030108070380803c403040c400b603840c105110140c0000c00341920001040d001404510000c0d07070010f80042c0700307640b041004074001807181d01603c08103a040b8196100954510242d00001c144004004c0e05502c0041f038000b40103a82038000b203500c614560303820300071000c07c080b081c0d0b122441c0c02125a41a0070074001441594420701a60b411007c0d01000c0300d516484540740c400440e807080c1c008a64605003080852030 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 223280188 1250 223278938 223278953
    0x6110c0607210f0e010c060b040c1e050c0c0f040f060602030c0106060203210613020d15080a0c0b0307050906071202250e040c03060e011a030703020a090b0402190804 73
    0x1940082c00d01c03c840036410400105500d003000f0b005811321040e20130040911055900142c0d40c024080c00400c5007064148018108072641868980c002501c000040d06c00c900c200e0030348440704030440040c030b89481500108403181c151360301c03102e80107a07503410100c0501340540101d10007000540c01543d6107a00c40da600700e003541c0068004209544c81042580c8501c807480500407144030503c1e4010b03905032500000240700203000010900c105001140309040d865081c0e221103410a662007a5403002e50744c40c25900e031201c1d0306180107002a46c590004005203d040002140e204000d4a03140d46030023a410000792564114150980301e440030306180c84003a47c1c0404c070040d00d8000310706540c0b40c020103082003107180441a0240e1110104d483c00820100510390076070390003a591200040c0074904200308614000c1a44410800e815210103100000c1409d01184890507603802402100d55503080140c13407000741401e01c0b1182c2e0056402c20014240003607407110a111200165510340003400c080c1030142 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 223281438 1250 223280188 223280243
    0x7030603050f01020f0418110309030306012303190b0a0e06100305010e01030f020103060510050315010905060702011d0303070b07030e0106180504022115010e1006110c0607 76
    0x800b60f038810000d078882c0d0410041904d0480e0200038101500c0b1040d1032801024281c84400351710491804001e001d4480008400f0758070031b003020b80c2c441e040d00b800300c120406031403441c1032000303240e600400100d071039400720150000051074110341c08644200f213240800c01c5414a68451205460103409024240c81c25001c407500340b0213203207000e1016505280180c0690141031000a00d0101500707282c800310390003508800001c120007000d035030b1079040e11000a80f940d4811183d4511825074403150f10010740c065103a91702559806040c103814204640d006407084000345a07812140c1401001e010101c0d6000c0004012076481102428124140741d500941500c0d0b0680e451a41c41e41007100034000241d08000c2201b410701203990110304c03034990703001080802c0b498503030448101a40c8003000818401c0090f1210503e2000512000140e90390141c041030f48605895409045948600802c8254800d185402c24483c80c001960280c40d0700c0c800050f071540c421481100c09039004410076108022801141 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 223282688 1250 223281438 223281463
    0x60e03060f04020312030a090b131202163006020a12061401050711030105182e021e0d0f0e0c2101090503040e040c0605040b0301030f1a0703060305 65
    0x2031001e0b05007680000d844510001c00590300d5071010000600b5a520707900300c00c60349604140740d551541003050901c40c9010f40f141d0140e444805107000080c09910000f4028155000921004003050600160f07031006007440712120283d4235100031902031403c1010030302847c0c0e4447c540040c2d81c1e11641c1e10140c641c0960204003141c01c0c1c60644108010045c03018950b0300b00e130003442c007540d84905624005619400c15508250958608020019130b40740441c41c03101225941400c95001080070151000b524918040b5030070308449520606c21440e075580c015007213007200600c0c01440d800584600c0c117855041000d0030034025444240c0c9004003d028071801c01510402d00140c90340c000e005020400040e0840303c048580a0301200e0a002c0030740c29884203460541c060241ea07078450742c45054034446402503c050f0388421500c1800a902030086080300c040311080780106007141e20750340b281e072990208407809aa451803516010f50070380d24840065031050713015440014a09003107081c03251400c500c22040c2c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 223283938 1250 223282688 223282711
    0x9150c04080615061605060708160c1209120c0e070c030e0d141203090114060d0b060613031a0f07050403020d080d060f060806060a0e01081e01060e0306 67
    0x40c025050049071266002043d05108043d0710000f00101d0140e1140601c00710440c60f444961008001002c1031541c000e01c01540c4a42850b00d41412070250703220301d022058080780308000c0e41d01c0000d0001603004481e101c1d9040200d6140d958085c0d404284070036403400c42d04072403001d001780f004d00003000c6003503048602842c00501090555501600c030305400c89425100f104445401020044001101c0311181c40c1c00040d02d242c251484094039154006841c40650b55003002d61507164a61907940c07091049a008010881d984040d46030200601d10141c220341d04280c04102c0f0400e00c85442c1980402144500000601b40c041c4500d184030021f400f80c001d501e180c91030004d01159070380c00021798081d2501160705031540e40080c61301c03400794030078068403904250500f8400110103041141e072104a407050703116121039540741d1040006510503903c560b80403880c130405008682d4451001c590340100a65488094241044000c0340d22000c00d81c0702900003900c4107102c1089060a10403903070040e034a50303403 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 223285188 1250 223283938 223283947
    0x10090606080f040f02121b0d030915110a0c080c0102010b2803050115060f09080607030209030307050f0f0d0503160c031715010f021b04020310030b09150c 68
    0x1003104001604418500001c1c2d00810309100c0d094101c5507255a006007561004500400310030313260200e90107500881201078188007058104035200c0304800e03600d42c3d03030651058140488402121702a05008040000303072000e003040c0080c2005040301c02c500030245030a04900d0441d4842c41c04290391405070441e410180030b00c0307080c1c485506c140c1c22005040503440144030050b0051641d06403d50010305030750300780b000c14036613903448000d1941950b0f00350b5182d0708144035000c5c01382c50803003080c0f080540a901010002d082c0a22030360250141c250000c4c103881c6052529201c0c1445d001e010390001d1000c2d00300c00700c200b1041c03004211210360448c060902500310728210521070301c900d0801103000c003401a108846401c051044084a201450795042036078141000116400704d80340121495010075025030340c10450b14000500514281c810031302c3e02011540c1c55003400b000c0d402c00b40c20f105100b4072070130000c40040d141c641214890b0143c0c1004102c0d5216510600f1700440018004805d061030800 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 223286438 1250 223285188 223285199
    0x30c0d230717070518130e060603030412030c0614070810050f0d02090c130f050f0909030304020f061306020c100903020d12180303030c02010c020106050a2d0b03100906 74
    0x1400342e50701c5001d90403c41d0302c42c14440700c2540c3c11068000010b03842110280c920030461150390100c0d11444001048a8050b940c0100b899501d1185010341e00304035609096060001c0d10880141c0c255901c0358102041c1c0e004406412040070300c003a00c420021555010810810300c3c42c40750301074000c00080314807c800758000d4000c100190192030019000351400000503030042c0185080712818164441008125503640f444108a00340d20700805101d072414810b604d00920f0030400d40c502a5041002462846d29076132300f04944c02810902442d00200c050145103d203400488042c0014112070b005006c0072003080080105082c0100030704001d010f250401400035807106244404410b41c0070b2000a00310518442c152160b01d403081d98180066a482408000c240e4540c00c000c1c0e041a10340c00901a20395a00c0c0d05a003616024050141c010091940c20005c40954200c0d483c081c5101c0506c0180c02000c581d041d0b40c1100d030a03040640424000014015010030800c0208018580a43c04000c00d90801 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 223287688 1250 223286438 223286477
    0x20304081c050c040909060e0a05030a03050105011809020d1e060e06030616051c02040906030203010b120d0e060d0603030306470c060108060109060b0708040b030c0d2307 75
    0x240100207039039071b45007500402c104080c0e0000000c00c0139841120781c4641e4600d030550380c9511810031440080d05100000130994002c09000f2307025141c1004680b115818001c80d20005c0d04400052101a5214940501c0a00d040e130f05140c0e030000109404134000d820701010164940c00a0601c07400780d84960308200c000d0325004290256081c052a1403561000504070f640c01c3c40d41081c1030205261f01c002400070302c1459940c0702e001140d101340e009000c184406c4003008108508403052018540200d240340c10351600c01d00d0400c05030f1000501d000e040160000c00c0b101150b299801c00c40c04640d0310082440000078441820548409103d1105132100d5081c1c15075503203540b16010301b441d1910484100d41e903456490260341400d00c94404850540d81c1d20741d07056507226001e11409900500c1e201000c078550751402c04540d031031038024001c18509482c0c0035002d10150f0005041c603002e8107043c0303c0c9a8120500340031b81e0110450640c004403840c4814565451f00020250804062040081d25242d48601a = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 223288938 1250 223287688 223287697
    0x10e06032b0503040201020a050f0303100801050402010e04051b0301031211160618050306091b01260c0f0309060103060f0b031c02100e0601031505090709150306020304081c050c 78
    0x1140750070b9031240c48510041c2e1078514000c0c0c004086000b001c000f6000c60b94008055840340000a903440c05070b903078030b6104071700300e45060b42c0103800689003c04600050509400058115200c807820040c291400c820f0100150000e8200300c1c1e0440c2484040e01c28035502c01e161141080c40080603006452070320000e54081402031140e1001d0140e2200310135001c6490b003d024004000c0641035070224030b001c9889988511810284640140e5003207000c0f2440d5105a030000d480b401070782e0300203000564028454844941c020716080300e0050800400d4004160180918026242100240b07119411842c280098940101d01c0c060140e2511107070201b19540000c015500d103c1d001842040803082107422401c1204d000e00b051121411f0051440001800044050490b070044110007842c80d458505001a5042910384c81c070300350b04c500070611201d00b481e84000415095040c0409110307540341c0d2560103030b07001258180e403810f0000c600070050807481d889098881900300303020082450081c001d2007041c0103 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 223290188 1250 223288938 223289023
    0xe010207060b061213035d050c0403020307170c0402180418120f080907060206010521070b09010810030816030203040305060c03090d09060509040b0409020405010e0603 74
    0x5e00b0750006150158004c0c1c1e410a56010000103000340c40440d0311003403242a000c01080e080290b00200c18401c0c40340040fa800d51040a900030780c800d1101100000c0c0c13501030b001e801074203c10031000005a40070080c1e580207041030100c00840003981400b030350401d611000603a000341e004100018400010080110710081700303c0b00000d8020040f4220b044003c0309203401400c80b94450490081590440614600000d166582c83c005079950303242c076a01d800c640c0c1304a42c0580c4c0401c0051080d85002c06030356100410002c903080302a03940342c1043c3c5c50505140d21042d540d100000d404030955074044000d907840b907001c0c42002c2d1180e18540d1070382054030881c00320800c5981001804420180b00f401158021500401110054107040302590309641c410340308009280701c0c03042c0b400d008901507109941103411030340395641401110407d11001d411003030140e0f58019603401504005a84a1260038041c1c013614844420030b00d0030f1030905151074080042c01c030b10340c00c9000032650a101d0020041003041c2 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 223291438 1250 223290188 223290211
    0xd020d08040321060f0501030207082a01090606261c03060503152d01120609060f0b10020703020f0402090f090a0f0516020d0c03050d0e010207060b0612 67
    0x26100e007803c03a4442c1d9082030842c020702014600350341c054078a400090980e41120180c041c00e580c0c03040194200d102d940e0000380320500c244080e507500f04038010400c003c9445004c500d20000141c0400302c0c2121000b1000300c4055a8809092203488580c500e0700ca60305a81260401e118801c0b0100c0a0340e40c0b0b00041c1c0030084071401808005894400d81100e4000e10004c0c0440340a2120211400304110007210300940308804068070000c02000d80403012080702c8020001c070b080f6402d02200d0b1030302046208040e581c403601d9026500000b81c00c0d10032034140c8103030740800041d400d80c060f041040280443c00c424046500c4014184050723070752070306809401d42040b9801660790a003131001c141054800210319911911020070460300180b142c0240902418040d8100615503c918009414400510103140141c0c40701d100051114040d510303601840d802810040d040010610380d150594090100c00c001594012806004020160150030b000c00000c680a50410303a0202c4030611940000b0041e0342c410 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 223292688 1250 223291438 223291441
    0x1020d050c03010335120604111e070f02100804050c010828090209010b0a030e0d09060f030902031b04050c160816172a031c1d150106020d020d08 64
    0x100460612450302c41c00120b040c94503041c6c5100352400006085400a000f641410340ea49900800300d401c94051401c40004801d14034071940c001c0c07801f1b40000508035141d00390804040d000d80c2d00c0e0383c100301005855507140c1d0818a400d20f085810a04480300d2a8188000c44007840400780070200140402500131803201c04a458000031800501444400650401405030020502004034002800001000d4806011256802410036680d000b44e888500008548a4040c804544640501401d2171243d00d80410541c1b2140c00281c00c01a201307a464509140704110300c00103003031a0140507804489920510306214529443d10b00002d8816801858644002054950072580c085081c45258003c802e08060b00060017200041e9032100b00002c175144036a02020841250984042040000307000185082030020498807412507003c03020112540d895001880603502c2513034403010041c030048001d009209024210108a107010780040701150000700c0800d004640010b03840f00001d00030301d440c6000d07 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 223293938 1250 223292688 223292753
    0x605090d0c0b13021302070c06180510080402040e07060201051506040e040b0c1902010519020c150603120f0a0912050604030f03020f0c07061236080c01020d050c030103 74
    0x511000e0318240c0c015610107c1c2010600c5000c100403015241d46484410314499030611040d0b05150394440c2c0c1da4070240c10b250726802c01d80f0440e0072a8002c2e01c080e1020814481041d14a4200307146a00820010303903488082101c030b0303454201c004501c4441030718801d1600c0d0400e26078000c103040c01403010302182c20a0011461600c5100101e551800110204400c1c0108940c0d00a003c0c00e03040e902071524034442c0c401d0039401c041c03034401c07a4800018600204100404141c004c684080700908503070740740c010500c0310140c410000f070040030015100c14581c0da40f469501e1010b0710600494008025864005142d080082d80000f04141c100390181850040300212a00c1100a0310509001c5c02e400300c8003203031500c1d94210010302c003401d0f81e08a03100d803007aa00341101094101c92008a04030680c0d10000746029000b80304130303000d0045da40701d00142600c6006545400d18a5800840c402c0300a80d800a24080c108802e4800c090b0003440c16440c0d00e146525544603400000c840e48080703103c00a403400750120 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 223295188 1250 223293938 223293949
    0x30103140a021003050103050c040e1c0201110c0102030103021813112407060f0c0909020f071b030c120206030708090c100c0b0108030a0504120c050d0605090d0c0b1302 74
    0x3407003540200700c640180000d01d03005003c1c140a110480c0c01d441741c15107860152806009101850380700100400111840540200b0002c480180c02030075556070b4262400844103503402086500030314000980c0d654910f20510100000e00200300050500c0c803010f101d0b120390003c43c451a040e401c820290fa00b003c154000809800010b0300c11002190508000003150080f0360141c00c456024040401444c40ba02000c40195000c01032514005001d0703c005000070a26540540400c1486551060500c00ca80d96400017080711640300d0f20007a46010300030410012043c102030040d1180304402440003c0e0b560114046000141900051088141c00101c2880c0200001e044152008192407a40780700d030740c0040c2038018a02816103d440c6000000305070301c4000021998049a19940c40785044c4c90100408100c15001008032002d15a60700d0005455071000807807403885001e1200000c960500c0c04503145000003034003e83d414090108001c0c00890b08001610f40e200016400011403140e403440081c5 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 223296438 1250 223295188 223295203
    0x5060f0904020a0c06140402030c0d030201060b0f090a06142b0504060c091205030403170c011b030605030604030e040507022103150306010305061f08030d0f050c040b03010314 77
    0x1074201d40301240590899902001d0445800c0c00b41004102c04800e280001030f01c0c55040b10084d40680c0042288982400c2c81d840081d11140030344000100b40307032200c001d000f4551282049814900c40400c00d043d90307207803030a9958001d07c40c80c02d2040c41c02041031004151401801d00340e03503400b05001428200c10140d044400350f01030f0546800c200528252921100074000710440d000001c107008404601603401c892150059500080214106841c5a9030404207519149006130790220910100703a807502d003402120513080c4000c00c0880461001d04004003252211303404140b09900c4a07043c031002c2500a03c541540b00703070990b00130541d5980c5071001d82c40d000003007c61411500c00680c4810801008201039030091040313080c000f083d04411420103544520a0001a000d50000000b1881c14480d81d036003aa065000c8441c4c07110150ba41d4201182541c0000340c0d11803989840b0440c1c40c050350f019108240d4098198108107003401d04203508110765020501004103a0751b440c56088000c3c0d5010440403 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 223297688 1250 223296438 223296457
    0x21f050a0b030f1005060f01020606040e031611090c181306230a050907050a030207030e0a0801050f0703060812030901110328090305070209060109090c0201060501020c031605060f 79
    0x8400c15050120600c1c0c4d19120114007100213854100030510500c0c0842c10340701b5400c4140d0007400d4944074903003000000e00700906464081d101c100684200305481c184580c901c64011810f13500c44400350014000e065200414800d900002044418100b40b500383c442d000041c0280d8040941c0f6244800c481c0040841e81c0082201d038045100c81400000d140c16070404588090ba5203600e02d50f501c4060041610007a00d607400400c000780000380310184240e024203500c0e8041e2901503c4468024042895019590018056039445c2c40070000d0004c5000c0005400440d1403034200314035450a10426161100d0000a104140001021554844094106030003000040e214540c2d21f042111a0b008040800800d00b440310114541382d1380303604a02e101e0740c15200d405880d958500340140e03080145104000345040d0500c440b2204c0495055840e03c602c200140aa0b00006003041c00c04d400079152a0360b1407d01c45c820303880114100356400000d4840000c070707602556010b442c2d6074020540104e500580200 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 223298938 1250 223297688 223297693
    0x141303090e09031b010902061e040e01090207030201050f040309090905100e0106030506070512010506030a0905010c0f0207080c1e0102120703180b0c0a03080903070605010f0f0501021f050a0b03 85
    0x2440280a00840100b061072101349501071a0090303841180c0c243c481580001c4e5001c81d081c452480c0caa204410300032520005c0c002c0341e40c0b5080d1241006901c0c12020f800032000d196001c80e1030000c03d43c09114554022002c806044014603256800800503001400341e9401c154903130020b071080140070058214400408142440740d50484840c0c0c5000700ad0381c2c8002e903018818a804240c200b4024402c48643d544007650b0005580e007003d05010b440d81c809480507824540c3c811741400071070820b219484c6142c805503100d140d41136032140700074507140543d04141405d400503000d801a564500b00440e00718800e0458401c121800000143d0400d00081040d4041e41d10000e00c03a03040580c000030f04c10030b5401656104010503101e1140d81c6a038050120008070030b40c01084500c0c0401d02810a19a208103070344112841c12030240c2d160000c0d01c0d000e03032015840950050050040840d01204100907000a200409014440600604101d080c511034128015070f2000800e48105007034101c00c0404901404 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 223300188 1250 223298938 223298941
    0x711010302090a1d1f0602060a09020a0302030313030506150306040b060406030803010602060108060a290415080f0706020f0a06051308040303110c01020304050a0e1305060705070b0a141303090e 85
    0x1582d0001d00c2c000c45e5400c2d265170f803280941e6002002c00d102d107015900070f40e00415060f0f07184c1115200030004000240d901007007000c00000140c1d0100010048030352030258003000300d032642ca4080e1900300c0151450720a0f08034031001c0d400130345000401961040d00540b00c40352544940c00410001c00a90f000038100480004c00400c0c41500003488504807801c1104480941c0d507080140d208543d5642d280c040c0d000c0710310f1211207450076410b4495240e03a00013400010180101d00d400740f000f000715070120340d090700700801441d00380348140b25003002003200b8000b0702401c2c0a282e03400d6444164500707000b0700c1c207070344c8501281e100a01041c02050503075001c084207035955100c0c1000703844880700740c1020810344a48100083c0d43e51010094a007103d40141020b4640e1b030410140b441512002007c59a4001c4455a48800708808225150041040c0c0e21941d580e500355041401c01000300901000d14242406607111316010012030103544181241e01c00511103000d40f0f0704032103a110580c07107003400803021710 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 223301438 1250 223300188 223300229
    0x406090816120e0d0b1f060c0201110606010e091312080105090610050a1209080409140705040b0d051302030a0c060210060326070b040c06080105060711010302090a 72
    0x242009802409100c0c0c102046224020840b80f14450b00c03211a00018007a804a000441c8049440c0d08021401c081c010a01c0280301c0f0410419255407005001414040d032003015560003064694050a006018107070302d1400c40c0000e0070300101007900b1809100d640c800140288003500500540da544034201c0c1058101000004046803006e0003550b201b80ca903040454028036006d0343c40c200305c0d4241e407521802e12915210513141500d1940c00025540c2e140c0803480e002030581d07402017015282070300c0d0000c0d410b80c2c1401d4281c80200010481e0050040c100024840345860005840c42c03514500c001113000c0d81c030b40d00c24507254800b07640000d406204020209040082d0108130400307641455007200c00100c024510101500c10303620018080100907a10f02d941401030b00c10840f07845118606103858600e9950780c840c0d500300111026580320100305014040c40c0c0d8003800303a0703004003400c9070100d0404405803601080c8828144105041c181d0014460204c2c1c1c8543e41032900404c5181c90b91480d04680e070 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 223302688 1250 223301438 223301467
    0x60726190e0312060108060d020a030c06030510030507050d0309051804050d03090b181c030b010e01050c030a031508100e0d02060f01030b04050325020109050306070203070b04060908 80
    0x100341900185081c412001c03100c107800025101c42d90000181c0d500c2d6500c4690056a00100145c0241c1d04840f80507010005601c8010210300258410425900c0182c903111005080320006001c91a90345c130001c6080000c40d1001590505451341201c01586000d41ca103002d9800d81c00c140d02031900031a21000d614500b40304603081c20f1146000300240d1703a10140c81c2404904507109013500500c3d010740761010074100482014a41700003080d903c2150310002c14030180350b00b01d20000c420400000c1d100c801c400102d50f071003d03c1c0f0b40c200e1400e0802600f40501c040303205489000d00101e0104140d650894020120300c0d803000c10004140038825104245804900034014000300d000244042c8100c80b900b124040c4005400d07403140400030020f607102d9007143c0e07480c801101c0242c001d590b80e2106001c0081c0d40c9411184d0051b87c40006165440d94a640c3c2c4000f400f54940769011030b2003600850100140c16401104407906140e000601d11119642c2e8078210707008210515000c1c11100d00820b0304d800348041d4 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 223303938 1250 223302688 223302721
    0x307052a01020919050607080f070b04080a020712020915010c0c090b03070b030402090403050d021201171011040b0c070305030d0b09010e01080c04020f0904091211030903060726 78
    0x54130000529080402091281e04003880360540002040106402080880001d000d41c6d450b001c4526107441c089841d45000c1c104155401c4e0784590000850a0646404103c5603000302640748211441603041e400140109100420741c0326580d40c5c0d0407405031140e1140b014030b039000341c1c01b5600d00d41d0760380c5920f1804014500313400303070034040e11600e13402059809180003528803940e4010b128034110340d9140d408a030160806440088034540130300c04070f80b44000c00e206081c0a031441034054107040c0e8240100d2450000c01a11000520b8601a500c180705a5550121400d4550003407c556035002ca950200c0c0c60a4071541c0054224000480c003110b0000d09a0030140c82050120741514680c1d0b218651602c090f1400c3c898880c0b550310010614840d8102900540050f4400c242100d09042412b004681501e40c26034041b607040c40000c8100e80c1c07003038110007028919100940114100304806010030340d51180605032034240450200800700090a5000c4210300703d16003c0a000d09003844268034019501 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 223305188 1250 223303938 223303957
    0xf1e07020d0912080a050a0512040f2a0501140c010e060f010807060c06050c0f120105041b090311040e031b010b1c020409021f02060603210307052a0102 67
    0x6100d2400a03c400d82e080d12241000d800c00c200c1841c000303040905648030307030000b8642000c0c008140084113020441c42000341c816401f40001e0307182c16440b440c20358421860702c1c2806c0c8001544d03140ba1501103041017400b41c03c1d2182030910380310282e03206042119a01581c0c100020139800d1084101c690403020441078065101c0a04807145662901e03001911042d1034094000001d89a18403100812800d0b0001c58104040c40c11031440c000380455440c0196002440c00d6400e003540710010001ca0030184140b142650848519402502d0314540c02800c18074240300151110040144e480300d5030780d50380e01543d040c50314081180d607550348005500340d8625503804404102e51030f0000b40314003818001549050700c20901980d10150843c0d40c2040000d0070b880800340d81008203601901040c41141c1803240c004030094004060710300c1c080c01003601d08220314480440c8240030b40c07100c02400c2c01e4041a01e40000440c14030685900642514040c0a8989550201581e14100c40303130f0000c87e010750040c40c5c0d462 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 223306438 1250 223305188 223305197
    0x9020f0d060e011d03030c0a1b050606010f05032202031203011e230103020c01090204020301180b0a050a030212031e071401110901030207060e06010b040e090111030f1e07020d 77
    0x1210101d01680d1310b00941030000681080001030700082d40c69004009030a5075007001030303141c1c5a200813440c1c4c0c0c900c1280221800d074441c0050101035a0051141000d0401d0b43c541940b5520304102c44902e224100c0c0b00744610350300e42d81828402c6580c14481c1300d40d1803442159164481d0780d550540088040c1c2451105010143c1c03680c08140400c185007100021b1841038015075411601100440003548100581c22043d541d40d03c0c01401603403580002c5000b0141f84195524400485030000704440f80ea490392817007083c40060400c10780c2c80d080000412030360125543c80d1908868068607055124407034281b012003020141c4645165121300c00f62001c0e50040310050a810495403080303003202c0c1030061048061005020016080d80310b5001400315521070003011842c0c00c4884e84191500400f80c2040c4004040410144100420556400d5101c80070130005c0c4803040d030410003003007a440b0180200c941c0210708000103112100c0c10000640070349411110030824641154029240c0172402d10440004 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 223307688 1250 223306438 223306451
    0x90702011104050909030d110903070519062303070507030806040902031c0908030d020903011b0c1502090907210c02060f1008060a020c0607050301030b0a09020f0d060e01 75
    0x11441442548081e00204100d64585410b00c0e0802c455800c00504054a610042040e480610410b000e202840131311f40100d40e0716203c00701e00f09810013400e030f00018064160003070300144900d00b0418641c1100c1450419405824100d4030611a00c20f101f41e50320031160000051007289075018005012644c042c0c9d40b044625113900003040107070741c0100c00c003940c550310040401502000c1d8800710b5046a8a60600030105942da0b1102411a000040c1142003958040b800031030504080c0613011844580074920801c2010f420009800580c40ca00c0140c010380821603603510400c0300b07504a038402c1c900140590070900c1c0c64400100440781c048202c0c202c1d20000e60202c641d405070b42c040c0081c1410700c0d802415607603039010801004140024824001c1501c400c0300080d641205104103400740e60409401350340c40c005c0800042c580100a00f130403040042c2080108041800e004c103641e0094416800401c10600c203000240454011030792440d0301c01203c1001204004541e0b1240e60f10510920007070000 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 223308938 1250 223307688 223307701
    0xa210615030f11030d03140f18250603050417030606090a090504140303060d0f0516030305030406110901080705090d050d210606050703320304031e020d032f0909 71
    0x4d41f03800d01305c5030340250142c40101d00003003070382d104581c0e001102c1d002c050400003800100d14600f4114041403030640003001d41c401c600340e407a100540090007103400c0602480c10f107559401003c10b0700c0c1c0c0803455680c0d00480031800e03a682c0c46d411642c0c565030041c00e4940864030b6030742040c020801920107d40008200c2c40c0c41795100340102c1038a00c6203400901880e80b100603034850480070a01c00c901221140691045101c0010740311440d00b010303500980e49c051f120300d0701c0d2500e4001c1b104001444004588140110801c9a903c41c10386a481100761416548450108012440124641d480140180240280b90b030000da03120407407091010034850100043e8900b000840101d503843d000d800c000802c200031040100e40180481060495050f002d042e00640303018900140c45100d008101c20808000b003804103243e4040540000850041c41420805580840c043e555011540d0340806040c0c60b0010700480c02c1c00181e01c0d14515070301310b44901340d0a500c410082e40c1540314000d075500c9044400e0100c0c55 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 223310188 1250 223308938 223308941
    0x150d110f0406030c14041d030c0d0c020a12081b0f0d0302040509040f05160b0a0f02150610090e010b0703170c070b060f060d05060a210615030f11030d03 67
    0x480e50048aa240120700f0803100c6102840b0120000d41c106d9140d4100d980c0102146d81c0340d1094050000203540c66001740404907040000a28404041100304040c2d500036070740300d44000c021108062035010500c0c036546400c942c90b004150410400c900d5800210500c120045010340c82030030b0402c19500003580b0840709a00b02e004a01501e90403e000400007800607001c2044580300e103002d00125043c2032003402c280c0710b181141e80c2148110890214040d2001078024100c900e08440500150000700c044a6810311030882c0105424850007601c2503180c8500c3c062290040600b0503904200650360710364482642650000c0c20071800603da914842c0d2a0519070350170603000714002820203281c205107442d480350960300540695849a640801c6a480c1c1d50350744020422a100c0036404075207490700104101140106a0207824101c07040e400203190030700341500361143d1503804400018044000c02e0500e0426031036400050420385c6c00703100001404088068003048800c100c00321243c2000a150450 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 223311438 1250 223310188 223310201
    0x9010b04032a0503070906030326040b10091103010513020901050403030f030f0603060e070509090c0105031506040807150507031202070201020a0206030a0209030f0c0105040608150d110f04 83
    0x1051001024810020940c52600b4203103044030207080701000503101c000190a001c69a4012003820b681c5180410030103030461440030601701d0302d10070401c8100102c0000d107945a4010001030050044c2000034000d030b04282800d001401000300104400c4801c00041c000643c001c1c0107240c419104004a85043c0d4446d001311580e81406a50b080e007450f2031a601680c001b07901c450075605250b110074043e44e107004c0900c219001980a09000300c0e002e080d8031000ca0500040d60403e43c011102da40401c00c0c0050001079199041c3c200b803801581d00e03070320703915130f501d200e5542c450469001c000018002200c0000090300c00542e89244010b016808040380103550620840c00002c000c035070798404403424040940c1c040d081c1940103005840e032100c0c0980c00505c490b803007180c07400c41040d40401c14480d207003010031881d00468214801010380b9000da0001a02500440c40303910100030442000815164080c00040720981c405010140076503900c0c50681070002c025168a03008041c0a10b5032003a9282901924 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 223312688 1250 223311438 223311443
    0x9030702040510080c1002030403210f020d050313080c1005161805040203251e091d040212030310062601030b06040207050f0601030203070f180b01030b03030d050609010b0403 77
    0x400702c4031703034610034041c0d41c41214640c0b100390700013800000081020030100c0d421611514600d41c0481082680140100c040918414115480042445440c070382140c2240c0e0042601d002419000b1807034035202d480f91007083d90068680c040e540c0d507052040d0780b50300464000c103094180007412442807041100e86001c000b824030b00a10102c9800c00490500b0750055811030b804040701d040d040b081d80706004141d0204a400b0000480c60403260003011107000400308400000d1900107040c0b0718240214010000000843c041061030001040440d943c003c483c0e1a0396a210003036980b03030702d4200452040480103201b0320020a070003184803407503413940400800094403c150303814030340e0f4290f8449070213005c4002d0805030002c1e801c00c160800316a0400100c900013450a006000325815803040c50708001e22a4010007403400343c03880901480300f00000002c02100051070004100c82c440c80101d0203000c5200300d0503014040010000b8050b81c46402c41417040c4401e40d00d07020710717036a2900d448200380300d20f00c0003 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 223313938 1250 223312688 223312693
    0x507170f01060525030e0112020c1b120a03091a030f0a0903090503150103060b01081b0304020102070902040902090108090f03160804030b090d080c160f020a030b0903070204051008 79
    0x40c003010b402800075110034484ca810f000288594000038113510882c00d013080c0c012800d18810b003040d644e40008080201d00220a080d410081c070454042e035034501110012089005c100b420810644070162544c0000d00b511041b00c2c0e03c0c01039030034003811412141c05a40c1038403080c48120884003200710102e078001e9a441c0c0162000740e5030001600c0050240107000c404104082c5000a860b5800f0050001c090300f4032814405994510b00d400021030f0b0800079118140200d56040100c8024044440141c0c0d10141180d15665a16880103d0a0265540003429081d1000c0380104404646a0290080310420303200da1610b5150000603503070300c0c1e07191502284280e1003008114400e61040c0c00d55142c0610500b6500c2c01c05860341d880183d00d110441d510780c80c4c1d91007507a200c000254070140302030b003040c989521585400d0600003c161f00d03c05007a00580102d840380003001c115101c041c00b00e8000c54000c03090b100d09091441956440b41d00146040c2d100c0c2c0d09140105186000004c200700884081100 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 223315188 1250 223313938 223313941
    0x10503011202030a05011e0e070803040303050f0909040609020108060103090206090607020d060507020c0306180d080c2a07060914010c020303070b0109151d0c0d020d020408010507170f 81
    0x1a000400c4a410482e050300850b13920000141d8240a46080740c40c0540c44000c403000c80000c18821100c1c030a12841e01a4011401000019004821a015030750545020355403252101c1c540b1046204000d0441d0708000844100010304c1040d13404082024801d80e6000c49070f4946900460a813070050704007940c4040c0400c617100305860100f000700f03180ba10240009100040503107800045807000c44510000d038100d4108001d40b40740034440b082e4800b42c80c840c1c0c079828ac00ca200c041503646404444d45814404803e0224405850311019650301c0c1e5140902500386032014540c1d01109600e0180710340c1c280c49010400304041e030041c080c5000381c40c9803000301408180080011034000d1030741d00040c1c1e05800100002800f054060700036a0107880e03076140100e010b10f250414020901500c1d80441211401b1184003e103d40d084042c1c0b64100a140f84e9250700c4820f00304000c002880303400d81d0500d0a9100180003d030403901900802d00c10041034450b00a406281001195504000c440907008019090f0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 223316438 1250 223315188 223315199
    0xf1006030e0705130504050610081c210903030605060406050d1a06070609050d050c0a0605040201050409060e0f0105120a1218030506480c150901140601050301 70
    0x62140445880800455800d2951500400c0d01301c4032080c2c940c0103003910f0300200400d000003041429080354884681d03c0200d841c00000300e4480303c4030090180d07420540b21200c06001d10644a56030020303901c0300818950074010176014010018508110046418044001040c0c80d03d20103a504884040d180d036490600c86800560051994680c1c1c20320340b1f08503513041071941e265400a042c0b45440f4030400200d862080c14640d01c0c120440c4112401c201040281f1000781c400450328910040c2d200001065580716840140c0b03031b038051500700119042ca045000201050f140100e0b41c02081014031400b60707a41c132070040c8511000c0d0070148042551000b02c2610010710315003000303503850782140b4218130b00722403a0005d4200510140c0c4240c40c00d038441e0050024440c3d0810710069054014146403511544440b102c3c100640c50100024220400c8503d400c0b030b1220b141d0403140001690401e0351041c4598000840400405468804040d0300c0d000002c1003c0d000c0e40300081c01514140c407000d00f1686010b = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 223317688 1250 223316438 223316441
    0x5070c020405041703040309090e0105070c0b070908060718140a1a090604090207031b110607051002070c0812070512030405030c0703060209150301120201030b030a120801030b0f100603 81
    0x43c10403200c61215024010504601c0e03c0694003440c030a0b921298a0751a08908909884154115000c00d03490142840400c5410410384d07521164054a403d0711a5169035064500c1c840c264481000d030302550003000b5010307510907201509441003a102c02d200381d803250346218440b09010001c9821a12420040c401c1b02c03a4003590003000c0c2514000c0034504055100820b05a41065004103420742d00400c0301010190402c00030040a5043d8100720003280442e2254402c51014581e06806403000140e14400c1c081c0622402802c64001e032410341d40d400c1c217454003100000051080f40101d0042d54152240c03060030100300d0340030980050080100310815186201164005041111a84403c0007290540041030040d80c000b9405904011389807882e08007446044150400074407402a002c00042c003a10f01c5910400104580a280024410b100c15001c00c1c03a101d87c1d104080e02c20f0803e040b004041540c8125540d0607680b0032040c80e1a580c8070101a081050380c2520446540a1140e500744080f81c071030b = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 223318938 1250 223317688 223317691
    0xc090423060f0a1d030d0c120203040c09020a0903060e0f1504121d0316060206100612051012051f0b010e0f041d010e07120201080414070302040612021305070c020405 73
    0x984da00750201484246491540c0e0101856045c060303103406411941c25040340c41ca0701c1c21208100250b1541c607040e40d48010071141e50284842a0f84e01003035032039180e0f116200b0308000d075601035030400021a44c001417a42e10040f0050f095100e01c0750038049000c4c108034101e02405107500ca42c1d0750011482c040f5081e10521070000e4640702124504c2c242c50480d6404110b1a05011161074600c14030703904085000713040c60f800502c40c0030306c80503103001041040e61010041d90721005a5200003040d446007101c5005030341c1c1d00d52007140510f1310707000c040090000100303110700180c286242c5244074004296070783c0162030b0090300881c04916003c602d4001030a200c101289198001040013601d038102c02145800c410f409806507015a43d2190184d90282d1308008420203081c1c81301e0041d0f0f07400080c2d0300003000c40380010802800581c00250451115400b080f9550265600400a12440380c03a50a600b84802c0b03585010f903c80e1001014000e942110b80c8036041c00740c840341d03403064a4a09245c0038000074180 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 223320188 1250 223318938 223318961
    0x4050d20030d200a02090703050a1407050406031d1204090501050f0901090e010f050907030b0604020309060112080c0706030b040f0c090b07021f0504062a030309050c090423060f0a 79
    0x604c10540e030050707441414031031080c1c1642e10001003d04211011404840300041045401a450814000302a4001041d00d08440d01440e000c240c8115110a100c10710352449440d05d0248a07200e0320400c5403004002078010765005040401040c1e980d0320400282c1d04901c110642c01140c0d100c0103010203c40703608040120f01503980003240403c40400403508a980c112174100752504541010710401903148061600031004480075800c50828041464440e80d0600c0340d403011200407544081048030308000d64407201e0030391064171303401965240090060426210414403c610349040400c02081c6482290403003016551004074540c101030032215180c3c032a420580e4010420b90304208a410300c148030542d840034603515980c4a03481c14401034490007212550000c4405511940c4501960440240794840e80614011407101c0041c1451420500e04040550304aa4403504100600c480c1c0100488220017584102c20f004410f01005a15090165002d8045450030008a040a00560410142d0710f2 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 223321438 1250 223320188 223320193
    0x503011811191715030c060306060306240d060f06020109050d0f09050a140411030103241103070305040203070603020903070b0c010b06040e15120a03080c04050d20030d20 75
    0xc40c0c030003c1d01000b0804a4001e80c0030102007444010b14101070194500e041070503581e080c190f00348900000c195020041090307010346a150036131f04008103000c403c00145104110001c2d9a003000c00ba0b00c4c4044d06503401303841a82000c0790380001d80c0c14414401c508403640c112011f007410ba00b46c500b003101d140c0141c602000410a2142000c1015604c0b2404c4000400d9610800c400d91141003040c0815070340f07200c181c00e02801043c80108080342c41c1003c1041c5d043e1403401c2400d5200364550107240103209010311800700c0f00c000700400c800c0c26015807040b402079000b01c04458031942d039600c045040e03109203140a80c02d0b41040c2c00400004180402420284661800100c0c010400708003107105504650700016440d03d244003400000d8030741071000c10414100359031244a0b8a41650007035554000e0300401420486071304001018106d2500584002d44001030a07a0040ca2a03800c0180e400f0501504883c64070043d600082c061340340001d0010010880b0f80c0314103842c0d4001d00d5111045440780901080c090 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 223322688 1250 223321438 223321457
    0x11d0a03081b0c06040203010c1e0509060d060306050f01081c0804050102042c0c0703050a05030601021c0507030215091f020405040501090e01150501020309040b0d050706050301181119 81
    0x1ea200007800c140c0c28108000e051340d2501d4010107081d01e45400c0702e42c040c030401062080c100161a5543c2000740e91504129a45100c0c5601140c6184140c13000001c01da854501d0100c10001d154001c40c6c01000c103001507a0590f6211240562102c803803c112004010324084a40403085c06041a168001e006600060a1540e10f03c400920700340c1904040009480380145460485d6081c000682c002c81100042e81c14151584d03406409441081803900600c040030000900b9603108000f070200c60711052810b0111203070740b0103001d4129000321078100c02601510321144240c41c04000407d1242c04d1480090100558403010840000e07a1074902141f0b1344d40070000441c803034840d400703031f5402018000c0f000195411030900043c01c40b0300c0c1c0024840407d4074400d04000d10380e400400d4901c403840442c0d001880640c22400142c02060907130380140240600c0400243c0d06802001942c12500300b0f440d11602501403880000c201c070358800030064a10001d01c101e07403c0940c002e8141503510118140002d04 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 223323938 1250 223322688 223322731
    0x10c1d0a051201050f070c020d022e0207060314060d170403141f0203100e090f010614030d0206092a0909010e010609021204110a05060708030405011d0a0308 69
    0x1089190904034002d40e4440d010301469044031840c00e5440314462418018450f80c070360005180000c6440e01074800c4517119031440c0d020140c2a81c100258002100300c000d444a0070502079110002442810b010929102d007581c8407080d0416a14401c0303000400c0e0601c1701c61ba540d1850048034081c002c12030700b0724060001100258035501600c04000711140248146401013514000070145c07a460707001924010700600c9000144901e084040c3c80c442985442e0580d10480301c5440c020f8000c400e5000707503080540008994070244800c0d54076103426415144114a440c0c026a42c4240030b03149104564402c8182d2451240100340d4242014403070102d41041110840000741d481c402918242c03840e9655101029610800344682c070014a0b003000d0540c02d0035583d241c070707a002003001400548001454400000715950704152003000d002e000304226240c0c022405c218100340c00c1124210f80d0780d803a1080340c100c80d0340c4d4060b01d0140ca40360000103001050003070360100c0760b03110701500c80b88174042c1c103044c2d9165 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 223325188 1250 223323938 223323949
    0x504020d090c080c09100e24150d05010b0403030f0f0e09010e09100c051b0a02030a1a090105060906040c0905030712051b010e09070207030807080417010c1d0a05 71
    0x300507010040c10b140c841a0100101c0c107502610310b4103203204000007002103207c04480641e1000c440070040c01e5682800525045031031603a032615500440e5510003180240301c11004d043d0f580721021041111361f0322958840b900d403146020140100e40301010b45c2449030320030503101e041000b29203000c0795103509200100300440702c280c010b5545005043c04110040608100f54000d412000e14140900d114215001c0d04c58490040c041110061800c440c1c4c20003003080000c80001c2da809070481e408110b25003000c5415058580c01c20501004010100c0c0070003405004490060100030021910b03911280d040000030f00000714042d050240c102c50009040da4144074031001002d031182e454940d03a400703242803400e0480c002c000c03109401c0309280100781664042c160200e00e05094070400c0e030f10f4481c900c1c00d070b01d0520ba0394001040e5000028101d000c000e00900608102c030103810030b040810034102c3c049401e907511101d005000645c0b101c0018181e00d0f8041d01d40e0700344000908000d441c40e031950089039 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 223326438 1250 223325188 223325213
    0x17030f1c050a020a030f0b0109060e2106071b15020304021309080306280302060c030c03180a0b0315040506180c3c1312030c060b010e03070504020d09 66
    0x200569010032074013062501402041510840c4d140208009036041e00060f051102c1d85c018581040b100e04d414001c2500c0389100b400300948580002e95000c0700e1103c0c4a40e0701c6004540383c0b80003072a82041e0f1004245080c4503c8400c81e409184c1d9140412002e00400094200400599103c1040318111061256038401c03056214081c4000556914201c424040d154103030032684001b07401c0b43e403840c03600305070f2607100e86066031340c1101c15541d2a0924070502d40382d80588130b1034400c0c41c04000750b88191941031031083c1d501e010042d2402c0c0941d03541c4081030344180c0400c5801d080034003181c104c0c0f80c005141592180398092f2000700f8065504501101c40899034004a50113420603000140103010422804001510b99420030b40d04004485814801101d060310000c04003481070b00803a40f50004d501ea041c40d1001f074080c1e044003089030f49403800d0040c8182d64641c1c0c02d4444900d403003c016003e502c91100c1c1862a500a40200b80351440e02042c8002540701c24207550080b6038070080000080c0d000c881d0312 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 223327688 1250 223326438 223326451
    0xc0507140c010e0a03021305271606050a0c063308010b0a0803161a04050105100b1905091809030a0207470a0306060917030f1c05 57
    0x105651411040094010b80c039030f80721148503039494074081005941d040c139901c9503c02003406c040f60a48030120701484008100b20000004001400d0540400c5000a1810807200d5400b0080020703960b030ba0f00645031480382095070f50000b440c40c600c0a0203d012034101900c008440c40c0d218041c8042620508004800e25446941054106034100500c42d0240103000310710300200d400d12403591600c01c0040c0c3e03900c200c403c02541c011120724583c0034050050039400c441c0f520940b0382112890305281481c02080111008980c4070441603010406515a000b81e0308545604150407a1800110f03030142c2d946c0d00076103d000c0c0d016200900792406e071b10b10b2401c094003544031000110b486658410001c0d007403021a40013a21030501a2424090300c00107583c0403c0101405c0c40660381740e0400c0e440c215242c8804808110824000260300d800040e89540320000f10b40300c0c1d17550500348a8031200c0a031403100c028040c00701103078014018014000c140074010401100460040c001880340c000000007076a03011100d1 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 223328938 1250 223327688 223327693
    0x31b0406030f0e010e0d1b06020f030f0708040302071e050406141008070801031707060c08070906080603030a0e0111011e0b0414010b09120f0d090e010e07030c050714 73
    0x14401c218070076000e18001039109100030b12080c5650400c41c2c2e560a0180c1040c1c0030465000c0c55241500c0100c00d140c1031f0160010400d545c2d8504100c1c9020569000795507040780003210300c0c00564003510445500c2e00483d4182e001d000c03814500705046148480b040300c00201e5079011400000c8070381c1c072071051900600c0115060014100004100803901b0354840b2081e00b4442142d00708101c15034071081043c1560b80c003031810600b80c828210b040ca00c500440000800151800d883d000c6c0d02c80e000018a440341c501c9075130352507407983c07540011141303403400f541c0854141d0f006000e040e46080c05040c007590300803018940f003100d40b4040402c0c1d45c00d40d0013407600c140074282944c0704a50800e0943c05210001030701070303800780000401d807034540d44e0b4404144144075880001207880c0649903582ea001e03007070000d1403408031814135001c404102e80340d46d407a052280100f8201d800000c1c001c041d03141c909040720039002030694156103400c0b050300a04031101072401000020000d0900050f10780640c0340110710f60200 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 223330188 1250 223328938 223328951
    0x6080a050618030f030601120f0504030908280b180604060204060f081905060f0d2d030804030339110313031b0e091015030b060105031b040603 63
    0x420000426140d0b50820031900100003186414001c0c1046a401403420700c0d05250f140c603054219401000c03060f42020800b8100000c0c0005c0c50b5012090a06403860041606c003020303400b00607582a5600200400d00e5840440180d00114444140785540411a040c0c2c0345500c01041070510b0a1480442e400c07100d5680c0814140300d40c50f0f01047e8140284294104812541403402484030702a800542890041e91240002070154490500385071102001070000610713400385180c2800d294000000c41c0b801c10601949244990700640380c2c103d40d03103070161981d00301c2d03072200c5e103044011708000d00310000400910043c00c00d515101c40050048030344144008141901c0d484002080c0b1101da8240351000ea0044c0006061000701200781c400301c903449140040089000e00d180044804950700583c01c3c080403100300404541e0128070030110ba8a1120200141d017200040c2c0744080d4018080505070001c01ea0005005501680085402040d009103201c507004004100600fa030f03100d50070903400251201c8 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 223331438 1250 223330188 223330201
    0x602071b03210309020a05040905120f040303030e060105150304050a05030f0301091505011d030c1002010203160314060d140f0c1c05061f030605011d25030f06080a0506 74
    0x40010015a042d860300b4080c1c404d560300056081c0da0310340030f85071140b561041007108004003017042855500306d0700111030315650001070600042c3c20030301c0240d01003410860328a1499034041603090580303500400141209455a41c030f11940c0e000200200c031148200c1c10703982c011410400c00b13030942c8141043c007560ba960508080c00159a140348440701440c4400006002c66a00400c0c0c400d10794441c82016400110441c0010b841d1841f043c410541010803020b82400b015419002188100783d88800c1d01003103a045641181120240f0f103c005d13444c801103010520074900441c2c0c903d20640505078040103025400c9a140c10020160302c400301550100d0812a000e007032002076603150110800c0965156200c2d512401e485d40c03801803045892000391040c1526040480e5004006503070495402c100c2c03580c4842540c1942620b1300208103500009500048a0b402038016200d1804c0400d41600050001d040040c1c0c0030740328980d250900c6039210800454441c1080040c51046805070b40102514201306 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 223332688 1250 223331438 223331483
    0x9091503020f090415050a0612150b0d0804140a030618140a0309050d0c1a09041b02030711040e120d1407020d050c070f12050d02010b0d0602071b03 65
    0x404903e014a1041080102007841c85058103040644120040740c01e940e8100380c00300800c001c0d08014150300e0619041418000c044030a03901d003601101d01042940d01150030000b0010202800400c04101040b080c000c3c40d00a0314055540b10b80a4452440360f0780302d80d01c08064ac1c0071a410340c203800d105021103c0900030500c903c00f80395a54071006d400e8207011a1001485170309640942402500300c400140208110125483e004060030114248480b602240040c4180c3c00060100d1086007001004030800742c0450b010001403090381c00440c60f1006a950b81c80268a140c044d25600c140c1e0340c5243c22080a0621012540c40203110b500f580d20300094480381d00f11005e4015001e200448003003001030f49500001c4842c0c4420181c2001d40e12010301142d81860720248ae04908144503031214005030301745542c0380c604c030028802d5060300c101003f030304812400c9903503107240158403600c1e45450002007165580204815401002060f0807034500e40105400001250700440b0020f06030458984801c030390 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 223333938 1250 223332688 223332709
    0x6020d061509211e0813141512070201150906051309020d020105030408090612090f0a110f030a1a041a0708060111011b0806040e0f030a0507030909150302 68
    0xc0418a643d50340704400624040121500002d02c0c000043c20100c052800c040c0948181e203034418081507407000a103d415103014818410b4a089882150396039050b440c1011081c01404602c2e4180b0f814685150440044d841001e014a015556107000b0404502c1001009030054414402c1c085405480d00c0c05000540d42d4543c070014066181c0f400020040c0c0e5a20700c43c940083e0246406070b10794485080641440c40340b400c5080d84942c00041207a9654a113403542841000ca00080d551184107030080b10381c4840d02e12030010304e00c0142d403d810241c0c2c50042500c0448800103002c44000c20016507e87d070074000c024414903240c0498008000402c035800e51940311600303000e01450614248640040c0c1401c2001e06120f0510509012008805400354002207010b600d0411001c40f8030b0507540b001d01841015140e5a0090741020800c610081000490800100c1650000c600d07120080004584030b402c400300813802c10000342c2d4005141c4142d409900070302440c030125840329070719510400030000030 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 223335188 1250 223333938 223333949
    0x320103051c031820010c150c2706030e2b02070803070506090106050102030a0f0c060905060a060510020d090314011103010b032202010e210109061a01140301060c06020d061509 77
    0x120004800c0010600e100741c01c040b0030415000f042310440014140c5a803480c50350485c85400403802007154038031100314204101c400c181c4042182c2c00402520980f00c10003d140580242680f5020000c540403008483e07c00c800300d0b20542d00e0311519002e00c14199030141130140c0e0786501100034015450402c1c811a00240400d0005502d0000c0e10003016200307602c82c1d503440060100d045002003e009c6250400c01c00c00c0e81c0f1a007a20614504a00350360000c1c030803070055500903001c490040300e1003070000070016061140354440c170206514650340c8541016403030450124654907011030345440d5234034101a5001c0c3c00010300c00350300d03440c1c81d08441d007080143d05504500395010900e0240581d80204415050760b60940300214214007002e103c07405800000103440300344d031a10620300240465544002d40c2c091008074400030502190004440c1501c0b0740701006401d000400c010444140035010300c1d040c140c0704000150402260100003003c46290340e004401a00120220902042c0d010b00342d40d02a10 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 223336438 1250 223335188 223335197
    0x412110f0a0806011e031a07080c0408070b0306030a140703151e0b0a170a0c1208030106080a0905151911090f0102030904320103051c03182001 63
    0x780741c4592a950b442d818400c5d0806048504c4201340105403840c2200051a00203071078240c590340c400c0000400040499602c0000740302640071518240950084508840004e8000c00c8000d05140c0c00301c0c030980c005007415034140b052055102c00605001c04c85038031031040c040903100300340ca542043d42c01900d0210300c02c544c0c00d242c034030f150701c40c4803042c010420707190b01c999000203403a5140d81c00b1600110191704070b50b2803441603103a6016040000038050305014440c44d440031503269108290320000c0c0d194040201200420310042c40007500c24a050f0340d104034101000300d030410040d120103041c01d015403c4881c0301404038041007901c42c002d00780e200c90318164400802c040354a0300e00c1c00500e800b602c1d00f000c0c41289244410100c5a2080080d03031192140240704120000601c042c15080454000c0d0b00d064500342201d1007050300e0326180845040b207801038044c10342405007400d007001070850b07210000181551a034807020b140000c8040b0101052044e480441e1131803c017103403010000c0d145040c03141040b = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 223337688 1250 223336438 223336459
    0x21903090804170a0b0c220e04030807050f03100501030507020a0b011701090501050c04050f1f03022107020a030e0d0c0b07030201110c072111100201020412110f 71
    0x901c800c41240c00b140d080b602844a0b12500200d8030741411200c0c840030700280e01601c02d1042c0f10042c50000c114418504110000300d502070015816031107024400d40204610440014012034000c00200d41d10801519040e0b180c281961810452504140d071420f220a0505409000c0c65806110313064000d000307400200b4021503255688014900c05000d92003203c1d218501c0050003100941140c0c81ca60b03404030081c012441c1c00c1c03d8403c4d060704644982c510541101909664509100e0103c070000b141c07060480000440c000416000780d80661007150100101d01c0daa0111103010040f5a40100403a6011300b6221055090003000d505006c40d40782d01ca488128003140c0010300d01040901115040b029158403010349013010307801040910903030940c0c4580007452101441d0046a4942a580989400d01c0390481000342e0351300c41e43c62840010318002d0b065544080c00c4c600034040585401040c4005441c054448007490121005541c0481d07030812b044d500524503203003c40b0004d003500e034103a40e520b017076 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 223338938 1250 223337688 223337693
    0x8010e091e0c0604030f0c0504020705030313030e12030702120d12050408070c030f050d0302090603060616290105100c0206070303090c06090314010e0c130f0f02190309 74
    0x11040705504034510715a40310000450700906100042d81800d0007040e25460700d81d02c0c109203200c20f4010104585d4110035680c0481c0301d01d0f0610035a111543c22000079401c5599502505104001c0c8060030b40c140003004007501215034030b841440f00c5807592031002c1c54032000d541c4144040075418504d541c0d480d8102103118588140c2c1316000380d01101040383c010403140c0300e50034003645c0d51042c800090301044603103902000380b25800c141921940d204004036101519500403c40490041303810559001d082080840c1152070907401a1042c118628540506040280c0c8ca00c00030380b0202c9082492000380c0c09581403c0781c00008168010107042c1e6101c07800940314000104081b1b00e13800024450000880c6a00c28184203034130880d01d00b540001c080e602c107511600058208485884101d40c04408520300703441041040c0200f210250b4400300030401c1d0b0913031004100f00148100b0b59900700550b2000c202201c00d026015500c2103442100e001a90703a20f204c84143e0003c001c5803c454103050604008500 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 223340188 1250 223338938 223338943
    0xa0f030f0e180a020a030b03010c02011e0204080a0b2d0106180509010b1c05010b03060a090b03060a0e121801110a150504021206070e04050106090602150c040b040605090108010e09 79
    0x5100844080042c1c5d2070400103c05d800070100a43d60740d405620307140d001c40c41913405600410766907428100e180c038481741203210001030388101c0c0035501c003980104600c1c40000e000382c001e590b00003a55482c04c10054107541010380d840000c0140c071085a45002c8010040b07940c1200c901c080318207030100c004907031901f403201042c42208180b0800311391880000e1840359142640c01d80345810108801d003031143e0350750347c0c00b050b4540e0030581d04c003071154407680c4000030b089201b84039080110801502904a80d0751701105907000b4030f4104899032090184040d91000030385001e000b0300b8940980e1300703010548000fa030b0005141c842101c1101c0c0b015808850600003142510748020340003210400c0100f015a10303880890119a150204c03100d04d441880c0900c0110b42d008070a648070100241c3c1d0070041e0381c0e610071007190011154419240540c10500ca03c6403a1007508502c9980030301110780c090304e000c4e40e03094001066402a802000060408110b0003c2c035a48405100d00600c000c2c0019480d6050601243d074 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 223341438 1250 223340188 223340191
    0xc050d2f0424140706050417070203060f09030d1d0f06010506071119030b09060601020318060c07080303010e010807050a0b190e060c0109210f08090a0f030f0e18 71
    0x82c52070800d21249610407a0642500398000d40c800c2d46440080c60018040c21040d1012102c8405003441c00700007146110541300045d400500515144d141d001d00d240002c08041d2900150340070411040c244c040103070151040d101c4a040781000195a294111800c1c8031098044041e180c020301f004100c5035503242c0a840d906032300700c20424010b2005170001044003014000c00000c07844084000000c2c0420054103078410140201502d42c9691060012078586c484e040d0121039214a5444500a60400401501e04071305914100d400c500e032500380851458000340d0051000d460b240005011502c0c1c240418001041c043c2c4040c0d01e02800d00700002d0080c051900c1003400c1850070800d52040d24842d45000318180c0703000c2c3c4003c1d075880c034070b0079064044c00c046101540c002c0074181820341c050035000700d0a00c0c12131065480012410f030726003007261092400f8100c034526206440740140840d0840410a00481c8641c4443e64030340b58026028180d10755500e5524030801c4c0844440080f00341d0210000d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 223342688 1250 223341438 223341479
    0xf080a061b08010b030c2101090c080402011b060b0a1203020d020705030606060a030b1003020d2904020a090308030718140d030e0a08030d091a0c040302040c050d2f04 73
    0x40e41c0306d54420030b20f98614001c4a601500011118500c01d1031020304000c614181d94007034000740103604001400780c1e55058241c400034005255050b148000c40d040f111254120341c0b044902081441c6c03034000041046141d82c0051302c0c0400104120810140c04121015000d0100e0020380100744c680302c000303a181c00b00108091f00640e030025030389800d80e100360301103250600001d02404e01c000010704010002d4200e2101e0042c2103251009031001101d441022412185194005090000d0741e481400301030b402400341901480a20000813000404103030186101d25603960b5482c510100d0b480d00035076950b1b05940f01120360228404425001d03100d07551820030745a09402c2406107200310801058002c05164032001443c0000b04900c42280c0c41070700203401c1c041c007580740c2c84048010110303c15484c03001a6005140000c04100c2080141859002403900400d0b50914509004d110480074050f075840e410301f50f80c0141170005482c0c0d903845c051240340d065528404540d0806041002c0c48007440e00c3c0039040c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 223343938 1250 223342688 223342709
    0x90c0105031305010518010f02090a0b0c0a1208040b060a0e0402041d0f100e0f0d0c05070f0905070212090a0603050c0d02210105180402060703090f080a061b0801 71
    0x1541500300c0040c040c280703640c0b000081005207400c6c9000090101c14a25080c000c0d402d01040e10304005140c021f440039041d000700445a058504400415560b0141c0004e0f074503070081c0c160360000300f810040854041034040c0c540181d2450945402c0b145004000c1c240c0707110f11502c081c14060040100800c560260741650300051400307481c800b08002c4060380d23156542e0ba100c4d9120440c441c03800851120602c24420005010a43c404c980807901c0e5110040c000480f5803001d0700042c5031902c202040100740e8090026106950348405004004d006103411024030303d81c03200e050040c030642c1000040ca203146504021820503140100080503174a00348102802c060b203034030108820341c014000f2108182c6020034115610300210403807118081065440110740a444400000c0b00e04002e40748540c40c25141d0704041c035640c1c40ba404c0203c950050318080e010803d1800001ca50b91040103100000790803042c0080000c40c007185480d00c1515103580ca8810580c801c1012400a1030300485554191021f40d1203 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 223345188 1250 223343938 223343941
    0xf09060e04140c04110c0c0f06070209040c1a0405180426040e070c0203070605130605030a02090a03050f010b0d0206070605040201050c03160c080d0e101205090709060806090c010503 80
    0x2d01d4a80005812420340c0149044c441c42c95003e0101c00501c0c1a0700340405031105170621004010008041c0ca0b299030f0008410003000005103007601c021a0701a2060030320a007010780343c004d0104e14002e440c03401140c91074005800d001911b03084501d1186900d41c0484600030781340c03e65900b0417403880c1103510440c0520a41842c0f010121242c195005025400d05100c060314180c103008085402240d0b0036400707400b40502c046503d510690407510460884500c0b4a0725503c3c0202c02c803280d600040444480300d9090102000030303507520280c24000c500400040c40e50304035402c0f00908484030042c2c141c0c8205d540c103003540c00507107500c01030306c20450700880005159580c030700050722244203c050200d5103000000d500c0100e19403041846e0307146d81c020300c42055490749800d5560783d00e00035100140c2c0460200020340d4071503d8a80c02c00410b003d0545010600340a9000f103090658030243d9045c40c480c0c0140c001400001814401c070ba0041200d20700400641c1400ca54040d10350000ca003406042080000 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 223346438 1250 223345188 223345223
    0x21e01152306030c04030c0b120609060103180b09010e07060921080f270904060504080c1f0e070315110f0a020a020429060c01140108070f09060e04 65
    0x190700c20040400508001c0e640d15100010100c0c036401800126400082094045031410320f0714281d884440d4031660b40c0d040c0c1e0300d40804005106000400031810103443d5507503051075802e00310824030424414114520325042c008255425510b441c403000e409507100c150100040c43d4402c288404440c260301081ca01040c3c58a280d40840d00c410401402d0380000040008607440044c00409219038030400008541201e240400c10020501401982c0302c042c1501107404141d269000b00e802c6403290052a02e000c08115006040074110b070600d581000d12401210000d002900903000a501c0020141500ea400d50b070705c1000062649429280d01540c810404205046060464050540c100750481e101d000d803260081d556500050101d00807070810601c40c030440030031815805e5200c800030b2580d035030214440074845a030700002c04902156417034440402a1040858034240640300e5440501a40e5041180b00a40441c081d44000105890004c00b08104c40d5040c580c1da4001d94030011114140b80d0743c4 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 223347688 1250 223346438 223346489
    0x10c03080a021b0706080f070909020a020f0d02030405030c030705010c030f090306090c061b0b0112150f0606180305030f090303090405010605040512030f0433021e0115 74
    0x314515000e141c0400e6012200c1a0008120080710b40d21b6442e039080e0742d56014000924101a680c08020425559080c0704a6209401505091000d40b0444041c211034030f00b80c40c0b4103c90040b1600142c0c0000a00f8045401d0074000788034074003420390080c0200d40c900800244850240007025042100e02c010104580e031250a002e801103030010020300550031682050300400684d48101c1006ca10f68503424041c03520100c01034a9203a42004080c6000d0b0f117059034401c14101c40010403510707845a003c03420415042807003480d0b02c840c603038600050050300700000546403281d41c4402c2d40626042c100100009500002240c0d01c0c1042002015112009540400c4c95805100480d5134014103210002c0390b000e40c414040c0045600446280f000c00c005020032940b01e11507221800001d030b40400041c800c1c0089108029a55260b03415850307109845280340312a03800e96001070000503000306007904a140e08600c0d10108110f08400200145964582c1c03102144040d48545014448404224403170003548 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 223348938 1250 223347688 223347697
    0x40512090a0b030901050a0605010c1101050901020a0b10090606080903190c0b07030f0f06030b01150c0b010306090611090913030908100605040609050c0d0b030a02040c0e090a0506010c03080a02 85
    0x61200c02c0f501ca0400340980d40c0a01022180000510300e00140021650b11480e85440c6641d00842a080c0d002140750046500c0e501c041c110605500c1001c246000103000144501e201ba04d5082c1140d0240c2e040440120a0b1140c503480138040200c1041031003494000031045480360701d040e50400d07443c41100c2c9000d44004600f00c5021340240700d41c10420078000e4150b0080340c16109261401c00806480ca402d03003003103808502015001804050040c460f5420750700c4030015400b042e013054039100e4003a503141239054500342c008941543d00d402054003004514001d0000007224040b04a080522a0011603440c600c0100791000c1085020340c054203050240300468040c220140907240c1c0300089040d00d801500080c420240201c4c0b4008000903502421301c215400f8421030703480f191070103400031140342c040c00c040d18540750f00d0b012b2000c00400599540c03044010210090704c4400781d0012480c1000601c01c0700a02a966042c101002c02070642c1c2d000390410a00d6506042440003a290142d000d4024003c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 223350188 1250 223348938 223348949
    0x180406031a0f0702070f030b0901020c0f070e1315050a0e010e0c090f040c121109010e07120504031215031403072003060610031b050d060905040512090a 67
    0x403422141076500441c0100d882c03180e04070520001d80c54840c004103ea603140750340700c0c9030713072004d6520700500015451802c00d5400075401c1d0700240c2401d088100366410940c00154120560b40510320401189000b00c404641c40036011507050103025a50304c030200004036040209040303644c0c64000425021b01076102d182c44160b024000c00c55440000d00c01581c1c1d0001d140c0c0507201e05032120024074100c4e00074441d9489603030301c4000c0d50041440d004c500c44d00c441b81800c046903c0303540c1122204407a00d8100700035000344880002d40007241440c03c0c02810f0403070800c0e6503500c814100300030800070941003014091080001c0c44c0018404d0325203091220001204e40008041c48c1a000044a00040c000007a0402d14050f080090019600b0080700d0320758951050308540503040180003501d00c2c90818030b240480441da080101ea100c5148010220781c0d003083c0c01d040301150000c100c0d040c039140340384180300c040c1030840000c2205003000d403280c135514642001e540000c4200000c0a407119115205080300500 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 223351438 1250 223350188 223350203
    0x3091c0e0604050d290601030e010207020a0e060a120809210a080f09090f01030605060303161101090b0a030f0617030702040b060c07081507090b030403030e070b130509070201020a0518040603 84
    0x517022001121440140d8138140004d08020504400c0c0e881032080381e01c0c0c02c2e80142012805841c0c00090484044d00400f2a0b078050340441c00050b554614014981d001407050100680c0c60482004128018a4000b910018002005203102d1101c1002441210a91708001080d8540c0100c00e00c042e20b034466980041e4000c580c4a0a000d003c2001b2450300c1e058a100e000184240e0752450185956030080080005800c0001c80a60707000c109201c2e90080001c00c1072400802150f151250110107600c8100b00314002561400100f49005942c82000c000d00119480300b00159012902c0582d030b4003948030302074440d0f071b56108031103d25a601002ca4507054204425216a40d0340c5c0c408558807410340da100300f2180d80d14040018162846900305c102502c40e8510203a045032039580742100208404410410300c0e00c01c1900c041000d6945a02a1200030044109aa000e90a0805120304168042e11a809680c014032030b0020191300070040d1028040f0307122814054402e8040010040c2c07900d0340c405042d02 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 223352688 1250 223351438 223351493
    0x10090c05040e070509030318031207120f050f0a0e040b09010b070303051f06030b0f041805010f050c03180712142b2303091c0e0604050d 60
    0x2a030440050012110044015600380c1e55000060b60644101c0c010160f1581041145800188031103500b207644100c090112403040d5001000d14100e41e000b004159101c08502c0001124268803580495045000d032070400c0c00c3c68a4200c075852a8003c084004e41401101704404110303403902d074400e44005000a08041e01c95035181410011644826001e800190825000490000300303680108106081e10081c16422460018128001d191940a07158040c400510002c0b00d03540d1750046d402d031a08080f6420400103000e10704142111000d410345401c072801c2c1400c014000d107818041d0f03540b0810503200000a001d041100303a042c010300c0c0e00071705040448802031000784481d800c61440e0300f0140c082199070360b211724180780440440c0710a111102200001c00b07011010320601d9a44203515110201d00185401c841e44040250000c5400324030350350010203c0100711b209010a9070018629007030020420f144030001c15003e1240d8040c00b401540c44103a0b55041100705c9229034507804d07104400500740c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 223353938 1250 223352688 223352711
    0x32409040b011505040303170c0d0e013603080601021e0610060c020d0311010e1203072303040308071e1808070608040f0201030b09130507060f020d081009 68
    0x4600081c040c903150f01210124610015008504407410340350076442d0500078910b44d070290003104400402d194000c401c28450f207c40100c003400b8124882da50300c0004030315042c1c2c1001459440c43c209411b4880b0114014008480e000a0410215900e41510701031138a1b40e0f4400c0140d160280c01c40208040d8003165002034040e01004c1451406550300c2081c4507422a40c91504444d4102c0c9050041d600034500440800024000c0000c2d0b0004802c2100228a0b152088941810050740d00d03140c3c54203803000020062043e60020407034130042c100c00490081c855054508280d04c2c00010002405e00c00c6810124407a24002e004944401e01c543d0114241c1081941d4001c001c180583c03113039894440380c00800b00d0080c80c0880c042003529043d5032210010f9880344c0700d440c2908100e0b8800ea0505a0711100002c00b81c4034045881e21565800320181a090708500c1e00c2850700e10036500540801140c0c0808115582c0e0210b0f6010322183d0610340b40300d65460f060202c4410f100c06503c82481185848000d215 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 223355188 1250 223353938 223353953
    0x1101081e0a0b0303070f12080601110613170d150b1306030228111209030a0609020d1b0f2403020c1f0e0705040903020c010c24050a050a1103240904 65
    0x7c20b036031310b0344e0301041902c641c0019138104003503d541c1c00f10742d003003e400542491940d02c28102c3c1c107801483c0e800c10b2a000000504080d5000d5501444450344030800a105541728038450300081081685c12071900700c000c0508142c12281d800f40e01c08040c0c00040c80b0308808000c0322070703d0411041100c4008000340750500034002d0155003100c62294001d481c0850715039603080060700e00c8074202030054402c09680f581d90714014112003c00300c2e4811408901d000224031004600300190940b030070920280d5040c800450f10000c0e5030741c059424000c3e09080040c04210a0078140c8841c4464200941c4401d000c00080c0d0034840070640c8000344221a000d0020403030031640103111316190300d0040e1031801e5161018841968100c540140150b800100c4500d03c5510410380824041d001d50b03058480030240c2c0180c00d000041e03043d000c2c01c010751036030180150740e0b0141c843c164100f52400b40800141c00801c02c0003802c0e00008000c00070740702c0010a20307208003400d00006a501308004141c0d001c00d00c2c0c01d10f031070796 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 223356438 1250 223355188 223355213
    0xb07110618090f271c03020408010e0f0f0d020a03080a020c0a08090103140606220b0f040303030b0d020109090f02040b070503222709020303071101081e0a0b0303070f 73
    0x1801165003c003038107010b8080c900d4220301074801c1c4050284514005c0700400b030100c030300701c280b410150708010010b10174a0038404c804015262001601ca5846042c943da0b16210f00450b0742c54560b000790041d0941160002404910356505041941582c0c1d40c0a100800a004140b04000380703000e03001c0020200f1982c8070003002d0314042620200700581b42401b0820074220b048a0340b50708002e00704801041c20014180c0841901c190261201e00242c44103100d50240d008000501d43c00480441e040c802c0580500400c0301411b000e0300c41d0403980350903400084c14500944200c0b101c0c41e030346280440042095070121806002e80b00c0d4240c0c1e90348440c0c46e14a07500d5111850301c00c2814845450b004e90034441841100845628050030100b410307201d1401ea116600045003000f8080d0350f180c0c203a005803402e1010f0500b4a00403008400d55a04100024055000003170402c059400c40402500c0202105000c4d950000c08a100009100c4442d00200380ba6104405004c1d145c03440a5440704c3c2000780d00301c01034 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 223357688 1250 223356438 223356451
    0x80a050a0618051b0d1202101109012003130e010305060702070305100203130210080405010f05160809010f0615020f010c0c020904170a02010b0a0b07110618090f 71
    0x810101a203030810200e051030a0300014078a401a00c20807102408400403010031540091211091820954681440502c1d00f0902009600441e030005598440361080b82c02c030222706003c0700c1c6000070040000300006041a00032082c02c0510024940c05082041034488640c41c5080705405642c46e182e5202c60f40c8030901c021506482018006141c8a101003130300c0c001c4a500c000207080480c0c5940000000c1d4000800c0c1c4c01000703c40c25889805a1f642105803821203075141c80d104a5030a00742482400e4407503881155000500f084144900b100b03d030203448420441c45e2500501070344071201164090318080c02c0058100d800c10780c01240384844a2102c03060038000e902201d1a40c0044122a800c0c6c5051098800105984200344005030400c0b0000a0380640b142c290005c40a4040b80c00ca00036420141e000340046c0c0d51502c40100c241808d00118000d012100c8080b42080555610030902085202c000f90191002003112104072681c00b0201c01c1040e0010040c3c02285000109283c0c010421a003c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 223358938 1250 223357688 223357691
    0x5090109140115030f061401060e09070206100909150207030509030d0e01050f09010e0d050105010f1d070e0d062409050f0a0b03100204030506060306060109080303060118080a050a06 80
    0x6284039680148202e004504055500c1d10060340f45803a24005c2107140701090f16860f4640c0030304042403200c00c0406010b031003103440351081581400240a84078500410120555200109000110140c20718420403580c100c000441c81009901e030484243d814203400b40861400895680101038116001d080082800e508440040840031021121012052159400314008001c04070020301c2c44802441505410b04121480c000000d021500d400302c55442941d969640d40014050031400c4000f060062045041c4180d00008640e0140341581000c0c00c0041402100179000c41c1d1030300d64410143c001500003400704400444001c2105824004442c01610400e0718840818815541d1260500900440d82c803803000d5911050090300811a940100340e1500c121024951171780306500040c0061031045028200d82c0c20140300341032406a018080da4140f1084c80010710451000000341d0740c1c04102480e010f19542c9001c20f9030248a017054005550304d0040c101c442080c0304001901900c81d5205440 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 223360188 1250 223358938 223358963
    0x7110717060f13110f0d060e100b01120203090106050d08030103031701060f030902060409021602130203042f1002010c02061609050f040e01020a0f0e030c0d08160605090109 76
    0x2800103080320444050000180005694011801240380f0002c413110103003407001030440590000d14103c00c80c0310211961030f251031101001c3c2005109005604c60341800a0001018180010300081d206603e00c02c42c95501100050303035078600f500318038004d20015040b001d11a249d82041c41041c3d00901050b40401c0700b003030318141c1b405c103005440d5040b0780c0c103969800781c40350340000214060100b02178142d03840002403002181814641c4010050300e208100c0e43c5030050910f01c18041105104545045101c1c4144100000304490004503654014410f0301c9590b800f030300904583c01c24009005198000c41140040e100081c1c0551003031700540400c2d0212281c03076640006907480f044034882d6020001340b0810041000d4140808400005000203001140304054950b4640c02c80e0844600c0c0ca001070240011003101c0c1d500f00407841c1c102c182c160040e029050300d840120720000c01d0224014400c41d000034441c007418454880100f0803a5004000348a5410000c00b0213001e0580320405640034420701d01d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 223361438 1250 223360188 223360201
    0x7080105011d0d05070509010902070204051311060d021c06030308060d05120c01021e070c1d010501080406020904141b07051506060c010203010603050f090c0d0b0711071706 76
    0x208407910100001d00804201100b00c4288042100c0c0f0345030481e014441c0c018045200d03960464454040d1104860060700c4160500400c400e0302c0015011248941d01c10011002181c0702600d2078901c58010784540da0b40d4240c41d11050020310a031034103104400805100d00750b1000072a00050110b0340a5030f20384d90189c40e03107000c100c500d01c11644000d1003a400b81e41001e183e48000d2014045049280c000181001c92151030101d0364050303e1f100003245100021000c040220f0302a004018003c0e0400c100f4441d847c1440080302c0c0d0506010f0141802450000074040040e5034040b100e030340402401c180144500701280b107440d600e05079101041e64841d100d01e1040c5200200c280d40445401400502103a6200d00000045e100c014004580103d03003041040d171032110900040d4000d115940c1e00083c10714040c9245107401300041c04081d0503400401051070269240158400400d410100840bc1900c404100340d8204020030611340840c0030b00b000000e201c020319404664035481d800c0136507600b9501d91 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 223362688 1250 223361438 223361447
    0x1505120606090d0b130506040c0f06020f07090225060b040b01052106060903070b09030c01030605310c0302030402100c030f111513020f0303040501050d05151002060708010501 77
    0x7505503000b00300182443d01040c0354007807494008400684c02000f011180d1100780c01e100d4115020346d04500014420010001d4502c60f02000f13200c140b01500909501144076031320b0f10424801d1140e200d401045110400c3c3c0f9108690180f03a40c0700003100300e0001207103440c5024005072841d07184500d1034201700204a50080d811241d50b109440d884411481009900e50304e4410003802e40b6400200c2800a290182c80810030f00c806000c40820301c1d038444021504040c60540c002280314101410310304100300c40c0c0c4460a59110807a815503104001d880c2c00384161200950340f040741d2101c6400d02c14848a5a0b41580c01140a01d0095401c2e202d0012820b0301981c020130050310040019802040388030829108000b9842401c3e034030800d960280d06c6d00f41900c02041e800741d6202c1c3c0c000d1008501201142fa1900310009580b40130380c080c50a140c0b41ca40060154020201041c1620707485400084503040304142e05054454001d180e07820012000c1e50080d43d030842200c80002250148001041940c000c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 223363938 1250 223362688 223362697
    0x31112031513140c1e07030512070c060c180f030503040b030a0f090b061002070806061207050303030c040518010b03071b050d081009140703090305041505120606 71
    0x6440c10500241c4007814000c0c190010100b400885588002d00705451221441c401d0045aaa0840940b01d0004548090b0304461002c0d032003920040c01c010745c400090f04032080d03407407442c0c82c40e051105036030301e00b001554180303001c440040c05280740691450074560017a0f4150a403c1010406003407d40d2100c0042403101d0311804090a568000d00c000c00002c0d0030034000310392000c10500080b80c2c150859492070184c941c4440202c07a42d01c0c04004100c082d00700b4902038444800e1610041c21580e2801c08015100d10300508030500036030604001d00d0540c0d00802041000308006002c403507682c03070080491a0203070091b0080c14440c0003288400010a03500c941158160742450248514544a058051b110b00134001e0024a90380420300040e00419401d01c0844c0324500716840c0d14049149c42540544d0111098108030080c51030320f283e246850102030b200c540d009450b400d0000b1a05414101030b9424003c1354080070070900350b0409106066884000381038907a508075200400b64580c0410400300d03024 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 223365188 1250 223363938 223363951
    0x3030206102907020d080c06040b06100e1002030405130501090c020706170402040902100905030c0d03200a050d020109031e1706060c0f0609060f090a030c03050d0903111203 76
    0x2001141c15142e0403070b0300020002c05200500d05198400750307a85210082d0400010622140c00c40020401441000c4000544c010405c9924402c034a01058004e401c410500200e540942121001981030034000c0041302c0141000501000310b03800008141e4000e44000d001d010315a81c14650b80040c443c0c000070f0300c501541c07103a0702d0304298005005892440e0810041040c0c1e032044d190810a030141e00da40c9030721121049290b8030001400d06100038146030170600741c103040c010003000f00b03c20b01190b44804580d104121040e0710b800c41c4845a0b4000745025000c00c8094014000c03c601d80035034507015842001402c1c0b0948842034404403480101104c031101c41d840b000031501d003042400c134410701c2001282d40624028425420a401c00c8201d5103000d2551307840b1101d43e400340042c8005c28404110040d40048a210599103510306000d02c551106e03001400181804420f0404404240c000c0c000c3c4c65050785203040800c6944280c0c14001d180180d03440281da024080c1500182803a208001140c0c0b0602c0b = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 223366438 1250 223365188 223365239
    0xa0c05030423030904090f06050105060c070501142a0c03060c030a0b0d0b10030308010b16140709150501030c020706020c011202300903040302010c02040f150303020610 74
    0x1a9101d1000d16040b40c0c2c84001c0d01140001c014044140d944ea00c1400e14181c0101850b2000d00c0392032074175404540060308400c3c80f8980610003a1041a000212102620000c1c6800607032846481440003090107042d0740a61182482c502e4283c0300024078070714614100e0b0101c2143e4944000b101850740310501952a0360b484d900c00c2000412040842d0065040900003400141024036540c6400c0000b81c0c0a4803c0d89603840000c4080040c1075000e034580d4094040e00341001d260425844401140d6005124000c02501c00f00c2c03840e805030300082c0318140007810490402e014200c0d0007404a21404c910340181c0380401c6c81c0220041d48140700107a00011743c0c480390000c1021800321070054802c40160700001c0344540d0208500400030480c251000740b5240102c12222114448500c2c440181c0e00c003c02d404010782c003c2c40100090303a0720040034804035070140c4000070592a0040c0b4400904011040001001140b5000004159001807100d1091540900b481c6009441d6448440700c01c5000440700d1465 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 223367688 1250 223366438 223366463
    0x5040b072c0310060303080702010f0209030c0f01120204080d110102030907031113060e0402010f0c032a06050403080a0b0f151305030a08040f051c110f15030a0c050304 74
    0xa4124440e54003107004089501400c00030400505842135900110f000800e54020700030170a8090140c40040e5001100940c10b02c0c0030540441c0e50786030581c00c2c1a1003040c464107080c0692340038483e19801700c040300070290364441d2142d070702d140e940481901c40000034034082d00b00c28540006109480c0079006680c00f07004200c0c45e540b00c2841214641c02c20f10780c401c2c41c11411141140c000d12514004014103544c03140d040c41c1c140009407a41c01d01082d000140101c00610308000b961000c1c0c03a040400038425059901801d00c2c558601030444400002c114500e00710034081403503080201c440c0710310521101804200308007401c3c040c0c1d40101402054012501c00904000c00030541c3c007400302003181800100c0215640d0303000078904901e22000783c49440340040d00340542d90701a484180584010b403202000d070b2140f2b00040c1075043d141c04000c1c060b001002c1000d03003203582e4100c5440c1c582000902ca0990b03d00c4200050485500c00c3d6003003c0e415107850801d60100e8014001d481c4541c1d00401c40c804003 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 223368938 1250 223367688 223367747
    0x3040803091e030c01350f010e0c030c03220807060b100e21071502010c05090604050f03070504050c250302030a050a141306021614060a03140a05040b07 67
    0x7070351006509906c81a00c98283c1e583c04410300300c00f8140201c0410051610381010b588041400d0b070b06800080c00c1e0503000c0108800001c1100881b604419220150355903980d5540c040c6c01d0320301c1d8411001c10b48100c100005018000b0440c00723801130340e001c1c0104100160f03130755007007101c0c00e01d100044c5800308211403040040391800103660849900308402d41062410300c034540e40d080020130780002400000100010b40c2481c0e09104019800d012410094070340b0078058009041806144100c0384030b9202c89102c18001e0310144000b02c000c00e00070300280030500704078240c6034042d084001a240400007a003008081c21051010100080ba05500950301c5c03c0e60350041102d49078040554803007440000c070110607003411030400500e0f01c2102843c00550740307410807070003d092090800c8098040307000048180300101c11044d04440c0420700f150700554441403068254043c262041d500b8884070f50301c4041100c010f9560f002140f055100d04815107880da101d80080d0740c031207440c0d06a200303100c004074503a400 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 223370188 1250 223368938 223368947
    0xd02010f050a0e09010e0906090606090f0702010e1501080d020606060304260a120c030b032a0a18060b070804090f0905032802120d05070504050303040803091e030c01 73
    0x3441c0c0c08a03c0c080c0c0c100003d500100e42088800c0c0d00980e10b1600340010094888418000c03141c0011191010700101d0a14030002403c040b00940300d5004400110003055025000758028000c035100303002514000070001c528120b50001c02d01c100780c06802080d0305030307500030320120340e00d44690801405a81586c8564581c0c0c1c040103c4a480c00605110750404560b0412030310014024102981d41c40942e4190819440c2098458000d607000c2814109403014490382d5000c9184100c4510f01002c40c40301e04913805c0100740310f076203601241d5084800e40d400882d10300344940a0b0303c10300c2d110400034400c5540d2a8004a1140315820002d400703100207002c20300030207283e5041824624000100440e900701641c658070704660000c004203d203a000941c400d075541003181440028559107001034003051a5a855043c0300340b05002060030250b69807000114241c3c09003007078802810001d006c076a203c5440305241541d0b50700035000e1500c180c2c074502007503804880c40d29a502200c1e2001e005888000440f000559 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 223371438 1250 223370188 223370197
    0x815010212040806010504060e06010c06050603070f17010c020d05030c180402040e06030714010c02130e0604080d14070e040c0e04111e07021c0f0f0c050f0d02010f05 73
    0x14118010380030141d84000315200076002600e41c14024000c154034190401c4112100c580c091150380411030100f080c1a1303000080940c00941002c1c001c142c55840c0b400090409003550004082d610342004042402d0a10361505908290150000c005240d081801a030b600d048240c44a80090001c20018040521102c05043e039404018250748132903002600180c280d0f000b58003d0501090228200001c51608201c40001803001e01c0c00050a0700000000801c400140c10000e4000e403e21410400705001640c0500e800802442c25124103003024a0120101d5200307a401f020703282e0900115203d04441c9501843c0103c800f615410f1052800348240006001490000745c140401e900d090851380e2a54010541d03844051101e1540d1003150b80780c1d4142001c1824001140550144516401070f202c02c0c3c02010300445003203054410300c20310f00d441d000d035102520008106c8503484a0070340c1040740d141515800c1c0c4804450180ca020034250503c54a014203042c0a40024507040c140308460307002e1030040 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 223372688 1250 223371438 223371481
    0x60b300907030210141c1b020d1416030c030215010b12070e031020070804090207050709090c1d090d120f0e0601060e0604080c090a0905010c0806100f08 67
    0x32030242145d0881031300c950004006c550f241d800c00b030068103540c40316100301031448030540e81e079501e800d004080083d40c40310160201c10500c0340724141894804d070400140c80130310401d090881040b07043c40c03500078000802c990046001d8441c00c00e2041d0408080c0c0d81d100c5c10385240c0541e0b24202940c100d081e004221003e040300e024003000580c0c04040e91024000440072101c0447c0108120305000c0c1412060802e04c1d1051166680030b00640d00024000710860b801c82e0071348140941c440d901803c280c0d0900505900420b501d51500142100700410750780034400b141c12090b03041c074000b008070750340e440d000d01d089903a50682e4000c00900700c002401501b000c2014002c1c402c00090044000102034121345034080c910700706500403801005072a51000704180d42c100c0036212141014a0144030583c0c0303c0985a03403901c100f4000307002548804455110380000768001000703000c04485d6400203441088207442c050700449c180c15030811501d0069070080c24440700307036854840700e549150007a030b030108495410 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 223373938 1250 223372688 223372697
    0xf0212071a0a0309021e0109060906020703060e12032e05031905120c1e2811060403080a09170d0e12060711100c0c02060d060b300907030210 62
    0x1080142c2c507032043c81ea064081400c0d02c3c0f105002c40c0c3d0005040a08c0551100d002c125582205001e0180e01041a104480d8069808900c0b0f440a89201c0e007004105600a1500c11010080001c0300040850058040d580e00b5500b0000c280c03441007003e100c00641c050550598070020790b40380201c424401c0403650602490075564100d946c40c1c8080201da2105100400e2a40000e10b070201a64424580c0d50503990540b00411080c0d401c04c0844401904148841a41d203980490035070078429034039282c164481e0000e0545984640300c0c0f80030340c20354202d40e840303e0015072441c07000b248201d84e00c00c1c980c0c0c40b050050000c01c4c0c280e10030320b4221444a02c42030b010390811202014a001d01e0300420035540110019107840d11006a01e200c010300c1c05101c1c0d94006139280c01c1c140d4010903142c100240800494043d100141c2c0c44442110940240c480e940c0800c08007040050313240c40305100321031041d1000180c1d0414007840401044c03184042001564010002d41003101700700018982074821b00c00c015200e081 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 223375188 1250 223373938 223373951
    0x901051309050607030b090a200315040908070b0a140a0b0102070e0c040501140a1d04090507080609010f020c03030a02031902040e0105010e191503180f0212071a0a03 73
    0x22034505101c01134510102103505d541805c1904d00d080c140280d44560f04040421031414140e003040c04442803120942600d90000021803144000c035100b41d034026002400a02c1f002581e458100d6040c2d0003181d050f43d041c84840c4c0440c1038201a4000c58092508024180c2c0003a11440030b05402000c42001e901d06510850348005188450a20010310610100000c40c0d01d4030324080000d08215281c241c0d0305240ba208108100d5915001410302c1070b0720418500c140840b18030140480d00030104464058071901c1001000140b424000030a98401c0380c0e0700000780100010104080300742d02401c0e4200e5511340051000414803d0541e010b503a0029400b1100310300d01d007a08980c80700b281d00030f40000e40760415440050000d940c04c103840f18071452045c1c40d02515100441d210605142c2c1034000c564610b00d1090503c54514880e4101c2800810044d4214180ea4498600707141140e1610108a00a007a011b00c480400e040101c0e419040320b5200c004900703418205e008000417540101044028190f4641 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 223376438 1250 223375188 223375193
    0x60d021302070605012d1a0703090506031015050702010c060e01111206010905090609072115090b0d0c030f0206070b01080609010f020301080a0b132406080307020901051309 76
    0x244500800401342c4440c900f00004036081c40c1ba003030800f084038504074120300c00c004100821031041500040e171000d554507081d15150484201c030311070b030041e036001d880407051028a000b82c03441c0da4121769004fe010290ba030007045056620380181c002c080d0126101844050100700190486001103000000009140d101c0f0840100941c103c4c2100c0e111400722001004919604030301c0080207860300b1500c041003880e1190000700780c5880105081c08102d46101c42c201219079600498008044c0c802041c0007103056058012210b4401e8403807000903038140b10001d415800c003640706000c6a0b4210003403141c640e0841d110f1154110348810106d8101404100983c0401c00c00501907000c0c20b0761b0b8024280340d0900c00140c0303003551561903400030824410401000100303400114069080e03800365803114250359202000303c00c6440300c40044d1034048010b100f034240014100329800e000440d48820002c0300c0e1035484140d070342d01030420000d4000740d00000501962034407500d0344120000050001c10a40c0155 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 223377688 1250 223376438 223376441
    0x10b04120c0807060c0605060103050c0d0c02010b121501150504060f02160e01090c0908060114010c06020c0a02010801090501441006050411040626010806040605070503060d0213020706 81
    0x4e0303000000050520345070728108034150096a8001100346020322441c10102441800d80c40740302160a6010b07035403400103071441e000307410400c15050014550401c4162102c5007640b40d001d01c1c10b10b81c1e040c00b0703110f001252030043d0f00304560131103140e90b50b228141030030248281c500c0311404901c901540b1542c2d480f81c1080315144981805804010004540c0c3d5160000d61070548607041d07405010700100300003d0000d03400000c1c000381101c007582404c02da10444140161a40000381c14082d001c43e0000402c4060014000b8503004100e1003030341c0e485501da90f11f01101e0111078007800740402c500503050713009011440d0407a91548242100b1000443d01c1180140200700310359409485070340d44c0152108810344c40b0307940b056400504050700c7c10300403541c6070103002c00948524040d0006003d8054501d00d40b080c0d01c41040510300050000d0148a0b503165030038943c1d209800c0310104c80850408000984a520440913a40100b41c050701c807020b9900580d0800c42903d10141d20343c1801c560900000c80440c105 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 223378938 1250 223377688 223377703
    0x91804060207031103070210050d0621051515040b01091e08060c0403050a020915030304080106081002072310141608040206120a021323010206010b04120c08 69
    0x203034401a540eaa01e440c1c06044100080703581c003241d030024490b0102580b9644000c505090161904503500d0340c03403550803802403000e41c0100b0f00040003880e040191190050002e01000e0042d0100d9101410382da62000fa401c400b04c818102051010815481508282d003000506060506000009586070002c0681008445200c20600c210310101000001070074009a42c001c114039010600c0c06040d0780b00d9591762040c800b4000d018115840015841400000203c481420024107aa030b54507600d60b42c0a0181c00d49004884203401520300c4200e03807007224400c403004964004114500310315103003043c03c507849042d1040805030241c801d0604c1008035074400e6003170b0701c00000c180c46401d082005152080d400100841000c1c003030a4824000035039200020746414038010744416809545400d050740c00390046210024440c40d003050045801800090403c040315000c1d0034038902c18510704012642c030759081c81030058100f070070401840101c9180e0740245540d80a041c42c44e241c82d1f55103c00d40d00e06600c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 223380188 1250 223378938 223378943
    0x70602040b0a080a0608190803090106050d0f0303060504060f032306070c0b100e1602030d1104060e090c0f130503120301050118060e06090d0215180d17091804 70
    0x383c2c0c008001000d1001d2180901410f81e0b00014940910764400c90300d41414403100c041d2500c8404400aa4020000d4020070003900c030181c074012650000340380000300f1040d81103089000ca41084030209050a2901c104012510120101100c082c91521910744518244c00c000b003c1c03a5900d940303000d8550080001c0c9010346020741c7d41b010382001900740742c032405034050720321030400c004030004000542d0070409103030b000502d428210a00c000c800f82e06074a14070401c01486a22800c0c124035005405102020308121030340d40d2190070680724004200440504215151182e50800b40701e0a001e02e424640900001040c2c00311202006881e000024500660011605904600040144003a59000a18813041a401030011382c2d6281403c2c07000e01800c009030200744c0030748004100070215aa07030f081e22136907490300906658a514110320038042c5a50100d40202c84014503041c4556603814150203174030780c198001040c1c419034080c008444031990702c04c041e07490344101500129a09043d00b80b50721401240f = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 223381294 1106 223380188 223380197
    0x40902060301301101030e0a0b071209050708010c0e03070e1f03060c0305010f08070b120402041407081609120209091c0320040614070602040b0a 64
    0x20350b40e4468400500300f60480e000740300f1044040400c04030281e03024410660001c415903a00c2103581001003806a2800015880d644904014904502641d901080c18004c90f10b601e840c08142d500459210395480318040c4145401881c0403811903c190701a24038245840300031400382400820301440e111380080c8251030032000c1c2c04030a000d145c3c04442041039405142000700101024054184e001c40140b502181200c000a00d41d81180c0802c9103652400e900400c4601e079001d00500101c0e0060b40343d68150000b080d01d401d4280c030814083c4c1c0ca01c1e25600c2e02c0c0d0400302c50b1110303512842d402e01ca5003410501040445503e40c44806806503111501500c403008a01e25000c501e075016004204141c842812555154001c068049002a8100c40b003440004c10500c03039100d940706502c0030507402541c2000c2c52101c180a0300490307003c2c00b001810141c0c0c4a20b014000d9000c10010700004 = true := by decide +kernel

theorem cover : BRFrame.Cov 223201438 223381294 := by
  have h0 := BRFrame.cov_init 223201438
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223201438 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223201438 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223201438 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223201438 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223201438 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223201438 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223201438 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223201438 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223201438 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223201438 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223201438 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223201438 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223201438 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223201438 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223201438 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223201438 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223201438 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223201438 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223201438 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223201438 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223201438 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223201438 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223201438 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223201438 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223201438 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223201438 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223201438 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223201438 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223201438 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223201438 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223201438 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223201438 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223201438 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223201438 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223201438 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223201438 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223201438 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223201438 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223201438 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223201438 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223201438 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223201438 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223201438 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223201438 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223201438 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223201438 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223201438 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223201438 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223201438 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223201438 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223201438 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223201438 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223201438 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223201438 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223201438 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223201438 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223201438 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223201438 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223201438 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223201438 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223201438 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223201438 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223201438 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223201438 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223201438 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223201438 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223201438 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223201438 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223201438 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223201438 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223201438 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223201438 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223201438 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223201438 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223201438 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223201438 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223201438 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223201438 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223201438 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223201438 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223201438 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223201438 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223201438 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223201438 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223201438 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223201438 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223201438 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223201438 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223201438 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223201438 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223201438 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223201438 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223201438 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223201438 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223201438 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223201438 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223201438 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223201438 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223201438 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223201438 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223201438 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223201438 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223201438 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223201438 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223201438 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223201438 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223201438 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223201438 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223201438 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223201438 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223201438 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223201438 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223201438 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223201438 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223201438 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223201438 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223201438 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223201438 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223201438 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223201438 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223201438 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223201438 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223201438 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223201438 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223201438 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223201438 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223201438 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223201438 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223201438 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223201438 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223201438 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223201438 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223201438 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223201438 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223201438 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223201438 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223201438 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223201438 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223201438 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223201438 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223201438 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223201438 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223201438 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223201438 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 223201438 ≤ n) (h2 : n < 223381294) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
