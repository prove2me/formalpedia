-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2476
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:49:28.571176+00:00
-- url     : https://prove2.me/submissions/2b260abd-d108-41d4-b9fd-f81f8b2c1a75

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 445143884 ≤ n < 445323741 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 445145134 1250 445143884 445143889
    0xb040f14030d0807140c060118151202031923060702072304090b0109051014010c03031d010c020f0304060e090703020d020a0c050c04110313020d0f030e010f0e 70
    0x50806840e100f40b00d08600841c0307125108000c02c81c0b6084035042d04070303240c3e0b000302d10306038403010288030b00484000741d012210303044201ea01c10403c10b170340d40028043c030462030002c100103a40c0e0180d0701039925020b28000c050741880c40109100e0101c0c0705000c1d10101031026011040f01d4a1000946030301d551025080211868000a41c4819540803155443c020140070481005005419181541150800d9084000c002022000c1c40c140d07440460180055130b10300c1260303040307003c5c01c2c460341d010134404c40301c010820f50140d0501c2100501a203408582e01d0b0019401c1043e801a81c6500d02030381e95a1127101c004a2fa0503c1900d078600d1015010314503040c80c001002b4421120084070912074120b100101d03110314043e604550280b0030b40c1c2d805540b60303007100300060424100c139a8242c44c107000312112507505142c24410100e01e40490940103007107440340154242060035400040760045c40101d039800203d44003900401005111f542d0f401103400f41403000400c20303010014954140050300420000300d6 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 445146384 1250 445145134 445145143
    0xa03080a0813080f0f071e0c0b0708250615180209130b060705060a0902090f070f0e18090601031403360d0f0209101206020702040b0303040b040f1403 66
    0x46444603a56525401702c0310494a59200e60200103010950b4040c400942501c8613420b000c1c001d000380d075800c604a130341302e21101041c800c10303400510400040050f21440e40700402242e81210601c80005902c0d80240d540d0000c64541b1001c800e802c95004000b00030b5005004a61810988615400e508060540e0085020702c000c2c484034804060300c3d46980c0500e07807900703010b80b4120b42c0c2000450ba81c9050141c0582d008050481050307004d0b030791000000701450075403e0858004c05041d07940d40c0c10680160740840d003501200a1044d4040080ca036106555148100305900959165000e4550782d491743c40e004101404281c080c09581c0c10512141e10900528070035030206100104010f0022103c0100c0f000317210656410180d40b10340c07003e034a07009205235980601c205c98400d17141024162110000d1015a600707904c2902c20480803034001e140029610340150103150720150000c1044000480003c0c00c0d908183c12400c0c0c1c00c40003140c20050b88985d601c00c400200314043d03c0070b01451000c000b2070b46a = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 445147634 1250 445146384 445146397
    0x307080f130f080c0d0209060108060a05101806020d080705130f0801090b0603070f1418010b0304050705060a050708090a0f0b0c061806010e10050a03080a081308 71
    0xa810020420310303142522282101d21494a075800d031a00c080e102d1500440c1e0b102c050180f07410512840865403141d0600040180000d500182500b12650b1010011648094002c1c0116042080d00f0000926901c90003815141c00b4150f8135407110036001000c0c0840c80700d040717030702c041c046603c645034074a41c09821941d5a81c1081d6546401995004050070038021a94142d025541c8a08890400154030006622804034039108291041c456142c03101019031300d4400d4095504040040001044070040410304400308140140040c0300089a080c2c91000e84030099010b100107800000030003013004014020b4074040c040480b80c1324104800520010154015a034009040742400070340700c94a581c0d60308600000302080407a6a5250307455140304c21b041c1d04409026011441100c0115806d40484c84c806040310220400030200c40c2e280c1140d0000c400ca0180984c10203208114010130103031103001001010314000e1220503a00c04000800a0100c48010250844040170801c0c1c440090a060200c070300703 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 445148884 1250 445147634 445147643
    0x1502041d101502010b03070603140f0c040b0a020a1e0302120a051c0e0a060f11190c02010512040c0f1d010302040c03110310030219060507080325020a050d0504080307 73
    0x51040710340410f82c010100070302d06907070621030840009040340c0d05800c01c1501080d510010100383d110b040d03064840450580310850301d6a8144000d00a080505024110540051040303804049403a201d2501403403100c100d850009900400d220140b41d010080713411b820800c0d1444070700c0c000c00100e0040040c0144c444000d2081040b20201d0310360b080c550014a5500c080c1e900f9586984141d1514600500e6500c004003125414203880040340000c14099400d2092021050900074401d41c400b00c03280c201d2403804030305101c030500010425907042092035108601c00d40864036824102a9403014000c1250320a90104100c0300c0644580041812081d0450b607058801050015100009501401c0300c2c200e900c03910311000c010014802c11480754002228020b07a0290707800c41d13084800100c0001c2c10b010f400007140c820400040010717034640041d0391081c007070b0481450b17903029403800e140741c01c4020ed1a240107078080302c07022041c080f06100d03208084402e428020701c2c007032900358101d48a0080000103030 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 445150134 1250 445148884 445148909
    0x20a091b0c032705120d0e010207050303040302190b030109020d0b0a05012f0d050405130b10110307080c0624030a030c051204060c12030908070b0a06031502041d10 72
    0x43d82c2c0150524500301600d070042051280042d41a440f603a250b5a80c000040020400c81d203020065001107001e40030303144c000e800b40d890541140c00340301a000070090440a518000c140014020700150040e601900c02c1007000740c2d85601004205090f0381c81040010310860203c1c000b0445a078000d43c030140c496019101818400300c5500101c9103607015915415601d006484940c25040d80c408000c10990700d080b114100380d0a06181a01c0454928110b034540010300c000f816800305003c1d48072000c1d41c414100840b46481150303522005160001d41031100147d100d103041c084003007814500c4223800c0d01501d1203d803604030140006640c0c1c1911040250900c840e10070340e1014404188014090710000b0107410b60754680e125002004103403000ba06489180501819900061090187d101125005616141082c130035880e0b44690020241413546896542c94001002910a54800000d050000030050300d4034608955604403100d00343e2413107442c00b80d42d001c0226003181c4440c248103941c05000070340c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 445151384 1250 445150134 445150187
    0xa0b19060e04150e03370215090708010c0e091f0504090615030f0210050c0c04020a12240602010608031204020d0512040906050105090315070507020a091b0c03 70
    0x210051804c1c90b881c0e0030501001541c04c10441c091042c05504032652650107480100b607141092040b40c2d5000401c005821001c0d40c810003140c01520303581c00c02601019202507644e911116800c4528607900d807404103800a80203901840d102c1c021a900507440004562007124000c0d410202544600807a407040d95110200002e0151913130121401100f0060864006926401d00170000103640804030700c2860303000800c81c6018422800e0b100214038a400034074101050390704200c0603402c581010030411254a04000e0301c08028080c2e5141080082d40d41c0d43d0f54013003202c01142102503a001802568140b0b9010400503100204442d81c2c0010740c0117400e07850300e9038800240300d120341620181c00c601c501070007085003100b1040200100c0f80001c008010309a510b200640b00c9000350921294140c00c4441107000d000c00e0052015400611850914601303c84c6500060042c0b40c035800206106c2d40c0d40c0c1c3e0b440c00f159000804407802c040b60781050440040e41e81d400034182003a084403044480c0c444801c0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 445152634 1250 445151384 445151423
    0x90303180902031008280b0415050a060609060f08240d05010e010606140304061a03010c0915050301050a331106060109260c030a0b19060e04 62
    0x503a0040c0101d96000c0d581d0382480c0114981c2c0d41c1d050301403401c050040c0080710440c10801d40000200c0c180001d4000754010b121b03114100209401401954032252800620754411158410070f4030a038202031000580c030342400001005100303103410480a0007212108000b6058024a0f0103500c000c0c051208108000840709002d0007103450a076040c0c005443e00610410810190402c02c20110110020030080351748480488144070041d49482c0c03021030400c00f08011850b150483d03201c0d00032100b51042008051030100782110f403c010003000051000d0000d22071600c001340150700001144c64200d066505140009181010741c2c821102c920340652195080c41d4013450b41c105903402182458100354107601c0000c0c101414941c120a4107024002c00900c043d80540545000e6444034000d100d60b88906100100b00246d0404081849200c1d6035811070140e41c00300000601e00d403240d031441c0214207011062014241d20780f9605481c142c102403040c800c0011740070030030340d01c541c101060540b444040683e = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 445153884 1250 445152634 445152677
    0x51e0d060f0207151b0e120127033c0311072103050108122a0a0516080d030506011704050c010906020105040f0f02031507021005090d090303 62
    0x200207841c1400840c5040c00e00c0b201d86080442442881d81c00d000c10010300c0728a410b10307070617481040003041803000b10401e41e0606074205072007074a0440002524a03400c802183c2c2098064844900445040c110310040560103004d0315006108520041ca000c80e60300e600540d5815800300702c010700b01c5a81400341085107c1e8010002240c01403801c2683c0c0d40507801c1005101840050038241d0215200c80c0040d6240b080c41024102c2e070040025007040144440381514a0b480031a0a000039049541c108402c445004555108000c4810082482d2209891b2007424034003100041e21000d031102104008000c00480c00224644c52840c000038541e40c0c160040c0e030205030381110340e0310846a010402c0100103000400110f02c42090701c80329443c0799100000c81c2a01c4044070001d0540d485050f0801c001207102c42c049803258402010b464880c1c550313240074100181c048924000507804680d800b5101c1c4040d100e1150420381d803401401c0c1c0601c07041c0001c0c090b0089440000e04002c200c18244d034a8403000321 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 445155134 1250 445153884 445153901
    0xe12070e0c07152304231e0102090907021902101101050a090b090120180d0b04020406061403070e1201060608220c0311041b0201050907051e0d06 64
    0x2550b952455040603c0c1400030700000001c1c0102950b6183d103815403441c1400074504c200d6000200b91007450001910041040c0542c0041110744590b440001048040b2661603c1c5408110300040e22001c07070504000c034128001e0b18107410b54001403d400092241100ca0000e55601130f102501074000c070320b01c102c1d411036001031061b900f07518140600001188903081401c1681c0210020f21300e5844110105089809620020000040c404508070441040e0000742120000c4401d000790746803914000b181080c4800b440460302c1c1c10a403020042140380a2050502520030b500c0c0000d031142990100f00e0681c07101030800c5051000c0d920341d161b0b0175603070f42c4600d84102010710000e0207200d6030f4880c0502900380503100c81012402c40c4001d80c0e1101c03603001c1d0110340c580c2c1010703c41e201545582c03680038842601d501404c0c0c11903110594004c6400100000b015240b0056000044d2440c0c1485142d04004864006070f00c18003094240a07801456021840c0c0300740c0d0700f00c1c0d00d6025480c0e41c0ca0490014002d00 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 445156384 1250 445155134 445155143
    0x1050a060f1806020d03050f060a061206050405040f050f010204050d020105031b0c0a110f150d0213030c0510030c2304180c0210060f09020d0b04050411010e12070e0c07 74
    0xd0400f00d030803580031440740c80d00340182c1c9082c4030a454914011038090801c6074829003000c0406800c01a541c85400c04484140134941e0003d81c03140c1b90303008a415070701c044406440c9001e04680403004c0110800104000747c034540000c50801e42410002a00a0302c0c41c1006810402c0100100d9440c000bc5e04080d48000104444203075501d030104005616810350f5901030b0303620314049234111061300740f034080103107450340007030503641c0c1901c80d82807240b4a50402c019280c1015424001303000b07406210200e00001d540a0000300c02e8040c640b00800c40c548480c070071000300f01130408003401a810b8002190b03444a0250410201c02400309614203449800b5660010311651504108001c04041c07a600c02c1503490b6850782507900c4c0c0036141d0188007d4a41d5845164010030b21000104900b5200d40d010b0803007059203038070209101120f000050240c80f015030f01901c0c218541c009240c0a580c00c0a1816500001501c001d905100442160784d101c842921800f640b05c070b003c000080380715040104590b401030b0310 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 445157634 1250 445156384 445156427
    0x20108190b04060e10060306080618030f0c030d180c050609010c020310050a0507021f1a130608010c1103032d0f0609070914130605040e060402041401050a060f 70
    0x841c101c20700744002c10303501480c003000e44617400701c0c200e4802e00404080d504400000c00c4103459550101c603140340c3ca03a00c40803482c04180310100484030914010818402480d0065856403040c0c0c0540c011681402460178030742c040c0c0e0f1409000548542c20716403c8403401c0711080d031180144001039543d0b0100460096250284001d00401d1489550010b4041c180c5100104101d0f600c104c01aa81c494404030180220b001480e21101002c00c00e4200352804100010500050800b01010a003a42d10710f400d0082d00750303100c020901c000c00c0c013489125180c21007131408420140c850a0300c25100c0c8005444490f00001e4082004498450014856a00010403619080500c0c0c02c1d00c40070200e17802074414031321800000c4007048070607101d140404140c42c000d0031a0598600c0c03050030401040040008220442d486000c00941079460784211007032004060040c0c40c407482d00340704000480d20f0001e10907000150720001440681c07961070752142507502604041c54400c50b101000c0d21413616605a061407001c0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 445158884 1250 445157634 445157639
    0xc0313061d011404060606050306031203362a0d0203030915030106121e2a020c150711090a200c100b330309030403120804020108190b0406 61
    0x143d8115104600500e0700b04099520740d401110b0b5407105441c3c0c035505501518018814002610080d6005062604004400720a503000302c0c80080d1452283d02100c0303030450340f407400300400784482d200694001c2503601d0001e8654526070154001c02c7c5026024181604812045450800032246891001003030300c10443d081c1c589a040c82e41c02409180002500300d00c032176000034005d02881440c0810000241e1210fa01c06644030001c080c40c2e41d8151b0784150005444a076100b48211040007a90160302a10003015007009021103c0130818800b030f2a08020402d40010826100d0b03c1c00220108441c2d000c2d05480da15909009070804030741c8030000444049100142c004600d0080c041a1408001d980c12900c200f40e404040310003801140b900030030b841142860718104171040741841d9000105081c503000f201c002c408440d070400c9078011040e03840081e09000388250120120f000000390b02e84108140381c6903000a01c5120064142040819141250f40f155282500540076002002d40308001c51503 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 445160134 1250 445158884 445158911
    0xb030408090112061404090f120809011404050d08060a08031809010519090e030708071a060603010f0e04020d02060706060608010b12011401020a05060403050405090c0313061d01 78
    0x14062107803540880c15049501d55000800c0c051079046030340d4440e0042ea140c1d011003d1001500943e40102d40540300c5800d1280092007008510600d410303140e4944455151080025013129a2968926420850b40c400c02000445c0000c0d81401500c1c02d15040300c082e103034000424052400794000a881307000201c0c9000c0c6565044510761480501100d4010080e66580c080c4000d50200304240040041208001e026404054201440c65207014044178603003281c5032201c03080f030b03040000d0440c0c01d00b55281c1c9a41034081e43d102c0503070b08490b044980c20f00e1545880d01c0029414014440c03049a418558001001d40d81d81c0120342560355000b8010325aa0f058500e054001804030340103400c04904541c0c0045000c0c02c0070001d460b00300e8203c000f003110590030014280c1c00d140c4021000e40c1144501080f000000d84144429405180709881d01e648036401c06040001001000303040e141c00190138820000c09a4040d500419450303001000000c0301820030084091040d4280342034842c560034441c1c40d21004 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 445161384 1250 445160134 445160137
    0x1e0212032e060804030e09040f0f0c050418020f0f1f0e0a0b0a030f1506200f0604050c0105090a140a080d02070611060106091e05031c030e062206060b030408 69
    0x4e510070b40d90f0100300c6a08004000003030130241c8020344040c04010440e400500d071804c40d25001802040116000e41c1c3d254000f80580e80c1880c4403039807120801031620114100500c030703500810310490710046d403c0f403200e0120b0b000c0044c3ca040342150546001c031020f0b00c1c0f40254040f1000880140900101300d449000c40c900369030041d205900002e1804001412040740c0b4400c1016001d54039003c1d4a030741d85808421210492219000040d1009602425000342c00810514540da0104030181c1aa40303082c2c10414180703074841c0c8649042c40020003220419030349070701b00303d0166483d042140e01c4100c01040800d810a8203500401051b22403100818502030700010103078100c8000382d0320103164141c142162626103100303205001c00329034024400d215041001c402c2100d0401c0558070311051580d1030300041c3c500b40130062403803e4800489140111a83c0c94000c1107982108000184007031f042c00c0c58240b4406140310500416118001685401c210b0250040381c000c0c12a04040c607103a04003400c04803d213 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 445162634 1250 445161384 445161391
    0x913020a020d090312210240060302070302191b0f15030b010c060216030909050906041103030c010504050f011b020d030911101e0212032e0608 63
    0x1601c58103080d081c001c0e10a9080f201580e6012403030f80e8103444180000e6407804060441d0724000c072500484075455015604c003400585140a050980c0c8004007901c02c20300e00010f58056401109030043c0a588030140e0054404880443c54010b030385141074101241032484a540542c58106c00031220b400b8880c001c1420001d000041d2020f0840076a0f4a0f4000b00150303441c402d4280c0c98101c1950f0082d1540251310080391484181019990080c05540f20002ca03070040796000300d01c03894030702824245980100c0b00400740113401c808001c3c40c10009500c0da55000014401400e00f14899070003070154406005441d00380710070400030700050030b003850303c60b459000880f1300058540c81d0140a4550148034403409501c13448503000f81c01d100c2c081110480107000c1ca03110945102000352201d10795510f40b4650a891424141d440c40c0d14008000704100441d20b840ca12001103500c4900c005103a0700c065803c40307030401e1040080c13500e1241201c01544030b14a085610040c11882102e001500d9500100c07003071310 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 445163884 1250 445162634 445162637
    0xf0e0402070f02031920180103050303010f09090519021207060504091505090115020732010203030c0409090215030403050705011b050a0f110601060908010b0d2103020913020a 77
    0x94200f60001111740404521038054003802c40b00404d42440080030508000202010304040041e032149454468055003e034400c43e0075606c00801042288004501d0002400b03100c1307401d224405154840d00e9641428121031115003a085c0d02c41c004654440d91840d200c0c4100380240c910003650f0310000b0f00b283e0841c1c440d0010b15070404c642038901d0882c800e0658141e0b00b000300041056424200c0c82c0c0d22281300c1c1c07102d540c02d521807402d000c107258448805a000421510851210b10031018559002600c60400414199801402030260555502050340d041e41c00d007000c00600003209000050001010b039005c1040c0c80d00010030302c424982e00c40014403816000700c00030700030741040703441300d46007080d2440313000000030b400b40000302c0e10a11440d21031005480300e24000080000165509040943c01c1c0d0040000c203148400030061150700380214404014103e035803a40742ca8031070310f480c21803100321910b004803145a4040601c2590103503043c0c905410380504000a001540c403802c07002503109201460 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 445165134 1250 445163884 445163893
    0x60f1509090803071101020d021204110904030905060c070b36030a032609060a0f020f04031103070b0d0f05010e061806010c02030f0303040c0b04150f0e0402070f0203 73
    0x60485101d0203528042940b2051562860b52009412510041c2c03500071400f180d5020440c500d080751250028010a0344c180c000340400707007001c2ca07080764520001d0503140d014001200401021941008180040f40d50944015558000d0036500504140060f046404d025402050740120040303d42c8940f4a0500411003d441c0301940854170f2010106000046900d5070010000c000024859001c035087c100503c2011510647c40325080a0b18000403141c45ca0039601c80c0003040b129070804c2c0105200241c02c2501185082c400256011040c400ea000241040383e20307511426668508100c1c8000800315002030648400c292800080030b000703022640030000341814000306000c04c80002060099a0043c032101610751001c0411401c0d6100902d000d051010400e5803001684060014513084d152100c0603503907034a001e00c2c020b0480794141e001902c03284820310090106110803075409070300c01d60742d08058080c2203202604440020100111503045800440c00c0f40400001c0800654154400c906a5 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 445166384 1250 445165134 445165139
    0x30b010801061a16020a0e0411010e01030605010c230304090509120307020a15020f0a020a05060a0b211f0213060206070905040e0a0506040302060703050c0f030c16060f15 75
    0x30803140c401d203080d8008080f81003100780300100c4181d50100d407a0744013400b4110482e17600c403c84072101c00c01711010340b2000c0e190348074a0491b607400b0601d07206810003402c00708016400c010008000d203544910060181102c203280381f2034001040c903c404018510404c9a580b0703600c41d030380d1001410080d212130307003244545208007060884210030b80340f0448140d4002c1000649640313640e030b084c40d00b00500501f240c0e07003000840c5131482043c1c018180325a83c0d030020540480079150081c0b4150006180c00f400920700180b014160f80c514400c1c4422085801170788165130000a0a542081100003140410381c81a016101c0181c0c000c1c0c016044452100c3d40c04140c440c0da8403401d98580100f00c2d54000054058601804186800d0384000d591007243c031b04a80201d000e5545c3c05161a00a072016070169101000f00b00d0f4050f031500820780d00825401c541c2c0e09104020715401860300000c1c11000300c480d400300d0410311a50021000301c944a400010600410314019100c07402000b0140380b42518902d4020007 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 445167634 1250 445166384 445166399
    0x1807050409150504060b03030c0c0f0603090c1e19060315051507030c060c0305180109020102190203192004020c030703050a090b0301080d0306061806030b01021204030b01080106 78
    0x20074180c40e4100851401402d8520450700003400000d00c00c0303441d03a40e9800c01380c0d103645041000d0114050510010803080506c00100054000d42d507402d00e1088a04204200c140d000108801e540301070140c4625020011b0381d0000e41d1081c2410910780e810262039080d040e80c980001039840b0841d08a51070801068100c204000c040c68414020150041843d043c8500340d0b0144400401210303003c1d2400b412821071603501c51003274a180c005034200081d02c910500546016203400d020498401c00001c1103c40320313560000c0e468034080900041400303103031925203095460a0050b80180140fa80317000d80f03162a1481c10103080f64800e90741c200b90114400286115003458400c446000310786100460500c01e05640031030303490344200c051004000d000400010903500312800b950117000c91001038a1050b59041000b8200c03811540914104400c107144080c0700c00d60f144005082d02d04500e80880c81c294600c006074a441c0c16014036043c81000004c0c00418071106034945d605a80042c0f00a0040a964500 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 445168884 1250 445167634 445167641
    0xd0f050f1e04020111030f0409050a0b0a23060f0703020d0f0207050f0d060e0f030c1209010503040f230321010b0a08070309120e010207050a230d080318070504 70
    0xa89200300c601000400c2c0950b004200895103405440100ea180ca004c51400d0b0984e50020390103046440e0711401480705412040c00707440740d4100d06035202120180740603082410701002000d07002201d15221118003480d00c0f5003085914580f24920303080c0c3c1e18055482c000b036988140701c8106001403210103903c20007030310100304001180c100070724603510004400c0800c10f28030740c2d00d0411194655202400c0441c1d80081c4440b071105076540b030241da26400954900b03810444c065010b40b0240d001000070703051a80c0c120302030741d80040d00400e110711941c03414a0103c003481741c081c40031005502c02800c041d2400c40000002c1c81c4480c8c001103014115400480c4000f001c41b0300713014407400d0040038004500128421690190311525a240101d0707445034544030080110364002d45080044e041180b03516242d601004070303000030711042c1c99210906107051000c5040c1c814203071082101c0b0000207044001940c918101041a0b40c00c00c82c07080d540c1c00c1c120520540003940c0c0c1801d0010f40120740340082c842c9041d20 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 445170134 1250 445168884 445168921
    0x21020304050a032a0b0a030e0304050a030c030b09120d0e01060504050a0b030f010b0102030a0c21030f0c2a03031e060303120b0901170a05100510230907050d0f050f 72
    0x40020342070203611b030030036005010200d12002e1248014031000843e960f0328810340004502690700d00c50164254180810441d00061409a0340c2d03000b494115481c64003041100c117200c0790301c140081c85400024a50b07024141542c80250702609120a1255a200c1c03548044014001202241d0702c907810103043c1d50a8681c008691405600280240d0660074003401c10264503a2048a540c0c0403540b24400480b00400c7d0b064505000075541c90764141b1600e85403090504030729050a03c103051445c110200e00380050003441c1c1c0c10101c0c0c0440902c0f400c01d0b0080d004504480751000c0340005421155100600070300c650300c001d0700012400d80340802c0040c8984102d4195410181c10050b5a03800d1020740c3c1002d5100007540003ca101d41c140c1c4601045090044483c4e1805040000c00c9a09110720034100f042500d42000c0e014070070b5071208280081d440107014010301010340f102803ea5550240c25545401070b1019885024186020f000941403d07a102c5c0d0711411032510b440141d0b440b65640d48580300d1014 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 445171384 1250 445170134 445170149
    0xf0616020f060a180f0818030a0b160e040e0d021903080408090a0b1602010e121b0a0b040603020403030f0e061b010b0301021314040921020304050a032a 67
    0x20030101d610b010440c1c00c01180b4003514400400d004e50f407956040000a1503800a0700e800e58040744401d0503401c280031582040804500800e40c0b1400e580b22010645000761000700038201482c0c22008050142d855815102001403080002000a8915540f55100106004014001d4070007070b000030780c0a031803a401c006805680e5401503560719541c56550f1b502c0b29013142e038041440a000a48880d0a03801407181100340c482000d0952071074070024094044102400d4440d40c0e10810810000b84001170740c0366008644094010958114030108071303030310000e41040c40c24140c000340110b81c00b82c05400a000300ca10956548129100256084400c640024074403648050204141aa10070404620910100c061400004d5040140d0700280c22640900305000712090300c40400c02c0b01ea00780440d80030400100b030b1001c0c0842805a07072103000d4410030603ca100000100f03c4100071852080003920090702002d441804442e0726810a261003401c0c01c0c0390301c800e000c1c001855030600b0050701070480407903944 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 445172634 1250 445171384 445171393
    0x1104080d03060b04091a09180105070302031b221e0605090105090f03070e0a06030218070c0b100506130e060409030509010509122b030209010206010b07060e0f0616020f 74
    0x28002c0020142503e0340d051a07050405006a1285687d141c0300680915002141d8407440342e900003815081d41c07001800141414411300070032604001010108211a4002c8941d656a074200780c42d04544204191030110200480b84020030042c1e04448000d104100c000d410303864440c2d56030001c507482d02c101100280060401d1100100c9810141400215410010162402d136a100c0a100841040844400403040e1301d4500070001d5050007024440c0709040306944145a00e4983e00141260b10454001440c00c594000001c4c40741d00c0c0b00030721501401c4000d00c0310b07688040b45d503a2280001c005001c0c1105000000012484520702481803100c0c2c3c1c0d17411b07101e0f2418041c2003001907400340c108401c031039003100290241080060f428004001031800b003101011500010480000342c500b840c0c030804060510420440409070380028a0a0440b000c00158a942d940c0380d2410034050400198800b20350b20403090385110030301c4042041482110207005000b54190700360800c82e56041d00c00c240101ca43c22 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 445173884 1250 445172634 445172639
    0xa0f030c1a0420060f0414011b0f06050f04210306030c030609032a061e0c0305091903120e03070c030602030406062301120f1104080d03060b04 63
    0x40c1110100080c010845005035400c0d81c00074001403401280d08841c0c03400d0302c85154000704440882c2e140950019581e20381011010200a00548668003a2107458a00d0702c81400d00c980c410004952141c6000358211780c014410f04d0301c0b001500c14103000b11100350510340060740324550540c540e48900e400c0030894140514500c00709140c6102c821500040513150314022010454241e41c6000951040600180c0c01c042410014080240850700d8500300c4600d403041d544103c41c075440702e4026500004001140a0007108074004814801c881c14140341c10821000071880c1c03d6400740340318004030010390700515903010000c0c07003030502c2050040100d40310103103075540910b2952091050a4103001103078540900384c2c440e0050918994002c5400c00d40000800c000c012050090170014890b00d051071034110039030946901d03182402c0781c101e41004080c2c1c4071084003101c1038000400c4907240c0e9004000c003080d0414400003a91090003038610310f21540f000c4094881c864456102195030000c1814102070 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 445175134 1250 445173884 445173887
    0x305060a150c141e030d0b030d1d130f02030601020f010e030d090f0209040503280f0e0103060905101a0a0206010614041505030405190803340203030609090a0f03 71
    0x40d10169800d40e407185070414200002144134110358002044003c54881c1544880310042e101c0c110701940c001d8001c0d0305540e41294002c0700c03401d4140d0146048000441c1440b010a0508101e001d61450060608912210752451680198080c0c6d0081e4261400c0310318071180c69003a110096440d514a500030803241141d18880d90001840610400303c15003d60f8464000811225003910140c4903a00000b900d03960300c200c1c028045070300b580d403294070300d6400c80d01c25400342c0b074920000d10000500204c0c10381001c07242e11070350040002c2d01210000308900c1c244280b020302d401400c0c1c0a02c030122040070700b8080c03220050205580303510131a030f0700405c00c5a013800f100300c6021040c440c850070300d800181710220b6250380c1043c20b4007104c5200c1c0d490b10b89914043c2082440c0c1410f622100f0040c61101e851100070880d20000c4a612102c0e140003c0c40c0c044103400004441070010b641700710342c40000c0701c0704044140e003c4000c0d40203190440f0022601c2d160314450319141c50310740d0ba0040c08200e11107804800207 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 445176384 1250 445175134 445175153
    0x60a06080c09040b030a050d081f15021903030c0f1403010b09180f0f130b0f0c1e090a320a05030d0905132007050c0a03030305060a150c 60
    0x12038018001040406400000c6890014800c800b11b1f8a500584168450703140d01400301a1300c0511010310510786028500184840d1015001c1da4203803080385400c44686034000c0110382081d080ca600c81e0060f080c0141801001400800e00c21400114803242c5c40403807a2140140121285141c5503283c503691030650048035503171110000c11b410142c40003520003801c1c0e888000074421034403030701c42017414580300840b444207020041c1b0f54400c0311219882800442d40c0300e000c4684c80100844035604c9a11003420005881c0100215410481010603c05891035031801c09401c2000046d2900721025403510004070781c440e03c0d19045402001030a100f40c052801846c00020b10a90103440b441003c1c0d152004207082c000c8032032070341d000705401c1e000c1084241072a640c521500322003800c0401410003c41044a01d2003004092030b2031625011130322000b03000c400c0c4801308511034003c2626415a55a02d80500501001c56215104026240000682a0385001c0103001d100c441c0c0d47e1403000311200e59454000 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 445177634 1250 445176384 445176397
    0x10022b0e0405220606090506040203040503031602030f0406020304050a09020c0d030c0309080c0f0c030f0a02060705101407020106350f03031906080f0d0f14180306060a06080c 77
    0x4200030783c104000d0208a00c2800f072621070280324041001410500c01c02c05070f0b1400360881c0d000d1881081000007044012040e65080050003070b441441c04801c5408030720354052020111213a103000180021215000401442169026114008501e030745444c0c000490103007403400142a0081e090342c6050303512951015408116505000405810340d44030840d0b50b4000c5482d840240d480b4404816011000b04030f00f910701441140100800e41600c0c00f141d844025101c4024011440800d042d010881d00b484400b80c01154001c082221014050100448400650340c3e14090352a081d00030540312114080303007180701000c94071013240010300740e45085031001c64441700303d09018407541c07440d241d030702480190b016038110400e904031022254290710440b0b210344d0049085601210003011884808107a101c0400c03011b003000000341d00710f00000d0344d00070350300c058141d542c10380091040480b421150b4144500c2d40c2c2a401c44500e50750310800d006603000c0c0c40c010718002c140e41c10001141000480700920a = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 445178884 1250 445177634 445177651
    0x21c050a03121506080105090a05060609240a0e1005071e060905060a0501090e150a0509070e190e03340c2c010308071104090210022b0e0405 62
    0x100000004040c40b40f00b1210f030460320006001e800100450b240815010b6040b1240b488204007030308120000032820300c02d000310203000345940c81760100003202d490303c0300a000120403203490340d444400000420790709a89a00c1840b03400c070100f1080c40d440c07142050f01c001a81c041e603104046651100c0020b50710540c030108841032034407400d11100043c400e000c050b00402d4080c4c0c02003401c1d414080e42d8400c0d18515044292990701030068082d004120702c940d40d1b045100900c0016081e2500e660860406c0d2460704401d00000030780080c8445080c181c604e2985c140060001080303201d01d807016081d01c9100d10441803075a07958484d070840e26036075507103004002c8200703d11100e0255a2190303107003958006254440d2405850030855403908214401c11000c02da086180f55140b65811540c0b001c960340034901c8094120f003052504200c203921030782d1000f000075800915042d41040d00110081d55120300320180034041d80d00318003102d020541d14443e100301c110b540e103a00b0340240d03540051000500005201c4503 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 445180134 1250 445178884 445178891
    0xc0608060d080703080702071505070609030309080c0f150f0f0601022409010c02010212040f02040603200a0501030b153114010206010303091707030506070c021c050a0312 75
    0x3000104620002c0035070a110751585c80182c50880006814072010b5402054444860000c40544a82c810f01321a801c0754800d400060380150f505040b40102001400203082000000382403450440019080405481c098200e4020150222a52401e101c080c0e0301c0302c80550811000c1040c0d41c41e44035440d6808101841101e26541420216103c0f4541d01c05001452441450521030065800c3c0035280b10850140025071420700c031004a443c0c01c01c0001d0000d00308002c4952040115640c6802c00c4000f1604604500c2e00c100702030b54540d404002e1217064621503000c0140001d415400390049001440d0001d00180d91045420030484555204a0001b00010302c004034011030340c1c2210b110000900021406100c4240c1090400208050484003450556000d8001000020740c044940d070192002490701803105107030703d9007241c03500081e9000242280a941c0800c550f23940e000c202c60752820300840b402e003290440281100d0301c2c0e0080000140407034001c0d03070110011074001c2c0103100c851440f000001 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 445181384 1250 445180134 445180159
    0x9040f030c0510060305071d13050106030605151c05030a050a09050a080307031220070305161407060318030f02150106120c03020310050126010f0614070c060806 71
    0xb414503e01106a040312603a965040c81400702c02c2100b03d001c0d2020590200806500d2a6005a010002031554903411805440c038000c00000390070910007035500800a005604005581981180341d003040036000d40180b59844500a020404100c010703600400035500d064500700c0300316001c0e0301c05820745c0103000110b41c000a641e214040c04078010008100a90780f07450641c64005c0143d800c485280b5941c60401c0070504c2c0381c2c800340ea00408840030010340c0560b0f401d0546800e5400340506081110001c010242c013205000051502140c20208130003920003035500c9400540131224081c0c5140c46004400805000090140a940b04061b00d68011581c1c10b4400c140300580c0f4282c00d82006000440d100c13485141e844035401410400710040c1001e41c1989448041245017030700c1481141c1c1046190300104114030382c00541e5080c0d0482130f20020310b496031981e245e016041350324030581c00001c00c0c6030b00c422009140002a51541a40703c884480c84034a40030040700c40b00006401c00d07a1101416602 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 445182634 1250 445181384 445181393
    0x8160c050a0503070215031501080406090501020c01050610020f070e040c030209070c020306070e010c060510080307050115090606093003020c01030b010e010c06051801060b220509040f030c 83
    0x1034401280c4542c0081d5a5594a031040c8404d100042c0b402492180d014030511050b6110308e0180481c6407020702c0c0c803c3c03856842c2d04069002e00700030a009841940f000801e0042c0000642105100d44400d482ca48c031003020f00d2404030b98030803144506107895008880c01707009880710300769100d800c1401000c5070041a512500040c810301410b175580004110102030fa403003182400d00007664404043e05101c038210f1015000a8490031841800800703069880c0001a0300c10301079010003004c3c040000481c1d446000074684a4000c1c50a086552000701d152840012824050700580c41a60b0307080d44c0f40384140340b40201545400e41d034441071501007920a1000002c9c00c0d00120ba0700f10460082e802007800d60140000034045804002c0494104681c5000055460741c000600112540d482000020039a4800840c10f0160034404a01d00495080102c0010a05200401303024040b41d00d00b200030103a11011145096581c8130722038245c022502c0c000080110700044200c000b00303406405e2080b40000103685 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 445183884 1250 445182634 445182643
    0x40203120a0c0b130b0103080d0e070f0f0807141e06120114091506071113061802090a09090809151e1201090b031f27020108160c05 58
    0xc0d403800070b14000958400c1c0b111404a650b00700881800c4141c500c840c907203441641030414000138081034000070f068003802009500c402d44003c1024140d0740702c942c54079502c48214120b0310030b0660f81110b180d0041080100860404122004031885404c2c03e21240140001607040c200c503180c1400c850411300d4100e0315100004c0c19000c0c400d05c0845069810420581c00e2804c4110001d4001d2009800b04014a00c0310800141c400c1d008580060721030300d146c50503442280101c03d0440e00040504c035224042074003900440203031110744030a1503124400c5010481240180c0d41403d40c0820407860400c441c0f070441d41b00c078a00070301031030741149070501e03c10110301e401c800c4a41c07440c0012030005619041140c0400000490072a54035002c0c40c094440106c03440d034030010b018203044075540b0b1440300f00320381e401c02c00316848541c510070510605071980341d00030042c0440c0340d400c90fa0340b000b00300c0700d2000e031030200800c6442ca50584441c0c117140c5686d00c110400300d43c9603030000d013804145020040440d00c02c02 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 445185134 1250 445183884 445183897
    0x8070c0b0c0306040c1b11130204120b07020d02030306091801051005040e1204030b09030403210f09060f0e031207060f0c08040f031116092301180504020312 69
    0xd00300b90349007808010701c070031070f140d40c08698104003803005000114800301040e0031169401050841c506480d4100103060140a00c1d0305402d07281c80040c0001e1040c02c0c102c02403c8150040750b030041555101a016600e4091003150480142c1040000884501d0643c10042d04074000e0039520b103194000c101690f00712141500c4114004a21030f07000c020520303050143d01040c24a8401a00b110850450394065070b00607400001c00600ca1140000e914a4080080d6001550000341e039400f8092003c01c8101144a003100c4100060150600102524064003070700301150703881d03070710403940a11100b4100c0700c44000a0b8105e515001c0e0030210100c81d0b5510740a4021240905d60005c0c4400c034200c00881142d442c41600f00c103003c204001c002c04600810440f540083d054140f044841414151060400b01491000402440c0596003c1132000c0268082c1c060091030082d22502d2449000032101d003000244500742c03507601c0201000105034940d82005800034405070441c1e030800f8010320001b41179003040 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 445186384 1250 445185134 445185151
    0x2070b03070c20030601140a44060708040305090d030201110c0f07120f021309020402030115030c0216051c0602040e10230409110901030305031e0906060108070c0b 72
    0x30440702140d40384c1442014010f0800081c510f80e01112500843c03180e42d000e03c80c4107032171038030f000d0303038000031202603140400c0030040c821140c147c41c0000c080094550005503015042c0c2c45000006480b0300c0c054107540c0e000f1038061310303141c1c03d101c0001c0400440302a00a0308800b15525100e07480042c400750b501818032280c5020140626201900d18140303002102c2e4094005903150030250f001040707040420603000341e01500e0003c4040035001492005d80300c074080080d0000d1001000090019001046005040e01540c0501c01c1072100c1d801207940b2100c50700c50000310140700da000c212500c2c00340304515610305403100c030440328842030321844226085544140812000c650800030428000141c22002c6e09054002901aa401102c4440c0f4002050f01e280e0045a039400320030240180c0154100a14000500c1d2524075a16440c00400642055401071014600710001500c04480e01459074031800c070507002084142d9600f001100c10f44c1e0050090700900840711f05074804a0f091100d80ca07c80e0079607 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 445187634 1250 445186384 445186433
    0x1513060e030c03010519090c0f0305070e01080604020a2c1503070e0f0103170903010f090b0c04182705070612020a05160c050a03050a061104030302070b03070c 70
    0x8241810071450480340ba110ba45070604204903903c0c403204000388203c04050007c1d401c1c9151a021301c10405541045411003030701d603000010403000207480c2050381c090a540c0c0e009039a90f201d0f920782c0d07541c0030b4038000d500c640340c0e45050018140c0c01003180b8080101032140c03d40c2110011015003080410303174007c2d44c1f03800d85148420490a041198400030f001e000600070a5203845010343c031106506000050112104070410400c4800c060300381c5140302c038020002c01800801c01003410060070f419808803104840da50020b035000b03a44609036001c5901c82c08040c1c107403c2103105c5a000404003191030144003002c00080060303140c011800840b80340c0c4103000a00d24a400d05001a0580c00d0200c8201e50241c010040711444580c002e00355401045891980c081440c0c00380703002c0f10b40340840c1c3c110907080200c0b2180041030140000b40381507500c2c0104420082144401c0d10800c02c0c2c852400080c0150b880402d0030440f0707407110f41c0250341c40380452030400b200315490340d51803001d00303086800002000c0340d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 445188884 1250 445187634 445187657
    0xf0f0c0503090105070908060c031308040806040c060207060c0813030c08064002010c02130614030c10050d06030f0804030326180f030a080108070b030405030405151306 74
    0x10900c03405030862006e0a080d03e040703180110351540c2d0384d00100303201d150040200100e161026008050b654480d03108039010385482e00d880b00a0b03030301d0004444c1641d07407010000c0009402800401e864090b40d5582d61111004001078a1340800356116442440420746a0040040800c4601504c3d0b006000c804000e40704504203040910403400e101c90480860700c4c0040310700c903031f5003001a0003241501a5408981560101400140d0f800020040042c1d00038021013903102c64149079901c01070550701700303504980c02084494103266803a405411615044150384985103101d80c01480074040038144400081691510b07035a402d000c140300580101c5200d000401d089c020950080c854864104561001c540c0c000a06006403d20190207040818402c600c5c0d4010004200d09201e8020700c00a48000ca940e038600c0100c005196901c01d00c5030914900031132402283c03000e42001124060340d0014000d40c2018140420040003544582309001000d000f00f00d180c092940c00380103440144200d845410b01c904 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 445190134 1250 445188884 445188901
    0xf0405150a110d0512090109050607021c11061b0f070503070b01140f040f0209030102032d07050f0d1805010504031202091f091a0c010c0e010f030f0f0c0503 69
    0x1051150081c800e40c00041c401c00f107880d40401a03034038486101843c01c44644038221b80b5401805003034405442400f9401c07c1202d45900010f00d00d511410800b070020b10144003000441d0f000f4981078005815030030480118113541c1107040b0301e0100e195507580052400512203465069a84421803c90301c41d0000b040c0402402640541103005004010041140c8074101d800240110b120182c1144034030780d6081c40c514140842e60550324a6034000c2e00071950390401081c2042c00d040c0d50440d6000701c82e41e61980d0700035129042d1166006038a1516494180341c02006031100d81e400000c0d155022955801901400040120344101c0c0d030b6024400001d02d40c103250400504203540703560075204103401000503013140d4880781c01030407000340f0303e48045804c0b084049003100e40800e1540f0400c600764104841300c034200c0c1050020101d214a003402045104a0440c0030344a1050c1d1450103408a940498114032440c00307500103203201c0ca514100020010340001d0840110b4184101400014501008000323040307 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 445191384 1250 445190134 445190147
    0x708160f0b1c05070203040506160209160507060e1207030f02010525030207170307080702100504030801050907120608070528060507050c130f0b040c02120f0405150a 73
    0x41c80c20303401c6107242810001640c801d0400c4120385011141d81e40001449080c03091050b0f802909000b080c0556848502e4280c107400c00c8100000da1092200101203025000058040c0d80006841d841c0c460800c078194580c0310090024248402c0703a40250020709141108031001024414402d46610444245480c0000e00710782000342030412212a9071144401d41d15800c103d040f0048513032a0140e81c500941c41c162500244242440c143d000b008001d11513065000510f01c2d114440030350071a010710040317171506c6050f5a81a00e010b000b00c0c560310010701030341c10000310060344a0110706100a01441e12007010f001c8030000d40c400c02840d04008c005101c01e19101c00d40d040748551008202508040d2201c40c03100b802c40c103100380404e01c100003c03104104030040c004c0b24000000140240e0640103810001c90280074100424080740d4600714070a00103103007d11580c00c102100d07034008c205500301c1012001a40d40b00070300c40c01004070b091100042ca0b07618086001d201e00c00400d50252105203128028284 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 445192634 1250 445191384 445191389
    0xa0e0c0d0302210c07030507031b0312030207020105120f071404030b01060f02120d05041103060709050909010b031903090f120305090105040b130503060a060503030304140708160f 79
    0xd056900082010079400503c406603500c0381524180104440e00e0000c69a2160341a001c0c994062034038000f040c4007022641034112406020048140542c42412a41250f901d000080000342c0b1664611003607442a40a0148944113060091424501407003421801d801214140090415035003040000c0b94450001031000700400d0300d0504042c2595035001108405000d820108101104040c000b1442001200c1c2c40000c1103030707007540d1810b0821400001e42422039060b80c540d01d4001c42d2003002d05002070300e5807161001d50f40e80031100341800201b052094016180f01e100d0364030b519a8000b0b46c1c1e8140304d0200e1500022000c2041210340e8076001c0c01803440c1c0c1e408050550071102c002c01170440681411300d6000d81c54540680e6400005005032514000c40e002085552008200b200080910081c90000c1d0b82c030407011544259111851441511503030700805130150402d0000c00c00107000c4000b581380940c3c0110548001399242c4904500c1d007444841c40310000500c1001c100600007018801101 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 445193884 1250 445192634 445192639
    0x402030f0a050a140304051e0a050f031506120706021b010206010312050c03040f080309151e0904020c0f06100801092f091501080f07090b0a030e01050a0e0c 69
    0x1001c07041921003d403907070f032403481c00741c00d40c20110045000c1500920484000d00001400909045070b0044c0c069000300c1000d809a0148049400c0801d551400c540c3c284180c42c8010003c1c0480701d5510820302003074002416486d00300119118044a007601400780ea409400c40d54018401c805928020440a800a03001541550010b4005001190710006c1100b0115040d0406556911105c0310300c0b407039441030f60301003d0020100300e004aa15500803008010740c400440725030101402c5612070507954031624002e40104131203214000c1d90442444040c01049030002d00c0103080c4204e0308101c90030321a03851605600b0350844801c000048881d0750103440908003140081001040c00d5540700071923124801e29110065030403080c600c451101c0341c2006004940900003966500302204000c040c0c110300c001c0c1c64041038448000440c0300c00b4044400d13214448690311203403e0751401d030300100198002505d6800701600c0300e9a81e2400282409668095582c0b2500058103404640c046800c0001a094051 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 445195134 1250 445193884 445193893
    0xf041e060506120f070c0f060c0215070509011103040e040609140a02060702061b070b04151803170c06011d15090a0c090321020f03040f03080901260402030f 69
    0x21618489407401c5580440d0212481290b174440d00c501b80d9040795031013001404201740c09440801c000003034001414420280c0c00716043d081c00f0311950340000d10115018000180c013801030300c04646c803d04081d141903181005903494640c490540300c5014000726000e0701d0541c0c946810408021b0700300c40d0225958001c2c009811a07200356400141e0720311403004047c0c81440080303000040090203500701c5140c0c03c421021070b410756030703036000f207445e50780051154000c030b40070034407910107030901031004890160401040400c07194219580c40c0c1810746090703200707807400760184100220810200003990290140060301d90b0561403454803a09008402403400007441c018010710105900c3e0500100e8004040c0311010500c0e690103081212100d00d070343d0028181605428035203030f40d40f180c4281010046507540c01c0d201911550350000350340780326501c50500c4042e225602080403458a0010b401059014504210081e841051050075940054030b41501c034803c0006001c00c51500308071f40c1c55181403600150 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 445196384 1250 445195134 445195147
    0x1207020606010906050409020f0c030705060a0c021506060d150e06040614031506030c0d08030a0612030503010b0a03020d021b060a0c0903021e040c02030301060906051201090b0f041e060506 83
    0x104540554030800c03c1041e00841c011451706001c9c000d0719080901c00040b240c40350101d0903c155500400e996110781c10780341640c0d9403107061011a481e1040141540810520389a031811304c0700070740c40b44030860700030345e0396141440044415103924001080b0034a178a0702c0c9424404c2c100301c11240240d016042c0480c05030700d041550340300402c071001010011800c1407071aa54040200341811050540c1d41e6100c42da8210351000c000302c0c200030314024543e40e030342080380035143c5804510400d002c0c0c80c0a17002c0b540520040bc100c031141d03402402e0183c0240740240c14001883c0229040e0382044d54003007600d100c2c50340b031007103120b200b080104d0348100610000d00425403003c401800344003c070300000c4e0140362040c21008400d404008000c0e0f07001c0d00078104100c1c00b80d040d00002d440340c00c203010b24800a8900d94001034194859010307660246860030341d00303405920b003482481c01460002040398200300000c51140c256595880350100a8941e9400f4a500280d108241c20071138216070806440b5481c10300c40f1 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 445197634 1250 445196384 445196387
    0x2070e090102130e041103121c021806070501021303210201060e060111070803040909050d08040506131110081b03091c0c0c03060209040507030c020c0906010c05031207020606010906 80
    0x11000301c40b07132140f07200841d84980c100304c013130010b000001940503c120703005120360400010042c10219a810403203c520300400594105910079201084d6015160003a4042c0c075241c94402004d1892023034000510b007102a40d100e04030140c1650003a60449200c0d4400c07501401940340c0340c4852412440200103081c2046901c01004c0000b800e082d041000318445a000503c0400402c80a0010b030421251503540da100070002078600310804652500401e030451074400d01176030009006a5004014100580e21004da0307006451030710078199035081080d81c1d4241c507611000c0485801506964440302e00d0301c0c20150460f810765107006040d1100344100100448040301140c3c0300d02d00d00040080081c140541a4201c410016424000e00f101c4400c103400030030080385a009080481c0141c3e0305100320740d01d440060307084580c291041c50140c0c200c200e00c14054907100700140c2d030103541414003514881090301c1d00c0d4a5030b0064203401c0101241d180903c54015010004a0750022092801e0303020b040c1040c10 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 445198884 1250 445197634 445197667
    0xb04021603050901030609060f06020c01020316033504020102190201090b0a03110409060509060406270f0905060a0608060403120506010c150b09011e030209090a0c0602070e090102 79
    0x102504026010411112aa00c45d401c0035000340b004820900006449c0d00380182820f00520405015224014802d0801e50001c01640c024543c21510000d0105c0c01d80c0b8190341d01207520313002c00c500c03420303089003100d4002d0001c0c2292900f2558007400d035903515261001916040382c0c41180d28440303441800c5000180ea004e540401641c100107186d0352503480004041c1c1c00340030341120044010b000480d0109500c402c40d4822012602304440c8840035032180707028001102c41e82d0040662a00890500c0c0244607980b0002c0c41ca2203946400000c2d0918454090100b1210030a004403182d8000c00b0622107000382c10300a04c8040e201c3d0760003902080c20183d0380035040034451551a520b040c0c603400060240c0e8052680d101c905c45d04510480031010950f16804001e00800020900c202c0c004000400c026811394078000d0079284601e040c850450a503000c002c40300700e00030701c258114414080b0840000340002c00c030b50020a000e0300107104113030500326013004001000308000700980c4103000c0440031000400 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 445200134 1250 445198884 445198927
    0x8030a0c27050105090f031e0d09062c030d0509040b090106020616091d090607020a0201050f072a0e07020105070f0f02030706051f050111210d18060b0402 68
    0x2044c075581c514207800b08222200d0503000e15414042c0c03a51546440344001e4803402040c03915000d5840a0011b14420384440c0d55a00178507001030200311090f050f00c100d100b0414050200246405249500000000e2500700c64900b20300005a0101c1e05510342e0902e4002d2901d10310084480300c0701981803540c025501c44d8024095050500c01e0f44442042030f005115400c040c1401d01c00b4a40c21803c4003040b22000401550026110700c034160009881c144089020800070307905035102da00c1c22100343d02051582e003094038255003802600024144801115030348007060600094414481c0340b4050500d261424000c02c0d000659062104106009901c54007815a465490411410858040c40201d01d14019004000e0909203003205024181ca07541d20420321030a1aa1004500705071160011160f4800c0c0710032005507640446441c00e0301003010700700e01030240340c0302030124200405808a142610f1100e80c149a0800710181150244607a9008085072400305032019032424540301d640111681242 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 445201384 1250 445200134 445200137
    0x306090f05010515030414191e0b041704090501080a050c031b1c060f060e010f061409030109230c010c02130e0f0a2001030c05030a0f020708030a0c270501 68
    0x1000500f0007c0540071043c0340c403210b4003115a004124a0403204e213551840c01594022484944c0158001c180e401c2c600b0b10a80c0b005040d040340d101e650384c11a0002c050324a8010901d414000400c2405113072041d180200200c1d40141540c188908055050514080b05d050117500005003a41e040c5903403865408a020095503440b2280c80051001204a84502c200074000c134140605104410060b8024406450075941e0102481c0d9942180c0044080c1c64450080410080951100d40080b550f0240c82241c40c050000b0441c1481d607500c2402040e08980c0d00000c503050403e55154118040082d01141042828070601c00c0c180c507000540e0503018080800f03800d540710101c0417510b98080c40745400d0700780c40380201c804080c01450308840c2c3e003406d801041c1070303030f008038a5001c0c05601c0790160101060150300c40b80e15548801c2c00c400040c00c130481e82030610f141c0801c2180b000550540040d403040081c5540003c2c036401c490300081030360324843c003216401400c00400c5e8414034901380a00e021503e09 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 445202634 1250 445201384 445201387
    0x30906070f0c050d060b0328150e0a05030721090b0a031515030b0301020a0e120309130203180708101a150702012606150c07060306090f05010515 64
    0x1185400d0b28050301e1504280d80151241e04c03083c003084400d400c4041080002c42c1500c069004141540603010424141e0642410312340820034003042c006200e0065466541c203001c40c03100200400d540c501100385004881a910006414043c403800f0f04c8590300c4803030f0700540c0200d20385014500900445190164480080c0001600c800c07440c040d078030648454218401255040f560754a0389840c0c8040e9011800110303040000d240351038901071007250048981ca8a8104a01d207540d814130503015180380d40784006102c00c2040801c99562a091500d038860f2a18025030b50b0300d01200304074599003000145900d940c2c04641c080c80800000304184048510801e000601c84044140340413800b560f03041110740000102d0800d5a0344001c150040138414000e8a4802200c6002c01525807145940034141311414030381ba000c50b00501d040c1411160b031049103202d030390034081c59072001800d2603000e9108901090341c0d204100081005802804884100f024042115600d00703c04a600c11841224000301e5440 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 445203884 1250 445202634 445202663
    0xc1b0e0402121c0201060f06090b0f030414010e0604020114070201080a050c070804090c200c0405041a100609120b0c0307090305060f060a0f031e02120d02030d0c0203090607 76
    0xd0411032480b88030000314404420b40f00c1c15001030300820300b83c0640159000071603000b28132140510000700c11119000c02051401d0007440c2d490034aa04094411640400080b154143c0e01c02c00340a009012800f40c4098443d5042a100250007103a007030101492501c070610524001d80e80018041d50700200707130803012071543d89003800c00c421449101001411410085400316110f031981d440880f82c8a11503c0b11216400505910b107855402d45280b02d81542c0310100d101990309260300440c0d040342c850903520450070302c4606072602d004d904980940364070f036040c0c904200e5503030700450710303c01843d0b000107501c4d0f035100c16258074180d002d00810500c008000000480c03a00f620841000004540200c19201282001c6400080c5140203903040c40c407444501c4c1e004244081801c0804044903448000d8210703494401040f1403c503030111100f40e80c0030031b101e220940c00000038030050261f4011540a1a0394480c44202c842c01c580707085000c003085500074440000c294480c07400716850b182d0030480c001030055 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 445205134 1250 445203884 445203919
    0x8040b070804050c06040f03060605090c0d0207020d021309030e120a1b0e0415051b120a09080a020d080a0b010903031206031b060e0906030606040e030c0d0c1b0e0402 73
    0x4d01600020342010b00020b0015403410840ca45034182c1b4403a490920420759520708001c07800c0025100c1c0130111104100b0742d24804110741c02450080c3c800740c092840c1102e107400040c1204007503042ca4021603144c0c0004010594002c502c0c503000c1c40c0440d110320409650b0700b0b4a17956031a1480004180e0110300490001116610006e00010501d0380c50420b0149454908400904244903210404a0508021850740326010710201e01c0500045032550510302107048c201c11000003d001d410040b5a030300c07100b20108800c10010f000690030383c3c0040035040301846004020100090a5421030fa181041c250000e070380c00199282201e8041c901400b0403079280030300e44010000c40c0d10003041d5000401c4507071400e04440050300d04649840c0c82e1384c082d241c1c1c18018400030f45c2c0221011541074001c0300c00559545820340c4200091480380c41200d0501003c0c48010745040b8401000070301003181d0143d03513010042034414059607000f55141c4c6010701450b024030f040e2910405400203200c0c8455403034556011 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 445206384 1250 445205134 445205143
    0x1701020706020f04030c0609030201080708070e040f0b100c15021b03180f240c0114041b0b0a020a0308130519060c0f020307060903170106180608040b07080405 70
    0x5030805000c668420b8510b20400181d4403501c41128514644000002c2090223070b15041308030394042e1505903c0c0c0e980c400040b9200031000b1300d51014001c840c1003801e00754950348a2442d000140d0080042d80142800800c0481e540d030584100400544200390740000d0302d400b8514a10501c034403030268550b00c890280c0c84141d080d090581c2603d02c00031a030300303040100300c0c000c400c5071a02c2944c1c3c40d03801c844010148251009607200001144050405170f1001020f82c400070b03c00c6280e05400025424004806141100000e0b0380a44030707050b00980101d900942d05503c0d10040c0b00201e0440d08d80b05140f50085e4a8948040000d410b00024800140852903200c8a80d58215031003000d484020000052101540140d81c0d4141c4006152805005913103004255440e90b0645a0300210700706841503503808003902144404030208604202100001141e07541d54602811854070b545170040015044052180e21a80c0072104000d10b003414040410703a0035034019001007452829988c103950302e052041c0390 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 445207634 1250 445206384 445206397
    0xe1201060b1c0b06030603213015010f0e040603120314090c030a110a0306021201060e031b010c11060a050c060f04021008070e1306171501170102 64
    0x40071000100d818400a800320701c035042c16000041041641e110074207109050000b1a100c40c1c0691040200c1240440000c0d9a0f24072045a20051481d1025004202c0019840f49101190b48810f4110702143c0e81409001c4175444100e4050908180381943c0009014100464180040c00003501504203151201d8003c40d02460300030301940d02071140408010018401104001d45800554020031000500481e0000840100900620300080d0f03984561708034000d488950395201d95400310000006543d80080c1181000082c5203c40541c9003100142050032048050751094000159815100080f0074220380c1c000700030f2030310020800030380c80d2180c201c94460910b00d500100101d81c1c00e0005501c08006e15400c0b01d1801a03072129110380390050f62400302a2002503000308982c03030511200384219101030703210055141104070040750b1000718045040c0400078081d02600d81100b882810700e550003054409141d60014004c200c0c04003074280c0401418044c0540784145000011060744003501035551 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 445208884 1250 445207634 445207649
    0x1081207080d20071b0e01150c0204050103030206040506092a01021006080c011b050706082a03070311090d0212030405040212150a060f0f140c011a0409030e120106 72
    0x400c1000b0141d00e01c89400c0b03210115a82a4117405034076404604030b1003882220010070a074a0789074204150043d1014000384041c00704442242002d015941d1030003520700030341c001d4015040e10300b098282503080240040640c0f01580c4880d42d00e100942800c403c0c1d44002440c0c001c1071071922800c1700100e0a042000443d00515424280c3c0400d40650200c2d901c45540000d03241c4210a1400d007100b59000080c00f84060a10742290404106560107000c0840d0f102c200c55141c01020090030018902004901c40700004945020040101030b40e050b200e102c00d11080120380d1414a841e08001810544585800038003c01c0007031a04c0102e4807040042c5c0740904001842951158030101c000c40c070801045840c1640d180000c2c04a030f0490030b04400410035911a07648a040c510301094080e101d89440c14090801c00c0b2040d1442502003030040080d1005d40118000420000c07070a806000c900603c11005a2085103018001d10020b9008165080803c078282d5042014820580c8a180100580d501400 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 445210134 1250 445208884 445208921
    0x90b180601140c1b0109050f0604050d0602040509100305060a02090f12071a0d0b0a03020604062706120507030e03040e0a150f081504020d39030b01081207080d 70
    0x42c1305000340c40001003000c002e82c0c1d41c01c212550307081042080300000400c550080c000300001d01203070424001d43c01c24603014680142c07415640788040350300700d6021125000d0101c443c42c000d20400000b40701483d0401e82c80401541403144410005440d051508080da109403a03422428900081c18024000104945000004045040b0130f0542d01075016103000d01c0c040d842d0030416100e6150503072160302030b0b035000380c03500e03003050b040c01000d80d201c0070308080010740c202062002c000501685000303c3c0c040c11040c0d540a42a1600701925803d4440c0549020181801c0240015214900205403000c403103031465010b401b42c4450b200030005102540c01603880d094a4980411031302021040441240d0581c403c552200c0d200305606c9c100e05906980095110810000750004140684a8126100608864109141c2555182e800c040c55003204004248104850800910181d885254014884600038108000c51840492031501c91400c00415504010892240d204229442400110008036445 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 445211384 1250 445210134 445210153
    0x702010e0d0905030c03011b110f070603020702041505031c090806010806070909180f03110a140c0f130c11070308190c020a06052d04090b180601140c 66
    0xa0032280c041c0070f501e020307101d066202e83c03003400d0521034104610300c0c1006441580c640c45004450312241d080d0800210b1080d0300070003000703690a100310702c010f194540300103944034454814042510001402068100b5030080d040165031000701d828100601c4801e0307100b02c0d140d82e0a505440d018202c1d0441c40c583e1082800100300841c0c000341c440e0280c2100d49815048075514260201501c0d10401c41400c0f03000070115003400541d100b40500031842c4242819000b64064180240c501541c11a055070300d48000b04c00c20364031607010b0041c0524118142c803e19101880320001c90030110001801314603071903582005071a11403080450900710b554620686000c640e0700d00300300d80c19420100c08034211041542e42140b60358000c0040e0003030b15a002d440004ac0318640740040d00c07150440f0300301360310003c2e80680d01041520b0311007020101c2101010700b5500c950402d00a041107030740600e45c55010312802089055000c0c01c001007a54801401d00e01404031558280492001c1e02072451903219510031039415 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 445212634 1250 445211384 445211387
    0x20c01121b08130b040b150a120809040f0218040c0512131109160207120b06041d030406020703050d0305071d0a090c0203030411011e08060303131205010b22050702010e0d 75
    0xca010b00047c0e682980302101d020f04002d8618214804d80b41024004c5405100086290000d4400100300600c0011603a11004030803080c0d82c0300201100b510001c40c8003800341480c0502c03903181000d41a2600c0303030a081c080e04401c15a02da001d8444c042c160301d2440310108101300d0700e03c50942e003980079241d00004e041440d22400703440c46402400c405030061070380204031002d10352a031361f85050300010032005a84515090200501103402d94401089c0e11f00c50303841c1101c4080005000038900c0383d00a110681ca1403c04c50f04101c0420810b104060a01050240c020750061664440001000e440d8454a03410b000094401c803d65205800250800100010390b54020001e14400d85c0a2195203020340c0c141001110030104950825800100008807103003810722880c0d01c02e90002c4040c1c2120f113041d02419403084409101c1e4805168150200440820050280a070301c0b5071010903520206c18201da0001554540290310a0044c0c49a8460004105501c00d40221074442d01280960302c8a2915040 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 445213884 1250 445212634 445212653
    0xe1608270601030312050613150f0f03230c131b0507110d020102030d0c031d07080706020105090c0906031f150e0f0a0b1f020c01121b08130b04 63
    0x10640c0461a0720764840c5d0a50054041c0b03600c280d030000c00303030420030940d019090002c03c0c01451402c0c0b0300703541001c08141ca049401c1100081d0128010b02d08445140d882c00e90b100f8100c501a42d001023042000464562100242300d4400720001c44803108407010b5104070900902480d40a0203480d091219211002e40d0810020038000380a03050243d042881101442610201102d0007401a071081140003642c142d190b102c0c5614883c00e2501041030041c1c000c45602d461184210182c00340c100b544108241e480130002480140781c680004d10681c900303060481d072210401c0a001d8000d5050200145881d603080c02508000849401d40c44141502c1e107002400804c8070802014191400c8000429075483d40b8215034862255074a61003800d658140012016201552090303800110b03000d0400c0c48060001c070f03640400c40c9240d0080080091900006014820309000c1001841c54585200340203901e1100540300d00d43c05040040c2e05803906400d4200d418014031014209170003407030602003040b41102 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 445215134 1250 445213884 445213889
    0x3070b0f04020a050105070506150d0b340206040f03050c0f0703050d05160f0812160305010e07051909080a060203060406050406180504020607020d1103070e1608270601 74
    0x80fa4140340a4840b0b0040d03505101d40720002e4a603070b10140000d1114000751942d0001224054140a400640c139a43c81c4141d10081e04d07142c40d01030513007282c0170340c43c100c4140030760042c3c3e181c9003418810741e80240081c0d101c200c0507101501400c188180c4105060042e402c07120401820000c51381986c0e0060400f40c0c94804500085446008122900d0422440741c010780e8403000b0020b806132001f11031030340c42259030301e8051001c0322031910601040e000d400c0d5640d4618407274184d2405031000c161038a040242241c10580154500812840502800035844401c0d02c1c1c20034041580362500380920541a54a442998450074041c400c10885400700441e540155010f51003e41e014094a07494004120580b00c5500640c0c1c0c2090030801a1911a10f082e00301c1504180040c01503132a00780c0e90b4012070310070515240c0a482c04101c002400440e42010041c040007004020b041e10b980d8280000030850030081c42c181070382045518000304416407694484034921103a0558050b01d83c00c0c1503403000b9101c203000d2 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 445216384 1250 445215134 445215139
    0x1407021011030603121b010203042616020f040618020c011a15160b160206060414011e0b0a0806030f070f0324060608011a040819020303070b0f0402 65
    0x10350001100c54914140ea0207030b00e00401425250005c040c0c8003030309420040102d4990a201ca010700c0034001c00784000c60007030380100d01941081a040c0359100302d00030700351034000721741100300b000c58906a00d0001910340300754111413107c2c3c1d05103180006409040300750030102d0744d14440030300b4040f0b0b540d15600402c41c4103503c2000384143c09519140c10f00030668001c90540051038201c450f030903040e00700001d01441d6511183e071004071343c19403219640e00700d0844008810012600050034245d0301000342ea98040d104640912a00c8804480d4180540040c8640501640700c081d6891104000c28209400303000c0f024a1541c4a122503200289152829a003443c041c1c040d200c4880c0c052500416807600755110000110b1034103246130355545800002c4000e20035180200802803040004038003621004180544c0c2d1345000d541807040581100d6042c0c00500741040c810402006084004107015481c40d52090074070a5409243c0040307030451058150040008500c60304110022418441d00ca002c3c41c0203 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 445217634 1250 445216384 445216391
    0xc05070f1a40090e0304050909030d021c0605030309130f021c0f050601230a050903100903030507171311060c060108100501031e050c0a0902120c0405180a14070210 72
    0x20b030030740b2500300c9681c0940d184c0742d42c1040000f48203d051413400b46030403203401c0b011649841c0e00791070790364102d81041011616005c5040070055907a0345c540a10400740c80110f01440c98920f1680016903101d4001c00000400c5441c2c4400150310156513058409030808a10100e03425628400c0718030080501c0c1d101c1c24013951406c8081036172548180340d801c0700310b40f0b00b00e03020071040d0b14002d4810b0160413101e801020400c0030031012815440600c5001a01c866211000c114000140b4001c3c0c2a1100140707100c0070403a0300030341c40080b82c00d1804a070b60400020754500d04e402c00c0c1801c04401d084000845503400c1013000510340b03000440011000d040790074031010394059441d09c05580c0c01751203080c07201030458150388003034202e084c81165007440c14502c11000c4a19020001c40030480e02a00707a8001d194040c0d02140c01010b03941100c000c540d110100c502030600d4203041c84c00142c2c0c903900000c44a0075030304180c80015001d009c260302c000281c6000052020461a0522009544407103c0c0f0b845d5007030711304 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 445218884 1250 445217634 445217639
    0xc030e031207140609031606150e07080c090a030305090a030c080601030c080d080a15050a14090112080a14160803160e010e01050a120204060c05070f1a40 68
    0x3c012034641d0258400001440c500000206044d1107603880c038a0507101c1c940c3d9140c2400150042050032002891a130998150342c0c5070118000c1c2480800a00c200c08005041001b1050707076442045890991b036140c208141c403510190301240765413905810040100d44030303403408140b54000240c52412a445800340041a0352110150b40d1503003013049040c000b280c203810209143c01d205030080544006a0f80c0183d4049548070002002203805a20050802c41010788402190a04c9602da81c050441040d030700110340119a2210414032850818500300084c42d18541000708180301220440c55881103803030041a83d60a264400313901c01c0c3d039541c10284e80364002111950280302407405140d016103414005038187c100540e580c0c2d2048500c0420812114046000e03060b007480038101505040ea04d01103110064540145408969086220141c1c0c4c9490100305088062030081c00e4610710300c00090301ea0710f0040500d01002c3c0c090080184000040f4800d06265860002310a003200b641c0c062054a82d5 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 445220134 1250 445218884 445218923
    0x30c0524010905060d150b040606020606132a030209040b0910050f180405070806011e050d0816030f030501050a03200d050706050405010f03060b03070c030e031207 72
    0x19418003281825503010004000c00b59540d40710340e034400740180924801105503035849018021810302d41188a030f5030101e410310360038603100c3c184c0940028001802c25040500028820301144034040c1c030302c107481d10f02c16054503030040e00644080031141e8001c0300400900c0f2014000e50801c0c40c0743c1b40503500c0c0c400c1c1141a1b00d030803c90716009044500e804e074400b5081000b84082c0c3c01c50316000b103410888141044101c001071000c40c900c01d03409240640390803801c101609081c014180d00544102200103158800607042c11542c80455404855492418035185014059400383d81c0c82680301c013203001044020f00d0b0700b200000c0350102d000d55003005982e883c0c0d41000a06822400040d041b50f4020717030f0310603018007022043e2954060040030040459000c1e914180381c0070443d04428002400032404000b1540c2040030307100419014142408540d0408004a5444c00020061804c002540ca142c405150152072041e007024006020f0b01c00c8015030307403940034407588544070444590b01d12544090405 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 445221384 1250 445220134 445220173
    0x30f13031205101d0a0e060c1207021218090108070b09040f0603060603050a030f0f0e0f120105070306030c05030f0a0209100b16020f04050f0c0c10020403030c05 71
    0x2503a0544a4495200040d5104001888014400500700c20400004140f007a500100812908650a4040b20f5841c2000400c01500c03810315a0b1211a40f0010030f0124006000040e40c00c031404a809011059840c1802280341110110b44800010b200003024031100503002c000004100041c0c6000903541d9a40440315a180424807a43c20184c60900429105150a03000b840341402c0418002c19003e4490310f60100315026940202d503103a01c040300400c20140c1010300f46003280300714284480000c045a1006d001c010f0105241c6124040c240b90590301d0341d0300c0750038031b131200e85d100c2000304014074040102078028821030005490240c00c89800103000e140019213440038106410181014240c66400d02c520f131400a04a48005012101c0104401842801a255514820200b1111180c10f401481a400030b8201407501070b03801c10003000f08128030f41d06d440b500a100d00021540e10500d4180c0c56003404815481081e4081c0001800018554041429010f250040e026112224840c1d580004030 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 445222634 1250 445221384 445221421
    0x1060e010f050a0f2309030d090b04090e010935040305070b090310050f060111060609010e090109021c0b0718050415092f0405061b0a0c080102030f 65
    0x80c2d040255400e158400d03420041d5060050810341d00400c4000c800350714030300710040702c4028000e000c60801420b2a041000e050030070740d641003118945042c020340908501c21401513042d000d482d0b04646450340d2003540300502190300140348888000120540c00c1d40c0184800703200340000000001c001a05080d182103d04480d0300c80000d0000360300d401e4414005170000c0c603031154103000d421300c001d03e000c2c101d001e2203114414031624040280345c008001b40114164424a06882e80105d04000081d103403c0011419644e10700304080361942d510300094054030000c8802904034494044a00b03408520707101900d003091242e210081c1c1583e03210b60450b020300500b04607140d0200450740403c640e05299000390024034035501024031440d11154a001654100300c2402e0b00c102c01000c105445c4c0040940a59021004400340d615040c582400550f82d402031640c2d0039800105000c1600030107004114080e10f41364403400028841d40d5514004c0d00070340040703a02010845450340050034103c41400c00c0c860 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 445223884 1250 445222634 445222637
    0x501050c0307110a03051b040c090e271f0c0503072a0804060f14190305090708120a090608130821090a0c120c0b07030504090903050301060e010f 64
    0x400d100c2d612425003043e40151840e4210080e2140400441d406201d550080000f4824480c50b081c1c196080c001120034410298081201c001c00901c40034000306c22043d000742002e046c003814111810b20000703040004841c4914140300d50044007070110b004420b020000756441c0d0040001520f1410241e40e60304c0110390305000210142c00d52010f1500400d00103003006500040360082500f0360703440040c00c0d84190005c6021944c0301d10030090003540000c02c242200b00303e061990078140c17408180d954032803000a0400074541c9540000f0400c0200b0440c90300104407200480d0001f07443c41c03030041d0565000605200000e824079001040d49406030101038001d0f403114802054940740782d00d5044040d002215001440e42101c0000407540c8031007000d440c0a8038801d40a032100382c0451070b0420744030340702e980005031041110034001e001c20300b440030303070780c110380b0281e041603a500c00342d1400726114800c2d5000400d034907251500740002d1540c003a0141d41a03030100d450b05c402028850b4010f484d80e01c0f03182c49950 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 445225134 1250 445223884 445223887
    0x20106180c1403040b16030e030301060e030d030c0e270403050405120319080405010212090f07090506030a032106030b0105090c03160e030703020303041503050112050c09060a0504090c0306060501050c03 89
    0x11510089006d10014544040c94005028000130b28842d00719802170384085c000920701c51080c6141e103001d0007a100324050500701006080610708001c5d01c1c89401580d883c3c4036002da12075a01c448031a61842c21000320b00507469001c60324080ca000341660f00980034080c000c80709074144007050300c400002c2b504607417101d41c2844107018182a0445003480b00a20880f0340b0754003031244030364103200cd01c610381c011140a0041c1000c40c448282c400d2908a60f40d014038a40b40c01c140c18004151000301d00f080d02d598140c80c0c032103039440440e61700d011602c070041e41114042e40b920500000340100107003028107864040301c1c042d071b0329182c0800c02010740c00151014a840341c420201e41507014051600440070490250507203294070b0b6250006800d6801030b40c004200200c159140810107940340c81114007400e0004110f1180141c1c40c0c030361642c1c0c0c3c00380c0da032014018180c4d00086031041d40e07100c14090040c14010010300403118286060044001ca51004484030360400d007000c912903000c2c030269500641d4032001136 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 445226384 1250 445225134 445225141
    0x307090b0711040906090204020c070501030c020102041a0f120c0a1b0308060409020a12050307020f01091a0c01110a050705060f01060c060504111002160e070816020106180c1403040b 80
    0x30003012003150444401c1d98400da9207006881d23078006011410100c41c080c0a0440c0742c0000901607485221040c41164070401c018441040c40142070107100c0700c080c0c8505c0d21001052400c1c000e510a100c0c040d83c49048580422480c565900d00a10801016980384458205181e107664030014404d000100494801d400040c660704040e4801090140000c041e0380015a562703004004100c00b58006503490b400020300101507040110003120300036000c4c42c20000b0246011940b083c510150891190500c100250444403c00250031800540c042028015a035000526010345540c0c084441204c06015010004010540d0b84d00c54a040302c50b503850fa00911102940d0728801460004d2003202d0801080c0a0811340783c4540c40c00454015080e0002c050f9290342c178a4a5041803115401421300400c05010005100d5100c500141c1000d2442c660034090301002a050b80504025001101c03020416001c2c5120802280c100040c2d49085444d004405003050303100c03c4451008071703405010000d035000071 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 445227634 1250 445226384 445226389
    0x10905060109150903030e0f060403120210110901180501120b0103290310051b03070c0b0c040611190f020105040e0c0306100c0302060403081f0b0307090b0711 70
    0x145500c128140b504103a1580c60381d090001d82c8100c0032608000501450082c010103401801d1038086280c125520740a00c0d0858000440350701c964040248000c2d00b080d10260118020016000ba03c400500b080c42540010b07101411260000c4140c0f90024441c800e20744040904800d1940030755506a485802502a503078006005d00088200d0300e040503951000f07019244200c9180303d8140d041c410a031107010203003000300342c6800c402100342801c040c41e10041c0003480e14035581c1100b04c0b550109035151a541d5400d0155401244c0e0040038180f08182001c001c034040a01c4000c0044d145c140c0c54a05003024482c080e82d40e1602245040e011000b000c0c0410400309499141141501d881494107a262a4450010400c1c08105482280704a0303808000d00c2030074900b000340c1c0201082d40d407030300700002d001a03100207507a060040c002400340152000440e448802c2c96060051501c2500c0249800c9035031143d20280c0399204441220009245c00030100d07124403094100e845464000c00b001c0d089652b44c004 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 445228884 1250 445227634 445227641
    0x9060117190615090605120f1902030f04060c1404180b030703030906231204080d020703020609010608061b030c09040f020d1109030318040e06090d0f14030109 70
    0x107010881036007510510a8000c1074001c000261100c400ba802c185148840c0181c04c0345040e820200611005003c0d158880300842c0d0b42c2035111071402d00300e48040e101c09800841c1300881c0212064841d00005c20080034500e00c108080c0190f00ca050f08215080d00c5c03031802c64610894031035080d5080c5017004208083d40c200006004528122080001c8422140e00024078040c10355004801182c07a00380104005078008842c003000c40111940118045000100100c051060020007400c00404101141c01d20800c0d4065508510340c2803000c554070840b90501a41c3d0b070200703c5102c1a250700700500800c3c101808903907140174001407548242078684203500542690001001203509060900081500d5619030040c1803a143c0c082d40016601c00d000324900e17040c0c80502e003041d11806800c01551340d16480c0041117418142040030102c0d41d60000400140151011a1151340e451140d0401d00000d00f9000c2200907c0400075110344150002041041d41d000e50007800c03001c18036005200404c480e0b5090740 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 445230134 1250 445228884 445228891
    0xc05130b1e01170a180302060405121305040f0f061706091203130f0b1017010c021e0c12010209010f0c020901030210180603151d0402042d051509060117 67
    0x9010540900c85903d400056071713500d8051380142e0021081c0300910034148403401d02d109110084510388a6840d0742d07a1007492251180324040c1e80c0e0b41003080c00c01c1503160f01c02418054112011301c00a682c81901c51070071040c409005030a8014000425629500004d600c810030511955040c00d5654001512183c040740510a4031220303080308017a80021100b419061160551010603d100c9050405100c00f00ea40752091100d0b1b41e2500c040f0302c0c40c690300081c6120b20005095107100e40340207244005800e200c405000c1a41190004c0c2005101000640107060804800c0e81d03940c1100034038241c111800b500d401006900540d40000500150900d081c480f885a2f680e428905800f48014140d02d24144c0300b540b0000001c2e84d500070a10206c1c031112001d000034500106400c000011441c4081c0c1c0c6400044c100a01c100d07903603185407040e0705401e1807220443c035810107500c00483c0c1402220b0040c10703003110300303c00c0c13002c5508800b1120703d09820000d01444040e5030f214074815020b10000d41001000c0c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 445231384 1250 445230134 445230151
    0x307022808070602060a0b041a12010f1a040b030313090507050c0f0109141501091a030a0506010602060a02070f0b0606091c02120a080d02070c05130b1e0117 69
    0x40c0c0c0840c90314400c005100040403583c0c0140aa86803d41e2804204d846080800d445242040548ca8884030b00170341900d0500c50031118000c107140c040754081d00420803512010801e81c140000d81100c00340341c08200320700c100251000d2000352004403c06490303100f00c0b80030401c202e52041051003165003503484030341d05c000c85041080c0750541c2e0680080c641440d80d0814400b5a44400c451010010780041d2030040f90740c0e00d002001c01980c001081388012205000d506001c03507850612003c508850f05080c048150b0190980301c1e501910f01b06a52140c009010740005882280f021601c03000882c03080b200340640040c6002d01c0441255030302e0700c1403840a814143e204000340444200b964616100d1000c2b0094401050210303040b500c1844407120080f000e41070181c00003001ca07004103c91000f200c03040c0d10581d03001641c50b10f95150808a000e95608074a401600c09501604c40120681c000340254100311801c6150480500d4407106c5002c054070712a00054001586c1030400640c401d01a8001146 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 445232634 1250 445231384 445231459
    0x60108160614040506030a02070c0603061409090c0a030b0106180302060f0901022107050105011505090d03110d09140f220e01020703090618030506070c02011205010f17030702 77
    0x40703d001805d50342054801c0c400c2142e0002d050000c0000804a0000034652420148002031411002c202101c030454520b40c0079800c00400035100c1c000512015500c0700e4002e2120310160380700d080c4005680408d004a1f000301ea010800c02a03607050b440c0e41c010445c1d0b0700405141c90075032480c1e4000d00c1a005800101e0540c030917015610450650141146480341020281d00c0c0c6a801c2801c200307080d03c0b01a488a030a100c18414555510f42d401750450b142000240d1b144a88901c00e80340485c1c1c014031420044c0700c640100d1099002d00340d8001d27101d100b1034100200300c0e880030818004200860502c105c0517548062003460400ca03480d0a1102441e0240220800150003c1c9403180c80d030982e401000c0450000b050070105000759130300700a400705691007400071006e030703e802e40d80c52070759955011700384030240103148840c1400c581c8100c2561154002428003030105503510505601050118003a507015802c0758000d40380013900000c02d403542d43c0e80040070503004c06400b0b1444011401441c0000504511 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 445233884 1250 445232634 445232639
    0xf0d1104050109021e040e04060e120d0605041113090518192a300b04050d03110904020c0111040e04030e0d47060306010816061404 58
    0x300c6200d0140240000e44000d81e882281180c51040d01c0d0490b4490184183c0c144000d1003030100101006500030303840040050388c070700040601881c103c1c1c0303040b0028099600140821514209412100480303206440c1885501c00101004000d400b0b078800c4c00800c542e00c040c04211185058001782c4e0400d06906100150019182d401404d107130100910715001c2099081c0b0300c042014401c41c0c408001c00164a05c2d42041d202d40703070720b610580325218403040c454101c9c1080034003d140d5480041074640c0030044800301b8485282400754205d04840a035194040c0c0f5a1240406010b4090700b0100201005190320306900207003000001c0d002100424039565940c0c0481100c03900d08030080000d00203111140759035260900c1d0003004034004c40c1c02c9600490721000b0020000d040b1a40141d024214056903a8000c20402e02100c0d92084445142042054066180c51012070141c00c0700c0c0901003d45c281c807240e0b0b80b202c488035901c01418405482c139180c4000c04008051154050042d148103918003e45811b6 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 445235134 1250 445233884 445233889
    0x5160b10050d0b1008030310030807020315011508160207091e1e0629071a070903060e03091c1718040b030c060a030207110d03050c06090604020f0d11 66
    0x49190000303d0b801060001888110510082c804000700000c1c03006520b545025801d00010001c80e00c001414007001140110840d42c0a004100c000400088492240d41e904ca22000343c0b2004481180b011901d044042036216105140c2000c1a45054000b030109528103000c000042a210100e10000801c0c898030003281c40b0640103060784030288241194400c042d0641d00c1c0100e43e1503901c401e00d1803a1240d80070015460042c06542d5070250154502d450f005203040940705007920034180c1e910402c2c110104843c16802c020704005890054004101c50701c5800c01003503980c850b400c07002c2d5019400c02ca130210744c0105101d0402021707114942903164180700b000b1003a1138ce0050803c1c2100c4003175104100350b40d4209441340b8449464114003c01c00041a00701003202c910a0001d000c04160b00081d080b418000e000c1140c5c002c3c14000780c0784a16010850a0085c8150881c46104165000b0030b0b0101d20030b1000043e07154091500140032200107480b4400b080f00e00c5400a104030b4040024420006055 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 445236384 1250 445235134 445235149
    0xa29060403210f110703080d09240c0804080d02030619141201020a090510111212010b0a090506030402040f051006030c021516020102040f0b0d0b0105160b1005 70
    0x14100c40c4442c840181040260600d500c00705181c0030000151200710f194180080d000084a41014503e9030319108690064080d00702840081d0400301d450074040c0149015818525128540f19030411000780c0520703046903594002d440180c5200d50920082c18610525401182c11042c010070094000400c990b4442c80c1005551103c039141e1080f5402030110304018030368a0200e06010000c5103080082a0044d0101e1a18010b40d40202056045556424051030b03040700c50703800e00c900700c0300e9068008800124a5004855080100c42610000a022004c030403c1d900c00c02c1c02915a092a54144001c2c070403a904010010781e8440e80303442220351154220302c1000c1c05001002d0010702c0306401c005002d004c1d10582940310301107501c100d007107105540d180303103010780c0042c0f602c0000d291940461504030301900440d0017a1080d119040d00028104901000501031f5100c924800c7c060f00301d00c0d00c01520700d8001e46440c800000c0b0000721602c00548003c410b29485410000d2141032641c586011800f603 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 445237634 1250 445236384 445236413
    0x190e0103061509021c0507020c03100218010e090a050c19020109051b24130b0a111203040209060a17010903020f0105040507031b1503140a29060403 65
    0x1250740d64106810007034401010785019000000c0103526100c2000f840030b103207420102e50701d141c843d564001f041020744203011500c02c182c002801c8640c0005030071156002507108101403840c402000d18182e6441d401014400c400c80b5005202340003540e60303901d10720081c0600501c58038285000308161122155142c0314491051031550000074a4501407031b00f1171034500125010032200180d400c0141603640c403d44201300c901640c00002142042e6110000403034050504816003c0941c0705010a03902e00e880f018000c200090758030540c80c41061074805440d00500c5c68411110042000081c0250038040700841c1c0040c40627207407000c2c0e1580c82212554200044005032513a0351a401e250082c558100194500c000c00300d4001c0189040983c1c076140c3d104440c0c403004003c180010f09209024110055420041a44002060040044083c01030050256040d2035240700b5210000c40c0c80c0105034420170380850006501a4102c10079664010401012071b505903038000d0080002000040464200004 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 445238884 1250 445237634 445237643
    0x61b0602040e06040f1a10110f0c27011a1e040906090212010501030c05070b09030a080c090a05040e28022e08040311060906040c06110a02190e0103 65
    0x2d828200100401c1e02e640d107201c1d500c001d007030488262681c4000d501014000c1c004442c0c120100403190400d40f400d880031240100c0a00854401d004403d1000c52160840002181ca0911a1028000745200441d207100d28036500380510005120070039000b03040351400c5003001d4096060030b0000d18000350320010445081d0740c0c40e50100707003000302d2486070140c11b000d815050810740c10030215010714540d200d014810f540c10507468588c11551280aa011201159000a02c83c1c00900c0c01880803960780e4400c11005000515550000348690f84c024191541d007070004204404080c5072800300009000c008100302ca0307502441181980301c182e614040660076032000780b0801c4941013801080510b00000300c4d0760401c01c44040300300820021002c0070202c040450b04120701303242c8843c10101c40c0e09800ca18000058451203050002144c40000d00c030788220b200d00003510055881c1e44007118451400c1c840541e00f94070040322500140b0309613441c0d051a0507000401d299403590b4072015080c0c06421f0340241da = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 445240134 1250 445238884 445238909
    0x80c040e09011a030f0604080906040e04110f040b0306060f040609020a030605030c0a0303051b1603140106090c1407150c0f03050a02090d020d0c050603161e09061b060204 75
    0x804201c20741d07503c201e22050841c00b0f0060460281140c070b46591008000908075500003d5a540640d5100240c4002d00040c0710000e545113013500e410441d428012040e0340c032582c0c0c0115a42d416251600a01d0008500a000b0b0289a01d410f01480405224100240d40c07150300e035000442c0c5205a0320141c2010b10b000c0c0da011135441e00d0300c02071505044400c4000c0340106070070300c1e05202183c0c000d4211024455010b8440047c40d181e40b211608241d02d03158051a02c440048c07000003884070741c101c6003440c443d080c0020888644d031040101c0454108a4141000c00d03843d5843e03248092141010344a40c5000b078403401b511540707525098046a0b00350384074002040003414000c18103541403086582c00002c0040861414800c400010040c0c0300341000203203e001c180440e8010000840340080042001820494803403c05400f4000849079200a001c0003c601d054060081101022400c80003413164603102c0e50036042510803240130840d9040d1810f101944e441d03040018101c1d03c01080206045c071000d9 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 445241384 1250 445240134 445240151
    0x1f03030804060e0d02011e050405060f0417041d090109051c02010608010c08010e011401200309150c1504210c0807031d01020604120e0102070e190c14070201080c040e0901 75
    0x2080d013401f00c201c10304201498402000001840041e44680114011744900180e0b5543d1078411424911808a442c0e818004140064a03102d442c0860555851074a2114019590600802e08903206524064190350041c030001e5032400c0c5190458048408510021501c10b448900d05420340720b104240c07a00160344080102300103600c940034903000d001c8500c4500d090702c03800f03000200300351081c1443e00d4601044410304040b9040400c00c483e8180000340c18444500705441002640b500132a0540001d40203c034034a04045207152841885994400d46c40800583c40180c41e144040c004c0074010b0611416101001c0841d61a0000c2c1451034800d5881c4026442c0d20902c2c80700c03e0520007241d0741550f0001c411f0000103189010a80340c04200d91922008158520f80100d152900540c89540d42d49085400d10413141c1c0c802c444480340480e07226040c0000c614039801122a03182c0095022035040041c84044e0056116020a48d0081c850f034031000d0800f03803149415100700a082e15040c025a5403007021 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 445242634 1250 445241384 445241411
    0x130807030201032a0f050403140f1c02150a0b060d0f0b121c03020405040c11010c02030f03011206020405090903030f06030705100806060c030a171f03030804060e0d0201 74
    0x103025181460b49a002d000406074940b09842965054000c000c0c4101403a05c910001d124209590040d9003100c1d6840f580414030901c00c1d1201c00c0e04c088440c5074000c12a03a48609520030100f175a03028025802010b8400301e402c0703140071000026100102e0b0540343ea00e40b01e182d54940c80603110b05003804600080c07002c108080340c0f08444803902c003180544a80740400c906100042180d8051500d03c0707284e41e13441c45d12800d00710024843c0d03070880c55000d4540910125265803080409122884c00b000030404082c94607820707a540e000d0441d410810150030001072160035882800038203914481c183c0942455294400900702d01c6080f201804c190780003008001200b11600e00c4150030810035005803164504040110303805c0f020802c011024000398002103021a11020304485a00f40300b8015039480300800a8000c0070f59010858a821850050000c5404600c44039003c000c404040c45d81c81005514595080d00c070420018070583d4581e07518080220203d2080c0001601400c26500000d04c60f140f01a2 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 445243884 1250 445242634 445242641
    0x612040c14090601123b16051f02030f0f030f1806060d03021606020f060106030e0c04051504090b2a121305011a0114161713080703020103 61
    0x81c0140305098400c00e02816036000ba0842c0303e0440082e41c00b00b207418101c40707584500090034516003406d000c074103c4102030040040143e840280404c080d03583c05101049011000c5e80103000b00ca0703000c2031086501c1c0c030f980350484041444410900540781000d600f5907001c090307a001041c40e01032001c2c00204024444480c0d0602d16840402c140c06c1036000158600c5155850000801d00341c052a0350030101d2052600070000c50004a0050b885280c4242e1110802900c801c00c80c03050381c11508c1003c00202e041c40c004c0c0600d0700c0c80940e01c07005044214402c000c00000d45400350440703140144050703250445440c4c80c05070040480c05010321840d0b6040c82e08400910649502c18100c2c18400100000d115000f00012110700196410424503282c54003c03810030320100980c0010300d207610b003540200340542d407018084101e40090700c1d42582c1a070701d4400207000e880b47c40040c05101d08050310701400101e11210a00c00689034020042c10600b5025040390400300c0b40c1c1240c401a44101400c00c115a814003 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 445245134 1250 445243884 445243919
    0x5160302130213060e030127030807080702100f0b06270316050927010614010503071707030f02070c0e06041116021302160c0608100b07020612040c 65
    0xc0046261108450f0b14000d40d040a014010400094074110f500554003504a0744540c040c45000b184658080c622114221480080840c045140c200000c3d0600e8001c290581c0708070321039005000041c50030341c42c14008148503001080d9455840c048008a6154040600543e22030195403015408210554104c51406c0348003c41c801d43c400c074404d0035188450080d420456400780d51a44036910381a140305030301103151919070841120000f0244a40350150401d10480b01040c140c1141d0201ca040110b520b441300316000c42c0454180c842c0517000d800b5042c1e030164400018500007540d14103d01c070007030580c1c1c08a0815543d8000142c814840300070120101c907001041111304125041d0750042c00c0c0702e18010a000c4502c2210030350140d8040d51600b000c048003000216004641c1c1c0c50a61154400410088105840000f0004e0b400b040f01070107034a40902803e113190340000928a010908491035019200480c0c010100307121550301561651405801648034403c4400c84500b040c0c20b00d040703036072401e = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 445246384 1250 445245134 445245169
    0xc0f1203080c0f04031e080310140a06080610020c1c03020c030a0f14070306020d0c1704030203030105150d061706130c09050a0e0d030204060f0302090312130305160302 74
    0x204199060b205040f000c903811a544480d000f800d50300c003130700c00050442c4401c0303011786010340000c100500345502407802c03402d4032202e100801c9442100e00920000b00124000c3c100400c0520020500e03600c0c081d400b0804074501481120084042c510200b00088402d19624040c821200031140030550180043c056900c429001030217806d000c1d03203451410b01e0120303501900b00441c00c43c40a824070024400c00c005150400d0080d036580148135482030041804050300d80000341400d801074007414401c81400d0280781c050f8010350840c3d0a010401100c0036000b104c02e14100b0080245070851000707400303050010300079100d48000423440b2900f060300f013500003084405040d40d40d085410000e1704000d00c1c0d4041c1c500c905000100f960301c40b04007500030302c510012186e17517220784420189622b51540042041c0d5070940da4501c4100c0e01c03c0740583c01d070300400c2015540b54002041800030300720944040c1c42008030106442c01a1070352900c4683c200b01c10101c042c1350009004a080c410b600780040b400f29003d0701c2 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 445247634 1250 445246384 445246387
    0x30e0d080411090414010c0f030e06040b042409050c032e11041d070207090b030304031e0210020a0524130204110408011e0203071b0c0f1203080c 64
    0xd03034540c0b0032000d540381c00c24829a80f480103d41841781400f48140505241c1c402009044898900a0064003000700c00100080c1003c40d2910854400f259940c01107034004001d440342d80b0759594690024400c4201d9111160301030740072100040362809500c00060090018210444a01c001d160034109114032030403074000007004101c915042890411a0200080b00c0051780e90070700043c41c1002e1107503910000740002d410701032500c412805101e4602a40700c07a021950250f0707a54142c4800d0300c0c00d40d5240e0341d1540082c003041021521000c508010400d1441d402c02d45481654001501d14501d420b40b0801680f00c2040325040000400690b4542c0304004100140081940010004054000e0002c407e8041040c0c0c490210340396500001006c00880f50019190340d1100441e41c000c044840f00d000d00c0500401036980060f03c2403080340d010710a560b403588000c0900101000341032442a04c00c42d0000c801490015000c54048041000752a1145840340d68504504004144207000391035103148000 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 445248884 1250 445247634 445247641
    0x27040507020601031203090203070512030c160b0a27170c01181401021507030c0305060d3c0804081614010e0301020c0d050c1606050409020304140d030e0d08 69
    0x1d00541c0c2c0c1031503183d4036020135011890b00c0400c1c100b03034062f4840c076000019942040d00d4554088040c000d03400b403110440b1101c540c10b15070010404024880c20403004d0041112074515842440b40b150140400c680304010185408151207414645034008080660000411007055009100078a030440c0c0134a40801c100021010201c1050800d105441024074079195590540c1d000b40000c0b040c00c28010398405180c6004038018000d13005401c41c1da000240340c00f0000d65145040041c009542e900702561050310000c10500312544120701c40040038050401c10b00007281003580302c0c1054424480c149003620b40b482d164a40e454020290b00c4018a0940e0358024400c142d503503d00ba4011390300920348110030422800201e40248142c103010742c0c1c103000b4038003802a8150041e004006c02d140c940c08448900024070501e0790244c00c40c0c02080006102000200300b5114a500a150400d000c1c1180c0e00d59a48042802441c1c2003010b14030002090701c40c0d20f80a0208070030700a10320f8845071811f008a41e8035 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 445250134 1250 445248884 445248893
    0x12110c0d02300d0b030d02061e0f040605070c0c150906030e2107050a050a0515010602060601140c0a051006050a0b0d1d0601080a0c1a03160201022704050702060103 72
    0x440d0081d014640c102e0100d540d402c0700d5a40d03001200080307406015140504000130009445a508442c3c5210302c0d0712440b40d074800440c1820419200380c0f408901c81800f80c0f51aa180405000301030328003000c025803400c0000201e078480700000018007140c0c3e4404e00351800e600018052400d40c0e44203906051030101d4141007120007049802050300c9800160507101111511102c460003100c101814512035000d1141c208200040c8001c400343c010002c46903880421140c2010343d0f5000d000d0f00740107070041c01c04240554001c0071250716503009000000d040400c82e5240601d88200c00d00f042d03849070b005c80c811003140101440f130358010b001b045d0b880c0c2500741c1c140946150988075917660706429617a0b4030f0102088250102000b082500ca9106444480d65220991030b034482d9090410344d00782c00d04080004149a038080003509901d02c00d14500e042d65540c01a0741540705000b8880001d554080100c5e1020300c2d000c0c80b2a41c1c190714081010240300c0c0d061414030003210401880c400640d48104010300108 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 445251384 1250 445250134 445250203
    0xd06140112050417070b0108120310120c1206020d0b0312040b180604060f0e0406150e18012c060f06070f0605010306050603100504080a12110c0d02 65
    0x115464402044a4031103250280e00c00c4d0340c8044c401400c4030080303075600c200302d04908054103e41e0030700300f2190108083d4454030030620003560740e0240030300c071503208015402000840c1d0038100c3c0207402c428501556901240707010700c00d41804880d4640e00040810310815075220700d65469000b600180b0f81140800d01e200c06621840c02605180500401d500b00400c0ca030254085001d8005064261142c0c0d803040003820001400490201080300c1c90004251410148207140c21100040704c59144884144400d80d0030100d030300105500903130104103800303440340024a000d0082480c0400110f8000240020100d039030240828109046a5041480165030380c1d0311400d6107140045419580d165400d1801c001e03400c410000040807682010000000d1018a80c001c40c070a0780c00340c0c00c0ea620b80b100c1172040812110103c0b4000c290380c00503c5045c4403140300740d1801d0000c90000000251410032000b5400041e001b40034140c18a03440320082c000c800e6030500010b0300150107822124440c07082a900c0703000b0f4 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 445252634 1250 445251384 445251407
    0x206010e070e0a0b070803060307120c051201020904091101020c03060123030f060106030c110d020a080c0c03121306050c0a080703120c0e0a0b07020f0d03030e060106050d061401 78
    0x801c0400110030b2510b40d00c80c0030b800b004000000348660f864100340303400c0941d900100c610b90b22074000c6844c0002c0d554180d101da052195442030384040d2960800c800c22503540200865010a5036084c01b4180c0d00e6100e5102d03000525000340400041d00780b010000900e0300445010b218020f800c0301c40100035400000b0211542d0001c0c0035180c03500315030401d001c246070000c0e03c07020901510690303000007111900340e4441c0c80400700300e980760310b44021040300007a0b866002c0c521410060307001540e424049907074100070f444080c20100580e51514101da000900c3c101402d42c40c8411503100241e200c00c1d01100c003c0b003000603c0142071281c2403407941c550080c1c603003840c5170303010701000d0340047c0180030984034100d100d01020404504018408800000400d125002082940111a20480820220318181c01c1e581210382c010103800201e86090300344000c07490818002c070706240e00c6101e005000681030240e10f001e0500d47c3c0d02d058803107580344d203680180c03030155216581c2c100640c50201007903640060050320 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 445253884 1250 445252634 445252637
    0x7020a0e070c020603150901090207020d0f0c05042a0201050907030b040f15090201090503010b060a2303010611060f13060207050f01020c0a1109010e130503120a05160206010e07 78
    0x56503400416901161031090003913002400104000540c22030390300035410f80130151107200301c03681c0b503803050300885c4110f0300041c4d400f91514404000085078001c00c00c41e010310640088542c6513450020406a85140c3d5040420740b00707451444030740d555800d034209900c401038402405981401280651110704d03a00014104840042c000740c1070110007c1c0841500742d10684803503003070b4003034001c0000401a8140c220300081c100040000d540c03805024409031500010100d5180007895042654080e0f9114400700001140b000001c504880c40c602850017440305491b4001407050b800400381c1003000081c907982006680c0700a120800348110386228440f40e1244c070050b07544100d81004c52526455448910b0b0540c0005011114010041012200184150902544111445c00300040c03814240142d140004446000811a05104115003a018012002d0340c0c601312407800c01e100700000c01c45030a06155291400e0101d00101c1446001d20ba0b00244064640c650608107222101e0700081c24100 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 445255134 1250 445253884 445253909
    0x1b0d0b01062003210a05190e0f0f010501061202071718041a120303160c0c031a180a0506160912060e2a01180302090a050a0f0207020a 59
    0x411401c110555144040310443e500d9904881035070030408620010540c80400b01030100c1c0c00100c5c5805154010341c01103460b5912000a41c680e100100903d1040030114481d100c00208800c0c4107102d000c000040c1440080390540c101b0300c003d816402600000100d0900c100034600c003080038140c240f00780b211700e1920350396215002e0300440703550b010840900d0ba11903d01440e204a148808401e87da0201054031146560707805000203988074002100c011074400501d0f0064410b107403192400c269a64400e50140741e0b001e8a171788405010076075403c8015200007030034080c84014061444040c210354500001021034002c143e075090340340d090103880c94000701c0c4141b0600c80640d0007601541c020f132000c443c881482e104d1780d0800002610118901424a0003502000c1451144140c0035041c9001c1c40307800405803081c1c04004685290302800040001c046a030b40c080016500c03a62406e0041c42c6544012490741802002142181d62240741c120300103204020341c00050701c07070b0100d51045450300f56018 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 445256384 1250 445255134 445255157
    0x5040315020c030307030c031104060801030b1003230114040f060b1c05100c020c091602010b120109060501060e010e1504080a1505060102032107030e0f1b0d0b0106 72
    0x2034080c074900c030100b600001c81006600342c1c0c1907101e400030060650f000c1c4103e80205104140a225034050710300041c000e5801800030460180400350030202605405080564035181c0c8014195110100102070041a403000e0f212402400f800300844008011031516007401c0e6a8107080c291003001c01058103803a490092625a9810b8400d0620b06401c2d0341c010035819a03180075920703007041030504031800745440b004000082c030008050a030b245000e442c1e01a141c858500316075a4168100824045640b581c2045003070b52207607003540d03400052803800030490345082d1800034240d5405800010030050184402c03d0142e034090b442840e0301809a41d402c00580701551040c0c0316210355001201c05201d00c0e905003007006803070007160074044060001005180c660900490f08c0e40714642040070002d10880d68000b00010b0514610342000103410b001509070091500542015154442000190800c59201c05850400b8041c2c103000901250140542003082c1c0d01c2c5055404180034132420004d58910f103 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 445257634 1250 445256384 445256423
    0xe0703050f0a0527031e03070f1202091e0907020f1f0b18090708010509100b0d0c0e100f1a0f040b04120c0803030405370614060d03050403 61
    0x5a00584040c1082e1034108104401c020303590307031b0084401c1c0c00b50001701e000108080c0410070035a40280025a01e184100c44180c00454501801107000180741e90b00b08841c0301c03280d50b102c0d0714640204841d07164040248028042100e4004014044019500014280c402030880420b1010280156041d002d00ca5580000480c0041c680c03c8055500900c1d1042d4170849024040405441540014101c480b4280c665951600380c83e01564046915842492580031001080e00300351545074024054020307150301c80d01e409001603a268840c40040304c5c1842440140040d5140010140803802c8282240928280d00302600c0c04400407901c5403881c0c08980c010102c003d0100700c1d0700409540034000d44841d11200c51000b40c8a0080045803500248030f000582043e01005680c401c940001c05230a0144140c01141182070004080f00c040010500741038a0182449024119141c001c00c4000b4034400c03455403d91442201030005441501012045000207600200312003da030b07070007810020b04080c0c00d4036 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 445258884 1250 445257634 445257661
    0x70c080c030408030310080c0d120e060d02070b04030206060d0c03020409080f07080408071208070b07020f0a14010c05130b0d021303061e0b060a11030d050f010e0703050f0a05 77
    0xd00f0580000010f0108841c400c25050007613803141030603507000c5074054081181d00207071100000c022411528082c41d07a940a400d00b110215000b80c01d0300e2925081401e1003041340d021301c6046072260010801d01051550400010340d000500742c80c641d20b00c07059500c840000c0389803407000a21803515000340108100000b025541d50780760410229807035540524200d44a40c00501070480d1070b02caa10b5000070006c0e22003407010320703441c0c00040c1c55250090503260810742e52001840300e01036214207080040d00c201c040140c01c80d114080d5441190200c0840402d03400c1d85c0c22500110200802800030101d078807050805841241d062600d15686d61810071410720190240e184000d00d1203c036000000140407254004000c0c2e100401400a10011820810002c4a0403e0200d541200d020312502018602450540401c01110b4080302c1c103040d134a200900c2914011900d04081100c000d0041110410101c00d0301d0700806d0900702405107162001d50081ba00b50018169110651102c0200e401c0707208008 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 445260134 1250 445258884 445258889
    0x15030b330f06040906080723010c0204090f02060307120f0b03150703091203020301090f0e0705010f050f0304051f0203250513060801050a051206010b0913050406050402011205070c080c0304 83
    0x110510501b40e441c11129101c2e0002c1c800d030580b1203562490040c440c4412070141e0101c00d0141c441c08124105038090200420b80c0e2681202c500e480d4031407480250391442c024611a422030307030b04e042c00440850459404d8484206568489500340502c0c5c0f2003a1f5000f00342180c0318900302c034410b1fa03240d42d0341600b01c024046402c80540700d89030240305c031800d0692580065059442c000801c6c400140b9400303500040750880c414142c0250003401d014059988204070505210f0b01c9860044e046c45d030100a10006503209650843e01d650200b1200910345e25041c0c0b1041d0304052002c1d085045180c104c000b8012a2202d0f840e1403008899150f4800c0c60307034000c0080c0c50055044100200212741c407028090540242030050910035031700c5081c00a000c0c81d0128048074810300d0307840500507691804086102d107802a0740e03031a62140703c1644000c44580144102c074403841c040d000c0410729007014000513100422081e07407401514142400c00c5070f05d90704003c01214045c0d003e01c0455894550441640c00c60103140c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 445261384 1250 445260134 445260149
    0x6042705010306020304030e010206040f06050c0c06180118080301050d03090801050a050f09120708031302100f090504060803090f1504060e19031205030a15030b330f0604 75
    0x40c00202c03d000c0c03d40d0255110f584a07444441009203400c00690740c0f000f040f0360007403203c4800c914540c009a034580183e5080103484500700e0034500d48a100354100fa1040f20010b030400c1000003011400340742401080c1d08151b48510b241100c8400d91150405032005006e920b02611070064060109845200b03a44001e15100000b0030150404403900c2e0043d0109480400410b140d01c0302050b0b0009000c43c410851040040d070261402c1c0e150b80d0303504d40d16040202200c81c0040080d1401e0f0151721000c82c0e940c50500140e0394000c3c00b01002001801110311500b1007800b07a0304d80101070085907000801c6898040e4200c0d01c802d1032210880008120761001005400050400701d000038415400c03400c1c1e00304e00c8000721010030590b55030403580c0415800340e02c00541031905100e0078000ea00d025100460308202c40307803c042250314803071342480c0c0c002c0040e41c41262a10101c204012848121841d200501d15082c0c0040030305c8401c5811082c40c41c070080940ca0310030030320140c0c65440c03960f40408a034001c0046 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 445262634 1250 445261384 445261391
    0xc0f0f09060703050304020f03011a0d020a0506070507150503010609050105070510150501030f02071a0907050d1a0601031509020f0c0a0606060f020f0a0308090312090705120309060427 81
    0xc1c98004c1850308107039400ca000740441c005852203480d0601036500100a50b60029a42024840030411540740005050f0b800c0345901a011038070b074072070350002c0014501810007040d80307d142c4034011800c0140a1540d1040100900c01885404d52083c01002250303002d2070070689880b5035003000c44c2031265005c4150f9110b86041d107540701803991460300b2030403500e003620100315804000010f602a84540007009160090f0441900c141c104011001908000340c90111154103855401107610080308810607260800301310f1050080c0102440b1240e03010f8001c0c43c06110842ea0040c1c45240c0010310302071504050380205140202c0c500315001d4070521b440e01008c94804481030b00300b810040c007850182100040c400e00700500034500016050014000041c01421088019101101d2001c006001d00c0d429000410110410f5001c40c00b030f0764040c80340b42000d8a0028542001c003c8030010301132040b59a90003c1c440c44060f90b84801c255011511224604807e6021034140c06020346000311f15a10b64038030b03 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 445263884 1250 445262634 445262647
    0x20a0c05090c0c011b11010b060702040905150910050c2b0f110c0d08010f030b06010309151517070e0603070b0a030906050114091302060c0d0c0501140c0f0f0906 71
    0x480c00200421704000d5191040040b411000300f60130780c0c850450060304504104040001400c07c1c1d448240303014014025034843c400c215880e0400100245c41c4910b4690140c2042c411004461094a40001488c80401c2c6040316549a4202c1c1c00c1d110894070b01e9020300c003000c200040c0350740c0c1c10450f8078003180941001500202000c030521600044854800344c40b400d00b041c04118021291607040c2d441c19181030b8052480c6030b0744c44c102810018006410540c6500c107100001c1c1d1244181070400040c410081b03103c85038505202c0006034154051542015507402c80710a1070004a008001d450702945a00c1450340c03002e000c42e01c0d08015031b1110000c1240091141c4165a160b0710440ca1644201e0040c44942d80e43c1041c1c84226094056503680304040b040800c284004001c1990303041840a07004905180105500300e041c1803c4001c04804103801402c800204642031241d42c0070348402e418118014181100045054098034914032018100000c070200c25400540030f9450001d401040e981da1042c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 445265134 1250 445263884 445263911
    0x50f010c170c0a1403070c09050a02071e02031b010f11120a08010f1a12190213080609030a0f0809070906060e01020c010e032d030408061006020a0c05090c0c01 70
    0x10650783d040d80c4041c0500880c12030408040201ca50303898210a45e00d41392420a03003030000800b030250451080310f80c20000c00000405402402c4100b204401d07001440c02c0c143c1c010315041070300c2644944c0c07c3c00140da088454680c2c200202c503508940760701c0c0c1010401142d40c051481c00000c075030203802e0351070045a0480c42c9a440144141690110b1001c0f803c07803a99520701c003041c80f12040070740b02694001e2000080040760690706992001c24881410400c60310411603904030b9001401e0340c45070904541c001d04c03c0b8081046003d801c15580002949020000d008c020002c50551004070108101036020401d054400c00c0b04801403c0c0041c1c040140b140d4414029080254500d815405801086022181076002c0d1042195914014020b00481010120890000905420440c0010b5050007144416003c20000340c000360882400902003814900030711003100010307074029001c551098682c1400a0711000018040301c1085c0c2e0390010365203a084205050b80076981a000d42503103440c080b98000c4 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 445266384 1250 445265134 445265143
    0x60e040609050f0604052a04110901092c0603030d05090a0309080318060a030906050a0204050a12030c060513050a120305010f0608150105210f060901050f010c170c 72
    0x340d01c50b034215001c030310b9004a001e0f01c0e2042114003030501c0d04054444c08800811260031484001c030132204428420307c60700000d00712424207011000032040070038041c41e1540c101c020900030b0b00d5003402c035101c00012616111440d0b50100c215403081410400800d03000d44041007900c0410075110f400307003c0c51800c49004c1d80d40b00203045007079000560140c000186620088121212050b04c00003541801050600f17106540c1c1c440ea285070205036070f4845c020081801072117200c0c040c0400c44805079845152600700842800d80d600442c101130151540c0e9000a0b0308080d00c583c0c181d81c06400822650b0311441c1c044810000311001401c00d000f03c884800030080900754142016000c0c0d14208407598072904492001101400380e100402c02107004210304004403070744c041003003005250803803a10401301c2101c0d5144280160f6a10180600d80c1031201c1a00e8400703003181d12034010b07251101d180d0714120006243c940910445810710032520070f030009101340d26040e00c42d9031042c04041030b900d8184110f0346558 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 445267634 1250 445266384 445266401
    0x12040302070b12070305191a03060703140f06010c0f1101030c0206070c08070206040801110a020d02010b1c1115070302060f041122110409051b040902090103060e0406 73
    0x6008240c0d000c502d000c1800c00f500d019900b900300711425595041c00c160000c000c0a480d600148804030065007041d43c05001e00301040e1111144036501ea01c51405041c80e10002400d02414541440303040d01d84101c441c013805910040007444041683c0b00d2a0041c0e645062504000d0201000820300109101c034014100c1e905001c00c0c1d0301000754407aa400101d8a80c2d50980e00f840026810103080d501040c0148003a0100c140020565071a0643d521209421a42d80040c3c0a443e1007010810706826601405020428103060000b4800d180001d00061a07000a0864006424600c0d0450f034050100b460102968010040c00d0345004800c900c04e901a00d800155045005114540014054515040a20380129808292103040700e400d0310412050b400351211b4241028003603007003103070070708010701070360400b408800c480c03644d02d41c1400503007415035000030321150813200c0510306d10074a024500200e9007200ca52080050700c5091000c012005800c590713008204440c5207405200c02d01519501c00440c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 445268884 1250 445267634 445267637
    0x9060e07030506101112071a0718051c1403180f13051306090f02130b030a080a02070503030d050117060103170d1107030807021b0609061806120403 65
    0x1040d550020101c090355412103200b0380042d003800490320014081e562800315803500303505035402610400640815600701c1c032403c1d40d4840781c0d0b0800750201090b15000c1900301c03039146005178190752440700300e103104007452080714003500e1091a007a0240c2181820985100e82c005081c079014500c0d07840a50f1b40b0342098507079820034040740040700c1b0756142c01501080240e0000e40110b0002c0144142503000741401445680e12480c00c1ca81d403c0000d45030b11541396420f01c1507801d4a0101000c3c01400302c0840c0d8080e404455a1509141405a540c001184210311794482c41e00c0d0341e2410f400808030b081082c641e00464151102240040710500180c02c1241a1a851511500c50300c0404101c1a52240d00707200140c50391640038010f2201c0d00b450390040180704402100420200f048203a00e0040368400002900003039003103002d000865505202c000c1101070b0750300d46421100d4604000039030a01c5076140651050304002501101004c140d103001c2e868510081c4100d840e5072107502c03403220423a41124101d0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 445270134 1250 445268884 445268909
    0xd02182410023403030309030201050a050402011e02030c01020d0504120306050a121a010603020702040b01180e1504020307170a060b0706020d1d030405010e15030714040f0906 77
    0x10090304140103640d02000e600e42c01004030819185602c0e140442c40b4446000d0a540300c104010401d003200c000000441c0310f59400154000d00c3e080083c2100c1c8042d082e041260304000c00c0c0b00161384c1c8100801c010700d1440009408984951b181603245214006507a481540089506480e102c02640041e204a006185954803918103050031000ca40450040030f038020faa42d0424003c80c0205103411042d01e102d02003000b0701c0205174402448009099201c41c0029400181140c210b04260040302d04610302824003082c14448040e0403c1c1082c154020400045851070002e468100c03040002c820410024000b15075a003024070700104088589040e00441e0070b0400041415125640302d480304443c07440401d1ba00b04012555a0b4029611220101e410395480701c05400040c600c08042e5400c1840300b800640d0758500c1c0c10b00141021100c41d602500c14240c0144001000740004101e0341e010700f051401405881d0b503003140500e980119006020081d4940348041401d102e2980302c5000d070780f081311601c0c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 445271384 1250 445270134 445270201
    0xe160509040506220807060606181a0c010b0a1221050a050f07171305030a02060318280605160f0e0402040504050412030e1207020d0218 60
    0x100c0340c42410303034009242d0390001000845840000b10882c8819840304010782c00d41d40c2c0e54071141c01a03004500150740c200e54070070082022581041148804407400d01c0c00080e81e614140c3d81108800c00042000070a400000b9103140b1020203600809075030780010150302e189501c420450403c0488102d0480f5070400c00b0207114800c0c46400b90071448011990707141450402c8801d4119026000784601d010120310071b010707040c00280d0b003101c44404c00c2a000c00050325000b030f03c180946081307615840340d40a908554050030158642000312503002c02c552910743d1019003880034240c60f10020501c03a00b51408940e2454902c400c8036959041424040c20040c451074a45010001e10701c1003035440031020522450607116024001d0212852280009000504041c3d031100841c0982e80c6c1101c04079078100c1c0e406a141c2e000e0360107104020868800300c000b0420f403034101d07404000da48a092001381c0f044400042e00e0b000c55903100b55080c03107241803420059441c2041e100c114518681243c6840f00100c442c51003 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 445272634 1250 445271384 445271389
    0x100b0403060f0507051e0f07050d08040510020f0726030a05150a180c030e0106030807051b0a0b090a050d0605060a0510090303050d0f0903051c110a110a05010e1605 72
    0x25a2229844024141c1c21000e16401002055020a007c0030b400b100901610f00824028414400101003d40310843e1901d05482c016081071160a00006414414090624540b00d840140e989999011800000e90012001816036400e03900100f100c1c601000410031071b0381c00c1550003460003048403007640103191004c2d600700712600d2128000d051024146198416004599801090302449036090006241c0e00707000e070360360940d03189820903074200d88000f60b00020800100106502ca404080100e9643d008180004403502c25521070000c8451b404075090300300782d8444040704001c2c4802081528048450b21304107018180482c2c0704c0344928100c1800140c5130418182e00540814165549542107041d517a00f41d43c160040f0405622080d50780701d4415403440188036006505000707464954032600400c00004601c914020350b900c209041002c444648201401900e0001500c1e05000700000902400207285c400c0c0e11101901395800d00b82c024014480200303120050502419884200300d880700103 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 445273884 1250 445272634 445272637
    0x9040b0f03121e04030b150f10020d080901050106051c140a0b030f0a02220902090c03040b01060201110406030507021f05090c010c0213051f0b0301050f1017100b0403060f050705 78
    0x3002d440498841b00154844045039400c000f2100014840d40d5100e48c29004211065200e14903100941d00001b5450006500710807107a0f171200040c40240aa5814160006c1c2a070140c2200e00201c075807213080341a94001240c2082d10049002c0c0d07194100c1e45044404d5001070040505001d001e800f1b40e0300c2410b00442d012501c107103890340240030626244003141c4400741150300100d00c1000d0359581c806180040c2d850000082c05401d11480f02c98a9092604142c0307500071040c3d000c0303000e42e8500340201810011150942d4110345031400c00191a035500403080e4103090f1001c0d403c041d09440c2820311003c4c410540d101900410303e090484d800c0b070f900e00005581d078040c0110081d40c000000c0030030b00003041e013640025600016503505681c00d1460400c40240102d0340303810001a024001c0b0040c4964100a80c41501e410742c212010854002e103150085e0483e01ca030b003004000d280404000640070082410014000c0c400c0b280050b6840780e0300d085c2200242142c0040050070740c06c0c50042190703140701d01c0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 445275134 1250 445273884 445273889
    0x504111801141c14010c09120b0628120201030605101205040812040c0f09110d0e0c0603071716080703051807120b13050706211811060c0309040b0f03121e04 69
    0x12780c4e10b207480e02d000b081400c10440c1d02c00e26242c584142071040300d4414102190041c0f5902c02e412200c02036600c0058207465640d0052401200004d420000d02e540c07001e512600440f407104001203a8aa85c01c1c20505845140b400b42c0b9845c01740d2080c0010080318000342811154826495204107484004107015140c04018040c5940e4080c05010a01841079005a40c8952480203e800200b14040403d206400858816001c203407100701251030b0b120951072413640400d03951047d07459105140c0340034100d41c802500950030165680000340c48011011680450070202c0412520183e9035031001c0000c00340303202e000b2281100040e012508400e2060213180340a82d005000c2c0c101740e41049001c5072074200c050241e030f040510b038001c07200c80a81d542c403402c403541141880d2240350b1400e40c148180911242c243c600c3c0180004c10000564180c08070688100b160210b50104500c010600000c490001c4005a00c0c1d041c026040c11900403d20314009000d039a02c00009851012840403218500c1d01491 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 445276384 1250 445275134 445275143
    0x30a0905010e0301060f260303041703040f0209010902280903080705011503060501141012150801020c010204060f030c050a0c150504111801141c14010c0912 69
    0x806062155600070700d4031009a21010780001034840c1d0b107255001071050186d00610640e400f8049501913513000c400d00382107021884008500e90f080595401c60912055100413070402808030201d020811142040b203003441c0c00030201c0d20b280d611601031000039031014a078100b40d000b5181e07404000d8480e10310401e14141803900d5a50110380307151a0300d6040e5001a200f12000d550392903003a4400312042c00aa0b0246004840010b020360400d00319800c00f0209040c003a114403460b0480b00c9076103034010203101c80e942118002280540c0f05105400030554150030500a6500125004140d410305501820490303400b0380d990034010721400d005500301c508070900e24000500800103480100c2c0103104900c089032107040203203500d04501c039070700044075019102181c3c4011501e4407001c0b1464628802910050001c4140155515008005049030300842d0802d01170625000640880882008400c00041e00b007070f100d0782407900c04800c1f28000d0210103144000305c0c0b0051000f01e2440b42d41d40d4041d14040d0b10 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 445277634 1250 445276384 445276397
    0x120b09011208040801050a0b100206040209180a020607050c0a0501080702030406050310120f150b030316030e06030f0106021501080c09090115030b0f090f0714240c0f030a 75
    0x9020001c0340700d204680e410349001400304400201c00900740304042c4039103092200012400094006c00c00085010300b0500d045500070f109120140c4d5640e9100b0b5000048600c1101d9400100321040c0c0c2083c0706c010010b584940c0c08200340c000c1c0007000c1558014590104d0399a1107982d251001540c44101c00e9a600006034428017003840f5040c0030364019500903035034105401ca107555650003899440c0b044241111507132081c0060301c0801c0030180082c041c50b0f11440e400d000312840c00d0f01082e0b581c001d05031002504107502211900303050050408022070800503041c2503a91808124a08403e4428450728005204c0c921440f5140320040100c64181c80c580d001810200400000300102d44401a10500d043e56903901002e02d0300643e2502480198403503a00c10000d46070035680c0f484483d40090401d5402d80003004910050100440c454003610191000c48108050b0f10010880310307079004020801e000d100c00fa01000c031740f004102410b00320190341d04407600b00401d0740c4804c1c1c49015a03018100400c10 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 445278884 1250 445277634 445277639
    0x4030510020304051c05120c03070509060d11031806060d1e0c26100b060a050a050f0f22361b14040303080402010e0409050d030c120b0901 61
    0x14035400464001e4058012941500104084400340414920040d0049500010a5030a11842036241d2364044c9501034803604519107040050118846e03c2c1080344104000035407840e101c1c03107a03400356806480c4261441d84924041d105062a00440d9041a030648201c0001070031515010856024403940011420b811880c090008214002c0701c0404543c045516040030035076030811512104600440380780c19049005845500d420615100c5d80451080c0c103002058000b40c64000c11589100e806190060744c68142c96012101c03405641c0014003004000600f0701011040c12000d85101d1fa0700800400c545201079540010f02d0352140306001d1070804500d04900c0d000221400099010702c501030010500403850701c010120b9101e540300005410f601e4400e0110198000303007804520752400ea48502e0709080da00c000c0e2007410000c1000b4100072030311304440000d0300c0c1c0b40c1001550641c03000444030381c0c04c1280f0300a005003811495860004038007020340080c0d020070b4000e40740049405003e04034280d0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 445280134 1250 445278884 445278913
    0x16021c050c010c2d1d0102011e0606261f031208060a09180b060d0204090606031b0e0109050604020d090c06030f021804050907080a080a0207090e1c110102040f0e0c040305 75
    0x20905d46084c3d055568455241c1b200c4490743d96102070550300030000180c1d6500340100545034001074982c40d02440704005c00c0e041003600310451a0740115040d1580c1810b03030000d9880c0c0740018401c1d00010058070121903a210081e8000c5140350290230100c030703e10382841e150b000090488203c15021040c0c0c207a09468140864001c0001035000721000e807055911401310380118094030f29034101101d4182d0751380c02c01c03c1800f13403e62002120550f031000c8008640e140014072494008103000d80351000d0303650300105410350b440d40c6c1200c0201103034031000d220001090815480c8400304c3e10820340400c0c241608040c8103992803084481c200d01c00710b4045071401c080024071000345001000203107a442070050118411400700a130200151140010300c0d1b645940540003400d26000e0740c0315446840c2005170780802030402080c0348107410f510340c1121100b180d1511045421034a0303c1d071041c0702540b00041c042000000d201070441a1015541c480002e03841e401a5211184204c1c440034010340c003c5034540d40d0a4 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 445281384 1250 445280134 445280177
    0x31a030c0f012a0c12020310051e09030a0806010e1305040c05090c0c0d020c091305011419180b0403050d150605030603010516021c050c010c2d 63
    0x84406241005003140440f08070310440d00c03000960082d840c0d480d0301c03040401248421074409010f05914011003450541d01003079a175407000c94611132507078440d0000740b646c508143d2200b088160f05103030341c2c400c1d00f0b12820f074540326030101005a0005903100e000901d10350040c40046100400034203208081008442d043d0001d100280003245d001041900015403a9511900580500b203a548841c0c0d941054204007841c00c40d1a42d100b2040d9049a48158131a0b5601000568040840f05201c640e0800b103190850042109410500c60031803000148410303456022588589400011000c1000f0500402249125103243c0ca00070080320310b1340d00040c0080d105a001c7d0a030741c0241400400d0500403505290841c802d2a000394000a0000c0108a418034090048035013003000035450b0080581d02183c02500c503070780ea9004150400103034042e2a20144540110348031225480004c1010708542078000700a486901c0d1142020013421010564116032209145d10340c003402d481d51000c0c43c25024600140 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 445282634 1250 445281384 445281409
    0x5030a02130906060503190e0a11040209040c02010606020d050f0f070302070b0f0d050a0b0901260105010e072706030c0507050a0b011802090d150e1903031a030c 71
    0x1121500040001d000b503040c0a0040a880340da01c42d07644038034040001100442c0700703202003001c05080426a038850700f00841c84034542074012102031419914600440d02911440d15200e4001d40750803014400a070707040d0302141c2038074429429114001000c5504031158042c8044c0210400410018050000540d10041961030f00ca401600d00a41d503803494000075402031145410b654a000500c2c01d4801040d01c15642c0c00148450100725055146012884a403414000c0310900c82d5150100705040704c010300da000000448800074481c5603121941c0f00d0074904165000c0c00403132460320807014070121114004070b03150610220100340525110040b00a000200380c048140402045007801041c020b2014911090144100c100294503005403091700c80462400e041a4501c18032003004c540e91071007007a55201d50801e40c00b14488401301e21400040c084102c00c01151301c914100c5d1151107003890841c3c6034940c007030349023042007080d140301510360100c030300e0840703075150304551024102880c06c50780d501e44 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 445283884 1250 445282634 445282657
    0x1805040c09051504060e0604081f110d06051801031205070201030207141b01030501080c09100f0312020d0306050117040515010f052404030803190507030606081605030a02 75
    0x46007561040803e050ba04040441c2031841d80c0010300303000b00c0380c01800700b4200c64001d99017280340c10718254602d503c8100083e114011445520103903031102d0000c1d0000031403191907100055882c1a21007441c3c006004c44d00c100c1d4010360402c0e80700443e110350080e403030b412030f80c101e045008004c2482c102180c3c294000b0310103c2c10700d03909203c0000441d0031094018a03030a0b440c0b0003006035444070178a910310940d039502c0403410141068014001c442c2e0105003c40c4c2035006071641c1c07085403148980300c1441a481d0304150b80c104114540001070007860703202d000360500f840c2c00303460191042c0013048094400d06d0045502142005500000a030601407000e43e204c0d00071815aa0250782240e1500f54822080e8081d01c400d2000c50402d01c141e01e8030780030081151030603035402c0f0001c21a0304a8211280580e12020301010000b100092007d540e030702061280054450042295141001c0040c0041106000e110f00040314030001880204440c845010504955201c807070841e0340b122108000303035110303140340c05 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 445285134 1250 445283884 445283897
    0x1092a022526122a010501030c18060305010e060f100b09010e06091519050301080706051b03031009050f07140912030c1c0507031e0306180c0f1805040c 67
    0x340203031080c83c007500034406403214025201010451104000420004003400b0b640340800410014030b00d0304180b001c851000e40448405050907080310010301403a803000d003081d400c201c0d00e0a0003480110304184038814464410700b0a8640c0903141585c41030030f0284040d224010004003a5070760041900c00c0403600000c0100d46401c1c40302001c50000c07c002c042010340c1c240c021070050f54041112110005010061401a04540c548218203584240d544240404c0c0320000a440300300414040a03600b411140c1022a96207080110380450382000d10720500705854900801704e04004010000f8038014406035030f071000f07518882e08013500c8a502100c4601d91007540380680540d454414006400000015030141010038440740c0e101c4482c803180c55000e0708100c0b0800a000009400c203031071180030240320301000045100540c003540140f400303030080c0740b00040e0040000c0240342c01d078101201c04503880c2c0d034440702026600800e442c00032400e00e0310f0b00811140c0303100b0300560520782e00c49403164015203001c0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 445286384 1250 445285134 445285153
    0x9020306041d1c0e0a14060705070f2115050c041a0c1903050307260405010207020307080303012304060302060f0a03060803040e01092a022526 63
    0x1d0303100c92000c0c07980507000d03040840c08420104200180c43d0811400c1e00304401880862400034010368014001c0031031140c0051500001a1aa4000c1d14452540141200c16a45c0c45030070051107403400380708080c4032130207603911a100c0303003101c0d4254640c055114100d240d00061021400c4085c0100900c8209050010702000481c1600a2030720201000e15120b280e50303d4400400c1541020701020060030610401c0c070380d0f0400240d000007207a504c00d60b1403420741500d041840952407000c1c40c407002070200d50b07040750500c4103008040d401060024401c44c12555031903614041c1c00d44074042440340302140507030300c02500e80c0d0400f81806500c4905005000050403a1a6400246550042c510320345010f000800c201d041c0030f40500c00c45018040d103100442c1050301e042c2160011032414095401800d031100b0828030350f140100000700b9490040103c0d00400300103a907000b5a00c040d001481d06c0d030580d1050400800804103a02c80301036664500d40340303c0c480d0003400c44ca8016203408003207040700c2c465260740 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 445287634 1250 445286384 445286411
    0x141e0d1404090207030309150606030609060f05010809030c060403080f15030618030f0a030b03060f040210121b030c1205040f0602090105120a091502030906040204380103051f0902030604 82
    0x2403101c98404054001011403d00cae00080840e0459003003071002525200050148102141c4107408a4000b4600030b40700742c0c0c40000030f50560295681d905524450b40050100f0035800100c110b10640b07940c00103007000c0c1e07161030300c00075600300d01486d46815802102c04500c3c3d0f01256040c01c041d00900e481207038541959844040d80d103900010110340040c0e907030400c005292605100b6590495401c54009045042540000e407413070a03000407800034021000101038413824503800800c140311880382550003100003107201401030602e1161400008035055044545202c0074443d1a006070f41100500c403130583d81c0d07601d14000754000302c80c06040c0f00d0180b0070030064030040d49040c0d108200054010400d040c2915220b00b581e54130008449015006004010344d50b400009d800b0750040e0101d03000305100440c1c507520500103500001402c00415006110032740d01064008c03403d1954020b0b84c04000c15074801c00403071185062450018200304078460b040104400039006150080d42c01000000e0340016640d5 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 445288884 1250 445287634 445287653
    0x30506010807050102010605150a0c0c090e060a05090f0303010302120c03070b12010e1e22140c0a0b07170f070303090b1f0e04141e0d1404090207030309 67
    0x32211541d0300c152402e200f00c2d40d081c0a03904c020b140c141e40da83c1d110503010000001e24000c0c40c5040c0100311818500000340506905030b4002084904810031404004103c09034444030121029a1801e0030103020032201c01e00000c512440d03183d900059800e503400e42e403c00842c00c1e080840c81001d0b01c03e40c2104032055070248807440040119200d00e07540d80011018086429a050703000e0185403841e00104280e0701081d90301c5240500c240440d51803039558003508002050340c082c800e0160301444030b00380010040043ca58800346550314044071070f100f501c0000c020f2202d40364002c07034414801c2441208001402448120b403009884440c25042001c070f40151000d60708184029800a621010800140b100c101c00f4039800074202c48415140c0801b04044070100c10707540c407801d48154240d0f0009410720810300045e4101085650070741c2c00a51a030000024984400c40290035140954610034a0950040b4440c3c00c014070400c0c00c0710f00342460046490000c1d00700e890260241a210700404000912500 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 445290134 1250 445288884 445288889
    0x30b1f08070906080111030c090d0c1706010801050c12091906060e06010c03140c0a0209041407081504020f13060e10060302040b160c0e070509010e010203031b0d020403050601 77
    0x34010040e19241c1070401003a1102075121180d640d00d803101d141c1d100e5841e00700326540501011810780e510032006002c101203440e1914081d2201070b44d00404a0f410203001c5040295031440011030b24030340d8039110494200c540075184041182010880d03180c10b845203201d2268046403250959085030b440d4452030503000254a021540595901c0c0c06100c060701c622002d68010380300307280900605259a0f4041c26180e01441610143c2c0c0d004902480700381d070108200c1060a5025041c4046030805280000c500b40b9a41010801400b078144045100d410018600005035100e01000c8100c2c0c071140c0a0211046507503d0841d0440e907210000c143c00b000c28001c1d8401012040e0542e1103c1c80c0074444a0350f2210660030010030036004000c10020002142c044d1802d00c480d05440010002142c81c4c01d2030303002c0c900d61000051003840c0080114054011000d403524a03820380b500d460718200b074001281c44c1c0c44115807482d0303075011140e80014041041005407040011040c4014503003910380d29030700e00c2c28109a = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 445291384 1250 445290134 445290149
    0xc080d21140109050a06050a14010201050f240418030c0308070905030a200d060609050a180f03210603140a081213020406080c040e030a0504030b1f 65
    0x301481594011000d064540880305041003041001601441400c5601846200f8070140c883d0302245034900d055010400501d4000e11598000c5d076594101540c01d031041c2c0340320340076500c0d100003e50350801307060702d1a1081404103104200100603621100010f01d1400350702d500a5556920f080003001c190111184035070180d29a5250f0300d0b20341c500280035180041c644401c202c01060104076a80300003039000c641980c01800020f00d1a07290102108031180041e81940c0300086056403024064244e12110545500c0401030165554894051003901c141d002185501c1243d18070100110b40081844c1e07c0403403003490081401404c014112150384000b001048040d0f50354102042040a848001d0014403c0d03070380a800d038042d42d83c454000e0740c024210300036894480d40001030440b040e858010071140754010803c01a250700c4c0e404441d0f4410341541d419002c0c0b49071003005403c2180c00000c0d50074081b0340d6a81c25152600390365401c01c0602e400750005510381c501100c405140001c0340096005440711 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 445292634 1250 445291384 445291397
    0x50405091503010c1d060c0c030a0f11030a030e040c09170c040b0405061f090e0c0a030e1b1003020d0207030201020a140301150503071205100503100b1c0c080d 70
    0x840c0c04150854111007000814441d01c2171041030501945900075021003000c8920300d443c2d074030138106581003040b0101a1940350144c010840108401c11000f40c40c003030302540c03104030856201d4081c540c0e01d4500c4507000d00800c0c0030a402c050140707000e0700b01004403901440c000c80902d540380d8800d803502604011250150300444410320350750415100302400c0140841d0280020b050202c003141e007030241c168aa0201e4513185880346400e50294072240000c0c0b8600120044519108a05618a412261000c1d0001c0e0030110104011440000d40c0c0d503002d05051071700d20460341c101c0c00300445000488030384001c1c19024040c46c480c1c0410392025000c414003076000566038442001000f0012102c00903802c0c00d56006000506c0f00241d0f49405000910460030640d81e25114541d013680c2040f00c1c1c0daa001107483c10701007040401c10580044008840c0705400b140c016002400000342035400001490750410240c690f080c40346c6403c0400d4405c1280100124141035469034441f078144075680800f030010488 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 445293884 1250 445292634 445292671
    0x10e010c03110904020c120706020405011d0306010b030a061a19080f040b150d050109020918100c050c0f0610242712020a0608010501140a05040509 65
    0x428014a0360304591440c0811095122001012503801079100060003150b0105040705d0403001040182030752480d80c01000e85515603072600c41e0203076200c2d0203150700103400245101c1c11205040b01060001400401514070781c0c0c03c02a29038070f5904020201d2040940b92080004e09106500d1010b40d9040b080030099036500710200005071580c2c416900b581000f11038010014182001030b130b25500b02e40e001242d80c1094a40303114020008082c031241541c80500300044200700203055010060041c03099480c2c501c07a5035000d4501c2400c03004608070300256005150305003654509035200420f1500349061050604e45142c03802890b2243c65489a80c441c0d0000742813000180201466030003c101c40080700d8600d040c820080000300d40c010009106220b0080113808480300360802e810302183d841200010380d20783d1035944103040300d880342c1e00344c2c02490030103001700d280761242c1e024905841c810303119540d090f070800010b02001c0c1e200d40320002c2003100c20710010441c3d584200405000d101c001c000b4102412 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 445295134 1250 445293884 445293911
    0x152c01060605031302091f06120507080615030a09201302400315060909080711010905031227010f140706020301060c1506050108060409080706020417060109060f051e09010801 77
    0xd2b0041e114205201203402009401d9032801800f030b4641914031480c40e140e40340e882043c4050040824010030528000007849402c0060000414010b1002c030f428109030300d42000003204a10480316800030001403d4000b05100c603c030125020b844000700b04100d04036556201e042d0910b8103d400484080010407202101159280220409003018100800070312005070f58980c0c03103114001c001040ca00064003218903c2e8041c0c0703010802820050705403224202405100e060507402482c1004804030030303490641907025104407003c04003206840b0b00f41d041ca84418252054120003000fa15812030030003c0c40c001a0301030018500811454075030082c44500f91a000c0401140c0c848264031061400104100f540c0c0e000d078a10360468416100007404d02418140500d287c45030700d8001e00b46034000900012161110144100954218025140b840c1d8a40c01000c1c103903040b44c880c0c0c51000c100880c00b4005c2d407411240c51100230b009906140c01508403000810381c8508260300103241a550f0f0100092101c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 445296384 1250 445295134 445295141
    0x306010e010b04031101110f0607030f090c090216060204080d0e101710030803010b0405190b25051f06060f0804152c01060605031302091f0612 63
    0x109a600190803440d8103000540308980107030700c8054a800400558485507074054403000740030b207440400f43c850b01d600c140305071a6113007402c3e281400001c2c6060040701c0358001ca0b1140c0ea0720035510190307200a1a2030a40d150001e50852a80161040381050305080040e090b032004000130085035010b072207040780c26000078140e03440b038040640c000c003d0203209000142d40001110071912040380425110340f1805402401c81010741c10003001d0900020000c552458154080c10444800300e031071600405140a80721f14400507481190010759060203881d4000c66585aa4046007104200516001c0d4040d19220720300001107154049005103040000340d03030f0b5458007402003d80720f103041c00c0302c9008403104005c0c0b10350030051024080c50003c0c2ca450202604035009440d000031245440c4804400451105000f0024041d006800d90f1809034001040350281d400c0d244618455603807488146460740038004c02c3c080041113810050010040e640d109090311168030003a0486654002c02d0500200c1c040084 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 445297634 1250 445296384 445296389
    0x909020307150c1709041505040b0d02012a060903031a031903051e0a0504170c0618040603050d020c0a050409081e121e0f04200d060c0509030601 64
    0x14080c10b0714810b8200f900022566444036003e29140c1d02d40c0480c4038140500d07804a0b9101c0e0500c0c001c8103a101c2e1076601e075015513104840410041c00c002d41008501c103610200240428080f030351569500c0368445140354a115180001c40502c05a5502c0c9422115016411400f04c2d941e8071080108400340b1042c6035044c0e0007a8000c1c44012140115101102145d010040c10054009a940505682e003103c05914104075031711079440758000c0c9000303080d640290140c0d502d1001d101d10b40d41d5038040001074003120048050441440e00a20a0070012142008265250001d07250880040002c100f00403902d10103000e0ba007d094012400004c00646020b16071042e0310450400006101180e800000c17520311103207440c2c8103c1e040458000d01010717400b4076201c4400724003095007003001d521003103000c812000780c41c22010b210b0b65a40e041940c0b089042554040d10851404102076200305000c200680c1d902d900034004080c0710199512081917403148013182d40024004101c13600117060800c041c502 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 445298884 1250 445297634 445297649
    0xa0c030501032f12151e0703020904020c0f10060e04050c0603070c120507020a06021c110f03030103060204090b030307240e0a050f060112020105070803070302130909020307 76
    0x3407035145403914203140da20310000c058090300151404004400c0c0e0140c0d41d0fa0488068824070744415480c60f441c0d140d81e00d20405c100482c0c1558002a60545c04035007000071485980302c3d0b040c8980310306004030000e412150466400c1030342045105e200d80003c1154009200d03a400c01003074114030080030581a2501075028202490448042c0f000044010401c0d0090107000d450868607642c030742e00701b1074a541040c500076040d40414031150241c4c130782c002c0050084130300130303200d4054040e030f1000104d94440300e403002e141107601e810b003141081500c240e165001240e0030200300c9210040d5181b04500713550085e403040b102c166000804000031b840c0ca005800d442c500480c0690b003442d00391744640060381202c51142c00301d40341c0d5000205124503a50701605a17940340c00201c40c4500850324106945451585160343e0611403c4000034407140300c1c2d204508075075410380d611400d0214654590788242c00150440003419000e10101c07101c183c07c002c8010042403001004107800603e40107140c24070245403c03000 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 445300134 1250 445298884 445298891
    0x31211031207270302100e0904031e36080f0f0c010f020304060305090a0b090c130b01020a0303200f040611010501050f0613090c050c01050610082701140a0c03 70
    0x1d8400c0a004600c40c04c82c2e4060300c010b808101000000c84480c182d000d01503900101010501080c19400403131656501040b041d18403016007000001d41b00c0761410312030225000c40c031102d51131030b00504411010305040c4103e10802901c1e00c0e0983c540c1040b002101814265203c1040c6503030b240c0c0100041c003001d2000703003040344101003030740d9000b52284103d01942081c0360f00c1c1d002161405008015021140707410507417415550408aa480313071207012150441d84902d0101d00811443c115a1091200465050300100200c5502c0d6405070090318000c000301c0406010651000c003150403200052003000040c0c40700c00c0c2d82c0c60402d24082c180c901882c0409005a140c00700600594a5000039451300340d800b111800e84542d4103e034022405a615001140c602e81400d61120442d41c000001d0070102c440e80009105039610002440310072981816410000380c1c64601140400300c0070039a0b00c00d580d02c00e2103114007411201c00714038252070b490304100b0301c0c1d140742d4810007000100600c41c1000090440c5001e1 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 445301384 1250 445300134 445300187
    0x5060703150506040e180307020d12030e060108060619080706020304061d150c0c040c080a06060c0803060f19230111070b030601020a0209040803010825031211031207 73
    0xb0281c1e80010a80c6c1d4400b8481d42070301c840c036541041980c44159005180a80301021031508480121000b00004007003418502e4102100c0b0010070702e14141c4100340000c1201d0b80d981000c00c89560200981480e411001c40004100e8001c140078183c0580f100d5001076690718603100006102c1024102e12071104041c0a20003a0aa0b440c0d6000310182c0100000316038a030320724024440d081281800d0b1031903005141404100107681c200391346030b21520b45a51f040054a03510207080d5100e5050000003400c0100401c001070361407602c1e9505c40b480c5100541910201e2180b420440c11107000758100702804150514800e401905420301202c10990a00e003a41c0c0480194806a5540d480c6000300e01c4d2420021002400340c0e4130810103006a5500202030f003106060504140216510a00414030fa500400b540c049030f540b0301c25007007019410488071794403480e4590b407100c07003000c48070201140810206800038035001c10f041014112511100d2414442403c0155020304114079461507001c2590031200c26 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 445302634 1250 445301384 445301399
    0xa03080d05180d0f0f140a03060303020106050303090603011806050a0603092006030a0f020c0304030c141801150207090c1805010e060406080a02040503010c05030108190b0402040b04090506070315050604 89
    0x800900e80507003400d0480301e441c5c0005540054000c08005138451000c2011005180c0c5034000030204c034003c5d0000c00c0443d440d6418941c480c03003100c56041d04608108010055550380c9000d52081c0801454001038280d198000684049420340c0300b01c000030707160171016040c0003280569181d4000b01c132880d4055a11458086000c41c00300600340131420380c1c0c41e1100c102c051540c0c1c0442d1076013880c3c40150303692103403030f490034102c000b03114064465009000417001060f0b003011015a112a40b41d04200d260903840e1541c1200d0400a40d14000d0840c0520303400010783c3d81c054090b0510141d1592203500803104420107c49044001e94015070405c07071070303044075010f5449200440b000e41e0380a01d000d038030590b2010200e6019203d190711998056180110b404e00c86688070001c0c50585407038800f40c400c0c042c1005c011600e0b0395503035030000d03041c40d2000b40458014074182d0710841135103202500c007144030200da4407900c0c201441140c00e80f01084e1101120000710008001050152004440c20b0341402d0400c2c28 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 445303884 1250 445302634 445302647
    0x40f0b0a080103080304030c020306010b0c011a0105041509081e0c010c020f131d030403120c02031e160b1905070f030f11030301031527030e0a03080d05180d 69
    0x10107490130600001182c1858414120109220b4000d421a0006d580d245c0b41c080c110751011061030703015441c0282c4c0700030f48ac00c1160400d085002c1603560505043c2804070f08042060616030316428000c581c40c0002d1390713210511405d81d8041d169810000e01146180781c1da401e040c04545401c2c10001000003103001aa540d403130500c0b4148082c0c507442955100302404800500600980039035a41003c4114400414000f00810580f88a070f0000d03400c1600f00754040d03440c541c42c50402549504903809044800d0500408040d9200700d260031030b0a00d29550b085c060141ca03c9420188500800007001a620303480f803c5983d04c0b840880c6401c502d080e01a44803005c45000c010001010001c10501035603200c2e20071105900000083e2040d21b5403541e40b454868048008030044151840c00c0c00461052040c0b40c5920040144144c0c00b510f403c030b0190b0382c0455990003c125440d51040401c00c020010030710b40009805030301302204000410342411450340450b801e42d401e52000d0b0303511031960104401d51040 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 445305134 1250 445303884 445303889
    0xf0516060e0a15050403020f0a0c03060c1428090605090910050907030606140406052b021b010b060c0a030e060f0c1b03010606090e04050a020d08040f0b0a0801 70
    0x5000078800c03081040d450a0400320708020b00361840310b90110115120541c8840d00440c82a0220f68a007036401e4034841c2c1740c4248000242c0484d187d00c41c01c201003542d58222040165051400c212040c14020f0b90712103d4000c04c00075154a180344240c1b1500032006140f441c42280c040c1050020701345043c6d80184140f1607104005c2c024494400400c0003c4034551402d80a090010100380312880c203150010b004080364450180081c00c2c07241003210b0360055000301c07001d44859984286c90141c408071258050903a8817800405024651500c41d0403400300e1014200045846513440811111041800d00391000b82c644c082c4694820800d06840180008840c080c590703260a0400304480c0d440c00065250144000d40b0002040c00145040c00d13800c04503030309100d22101d001d8401604000d0083c18202c07111800345d0f00201c2d100c09000d1000301e84c0200c44a6002e0300c2441101c00b0144558003140403010078650031507005101041c203000c2040c41c000c5500152001e134810701c0c14035412040c02030001a061 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 445306384 1250 445305134 445305143
    0x3090d210525060204030821010905011202090403090302060319050c2505030d05013206040909050703020619080a15061d040507050414010e030c0f01020f0d02010203070f0516 77
    0x1c0c520b07007040196010b0350001c64001c0001501d421070810741000310480601e0920000741188004203000441d445414140d842c0c685900301414855400e2001c042401b500c26001e01a21840020059840c14010340c400d118000741c3c5070f1501c00c00059032041d01d901500111040e07609210081300001a05034801c905038202800d002c190300c881c02d0003800c6202e055180b14556040000201c0c90001a860007001148800c4280510310420400a14800481c00420341e00210400041041b020345400120b0500d003d10180c400345613032a4001f807041d600c2010007403840044c88103440a09504184d10343c0c0e20211906043c0000c01601d00100424000d600071700b41480090300c20045c00e400c10142112072079101030010005418180f10241c00340d00b00b0300c51480520401200b038910741d4842d1101030610310f030150050035100c85001c1000103100005101904500ca4428507204a241c10003180d21841c4080d000103a59091496006108140ca5142d080500c02c007000840c240c084080c24188019400 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 445307634 1250 445306384 445306447
    0x501020613080310360c0801030210020102040e090606030609030c07150905040c120b0d05071a070206041707090207471e060102061803090d2105 64
    0x104e940500c00c0c035840303030046a01c00c00203142175684500c099402c3d0b56890404112a05210b05186690713050b01d0f040007101e00003a400348010001400c001079042c18282c00cae80005800c003921240310200c90102121110507681c000000e02c85141000c1c0000364002d25000e0196250411611401d5520070f9140720364802c20b024503e031114414461a0000040c0000410a010240407918000c0c076603445081162581d03454013010074207134949286880c00030f41d070110281040916052110301555102c0c210081103607010081c01c40142d071290000c0001c0c0060f590010700c09250390790f10b1464a1030940200c0c01c40d070300c100070000c04600e4400d2803031100460401c801d004015401c10300341c0980c41c42e0139010580c100d440305a840802049000a21030010401c010013084020400030710340711400c2e1025400340e0041c178082601c81c0800360b00050701e0f141e2841241d1800b1003090118001d1088420151100b000d00898002400181000303980b00d021240781c140d042111401098205540c0410740a222045 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 445308884 1250 445307634 445307641
    0x170a03140109050403020f06070c0f02040b060c100f0c05030f070c050706090806100f0b0310121202100506011b0609080c030316020a03020303010902160b0405010e0705010206130803 80
    0x42500003500320951140d001103156541d046120140400365000c80150080c001100300301d150000e4070920585c1140e4450210410903101e50745030700103818040c2d8000e515408a100b064860341d0080c0880c1400130700401c0091403c42d40c00049400407154034072114280301c07030740325217a40c0300c025260040902084840d150300c0d0030390140c500c3d88403418000d0003400341d044001006500000c7c03d0044400b000180c803a00d03641c1c0b0551808100440c010151450980c80e0b0611510490344040c0da0f1040c03a404110600a031120a41109036207200c80440e1024540c800c86e450b241c0d4180710003644421500828001d500b403d1001a00078415415003083c2c6000b07482e00e01c0c040c03111580040ca000c0740c1264483d41c0c0e5401d04401d4a450758011114100b440446103484cd144500c001400048250154065400c2d642407403441800303035005e1711082c40084003070000e0b00082170b003034902c040c0140c0c1320318000034900b11402c42d40c0e800e00c11154811419500000c081184091406071030024550f400f44000c2d5580e07030f = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 445310134 1250 445308884 445308887
    0x3060f090a0b15040609060e30010e031306080609011502150a0e1204030803070815060a181a070f03031503050a0b0c0c0a020d060219030605100c170a 66
    0x51070a800301d42c07044203001e940c3c440b94500c100502c15034a40b42d44494103161a520305903441d0f090912516000b10403551409004450309441c3c4010013130052400e024031018002c6c0394251500c4800c80c400d0740d080050080c9004800c240010020011802e00a0031441c6c0381001902e411070500c2114006038154141d804a2031082c440c0c00d000c4594000310000b141001c2c4803420003081c0c1c4801c00303007051007011690b100d1002d180c019901201da001e041c03149542c3c0d6a000880b000d030405450a00312101c0d203000d01e025a0341d00406006104660395966800c08610042d0340c0f420003403a4400030a00030340d0303442d1300001c0041000b124002c94100c02c04000b150501d16040f401040c4050385210360184502c000710400c440411020102409080c0c4111591110300c100001031040300c8a0500f160302004404005080c850450711b00c5502402d0014203000200200e110034124141e180303400030f96a034909101c03516049500c031000184905d4010142140c40d6180e00c62015401d070038414a4601040344c04400307 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 445311384 1250 445310134 445310141
    0x15061a09090a320108151302010212070302101113120c0503060403081e010608040f030210061206150b0702061804140610141c0b03010216050d02010203060f090a 71
    0x1d01e82e032645a8070070005500a000c00e440591070524215100f0000801200c0000e140d5603100080d0b090040710307207034410130760180d549212003241980105202d4100d010070b0b0304041c040f8503010f9009010f4141340402100e003125600c21000c01481028003921130a001081d00b410152861b003000f460070540c41e81015800c1c4011980816031512403103041008240e80b203e0503034010b841d050514a0422100e080012031407000b4020400090a8000014041410020209001800303401074800b0307110110b0514099622581284404200c0c20b000d403801c011061080303006401d08140240c0a0070309200c1540f00354400e504008c0d120f111b01051444455001c0701c0d41602902e0024402c00c07403440321042032840e0300303c101d0302030380f103990300f0f4400c001036501555408216807041c9100b1132034000413190b581c1000f04100e011540c4c40d07a8403034043c155500c0c240300803d84101d40c6400c0b038400700000d20300280f900501400000443e4018418804940c0342c012900f464910221800e03106a03440704901e0009 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 445312634 1250 445311384 445311401
    0xc210816020a170c061003080f09010512071d06040f0b0c030d0c021b1009030201110c030f0307062003060d110910031b1805130f15061a09090a 63
    0x103000e4200f4082500341501801000034010350b4054902d955504400c124082296100180c8a13500412013190440e900c03000800042105041140c1008940d410123100154100c580c00e0203e1704c10140e0b5401ca10455040c0980307070008030340c078510301800d100301c1b095608458803c504a8a0001c642140420300510a964200595010400504004060080d55111070b00611100c200c0c030400113a40b541024400c0d0b5060b41019200c0c40c3c1214074646c01111513071075801d03103103509000d4501c4901c6660746c184040d40040403640c0046031034070b001c1d051203000c9071101c44d600f1240021000e070072400049103009176581324008545501c00e85406041c40c7c0e03940e603200150301d80e000e41d9600801201c500424002016240990319200c2404c032003802001400015000b09900708142039140303100d0300721a0700021345c4081c0d81c0d5074107000203c4580d40e041516050801c11540650303441c4049820644070f1258000030040d135900b1030448c80c500740240045109000885000301c1881e0005810240150800483c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 445313884 1250 445312634 445312643
    0x907172a031203070306060c0b0402191205062202150c010204090c050a09090e1005150d2306010302090402120c031917041a160b070c210816020a 64
    0x1820703541c0610b15140c5034012140c02d000300b840d242c0003040c030318415410964080e90249406409480d507800300414010901130703402d1044c16400c3c0203d40341040c28110404c162155005110500b01648410700c80c8200400a201c006c0078000c00d4405a0307951801700d0b00c4002c01040141d40c030000244541d019200310f030482004182441e016100f01c0307074840002d281f182d02030f5852055007600c070304055081c1d401c0c2122803c01a480307140103091034803050380555040b0041840c5006070400003000b0500c1030081c18400d80301c01109000740c01180d0b100d0094101e00400300c10107461150b0542e4005409a2000381007e030203400d550199107242c28003003081c2002650700074121016400160402484040e00b030388200c4401c10b411103051248100c080a40c1c042d1448044403801c0d107070b425200c12156802c14001d4942c012030541d58000800c4403e54000d0051240391345160f06000541800035049060507028207a03064a480e500f035410b9030250b81c268021500b10340c511a1004030190892914181c01400342 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 445315134 1250 445313884 445313893
    0x417120403112e030209011206120201110606090106051b010e0c2407030c020117100f14030a1e05060f040c0e0903040b0d02210907172a03 61
    0x90001c00100a10b50142c03c42e0601d003000019601c1c0114034010411110000c404a10742c659043e01a80140c405800180b5001c18801c2240b50104e003038940a9200850441903d2594410342d40d02c00b00035a80000301d10018000c6003009004280c0a604c1449180e04220020a40d0a040b05d0703400c2c0301d90300350b0708900000e001149085c075580d0744860855003000e102d03000c40c000b1804034142c81c5003510445c003130200440e802c010041d182a50740b81b005003000c904106800f54203032560340001100a02490180010203155420021500c451052039041441002135404550741c1a90340080c0c917160580c0e01ca444410510240600701d08a40c1500030300400500030001006004141450074a2040707018403c2040f0881d5101c0300110f6030102594412044d030020001400600001001801040c02c105801854511024600d0507a1006a18140e6246a8200c180205074608001e164080c2048220700c41900c041005007641d11138400b8002034108010f401e11529010042000051980300a804c0d41d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 445316384 1250 445315134 445315139
    0x30417030709080c041a130608030307091404050103021315080f06040516060f140f03010b0702010225090e0f120403051501030b0f09101b080f040804171204 69
    0xb030190025070103188068422804804c2c41c03854603000741481e4040c2c10511081d0f074594242480f140d0741900c1d10f002e00300768070f13550009a08101000113602c85c20072aa119070200f420011034000261400318080e101c1d504200050025a4803108848201c0d521540b00003040d0b030001ca01c0c4d01441c1d001c0c0d400103100d4090f205c600209140040340c142e00c138a106106036040080f20701e4000d0050420340c0622000101c1081c01000ba05002e58001c2589561403804142881004c0012030540e80c801d0304900c610860200700c1d00111f580400371004008a0760180c010340002d0030b5151004e1104900c1032420300b58803844081240c40c0c05002c0c3c036400380c98940c182d0b0b01c07545021300c0d500301a500c103200c211480d100e004412050a0880d059540c141c0e1307800300c40707641e19407a00a40340c1d074020301c00340143c20b8034010aa184403824043d0f2180f042c50034106401c2d00301d00d03d0350360009820b48000400c0380d540e09a44004210010700e064046800307076041c00f4401c1c1d080c4144610910700d005400c81c0b031040003401c0010301 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 445317634 1250 445316384 445316387
    0x80105090d090f0602070b0d02070b10030201030e010c0519030e0102040b1e07110d060b030d0207080c0d0507030f0c03060f0504230a030e0d020603010f0602011d120304170307 77
    0x725034440da0701e44440099560703419040001c500d030340c13250200682024505106203c1c6080c001c1c821040441d40c09801c00c251030700e07418040082541c4401200c44089010011941c1501a0020848005000308172181b44060080c1052040701e105003da2038904480b0440c1501a6210502407002c2500840d19203440d4100071010358085101d407000115060403502c01300881204540c6031550010000b00c4c9403c041c018880d02015150f4111282c3c0e4485070004125202005500070010b8160f0041601c0c07450268281d041140f220071850180341c0745903011001c5040081c50300c0407a540060001005482da040c03070182c03e10a5040101440d00f040280c1d0000c0d02280c01980c0114000d2110014410700c01860303401c01d920140c6d4041c269000f4040140100b07005442101e00040d001e41805c04203e1940c2c00a40c041d40240c110704d16038030742c0e103a080c00f685909100b0186920a0f408500544131442c1c00300d0750782c60348200300c0f000112800100107801c014109680c2042640d50501c921b40f41e00740700d40f0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 445318884 1250 445317634 445317643
    0x706060b03010317040b0a05090a09050406050604050a061202060f04080714010e3309060f0409050c030702100209010201061205010b012304050d020415060c030f03110f031008010509 80
    0x2503521060000708400b00d010004d007111300719003580d1706861030f010071603030f041d119600020300d01984100707a03030310021f10500c240c0240b40c8154030603100022503280c01001c0100315031020304182d00c81c03840e1500c28040d11200107035422a046e01229619200c05107000020f40510968020700301b00c3c010783c2000074100c075008400d20b0004900341c0303a8401414a40b030501c602c4583c0c070200d6030000b8a03114a0340a010b405103800d207005c40c04840c42507280402e90008140c0d15884091403003a59540000c1c20003c4603c9407180e141c0112850109a01d14144060029940c40f1800b00c82c0100700c0d030000c2e8181145c0c0c000d501110003040d03840504241c620386420503900a00243e04d109002c28440e15150f002026060f40f94424041c82c010102e0802e82840140141091050740880e0084c0d0342c1c2da0311004c44d403600d41d8540c0092019644001002c00c0b589001401000846800b00c280b60400501010700d07109001900c8010081c1d00c03000d512980c48424404005840f540f05040d15482d00341840302500004c00d = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 445320134 1250 445318884 445318889
    0xf03050d030e010b060f0901140a11010b030c030a03080a060807090606030e0607051b100e06040507270c051314121b0906010504090c0302090906010c0b04030e0102030706060b0301 79
    0x4504102d10760a60328074034282d036488800140e114000b0130901803c5802d02c0007501103268189025101c0303110b500003035903513540015040e201044103018460304200003409955188001500503042580e042408641d407500c04003001428488000000364540040d580414000d141c04011108602d66846400c0700604641c01000300007820156408150300340064114080c40003a40d032289865085108600c100340100c902d1440703401101d00a982034851401a039401c1c81000c001f810b2141841c0c60101e00e44030381640194a07034142c10350b080700d50b41c3c6800c54907681e0080d11407010580704c3c0b02e5401103d0328410035003c1800018072940c00f2400d404200e501100c1204250b4002c502000750340520360b51400b41c00e1000414a030008404906810000d0744a50050018108242055160140c10301640d03800ea44260000e0341c0810b541c40f0300c3c5081d40034585c201d0402e09045e00100032580716007640c008002c01c041c0900c40030306850300290b4802c10032240e44d140c100608000c03050f11000c1c0740240d6482031 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 445321384 1250 445320134 445320137
    0xb090108061203031510020c0307032d080405040c0c03050d02030c070206190201060611031b030c100c0806010908060a09050c1206010305060709152a060b09011e090203100f03050d 79
    0x81d80040019000064680d12500d008002b400c80a2543d911035411010308075814105401413104403511182800c10610150712030480a1b881c0d50402c13062008544036200704408208840c0223039004039801404844a006042e80090b0b40c030f40c3d400351208a0761081070030081d0000c02c006000c50b00b040740c2c03140c803030b140300d541364020f004495403030104403040f00313445281c9a0a82c0081000c5070146607021038242c0303c4c52495040c1c0f4140070041c10391032b08085886d5003180c4030030744518400d07882c181e101020710380c0a43c090030320403042c5040040050390303544010300c1c0403040740d902d0860400f441000c21040c043e1210040021022810a80e05507440d0074083c44102c0d074a1152101060010780103280c414103482c546100d401c43e0088000e021914005001c2c8003010b5000c000b88604401400b00b00c1d080381590160801042c0c01c05507205010309510140d01c244e01d04a03001d03a102030350b142c020134007808841c00444003580f29240c03002066040491036005403502c40000b6400000c00101250311042c91109 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 445322634 1250 445321384 445321399
    0x5090f030106060e0d020a150801171b09040c0b0c07050a151e140d0c1107060203090103020a03020d050901091505060a170109060c081b040b0901080612030315 70
    0x6100a05099a05034000d54010a0082c0c207404014101202d803800c3c0e49000504a040071543ca00c01412140040da100800003803100c6c0062144030460340700400154034040040664401420443c041c7e00d0036800c00520030407004004c10b05001228000d08007034140c000005660340340283d060340e40c8560a00c6224020840c10b08001140e84025540b26140740311921003500340414001d40000d40000301c9500030a0040701c207861000180094046c003600c02c0c00c5180000e0880e0ba20401606840240007126401d600c4400c0a212a03030340882070750130411080c20701580304c101c03000b0160043d0103282030002d14540f40c403041110a000540060015070300942e45400344d82e0031700d900c40b016210210f60359600a2013000c3c1c100402140c0021404184c0c200a0000540d0b40d071179a0f4000070749036007010103400541d0940c00c1c42403000050002c2403e00c45100c410502d403601c3c1240c450700074010840d01c1e505100b4150001002030700e9100545450078080000d0701c1d60307454158503121003044401000d6004145 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 445323741 1107 445322634 445322659
    0x4020705070b0f0405010e12100b03121207080c030f01030816050a0c0e0105010306140d060e030726160f030e15120f01050d1419030509 60
    0x940000c0d80b42d911362904000410020201520742e104182540034031b05140c400141d0480d40e045210800f1500d1f0420800080c11701070000042c1c80c85080c000b51600c0044140c4000c1031241d04607449200c41d80d22509c0684090380400c4924001560301280140301040740f48001d04101d00c0300f400880008100d40c2e0305c1906040c45482c4c2221804422107003070103076407a250505405000c003840c04001503440d0001d0315580f110b10b04290f501810711a8400c109001c00ca401280d80c114001046a0360380703a10b441c180e05000300c1d1096010040384003002c84850403090358100c85501c10b244880031f8101c1d4440d101c00c00380c620040012000c0c00f00210030719046448051941ca03440d1540c074501502c4404031050300d83d48003030042000464012220041c04039940c2e24030410059600059000d282e4081c00c80e566117032825400e10390f1000052a0b450004042d40400141491b260644248a0419 = true := by decide +kernel

theorem cover : BRFrame.Cov 445143884 445323741 := by
  have h0 := BRFrame.cov_init 445143884
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445143884 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445143884 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445143884 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445143884 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445143884 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445143884 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445143884 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445143884 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445143884 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445143884 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445143884 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445143884 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445143884 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445143884 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445143884 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445143884 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445143884 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445143884 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445143884 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445143884 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445143884 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445143884 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445143884 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445143884 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445143884 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445143884 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445143884 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445143884 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445143884 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445143884 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445143884 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445143884 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445143884 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445143884 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445143884 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445143884 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445143884 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445143884 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445143884 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445143884 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445143884 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445143884 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445143884 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445143884 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445143884 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445143884 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445143884 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445143884 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445143884 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445143884 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445143884 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445143884 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445143884 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445143884 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445143884 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445143884 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445143884 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445143884 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445143884 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445143884 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445143884 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445143884 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445143884 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445143884 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445143884 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445143884 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445143884 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445143884 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445143884 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445143884 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445143884 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445143884 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445143884 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445143884 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445143884 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445143884 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445143884 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445143884 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445143884 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445143884 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445143884 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445143884 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445143884 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445143884 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445143884 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445143884 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445143884 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445143884 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445143884 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445143884 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445143884 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445143884 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445143884 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445143884 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445143884 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445143884 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445143884 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445143884 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445143884 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445143884 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445143884 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445143884 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445143884 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445143884 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445143884 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445143884 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445143884 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445143884 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445143884 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445143884 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445143884 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445143884 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445143884 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445143884 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445143884 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445143884 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445143884 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445143884 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445143884 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445143884 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445143884 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445143884 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445143884 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445143884 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445143884 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445143884 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445143884 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445143884 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445143884 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445143884 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445143884 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445143884 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445143884 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445143884 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445143884 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445143884 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445143884 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445143884 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445143884 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445143884 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445143884 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445143884 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445143884 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445143884 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 445143884 ≤ n) (h2 : n < 445323741) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
