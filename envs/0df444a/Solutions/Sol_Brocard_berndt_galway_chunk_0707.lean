-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0707
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T21:15:55.307031+00:00
-- url     : https://prove2.me/submissions/f3b54f2d-7226-45c5-a3f2-596709fdbf69

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 126978417 ≤ n < 127158273 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 126979667 1250 126978417 126978427
    0x90209010206010518070806030304080307050715020102090102122805090f040c1b2303040603060f050109030204090f020619090e0408040e31060e060403080a0e21 72
    0x180c20b00074140e0000d4051030188020350f40d1040c031040d8142c0d000d03240b41459225038a800021034071b94041c030780051100e4400090441c0034040b00203905821241010310004421201a00c101c1c280d008124404d409a80f1410440c00c900c0e00b0b540c040c085580f103e0f41c851480345c41e4649050704002048a180001c90400105c0401604016915001103402510280002c0d101060004d0a400d0421241c00620342c0365004501081440030307100075542c0180031031200d51000240310079101d034043d21501002c2032400d8000100800079650380c01c2102d40c1615440c042c140340d42c083c44080c2001401c1110313008660401c03200140c0e600c2c0064204003a000001010710081d890028003600425009100e81e4110701080000150804e02100c05039840c0340e0308080d0345d48400c200102180f00304402680e01420310300c0d044071482105900d100e07002c1d004040c184800300402d003c0b151208015100a00002c0d07001d070005940303411076042040780000541c00c4906c8602c90fa4070000c400c0b031034040660b03c03003880003034 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 126980917 1250 126979667 126979669
    0x313051e0d030e10020d0905010504030e27010605070302030d054f0302030d05010b0d0c050a080106050f0904050a060e0709060215040204090b040606090e03070c170c0a090209 77
    0x403482007498010700301080302c00a01810300d5602c100c00b070044540f20350001030130210408039400094203150320030000c4c0010700b000d18001c1c01011020303408601a0007481c1e91606610000358210400040080101c1800c1c3d080845c212055032010f5001d1b001c2d0300c001c02035440c092001d4440c1e14410111500c21081845045592151108030281c9071030380001c03101071481c100c20580405081c81c202c00c6d40000d000341d4151a06a085000da9040000d40c01d1030a0000140d84841100518590028040c2008403411045081d103850041f0808bc6001588000c01844441d008000601030505000081070a0400140014007940c1c82151a1a002038846c141049101418010349800c5120303401c141d02030f2410204000d581e03818001c2e80070150001030020505548595004441081c0c004401240714606424000054141c0781b00d0b910706149860303a8002d400d0b030007000b607400c8c0c80d50001030141084e03d450518526149000c01c038014a004221000d0302541e98600c1800007015245401351b12200420 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 126982167 1250 126980917 126980923
    0xc0d0809010e0307170310150201050601200a02131d010614010c080d4a0c010f05211003110105070b1f15090e1005150313051e 56
    0x82a007040b5074401e0080c4000035540e541640500c0250301505a16656084200d40c15090203a01503055103414920b448001d03981904030b140704241c2a261244941c002d10b90000341c000201c0d480c28a9500000c02900040c603107803014180d0701c5216900807620911014404c0b030010318125002405a6640408010b214004098640340e80000d08060701d03640700380d0711401c0f2130b8842d0001c1d0481c020b580c1e0301090600c45a03c21911944205002c418200c0c1c001403140c24241c00f00206064500e070100070380541650b000085a402174641a9501c9055501265003596660012444052001c20700400743c83c6418091015a105d0404c0d5000e90355a00c1c43d6080c6040300010008840341040f9003048900e01180b142c1c01280e41002007800c1c00c000b2154003501c02484058190020682581003000d1303904d00b41d500c000150305442050baa06041a1140e400040d60410144212600040311809101c00d080a102c00745610810800002440055517614030341024041960040304102da0310308000514410 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 126983417 1250 126982167 126982181
    0xc05031303020f030303091509161206050a0b0303190e0d0506010e0108030306030c011407050d030b0406060804020f0d0515010602030a0815130b0409021c02120a08031b0c0d080901 79
    0x56005d146541054044180c0b580e02c414404000911007034045004078400300f042c035040c0e45c241c1603203c000c11340b03901c48401c42c00d03205141982c07044d0610021400698040c0b05030010000b00900851601c1e4080c211511400088113483c070038480b080305200d04507180c4058580803244500094500d40d810300801d10034881040e004181b09071300030700c104503203a05d0020f8840c400a41c2420300103c000080c510000a41c450303c0c1700184280280010070704401c1d0541c0042c2c900010458040c0310080c5c88500440b050642101c019600840d041c1c504401d03401c0810b141c0c2c0c01c1e680510b00b51020b84041c039040342e41e03010b02a4464001a840041c252000703650003440d0640254421400948494a05d000a000020302d940798002c040d6441c40c54104950b0380c0d5200e181a135902805d4510241e142d8002040f00d10002d0b0016400340e4a0b20011401140000c103180c140141d00c20034050868039069514110401c00c14403072400042d0400280301212020401c010400c410340d0307691002c92405085da41d007950700d0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 126984667 1250 126983417 126983419
    0x90504050c091009120b04021f0206061c0302073003020d17040302030a0f030e12090406090c080f100b0f03040204060f0803180303040306060b180f090105100c05031303020f 76
    0x4e005050100881c4030507400300c0e0f190004011410340e240c5000181c2c1e65000c4d1800640c05411141584406580208000c3d101d214116041a0b442c1e4010860341340ca404c00d07460040c0103030000081400784241c80315044011101e1070008201e01c001400603100342d140060003c0c0d02591014032240200c507444084070741d5001c00203122140d0703800c09581c065503038001c0750040380500000200c61000180b00740d0003150221088011103c044a140c08400c549521601215000d10305211010402e0315150141408096050351030101c01e940f07004a2400c104405000d00d0b62000c0309003800180820050040d00340000310300300c225542d040902c104000c891041c2e201c020703014000d001c2040503c00100a031074104030300c1e112400009074040002425403045420007051140750000105104402074082e01818100034034a4441e101c001c001c12120441600c2c060b0340c040440c40050144d0705003100486842905401d011901e0151270b0768031800c41d0840415003804000d501d2040040d40f500c4509503c40c014 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 126985917 1250 126984667 126984677
    0x5072316020904020f190602060c040f0312090807090e1b030c06072102010203071d0303040501050a0c061a100311040915030609050c04050c0a0207060f090504050c0910 74
    0x140004004400460300292040d2076020008041d0344842d45048204100149118200e0401c0c00028111920300d00500c030040c4078440008103c118940700315015601141503104803d441d40d0764807441445400c40410402c000410f0002d80034100700300758800342000940c04140500041c5080b032810411070085000c0981c050413005a903200410701e808003950a82c1c080e40c0e1b5501508125141d031112030400c1501800400c59142c0c21035065000e14016540c650311503107558122241071800e2030f448007540b540740d001003004005960140c1700808020b109414a18942c0f4010b4545c0c0045984040c0076031006805043d4400061600311400008450326080410a9510300118034010780240c2c0564407581d642c4c2c0a992a140d401c00300c0340d00003075034030200c103000300d114030b107012038035001d403031012501950a25000c2018071511000b03441c1d4144072607009020040c940041282c4900071160400709018040d078010030581c0300c1e409458070840c522101310780d8811360300041c0f240c03a0b032060b5103800c2080 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 126987167 1250 126985917 126985927
    0xc030e060f0106030b040e060408030604060608090303070f200f07050102030424090302030f070e010e04020d0b1504020f030108061308041712070308150a062001020d050723 76
    0xea92111201c0c10b548035131a00054600113000401e0040060b03c0a5a4480c030800080204001d8100025449004156002e000107a9543c00c20754140e64142d541c44041d030024000a44032605c200c001440b04405454448841c00c10404111030002e080302005600b60081e126968011000b04180c40040c44280b000b145040d01e4001606481c1c1c600c0100000c03000c0403045440e60720b620512486c4055900107081e10141c2200d001d8007562002548240000030b142907000183e140d403006802441180c02410507200e6001903075500700f02ea0002072040303801500c0001d0399a076a44031440a04500b108500d0070355a40d50405a5140c0342030001080411807000340340c507240000f0841410380e000c5400404001000607600301c1201e09003000000030740c0c1900408035580e001c0c103901881a500464211444401005100c401e029820190340200750100b00410032294004e8610883e50f10b8200f6810001410b2040305200001a0b6005517800c01c0010302d40760b100a5a6910200003400040f03044200710316003 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 126988417 1250 126987167 126987181
    0x1080f1203060a120512030c0408010509010507080f0a06080d02030c06010b03060a03080d06030204090602030a0e0a02030c010c050304080f0c1003140609040f140102030106110703020a050f030f010f0c030e06 91
    0x501c8407030003405206141240c400d002c0100070032264440c1c84083ca0b01644030300c1c08000c0c03110386270400e1144420315030816020800c03a690600c0b555010305020303075880e016959a40c103100704152002d01b540343c0700c6a6079040041c00c1e40c0d0074440405550b26560156503501c102400091070244181c004001ca10010020f024003a600c01090f1401ca9070302c5080d00752180310000c2200004c01d50f960010b0b4005040101400c100001030b03009620131900000104000c520210905a5030074080748001c1d09940710558020856024049540030355101c1d40c01c5901d401d03103e4110909103040900c07203c84030340c0400b05c20425468030500d600e03480d00c0c080c40d0400c00319074011000903500c4409801d05000d49111404902031101180101c0605600840d44003124961031844a000f540300b441640d0014400f014624880400842c415044940081c540d880e2a0b040008001e82e0b082803030611a0306101c2c102c0b808200e02420701401007843e1075500c1c0003621800c410409800d0781c103407296000464008400f04010 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 126989667 1250 126988417 126988429
    0x207140d03031d010903050d06090c140d0b060c0a02010807080c07080f0412030f0815060405090903131401020c06040312080a0f060306022d030106030c09050901080f120306 76
    0xd440d018500410b2141e010003212405010f03d0007031040725424a01c81c08241500b003002082800c518200410840d03070781c2c0094108450410002c400001e010200000030120305402500345a8600f490004500d80700c0e8000680651009800d405c060b049419171030190b40e00045000c1c4d0000f400d00304001c0b1362811146041e070b28400c202000381401c00219000c800c0a17021401c1d0740151010007403001d22440715050113040b000d403001b181e42c00107000d840041d550312004007502c88140c07809030100d0700b003504107410050b8282c00103218170038510050044c9010825030289500081450909018807c1c8a49000a06182c51203d6590180700704100400014001e001070100918462510b02419102c0284c00300181050800d000c0c203040c1403440c0401800048d50003028400e10742d100200030a48941c2518170622034225050100b00414001000074a0003a00315550790f070824540152411340701c60005190000a07003003030807143d200818810025400700246401c5821800350103041d860030b2800600 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 126990917 1250 126989667 126989689
    0x70503040807030e1c060501050a080a06202b090b04140c060301080c01110d02060c0708040312170906101404090c0e09190201050a141603050307020714 67
    0x1003400009a00b030602d4410b0046801d05036000b015501c035010000440c0038072510303c4d80103840355880e0400000311440d04034070300e500301c1e102d0380d002e08580880340d1205e00042041f2590314138030740c4142540100030302101c001400010080000c481801c47e03918904100c1900385190b03030155500e020b50010100e90340702503a95020b50310410001c0c2d401e103034800d40c5040010f0b070f403900c0b90440404000481c00b02d8000c01c02d1b081551080c0c3e55182842d0411003501ea07114030010302100503070448004501446070303aa0042c940c0c107000300c500701d1425079699140c03844985602503080010b0407001c1c0b20108440d02c1c031513141d081002070f80107001d40c0c02c05402e2440b40e104640715240c1a002400c0310050b298849400c00c0301800c0c1c00c5190210055550f44100c0c6101e1021201c008060150304032070801c65500c04101c1100c20f406030744045c24400c680109580208206151030600c80050016541c2102c041021411691191780d806889017800e10380a0300c2c00e4442c0d00300320340320150b90301510340540302c1e038402e82 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 126992167 1250 126990917 126990923
    0x20408010c0f0f081905040201030207170405042d0b06040b0d060e01091a0603070215010801140106140306190503030d0b0a050303040605031902251a0c0d0902041e150b0307050304 79
    0x6c854a880c80141d000b44100e004c01031100b442d4413807043c42c1101481c05042120010348080c4003200c00304144032080d500000c0b072000d141942c40c000c586011620342c0702d020060005020f041c038090f25905400a903030804a002c0d200f40742c8038a402d103d031b108001c01884c01090312a4082c4203850300c5030358409815602180b01e600840c4040f00081d0000e200b0000d081224000b040019000d58407241d0311030107440d2503052240705180d135100000343c0d94460b500101203c20000169411034642c8410400300603003803200b0103c4410300355800304095070140000c1904103445880060109108020b12609210903031180c5e00c240c006110422170350b500702c0c085a030b1040748440c003050340c4500b0b84000002030140c0810020103000c2a850048600c0e200c82c09035030320a0107840051840301c000034120100d00e0003210b101c0d107000814891041c2c403840c01d420180341d00d840100041010280030410320b54124401014030352143c0c582c0c0b51050242c89401030316026040a20045d45503242804000c0d00341e02c0301070401 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 126993417 1250 126992167 126992171
    0xf070201030b0f121b100207090c050f040803130b090d080d020c0102190201050603010c0c08070c241b030f0809030f040e0403030f0606080a020a03020408010c0f0f0819 74
    0x1500076a03c4625020910701c004084204030005020020fa0f00c12100c2108500745142485040203858455002d01103c00d80b54028040641014000006450441401000d0200a100c2c05c0b00b241600070140024040050056840303000e103200702d50b040540351b0710041c880704041004250340c0d03ca10021184050b04080040c1e603400c941c0a41a0080c03058141e414401e520205010f000c1c5c486582400b0540d255070b0b8028172654503540101401c0b14480803240340070aa0f078007420000905610050300340c40e401000000d0440b9510a4005d03a254281c1c00d501c003404004080001c0700c0b035048640c0d45150301c64100071000420f0b590390003401480d0f0302c400e013070244030309000005c401e44001c000311104c081101c0340c1d4940b41c6650311080e00c0e0380700058800f14042418a80704010b928414480c1c3c00480741c0542d2280000d85908000c04000c1d441a0101410103070200000301c0c0940302405200905195a600c1483c91010507100808002c0c00b5500c0c1020001c20070180214480b1401c848000e20b8411400 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 126994667 1250 126993417 126993431
    0x1305010905060c180a03080f0c0307080d05040b0f010e06040902010203120a1d0106032d05010c0903110f13020a0c0f0c06031119050a030615030e06070c05031207020703021914060f07020103 83
    0x4152850107030000033070800c600001d02d40d400394440d4101c540954460010b4148076200d00c645010790b0602400740107450b00d19007000031034a1419030003c0d00d00c1c1d4010b00680c0e28125005c08041d234110307400c84008d6812501d82e5040d80304464012114000d10038208000c12155085a03500007a41890150a0070b0301c1c0201c4602c2288542007801e590b0f050343e4014002c000c502400c080c00351100c00c840c4420b880d044c502806055050034106100454580001c2100300007141f4000b54400a401c90f02031807080021503a03580740080e076501091810140144e00b510303c040e150080003025a66060086a001c101c14080c3c20942541c0030581c41c500c15080c100240c60313540c02d5000300e00414250348204843c10340290f0f00000d258166000122301d02621b000c3d6031181e610644165880c101c3d1000040182d8000c0081150a03400004440d80113500e91040c0e545070380d52600054410005000242e001c035048850070800026198250300c2890f8058842d603061696281e141401806087e2010f414140c44100c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 126995917 1250 126994667 126994687
    0x30f0603070e0a05190c080f0a1b120c03020a090605090310020a08090d030614090402041523010813061a0301050901060609050609091305010905060c180a03080f 71
    0x318a1020740302d6610884820700c1c0025850014050035a030991700c030411030040c024244a50b0040d0076050340740d611084034a440301100043d06210061804600c966a69200e0414492a42c2d60381002003090782c0710f1400c1001240440c08851030f0f010527034103043c0f0400119500b150480b48500884501d4201191121100740202e81003003541000b0340799452000a41c01001c50704803070600e0040c1b10000440b0300641c2c03168026021103546006800344034030942c0540c90319141003901d00d50b001384041c002180001600c0007903c10000250000c4200180303002501030128600410f00000c1c05003443c080c5040d0034003503c4031419880304031b8090b01a5440302d05648807420340d00c084d4070fa1190064001c01ca2490100b0003103001340389078092100040c3c1c3c41e8000080074540300e010745203600d00040031803807240c0385e20444140304c80c0600d02c11030b029501c48248a000c15000c0c40401d100700c1049580541e2100b440c01484200c0120140d0305100d031403851810310214800c4010341d8a48850321000b95a2502205 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 126997167 1250 126995917 126995923
    0x6071703090a0b040c0e062b050c040c030203011a030f010501050306010c12051b0c0604091d01021c1803021b031e010204030b1303020c0913081206150708030f0603 72
    0x5010f0214143c610500007000706401d56581102d20b420034100807504d8120030048608074030101d0000410844130f44000c03586000e042c515425101e10111030056400c800400e05031210346100b80c1c0420350200040003500703000c0d1080051890503012040c503500d8444420707048140103003d000d04003c408000105940d00520704440e4141d00001c00e83d00ca091001c8004010784e209400e500750488203070340340c241c1c8a5000524140089001072005003001c0c200350b00c0700c0041080b042d04a0110941c40e081940300702c401e1005220365550002e80102140c600c4040006076140c208c040b5080c1c00740029800302090380420500c40c80f009038a01410403c1e91500041d1800100c424004082a19043e090300510415070007041142d11401e41481c04d5a20035151345a00d0400140c00740141e040305014008620307110f03841d954480d907940301001d4080d245480f008413640141031042241401c0741c00b40708007403a013103072035100725070007018210b00d00070007581c41c0b0352140406444144484da0a0010507820340c1c5c28 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 126998417 1250 126997167 126997183
    0x3120c0c02190302011e14030601230711010903030507022e030e0c09040209070f0201060b0f0c01050f010b18030f0303130615120305031003021f030b0607170309 71
    0x307110300c00c184108003007900b14054500c002c9000c1280d04d071040d015003255418501c0250280d840d40c4c8528480019211314a9100800580c100510300d40072440042010300c50845010750301c2d6405440300c2c803d00d081205114011080d0303060041d0540100b002075400412501d0300c40d81500e8003080c04140c0d19402c1e03507142c01e503018018102d540100d482c010690640c080d640c0c40010b0b000f11804c4610800900854100030741d006508002c40c1c10005144078000c00c2c110b00090500c1c4000201d06a5400810700280c103c000c0340d1068400002e41c40040280901800c1c2c1c02c80c00c400a0b42d40c0c01d5150001c0c4043d9407203046035517040f0420804803240c1c640e40501c00c0701c200c000000c01760703562807801155140303840c0004941100c8291405900e601c09051700d807155425501c1c01070340c04000b42c40340d4a0556030b0303400081408000c0e545400001c4016210004e840641b0b00440d030003104007050304000a0291b4107441d07081401840c9c00d00001d004100680300c0c110360100d40c03110f1240c1d00d031240300c9a18102051 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 126999667 1250 126998417 126998419
    0x1050918090312061504030311070e010e0105031b011b0c05040603030309020a0e040213090f050a05030a0f02010905122101030b072709050c07021809010b030a03120c0c02 75
    0x804810080e16820100040c01007406003002141280d44180030040410040c540104105c48140300c01d00000b80910700c03001c0313000d00b149c0448120079981c103815120128240c000754220080e1100420080c1020001d40501c080014035080358480840002082d9013411444480c0355880c40c40f0110501003548050b0010b0070010703106002c40c40d201d043c0540509801c090132401034034140c600040b5241c82200c61401150b004147c06c050207041d0403400f018004045042d51028510000b103400070303c08002000290348190003854032030540e800040c150944926480b025641000d41250004001250701381707450500480c465202c0c01140690802c0c1d14204440c607406518034800802800210901a4403030a000e40d9a01c4103201c6940302820410484000034001000300c0000748131021181d044664003041c01c000c020b00309000c0ea00001c10040d054100c9400c0b62100c0000e021034000d00780100807102d1403d50041181190580c2c0040060b20a00c00030b4144946d00d0760004000c80c891841d43d041150 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 127000917 1250 126999667 126999709
    0xa090b0d0c0f02160e061c0f02031e1002070c05090a020c0610051f260103020a0b1e0906070606030803061014070209040f02040905060403020d170105010509 69
    0xc0e150200d4006041c40340105020031040403085100c81d10008225040d40210114241d08501d045070361415a80701400c40c0e9446054002e0011100f88101c250001c82d43c002d4101c81d0a000183c0140b50502d400c3e041d520328148049081023049400c0022035030b115440911005a54140300c2c140000c1140850b0001a4049149400d012994000f50040c003894160302e0300707650302a01c40f40140d5000b04a00d109030340d003081192111140200030b141c401d059404850030000c07001c5041e07404203000d0280540c5080d40450002c8010300540c2800341150000d0480d5440092a0103c18810120712300703080100d040400000040340b9002d510307a00d0540d0405a4030400c280a1f86860f403800040c20b80003250356038040c41c602c0180009035481002d04444030b402e040c0c082403a2081540920441c100010b109032811400c2481000c010b807210f00c91f40341d10700d0003080600705504042c9802030600a00080c06001c2003200d40f030a0201160403400c090440d002420220365404a000100302508a40420321003404 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 127002167 1250 127000917 127000927
    0xb07020a090510030c090b010f110c03031b010b0405010602060c07050f031216020d091502120316021002030c03070c030e090411010f03020705060103020d08130b09040e210a090b 78
    0x25850f0344900d03090302e1150202a00007612407101004a901c26039142c2d000030030740d118020345c60f40103280c000d01e01d070880026111004047c070007003071443e4400603036140584d004c0742d20854100c0080c49100c000c00743c2181d0522081d45807800080d601c00b4060900801d5050015418040047c1000808480840141602d8484c0080c0d2003008454704221200301c0301d0120384854403c0c0ba440400d1a0021102c035444102145042c800242803c8103541d0240d010361080d088038040c0ca50454000c0c51103401c8803040c10400b0640c0c81c2e00241000451000080c13414014400e21038036640203000c0e6680404140761620310000b036030074119501081503030381c560060f420600740024040740d2100301003503010a80b14058801da600c03008074221300c0740e040054155000600140300510b0440c00342d04501d40900805820401039001a0b005540341d640a0300c07040c800010050b020b81018021200301e0020340c006082010120050209114580800129039410003e01d80c000c090060600d54090320b40d0508a6480d0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 127003417 1250 127002167 127002181
    0x60c03040305120a0e010c0f0303050901110c031b0a0b04060c03020f03090a02090106020f100c0306050a090e07090b030309010c051e010605192303010f0e160905070203040b07020a0905 81
    0x44e0788602070400006000022804465000b03800c0114000e81c00203100f903030310400e5241140200405400d0420554072005564100d8180303030082c04060301c00340d01031507407402c00f42a03400125684103060410b50b00705880820100b000e07610020750082e00aa004543c043c01510110020311402416684845011050040c1860006a64000c0502c2902d007600280d8941c1d030280c1e07855043c100e050b140ea0340071600314806d04602c4c1d00003011014030fa080102e5255220320000d0b589120b650030103100c031503990b1002581520100641070043c00069401c01204107560b000c26141d110b40c5485605220300700c5020340c2005010842e8a01381243c2101c0d44616010050710301d4080c2c0080e22400e40700d40803400036248044105124031003182d0000300403040c042c0e403440300036126207114107405038075543c1c4402000c80b19030b10340280049042c115000e06034103070744050000301c84012600f014207401d16100400c404540c001044a054038200d503178094035404107200240b408180368200c080880c0c2030a00380824 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 127004667 1250 127003417 127003453
    0x20702011b03030e060703050610031d030c0a0302010f0b0d03030e0705040203010f0801060b0a0f0c0c090203070801051c023106030804061d0a0b033402010b061602060c03040305 78
    0x1d2040410607031718941c6030602d0440695100351100b9510515040c10030030041d00a0703102c0041081900c1510360074801c5c8400e601d041d80c10401400c04503030800d030080380806038280710b40200c0103041c601c208801008035010500012070100300500303142d520302c5064007903201084642c0013424000e000750b54075030319a1501c40418005100f10881c541c00c0c104042854007810042d2130303241c401c0e90f070f035841c000c0c00441080701c0c200d210755000e46804212400c040741941d49400254422a0307151520101540b52000344410115460b8509030a07d000d500250010f1380c07840c000f2581c07410456014001d00b0b0440761400c0f55411410790103140c2d5468800e0000801951801030700840b913441e1602000c1034442641c14104114038001944d1080c0790300424001c2a0ba40c00103950055902d202507036800043c1040c0001c10043d184115000e00c01c0485c4180355198240070300d80b0500e0f001d0383c0d92070600d04a9500340c2401c4003e880024811200800d102014000030402e0320003e41e0081d084620280c1c58030b0405034 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 127005917 1250 127004667 127004681
    0x60303110d03050408070605060a080303250804050709021e04030507030203010c08010803090105160501090609020a06030e0613020402071703010f0b04051e01230c060708010503060109020702011b0303 88
    0x100394020400240c44440c0a4032801d4411500415614603000d040e07a07881d40200710060100380d10004560010920f4001000594491205104c005555580c10423540402d1150300d40e03441300304000c80041000141d40880d403030046a00c03220780075841c0d030f1001c6c000c040c105908450030b05841101280010601c20002000310869009800801c02c06110740411a09aa0240150b54641c2d004100740c54240d4416001001c2d412191070130a111640e0582e509401c1d2140100c050761015200c20700f00c0b0540c900200d2800042c0301908040110100740244c541d214080201114040403100a48406546441d01140c2c0080d42c0540740e002800d02e000308121a0b07401c203004d8a0010f611404010940d04100000c54055420040041074078048501c2900034040c0c14a003401c0c10000c4441d0720841600010343c44003480801e0509580c1c54000b040c03561403030004001d0440c02007101020041010352004502d090544040f40350160740c403280380c00160396405402c5a440c1000c0c89020000d0249503065110b21 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 127007167 1250 127005917 127005947
    0x12060b070614072d0e0411071101051c11071725080f090d120302040608090703031403090111030c07050d2f010609050c0306030f0607020a08031801060303 68
    0x14040343c941e120100e403940e0011000c071502002150301d40d0041428010810080d210758500058009450008107094400c036002c0d2011802d00401c41c001041508221108402020f1130140e043c080c1c2c51136820b01d01c00c3d04164a40d5070716a11003440060801c100304842d0300f1900300540360b440307240d5003034540059440a5101d60380c81e03240c15840700301d078050540940b00e41c0e074015207098103103141c00b031860f0a503910424120360311590004440e00021481907a0104440303203500c006859a140100c040c10540c002010300724503400444c41400007980140030094007244041c41d031034a0b50756400c1d81c90300500321240150440000442080080802d810041001c2845a4161050316610107030584500400f078000c245061a94112007020390528181d801301421100008148141d5600d22502240d50988081031400000070801c00d003414204580400031782e0400080c180f0740f030080402503c2d02106c040081240000001040205200090b1510703114080b50080001c42d540385806005605000846 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 127008417 1250 127007167 127007201
    0x110702040507080106020f071a090f040905071404020903060a020304021908060115020307030f030c020c0402030f0a0e070b041401090503061608072a0201020a1205030613180312060b0706 82
    0xa107c001d501140080842d03044503030882040c11410782507130140d08802d008079046000305818100594860143c0000740340146d0107014168101081d10300a11801e0b0003d41c000c43c01003092008940b00016080e0b88000d8543e001130316620740d4400503a41000c04590101010b021081c003290145011074064101d602c5404040702b8a46103090a84c2c4a0040d00c1020340072512580c0b02418041c000c1d00b2810840b00340c2c0c410b903a55401c1440004049800c16255140054040e0080003501500d030310424001ea245040104203280c5000a20891440b031030052200c0041e0305040002c19902540c0d25002030300000f800d4030081d01d0b0280c5e400a40e5111401d443c000111b1160200311a06d019400d038030307000b000006a17850640c04440300e01805196440f0300f00e045204045000c0045103120041141001050340d5040e52810003008000340503100903c1e41c0700c031504c0c00300b00c1c6009500d620440843c0c40e9042c100700c1049000350007a10018a19513001c0c0d96255000600c0c00f040140320340c0640c180c17444261301 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 127009667 1250 127008417 127008433
    0x1080601080615010c030e1201060e060a05010504080303010909060f0e0102091509030d0503130816060b03010231030212030d1803090314010f06090f0e06071211070204050708010602 80
    0x202403080384552080c3d40800d6404511402082c42101c5015010074090302038183d001c0c0242c034040c216445580300490045003482400014940140c804008107000d2034004d0820781480200d0741c4900c018864401c1c0ba81d071780d220740403c0213043d81051004040b90030f01042a10103c07040706010f076020310303181032240c941404445440c007a030409552201c8005002001c01c0c002c0c904050320f4951001d01340c612001d0201200c600060310700c10040120b10f8500204505034207003854510256a0511036041c42030b4011701655114500751b500c16030341005400003000f95881c10701d08800c405c01090301f029410041e00400e01c03902050000040101500726002002080c246c2120540403a00101e0010001585090700b00085510614071307111283d80e8000009051100070a51800c40e403595004240780c9407034840380b610054541c490b60031301079402005814a460070707810090040921103d8000c6e25580d907110400c010b4200320940e41002c0e4050000c2015050003100a06448424424540180f007040c031 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 127010917 1250 127009667 127009681
    0xa12170609040c05010f03020c070305070e0901060e06040203250306141804030c0c0f080606040507020f0a020118030b0c040302120d05270d0f050d09060e04020d14010806010806 78
    0x54102e108940000c0c9000071541080c00450349158000b04c94000c05800348440e801e02030301400a100218403c00c010f180592410b02c0301c0702903c3c0c00030413280540e407409200b04509020083c2d0194001e1048070b00581ea90741d00101c16140905145d131074840c42031000b200054083d0140d0040003680d1003058003440400a43d0100641141c00b5601c0c000261420703c040f40c0003d01445640c4440c0d8030890f9013081d099141d00410101502d40e40c4520540d5005405000703150405100b12600700341c1030310261410000d03049046a030b80e91b500030020304000580c40d01404000a101e0068055580680c030180941415000000c55070010302007a8440c1c58041c0c2c500b10181b0000403d0201c0320b201e41c40f1503003840c0700e58008a08041d81d400b64041107030b20740c0c00160029500d07210301c0c0c24014071a1140c000700c0011400c0052800c01e410001005100d1803810a011031500110740d0400701404580250b9191f0403800300720064034403001030b03200c580319500003c20380440201301d0344e0507116038004894003990761235 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 127012167 1250 127010917 127010929
    0xd02060a0902060409150b0a032301030b070c0501020408070b0d060807060f0e03010924050609150d1703040807030f03110405040902040b190f120201020607110a121706 74
    0x600001d43c0900108030801500d41da541010500c0d652204089000a60725040f4040e41c0d8800b514120001e40d0308d620b00c2450030350318904a920750802c05c0804c0401d40c116030707400c80322040140214060040a01c80941000710940403a4040c021400507035001a0391144900116082100c03110340150401c40c1c0480d000000180d29401c8400a541e8440c1c030a045013400c5c3c600751000b80302c80381c155407101c1410000c80c4422034a002c907901078000c05001b0b101e0b82d803036002c01c071240070b400b49208038058000c0c420107500b003c12074488034604866900440300c00d8503080e0500011941c2010001c58003000300070a0010800c003030b0a1190003903c40c07100d04103001c5403c808032000d0384802240c00c0020703c4180018209944144a401c1c40940002420f88180d0001080b04000b180e01c2500800c00f443c081c040000c4511010f4010b0040f148100010b600d560b0010352502c42c0281040d017080040700d030b100d4941104100424042e0341188045c41041c1d40250300420a4050000e4601000f6814000c030f119400d041c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 127013417 1250 127012167 127012181
    0x4090e1515060d0605040c0e19060806010f2c130b01021b010c02030109060b10020102030114060c07030804060c0c0b03190e12040e010504061505071211010e0d02060a 73
    0x3088035000912440070022983c00c060300d1594010342c0d13914040380700d4541d84200c1985400f00d0310356828140454041100c040203400c604448442d08032010484d503500440055000082400c002408400184040303d00580344030310ba00003051800403151076004180790280e44101b066984003c110700e207003008019200944c0d01d845c0143c3c0300c1c00c1540c1c030059140483e41c18072101450200b02c209100d030006030951760510307400c1e1595640c405502044c0c0c94900395060609001c0c1c0000d6045600d8203944011224403044000c0c064040040d16100e81328041c0002006943d20004140d00d550301c03444000c044030610b030700c2110a540e50040102e0b10328180c109507481142851240e141c084075003c1c280780903200f80d941481540c4191502c2c0d225083e00b600152010b88110305041955601d01010801070b10010b074000e0100b08100d409a048865218007101d207400c0d0031615100c400c400500040b11540c2003800c42482c554a41f0b0600d4100032004035030040c0d00000c03542114481c4e206d10100c4021a421 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 127014667 1250 127013417 127013431
    0x12080603060f0c030c0705061f050301061404051b040806040501050a0504050303070c0c15020309090f0402013c0e01020c0609030304030b130501020c070f06090b03010e0406090804090e15 82
    0x20480081d800f011404001c550005038800458200f1581f07545051800c0300039034109003601e10740c128928160640140500003408201c00030301c10b40746000c08c540e0780008003604140c050340e1030b100043c282000c1d9030540c50381d00640b0310340940e44a40e42c20390035440d1741060b101210b0035400c1c4004910000c09074020940290b4110000c2c51071354542d1401503940340904801181c40448000c00000c019542942089920803107402a5558601010400480c0c5030004c0c90340301c00450020511001d40d9100400220140040c02050108018170781d08402c000300c180822000c113094030354840d110680c86070030110340001c04e800700d42c8400c907032108100b523a0048450715901940144810004130b00ca610200703800c0a6450511407d18000780c64003402c0e80c0c82591b01c80c003e50300524040007110368201d80c607030050a003441c00b11489414800d100c80c07248818410900e0021200c801703d424401a81e02c0b420b08582d02c200f0042da07466450301000c02800c01046030f082140100080206a40f1038030000301e1003400 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 127015917 1250 127014667 127014691
    0x3010308040303120902130e0114100e0109020c0c01120207150230220f060e0708070501090902180910090605120a020114070818040605010203090a0b0307110a1208060306 75
    0x80b001400784001c00c0e400d0b01400049d0b4036060b00c8090907000c1049c040c001d07180d0341d401540d01c900308894180e1041040e41b2054081c3d10411401b100700b1004541c1e450708803001d117405401000700c1c5c2c0d8103101034050048080c008900f0380e103800c894400d065004005010410500d210302800303015442410080b8000481942a45c12000a149071140000d000e8000034101503d0440f1003d502c5018021648480032200c066680340243c000d4081044898020004603009210803810840000d250b85464410304003240d8001c00c40c01807491099a0a6801a602800c0e41c411031518443c00110900710b8440c140949140400210301d43c00c01c0a503e8103500400300003042c0b041042c1d40115000c542090031294000400e00480c000510080010081000440401d401001c0560204011100702e5400b1a0644d0320030030a0500348e032244100c000481c0d2801820540b250384980050314007107505c00c6503042a000361318030f0008000321f00d81070111082c1266900780c2242c3e142c0c0305042d52000b0030345100012403 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 127017167 1250 127015917 127015939
    0x2062d010303050c0102070b0112050c09010b090d1e0302070603180b060603070912060b01020c0d0b04060b060903010c031e020304082d030405061806070e04050c07050303010308040303120902 84
    0x1a0180d00184903c49404c0300052901c00b15881e81280c81c0303020303001600f0b0818550030200030300c60200408242107070101c1e80c0b08901c0d494001c03003941c18858294060300a00b84040110180700e010884c0c08504401803c81c516040c042d80740007901e030480ca000b031070042403420644441d0380200e1001851250b600c084030b868682c07580001c2050b070350001011641000058080459404107a51011a82c3e42c46100007240f01c1200070006030904800000c042c0c01440084554004500218103480e00a504030000080321100c40003c50311922416a100d5015804c4c1211908107561642c130411204010002aa0350180c9844281c01a44030a82d4003801d818028000d21510a4603071422100080d500501c1c0424000c00b1418911250401c072002d071a0307a0410303420080158030b0041c20003903200d502c90103480fa034508018050202000650307000d000310390f12000549020610070440720440d40120807280c0300c1d81c0d06c0c644614294482c3c0000c9000800c0c00c0541c50882c240c5004000c0d00c20b0303006207094181c0f = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 127018417 1250 127017167 127017173
    0x60e0a0905090d050d1104030f173603030301060504080610050d17091e01080f040510091a090304081e0303060d11130204080c0f0f010f021c02062d0103 67
    0x103174000c22042e140c1143c0d0307030250502e9840c0c080010300c011840f404031901c42c0c903d00d0900421022140d00d607100c00c0d40080000b40345900340f180041c50701d4440707800c40c800340114194104000044d003031026601440008008900d19401001070003c5400c030b001241c12940c2d401c00611190000c0b481041d030030006040d003040000f103c00103422030009110815500301405240050300010746044004685051851090707042d5902503065035008481c560a069a8141580c503155580c0da45e0500b08403259503501e101c0c0411050081e203003a00f44006040f10b1550818407420b5480350703c03d11460500c4c0c07140303034010303c801c4003806c0c44d503951181c005002c0d50071695044140030313038589185400c030b13071001101d0210700b9941d5943d20520b4103440d911200584583c10400001e1a11445c0d00200344900c51192000d034135940c9030420641b6450080c40c0c030301c0c101100c0400c02da141c05000803a29010505504401e100241c4c0044d030944200e2510034214082c3c801181160400406101150180c1000d200140b000c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 127019667 1250 127018417 127018427
    0x14030606060304081201120201080702010902150a12050a0c0806011b03120209130c0813050307110102120301030515010906211707060902040e0111030f0c0403060501060e0a0905090d 80
    0x40913000740d10780ba140000200c42d0070815642604400003145901c0d04078025947c0c05850150310540d90b000811061303905400280352240542400c0064131000600c0703010700c510a460081c44030743e03d110306101a08003004079102a2814206078000244c0b03800c0010003940c800c085202d540000611040c1e000c0801e610110303552044e45200d0074a803030b000c0200000310b844480c01154441580440011a0520b508000b0962032004d84801c1c03030400c09055a81c045100842140d501c6c0341d01500f91150704800c800180d0402541c61110f50003660701100000c00c0c044003081c03c1c1c0744214929000707600c42c2e032140440000c5503240e0040003028004800c01500d940c510b020748440c004d001e002400e445000f511100e054a07488004122900741e00c4104800460034107000d41c4810100c0d0300000e0000301c5550010f99041c0c00010881d00d2540c0d041303004920a2031061085801070b5400240a000ba981c60b0400039003842c161060780d074091104100002459404c46c8249030007800220094a0b41002800003110 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 127020917 1250 127019667 127019671
    0x3040602160c0305010e0c100e19030209010308040906060822030c0203030a030c030e0a120f0e06030a0203070e10081302010512070c030f020a0b1b07020301091b140306060603 77
    0x1100e00c0128500e140814005402d200c0114442c400118404e4101d8082c5414015201030b0b82d40900f10b400c140360401604031040b1042c410098601058010b44c2d22118000c0d200c007a030002c0d4116812900100138026040020300503500041c10600086950300000c56452030b08989402d04ea041001e0a012504541651006440c0c06031500c1d0a2405082d000681150312038264480440c0e40c42c000f001200303030140205000204180040d03c4c9081050701c940c1c0030420045401e500300014201c2c0980614040e01040903104000703010381e81c40740340c00c150500085d031007075501c01301203001680c003020a483d1024844051401c07903650b881311511650300d00c90820427540710403030601c4010b020510903895009039841c4629071301d136140b40103454141000341c85c030b11204407182c0842d00b003040800040384c2e281c1c000a400440a003540c0402c1ca001e41494583c41c040c50100940c15420710b1090070600128030591500600341140c085d2982da40c0340080420700d8003500e02513030503030040000100a0318040c40616 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 127022167 1250 127020917 127020937
    0x20c09160509060c0c130204050418020a0e1807060f080c07020a090c02010e150403110d1704030909021c0605060408060a0b0a0302150316050418090203010227040b0a0b03040602 78
    0xc1e195645a00c0003611b540d11901c4441a00c9a01040030070482c0361034000d15044c0c81c85903209218215140d00441c40c1f1500c41c2c0100000c4040030740100d202644081080e0091080f500c00f031315031090b00d41034014005070101c05203100061800000c00d08800d00841281e8505a000700040c04003032a20021038050071454180c0c9040d95030343c00c0b0900540c1e9050214414607141c48a01c544c4a14107442c000c0c044104062a400b81a4008108070b6a51a081070740e00280c810760401e03590716039a1345d180403112041c03207420805400780049607000f0002c0f00c00e401080d0b190541e1000b400a26255014405180120302c250303802c0c6c1e8041400f080110788550310440051001400403c82c054494010170100194003d110b1041c5200008000c842d90040d1105005030b0494900315180910340301145024291101824124030754402859003190383c254101c5140d49094030015403204110160000c03050b16030045540a42d04180120269182c1511aa03054600c1c6170351083c20340c0c031580c0f03c000081d00881c401c1 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 127023417 1250 127022167 127022173
    0x3290624160807021002010507080406110d110a03050106030209010507020d060e010204060801090506090402010e01300f0b04020903151305011e0f060e0703091110020c09160509060c 80
    0x4402030440441c401e821901940750309a0f290014410b000146000d90080011a407401041c417943e0390b88203240c180c01c20340010000c2070407070312040c0b8680c182c822103c0d90000750340781c03084008512644201504802400e601c0400460703076548800d9081c0d01c103440b02030b8005881006140010716180c1100e41410703014420001d10210510745d450700b240e209401070301c082040440108035220560003510b51041003600c04d4801c83c241130340080d0002c00b00900082c18017040036803201004064185003018488107920043c1000c000c0c07914040202020305010042508003184800076091a00850314070a070040c3c010a40c4020130b00301c03030014a0002d8044501d90000000c580085142401000c11203d00000380090402c0b03884548400c42e82c0713100e060000c15041820800210300c3d03040c61142e011106050100e01030307585141c000074840c15115102d9008155016000000703500051240b0304c0c2c1015514030500740c88078407440b807032a01e140080310000b406c200080c01c024146031000c0c0030b01c0380c128811 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 127024667 1250 127023417 127023427
    0x917070b070308040516121218060f120905030405060703120504030203030a060509131205071b0e0c03010e070e0f061611060c03030606090d02090103290624 69
    0x2500300c056120750740503070000d05614207000a0013020310282114019611101070190719049403a402050b4180e000f8050942034807110042901074020f524013401d08502c0d020520751100360141c01070269500b01c07400140002080b1251600a00c2200300194000c0002d6083c6490031080201940c010039048042007d0590f46d03000c10841400b5540c0554840d801031034592800265090440341150b112610501050045c00a2021122040d009284e000080070720204c10704031058503180b042c00e1004003100950785800c03042d0054a020203041e07450000944440b030311610395030344507400207005010300b812081c004207143c0760040b048461082c101500c41c035076204800001416640040d000e1042804000846208014051590034035a01003209c01500305144580d41035642d00004103100d0141600040200e016503e0400c01b100460340280507035203942e1203180580d154401c82181142041c4642d80e06901c3d45004101948944006858224808500400389080e080c1d884160f03040301d801044 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 127025917 1250 127024667 127024679
    0x290117010602010b03011a010804021e060d090605090309211203010b1329160206031f05040b10030507030f1a0f0405010e0c070302030408010f06080616091707 70
    0x550007080329800000e800500d030030505003520042424900001c0031442e000011b41e030000c0310281c0141e01a100c0380014620f507a0056031810b603415200d640000003140380700c2d076442c040d004003042611031101400300d9180c1c4008556203002d170381c402c698004540caa509842003035241d80312024480460845a04850140c40840164001e80104242c0400010107104011140445c0030050885030750140b000d08150b10001c0205400c040c105002000020f40200708014005c480400980c000b004c0b56500d080c000310768600e030b00134004554400070f402140004d0f03c0c6040d10680e042c00d0005001220b000324900411002032000400384000c0c50764491150252101d5845841e2a80304080a00e0100d807903010104040444812102403260f0705000c0140f082c1d80310741d5811a040711060082540b00c6911307150990450089401045443d0b1138003120400400d85504450201c0b0345003030a803152506c0740030000c2c13860100246036001081c0a810200031032400095034809003091142524490740e2511 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 127027167 1250 127025917 127025957
    0x30a0b0a090605120f0706120906020315012c060c1501140a0803090a090914010c050301030605010806090a1b0b130603110c0a030e04060e040f11042901 67
    0x6044400c00554a07401840f40341011048585418a440000d124044100e001d150b501c4409010b54001c0007403c00d140d080c003140c550001301c00c0c1c5a0013041551640340c4618028003448511100900041c222042d8030580b041f88604d20181e000752000c544180005001400b100754810b4410060314850324240e00080685d000c40300c0e019200c4500541c03803100c0b000c0c04100c00c9200c00c0d04100c0f001c0d0001c0010404545e5007021410441d09002d8020640388018108400081e400251105495080c49205122554450000d40c140d9101d55000c0009980300d842207590f4000c03c481c2070b5800da1110b105000441e1200304850b0031502d2180411100ca40c07641255038503504660048410f502c0c84036024415140c041c001d4441100b0310110f5a8142003a49502e150345550074803000e4140300084400c081e2a07100d41d0004006001140440100307406c2c1451300707002201000b402510039204240800589103080d001c2c0e03c1c0d45201003042047d69801040b4102d245140c125022418041200b0087c0002102d0f4 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 127028417 1250 127027167 127027169
    0x6050f01030212010b010c29010b07060c050a02030304060b0406081b090f0c0403030302030403020723040b04060f0506030a0b032b050304020a060807020705030f010e10090b0606030a0b0a 82
    0x8058185500c0d4034600c140584080c85660440240c1d0402040b4020750764042c50380410690882c8a04200508640303021078020f0b00803503600314502807040082100003601004000c2e540c03180d20100301280c06180c00301c1d0380303004003446038006800800200c2c0200f0303ca50055403503503000900000d1056568081e40e46007940c1c0400010455200d64051561440c1100e07015034010418010f101492404810121080c811408000c06159020003c10241842042004040c01001215914200006500322003401e600e440e01d81c0f20f68100101000e041c1810700030b10045540442c002450b040c00d0208100f035030740000b82002e10303156603860198034569017003051448012780c00700d0b080e034501095100f801280f508a18500140b10003042848016140c020148044408510b044000381d180c02c0030807800c00700c4c9c03603120b96454825040d00d0f098003081076004982d43c2d10360314220744450218080706000c0d00c2802ca40904002c1100001a00c0c0d420300c0d100030350380498507600c009160804000040ca601c14a = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 127029667 1250 127028417 127028431
    0x40f0609090308010b0a0503011203020f1504060c030b01020c010f020f1203040b01060c02010e040f150312110c031c210506040501080109020d1103030705030706020a0f090b030a1104030605 83
    0x10759500c001403603000600c035409000c144060a24100c211031000d000f46c401880b40c190b85600d4070b040a401e040c400d0040c5c441c074034550800d444e41400d075150300801d401c1e424cc42c11b82c0d02d2807511841362031b080d0080c03007020441d10040e0041c00a058071540191207008014403000c0a6001d4156500044841400703401d07a0b0048141869880f410241000c2c5022141600002c0900c5448400000547e8110301078150100c0210740209100402805400240000c03600065554008520100070040103804100c0b0b03521041d43c56103407003451003082c103681e404503410041e05274112002c0c50304030414014482442034040d051000301c0300c0902052140401074402290b94641d82c603000c0c04160301e401c0c040c01c4c6c01440e010009102c0d0003803a030002000d21080c00c1c0000c1c110202d092034030170340362070500030f543e040394010080d0b039100c40c0301d4108040a0340c03182c401100060200c08143e90720b18000c5159000790350104003aa400d41c0d541c2c20840b401001c0c1806c104800010500c00040021643c0c056140314802d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 127030917 1250 127029667 127029671
    0x1090207032003040b0706110705060402040c030605130c0e03030c0c13090206090907091d0402100804080301140f1002030d050708010b1e0903010914060601020a0b0a050402040f0609 80
    0x140d01d04009008403500542026441100340300749000010001c180c4013515140745480e90340b00300c2ca2400c540141a61b40000752440c0d400304960702440b4002c201036114600030380d800c1c03100400c8018100c0440d40c03140030b1a54800764501d0320200c2044d143e4060b040900765800e024107145001d03000249590841c001c1e945859102d18803902440c104055031408140b80f005040c4070b03942c8143d000440740e000705030140d40035201000c0021007180c49200d0f010024000c3c1840c800340043c003050310038403521007190264050400c8200000029204e018158801c035008006c0b182542d003003e96600d880c0001102c0150702c402c1d00c02c21403050345e48503c0050300d00803541c1c0003141e4410310702c83d00005440c0010030203401d128180c001044416010340c22141c00600224003456100c03992005c00d081405407a1b0318030f4140d842c0840708020451007001020400100904640f09503444000490380c0e00d00e04100105414807800c00300701e8500741500241d400c188001d1001c00c44520001c9101c048910300c0d8840d01e03800d5 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 127032167 1250 127030917 127030927
    0xe21030301060212030c160201091e031a0f041b050a091407021b101b0503030603100902010e0f120d02031314150f1605030a1202070c2c010902 63
    0x20303804200e403903103200c0d1304400b4504500c0c0032035803c1c466010f590040c04001c440c40e030300c10f408c42e0b00c650342e44030182c001c1c031410b8007003000e0105c00741c602e0100d64002140d8014021070350145134001c4090b114454610900324410340e644698424551005131040c080510495680100d110790310f00c0900d501403c0341c0714000030303a80c40e02142401c1070180074084500b5034221449109603aa110050b501c0f6003070054444203880311a414046a4505000c84c40c2c40030300407034241c00010001c0210003180500d2080307041f550503513641c1a5010403102c2004000b070214000320211074076410700c140d40a031416002820240032204280100b402d180410b0b864200607000010b400140390314994000003d440c07010120b0303150700d8050002c504144c409160715802c5006c00303d11b003518031018200300c5002d20350700c42c1108030885980c03801d940c1d243c0103a44d02c50041816111003206034903441c400d0764881d503007243c8640d415030700e0304003041d00a030705000241440d5105405003030030807031001d1907260090043c00c00050340c071 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 127033417 1250 127032167 127032179
    0x7060c080f0f2a0d030c0e06031608010b0406081603020c1e010c020f06010e0a0e100203010504062304050a020c011404020901050a0e0a05090a0605190f05060607030e21030301 77
    0x20342c002105503002d20540f106980c02c810f00015a40c02103a15505000941151242080d10400d42c0c0018a540c4100c0c000100840d6050500d0072803103945064603a0070f21a603c460b00e10044c4c0c02580500360001d030f0094001108006080d0130030b042c00304c42d402c0040c681100c081c2c403d420415003130804024443d243d41c1d800031001c0248600e2080003500d101500964042e25402921094188a5412580020f00100d07450680c1a8080c041180603803084640d5801280f0a41000e90424410320303228503d01000001e0140000035045074030622202d83c014041f0008040000034031002d020500115800d000709514002c0c00d1003100ca400d140c0f4020b0f002a81341c113104010101805801450240790503400402241859038412070b00480c0c00c01e400308441d41e41000d2286004609080030b46110300348014001251010030001e0703201010001c2c180311080084581d8003c2e0381040d2070840c0c000380100541d8001c81e10440d08080b407514010105040c1c0074082000500403145003c81d041c942c0c03c000010041 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 127034667 1250 127033417 127033447
    0x305190302031b0c030a081e07110d0c0f0219030606080307170c03040e0c0f030403090e0603070311040c1418090f040203060627100f0605040807060c080f0f 69
    0x43d4169803840c1e0315100c1d0070758001d5103d0084036401070501c811240803d0000c4a0324102651040e0881d00c148018581050018400e02010080c03c056002d4000019603142c414410300c1141c40d044603001c903044401e0307800e200c8901a04240003541035520707400400059040c1c001c58008066000c0150b031548140d0030407070300c100008075070368210322020410907404100c080180c13022103c04605d459070380d582c2c41c10354844070300c14050b01015404001040200301034110388041c05484c4500d22600d440c1e52040d042c5a65884603020242c04041c0b1a0301e14400da1400c1e80000d1100e00940c5001a140011600609403541080c018012401c0c114840c0180c281031111481d94010b003001c032001c180c2c0c1440c3d004603484d0f12020b4120340c0212b0040c1211191052203640c004a908115480007400d858111034541c4410080d01454800c0383c0610300c00581a442501030760180c5480390040c040d0540342c044181c1c1c01c1e82c18908106c030180024030030340c2c000462020244c00030702c1031a40e10594804d02c2c840d405078 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 127035917 1250 127034667 127034701
    0x706020f0622051213030b0105010c0b0a0209120a050a03020105061903020f0f1f0e0402041d06030f030304050a0c050406080d0e011e05091f1407030519030203 70
    0x4180e004004200c4040b0b03524610700005074a840c4150501140c50400c20b0074548001042001607500043e04c01c812014454000704680c05050107580990304c0341c004644185c1000d001420900420004c01c1213041280d0081492090086c15424200000a501420301c803050034160352541107885103105168080c0038196000e0300c1200c0c40003402c0c5440c2110b01103c2c40b0350102070700401c4100355891458541c0c2c00a0080c04400400100d401c081c510701346e0052002a0b41c43c4400100710554030801c0b42083e0080d2020394012402c50a00e650202416072100a001402685d042c0300300070050380025818002140114010006007101c4c450078208480140d401740c3c890b60042d8603081c803c100d110b001188040003031030103183c4000b03445040d00048641d1070804050149015400308010210b60b000001401858000d860011442601203680d1780c0b4281d14000c0040403604088a440e19007901500900c00c543c13003814881d007000719171201032050a4901e1520408039600005100f410500101100 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 127037167 1250 127035917 127035943
    0x1201150e06130e10050f040606090506031b0a12140106051f08060a050a1d0a0905120703020703050102030a090302010f09020a090b03010b03100c0801080a030c03080a0e010905070602 80
    0x140d0a41844000b01d050101c048202c40c00c0c03165201c1000c46a00018040301c401c086842070180b0482c04e09548070500714806880443e2910701c0c0c04000180d056042c000c1c039203c2d00f0010b000e01003084910040e5046085202181903011005000c08074040c1400c98404007110700550352303000c40c51140c4400d03a003100c01d240c01040c401d416658003040501ca207142441c40200351440c0001e020b454541c081001150380d500450750044034144082500140b1614151054040008001250711408440c90407640e018001078a5504880c105c81070b1400414020400284244101d8681070b070b4a031185422a007041c1c0e03503004400c0d158005c030b0342416424050402080724501080154201c07603400107407400780354812400f41070b40303518000d9030b2a03500398014025100701509035401e40c0b81d4546100010414030003034502060a80001003040b42c0d0004409900540c1600d410100821a48007500c0212006159480b02d645860f10501d29a40030300940f4800c0740720303c00414030681095030207030508070170800207 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 127038417 1250 127037167 127037189
    0x41d0408030a02090102030d0903081909080301050f0d060f1505060a0e090a020f0309010603031709150c0702100c03081620070506070b040c06051206010f0905120115 73
    0x120012816010071290031400760b0400594480c1c061005074198001c0c024040d1195141c800c441e4103242e04428a507114001d018000c60101c403035080b481e0100c80d0780d803401600c040c406200500141c00d2401d1503803070a0340c004040110312809561084141c0e80c8040d00101c1c05030700c903250b10620f021a11b07200c03000b03050f0841d080ca041c00b0010400400714011080d00ca8401c0850401090000c4895411588855070810380da030755030b00d040b00300035019002c28802140060040304800f00340200c1e0b0b0340030350b010352000f00c064065107100304145d109031039000d0300c1801002010400e5000681c2d40f1348185401c0c400c1520703021043c08441c20b011300364510040004890307070344d0503050a42450340b01403030320214500403800440c44500c20a01a06d041c1c05038002c3e60f0040300006809007848000202a403103203100d00e100c5852a5141d210480b0280500c0140b01d48202041c804680d0780d6020356103540002146141a10034207940b4400654126240c1c0301c0c003c0c040c0d65a86000c9280094010081c1c0600b02c40802 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 127039667 1250 127038417 127038421
    0x30105060f130504211d15070303020906040f1d0c0406090605030c070606230307060806040e100501121b03020d17131517010b030a090609020301020a0302041d 70
    0xc20a0355140d401c004500d5a81c07200010100040d03807540d030030038012400c0425981c0d0045c400180c090b8107a921886800369204041070441c1c50710f1070401c1009901d01c01074a0600b01c455409031b0181d004204503d9000b04280008900700484c4100c1100070001081101109a1300da070302c40d1487c0304080e0100454040400040c011103400400d041c0440303c42d890300039603a9640c01c6180c84c00e8055150b0091256090000002e000306075101c9500e41000454414050002a00105a41c0c0e259612682002ca5107143c0005ca8034a011f80c040e0213246800f40655007006031400140040301d10913041103a0524810741010b0034805440d400d41700040402a00305101421600004e1030000001001055409482e15409001c0d1b005800e980c2e40340e00c4840c507060305071307103641d05800c000400d420040700054600ca03c07803a00503101c40d200307412500b0411440340746440e500c8200d0045c144004c0c06940054a940103c80140c600b44001c1c090300d80a50750068407242003942411503aa6800d58495a00c110f14007 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 127040917 1250 127039667 127039669
    0x1109130203120706090203071d0903071e03020a05010c050a090905010f1a04030606080c090a0c12110906070c030501140906070302030411130617030a021005070212070809030105060f 80
    0x81c0c08142c1024105140e458100f80d1a2000281c84034250081d014010b2400c00519100391170180c440204140382110025540e150070700703075a4001c62601901c10444400908540070004a080301100d000b881a200240040e440d22402d46020304c0c2c00c500050000201d8118003544011014007410107446c4c00d102c59494408035260700e01050240c81001918409103143c0001407008550045600680911851396125046902d45900030702c0f1500070480e010000300080e11034031802d0303c407521a03200c0b2041600f403405100018801c3c2c8400d4000d6003001c100124841c0d40b6030000c0c04e1581d2042d03020740f03041811898607a00350fa000e807149000c1c024070b103000d00501480204007164403140030700d001030303ca6907141000c81c540d140001c0031a400c40d461a00040305826650000d209030764007411501444c03e00c10030322a95030300c1102d031100f00503001250041d140324070a1f00b200b500f100c040e2044908184604a1840c1c00e42d12a0404980424000440760b82d1400d013801210b1307020700c0484c3c0c8007a078001108 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 127042167 1250 127040917 127040923
    0x250203040519120b010e0a02190f030608030c0105011706281808030708010f080a06050c09060301080304081c08060907090801050705040311060304020d120201020c03071109130203 79
    0x200400d072150075440090300098104403a5035000344090359102c40c050081d030401c1030026101b800303901208602c000000e110b1070014002c40e40d00d0b10200e00c1d1828205440f000803109041d00440c184209a12600001800e401c200060f0240201c0000002703180e501d4045620700100500c10408401c0e0055400c000001d024403600307405500100c0603540e61402000340b120000c000d0705100c00c50b040b0a40c80301030240090540603610412507601d40442c0341e621341040380070700d5a10b445100d0403036020380d51540004c0d9441c1c0040b504100c05e6011203040062141c0080d0f0150403d8201600d0340d800810708010080040001c0080840d68103000b440d40410b0f080004e01003000240034500481404000c0740b00b02e841406038030010500507000b00824107180d4401041a40f1034801550350840c00780b095011031416404581c00303a0783c01062000c030790b03081cac1e07a0301c101204401500c601555401d015035030031114107200405800e84100402c6d90100740070002c20000c200b0141c0704611a00c0d0300342d50040140c81c00 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 127043417 1250 127042167 127042169
    0x10c09060f050d06060306050f03070305060106030207021207060f02060f010f150203071218060815101806020d08070c110111071706010302041d06071416050625020304 74
    0x2600d456081e04540d540300307030740c1d0340b04201c940306074289070910000d03203546e0680c019019600d04a8003641160060000c141c1ea850040c0406402900701c81c00400c0024001da001300b05042c80540038104101c9403450300345c10041c0645c0003501181a60000004042c5c0c18000c0343c0c2d1141460200c1a20741d41429450507110302e1a000308110340d5810710036810024000c07c2503a080d0b9911207001c6210604025005041c0000303280e0b030900c401000503010984a0255404070300c600c1d02e00e10b00f4059101c0d0796081104250304d401d806404e008400c8507442c10307134500308030810140082b90003d02501081ea44014043c08000b05000200115011040009a0905101503d0250918155102c8003031843c1c2d41d81040412f900617680c0e01d50300c0c0340c1d030111a0804507645040700c0c021142042080b004000001c040980842c0c540d02e66000200002c4004d80902a00345080102c180300a09008018010483d011105541550b4642c040c0c0f0802100030b040008141403181032403203000003c501000083d64074091 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 127044667 1250 127043417 127043429
    0x18030607021b01050d020d0b1e060304060209061c0905070905010503060403121b0c0501050903070206030408030c04090903110708070810180816060b0f100309050c03060a0c11010c09 80
    0x541284800b0f130304c203005580f00700c00181e00031559409400c0001d00100111081c0600030804081c079a5542540307403031858a28103014103079501c0d580c1c841d512071000303601c030340032075a4001010300c24860390f01c040d442003070710104c03140b0000144414181009031411301d9580c4840d503401e090800602c8292001720300310b6006985800c3c0110110042c001d40009018071410200c041c0d2040242d44034001e0f0b01581907861103004400800c4107403030303048005441740b048600281d00940b041010900007248800115400418003042600f4a0703100c59400c01030f1150084150002400f558190640d04ca06001d4040101065401403a50a2070190200d440341c0c0f0100d6151740f80d6507105a03109400550340d0380342110039072180d1406e40d0794043c22401014090107103403e0342c03c9403070000120083c0c104006680341c1010000c0200d002c080c0048002c80180503810001c6071580591084440540c40c108280b6000302e059060100e80d00c03c0030800103200844000340a40140c0c14141540c002c143c00c120003105581e0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 127045917 1250 127044667 127044703
    0x10f030807030f090305011a0111160312030b0904080301081c0e01051e030f090706050a1706041d101107080313020109080d02070f0503010c270503010608031803060702 74
    0x5606a003071341c3c2581658805031142d400c003203e00561000c02041d000d2000c3d003d8903940c480101807c00e40d5542c2c1c40c13100503001c481d0030580c400c1c00402c0030503a030720306c03000018900414401d010f84045103400b131090354110f51190011005201002040c0441318000c0c0204201140710084000c00404107003400b0300e07442c1805000030f48008807400030b040090341d4083c3e00c580b03581d40703040c80404118071050480d50500c8a00652401050603031182c421100d0403882c0c5c5c0e55103050000b40d071210b00b00409020b060305a1044d0b85144010040d000c00a034602c07210301440180003a0349c450001c0708d00b034400348400328511003410802040082e80f00010343c0d42003600c100004c02c0c044100e03c016a40845503411201081c8140d28481c00c1141d40001d4010aa074113070a0703441140780e515001c2c50f00344e03008142c85002240c0e0f00c4a101c0d1244403076039201c08241720f00d07540348458140e441700880d08552140d00070044036040095a40038212100c8100030311040203800801e401d142041d0000c0d04c5d01c44659202440301 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 127047167 1250 127045917 127045937
    0x6150f020a0326040818010906050706050a02280f0203161e080309030406021207020d1202010204090e01090b1003051009020303190201050711070f06080604020f070507030605010f03080703 83
    0x30780203c007010b81c6840200b4504649051909044a61350420419203940c800066681c24003940b00714880e1003141d003070751900d5003003603e80c0d511440a40001022134074505d07800e2200c0084400042040508204000340c8903a100002c45001011404000c00c014155402000f00303542c400c2e4098120258290009010300b080c15040785080a0a0610740b03000d00441070110a200e00e652020000f001200c9032502218000501d1090028050098000c00b95001c1408101c401c04030351090510b100c4641d040c0b000602d00f589441070310003200c554118048441c0e64540c15003041018155200c2d03040149112400d41441c03665440a40c2e4894403540c034501c082e00c9101980442d202081500c41050f50385900d43c0b08008150700080c020102100d01d01c0000700790b000b40c0384510030041120401c2d2908034a11000309402d0520648403500080c4c503d80d00180d00b080169007144501026103401c52054003d0980249103040c12401c0e100180c102080b02c032314180080000850400407580340981c581007c203004 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 127048417 1250 127047167 127047197
    0x601050409090c0305120d0605030601031203020903160807061103030c19140d0203161107150c0524150f090a0e0105090d02012406110304170106150f020a03 69
    0x1190f5501c020301c035109034001703041c031304107800003400062042640c200101542c402c109a500e210a210240601c044200d10310b5401d442a00203190071080902194907404a4003551a00d4201c19403085440c2d801c486000d001c2140e2081e11011480d4085008504506226042401c1440b0303803103041c9200c407104d024210882c0d0080d0000030441c01d0518501340c0b20043c680300310000c0d500844621440c146a18401d070403407405030203242000c41d011001490102c0c00d140343d0001405c0074290307410900c6050052800001d004001003070202141d0700c400c5070750300b00c00150004000000b0f04401c00388110f50000c480c25440311440103070340b81000c94ac0d0f1804c40c0c0720000c40700024581300281500d154240020070140c000c00050340114009664020028003800324482c481c410100c1c040d0002d00c6d886003104100342c5101e070311203052900b074800c10b0780c1c034141e070301c101d010f01f00d5004002202c101c2e5140e010801c03d61008030003119101c140d03420200c80c0600b204200a40750f90104000500f132100001c000621 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 127049667 1250 127048417 127048433
    0x1050c071203020a0606050607030c020909010e01050a0b010f080702060406051503190c0902070803040b04020103110a0f0f050a020c0d05010617150c13031203330608060105040909 79
    0x10070044a500307100c0c80090a0007519103110010030780340b09042c03c030300042c00c0c103115003110070240e0182c0e1182c02c034005544c208000c040d000340c9140c04640d21240c94400440c4207109440c062040c01d2000140703021450000741105260707940020502c1102d41c100018190045101e59020343e124000241d0b079a680340d407103603e04040110301a014440c041c044861070003800c207070300ca030f030350040c40840003076599400188140c0c0301d044001000103401740045070001d42c556140c107800a02c141404030346219600c041300308039008145160300040c0b82d62002100d0b10b4000c5044c4802c00610300d0306501c2d0155414000c2e503112160b40c4078502501031240150103101007984940064002000710b0210a02c2020180b03940d00c524410070110901d0120111791020880005c960900c0e24400003990442c0c65529642d00030840300d024282810749816841081400214210080703041e40e21045540c0a01000d508400c001e03140c00180500070780302c06200b0140e81140a6030f0031943c480e44081046942403524100b = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 127050917 1250 127049667 127049669
    0x9050306151908060403031b05040e0a140c0a08090c06042313020c0f070302010813110402030f01060806090103031d010504170c240a051b0d0e030f060f010501050c07 73
    0x36110400e00004203c5100c041941c2c1e01942c000c1e43c003402540c5050095a0800f0b4515648074046001000100b0810354400e044651244030308a000460b110400505605003800b1204c000503900005030911000ba000b007155500558910000c2608414010200e411072056000b5860020032440b24406c048444403004080d40c1c0014200002000d0f0210a2902940180f080f01e000b40c001d01c685030104a00002d905000c40350143d54002c4aa141e0162a00c4205807001c415542e000d02c910001019032540e00003540600756410010006600d0a600102410300c00f4200320300ca40c0f26000100040707a40000b5a401981018503c803859801050060b40d0300d104680c0010034022466076402c1c04140c003c520703142003a60986614840e0340ca04142c20884501c2c12501140c280030034031490720b080b4030403c064543c1c401c1090f1a84068902054001d00e84060f0000b0000050400180300d0b1090806015050780700ca0303940018a02806c0041070b4000e0a0414000c80381008030204d034140e82070a04116a0f0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 127052167 1250 127050917 127050949
    0x10311130b0411030604060501020a02151303050706080609070e09040206090111070f030b0c040f090903030608060a05040309050315010302041a100504060221030402010e03031c060807060905030615 87
    0x3c16590303014001e40c400d0300b044030310070301c980d03c0d081c0c002815500108a5490b615401405203018840400d4000e80b00d4010244004103668006030110002d182002090090400d588075400303107140440c1088a02480208207004000301981803000c561102c18083da000b5038126001c0b91180e5464004032503000868101b80c3d42445a40c1000541504030b8810005480c0100038092181d900ca02c8562642d21491140c004100e40612040011806a03030004000310702c00e140c0412035a0b901c5000901d451000d40c5e4201b0380310f542d40140400c1681010038900105001d80c050002c29001c5002922507640521029002300d440b101c480c602b0084105106128400041200b001981c84c024014001c0d042802001e01502c120300110941d92002000c0d415040d40a0000e10f10350f0340c8070303401114820320812249800d0f1105225000c003820f818588280503160a0700002411484e0402d07052915a00f030340020244002a0800d000c20f840100c0c2c2d040d03001c001012041008028040861412001400c0c20 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 127053417 1250 127052167 127052171
    0xc0b04080d1127010906081b030c03150a180209040207050105011205060a06030b04240f02091f08071b05010212070f080108191401020301030326010311130b04 70
    0x200c945003101e40058288424545400701e103000070f04110701c038107041429903240031841040c4108542d510a4070a00e6205894401441e00d4180388582c40e4866041640d500c4a82c4c400407003000150a0690800c21303441c10b0484190b12002e00d401d5416001c51034480c0d528a04d20340020313055202e501c813501207450999020008000540e034440c2d1440303181c00307101c40071a420300400c0b002c211444820b001c0d04080c2d0750088c02c10102d90300d969403100e42c1c40f280c0001c500082c440c0070802241c81c510706d1103000503040b030742040503a41c0d010706010440a1003102e103000c500504a542c0c604079082e4840d0446030b0001e103a0824403444c0c0d00000241d50320038482c6400034915800000c06210503e54251542d002d501c264585400109008406580f904400d02400500398001c100710700da259404600c040059010315610085074141110312400c2e85d01c00d81055010401c0001c40c00c044000c880b109070026014150522915410340d50f9490b0420940c42d0220b104081c200c2c000f4010640759031002415110007001 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 127054667 1250 127053417 127053431
    0x90213060f06080108030315030a0b070201230405060a0506060f07030c0212010504110105030c121e01080d09050609060c031303060f061212020c0d03020610050a03030c0b04080d 78
    0x104018106a00078032001c020000e0001602c1805901440c0c1a20040303000703142144d8580701c07c0c0c51210040201c0c2c0340d06103d0b4145400c0410283c5a071180180f20990002c5481c429401c0b0003648054410100c0c46052034010800c80031400c0455556004070078038201080a4491a000034650b00884651100825002445004054006150025051080d24525032690548020500f01c0700207c80141c46180041c510844d15841800150b41c41001c04100b141000340100d00f510050008480300b100f080042c4603030f22880b080c00d001c0700c2e004100440090411810101c001001c3d40c8842c42072a00400d07000c10a1800b5950300c1c4107a94100b11461708907501c0361080300c0c4d2022003800600c01645c1031460681070903408030103030060384196180e4902a45908070310340c0c0c0d84004410007040c190114084c110100740165101e0901602090003a0300411403070030701950254810900d5407061780300b40484c0104100007034006440c040e0305a0442a80041070792141424145403040e44540c150706d9240641c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 127055917 1250 127054667 127054699
    0xc1602091f1d07050901020303040204051b0c0c0f0d031b06091a06040b03060c0702010503060a0803040b120a0603030903060f0f0204150305010b03060a1211040218040b01020604170d0902 82
    0x400c4802c0c100864602645940605440503c00c00d815240185c000b04002405402c2c41c1c2c00c1160450000355241c070840d02c007440e08160541218214014079000440c81d0242890300002803141500c0844421950201c40d6070b001d0320a1812400030202c00403480780901c14040242c1c001440580c100c94400009080d01c1440c0f98540ba08580c25417041d4603003031800140d8140040d41c58410090341d40302518161558006440c20b4000800c0540e0101640070003044c03000060014000903c88004072646540d00d01c120803140820003015644452326050b41000030a6001c00540e04403a000000020303501640c1155201614100b02465002c0d0300010300000c503403143e0710032651032141075a0200841c1c0d80f01c20b40107200348403c2e1025a4400c615134000d0203500702e1891070040702d5100c3c11000f005d010102001c1010b030f0b04031010040100f844110075641e82d08003400b50000341c1000b403014207010b00d825980c041142c0c08800704202c1e10352022640c50f40032016540800c4240350001c1041e601150414 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 127057167 1250 127055917 127055939
    0x14040b072105040203160806010501051312050c0114070507171c0908160f03080901090305060a02040f06020d2c0307030605090c19140406180509060c1602091f 70
    0x10f07904074001d104600881c2c00b203c0c480000102900d40c2d0a000d8440c1d03074a01401140c15810102d94040003145a810005142c903051120110803440b40e0003030250f0010a200240c10440c0142c4c045480340400c2140310000b4030003181b0041540d041d1030b0f4604072449020506482c02e00040701007140021541e0445440c16040409441210450006c039419503201c010b4041e01310b602440ba54140900401e020300000385c2681c040d040c4441d06251861440340c1c1c0c0e071915803400710180c942c015031036400141440110070249503a409032041d40010404041c5401c030082811111803503071007612900d4031143c8294810308881404884004003140e0200b03840e82890380c02030805844400076445141c402184506100c1c3c03040480000491094041c9407803c03403110034401c44506400c1c2d02c5a0f403010045640017440102c650078606508000079989001590a8076021000c0c250b5560120140244100071412aa80000c05941034486441d69114040c0201600c64001364a044004a80c4004a1004280 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 127058417 1250 127057167 127057171
    0x9040c23030c040b180601030207080d06030201020d0302031311222f040e1906030f0209070201110405040e070b0c030c0c0d0f080a020a020402040605070302070914040b072105 77
    0x22010b40d50b44500510400046404007508680c0105200c1c21200c0840781ca900041e60180f010b040c094070b0000c0c0f581d5101c040307030311003e8004030035641c3d51414400d55070304118400c40c10b0205d080c03c61440c00c00202010858070404c9000f0108411000e07131421039269915910000103042017003860780302c281402034001d0100000008140800c01032035440350704811804d450301241c01c018141c81d25007411384065101c1e42c001c00401c094aa54800c100d0814414400c14000f18040c0d8000790b442d00e0713248100025002c01400320021681800291012a002101110110382044038002404c4a00ba1425070424003503070302c4002a00d0001c50012441d403008002822003000380002d9840300c404110403c4150085c4100240007070290082001c0050344000003001e0100103030048600540150f40040c0691b44a42c02000008401240702d508040c0c04010f6400a4a03003c1401d200b080701c7d007040c801041e00010f002826000750741010581d4907002c0c04000781c481980c842042542c0801c0c10a6101405d42 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 127059667 1250 127058417 127058419
    0x4170304050f030c2a0a060f02012a120627060308040b03041a04110103050a0e060106051801020a0503070323030c040509011d0406231e0705070503030609040c23 71
    0x517518044811403e880f0030494001d001020f9102d21800d0074400c80d440300156511400392349d601e80000001030004170213650a4030542180216040241d0b1000300754040c20740302510754500b010740511030110583d01995140250300d000d8502d407a0300f49107000c0a021154405000b009000502241c2c80f00d010004511650040300164100e0304048011355500108503805042c090344c40142c80c00e1984650002ea411061506011409541d41c42e10f690400c10280e0040d0f000c2080060080c207805400c00c0703480c1c10340074240040c10170344095031140c0e0b80b288642c1d04000c04222a0a1404c2e411056138019040d000c42540b0a1585070318181408804540c46405214800d00081000048150303052000755260502c51895440b90740743c60b42c03884013401008103034110702d407540c41c10814440c102111907882248002d1104100201101b0500200c80c0003030002c404005003001500d010880000403250400426118282c0f141c0c0c85042041030307180076400583c81d81112400c40020414455680700315050 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 127060917 1250 127059667 127059703
    0x60e0304060311040b04090f1e05060406090603030816020f06010609031a071b170a020312060f030715180806070e04180822030b040c060804170304050f030c 69
    0x443c0e043da5030f80d40900d108055609004110a000260240d0005000c004030441c0220304a141d040881c4032101143c0303944007903150365004102140c0b03008c4c010300c2c0041000f603008100150450714020205e5100600241d0704040403444410428400c211b82c1f071141082c4004d4a20a50311a0310080c207030b040b02e1009036449c150301d925a81c0202004101c40e07000d8550b40d103445c240350011070140101c10b041c3c224191100c05040350414003448004000342504500d6034003441e5103901e0700380403000e1070324090445402000402881e142caa140061080c068400340607080c4000400c640c0c04642d10b0040f038961800110710480d0019003103c00243d85401403107140c0b6204c203810380e404c0910040725402e0f940a03204060140c40c0b64082913180005041c0203511030103070103e002d898240b02ca4680490740c030807960041510108028003c0134068040a040b90f86060341403410640c480306d2440c186006000341e4000d000000c141005801c01c44401880c90325000c1d251218002641760f03440d140460a588200c031 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 127062167 1250 127060917 127060931
    0x4090507091706130212010b03100605030601080111091c1211060a2f120f010303020714090402090705120f01050a05011407121101020d0903030b120c130207060e03040603 75
    0x400206603580318040020080c2d0740045185c003008044003c000104030f665684003480e901d1510240310528204000b0f40000c100589484240340c5060816031018840e45d1601681010441a0707804982d00400201e68422042513100c1c00ba403901d010f4190011302c607068050ba03001c102a002206600f01030000d20546940c0d581e403161344000e40e4441d80e440304002ca03180c0800d152007902c0b80814000c0c0039900382c10a00f071070b0107071512407400802a12080210081c01c0b0040082590400942c0d01508807592403042000b5040040b90b0200c401500081c0f00745070900020340410f01c41c0056540c000b10303c0039250000d040001c910a2811003e005841c00740c2190300010466501038070041e647c2514500c456440c1c004151284c03501010016240810484074551008101d0b9003400500304420940f0710004407840301c0d01c0c0103400c9612020b0141e01550744000e40d001074000102d01200c9404081e18902440c6011a100d40000c1c400e448005161924207a4403001402c400070180c000c0d121a40c604100742 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 127063417 1250 127062167 127062209
    0x80c160317060f09010603020a031814070815060d060b0603070e010201060807030b04151107030206060a0501090e13061803020627030a0f02010209040e0d0e04180201050f0409050709 80
    0x702c0004440f1076004280d120040000c0d503ca54001d06800a091500190340ba94010081384580810030003500d0000d41403020f400719840521902c8001e140e11001403421208891780020000300062405101e248000050001c0c0072a80c0c20620b0005c00c001c02695032803400040c05452500b080d83d4203401907107420404128260300261b03100aa1b034000d04c024456960320381e10744181c070107409a40d8103900d40303c10a500c692424000a403202c14440e401410703243c9000c000b40100c0300900d60015041020703030241041182428581150450350115000003000341c40d0074803030007929503012a0f00440d682c880c0c9210525030f02255280c000c1d1030120201c0b04140c03200036484a1003441c030101c3c103070030382042000f4180c0300c0c00780c0c2c1c0b4140c0c03007143e40c00090300b0000c0401c00501140c140c0e84003241d06800c1a0110928550320461140b080300d41107808121b0441650308001103004584802810b0140025003810960010410b0b58010252000148803626203068014080201f0780320342048a41c040c10f400c20341e = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 127064667 1250 127063417 127063429
    0x1517010c080106210b030313030501050c040506070807030221040306060806070801170c0d21020f0c0d02180405010212070f02150a020c15061c05030307080c16031706 73
    0x482c3e00700d5130341d166001044800024071020512500e210140d40f1440c0301c115460500c090000303130f0002a00382c18402d00c1c4d82001c50070b584000349078980c1e410f0100301c140a5661410b050711079040d04440c00c039807104c0861905034030b401401c4c23201d80480000a00b1120300800d03588002c0007941e2003940d042c0100c0784d42c0da91481c0e03155800c1e41e0700c002044107031006026205013071140a07a0140d0340022140b4010214000c64940c11001c80c003910943c4481c4075211900c1242e15007607202103141d1008080510399400c655031620100d0581c2d520500c00d80111000303650700d19a880d00303c0c01220150294a090516289000b9401031240c20100e50368200050f806501030b800201504d80300350003074000c004a04014042407040109501d06071542400000120a42042140001c108034a212807150426004014034616440e0030100515080005503001903c04000d9940203281c0d400d010820341c81d006280d20090182c22075042a01c91810108001d0590103131040407220511082c112a07038a5607000d100e4 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 127065917 1250 127064667 127064669
    0x6190605030102090f121c0804060b0603060102060f0603120c06010e0c070506060103050c0d05070903050c030d020312070c02090a09230c19080a08120108030301050d080d1517010c0801 81
    0x40d04c24400d040a40e030a003001d4010303281c440300a805440d040325486082920307c4010400ea240001e890000300701c200004d40c0f00d54601c1c441c084440b03506520b00000002c0da0303070100408801c28403115102007030b036607282009090559111088031a841c0d1805130b580740e1761454244a01402d00f910303400401d4091410000711403001c1e030000d001e49907680c0d41100540c094013015018003290700d81001741c101004410721501c0e004481c1c45c1e03603442c142451420041d2820700b40e640410701ca50811080201003540010484400341d007410b12580880c1d42c0c0080a03200e200508034080d400880f80400c01c07000c7c00840c2d00c80d6003614850140480d000c80103105440c00149145801e00c5650b010502c04207141c50282c401d081c00e8141d0701c5600a080b512403084505110075414212034800b00441d0920403036100010301d42c0900751687c029800e44d032400c0b00061100d540d020018120100004007035080d074056400c480d01c1d05c0000300340340640a580301044401d00c44a880011025403808189001262082034024 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 127067167 1250 127065917 127065919
    0xa12030c020a060203040c0905090a020f0906010203040608130609030906080a0b0105030402012706051b010509061914010b04141008060103020c0c0a350d0f030209030619060503010209 81
    0x712400b042a95808000c3d840608162995501080c00203211166402980d00c40c6d0302c80380c003030300500041c0d105001004070080f010138403076540102000080e0740c0c00801d807800c44d221490951413941b03030984806e8154940610181a8a090a1005003819008031850080790241d5849400681c2c50302d42180485036254403160000d0020000314000d580301e80e0703c0d03104409071038050100d00e0318150364494a0b640c0030380c02000070440c045061100032483d41140024521a0310003170094dc03a150031940c1d10340d24024540406203401003584c1380020010b07401000fa00c030403808248a2540c5541200c41d0542103803240720880c100146004e182402c0c0301c1e501154080d01600ca81440b03884500064019420000d5180c0c228414283c00d14141e985121090f0001c0000a48010890858020190050030b41c072020b0f500c00034003559480c0b10320300c2c0010303201201c0d05189003804000480c46401c802900c1124505981031044000384514804100a59014414558000c0002c156a84103050030b03802a00307081 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 127068417 1250 127067167 127067173
    0x91b06021b01020312091e061f05090a1d01050f180102070b0f06040b0a03060b011b03020c06030411030a2a0608012d06050d15140f01031d0a12030c02 66
    0x5c291280c04540285540003602c000c620142c21603882ca0190140580269001c0000d1203a0100c0403100303807144280d001c20380480c840c14100071880180014060231507165071051540c40c03101d2100400075119804800078411070070041005400e441040c0e91000380707541c418492400105051084544066000a140300c05030740710004810000c0c002460b0641094aa80c03a40103660307140d40401c800307180700702c070005a00c400d400d00040c031410344160b82c01c1d40e00d1016008032000c0381c1c000501029090003240e0140e9240d80310728014040003a50246c0c1909442103194507000c020480d2480251000c81d9000b2410000b02101158403642d454441c2c2c40200c1c4041e00180902001c41c2010051100c01d240c140c0b511044030305601716424007560144000500114000f80514160301547c1542050304101d100464204404050380d0086414801d20866a038054008603034000d40181003e05242c40c01100c164015856040e02c9030380303482080b124594501c014101e800e000380324189035602c0550003 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 127069667 1250 127068417 127068427
    0x18020108070c050c0d0606140a03020105030a020a05041802030a0b0406120b060d05030a0801090609020301030218180d021006050a06050f0c03040b0a1d010c170a03091b06021b010203 80
    0xb07580c54480301006603814041e2429101680c2c82e040c034140c500c0303807041c4c000141540c81d00b19070b0300b4903040c43c032034070343c07103100c000d10104090303a4403009590b003140c501540142d1b6000f440c081030f15a80700790343c002800b01180b0000c40982a0b900c0c0c1c0550301c15003031540c05020090608080000312242c1c1d00642074850300841808000c543d522005660041e009803000c001c02e80c0d02d40b1403520319082041400000760313051005101e88242c0d4004c1c40010015004150300b5941154001181021040c8590b40450418400610105d4000c0c010300400c03038582098608500060030300948507026250440b070300a05104000a03039003061401182120043e903541824220200070344161a0f0040041c01c00510090002242034010780000b80b0394070b101070321030705400207a580254140c012010107650602862010580c00701c0c191103110110880308a0203542d80f0f000001d0f0540040109150191000c000011a11400a09811180240c072180d4080368004003480303264800003184010034600682003804 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 127070917 1250 127069667 127069681
    0x60f1805130b0102030c030705011e09050303070302030702160806060a140d020f01120606050901090e150f0109030c03060b04200f030a1d06160201060f05120a2001020118020108 78
    0x31040c0c00b08641403058918100500300000c0c50b64004c881d05540701d035583d4841072000500148129951010745001740720710241615043e0300d902006200000380360f00000001e060510030b01c45008141c0744401c182401603120400c02d55074a80841d851800b4604c1c0c20004582014a000302c001150801450510454510341c00d0150810080c800281800513010034107180d40c13446e004400c0984515503600d42c4076a0004c00041603121154411000c850414050005041c9003420045903d401660441400c100350380040340c2c3d1002c1c07a4005098904861404020044150080e56245208840a204405801401750034020719040720340300448042000885401b40780018581c02108180000f60307030804240d114030400503040e201c0d4a40c0e045a03042000fa03101d811a40001210180b00070400382d82401c0741d5012105441c06014810b006c2c1003d904001482002890b42556200c2051600c403039005102c00207100342c0c050f959000d54200a4100503001160000062003070b0141c1d152900cec1d8442c90 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 127072167 1250 127070917 127070921
    0xf080105180c070c1d040b220201080408190c12050913090f02040905030309010509120406050309030409111308060408070209040317090705011103160b0901020403020406060f180513 80
    0x30108032030203041d00c000042c410140c3d200503490b05042d12545c0410785014a400712203900000c003000078003080090761196080d0703040b010800e180d80c2803e01203040d845a0a2a141c10b0081e296a00140380140d80b54001003a40142e00c8d045145c4500550760209608000a960b18003512003001c0c0c2080601c1c080200c01c00f216041284458002d400c0c0103200e10498001c00c064030305d50541502d183e07000105120901109109480c4e000441c04050101c0140c00c1c1d0420045200d01e2040321b042110110200e044420180304032002440072503000c018189800741c4c81071413070b042041c25015203012054001603044002c203c40388100e60012000b4900489a42000b65010b0054000d0341000890b10614050002100a03240140180401059181c0c9814001400d00054000361406034000344800c0c506038004480010607694800d064228568400030761a0082c0181c1e480030398042e05000000507415040264110350020380e80d0703001001000b808018175504014401d458014105041201c0651034917 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 127073417 1250 127072167 127072177
    0x406091a030c030610120c0806011d0f0f0315041113060807030201030903051317010c030605090a0506120a0b011701090f020603060604180e0d020d050301060305070e100f080105180c 80
    0x3030074010b841208000e8440c080b01d07c440d0b40c05e004514800300340516580c001124102000829418242d0710528501040900f00500316090107540e581c2003102d10341d5418010b5042c1c42c19165224082d9180c0b0307050030703140c22440c00003150107030700f00300c0b541c180c00c1c030550061905076542c1c03000401d6420300e59070045004020001c0244c003040750034403440340c0c2c580b8004075a00040c41d00da00010385c000300c043c81d0300342121002c03803100d020305107001380407c410740341e51003110780c04080c600001640b9a82c50012500c0d022040709240f41c20300850640c00204100b8a0700749040e43c2c82c00541c0038170214500d8600d401c9404000c4003810040c40660b001c001441d041c4000e40e80003078050b00d03460425070b0740c480052100741001c6008680c161a4115071140c110200f14003200d82c0c083c4d1005100c0c0200f803501c00350041c0b106000b54020180c540b00003c2056008002c1d0252001000e84001d076549603404000307001d000351030044000110030300000a8145010101c81148003114480007a06032541c08a0380030540c40 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 127074667 1250 127073417 127073449
    0x30406021207090807122406170307150e1e011b020106030b0601030501030b0103080c070b0309010509010509070602031206040603050d081f030807120c05030406091a030c0306 77
    0x820820300100714103100d05000304107580341c00008608014016007080c00c550810348246032a9191900030943d8510114000500d803e000c03004400c0511441001d8140d40c4c101ca0f0700504502101c83e0020310020041c40ea150149a000131400b100000c80010f0f1900b02d4144c100940c405c200b044600b002114001d00061800400001c0310132200b1411100700c171044000d00c0150755151340400c02d002c803c45a055002c4400d117002c1101e0760441d41c5181070740e041070101610264000c204500d0f44101040907601902509030040c2e1a80341c00100180a803408540b0343c0d0855003000c000c1162001b0020f00c036001d90700a0f40140d41004108188071141180042c040c5a205481d40340002c003180701402402e410071040e40c1e4440c0c46150500c21003a40200b00c0341c03c14020070000004001203070040c8240d501482c1d0164107031518003142002156030140c2c0d401c0c043c0103404000750000e4021b8008000c042215040090140c1800e03043d583c1c3d1069001c101da07820100041040090103528040d0510311a00003 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 127075917 1250 127074667 127074671
    0x403030f06050a080a0201020105010803030f0403050d14010b2d0f0a03060e07020a1a01030210050a03091416050d020607030e061303081c290d0510021801020303010807030206030406 80
    0x358400005203500c0c601c3c1d1061159405c070034580c0c815541d0a01601d405450040002c500d1401c00d0504603440250043c03000d03080000228441c0c2d104100da801400ca4114044820040b0b96111800d601981d480b507140c11154152307554026000086540405407541c92071450b03942812150503484500c0c0c0c0c05946078070f04241c1c1d6903001151050b03000c0c09083c01020700341d004146107100e0f4075284024101c91040e817544845a140100300581e03801c100c110740c41000f4030340540c03205852441980034003a2104d0040215900068082020000003074501840301c000711005080c0c1d60320024402500c00544000c2c4d040388081203071030046130054110302c0f401a00a130080d440d040d01070f040c445803c5504c2e003044400040015459880c2c60411559288512581400304075201188003007000324548080402e07020340740c0c7c00c1601d556a031502204042a5080380030f64440340070720502d480003540201c1e218203107071031000c942001e20752000041d00e060300e28a000400b4400d0950f020890660001441150303007039 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 127077167 1250 127075917 127075919
    0x1051c06020c030c161404091a090a031d0603270f0102030106140301051311041a0309060c0c07030303181e0c0509190b03010b10020a0c080102030705030403030f06 72
    0x5400391004124400506001d182c0343d0b0100d0080350b061075040c4200000c1d000305003a050103003102d081044e035080341d8101c40000b00d401c00d40c5000000a01d0f884905e074030000f5910104a16210040741248045110b540c86992824035204035140c0110621980c94000805100140450030300741c10040350a4180f180d4032540e054958075040c901901e40d089800f003a50040010441a50444880c58191444802c102e05542c1410081558461071001914007a03444a5030008040c3c900c100b10380141c5601e07102d0381c4928400403c6004a03900640d12a4110310880e00041d01d62140702003a00c0980d03403984068120f00349141c03001c0b00649610038111b601001c02041850005030000b0ac5441040d448540e80c0c20340041906021407000d18541c400c5026146500400200c1c00040400407040e201d0307410001808440c3d50082401417032080500754018007070790400c02007140c0000f20001d081d4807030180740280e552034101703143c02d034001541e203600450030901c04a0006402a04170003140184030900081007 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 127078417 1250 127077167 127077173
    0x90905100c090e090c0906300d0806060a09030212011112150d031e0504030501050708011e0503030301090c0522150504120b072309040b0102011401051c 67
    0x110110744407040400e84000007001a4000300c0d210340d9208000001801c2c29500c1e84010803242000100601d00c01d115820003030010036982001c014a2002c0000f0210044000761009942c0d175034040007810100d210240003072400c0c0351074400c031f0320803c10aa076804102403441d402d01001c00b1900d0f82001c10355403601e400c0800c0c0700c00c100203003503001c50000050b00c41d401c00300c100540307040c80c09240d1805075812500c0c000219800c000c5400d6810841d511001c142c8607400000c4070b85011755080207016500700400d2001039a80007030a60b0580320000d0901400c1840c0703407100a0700000790703c034442d016001480104000c000d254080300c000d45060500354600210148840418040182642142c0900d00c50030701c1202d41c07030391031520100b1650921030701d40fa00b01000c0c041484042c010082c0a803085c10000f42d40f2078401d01d0380d0b00c0007145076003826042d0302c24005a03e5840e00001980360003079140c02c01d001e500d584140104e0b5002104000307074951176400d040901c0304062a02440d40400740c40c0ca00c0503000 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 127079667 1250 127078417 127078421
    0x51305091f0606030b01020114010e0a0905100507080601080f07050a110a0c060f0513120503190f0810061209170403060203040b0c090a172d010c021609090510 70
    0x104004010028202d810b104014003180d4070b03201654110387c94000b804003005100b1001d1819981c04140c004125960401448094a01418000d110707025075008554603010390b8000c140904034a40320001c0c9075a4000045603800c100321080c41600440c070f0f0210710740c1c6014a0081c4201c90306483c040350140300500500c1c0c50685a108102c42200c60304404001544d030102003603203c11f10034074040345000542c5010030700c0005280103641500c21150041c2041080402c02c41c0c980c51044001408032f01034981015041100c413035842404103190400150058620b40050003e650f0103440386104500c09440840c020160040c00300c0d8100d02980003403000e00d849001400086100b102c0260303070780c509403419010b482000342408002240c24004182646d903041c00c20b109440c03907402c0c21042191540000352828200310042d0302455007068000b84054264800caa6034490340000a020000705100104d0760303130702d00309440301000c202114240310200307550300a540720600038012282d0081b801d81c11201 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 127080917 1250 127079667 127079713
    0x90c020307031101060b0f0a02010b04020a022e090506090106050402070308011e0905100501090906030206070813050a031101030e0a051905100c0309050d020109030806010e0d050f03090310050105130509 89
    0x1f00021001c01d04445040d030901801196190540d000d6050034100340d80695101e0407030303614010810311840d03000f5540900d1050040c00740000d0f0414440301c105820020f40f10002911320b180320f5400c1c01c2002ca81407c10780201c4a0095166450b103203241e00e00511001c07203040e200c0c00e848600000d8900003804403868040d15000380e482d040e41140652410001500c3c002d0303241d100300c182c1803e2a0080001d681d480080c0e40601d600300581c41d6482e206140310000003040c903000141e00103c030741c0011052103050b40058000032000e0303e0401400330040c040c070f6906c00c007a00c0c00600581c400d103103a1141e810a601240a5107214030304503110141c03580710587c06e440080c0e0000c80000c4d9100010814403070100031405034030806000030449a10302d03840061030f114005240c1418003581d10701940007615000500c07141d280c2c100096030507004140d0310141e01d03a440b9014040c0300c1d04c50300c444001d01d0100d510480741210401005402d109183c0340f00720005d0540203001460b80d005000e0814040080e13009941c3c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 127082167 1250 127080917 127080937
    0x150c0b09012c010c080112030e0102070f0801021801050309070303030b060906030420060a02070b1308010c030501030b0117031204080c1207020301060e01210c12031701090c020307031101060b 84
    0x2003102070085001908464913000c8490401242c1401081101c101802c1821860380614218802403071020041c5d151072211390242c143e4407400a00001c500c1c9040d80500000c2000010300900c040d495030044840780400e540180040d0042141040080d010b980702e11160803002c1c000d14100356000001440725041100d054a0783c8542e0100310301d20000c52001d2007040c100403525941001c4401c94001d43d102c0090007244801500010052035600f485d0b00c1e20801131404400920096420307a1009016140a00c0111040c05804001040c41e18007001484102d02e2250011030500e113001e10950b03400d081c0903000b0f6541040804c1190720500d004d00c141300e020030401d06c12a6503180c05e48149800c60705554801104200c5c2103006018400c50500f0b10b11802c201c0440c021107451007801c03c0c1c0d0003c04194000d044100c8800d40c20401c060300144617881c28040d803190b140090380daa42d0400c041d00d4000740d101c2c0060b0030811401c400a03010345107400310090300c1c400025100303445544452403540301c00500 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 127083417 1250 127082167 127082231
    0x604050c030114040b09070504090602120604110a030203060406030b090a0510050609010501080a1b0306050f030106060c0f05010209060d0b030d18170c03100b0307150c0b0901 77
    0x501804009400001500364001c02442c0320762140f00d4604040504010907042100020504502c000c02118010700002007007005078840a20302103009500140300d180120300101c0024607245040d00ca501805c0c11080c40f090b2510115100c101c2c000d50008001950181d84c900002c070105100c0740701580304003184001081c1c4160a0300f88149889011509101603034104001c000298444880150455000b800c1040381910b07404070100c09011404035008041c00604c07003035039034643d0581000d01101c01c103841b00c2201e00c9441003814241da55a00034140815034450600d03000407207070280c0000050091300014241143e440024810b948161403034500c0c1511403034294224501031007000c100c401030b4102405100245070343d00d0344840b21823048040c0386166040d00341580e00c09101c4040d610748001d0603a135000b00560080e81c000c148409071140244103c460114044060b4054200314490545550b02e200c0141d0342c0f406280d00d00103104a4041d502c0e00c1b610803001520020700c8000d8800c1c480b075 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 127084667 1250 127083417 127083421
    0x1e2c12010c030501051518100c12031a24130806070302030403110c10030c0203160f21080402040b0a1d01030605070c08070602160803090a062a080a06090e06 69
    0xb044005e1040c5c4044254541b410048005107500d1446010710440e0140c8000703224009840c000d580700500924054401c105030020300c441320303030725900c8028001d8800c0b0801401d02d11910501501a1410b41c1080b503c2402055189012407408050702c0c0a02c7d100035001592511100e10303505000d0309070b03442e101182c0c0201c180801c25070041041413101e440f810003043c3c20303c00017000643c4078801415903403e00d03039200c01c4000820300c04c0c0100c4104820b40c1032a8002241e951403c0340311b488000f0000e54084078103c0c4403040010301c208141010324101d0b5101c407087d84664003008010207080e5041580301854540028030352201717500000900038601d050300181d40c55030400400340c13400200007a0030051a62111400942128280c603003032030b0047c0380162141031a2000c0803c142e0180d8010740b6680000c000c01c10190700004400c00f2945c072841090140c820f6691119a0710b010f0100b605455450000b64400d0407032180b0b00b401ea00a4044001003a02c56654001c0030890798284c04040a607000002 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 127085917 1250 127084667 127084669
    0xf05120c010b0607080a0806060f0a080f060d33060603050403030c02070f0e04060b06070503030711010615051c020c0f060f0606030f251e2c12010c03050105 69
    0x115402c07003140700380e0300c0034a4002d0a907916802c500c00d80c29075000f4820900c02007202500c4480a49880d080001440e40d0b82c1d0340040405004140c0446802c1000103802c4009103650400824111401d5489202c0c1e40a60301d0600b6000c1c0403140f0007040702c2d40c00d1914441d1034181201801480001c048a0b200000e050419007802400e4900170024030095602c400c00402041c44040c140004403100f103500394540c1e444915048d40604007070440c00794804000f0401500307221020000707602885064841d21960b607403411003142603a40c14443c1078070106040e90344010700c5000348010b0421440c210303040d000b60034000014204a07040000113043d258444003890390304480402809400c404202c2e0303845035034900080001c00c1c522000302071044503406413011545884190928240520003801e001102c2c44075514000c0043c0d030910f44504e5001003400001b14074500503089090040e40003104c00c110201111009000035240d0249150800214003010349104000e00c102c1c4148070b210342e00801c1d1545444 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 127087167 1250 127085917 127085921
    0x50a021f1b02010c09140a03150213080609030306040504030215010305100c020606030604082b0f0623040c020c031f050702070602032b0203090114160c0f0f05120c01 73
    0x1000401c1075a2503c04c80c0100740750003100c03100885045002c00d000e13488568000c81c51241950740020980404014264510103807a00a41042240c02a0b99122280d69480391070741d4103420360700040c140d0030810100d10b440c109604038a0f400303800f03801100c0d1480300300d1202c15120700099009403500c0d041000081200c1c0d28038001c00b412181503200500036806c2030360000e03447e000c000e0801000844005111a99112100c148070000c0000000b89140820002c410801906031625491005498010041162100a00580040300b00882c030b0528948103d030510004000040e003810075440303071240011203540e0811900f02004880d00c1e001d50060303c0d04115005444001e801c10003950084202440700c5035000017600c0074015400500005000400c80c18010002029004404280008100000b06805400ca100000d0042022070302a40c1c62505402c815032200d01d024001071142001c007004122914010f40c4024020b0360309001d08039141e600e152030300102046401003640045103c01c0825001c0c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 127088417 1250 127087167 127087211
    0x3021009030302060f09070e01060504050420091201060510180e13080a050f0307020c120c0a0b0f09091602010b060405010807030c09030510140604060b040303050a021f 74
    0x90600305901411035601a40f9000000e08001d40510400d001450703a9804202400051003102200714481d40c6808000705035074468081c680c001c3e030038100084c6045100705207403600c520990b90820304009900c0c0c108010340e40e185c01401081d64031403001003095583e0243d403e1850456850741c0b5028210b00302501a039000700c3d400306100c100846c1c00c015951200c2d090854045900c40f00341d603039a50080105a400780100d095a146245002c000c01101540026071020072400031641c65031040170765003504d07907155448a00280c00014000d001c010514180c0301912500d000c0408540c204001403012913182c1f00101c0700710b40b0009910041100454084c03107078154040068464074a130a040c480040d01880018003440201035844100002e203512904d150703006907a110707050f0f54180d01c4071a00c000207801d10719610101c102600c00400d81a01c0c0072300c01c0c0d5085a0780003a5881c01d142c80d40c0c8064600c0d400480d0500d0650086442e10414180c1c4a4094135102000a40005855401c03034807007031400c060 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 127089667 1250 127088417 127088449
    0x402030709090e030a020a1217040b1f0506090d020307090c03090212030421050f1e1005090a020d08040914040606080313031407031703070206060a0608040227100302 73
    0x405c01062842944c04107854184a800111009125614440456100c6600000300c0360382200101170108000000d000300d40070b40c0c0c6102030340c00b04912941207140b107007095101d9241e01501c100525800c0342002c91041e01480d00040a030b42035681d6422404042c1c3c3d8644510000080d510b020440441c40c001c0c4022150340c2c5540300541c02d103030500410300100380c8801d0010b0064184514010f00304001000908401181c0c1c3c4140c0d01c400b40c0320801d44000d00001c10940c480c5000d411b401811080180c03103014828060140285002105502800303d6021910015208804200700100c0c00205900600e80d42201d034001150403440c1908028040fa0020342180f005500f0030040300c0703185145069500290383e00321252034403401d412400c030f52400f1400d500003000094030b21074494980f00d48101951140300190246c4484da9124010002c100c420340c09407101194100b0003181c0541007141484003034000c50102c2d00d144400c1440b00e04411070007100e04000d02000f0480510441c2030441d0742e42c0c44484 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 127090917 1250 127089667 127089673
    0x801150f03031d062506060504091e060e0a0c0e0708131b15090905220b10030804031401060e150d02040f05071d09011406180402030709090e 62
    0x20a541d002000f40c40340310800041c0510021002041e540c40c541110322400c002c0c880b4040310a2018000c60107103a1103101031381c0c250f140410020315420f02c0d0281000656100b0b510802e0340800d4845103010501800040c0e0f004c035500d5140c041008030410440703500a004408000505181c010141a030010040240041010071001d1003020080b044501c58003580c0005040415011300c980c00703d40c4010759000c411004d1580229a11880d040034000c016224409001d000c1c95580c4080ca0200103483c24030910088010080f400c00311352035103c42d42e04a01e45800355a1501c1c1d603a129059681c1042e04151400503001d54054202074091280c40300409001400d80010326183c2500c003a80c117203811314140901c1801003400d0441d0781e41d911a0441c0c00380140100142e003030070807000344030700058000b2244141005840010303070300d8079805c070604950070a007240c0c0306014207105204540d000701a1400c00c181540c0040021030740c7e2400910710486460f5242ea00c000c0c076016040007500c1c4c1c0c00800c0e01d444e030 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 127092167 1250 127090917 127090919
    0x70b0702031b1606050901030f02030a060807090207121808160e090115050d020a03060203090f070b0906031512010908030615070c0902030c0d0501080307120e01170a02040f0801150f 80
    0xc1d03400c0614000721212410000c3c3c46c0d20200c00143c02804440a061001510010070454644190b500c5442560f04c62412102101e031103480010072070ac41c540b400340002e120000100b0400344030380c0c40269240c100c15072900b074071a41c8a849a2400f107150303581c540a0207100a0511450000140c2140e22a1441d0001e00c01c80350703800c651840c0b0016174001d407030080d0709024000040d9201c2c01070510003154452011942e034a13081e003e6a4960304113114804d868000c409000a00c80c102d03006a40100030014000c41c9186c960342c0c22080341000c08814980c001002241c18100800300f031003404201030080444030ba9a1501208001c20034140000703520104d2001c2c0603c0c00410701c1c051019060f945403000060360ba845e40b9140e03c02d50300511810840d13641c200302c000f040551020016018640c454000e102d441c8001030300545028405a0314540080e031283c041400c1500d035050b405030000d12600c401840c00d03840c0c003103080540b2955000f540a980d16140740030b1004e991001050700400865200c40002 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 127093417 1250 127092167 127092193
    0x12090c01120203070201060803030903041706010f090207020409020d0b2203050d02030901090c14011b050307170d0603051b010201021c110d02120403090f060906080c070b0702031b 79
    0x8000745040c04000940d020001401007030007544184040c0000000301c0c0d48a19180040079500d034006c1c0201000304140d14a003512580c000a1030a0580310700404030300d205801d0001030780c025001484260790007a1124810fa0168854992502d0502d0180d40004410301d84030300b940c0c00c0302c461030b50a09181d000510400740401d03402401e8402c5054041c0000d650303609e408803400c2c05040000c1c1c010f4080b5601a000041e0f800050a1040c1214404c3e211402a1424003000144814980d0000350140c0c004021080000e4103104d030752001c804c0c511032141e05100c45490b104003182c070140c0084407568410ec0e400740c402c0c40d1100487d00015001d02c0254070340310103640300d0740105501083c400e10030384d122a404a040341094056901d0000150021503d800f8070b050390311040d141c144c4081c1e000c5a4180c4000c00d107000d103d0205003e440d0551144070701e503403800f40112160480100900d40c030030002d0100b180000c050040703183c092034080e402141c4401000c8420007446042840c841c8003071b80502100444 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 127094667 1250 127093417 127093427
    0x519080c0a0305040c0506040803030103141603030c020102010f1d06010e1e04030c021e0f0118060f0318050a02120303090a08090102150907060e0301050405030702041104080303070512090c01 84
    0x1040080c0c1c500031500c1c4c0c480e0301c0d02220014954014075072120010030b0100e05c560000024504990040d2240350808420200ca140c989165403092281240d5000040c80802d011395460080580b06100002c2d04404901d040b0b021241c904018001c4101e280070f0140c081c0100304102c6000d40600e80300d5421904020500c0e140d041c800d54103502c101c00125001806250058404544031a0083c003040c01c1103595904801070b008502c400144141c82e4130302c0388c41b515480f611400c030343c010012034000c58003030030600c060700c00c070b52442c403400c0030140c480c00c03d0240141510349a0210601c03585c010040103415204000340210b5029150103964818010080242c40c00100d0242403608a1011555030101000407402c203200c401e000ca070110105014001d1005000440c0021140190740da00c00c1d10402408043c244c600a42d00a040c81c0c0c0244141c030090302e8250300248884984042c1d05180645d00c242903405e40d041150b6031400700c1d0f00451024030540c00d04003403540c0100c3e0300c009009054407040000e40 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 127095917 1250 127094667 127094677
    0x1204061d0c09060f0d0f06020301030309080a03081b0d02120103020405251d030618070605070c0b0c01060305060c070b011508040b0402130905101b0504090908090d030519080c 77
    0x4440c007410313202c82c1e00c0380d107a0b0f607600b20714550401c80032562400c45040403030180d071003844101c00007491b10380000343c00b0030f021400c0d09046034580c0c0e50b11040e442e402c0101301902e2501122001c2c0d81000c000d00e1a80c125244010702c0802c260003000300c010344c074600410049601c02080001015100400031030020b00d020504844440282058100d555030b00d2200103520180098070780c0c0622607401130040302c01160252a241c41c03800f500700d840194480070200c40d14000d58100802102c50320109114820282d006030064031210000081c10640d03030745409141140603140c00d48024000560141849512440380c1d014012404614543c0012010020000c0c400284060801308907400400d04655601c43d10511001420f1740030f016102c111b00380036071100400c807061011946456492500c0b203140b40144030280340581c6038541024604210040a403681007811100540100800c0c040b980d21500e51b0b5803118041c0e40c0d8030f900c0d40250804030025000400159051100c0394003082014600c84003111 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 127097167 1250 127095917 127095919
    0x50106090e031c090b0c1201060f0c03081b040612060f060905040b041d030405040b0d021513030c09050106030f0510060e190b030402011205010510030207081204061d0c0906 76
    0x4120b1440c140d000b0f40040100784c1c0c00415140c1c0040c140503032044280c002d0030b01420007034007070b04090740c0e119000c1d0340d101f040c0c0b521000440d81000e0858082030180140c42d9010140400000fa0601c1364144041640d00c00d4200c1c0c80410103501608054903802d108880251060290001b60715040c0200a00100035611a07607205a4580c00344e2409501c80d034108803994220030310850554001c0c00180b68407a000f5001c3e06005515090307100d14989040c405c64040d954002c0c1c4000722412107450040d41a506c91081c002115034815000800a54107015180050025000000320765050082c010203850040c42d00e45034060514040c031403c14013000c000001c0b101c880c204604000c0d40b200c0440d01000c0d1885101003115140c007000540a030441004510840c400d0340c8500ea40d0404050b004101e030800e024013034000120403844500d1500076401800600d0141c0c1c0c10a003000b03011403002d804c0d0002204c04403030302c0b5100c46518031400e21824103000100d80c1403024041542c44d5202090007018021300341c03 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 127098417 1250 127097167 127097197
    0x3040b0d0c0e1002100b01140306040203090a080304050d09050108040b0705090109050402030a150806040309090b12061006020f0304050d060c051c020705060606030c070f02010e1903050106090e03 86
    0x10070820340500ca40200b940d001030414005048640e402944a00344c1d00609015942002e2020b84103610510a20070100d866003245825512407005001c001d400041100d032052282d03101520206400c00c01551040348288002d1010f0143d00b4801040000168010b9043c052444140030015106a0301c0b02d6010350142703406038503100310500484500c2815845590414030000c10f03c1404001c94001441200c5118420390202c1d0f5100c400710390300c3c00210307005000501c04600602180e5003903008921101401041a036403000c00200c0a41400c4040c3d9402e8080042c0660410081d81c06021180c0111841d101030b5041500c0c20340400d850313021118004000d1560381032441029802002a10f61000401d003104401c41010f502c20030080d0f000e10001c0c0c40510170680022014901403080724030803034201c820203003400303042d603200d4201100e0750000701e0502c1070606007841183c0340c071141e0045070141490680d60701c91a604056003190b10507044441442d08100d4041c00c0f4120000881ea4100c0ea03030061b03 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 127099667 1250 127098417 127098431
    0x2030312040206092112070b01090c030204150e030c0103050106090e090a080c2803090504090c050603090c01180608131a0c09040c03050f1b0f030a150803040b0d 71
    0x3c1c000c0c4070f11030865078404200d003a8181180c00c205542640141c180c0c04581020034901d0384000d480c060001e000f4800e20103500184030342d401c103400c0303003025045c903040160500352500103031b2119080110114001603102d820313544a40c81c0030400400030710400c0c2400c000650620100402500c0383d402109082003a800100308818003c225501c8121342191a50780c4800c4407400140e104c14507012400441c52170303110b440700d500014200d54242d16a16484584c0484e1900c002d10020304100351003904d24440d519000500f94030cc41d801144107082050140081040c10000074080c1c54074449a42c01050b40001c051291a0b00800204e801060300220f0034040d95042c90800d00014010a0032380180c014401407101c02402c14000d405c0c1d0910444060058070701c50380b0100c048410883d284010191094045544a11591031034030824118a927202c0c0b82014080c5000141c0c0e1068074102c3c241580d40c0800b40000a8160428004c4d00b502009186080c0c82c14a05400a009201007403460a5903224 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 127100917 1250 127099667 127099669
    0x10090207020d0804030f020907050c032b090b0a1a0d03030b030304090c0c0218070f05090102121210150e0609010e030f010c020706020a0503040b16020d0606090f0504020303120402 79
    0x80c40501540e119600d43c0d9160348900d01b840d528104010106d00910561000c60804c600900594454402100041d828181500e400349800352000b00080b50004203422040050851400f039400300718000c03800b054080c03d01185500885130340f642d009180c03240d103811022181d90b6001146243c15003614010485d500c010001a0840c4565441000400e00d48000c07801c140d90000b41e44000c441c002c95a9406102c0180b41e07103204074204a520b40009103810751590b00081c0920b02501e07640d501841100c2201310803941e503519a41c0f204007201095039090081200b5002c000100c800a01140550a414014000b178003900900030344450724821400442c030030140340d00c6007004075440d00001381182c0028119803005402440307445c4c4000014004c031180030640b82d000090385003207654030600a5280c1494411525071a8110303c0345840d021102c00d284601682d606030004016038096032000070140d1400d649003040f2040848141000b071706103801c100140c1c0d004019600142c1c0c544641e09a160f40c1c0d84 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 127102167 1250 127100917 127100929
    0x903300906050906070201030615030507020c0d03020d0f030e01060e01080705030d0c0b191e050601090b1605160618080c010509120a0204021317030c031b0106050607060207060f051009020702 84
    0x5040f2b40001e03101e4000400721198550070150003174580d5025100c00d030800304c1c00e200c1d82510504028025074411a40304060a11480c508405591540ba000540c0038048050038251141079001c0d20311b00e440800103100500f03042c0074600041804030000e107155001c03020090643c803c1286c01030b150b1704020b000150580c910789030350b1300200300c50302d820008800c005900c11100d04a00c03210f842c2d4103151000080325940034068807810380b008100403d007800090021402d540241200883d1180a002040380c410040c00e0340c5500504040e840e0300c2d014907252422040d8460340c0d40d100307001940c0a20b26200c140d98101d022074900110654104440d40c40381034909142c0618280001e410910004003043d401303040c4d01061043d102014100150310343c8000078540c0c0ca018515001c011500708100e4244d003885441990b81d0740740804800400c4295499000a1141d00b0001045d075502d50006410300400600380303c0d11508051400d400c1042c0c0c10692154a1241e03018010440e41540c00549101035603100 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 127103417 1250 127102167 127102169
    0x7170f070b040807060b0a051c050a020a080307021003060509071103070c0609051e0f09070c05030c0615090709060f03021b0309010f0c0f0f020109033009060509060702010306 77
    0x10402507182c00c00749410070b0543d00c242d006642e100c0c68810b1070340d014544010240100d8400903d84071702d4102101c5026140c6005c40421034141c40361010000040c1c82c1c2406004c0180490009135031540240d0040c072000c03061164000040514101091050b80d440d9074102d90801081e20341481001c0890740c44a25510580002803e10349040c4400941e541e030041c000c1d42514006ea940315810400d68503c40300842c0083c1c8401c3c0d0000c003126100f641c80c244406c10580c08642c920380031005040e1522a035040da03120600301c4406800400412480031020304d0300060340d41c41910940c6540c544018024082c10302030050b40c04100d0b0540e8103002141c42074041d2010141110341d2440d80041c60108103580760300c01e030800390209441012403000d250150401d04006038011202c07200070a50303070381c070489600e2584030100d050041103040400031400c8001700b401c5004400f254483d0303880c482c50444030881c4241d00b5041c100405c0c980c06024140d400400c2c0c9400c000d00365002c0340c94040601c0103030701070001 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 127104667 1250 127103417 127103423
    0x8091513060e01021c0c0509030a0b0907030b070f080601110a1704080706090e0109050417070314030a0b03010509030307021f0f020a02060703050c041a1819080c0607170f07 76
    0x8640103030500428031800381c00c0c803c01501040240360b0318801b1f80c0c46029036200b659168000d140901c2c08140010455603112102c4820b4810441d102d030348030340301614141c40c80300004041401c0da503a0300d500450398940100c1f003401e20311075115008030829aa0024814000d040810000c0481552034098040ea0003030304141090703944c426165400145144454481d20000209040000540f0006480351030b000f07a0b081104d441e0020031408070740c100c2d584030110131001c00c600c1d00e8003000300c036400c00042d6000d910503100c003184400d546400c0509489015150311943c1e041003050101c203907000545662000001a0003d80700b81c21110b901d0b000f06401e0382102c80c643c2c0002124a4815400304541d072140c0f109031810000340e141e188059180740900d00810030002c04905068000310905409080400b4025802d0003a90340382c2804100b41945415200f0580503180d0018408210705108140154000780e03903150034031031651a202e40d009034480c0d82c8101d10344001022070041c00000e045a80c2d181d0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 127105917 1250 127104667 127104671
    0x120932010201150b090312030114060a090308182106070c03020109021504060807020304031205030901090215191e180312090603060909051b04091e0308091513060e01 73
    0x5541c824513099a48000c2540340720340200d007141c804841c420025241a5000d0591a441c2c8417640000d01c611584184100424803198260000019090038001d001c0d1600d40346000700c03120143c5c0244464a031809610400000240074100c01031400040c080e9030042052520300120420360030181e00509107800d029402c189440801407428603000c0c010300888074160380340300d43c9a80391a000c036200d002e24000180034103035102e00030040d03611039000b640d0040c001030f0001030a0300d0558009440a01e101c2c2e01c00300852004aa01481c42c0030301100003d00c180303a4208101446900c0c3d4054a40042c150003070000d00c420032050141903440000094095a4800c000c0e0401803603071075018201208a00c10b0800003420920045150142400707951034640c0d00c00c005250303403581d80725000310035240110745d550842e64076070070b17070000c5200c1e5000b94a4102042034180034246203410002d011181c010b2001116501c081807510100001c0040d0642c01038106a6605144050b4586480544202c0303c00d003a03030358 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 127107167 1250 127105917 127105919
    0xb03010e0307021f0905090c04050d0f05010c0201110429120604050105060403031e0519030203060315040f110409060f1509050c0d020708120412093201020115 70
    0x404000700030880140211050102d02010512015000e5400038060700000d03800c140410a41c1800c2c6041e5400a142c01c07105400d054a80021640c0c0100000d03098949618a0800209004003031099411603616480203016800d90240d1a4255204e00c2c0705600340418039861080f11142c00d80308521343c0c3c84030071030995034801880c2070000210b0310a80b810b920407882c04000040d07034500358040b9000c036649a140c000025985260002910b46410080f1081c060200030881c0000030201c141c0380304e42500d840058407814810207040c0f6041d907005280c0100c02c121024403000c10401e802440c4540d070700900f201c801d000c90901007001307012800d070004c0c032250424034800c01c00c41144d0032542020000c02c00315110540e403001030400341e91040d6144c9086080c01c0001c1c0c41034000700d4009110281c02880b01c5490008110010607480703c00321001c0e04e030881520600550310703502c461800b000b04201c025180144803c3c2d20a9828100b400b044511101d07108008010203074001e4200380581420020358140403 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 127108417 1250 127107167 127107191
    0x903010c0518010c0b0708090a0803070504060201110a1e14030103060504030206060d0b1303050f0304030906020d030c020319210506010e19060804020d050609010b0406080c0d060b040b0301 83
    0x142d0041030300340c0c114070300507203032849107500c103c8600e003a0b550045202105500c3d088400c2d2152500540400761500801c0754140118401000450088030340e9914a55201e21b4442c001782100e9490a030030071003000410a503d002a07000704901c2034590b0300031042c0d0360110f41c21802c0d1864002c012410302440700c084000005e005c180c3c1c0c41140b080c1d009800f0303280756544490811154140b81d010060400d91807002007540c420040d41d0381000984a414001d06d490380c0141c0e40030854008940850014042d0b110a0003055410702018029042a05046c0092800e881021b5103034016a03180c0c80c25110f5640600c91401c0c410741102140c180480c101c180340441c0d00c40148040e00c2c1c1183c42d98082a0142009030540c1040c0c0c20300d15a541d404141031510751f042c01012680c03030802910036644200b0080d0360030301240301401400e020780c0c603a50001a44450701c0d4144008d50b41e4543c012012a001050b42680720340b55000c181c81215401a000100004030070000b40c0282288a0398507015845c290213000303e = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 127109667 1250 127108417 127108427
    0xa11070906090f0b1807030b030303130302010c08070c110d0f03020a0c050f0a0504050912130312110d0e0a08010905070f0503030c1c0915170906070c020d0501020903010c 75
    0x103a4501c0e440074007000c204070512900752488030b1403060300041e07080e100b0448000344179403044d0440c03100e2402041c4000c3d400c001038a1500140d40300490851800300391801c1540900c1038541400c0d007800c01c10308600e08100e01900301c0d900c0407000742246020040c464815039428140210040e4407d112003110911414000d5440122010884001c8504040481c01d840d1580403100648001001c0258036401c14040c40003515019008440758480e9440203580c8041010240005546140d40c2440782443c46c108400c86240e1a940b400c00d00c02c514000032412800858140b00c0c8100750308204080b0342d500030100b1000741c03444e40074540710f520b4000000200f010225510301200c40c0c100c240b200003a200c0081648900c100710003106a44d02010031222600700340c4501d13480050407800c2c0021055660046500c41c046046900000104031a00c8030004a000d80d00803504800762000904944c41c00440103091154840c8000c8c0c401c400800e10b60341000000d4044400c01c030f5001c0c5c020300403005451030180c2 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 127110917 1250 127109667 127109669
    0x418080703030e03040b0703032412030e1009210b07020f0606040b060313060b040f0e100923070f0b03070f0f05090609120a150f0e03040302060a11070906 68
    0x20010341003140c070044250001043c1c40a0b10409040c06140107c940e400350000c0c04055003400e100d10080040c08004109103030400014000c070034002e102408107203030081c200096402180d00c1546003c07020034409070310500722820748a144c030455100503556100e40940070b80400008000804080400a0103540030880400d407501600c00c8408548030103007001300f900c002c0b010b800d4001c0000d000090054219014110034103000b944001404034030700000c9030a03a079001c18405d408689078001600000420042041c0d40805100f0420016802c1c0e0fa59044003180150540030740719a18420070f0950b4401e10208000b84144c0300314640841c0e42d001034001a030021a901d8010444800600795124010010f8081c6042e10350360350340c601181c5104012040d008050150382000d001500e008401d00308204544500c3e010340d51103e500c05a8000081c15604c2c0810345890b49800c24419641c058030000a40d01602e50442e00c10b5140c180e00c110455500f41e0b104282031242c231a4040000303030103843e80c0c8044 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 127112167 1250 127110917 127110923
    0xe03060a15050307290409110304020a0e09060106050d15030606061808070605030705040b0309010f050c0a080606030702011b0c030f0905130b01030612031107051f0e04180807 77
    0x3010741d0354942c20103488030298400c030240302e281c00021420780c410340044d882d40f440c00655405d00f810340301c1014208403003403c412085001c900100340025850719600380c000409016000b0401e40c94417242e020784404e0103108200901102150081c500300094000400c1882e00c202607070041c542e68180b010252020344241e1002c41c1c810200b400c54174408446803426544500001e000c0c0603e03260341202c031903000800840401c241840040340c030800c21001540241c04146c008140310380c003031400108560002c3c0560516190401c030384d0502c4d0790822a6a5800003048641c039440e50342d8480141d0160001c1a4042c100324210501c10301440e8000340608030841c06990fa00340c0c03e80c4034180558000005004081d07204038041d40c186148151034022a241c024180343c08034001d40e8500c000300c641140c102080300800d0303c1e04482c0300d428804000c4c00c001003008603402e031b140c07840d444901c4045c0000c0d04107000800076503050410702625903130003407400c0103400c04010038044d049041c0303d0000e4100c002c040b = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 127113417 1250 127112167 127112201
    0x11070c0b09010c030e0312040306150803160206090d0501020a0507030201050c210a140c070204110304030806150705031215010306030308180f0102131e0e0a0207030e03060a 76
    0x4a0115610016101101d80c181c403032108085080e10182c1c0c10b00842d4002682c11b00c622940341d1084003601000e00002e6100b40804105003c02c172007803580114542e0411610755000380100c562441c00864030307006854055034140d40c0c5115680108128241c041303c003500d00d41c00040d034204002d60101c01481c801e4041d900810283d210300712410030030300c150f006140b61004103118900111400220180d000110b90300e000481c941d03442c2c0c1ca64141e0302c0072100d41810100114a01d808d500b072602030041d1710740031521940e1071864543d070040d02c2d440000d002c1d81e024005031244049107a4040d000c80c0c81c0203810400b2203481d50310103148405480e904584000202240501101442d402401190292075042e15012416074901494204100b59965075403030b0b070701c5881c02d0040d6142c2c080c0f00410740a0300318111070081c141003c01c4021000644100e4030301103840c09030208141068102c4d002d42003c10400c02503507640803800c01315086071884041030b501d80501820b00c0000e82d281e5125800d5410004a0703 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 127114667 1250 127113417 127113419
    0x110903070e2e0e070309020306010e06132009031e0703230606060306010207030b040c031a010b090d0804090f090b0a060b07060b01030e03041508060904020d020904110411070c 77
    0x3400c01e032082d80e107420030381c80d6120b02401003000081141d64410f0481c54000703045031441d00064034140d002e9200001c4104080f0a112079130030440182c0c1001c1080300c409120b403808d07500c1c40030300f0000050001c410150b00411013080b0b541c0c00740321340c8803110000b5110704010b4254890058864249201c21030700d0352080c41514441012048141c401c0c406098007a00d000c0e034600060008a60000f00401e0441c092440084002900701503ca401745009480358400c07642149007081c010720094054003a0702030040d00401c403c110042c101c8800030001e446604080300b9515000b070b40c0740216080741180600f4000001a1512141d111710082030240640d804d0548541c2501b104a4805020341c1d01045d230104551404250b154000034850ba606240004039000c000341c2050171030700660400c20440c03c81c4400312140c0ca90184680d50062421940300e002d604140d03000400501040c14002d0085864038005030903c40110424041d02402600900c13a0250000d40d0442d25404001d04450039090020 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 127115917 1250 127114667 127114711
    0x426031609050f1c030e0312030a050f250203070618030e010e060a081e0112060501090b0a0303030f1e09030206010b0a1b0501061e050102010c0807020d03110903070e 73
    0x91200360801400034252401c0c0e440d500c031324640c0c4c0d40324150207011081c00d004801e070310200202045101480c100e240c82e070a0070340207001515000f030200c0003e0700e150410301c02050707540c000101084003440360801e407604411005905600405d07102404d001e00d0300c2210b18241890b0101d510021303100f5a14415058484401510307800c41c0c40f4041500700d00c0520100e0405409a200c607600300807241c84c0182581c031030044890002400341c002d451440b2625a40386c080000d10301501e400f400b6004810300030460304e00042060b1055501c0302404060700d45031400c00403250380e80304c1100c144118070103001200f07000b00c41001070110088201c0043c4280720001910071812400d41360740e003506694180581c0d880d1000d4050b24007103c1c1050740c180d541c43d140010000720140000014407031000d40000803500e8200068215160105400c1c1446401020085416130202d566820004581000922803112420b8079100740100c0fa0b07095010b10401001158204400c08054440c400812400d100c028044c8 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 127117167 1250 127115917 127115929
    0x30c020f03010e0d05070c0b0a02160f030b040201032c07050109080f060c0c07090204140411070312150302060708030a0c022404030c081207031d0303042603160905 72
    0x141203c000c03500f040444190052285004142e0140074802e41000c2da82c4a14440c0030b281c3c0820b440d48050380c03003111414038100da14504000101010164a1502840e54a031810f905070300603c0241059520908480b00025942801c0642d2400000102e5507914202c800e6503031f100503000b014081400c40e10001445000020071144510075100a41020344be00684d02e401c54000c0e40244040b40903c03880481c0140e890b03c042c0c402401800b282c10b2180d41c4100c140802c6924081e5034205200c810040310300402e403c00c0c40b042c030069040703070002002910305042140c2441c0c2508001d40c400340024180080c410001c0c007550142d401d0010411440b01740d804140d03078a0140807400c0103510a00e03000300c400710080c46107265000d8002d040094040b241c42e03070740c070a840d84103207003022128a83c01c051220041d45482000308030721004000401040400c2c098580d43c0c040200020118080301c031040e4600c2c1c22407041d18500381804403105480382000803120980d0000850481c00144114100090a04d464 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 127118417 1250 127117167 127117181
    0x603021201150302130e030f0a0306050a12020904020303090d0b040b06030115060c060209040204030f05010e0d0504170a1202060f1510030b042406031505030309120f0109030c020f0301 81
    0x3042d0000403501d154203125810003c010f51070b030200c1d591000844254800e2000b0603103c001e003c0300039a50b15154501400710340260300224090400c4d03240c14001c0045103031741c2c100c0761134045420310380c25610307480000d00d14800c410030f041c2c03c1603076038483c8020084056003941c011481800e080b83c143d603420742070608980402c06030b40c80010244104001d018010300044002902801000d4a061304d80c5011038182d0340903074011500f0040b25900c40080c00403c0c81114100040c41015014140001c0b4000b4201c0c000d07030240d0501c03501c15008906c94010100aa01c010950041e900c0c82564013020010391070f01001c0381c4108800b9036040000c1c030026540c1c0c5500c80340d044001e08250320040103690441c02800c00c51b481c607070030642e24a03458100211100f510300d480304000a12010035130601100034269881d2010441c0c2c6180505805e001c1550702100341d40d842441601c240d5400351401c3c01841c035100c510440329406501c0c1c0300c218002e043e400709110210394001c0e941c0248001c00f80040c1402c884074 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 127119667 1250 127118417 127118441
    0x60f090e07141606150501030c030b090105061809070305160e060a030507020109050f060114040b0a05060304020a171c0e030d0e010513090b101409090a060b0d0603021201 75
    0x2940c00828042c0c40040090a0030b440000d443c4489402070b540e9001c1200c03814030066010300d240d1744d020029580d0502526051035024a82403040070444400704a90441c18007655201d185e0110b032114201e03502d00411250400c009001c10316034100588003078000c040a950101c0d464040d07080c044038940c0030b05074081c41050041c1019280600c1064102d00600303026003a001195250401c1c00d0100e41704010706240458024080c0070107525000102d0f17500c1c0d084000450245e82000600090380d610500381504540301079030381c40e6030f9035580d01c0014080e13610340d003058418901303035860071403060f100041c41505061800d041308012101e51109840c0c4a006102c441d5240e440000d65040d0303240300e40300c0d0000603801810204c1c10503d184080b4800c40100303030030501004e942c1d0111107845283c002c40b45c1005004500b0710344405051141242070622030100d041e03005805582c04030b80d154000b82d10000040004d044c030a40c80b01911450035010349090711050b0f100d0710f10400c0e90f001c8205c041c8280b00741c1c012 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 127120917 1250 127119667 127119677
    0x60506161712180d020a030e0d0602040506180f090f061306080102071505010e010303020303041e080a02060603070902090d11060c0106080a0c15050d05150604060f090e07 75
    0x81550303034080d2460400301c0308590100e040c0403042d480c01e841107155000d1994107140c811a03403500d10141340740c14032102240c000c40d4485500440841d4006c2c8100c0e4903c141901c1e00d43c11103806041640c064403aa9010940005002401e00313000c10750b02c034501a24140458031030042e050f10750104070030101300f030f0b8411381811021804140c5170b1410040404003042da000b800314105a031940c6450891b0003d41040d6110f21050301d220041c4a07191045034050a8042241240fa504507103009560f070000400047c000b14a140c0303681ea1040ca1640c003505a10380c0681c44955a540d0400d009440b00c01c00d1b10f000d4000d10a181c13000ca05803003107000369030200101030098964240242c950702480f1216102c81900071108101c2540d2000d070138006c00c0c010344410300040500703206034a48404000099840104c0c0714000081954501354000100e442742e41d094040400e0648540d605002804443d400b130300c0d0b20100014001400c0d981100380b40000c1d04007a113800702c50aa90f0281140080422221400068 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 127122167 1250 127120917 127120957
    0x9090b01050d0f090b07051206090c07080d060e040303060305010506090105011211070f05010504150c05030a050402030c030d27030f060207210903170c06010e0a09080f0403020103060506 82
    0x60b050780502040b00b440500451143c13665126412601d10544240d800118001003408140b01c185e40b0003034101d00143c40b0215146004590305c8068010058010800100090440c0001406d6004070340a044440c8a048003030401d8940900140341d01e200465070740d402c1c040081d190703140c05552103040390342c180c48001e404a601ca40200c01030008c3d4804052011091214002040030801c111003094428000005c0d18202800c1c4642030303019040784521441d00300542c80748556848000c1d250882500308010034030f601c8500c0024109150382d02c01e40d805100310305640303420551281070700004000d82000c070346015034080742035500310540b0701000d8150701c1071030710300380c0040d101e80e0061001c64000c4004040c0b1004003d4002d690014a040e0800040c000c80028014851030703a91030000307124000c02c150702d41500c5004c03d5446007014854045244600303400201c081c48581c211000099026000c03da4805510103c4e40c0d264020380000d90000c3d00e401c2e00850301e42070600c202e50404c007603150301008007 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 127123417 1250 127122167 127122187
    0xc030606020a020f040e030c011805010605090c12040602070204020d1b0e0904170405100201020406120603020906040504060b060a0305040c080102040308030a09050c090c0a170c0a03181a0709090b0105 88
    0x1c0c2000101d420300ca407104108c0c1d0900301c03078284623021034400300505400719140107003040303801d543d03040d0051442490448140805c2811010444e03801ea20201488207096966042c440004d0080040194015000090102c0011802d070310807060900c20225411001c41c06070001c4a50080030155942c000780410089000300c1e1800c2140442c4d030f08840c0f861072400b1380754008140d145104e8907500d00544c0d00807805000594008810032400486e442040245505e582c000810201010b000c0d14000d65036000820103001703554102551420010380f5040d5605850b00e40207000341402caa0645030132815104c0400d41c0039041c0212401c8070b400c507030130500755250034400700010000d02c3c1c42210303117124241202c01607803a04082148210740e035052003078680300c025002600860800f02e101300064111420014040164001d80b40c002400740350000b01d0f403842c1101078054103041a4090045a082c01802c06010009034403140309040740d40d2140c1e149a900c44020003a0381c61048450b02065046c0310707940c00 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 127124667 1250 127123417 127123421
    0x50406020a110a1707170109030c121404120203150c120c0415080a15030206030106050a050c12370521010b03100e09070e1b0c010c030606020a020f04 66
    0x103031210042c0703e103070b5141e03407030040701a102c400d20b80f901c0395034000c0e8030b042051141d440b64002194410700002d00910400c1e50b0000c0c000307020142c0c024001c80c030024404840c0781c40703040a80308460000c5c080c1955a07031211544801d0f402d60308412842031050001f014500301865500500a003840c1c034000d414038101e00595400c1040082070003021a4041c080050390006202c210350210065480d80625810503982400580e00d1001480b00c003601030040400042c0c44030f01c1241e0440e0914a040303511002d0b00241212030384510148075089120754043d80100d11822801000b00e10740fa01209500301181003859440703407034042d050640d44100c001c0c01401940c082d41c000c00d04603411010314030f0240710b0400300000c090030a030052001c0d01804010400210031980c04840079120010481220b458009603587c3d644d5030701e02851074074440305000301e2804d14521201800354641a02401e885840035440c450082c102100301c24002030509030b0024070340e4008240000c805070050580c0c4019086403041c400 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 127125917 1250 127124667 127124693
    0xc010c09230102120706060f06050a17060406030804030c0603200906030a0b030a0c1e2909060a02062401050306040c020717060412090605030a090206070b0f0405010c050406020a 78
    0x10540c0101c00030030f5031900c00c00004203c406c0c46041c1c00101d150400c5003103a04003c03240c0041c2d00b40041048849003242e0800f5500211154021000141d59509004280548619840181281800304001c41040b0300c09281c40d081d10b1803603604105c1340d4a8008210004009440c80109030b000800100300c007401c0c05001141c0c400003180011031207004c1500171030320700030340d410050354400c0b120302c001d22401e804816a00d40d5044101ca019400070300b03000d00354403000d01d4802c1c2d03003005100d00c0d50340b0007201e0b0590041e104000f4000303040d1500d9016041002c1d4850908464600c584800428000c40303a5911600528862106940711415a5501410302006100d980c103201c00394402c1040000310400040402404800ca4401426590a29203800754038111084050400d0101c40002031086950100941e1f03401102c060000c031f1004070358004141d60b842034100140c81400c00c00100300c01143d54040c1d450007207100303400812452005601c119440e005a0181c04d0050700044d4940002c0744400d08841 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 127127167 1250 127125917 127125919
    0x30304020a09051b03011211090c0405012007061701080304060e0d06091704030201390615150e04060b1c020d050a05162d020c040903050c010c0923 65
    0x700c08604d00780018141038009a100c411180000d4500700100300100da40d0b580010000d6030b408449051081c0f81c0b90b0940141c0c0183c60401c045010491080e015815003850040e482100391031001d5100c3d0307002407008004d403100c1030a10520b0b0b000060312102c00030880f0308441603503403800c800c0c03032860040141085007044165602501c07070b0905004200900580c84c0101410360165a40754038500c00940a4560303690b14180d00d14515081d02c040c1d640c1030090326174000b0046d0586102126624102c4024407030005c3c01c80b41440102c80215040744c1c01c1140301e8800c00c907519240814142c01c0104000e503a258011340c2d0020324140006511100041261903a80100c440090304005600d48240c0c1280c104465a800c1180c880040c84000c04404400030a10b1201e480c005402c2692201c405091500704d40380702c044a0780f2985c3c1c08025620074405034403014030080082c000f4400a0600401d0780e04150b5581c2480d5103003a000b401803501405101d81111341c04c0040010300c1c1c400f00c81030300d0321601d122a05 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 127128417 1250 127127167 127127191
    0x30a0801030822060f030c03020405090a18081801090b0a0f0e0102030c01020304082d041806120b0126060103020d0804050303031018060b12062b0501050603030304020a0905 76
    0x144050821203044a026040a5171070b8044240b01c094004c084d11510f40d856001d041c41000180f001d5183c0070070603a80141c10900210b12000200c0e15542840c00102000d400e60f0000f04a0344c01c2e00401c1e080f90019181e00f44d8030100d08603151840146a440303503281c01c80104070391003100045240120007071902d04c0414015241000e0451601e142a6030045a04944283c80000c0200403000c0c0f04aa030744191042411054000000080742842d0344140c0c05a0241040c40c507480b03040320113154001c0e40140812042d228181032142c0b0b807140071803c0c2805030309000000290308086034001d41c004035554201070001420b46e40d103580c0030701c42c2d031a4481c0c2080d01c08200400022904e038804200860240d8003846241541c80c1c0741c04240300b038161222601003540d5040103c100441002102a44d0340001ca0781d01c000f005032203c1001441d0103007000100c800c00d00851404800002d000d800c4490610f00450081c00b8071743d00c035801c1540b20301c01154025805041051300b4484180c8550145a21030103a40ca8 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 127129667 1250 127128417 127128457
    0x103020906120601050d022d0906030c250f0624050607020307030b130c06140a05210a020c011a090f0a140103240603150902010507060f050117030a08010308 69
    0x411b06036400302031f8021021a4604851404c2144024070312000f809100e40e1508151070b0000103403040c031020b80380c82070701ca0300032540c0c5070341d80c0285030b040040e280c03082d005241003403107443c0800e01e8550300042503400d2850030030080641e18490010340341c012080b0b10304240190600c010003545801051083c0d805104900d4044000780401064034041d03044103600c3c0c102c625051408511006180e040502008951068617102c0300001e02507500081103814000e4036110305511b0140d240720784001c1c04810101d1403040c0002254039a00402001c4011300083c4100e00f000b840211000780403008058000c242c583c000b428102e0040700254001c1c83e5403d0101e05010700300716400c2c0003407007a0000d54204c01201d00741820030700081103200070048440001e101c1c0d03e16548503030300c3c0381c1801c184020001d034403200c0b00801c41e031245048490003503001804004071a0b41540d0f0100401090040740444c0c110710811000201c800000d641c490b140070b5075001c0caa40c1c01c56580280380e41100c00680100419040 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 127130917 1250 127129667 127129687
    0x4091a31140318130207030215060f0301050a1509020711010309050f06072019030e010210050f060901050d0f060207061e0e0c0406060507110102031c06050f010302090612060105 78
    0x24480343d0f00300400865003021074401c00a48181a03620f025050748100224400640c002c2800381008100880507040303540c465000c0f941c09610300756a10790551814080010500305680300e410405402981040c01c1619803412004922480390082c0c0807050252114401e5031003a04800102071149040c1c0b0030600d5040c12443c946442628100045421328160300009480e2102c90019514500d004165690f521070f824002c43d03e650b400a03040000100700821242d00030444803d84c264503900401c102e20703000443c9400b058050741c41c14440c5090000000303603842e05d08282c059194004488c101300d0101961040000e6101745030480b941521403a4400303071070000341d00c20584031540340c0c4085420350414011038200340d039050010340300b03600d00762061120584c0001654840c83c1e0014210508409030b20041c0d00d5030041182401045954170400c61107264107400100071200e0559000c1c83c0c04030311500550903030286100e4a41c00c03400034403a08800c115100c1c1000e41040c8181801460074a5402d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 127132167 1250 127130917 127130923
    0x51b0915090d02031b0103140f1602031306030209030d030902090106050304110a080105061201060605070b090f010203010b0c0607090e06060310080d02010902090114090103030f0e04091a3114 84
    0x1a0401703861896104540c0d15540c042c001c0041c0c0408101030764046107000e400149510302c0c003502c03100d1000e24a4000f06070700e031700810450306c440014000d04080d0070350f81d40004010390f00001a40c0c1c004e006044031305860a0182c0280300c98aa8000d2030744c0301c903a080290480b99504002d100343c071201035100421880ba22695000d00250981900120b17107490f0036070038001150b4171000d8124860b03141610800082c1c1c0d220040d1190700e940300001d800543c440c49012881d02c5110400c48280c2d510010000503646001c40c0145805405001038440f00d560b04c40040d2910516440b9084840b07074000d00041c4145003400055a20100c1e2900340720b00191540e00c0d140c50880c1c001d19000150307564504100641c54886482401403100429003021155988045000b0740c5c4184001400c2c4050a0340c2c2445480c02000112900140500f08014441040c00e0003080d8081c3d901e9210a94820100800c403500c410201800140700707120075500a9a6203030300703420031403101041c007655075030003c0350800c1340c82e0018 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 127133417 1250 127132167 127132183
    0x9060105090901112a0f060105040b011107080705030f030901050301090c021c080a06230105071703040c0e0105010e03070b0c0304051207151803020405060d0510051b0915090d0203 79
    0x65218070b96001d5484401085c4c07041d0050380c40341c0300c0d0b01c450031003206c000000407400c0c150380c42036602145814501c40141e0300001e04403400c940d1401981408070f9100000262501110350460449181c00c0d0308100898481c840d510805000540400040c400104160082d0b0803036150f43c412243c0c85490342c1e500030b20004a2070602e00002d14804144200c1d00e0407030140c0d1014106004200781d070175900b4040c400e400d0300300b0540c0a0501502103100300a2200640702400d00c80795070101c2036500d240034074054409a1481c0540444064514004529940f184250110380880640140581410316508071040d402440901c00c0c9480100004603158444801c030b8231980c99804001e218850514010107040801d031290358003000b003980c83e1031040d01404524a4102c94050301d00043e00e0f100d0340041030724a00d1060f8040d102c0d00c40e600313110b505454990300540c420790200e01800300d0255841040300451059140070355004418051042a00a01c1c0006050244009090904050040e80030070708003040 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 127134667 1250 127133417 127133437
    0x70f020f010c0b07020c01031506200c0d120801060c050309220608010218040507080c0c1e0303040212030f0f031314070f06031b030c0201090203030c0703030e04050906010509090111 80
    0x2043c0c021b641540c1600032040802c42007a5a200300c00d0800e00018154584108482a0304055101540c00d1a00a00c80d40402c80d01c0508039514100c00c60030042102c241c030707400800002e26a40000110684502408800103600c5405145010125003c02c141c42240001d6001e81007900b000340c903454111031050344000c0004000160712120824683c0d48811400c1040301d0155090104002040c0ea1226085500c0640d50103c9070300d581000303117640c2c078103a600503040742c01c0c0d02e1620141080c280000080c601c12442103503000e861901c881c80240d00e9004520341c038203113101c00303110324488210182c01a51340541c00751002c103c000440e4440402c08428212a10fa45801001302823215010560004c000342c611414107014429440700013003080c801049031002010741d034011440a1610070340024000e640c0044c1107a0721010303050000c0352120101e2104070080b40c00880054a1803d06020b154803820403040074200d981e10b49000c0c0b00803000000c01c080f03542e541c0c850450b00b030b2035080c0001d0000444 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 127135917 1250 127134667 127134673
    0x30115030b0f091005090912040510030209130e10090b0a09030c0b04260405010e0105070501020d09080d0605150306012307060c0807030e0a230304090f0c05070f020f010c0b0702 78
    0x110b040c0501006c1d00e4058a42ca0042d0811901031040b45e00305402c80b022200c00f5942903420499943c0f0803402401204d68032644001107010083d0320145c01e8010b0541d00d090a8140c48559051012040031030340d24410003800c4186501c00200d4003074041e40308004980c0a0b040c01d186114080d6105000d01d1002c54040701c004201c4403c0b00d11001c0520901f04054592403074007880c1500b0b240000c4c20000c0141c441504004000900c02c04110081d010b440c00444038403c2448400054030b00060603402044000b880140381800c002850f2030400038003101000a80c1c415803560320340d840115841141d4100052004164201030f40964801c18014180140103500014a10b03003000b100034144540580a4010942003540c00d105044000c02c02105440e8000389540803030f21107000c2500d40302c004485111030383c0400f04000400180b03680001d031000756855420800c504144005403007038000e142010707109a00f1a6231020040c2000f140150a64205041c8615203034050740d40c0501104c0700b1120180160 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 127137167 1250 127135917 127135919
    0x910020c012703020c09190504061407030e01150f0e060406260615091915140306010b03100905130c12050709020307020d030207080405040204032006030115030b0f0910 74
    0x580e040c0007a01d0b800804603103106d89400c06d9048420b682c202c2411403414039070740d4404a01040525840b01c10001901d40c5c03901c0d0b052804020190007070a10280340e03104c650032300b9040410030400562420540d041c813113031003995074180350704191f8486000344401e401c103948140104003030003c0601c1c42c1c407034100032150040700c1030f22a1600382021400782c200030407002030300e801c5003256491140b940e07803100070990011400e401901c03800c000340914040100b54914003040202d0030350301e007526283d600740b019001c59015980c0c807000f400051104451a0f047c400262105014440782c03500015040071003905c4040000e90540c9074049608807903804080b01d200a91013803410010107102c884c2c01000700041c21421480c01394006515000711400103010154005138000422003924242d501910026100315112901c914007911242000d49050b41902c07405040f0f01d4452815208582c143e03120340440341e4803c44e0046066018109010425074814841003941c40d240d25945400b51049081078a008512 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 127138417 1250 127137167 127137173
    0x3040e010312080112060c03090210031d0a020d030815090c0316022a01050c06040602031803130603050a020912071502010209030d0e03070f080d0f080910020c0127 72
    0x356207020420b800f44883c00c001084204e080011440035150000720104206c081081c080307004107114080294404240200160714590590004802c1c1640c003070b0bc020890f680030184c40da9009810341c001d51107440c05004c080080d200307805281d000a1102c204070051140b000014111010840d501c00c0108408000c0100301806152480e1080302940054040304141c5100d245024807000d0405032402c6407003c8082d04d60344150121540c03a080307402901d850b0f06003441d048010303600035990081d5a1103100f81060140c4008801c503114106440d159810040c5401e00a40207400b0091608504039400d0200500540714182c090707260002280c0603090f00381c2418100329031071446007251821607106102030030280d207001a001d0000e120609128903052405000685401c61982102c0307070f03500c0c294000040c2440b00043c0c5c40070601281d1620074a01c03046001c1218904000c484c2e0740d00a62100300140e400030a90741c002c0c01000c49840c0040f64a00342c01155030120440f4800561000e200040c000e018 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 127139667 1250 127138417 127138433
    0x302240a0f03140712050603031e040603051015030b0d050a0317010b120a0e03070203070305070510080f060f0301020f0403111c020a15050706050f0403080a11040b1b03040e0103 78
    0x12000398420003149070309040d00000d121503a88205d0040882e074030800b1850641e010020703207184000b00c0c00c0520300441c5089600c49103070414811440802c0c04d000c007055a1100000a60040d203094107100810b450b8102001c4025114002c24103070003980c4034251001085007401074002150007500d48400360080c1d004000c0c03849905a0040584203c01d0040403c4074030320f0304071070f9000b0411250104411113040d0360740c0d003184500100254148140c5100004006020030100102c400481c2d04051400100d581903c1700c003012621103048010400000305c1390b10301010a0000c03000003400046c105201e406903220703030340c2c03007900107035206503291581c0303021490f0259245a84032042071b43e69500031140d901003100301e400d5000d0944886400d0303940c80301c2c0d148108161a0125003254041c00343e810118114040b59406640540c0015082000a82c114010f401101c500041c92142c5a150034640141d01c010764003c0f40c080c1c2c01514100e00030082c542001c0018101406404181c400654036510740105 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 127140917 1250 127139667 127139681
    0x609031806140903101409010f020901050306120f0102180901140a03020d0602070803040602040501080a050702070618152a02010c020f06160305090a0e0405070302240a0f03 76
    0x40c1030030104051190310307480482c040d2580300c0d008030961103c2c0400006400c102d00200d144294500d00348510102201c90300c00140141c8045000700314942c211880541603204002100f4003180040012448a08000c0504814000c100c2c064400a490909009099a0000f100c65480d6291114032407414905480c3c118010034400ea500f5030959245408540c0d42c443c01d1001038480c0602c0c0b0100d200f40083d5070115941142d100c1e12090b034a1074a490030700000e41040c014540094400390000da4844114070849010b007007650001e00c0f00e00d10f03000d822200700b95950100c0801d155417a81c00202a0b4500400101c0c10985459448448090030081d0303d210301141c21301b605018400b8514000750342c000d52300c50700c2c003501070b610032900d0410203010071128450f90605e502124000c081a00c10301d0780c000090441004203c0703007051402d64501d088010120280c2d40034003a1f0b004540308100504d02803107400007002c00460b0182d883c96800d5507040a90f00540d003c540450000140c182c030403541441011 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 127142167 1250 127140917 127140947
    0x2011d06010e0a111b010204140105120423061518041106030a090210080f060303071703070c170c070605040b030a1505040c0507060b1203030c071e060903 68
    0x10800d580351440e01d0044030000f400005030360396202d41003182d02400a0444900b1204420540041c01410041d207000b5803261140003000681c02d0041c2d803607580704408448100c46c41e009808a162690340740ca548141013841c550018000718641e4964070801444040d04c42d5451448441d268840401849981401e9400450fa00c0403801e0800c000161044100c0aa41c103098070055100e0f940c004015004140107500a5800951300c8541815190301c039203000c3c807a4042d419404c070580c43d40b600b45640d900458000070542c40a01c0312a00045105a000c1e5070720030100d01e41900118501e480d000c81d1002c03140001112100c0020b20103840a204006c1b0000828507031808a00d040d28103070201d00540800740540c5820341c0c07140703181044410038408841c05010014802c02141d411038401801d10392164408407511410308101100d035142500e12036000c0e0401a000d140713544e55041c00d40010b944600000c5800801500801c0c4d00641c03028040f00c1c505205180010b40310080d8100036101c000e41d1040300c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 127143417 1250 127142167 127142173
    0xc0d08030412050c100b01090f0305060702011a010e0609130905060906090a0f030509040608030a022104060206072601030602090111011505040908120c0702090108010b0603010e0601030f050702011d 87
    0x1038007100c5000901c0c1d103040000d1700f0001150000000107d41c809010303400b00c000208816130100501002080860261b441c43d0020005071011361540031548a0b1442d940780810001e00d80348110b418128002d00580000906001459001c0007504085400000050f07480d54030000400031a00340800c111a00010060000c2c0300b258803641d5a008032081c1e8160003400c0107000f00d05c00900d5240c036005200034160000940740c4510701c01c0d03002551079900d400c201d503002100d50004c0c2152000b420031a4240e40b07060380500543c3e40c9824081d14906c5000041d68003401c50102880000032401c0e85450207540301d0840542d4403010200010010b03480e50f02101c07540d925000020b0016100c85404104440080d140426081c6560030008228010864921741c0c0c42c0c1d4403030412104440c000000e10506208403414552640c0701c404440c02c89840d800110340148003000148003542100a099501510515020030520b0a0880f08030640342c0c10790344440541e464001e0042c09083c410b5080c40c8641c400002 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 127144667 1250 127143417 127143427
    0x819080405030702150d09111003021801110703050d1706041404030807020c120f0f031204020409060b041515021f0207020f06030f0403091a0a080601020c0d0803041205 74
    0x50542c41e44a0050002d2040314040b158954808094040d281c0e0b102c0740315010003500516080c0070220102c0d402502e84a940d0880340e5541c030b24068400c0c0c403c4503a0441c80e0300018142c46006540541c184580044c00e03105019000000601c200001c0340b2200156a51860394540c40c1024500ba4030081d00da10700c140d0410014100c83c0401c4400307158040d401d0f02d40a00240c40d0003200303070304012050140c1c5400c082141c807400f480c40800111110a024000c08451441c021000015128014414005e8140c0403142c04075015151580040c400f450041100041034111000010201c0d0102c0e001140200d03807965040050591107561003c03000080d0010745442c03540b0708007034868403d112080714449a40400ca0f0790640d1110413030580b8951014002d1513590503c1d0306000e1040c48212001c41c002050420013051204140e0035034440c04204100140c104040103a06807041200107211034114840c2d804118a0359840c04015030700c483c0511100ca0303690501e410002103c00c0c07000a00018442c04102e = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 127145917 1250 127144667 127144673
    0x5180a0b0619060f0e0a03080a080a11071a060901080a1712191103070e06160206030103051c1b0201110f010614031507090b030403110109031d0a05090703020a03020d0908190804 78
    0x4a84040ea29441c0c10104bd983c0c1c5000319000342424460458180000b190b280304000c0318000400940342d948580422990310b11007000034520090092275001d4100d0485500021000b42c07042180050b07013103030031781004820341d1200103c00086440c00c841d03440e107030132a0054900520030303242983c15060340180795150945014201150100b0000d014050008a480005403200320340b00d0700942c010b103a142e995a481c2010340d510b00d0b003c1c44009545c145440e500035100e010303680400e28440006521028070303120750010742e2040b001608070b070041e000342004c079041500700b0b11030ba4010f0f203100310703101c101c1c1100b800601d0300c0d1488844501c0c55400301034050001068225602c8021201790b0044560340f90380c0c4d80340890f5404500c0780707035107101c2d801d1070b119000305a00440340c3d841c070075080c190f24010001840c00b000140c000510a09400644e001c0100c2c00ba64481c0e001000da01b01c10b802c001d850203a100c0c15000480d0352840007600c2c02c1d41c01150381d40c02c0d00c00c022101c1c22411064501100f1600f001c3d2 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 127147167 1250 127145917 127145933
    0xf070503010605090f0d0b04031107080c06030c1e270f040c14030a09060b0d110402030a060803040b1317030f0a09030204051006020105180a0b0619060f0e0a03 70
    0x801102c040c4200071031100b00079078030406107048000020700b03a4184000a4544048080b4098508174041402d515460035858000500b04040700d51040c001c102c040303000424810264000f80c5203011300314040005c43ca05805446c3d610210340400c0c00c41c00d50b42c0000001c1e6012000c0014483c214040300c4016402c407039038400c143c101da440c4044030002070a000e04003040e603000b14110701c0600b0301d0101104011180802c0d50100903c5070003600705209074000c14040041015135003100411240070f0000454242c01d00380e026650111110000146460701c0b001a0380c91500f1591007400c0d10400080c07948402503049850034028030403440100752801d08101c0480d245d000e03a0710703000036542c404a541004c0a2240744080011a006403080026041101085884a2082c042d08016609010210304240c0f41b64405202c00c00c8004003601c404861941c45c00045103000d0421030b48842e1101c018130303800c816400750900518981d100e5400c0849206005020855050255032040c41460004c00c0402c1c100d0b = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 127148417 1250 127147167 127147169
    0x60f05101707080402210a060902130222050307060f21020c03271e06070b09060103050d0203040e19061701061a0f04060c050f060703090201080f07050301 68
    0x4640050012412031411a207031002104034803041421002405002c41e003010720180200d00030348190303510082640302482c1000b0b000741d0a20300b40e0300241004d404154664171002c2918802071041c186070740410070b4041a0f0300640d9051603d012501c0c1d80d003060f070b008002501c0c000c210540c050503525140c024003400c122648d64261041c0400390030b00c001c0480000318601100343c00902c0443d1620403443c041c66980e080070007d0100c416080e207101600c0080302102e2100840001c040f51900c519060007a1920103c02c010603070048420f10050b000070795400112449000c5000003086a503140d41095407034080c0c107108a8042d90000c000502020040007600f03640540e034401508641c2c1900d03041080280f04a51080400e4810821089103403003041d0030000c01c0300c81c034071040e00301c10019a40c03000e100d00c510208001c1c816420001080441e0140d6150080c460080e0700f80d480285045d0001e5040c010103c031441c00007aa1407043c00708542e00315940c1504032800007101e510924020102030443e101c1 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 127149667 1250 127148417 127148419
    0x90f04050a0b2407140115030b161e030b0a0f06050c060f0f0c0c0c12011e150608040510110a08130302060609090a0f110301270213020904090b01090b04060f05 70
    0x441a01c4030500001f500701c569511140d10901e43d00541c1d0341094800d09000355070f041101c07141101e42d100c01600c18103005400d03e07480102402180f10f854410f80051603424030040c2c100e0140709000072035070462b41c00c2400811160315900d0b6120002c0418509050004110000c103491000911802900e04205964050000150240d0300c0100c12506d501e042c0501d810b4940c000c03020380961014040642000b54484044609082c0202d450f2514170166034081d50080c0d20f404030b04034104034452040c29015003141c001e00c240c80010703105c0c407a131200fa82c000ca00000e4207001c000424601840d4440d02c803e41c04151410030140c1300b600755034000d4445030044c3c00705104050050105580490500c04401c90740e070b10100b486844a040e1030000c41103010792035400d109501e00850b00c030074110500b4074001c0c0000300c81c1c80540c00c6645a801c01480d1124000500d41d121750911081009480e00e2080542e85030181042141e150305d4480f004003a40c2c1150429409103042c0041000f20340000701400c41501c1e8 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 127150917 1250 127149667 127149683
    0x5070b131d0109110c03031303020d02010c02060f0a0209130b09010f0501120e0304050d030905101701150e060d290f0d0206070819140301030b0606090f04050a0b2407 73
    0x7202400c80301650040341c02d0501c00d400008140b0403d030301e0014002340e44610940075150340081d21481a422a030301d4200314000358210354009285a8402400c55500c0042c0c8100103040040c803001040440400940001d94503540f0b01c285d2202e442c00001950041c480032591084150a1100081840480ca40ea06080b59252010f0340792140003841607e02400001d810001c00208500740180646290b200342400381c0220718410180c5407240d007648400d5100c0030600410781e46032074994489051014100404c00104041c03a06007a0385141c002c0480b0798101e14003140381d4a4080c1564455004503803141007800c40b1b0680d80f801500d5181610b009031784125108040c4415500205006101d4140d000b044084001409041c5101810720301031010300540e90700040c24443c890301d40903807100303010160100c0c0742c0d070f030000b880361501b13500078103c09001802000c01401400041410b4440546070a0340a5855620481413400c001c141c661140030a61030450310b04200f5594400c10f446080d6000d08071035 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 127152167 1250 127150917 127150931
    0x7061a0a091503080a030603145808090c031908070602070b01030c0801090203060105040b0f0a09020406030b030a080a30050615090906060c0a05070b131d0109 70
    0x9070005802d00085401c80c220554881c00d2a030300400601103400111080700701e80c200941c46400001e00c00190300d40c2c9814000344141d48440007912400703204411400d40b07040600900c0a0720b40324a00141915507058100600c54188801900c0307600c00420303c0b0011b6210303000b250001d50300042c2e558402c202540c00101544034605206940e841100006480580001952400c110180b498541200d014885507501c1c551201015800d07116813035400780d49a444a070060101c0c1c6443ea1142c81303083e20050009000013140c1c030103c0c0441d05180c3c4040e000c9070740840c0422107280c060103030941041c01200500b4200120b40c5d82c86404c1e000315103801003008214141c2c3e01140c0680d80f48446200154003c0521040e1440031100c060803084a0fa64010b1122207042d1001519150649141400082240000b50345e0401401007641040d9401d14252060b1814800401d1080c005c01c0301401a04840a60f03541c00b01194002100d80f6600180004404800c5811101d41c201d0119040d5000d80101103251 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 127153417 1250 127152167 127152191
    0x61404080703150e03030c070b190905100b060a05030115110f1f0605100e1318020f0a031a070c2001140301080d05030402032107061a0a09 61
    0x240610341100a03a4420180044148000c1031640c0c40755040703808050151081940b000d070386901050b1143d44842c9020700c8464002030003805620362000011041c90880700d005078200d4252580c180c0241c54540007060030514a071000d020304546500700b84c1d0302501c0c20301c03031550050081c40144a0a1824041408100e1149110381140b43c0b84205040031504185d489440c440c0d2180e91282c0e0816a110000038204d100102c14014001100d8004000c200b0401c1e15040c02c0d25100c6070254800c3c1c2c042c40100c0b800e000d0010a1054a65420400e400d08200303445034414401841003e40f81c0c20b20400f441c42041000642ca0503281044840d48a010700c07241d110114152030361001180002e1604030b003c900740c0c0784021080010380da01c032401d994400c0e0b001141c442c40240c0384028007440640c0d1b0801d6000400c0d0038000d6000359001440502180e80400080c90a00e00090240c00d00c10025400020294248401d40c0a4280f41000c50b4040502d0400c01e44001681e07842584201c84d07a02c0d856031601c3c040 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 127154667 1250 127153417 127153457
    0x503070518060f1207061106010609090c0e06040f0609090b1c2405090c10050d020a090504050a0207050d02030406080103140f0607022109183102010314040c06 70
    0x6460001e401075400b1482d507000302d620f03030700c0c10700407000010520b0300c0300621f04000040541c100e801c99281c101181d0306156408001e4681014500c0c2440031141480c0d0850f20b41000400041000301c4400c4400750a2050046c2401d90a501a8a1982c240451194155a01c00400e881d400302d02e104405801140e107054a014940540107a0b800c00c5606007400100010350415449462a003082d145105c0b809401c201c00150b00c02c0e40300000401c14021203a40f0406907000742480c00c124103014503134035035813400a002d64100305d841d210f1158010401404021040005000f13000140c005581010305200c0000d0900740c0500c400b0704100e504d80000b0800350390901a0800c64144401681c150f440c000e6406075840b280800d169461000c609002c101034603003041030300c44001000384000c50204890001600c000c001034500e00746c8541d0306010180b0a10000741404403035842d18080700c20380026000140c00c54603d0221300c02250301c041c1c20000000c81c005038a0064800b00c1c04c04070b0118602c1907a8540b = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 127155917 1250 127154667 127154689
    0x11060a0b042009120f03030a05040b010602160902091201090f06060b120604021e0c0601080f070e180c090f040c090507050706090510060b1b0f07231e0406050307051806 74
    0x260f801b0000621450b1901a04254808d60050b20304030881d9981d00c6c03080b645d810100c3c44103c100f40000c0c40500c08001560018800028010700e0f0901c4e0b80c038040f2030a42100c94819040703c03d0424000c41c44204070b118098000104680d420450030b040102002c044010b90040ca45449160f001980c3c100c01d401c916480711002c40e030652926110b400d41a0310964501003030040d040c00c0e20451428074000c0c2d80018040090701c20708a9a0103141c1c41c0d0200010042c902a07158001e240101c1004202580f03c042041e4419101e040030300c081410309003013001001c4010381242e1038250600041011154000c401c840b01240d00510004284881e400e143d4140380c41d50650004050801e2400a100041076000e03110300b51490800100402c2404005540c480c0d414a2404154001e024200b083c0b0b400d00030040101890004071600c02c034003641c001124035100c1d43c0380ca001075034103250070a40e5041c40d21500e40506820f400511205003404001041500c0c1c140c0024908510140003030410780305d18600d06 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 127157167 1250 127155917 127155943
    0x60409061a01141603110f0607020601060f030b1005030a0921080c04030f080a0302040807090203090c03070e060d020d050d050702090a0501050114070311060a0b04200912 75
    0xe4034460040c1c41800d041c407403001d00090082407142c4040c40c00c401200c00900c0c007000990284011a030b0f00381c4500d028145819954024240c3c41e031700c042c0d0103101c41c52040ca0a940580980d604050000d00780520703440c150410145003501d0881d15807600340881802100301c5c01c2c01034482d52070188200240070283c03c010303da000680248c1400b1407030b084052010101a0301d60024a0b95003035100707a143e01851201070051080300c40c210f000304003c030008280189452802528080d20340002501d004040ea000383c44140d40001000703040315060105402c070f100c00b10007901c0e00034940080c90a2051016114622130040c00f48003004560740c0b40400d4a41990250a85900c0035110700080c2107034001290590141c1034840010304504007a00c6090305980c4141c4401245085406140c030b695041803408a00b8040700d0400c546800d0010003456100300c0c03050001007405540d201c1403000390381c0c01488803116590342146c0003e80031040d00580300700c2001542e501010000c030030b8820317241c400120080 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 127158273 1106 127157167 127157171
    0x17091c0203071a0c0708150106030e100506010318060902011412040318051816020106080709020d11030406050402030d0e01020a030c14070902070507050a050d0b06040906 75
    0xc038180e90001c3c2d4018100000390544528214041d0815000366001c074110180c3d010303043c8207030340c0500464501070001c5580740b11295525200c111010542a44580001c0d160381d102c0d510440c403500d24041c03100c03454211820828001c006103102030b4001840d1441d1406108030240845481000200e0303d8820b540c0c9503102103a4030303481c08601c80065040840002643d588410061003000481500c11201e801d221040c29140401c0c02c120205690606008024145020807008106e422030b06000da51408031061803130040031084034030a1040300c0071080c032061299960210340b080e4401c1e02110b2505026800a5510000c3d100e601401a80940c1003c1c0029218130802c0b00c801c0d12498418401c101c40124850801b6078582056601c19404590601401002c1000c400107200643c1d880031054285008030715004c4074035801070540705824004c58030310b880b21f61000218a07000902 = true := by decide +kernel

theorem cover : BRFrame.Cov 126978417 127158273 := by
  have h0 := BRFrame.cov_init 126978417
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126978417 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126978417 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126978417 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126978417 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126978417 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126978417 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126978417 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126978417 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126978417 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126978417 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126978417 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126978417 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126978417 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126978417 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126978417 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126978417 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126978417 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126978417 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126978417 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126978417 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126978417 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126978417 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126978417 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126978417 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126978417 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126978417 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126978417 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126978417 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126978417 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126978417 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126978417 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126978417 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126978417 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126978417 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126978417 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126978417 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126978417 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126978417 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126978417 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126978417 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126978417 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126978417 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126978417 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126978417 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126978417 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126978417 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126978417 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126978417 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126978417 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126978417 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126978417 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126978417 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126978417 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126978417 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126978417 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126978417 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126978417 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126978417 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126978417 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126978417 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126978417 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126978417 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126978417 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126978417 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126978417 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126978417 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126978417 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126978417 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126978417 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126978417 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126978417 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126978417 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126978417 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126978417 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126978417 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126978417 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126978417 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126978417 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126978417 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126978417 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126978417 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126978417 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126978417 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126978417 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126978417 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126978417 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126978417 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126978417 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126978417 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126978417 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126978417 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126978417 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126978417 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126978417 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126978417 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126978417 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126978417 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126978417 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126978417 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126978417 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126978417 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126978417 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126978417 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126978417 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126978417 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126978417 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126978417 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126978417 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126978417 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126978417 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126978417 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126978417 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126978417 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126978417 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126978417 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126978417 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126978417 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126978417 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126978417 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126978417 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126978417 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126978417 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126978417 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126978417 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126978417 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126978417 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126978417 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126978417 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126978417 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126978417 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126978417 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126978417 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126978417 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126978417 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126978417 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126978417 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126978417 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126978417 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126978417 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126978417 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126978417 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126978417 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126978417 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126978417 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 126978417 ≤ n) (h2 : n < 127158273) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
